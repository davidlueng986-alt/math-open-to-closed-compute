#!/usr/bin/env python3
"""Sharded batch runner for D9-C6 production closure (<= 10 shards, <= 5.5h wall budget).

Supports two subcommands:
  --prepare : Stream r38_26.g6.gz (or any 26-vertex .g6/.g6.gz core database), verify & filter
              by exact D9-C6 edge/degree bounds, pair with all matching canonical orbits among
              D9-C6-S00..S24, and write a deterministic shard manifest (`manifest.json`).
  --run     : Execute shard K of M (1 <= M <= 10, 0 <= K < M) with per-instance checkpointing
              (`result.json`), resume support, wall-time budget management (<= 19800s = 5.5h),
              and compressed DRAT/LRAT/CNF proof manifest output.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import d9c6_compact_cnf as d9c6

MAX_SHARDS = 10
DEFAULT_WALL_BUDGET_S = 19800  # 5.5 hours (30-min safety margin inside 6h GH Actions cap)
SAFETY_TAIL_S = 120


def prepare_manifest(
    g6_file: Path,
    manifest_out: Path,
    e_t_filter: list[int] | None = None,
    max_instances: int = 0,
    verify_alpha: bool = True,
) -> dict:
    """Build deterministic instance manifest pairing filtered (3,8;26) cores with 25 D9-C6 orbits."""
    orbits = d9c6.enumerate_d9c6_skeletons()
    orbits_by_et: dict[int, list[dict]] = {}
    for o in orbits:
        orbits_by_et.setdefault(o["e_T"], []).append(o)

    allowed_edges = set(e_t_filter) if e_t_filter else set(range(73, 82))
    assert allowed_edges.issubset(set(range(73, 82))), f"Invalid e_T filter: {allowed_edges}"

    cores_by_edges, filter_stats = d9c6.load_and_filter_cores(
        g6_file, allowed_edges=allowed_edges, verify_alpha=verify_alpha
    )

    instances = []
    # Order highest e_T first (tightest S-domination / fastest refutation first), then orbit_id
    for e_t in sorted(allowed_edges, reverse=True):
        cores = cores_by_edges.get(e_t, [])
        matching_orbits = orbits_by_et.get(e_t, [])
        for core_idx, g6 in enumerate(cores):
            adj = d9c6.decode_g6(g6)
            min_deg = min(x.bit_count() for x in adj)
            core_hash = hashlib.sha256(g6.encode("ascii")).hexdigest()[:10]
            for orb in matching_orbits:
                if min_deg < orb["min_deg_T"]:
                    continue
                inst_id = f"{orb['id']}_e{e_t}_c{core_idx:05d}_{core_hash}"
                instances.append({
                    "instance_id": inst_id,
                    "orbit_id": orb["id"],
                    "e_xy": orb["e_xy"],
                    "e_T": e_t,
                    "core_idx": core_idx,
                    "g6": g6,
                })
                if max_instances > 0 and len(instances) >= max_instances:
                    break
            if max_instances > 0 and len(instances) >= max_instances:
                break
        if max_instances > 0 and len(instances) >= max_instances:
            break

    manifest = {
        "schema_version": 1,
        "problem": "Ramsey-R310-D9-C6",
        "source_file": str(g6_file.name),
        "allowed_edges": sorted(allowed_edges),
        "total_orbits": len(orbits),
        "filter_stats": filter_stats,
        "total_instances": len(instances),
        "instances": instances,
    }
    manifest_out.parent.mkdir(parents=True, exist_ok=True)
    d9c6.write_atomic_json(manifest_out, manifest)
    return manifest


def shard_slice(instances: list[dict], shard_idx: int, num_shards: int) -> list[dict]:
    """Round-robin strided sharding so every shard gets an even mix of e_T and orbits."""
    assert 1 <= num_shards <= MAX_SHARDS, f"num_shards must be in [1, {MAX_SHARDS}], got {num_shards}"
    assert 0 <= shard_idx < num_shards, f"shard_idx {shard_idx} out of range for num_shards={num_shards}"
    return [inst for idx, inst in enumerate(instances) if idx % num_shards == shard_idx]


def run_shard(
    manifest_path: Path,
    shard_idx: int,
    num_shards: int,
    out_dir: Path,
    wall_budget_seconds: int = DEFAULT_WALL_BUDGET_S,
    per_instance_seconds: int = 1800,
    resume_dir: Path | None = None,
    include_b2: bool = True,
    include_i7: bool = True,
    include_lex: bool = True,
    max_i7: int | None = None,
    try_lrat: bool = True,
    compress_cnf: bool = True,
    dry_run: bool = False,
) -> dict:
    """Execute one shard of the D9-C6 manifest with checkpointing and wall-budget control."""
    assert 1 <= num_shards <= MAX_SHARDS, f"num_shards must be <= {MAX_SHARDS}, got {num_shards}"
    assert 0 <= shard_idx < num_shards, f"Invalid shard_idx={shard_idx} for num_shards={num_shards}"
    assert wall_budget_seconds <= 21000, "wall_budget_seconds exceeds 5.83h safe margin inside 6h limit"

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    orbits_by_id = {o["id"]: o for o in d9c6.enumerate_d9c6_skeletons()}
    assigned = shard_slice(manifest["instances"], shard_idx, num_shards)

    out_dir.mkdir(parents=True, exist_ok=True)
    inst_root = out_dir / "instances"
    inst_root.mkdir(parents=True, exist_ok=True)

    t0 = time.monotonic()
    counts = {
        "CERTIFIED_UNSAT": 0,
        "VERIFIED_WITNESS": 0,
        "OPEN_TIMEOUT": 0,
        "UNSAT_VERIFICATION_FAILED": 0,
        "SKIPPED_RESUMED": 0,
        "DRY_RUN_OK": 0,
        "DEFERRED_WALL_BUDGET": 0,
    }
    proof_entries = []
    witness_found = None

    for idx, item in enumerate(assigned):
        inst_id = item["instance_id"]
        inst_out = inst_root / inst_id

        # Check resume checkpoint if provided
        prev_res_path = (resume_dir / "instances" / inst_id / "result.json") if resume_dir else None
        if prev_res_path and prev_res_path.is_file():
            prev = json.loads(prev_res_path.read_text(encoding="utf-8"))
            if prev.get("status") in ("CERTIFIED_UNSAT", "VERIFIED_WITNESS"):
                counts["SKIPPED_RESUMED"] += 1
                continue

        # Check existing local checkpoint (idempotent restart)
        local_res_path = inst_out / "result.json"
        if local_res_path.is_file():
            prev = json.loads(local_res_path.read_text(encoding="utf-8"))
            if prev.get("status") in ("CERTIFIED_UNSAT", "VERIFIED_WITNESS"):
                counts["SKIPPED_RESUMED"] += 1
                continue

        elapsed = time.monotonic() - t0
        remaining = wall_budget_seconds - elapsed - SAFETY_TAIL_S
        if remaining < 30 and not dry_run:
            counts["DEFERRED_WALL_BUDGET"] += len(assigned) - idx
            break

        orb = orbits_by_id[item["orbit_id"]]
        if dry_run:
            inst_out.mkdir(parents=True, exist_ok=True)
            adj = d9c6.decode_g6(item["g6"])
            _, _, meta = d9c6.build_d9c6_cnf(
                adj,
                orb,
                include_b2=include_b2,
                include_i7=include_i7,
                include_lex=include_lex,
                max_i7=max_i7,
                verify_core=True,
            )
            res = {
                "instance_id": inst_id,
                "orbit_id": item["orbit_id"],
                "e_T": item["e_T"],
                "status": "DRY_RUN_OK",
                "meta": meta,
            }
            d9c6.write_atomic_json(inst_out / "result.json", res)
            counts["DRY_RUN_OK"] += 1
            continue

        budget = min(per_instance_seconds, max(30, int(remaining)))
        res = d9c6.proof_first_solve_instance(
            item["g6"],
            orb,
            inst_out,
            seconds=budget,
            include_b2=include_b2,
            include_i7=include_i7,
            include_lex=include_lex,
            max_i7=max_i7,
            compress_cnf=compress_cnf,
            try_lrat=try_lrat,
            instance_id=inst_id,
        )
        st = res.get("status", "OPEN_TIMEOUT")
        counts[st] = counts.get(st, 0) + 1

        if st == "CERTIFIED_UNSAT":
            proof_entries.append({
                "instance_id": inst_id,
                "orbit_id": item["orbit_id"],
                "e_T": item["e_T"],
                "cnf_sha256": res.get("cnf_sha256"),
                "cnf_gz_sha256": res.get("cnf_gz_sha256"),
                "drat_sha256": res.get("drat_sha256"),
                "drat_bytes": res.get("drat_bytes"),
                "lrat_verified": res.get("lrat_verified"),
                "lrat_sha256": res.get("lrat_sha256"),
                "lrat_bytes": res.get("lrat_bytes"),
                "solve_seconds": res.get("solve_seconds"),
                "verify_seconds": res.get("verify_seconds"),
                "rel_dir": f"instances/{inst_id}",
            })
        elif st == "VERIFIED_WITNESS":
            witness_found = inst_id
            break

        # Periodic shard checkpoint update after every instance
        _write_shard_outputs(
            out_dir, shard_idx, num_shards, len(assigned), counts, proof_entries, witness_found, t0
        )

    summary = _write_shard_outputs(
        out_dir, shard_idx, num_shards, len(assigned), counts, proof_entries, witness_found, t0
    )
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def _write_shard_outputs(
    out_dir: Path,
    shard_idx: int,
    num_shards: int,
    assigned_count: int,
    counts: dict,
    proof_entries: list[dict],
    witness_found: str | None,
    t0: float,
) -> dict:
    summary = {
        "shard_idx": shard_idx,
        "num_shards": num_shards,
        "assigned_instances": assigned_count,
        "counts": counts,
        "witness_found": witness_found,
        "elapsed_seconds": round(time.monotonic() - t0, 3),
    }
    d9c6.write_atomic_json(out_dir / f"shard_{shard_idx}_summary.json", summary)
    d9c6.write_atomic_json(
        out_dir / f"shard_{shard_idx}_proof_manifest.json",
        {
            "shard_idx": shard_idx,
            "num_shards": num_shards,
            "certified_unsat_count": len(proof_entries),
            "proofs": proof_entries,
        },
    )
    return summary


def main() -> None:
    p = argparse.ArgumentParser(description="D9-C6 Sharded Production Runner")
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--prepare", action="store_true", help="Filter cores & generate shard manifest")
    mode.add_argument("--run", action="store_true", help="Run shard K of M from manifest")

    # --prepare options
    p.add_argument("--g6-file", type=Path, help="Input 26-vertex .g6 or .g6.gz database")
    p.add_argument("--manifest", type=Path, required=True, help="Path to manifest.json")
    p.add_argument("--e-t-filter", default="", help="Optional comma-separated e(T) filter (e.g. 73,74)")
    p.add_argument("--max-instances", type=int, default=0, help="Optional max instances cap (0 = all)")
    p.add_argument("--skip-alpha-check", action="store_true", help="Skip alpha<=7 check during prepare")

    # --run options
    p.add_argument("--shard-idx", type=int, default=0, help="0-indexed shard ID")
    p.add_argument("--num-shards", type=int, default=1, help="Total shards (<= 10)")
    p.add_argument("--out", type=Path, default=Path("out_d9c6_shard"), help="Shard output directory")
    p.add_argument("--resume-dir", type=Path, default=None, help="Optional previous shard output dir")
    p.add_argument("--wall-budget-seconds", type=int, default=DEFAULT_WALL_BUDGET_S)
    p.add_argument("--per-instance-seconds", type=int, default=1800)
    p.add_argument("--no-b2", action="store_true")
    p.add_argument("--no-i7", action="store_true")
    p.add_argument("--no-lex", action="store_true")
    p.add_argument("--no-lrat", action="store_true")
    p.add_argument("--no-compress-cnf", action="store_true")
    p.add_argument("--max-i7", type=int, default=None)
    p.add_argument("--dry-run", action="store_true", help="Build CNFs & checkpoints without Kissat")
    a = p.parse_args()

    if a.prepare:
        assert a.g6_file is not None, "--g6-file is required for --prepare"
        ef = [int(x.strip()) for x in a.e_t_filter.split(",") if x.strip()] if a.e_t_filter else None
        m = prepare_manifest(
            a.g6_file,
            a.manifest,
            e_t_filter=ef,
            max_instances=a.max_instances,
            verify_alpha=not a.skip_alpha_check,
        )
        print(
            json.dumps(
                {
                    "manifest": str(a.manifest),
                    "filter_stats": m["filter_stats"],
                    "total_instances": m["total_instances"],
                },
                indent=2,
            ),
            flush=True,
        )
    else:
        run_shard(
            manifest_path=a.manifest,
            shard_idx=a.shard_idx,
            num_shards=a.num_shards,
            out_dir=a.out,
            wall_budget_seconds=a.wall_budget_seconds,
            per_instance_seconds=a.per_instance_seconds,
            resume_dir=a.resume_dir,
            include_b2=not a.no_b2,
            include_i7=not a.no_i7,
            include_lex=not a.no_lex,
            max_i7=a.max_i7,
            try_lrat=not a.no_lrat,
            compress_cnf=not a.no_compress_cnf,
            dry_run=a.dry_run,
        )


if __name__ == "__main__":
    main()
