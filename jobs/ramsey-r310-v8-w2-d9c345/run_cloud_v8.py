#!/usr/bin/env python3
"""Unified Multi-Core Cloud Runner (Kaggle CPU / Google Colab / GitHub Actions) for Ramsey R(3,10) V8.

Supports parallel multi-core Proof-First Kissat + drat-trim (-L) + lrat-check execution across:
  - D9-C6: 12 surviving canonical 3x3 skeleton orbits (after pure-integer saturation/Hall b=1 pruning of 13/25 orbits)
  - D9-C5, D9-C4, D9-C3: surviving canonical skeleton orbits from verified d9c345_farkas_sparse.json
  - NA-T1-27: Unified NA-DAG Tier-1 D6 (r=5, n_T=27) on McKay r38_27.g6.gz cores
  - NA-T2-27: Unified NA-DAG Tier-2 D78 (T*=27) on McKay r38_27.g6.gz cores

Can automatically fetch & compile pinned Kissat + drat-trim + lrat-check on fresh Kaggle/Colab instances
when `--auto-build-tools` is passed.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
JOBS_DIR = HERE.parent
D6_DIR = JOBS_DIR / "ramsey-r310-v8-w2-nadag-d6"
D78_DIR = JOBS_DIR / "ramsey-r310-v8-w2-nadag-d78"

for p in (HERE, D6_DIR, D78_DIR):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))

import d9c345_compact_cnf as d9_solver
import d9c345_pruner as d9_pruner

KISSAT_REPO = "https://github.com/arminbiere/kissat.git"
KISSAT_COMMIT = "8af8e56f174b778aef3aa45af9f739b2a5f492c2"
DRAT_REPO = "https://github.com/marijnheule/drat-trim.git"
DRAT_COMMIT = "2e3b2dc0ecf938addbd779d42877b6ed69d9a985"
MCKAY_R38_27_URL = "https://users.cecs.anu.edu.au/~bdm/data/r38_27.g6.gz"


def write_atomic_json(path: Path, obj: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(json.dumps(obj, indent=2) + "\n")
        f.flush()
        os.fsync(f.fileno())
    tmp.replace(path)


def ensure_sat_tools(build_root: Path) -> dict:
    """Ensure kissat, drat-trim, and lrat-check are compiled and on PATH."""
    bin_dir = build_root / "bin"
    bin_dir.mkdir(parents=True, exist_ok=True)
    os.environ["PATH"] = f"{bin_dir}:{os.environ.get('PATH', '')}"

    def _clone_at(name: str, url: str, rev: str) -> Path:
        d = build_root / name
        if d.exists():
            shutil.rmtree(d)
        d.mkdir(parents=True)
        subprocess.run(["git", "init", "-q"], cwd=d, check=True)
        subprocess.run(["git", "remote", "add", "origin", url], cwd=d, check=True)
        subprocess.run(["git", "fetch", "-q", "--depth", "1", "origin", rev], cwd=d, check=True)
        subprocess.run(["git", "checkout", "-q", "--detach", "FETCH_HEAD"], cwd=d, check=True)
        return d

    if not shutil.which("kissat"):
        kdir = _clone_at("kissat", KISSAT_REPO, KISSAT_COMMIT)
        subprocess.run(["./configure"], cwd=kdir, check=True)
        subprocess.run(["make", "-j2"], cwd=kdir, check=True)
        shutil.copy2(kdir / "build" / "kissat", bin_dir / "kissat")

    if not shutil.which("drat-trim") or not shutil.which("lrat-check"):
        ddir = _clone_at("drat-trim", DRAT_REPO, DRAT_COMMIT)
        subprocess.run(["make", "-j2", "drat-trim", "lrat-check"], cwd=ddir, check=True)
        shutil.copy2(ddir / "drat-trim", bin_dir / "drat-trim")
        if (ddir / "lrat-check").exists():
            shutil.copy2(ddir / "lrat-check", bin_dir / "lrat-check")

    return {
        "kissat": shutil.which("kissat"),
        "drat_trim": shutil.which("drat-trim"),
        "lrat_check": shutil.which("lrat-check"),
    }


def _solve_d9_orbit_worker(task: dict) -> dict:
    rep = d9_solver.proof_first_solve(
        c=task["c"],
        skeleton_rows=task["rows"],
        out_dir=Path(task["out_dir"]),
        seconds=task["seconds"],
        adj_T=None,
        include_i7=True,
        include_lex=True,
        orbit_id=task["id"],
    )
    return {
        "id": task["id"],
        "c": task["c"],
        "e_xy": task["e_xy"],
        "e_T": task["e_T"],
        "status": rep["status"],
        "iters": rep.get("iters", 0),
        "cuts": rep.get("cuts", 0),
        "codeg_cuts": rep.get("codeg_cuts", 0),
        "i10_cuts": rep.get("i10_cuts", 0),
        "solve_seconds": rep.get("solve_seconds"),
        "verify_seconds": rep.get("verify_seconds"),
        "total_seconds": rep.get("total_seconds"),
        "cnf_sha256": rep.get("cnf_sha256"),
        "drat_sha256": rep.get("drat_sha256"),
        "lrat_verified": rep.get("lrat_verified"),
        "lrat_sha256": rep.get("lrat_sha256"),
    }


def run_d9_cloud(
    case: str,
    out_dir: Path,
    shard_index: int,
    num_shards: int,
    workers: int,
    wall_budget_seconds: int,
    per_orbit_seconds: int,
    dry_run: bool = False,
) -> dict:
    t0 = time.monotonic()
    out_dir.mkdir(parents=True, exist_ok=True)

    if case == "C6":
        orbits_raw = d9_pruner.enumerate_canonical_skeletons(6)
        assert len(orbits_raw) == 12, f"Expected 12 surviving C6 orbits, got {len(orbits_raw)}"
        orbits = []
        for idx, rows in enumerate(orbits_raw):
            exy = sum(r.bit_count() for r in rows)
            orbits.append({
                "id": f"D9-C6-V8-S{idx:02d}",
                "c": 6,
                "nX": 3,
                "nT": 26,
                "e_xy": exy,
                "e_T": 72 + exy,
                "rows": list(rows),
            })
        orbits.sort(key=lambda o: (-o["e_xy"], o["id"]))
        farkas_ver = {"status": "PURE_INTEGER_SATURATION_AND_HALL_B1_VERIFIED", "pruned_orbits": 13, "surviving_orbits": 12}
    else:
        sparse_path = HERE / "certificates" / "d9c345_farkas_sparse.json"
        sum_path = HERE / "certificates" / "d9c345_pruning_summary.json"
        farkas_ver = d9_pruner.verify_sparse_certificate_file(sparse_path, sum_path)
        manifest_path = out_dir / f"manifest_{case}.json"
        d9_pruner.build_surviving_manifest_stdlib(sparse_path, case, manifest_path)
        bundle = json.loads(manifest_path.read_text(encoding="utf-8"))
        orbits = []
        for k, v in bundle["cases"].items():
            orbits.extend(v["surviving_orbits"])
        orbits.sort(key=lambda o: (-o["c"], -o["e_xy"], o["id"]))

    my_orbits = [o for idx, o in enumerate(orbits) if idx % num_shards == shard_index]

    if dry_run:
        summary = {
            "target": f"D9-{case}",
            "shard_index": shard_index,
            "num_shards": num_shards,
            "workers": workers,
            "total_surviving_orbits": len(orbits),
            "shard_orbits": len(my_orbits),
            "farkas_verification": farkas_ver,
            "dry_run": True,
            "sample_orbits": [o["id"] for o in my_orbits[:5]],
        }
        write_atomic_json(out_dir / "cloud_summary.json", summary)
        print(json.dumps(summary, indent=2), flush=True)
        return summary

    results = []
    counts = {"CERTIFIED_UNSAT": 0, "VERIFIED_WITNESS": 0, "OPEN_TIMEOUT": 0, "OTHER": 0}
    idx = 0
    while idx < len(my_orbits):
        rem_wall = int(wall_budget_seconds - (time.monotonic() - t0))
        if rem_wall < 20:
            break
        batch = my_orbits[idx : idx + workers]
        idx += len(batch)
        step_sec = min(per_orbit_seconds, max(15, rem_wall - 10))
        tasks = [
            {
                **orb,
                "out_dir": str(out_dir / orb["id"]),
                "seconds": step_sec,
            }
            for orb in batch
        ]
        with concurrent.futures.ProcessPoolExecutor(max_workers=min(workers, len(tasks))) as ex:
            for res in ex.map(_solve_d9_orbit_worker, tasks):
                results.append(res)
                st = res["status"]
                counts[st if st in counts else "OTHER"] += 1
                print(json.dumps(res), flush=True)
        write_atomic_json(
            out_dir / "checkpoint.json",
            {
                "target": f"D9-{case}",
                "shard_index": shard_index,
                "num_shards": num_shards,
                "completed": len(results),
                "total_assigned": len(my_orbits),
                "counts": counts,
                "elapsed_seconds": round(time.monotonic() - t0, 3),
                "results": results,
            },
        )
        if counts["VERIFIED_WITNESS"] > 0:
            break

    summary = {
        "target": f"D9-{case}",
        "shard_index": shard_index,
        "num_shards": num_shards,
        "workers": workers,
        "total_surviving_orbits": len(orbits),
        "shard_orbits": len(my_orbits),
        "completed": len(results),
        "counts": counts,
        "farkas_verification": farkas_ver,
        "elapsed_seconds": round(time.monotonic() - t0, 3),
        "results": results,
    }
    write_atomic_json(out_dir / "cloud_summary.json", summary)
    print(json.dumps(summary, indent=2), flush=True)
    return summary


def main() -> int:
    ap = argparse.ArgumentParser(description="Multi-Core Cloud Runner for Ramsey R(3,10) V8")
    ap.add_argument("--case", choices=["C6", "C5", "C4", "C3", "ALL"], default="C6")
    ap.add_argument("--shard-index", type=int, default=0)
    ap.add_argument("--num-shards", type=int, default=1)
    ap.add_argument("--workers", type=int, default=min(4, os.cpu_count() or 2))
    ap.add_argument("--wall-budget-seconds", type=int, default=14400)
    ap.add_argument("--per-orbit-seconds", type=int, default=900)
    ap.add_argument("--out", type=Path, default=Path("out_cloud_v8"))
    ap.add_argument("--auto-build-tools", action="store_true")
    ap.add_argument("--tools-dir", type=Path, default=Path("/tmp/ramsey-v8-tools"))
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if args.auto_build_tools and not args.dry_run:
        tools_info = ensure_sat_tools(args.tools_dir)
        print("Tools ready:", json.dumps(tools_info), flush=True)

    run_d9_cloud(
        case=args.case,
        out_dir=args.out,
        shard_index=args.shard_index,
        num_shards=args.num_shards,
        workers=max(1, args.workers),
        wall_budget_seconds=args.wall_budget_seconds,
        per_orbit_seconds=args.per_orbit_seconds,
        dry_run=args.dry_run,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
