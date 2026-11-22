#!/usr/bin/env python3
"""Verify exact shard tiling, re-verify any witness, and merge Erdős #647 sieve results."""

from pathlib import Path
import json
import os
import sys

from run import WHEEL_W, verify_witness_py, write_json


def main() -> None:
    shards_dir, summary_dir = Path(sys.argv[1]), Path(sys.argv[2])
    expected_shards = int(float(os.environ["SHARDS"]))

    parts = []
    for s in range(expected_shards):
        path = shards_dir / f"shard-{s}" / "result.json"
        if not path.exists():
            continue
        data = json.loads(path.read_text(encoding="utf-8"))
        if (data["shard"], data["shards"]) != (s, expected_shards):
            raise ValueError(f"incorrect shard identity in shard-{s}")
        parts.append(data)

    if not parts:
        sys.exit("no shard results found")

    n_start = int(parts[0]["n_start"])
    n_end = int(parts[0]["n_end"])
    for p in parts:
        if int(p["n_start"]) != n_start or int(p["n_end"]) != n_end:
            raise ValueError("inconsistent [n_start, n_end) across shards")
        if p["wheel_modulus"] != WHEEL_W or p["wheel_classes"] != 786:
            raise ValueError("inconsistent wheel parameters across shards")

    u_min = n_start // WHEEL_W
    u_max = (n_end + WHEEL_W - 1) // WHEEL_W

    parts_by_u = sorted(parts, key=lambda r: r["shard_u_lo"])
    all_present = len(parts) == expected_shards
    tiled_exactly = (
        all_present
        and parts_by_u[0]["shard_u_lo"] == u_min
        and parts_by_u[-1]["shard_u_hi"] == u_max
        and all(a["shard_u_hi"] == b["shard_u_lo"] for a, b in zip(parts_by_u, parts_by_u[1:]))
    )
    all_complete = all(bool(p["complete"]) and p["completed_classes"] == 786 for p in parts)

    witnesses = []
    for p in parts:
        if "witness_n" in p:
            witnesses.append(verify_witness_py(p["witness_n"]))

    best_depth = 0
    best_depth_n = "0"
    best_depth_kill_tau = 0
    for p in parts:
        if p["max_depth"] > best_depth:
            best_depth = p["max_depth"]
            best_depth_n = p["max_depth_n"]
            best_depth_kill_tau = p["max_depth_kill_tau"]

    total_u_tested = sum(p["u_tested"] for p in parts)
    total_t1 = sum(p["t1_survivors"] for p in parts)
    total_t2 = sum(p["t2_survivors"] for p in parts)
    total_t3 = sum(p["t3_survivors"] for p in parts)
    total_p7 = sum(p["prime7_survivors"] for p in parts)
    total_seconds = sum(p["seconds"] for p in parts)

    merged = {
        "problem": "Erdős #647",
        "mathematical_status": "CLOSED YES" if witnesses else "OPEN",
        "n_start": str(n_start),
        "n_end": str(n_end),
        "wheel_modulus": WHEEL_W,
        "wheel_classes": 786,
        "shards_expected": expected_shards,
        "shards_present": len(parts),
        "tiled_exactly": tiled_exactly,
        "all_shards_complete": all_complete,
        "range_exhausted": tiled_exactly and all_complete and not witnesses,
        "total_u_tested": total_u_tested,
        "total_t1_survivors": total_t1,
        "total_t2_survivors": total_t2,
        "total_t3_survivors": total_t3,
        "total_prime7_survivors": total_p7,
        "max_depth": best_depth,
        "max_depth_n": best_depth_n,
        "max_depth_kill_tau": best_depth_kill_tau,
        "total_shard_wall_seconds": round(total_seconds, 3),
    }

    if witnesses:
        write_json(summary_dir / "witness.json", witnesses[0])
        print(f"CLOSED YES. Independently verified witness n = {witnesses[0]['n']}")
    else:
        print(
            f"OPEN. Range [{n_start}, {n_end}) tiled={tiled_exactly} complete={all_complete} "
            f"u_tested={total_u_tested} prime7={total_p7} max_depth={best_depth} (n={best_depth_n})"
        )

    write_json(summary_dir / "erdos-647-sieve.json", merged)
    if not witnesses and not (tiled_exactly and all_complete):
        sys.exit(1)


if __name__ == "__main__":
    main()
