#!/usr/bin/env python3
"""Compile and run the sharded Erdős #64 search, and independently verify any witness."""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

JOB_DIRECTORY = Path(__file__).resolve().parent


def has_simple_cycle_of_length(adj, target_len):
    """Independent pure-Python exact checker for a simple cycle of length target_len."""
    n = len(adj)
    if n < target_len:
        return False
    if target_len in (4, 8, 16):
        half = target_len // 2
        for root in range(n):
            ep_masks = {}
            root_bit = 1 << root

            def dfs_half(u, depth, interior):
                if depth == half - 1:
                    for w in adj[u]:
                        if w < root or ((interior | root_bit) >> w) & 1:
                            continue
                        prev_list = ep_masks.get(w)
                        if prev_list is not None:
                            for pm in prev_list:
                                if (pm & interior) == 0:
                                    return True
                            prev_list.append(interior)
                        else:
                            ep_masks[w] = [interior]
                    return False
                for w in adj[u]:
                    if w < root or ((interior | root_bit) >> w) & 1:
                        continue
                    if dfs_half(w, depth + 1, interior | (1 << w)):
                        return True
                return False

            if dfs_half(root, 0, 0):
                return True
        return False

    for root in range(n):
        root_nbrs = set(adj[root])

        def dfs_full(u, length, visited):
            if length == target_len - 1:
                return u in root_nbrs
            for w in adj[u]:
                if w < root or (visited >> w) & 1:
                    continue
                if dfs_full(w, length + 1, visited | (1 << w)):
                    return True
            return False

        if dfs_full(root, 0, 1 << root):
            return True
    return False


def verify_witness(witness):
    """Independently verify that witness['graph'] is a finite simple graph with delta >= 3 and no 2^k-cycle."""
    graph = witness["graph"]
    n = int(graph["n"])
    adj = graph["adj"]
    if n < 4 or len(adj) != n:
        raise ValueError(f"invalid graph size n={n}")
    adj_sets = [set(nbrs) for nbrs in adj]
    for u in range(n):
        if len(adj[u]) != len(adj_sets[u]):
            raise ValueError(f"parallel edges at vertex {u}")
        if u in adj_sets[u]:
            raise ValueError(f"self-loop at vertex {u}")
        if len(adj_sets[u]) < 3:
            raise ValueError(f"vertex {u} has degree {len(adj_sets[u])} < 3")
        for v in adj_sets[u]:
            if not (0 <= v < n) or u not in adj_sets[v]:
                raise ValueError(f"asymmetric or out-of-range edge ({u}, {v})")

    checked_lengths = []
    length = 4
    while length <= n:
        if has_simple_cycle_of_length(adj, length):
            raise ValueError(f"witness FAILS: contains a simple cycle of length {length}")
        checked_lengths.append(length)
        length *= 2

    return {
        "source": witness.get("source", "unknown"),
        "n": n,
        "min_degree": min(len(x) for x in adj),
        "max_degree": max(len(x) for x in adj),
        "checked_power_of_two_lengths": checked_lengths,
        "adj": adj,
    }


def write_json(path, value):
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temp.replace(path)


def main():
    shard, shards = map(int, sys.argv[1:3])
    out = Path(sys.argv[3])
    if not 0 <= shard < shards <= 256:
        raise ValueError("invalid shard assignment")
    out.mkdir(parents=True, exist_ok=True)

    lift_budget = int(os.environ.get("ERDOS64_LIFT_SECONDS", "3600"))
    sa_budget = int(os.environ.get("ERDOS64_SA_SECONDS", "300"))

    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))

    with tempfile.TemporaryDirectory(prefix="erdos-64-") as temporary:
        binary = Path(temporary) / "search"
        subprocess.run(
            [
                "g++", "-std=c++17", "-O3", "-march=native", "-fopenmp",
                "-Wall", "-Wextra", "-Werror",
                str(JOB_DIRECTORY / "search.cpp"), "-o", str(binary),
            ],
            check=True,
            timeout=120,
        )
        proc = subprocess.run(
            [str(binary), str(shard), str(shards), str(lift_budget), str(sa_budget)],
            capture_output=True,
            text=True,
            check=True,
            timeout=lift_budget + sa_budget + 120,
            env=env,
        )
        data = json.loads(proc.stdout)

    data["mathematical_status"] = "OPEN"
    if "witness" in data:
        verified = verify_witness(data["witness"])
        write_json(out / "witness.json", verified)
        data["witness"] = verified
        data["mathematical_status"] = "CLOSED NO"
        print(json.dumps({"status": "CLOSED NO", "n": verified["n"], "source": verified["source"]}), flush=True)

    write_json(out / "result.json", data)
    total_lifts = sum(f["tested"] for f in data["lift_families"])
    total_sa = sum(s["evals"] for s in data["sa_orders"])
    nm = data.get("best_near_miss", {})
    print(
        json.dumps({
            "shard": shard,
            "shards": shards,
            "status": data["mathematical_status"],
            "lifts_tested": total_lifts,
            "sa_evals": total_sa,
            "best_near_miss_c16": nm.get("c16"),
            "best_near_miss_n": nm.get("graph", {}).get("n"),
            "seconds": round(data["seconds"], 2),
        }),
        flush=True,
    )


if __name__ == "__main__":
    main()
