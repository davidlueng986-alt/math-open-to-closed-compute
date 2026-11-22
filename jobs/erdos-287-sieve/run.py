#!/usr/bin/env python3
"""Run a deterministic shard of the Erdős #287 unconditional covering-chain search.

Usage: run.py SHARD SHARDS OUTDIR
Environment overrides (optional):
  ERDOS287_N_MIN       (default 33)
  ERDOS287_N_MAX       (default 3322, reaching B > 10^1009)
  ERDOS287_K_LO        (default 536870915, ~2^29)
  ERDOS287_K_HI        (default 724775733, ~1.35 * 2^29, guarantees factor < e/2 overlap)
  ERDOS287_SIEVE_LIMIT (default 500000)
  ERDOS287_SECONDS     (default 16200 = 4.5h per shard, safely inside 330m workflow limit)
"""
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile

JOB_DIR = Path(__file__).resolve().parent

DEFAULT_N_MIN = 33
DEFAULT_N_MAX = 3322
DEFAULT_K_LO = 536870915   # 2^29 + 3 == 3 (mod 6)
DEFAULT_K_HI = 724775733   # floor(1.35 * 2^29) aligned to 3 (mod 6)
DEFAULT_SIEVE_LIMIT = 500000
DEFAULT_SECONDS = 16200


def has_gmp() -> bool:
    proc = subprocess.run(
        ["g++", "-x", "c++", "-E", "-"],
        input="#include <gmp.h>\n",
        text=True,
        capture_output=True,
    )
    return proc.returncode == 0


def verify_proth_cert(cert: dict) -> None:
    n = int(cert["n"])
    k = int(cert["k"])
    a_pp = int(cert["a_pp"])
    a_p = int(cert["a_p"])
    if k % 2 != 1 or k >= (1 << n):
        raise ValueError(f"Proth condition k < 2^n violated at n={n}, k={k}")
    pp = (k << n) + 1
    p = (k << (n + 1)) + 1
    if pp < 139:
        raise ValueError(f"p' < 139 at n={n}")
    if pow(a_pp, (pp - 1) // 2, pp) != pp - 1:
        raise ValueError(f"Proth test failed for p' at n={n}, k={k}, a={a_pp}")
    if pow(a_p, (p - 1) // 2, p) != p - 1:
        raise ValueError(f"Proth test failed for p at n={n}, k={k}, a={a_p}")


def write_json(path: Path, value: dict) -> None:
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def main() -> None:
    shard, shards = int(sys.argv[1]), int(sys.argv[2])
    out = Path(sys.argv[3])
    if not (0 <= shard < shards <= 256):
        raise ValueError("invalid shard assignment")
    out.mkdir(parents=True, exist_ok=True)

    n_min = int(os.environ.get("ERDOS287_N_MIN", DEFAULT_N_MIN))
    n_max = int(os.environ.get("ERDOS287_N_MAX", DEFAULT_N_MAX))
    k_lo = int(os.environ.get("ERDOS287_K_LO", DEFAULT_K_LO))
    k_hi = int(os.environ.get("ERDOS287_K_HI", DEFAULT_K_HI))
    sieve_limit = int(os.environ.get("ERDOS287_SIEVE_LIMIT", DEFAULT_SIEVE_LIMIT))
    seconds = int(os.environ.get("ERDOS287_SECONDS", DEFAULT_SECONDS))

    env = os.environ.copy()
    env.setdefault("OMP_NUM_THREADS", str(min(4, os.cpu_count() or 1)))
    use_gmp = has_gmp()

    with tempfile.TemporaryDirectory(prefix="erdos-287-sieve-") as tmpdir:
        binary = Path(tmpdir) / "erdos287_sieve"
        cmd = [
            "g++", "-std=c++17", "-O3", "-march=native", "-fopenmp",
            "-Wall", "-Wextra", "-Werror",
            str(JOB_DIR / "erdos287_sieve.cpp"), "-o", str(binary),
        ]
        if use_gmp:
            cmd.extend(["-DUSE_GMP", "-lgmp"])
        subprocess.run(cmd, check=True, timeout=120)

        result = {
            "problem": "Erdős #287 (JSP-000244)",
            "shard": shard,
            "shards": shards,
            "use_gmp": use_gmp,
            "omp_threads": int(env["OMP_NUM_THREADS"]),
            "n_min": n_min,
            "n_max": n_max,
            "k_lo": k_lo,
            "k_hi": k_hi,
            "sieve_limit": sieve_limit,
        }

        # Shard 0 also runs the exact base closure [2, 500] and 64-bit covering chain [459, 2^64-1]
        if shard == 0:
            p_base = subprocess.run(
                [str(binary), "--mode=base", "--B-limit=500"],
                capture_output=True, text=True, check=True, timeout=60, env=env,
            )
            result["base"] = json.loads(p_base.stdout)
            p_c64 = subprocess.run(
                [str(binary), "--mode=chain64", "--start-covered=500", "--dump-links"],
                capture_output=True, text=True, check=True, timeout=60, env=env,
            )
            result["chain64"] = json.loads(p_c64.stdout)

        p_proth = subprocess.run(
            [
                str(binary),
                "--mode=proth-shard",
                f"--n-min={n_min}",
                f"--n-max={n_max}",
                f"--k-lo={k_lo}",
                f"--k-hi={k_hi}",
                f"--sieve-limit={sieve_limit}",
                f"--shard={shard}",
                f"--shards={shards}",
                f"--seconds={seconds}",
            ],
            capture_output=True, text=True, check=True, timeout=seconds + 60, env=env,
        )
        proth_res = json.loads(p_proth.stdout)

        # Independent Python Proth verification of every certificate produced by this shard
        for cert in proth_res["certs"]:
            verify_proth_cert(cert)

        result["proth"] = proth_res
        write_json(out / "result.json", result)
        print(json.dumps({
            "shard": shard,
            "shards": shards,
            "use_gmp": use_gmp,
            "completed": proth_res["completed_count"],
            "pending": proth_res["pending_count"],
            "proth_tests": proth_res["total_proth_tests"],
            "seconds": proth_res["seconds"],
        }), flush=True)


if __name__ == "__main__":
    main()
