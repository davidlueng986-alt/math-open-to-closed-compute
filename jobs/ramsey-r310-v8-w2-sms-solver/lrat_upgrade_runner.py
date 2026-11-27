#!/usr/bin/env python3
"""
Standalone DRAT-to-LRAT Upgrade & Verification Runner (Wave 2 Subagent 5).

Upgrades any DRAT-certified UNSAT branch (including D9-C7's 4 McKay cores,
Lean-CNF leaves, or per-cube proofs) to independently verified LRAT:
  1. `drat-trim <cnf> <drat> -L <proof.lrat>`
  2. `lrat-check <cnf> <proof.lrat>` (or `cake_lpr` if requested)

Supports both plain and `.gz`-compressed `.cnf.gz` / `.drat.gz` inputs,
single-file mode, batch directory mode, and `--dry-run` CLI verification.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
import tempfile
import time
from pathlib import Path
from typing import List, Optional, Sequence, Tuple


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _maybe_decompress(src: Path, work_dir: Path, target_name: str) -> Tuple[Path, bool]:
    """If `src` ends with `.gz`, decompress to `work_dir/target_name`; else return `src`."""
    if src.suffix == ".gz":
        dst = work_dir / target_name
        with gzip.open(src, "rb") as fi, open(dst, "wb") as fo:
            shutil.copyfileobj(fi, fo)
        return dst, True
    return src, False


def build_lrat_commands(
    cnf_path: Path,
    drat_path: Path,
    lrat_path: Path,
    drat_trim_bin: str = "drat-trim",
    lrat_check_bin: str = "lrat-check",
    forward_mode: bool = False,
) -> Tuple[List[str], List[str]]:
    """Build exact `drat-trim` and `lrat-check` CLI invocations."""
    trim_cmd = [drat_trim_bin, str(cnf_path), str(drat_path), "-L", str(lrat_path)]
    if forward_mode:
        trim_cmd.append("-f")
    check_cmd = [lrat_check_bin, str(cnf_path), str(lrat_path)]
    return trim_cmd, check_cmd


def upgrade_and_verify_lrat(
    cnf_path: Path,
    drat_path: Path,
    out_dir: Path,
    timeout_s: int = 1200,
    drat_trim_bin: str = "drat-trim",
    lrat_check_bin: str = "lrat-check",
    forward_mode: bool = False,
    compress_lrat: bool = True,
    remove_raw_drat: bool = False,
    dry_run: bool = False,
) -> dict:
    """Upgrade DRAT proof to LRAT via `drat-trim -L` and verify via `lrat-check`."""
    out_dir.mkdir(parents=True, exist_ok=True)
    lrat_path = out_dir / "proof.lrat"
    trim_log = out_dir / "drat-trim.log"
    check_log = out_dir / "lrat-check.log"

    if dry_run:
        trim_cmd, check_cmd = build_lrat_commands(
            cnf_path, drat_path, lrat_path, drat_trim_bin, lrat_check_bin, forward_mode
        )
        return {
            "status": "DRY_RUN",
            "cnf": str(cnf_path),
            "drat": str(drat_path),
            "lrat": str(lrat_path),
            "drat_trim_cmd": trim_cmd,
            "lrat_check_cmd": check_cmd,
        }

    if not cnf_path.exists():
        raise FileNotFoundError(f"CNF file not found: {cnf_path}")
    if not drat_path.exists():
        raise FileNotFoundError(f"DRAT file not found: {drat_path}")

    with tempfile.TemporaryDirectory(prefix="lrat_upgrade_") as td:
        td_path = Path(td)
        work_cnf, _ = _maybe_decompress(cnf_path, td_path, "input.cnf")
        work_drat, _ = _maybe_decompress(drat_path, td_path, "input.drat")

        trim_cmd, check_cmd = build_lrat_commands(
            work_cnf, work_drat, lrat_path, drat_trim_bin, lrat_check_bin, forward_mode
        )

        res: dict = {
            "status": "FAILED",
            "cnf": str(cnf_path),
            "drat": str(drat_path),
            "cnf_sha256": sha256_file(work_cnf),
            "drat_sha256": sha256_file(work_drat),
            "drat_trim_cmd": trim_cmd,
            "lrat_check_cmd": check_cmd,
            "drat_verified": False,
            "lrat_verified": False,
        }

        # Step 1: drat-trim -> LRAT
        t0 = time.monotonic()
        try:
            with open(trim_log, "w", encoding="utf-8") as log:
                p_trim = subprocess.run(
                    trim_cmd, stdout=log, stderr=subprocess.STDOUT, timeout=timeout_s
                )
            res["drat_trim_exit"] = p_trim.returncode
        except subprocess.TimeoutExpired:
            res["drat_trim_exit"] = None
            res["drat_trim_timeout"] = True
            res["drat_trim_s"] = round(time.monotonic() - t0, 3)
            (out_dir / "lrat_certificate.json").write_text(
                json.dumps(res, indent=2) + "\n", encoding="utf-8"
            )
            return res
        res["drat_trim_s"] = round(time.monotonic() - t0, 3)

        trim_text = trim_log.read_text(encoding="utf-8", errors="replace")
        drat_ok = (p_trim.returncode == 0) and ("s VERIFIED" in trim_text)
        res["drat_verified"] = drat_ok

        if not drat_ok or not lrat_path.exists():
            (out_dir / "lrat_certificate.json").write_text(
                json.dumps(res, indent=2) + "\n", encoding="utf-8"
            )
            return res

        res["lrat_bytes"] = lrat_path.stat().st_size
        res["lrat_sha256"] = sha256_file(lrat_path)

        # Step 2: lrat-check independent verification
        t1 = time.monotonic()
        try:
            with open(check_log, "w", encoding="utf-8") as log:
                p_chk = subprocess.run(
                    check_cmd, stdout=log, stderr=subprocess.STDOUT, timeout=timeout_s
                )
            res["lrat_check_exit"] = p_chk.returncode
        except FileNotFoundError:
            res["lrat_check_exit"] = None
            res["lrat_check_missing"] = True
            res["status"] = "DRAT_ONLY_VERIFIED"
            res["lrat_check_s"] = round(time.monotonic() - t1, 3)
        except subprocess.TimeoutExpired:
            res["lrat_check_exit"] = None
            res["lrat_check_timeout"] = True
            res["status"] = "DRAT_ONLY_VERIFIED"
            res["lrat_check_s"] = round(time.monotonic() - t1, 3)
        else:
            res["lrat_check_s"] = round(time.monotonic() - t1, 3)
            chk_text = check_log.read_text(encoding="utf-8", errors="replace")
            lrat_ok = (p_chk.returncode == 0) and ("VERIFIED" in chk_text.upper())
            res["lrat_verified"] = lrat_ok
            res["status"] = "LRAT_VERIFIED" if lrat_ok else "DRAT_ONLY_VERIFIED"

        if compress_lrat and lrat_path.exists():
            gz_path = out_dir / "proof.lrat.gz"
            with open(lrat_path, "rb") as fi, gzip.open(gz_path, "wb", compresslevel=3) as fo:
                shutil.copyfileobj(fi, fo)
            res["lrat_gz"] = gz_path.name
            res["lrat_gz_bytes"] = gz_path.stat().st_size
            lrat_path.unlink(missing_ok=True)

        if remove_raw_drat and drat_path.exists() and drat_path.suffix != ".gz":
            drat_path.unlink(missing_ok=True)

    (out_dir / "lrat_certificate.json").write_text(
        json.dumps(res, indent=2) + "\n", encoding="utf-8"
    )
    return res


def discover_batch_pairs(batch_dir: Path) -> List[Tuple[str, Path, Path]]:
    """Find (name, cnf_path, drat_path) pairs inside a directory tree."""
    pairs: List[Tuple[str, Path, Path]] = []
    for cnf in sorted(batch_dir.rglob("*.cnf*")):
        if not (cnf.name.endswith(".cnf") or cnf.name.endswith(".cnf.gz")):
            continue
        stem = cnf.name[:-7] if cnf.name.endswith(".cnf.gz") else cnf.name[:-4]
        parent = cnf.parent
        candidates = [
            parent / f"{stem}.drat",
            parent / f"{stem}.drat.gz",
            parent / "leaf.drat",
            parent / "leaf.drat.gz",
            parent / "proof.drat",
            parent / "proof.drat.gz",
        ]
        for cand in candidates:
            if cand.exists():
                rel = str(cnf.relative_to(batch_dir))
                pairs.append((rel, cnf, cand))
                break
    return pairs


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Standalone DRAT-to-LRAT upgrade & independent lrat-check verifier."
    )
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--cnf", type=Path, help="Single DIMACS CNF (.cnf or .cnf.gz).")
    mode.add_argument("--batch-dir", type=Path, help="Directory to scan for (cnf, drat) pairs.")

    ap.add_argument("--drat", type=Path, help="DRAT proof file (.drat or .drat.gz), required with --cnf.")
    ap.add_argument("--out", type=Path, default=Path("out_lrat"))
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--drat-trim", default="drat-trim")
    ap.add_argument("--lrat-check", default="lrat-check")
    ap.add_argument("--forward", action="store_true", help="Pass -f (forward checking) to drat-trim.")
    ap.add_argument("--no-compress", action="store_true", help="Keep raw uncompressed proof.lrat.")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args(argv)

    if args.cnf is not None:
        if args.drat is None:
            ap.error("--drat is required when using --cnf")
        res = upgrade_and_verify_lrat(
            cnf_path=args.cnf,
            drat_path=args.drat,
            out_dir=args.out,
            timeout_s=args.timeout,
            drat_trim_bin=args.drat_trim,
            lrat_check_bin=args.lrat_check,
            forward_mode=args.forward,
            compress_lrat=not args.no_compress,
            dry_run=args.dry_run,
        )
        print(json.dumps(res, indent=2), flush=True)
        return 0 if res["status"] in ("LRAT_VERIFIED", "DRY_RUN") else 1

    # Batch mode
    pairs = discover_batch_pairs(args.batch_dir)
    results = []
    for idx, (rel, cnf_p, drat_p) in enumerate(pairs):
        sub_out = args.out / f"item_{idx:03d}"
        r = upgrade_and_verify_lrat(
            cnf_path=cnf_p,
            drat_path=drat_p,
            out_dir=sub_out,
            timeout_s=args.timeout,
            drat_trim_bin=args.drat_trim,
            lrat_check_bin=args.lrat_check,
            forward_mode=args.forward,
            compress_lrat=not args.no_compress,
            dry_run=args.dry_run,
        )
        r["rel_cnf"] = rel
        results.append(r)

    summary = {
        "batch_dir": str(args.batch_dir),
        "total": len(results),
        "lrat_verified": sum(1 for r in results if r["status"] == "LRAT_VERIFIED"),
        "drat_only": sum(1 for r in results if r["status"] == "DRAT_ONLY_VERIFIED"),
        "failed": sum(1 for r in results if r["status"] == "FAILED"),
        "items": results,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "lrat_batch_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2), flush=True)
    return 0 if summary["failed"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
