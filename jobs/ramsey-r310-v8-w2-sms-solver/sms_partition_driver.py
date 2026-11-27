#!/usr/bin/env python3
"""
SMS (`smsg`) Partition Driver + Proof-First Symmetry-Breaking Clause Harvester
for Ramsey R(3,10) V8 (Wave 2 Subagent 5).

Features:
  - Exact 1-based lexicographical undirected edge variable bijection for n vertices
    (verified to match `lean_cnf_sms.py`: pairs = combinations(range(40), 2)).
  - PartitionMapper supporting canonical contiguous partitions [[0], [1], X, Y, T]
    as well as arbitrary vertex-partition remapping and exact inverse unremapping.
  - Exact `smsg` CLI invocation matching container `math-compute-sat` (`smsg --help`):
      -v / --vertices, --dimacs, --initial-partition, --frequency, --cutoff,
      --sym-break-clauses, --hide-graphs, --colex-ordering, --no-SMS.
  - Automatic first-invocation syntax probing for `--initial-partition`
    (space-separated `1 1 5 8 25` vs comma-separated `1,1,5,8,25` vs repeated flags).
  - Two modes:
      * `solve`: invoke `smsg` directly (still recording `--sym-break-clauses`).
      * `harvest-and-certify`: run `smsg` to harvest symmetry-breaking clauses,
        merge them into the base SMS-invariant CNF, and certify UNSAT with
        Kissat + `drat-trim -L` + `lrat-check` (via `lrat_upgrade_runner.py`).
"""

from __future__ import annotations

import argparse
import hashlib
import json
try:
    import resource
except ImportError:
    resource = None
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

HERE = Path(__file__).resolve().parent
AGENT3_DIR = HERE.parent / "ramsey-r310-v8-agent3-encoding"

DEFAULT_N = 40
DEFAULT_FREQUENCY = 30
DEFAULT_CUTOFF = 200000


def num_edge_vars(n: int) -> int:
    """Return number of undirected edges C(n, 2)."""
    if n < 2:
        raise ValueError(f"n must be >= 2, got {n}")
    return n * (n - 1) // 2


def edge_var(u: int, v: int, n: int = DEFAULT_N) -> int:
    """1-based lex edge variable for undirected edge {u, v} on vertices 0..n-1.

    Matches `itertools.combinations(range(n), 2)` 1-indexed (identical to lean_cnf_sms.py).
    """
    if u == v:
        raise ValueError(f"Self-loop not allowed: ({u}, {v})")
    if u > v:
        u, v = v, u
    if not (0 <= u < v < n):
        raise ValueError(f"Edge ({u}, {v}) out of range for n={n}")
    return u * n - (u * (u + 1)) // 2 + (v - u)


def var_to_edge(var: int, n: int = DEFAULT_N) -> Tuple[int, int]:
    """Inverse of `edge_var`: map 1-based variable id in 1..C(n,2) to (u, v)."""
    m = num_edge_vars(n)
    if not (1 <= var <= m):
        raise ValueError(f"Edge variable {var} out of range 1..{m}")
    # Binary search for u such that row_start(u) < var <= row_start(u+1)
    lo, hi = 0, n - 2
    while lo <= hi:
        mid = (lo + hi) // 2
        row_start = mid * n - (mid * (mid + 1)) // 2
        row_len = n - 1 - mid
        if var <= row_start:
            hi = mid - 1
        elif var > row_start + row_len:
            lo = mid + 1
        else:
            return (mid, mid + (var - row_start))
    raise RuntimeError(f"Failed to invert edge variable {var} for n={n}")


def canonical_ramsey_partition(d: int, q: int, n: int = DEFAULT_N) -> List[List[int]]:
    """Return canonical V8 vertex partition [[0], [1], X, Y, T] for parameters (d, q, n)."""
    if d < 2 or q < 2 or d + q >= n:
        raise ValueError(f"Invalid Ramsey parameters d={d}, q={q}, n={n}")
    x_block = list(range(2, d + 1))
    y_block = list(range(d + 1, d + q))
    t_block = list(range(d + q, n))
    return [[0], [1], x_block, y_block, t_block]


@dataclass(frozen=True)
class PartitionMapper:
    """Bijection mapping arbitrary vertex partition blocks to contiguous 0..n-1 order."""

    n: int
    blocks: Tuple[Tuple[int, ...], ...]
    old_to_new: Tuple[int, ...]
    new_to_old: Tuple[int, ...]
    partition_sizes: Tuple[int, ...]
    is_identity: bool

    @classmethod
    def from_blocks(cls, blocks: Sequence[Sequence[int]], n: Optional[int] = None) -> "PartitionMapper":
        if not blocks:
            raise ValueError("Partition blocks must be non-empty")
        flat: List[int] = []
        norm_blocks: List[Tuple[int, ...]] = []
        for idx, b in enumerate(blocks):
            bt = tuple(int(v) for v in b)
            if not bt:
                raise ValueError(f"Partition block {idx} is empty")
            norm_blocks.append(bt)
            flat.extend(bt)
        inferred_n = len(flat) if n is None else n
        if len(flat) != inferred_n:
            raise ValueError(f"Partition covers {len(flat)} vertices, expected {inferred_n}")
        if set(flat) != set(range(inferred_n)):
            missing = sorted(set(range(inferred_n)) - set(flat))
            extra = sorted(set(flat) - set(range(inferred_n)))
            raise ValueError(
                f"Partition is not a bijection on 0..{inferred_n - 1} "
                f"(missing={missing[:5]}, extra={extra[:5]}, duplicates={len(flat) - len(set(flat))})"
            )
        new_to_old = tuple(flat)
        old_to_new_list = [0] * inferred_n
        for new_v, old_v in enumerate(new_to_old):
            old_to_new_list[old_v] = new_v
        old_to_new = tuple(old_to_new_list)
        sizes = tuple(len(b) for b in norm_blocks)
        is_id = all(old_to_new[i] == i for i in range(inferred_n))
        return cls(
            n=inferred_n,
            blocks=tuple(norm_blocks),
            old_to_new=old_to_new,
            new_to_old=new_to_old,
            partition_sizes=sizes,
            is_identity=is_id,
        )

    @classmethod
    def from_sizes(cls, sizes: Sequence[int]) -> "PartitionMapper":
        """Build an identity PartitionMapper from contiguous block sizes [p1, p2, ...]."""
        blocks: List[List[int]] = []
        cur = 0
        for s in sizes:
            si = int(s)
            if si <= 0:
                raise ValueError(f"Partition size must be positive, got {s}")
            blocks.append(list(range(cur, cur + si)))
            cur += si
        return cls.from_blocks(blocks, n=cur)

    def remap_lit(self, lit: int) -> int:
        """Map a DIMACS literal from original vertex numbering to SMS contiguous numbering."""
        if lit == 0:
            raise ValueError("Zero is not a valid DIMACS literal")
        if self.is_identity:
            return lit
        v = abs(lit)
        m = num_edge_vars(self.n)
        if v > m:
            return lit
        u_old, w_old = var_to_edge(v, self.n)
        new_v = edge_var(self.old_to_new[u_old], self.old_to_new[w_old], self.n)
        return new_v if lit > 0 else -new_v

    def unremap_lit(self, lit: int) -> int:
        """Inverse of `remap_lit`: map from SMS numbering back to original numbering."""
        if lit == 0:
            raise ValueError("Zero is not a valid DIMACS literal")
        if self.is_identity:
            return lit
        v = abs(lit)
        m = num_edge_vars(self.n)
        if v > m:
            return lit
        u_new, w_new = var_to_edge(v, self.n)
        old_v = edge_var(self.new_to_old[u_new], self.new_to_old[w_new], self.n)
        return old_v if lit > 0 else -old_v

    def remap_clause(self, clause: Sequence[int]) -> List[int]:
        return [self.remap_lit(lit) for lit in clause]

    def unremap_clause(self, clause: Sequence[int]) -> List[int]:
        return [self.unremap_lit(lit) for lit in clause]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_dimacs(path: Path) -> Tuple[int, List[List[int]]]:
    """Read a DIMACS CNF file and return (num_vars, clauses)."""
    num_vars = 0
    clauses: List[List[int]] = []
    cur: List[int] = []
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                parts = line.split()
                if len(parts) >= 4 and parts[1] == "cnf":
                    num_vars = max(num_vars, int(parts[2]))
                continue
            for tok in line.split():
                lit = int(tok)
                if lit == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    num_vars = max(num_vars, abs(lit))
                    cur.append(lit)
    if cur:
        clauses.append(cur)
    return num_vars, clauses


def write_dimacs(
    path: Path,
    num_vars: int,
    clauses: Sequence[Sequence[int]],
    comments: Optional[Sequence[str]] = None,
) -> None:
    """Write a clean DIMACS CNF file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        if comments:
            for c in comments:
                f.write(f"c {c}\n")
        f.write(f"p cnf {num_vars} {len(clauses)}\n")
        for cl in clauses:
            if cl:
                f.write(" ".join(str(x) for x in cl) + " 0\n")
            else:
                f.write("0\n")


def parse_sym_break_clauses(
    sb_path: Path,
    max_var: Optional[int] = None,
    deduplicate: bool = True,
) -> List[List[int]]:
    """Parse symmetry-breaking clauses written by `smsg --sym-break-clauses <file>`.

    Each clause line consists of space-separated non-zero integers terminated by 0.
    Validates that all literals are non-zero and within `1..max_var` if `max_var` is set.
    """
    if not sb_path.exists():
        return []
    clauses: List[List[int]] = []
    seen = set()
    cur: List[int] = []
    with open(sb_path, "r", encoding="utf-8", errors="replace") as f:
        for lineno, raw in enumerate(f, 1):
            line = raw.strip()
            if not line or line.startswith("c") or line.startswith("p "):
                continue
            for tok in line.split():
                try:
                    lit = int(tok)
                except ValueError as exc:
                    raise ValueError(
                        f"Non-integer token {tok!r} in {sb_path}:{lineno}"
                    ) from exc
                if lit == 0:
                    if not cur:
                        continue
                    if max_var is not None:
                        for x in cur:
                            if abs(x) > max_var:
                                raise ValueError(
                                    f"Symmetry-breaking literal {x} exceeds max_var={max_var} "
                                    f"in {sb_path}:{lineno}"
                                )
                    key = tuple(sorted(set(cur), key=lambda x: (abs(x), x)))
                    if not deduplicate or key not in seen:
                        seen.add(key)
                        clauses.append(list(key))
                    cur = []
                else:
                    cur.append(lit)
    if cur:
        if max_var is not None:
            for x in cur:
                if abs(x) > max_var:
                    raise ValueError(f"Symmetry-breaking literal {x} exceeds max_var={max_var}")
        key = tuple(sorted(set(cur), key=lambda x: (abs(x), x)))
        if not deduplicate or key not in seen:
            clauses.append(list(key))
    return clauses


def merge_cnf_with_sym_break(
    base_cnf_path: Path,
    sb_path: Path,
    out_cnf_path: Path,
    n: int = DEFAULT_N,
    mapper: Optional[PartitionMapper] = None,
) -> dict:
    """Merge base DIMACS CNF with harvested symmetry-breaking clauses into `out_cnf_path`."""
    nv, base_clauses = read_dimacs(base_cnf_path)
    edge_max = num_edge_vars(n)
    sb_clauses = parse_sym_break_clauses(sb_path, max_var=edge_max, deduplicate=True)
    if mapper is not None and not mapper.is_identity:
        sb_clauses = [mapper.unremap_clause(cl) for cl in sb_clauses]
    merged = list(base_clauses) + sb_clauses
    write_dimacs(
        out_cnf_path,
        nv,
        merged,
        comments=[
            f"base_cnf={base_cnf_path.name} base_clauses={len(base_clauses)}",
            f"sym_break_file={sb_path.name} sb_clauses={len(sb_clauses)}",
        ],
    )
    return {
        "num_vars": nv,
        "base_clauses": len(base_clauses),
        "sb_clauses": len(sb_clauses),
        "total_clauses": len(merged),
        "out_cnf": str(out_cnf_path),
    }


def build_smsg_cmd(
    dimacs_path: Path,
    n: int,
    partition_sizes: Sequence[int],
    sym_break_path: Optional[Path] = None,
    frequency: int = DEFAULT_FREQUENCY,
    cutoff: int = DEFAULT_CUTOFF,
    partition_style: str = "space",
    hide_graphs: bool = True,
    all_graphs: bool = False,
    colex_ordering: bool = False,
    no_sms: bool = False,
    smsg_bin: str = "smsg",
) -> List[str]:
    """Construct exact `smsg` CLI command matching container `smsg --help`."""
    if sum(int(x) for x in partition_sizes) != n:
        raise ValueError(
            f"Sum of partition_sizes {list(partition_sizes)} = {sum(partition_sizes)} != n={n}"
        )
    if partition_style not in ("space", "comma", "repeat"):
        raise ValueError(f"Unsupported partition_style: {partition_style!r}")

    cmd: List[str] = [
        smsg_bin,
        "--vertices",
        str(n),
        "--dimacs",
        str(dimacs_path),
        "--frequency",
        str(frequency),
        "--cutoff",
        str(cutoff),
    ]
    if partition_style == "space":
        cmd.append("--initial-partition")
        cmd.extend(str(int(p)) for p in partition_sizes)
    elif partition_style == "comma":
        cmd.extend(["--initial-partition", ",".join(str(int(p)) for p in partition_sizes)])
    elif partition_style == "repeat":
        for p in partition_sizes:
            cmd.extend(["--initial-partition", str(int(p))])

    if sym_break_path is not None:
        cmd.extend(["--sym-break-clauses", str(sym_break_path)])
    if hide_graphs:
        cmd.append("--hide-graphs")
    if all_graphs:
        cmd.append("--all-graphs")
    if colex_ordering:
        cmd.append("--colex-ordering")
    if no_sms:
        cmd.append("--no-SMS")
    return cmd


_CACHED_PARTITION_STYLE: Optional[str] = None
_CLI_ERROR_MARKERS = (
    "unrecognised option",
    "unrecognized option",
    "unknown option",
    "invalid",
    "could not parse",
    "parse error",
    "error:",
    "too many positional",
    "argument is required",
)


def probe_initial_partition_style(
    smsg_bin: str = "smsg",
    candidates: Sequence[str] = ("space", "comma", "repeat"),
    timeout_s: float = 10.0,
) -> Tuple[str, List[dict]]:
    """Automatically probe `smsg --initial-partition` syntax (space vs comma vs repeat).

    Runs a trivial 4-vertex UNSAT DIMACS CNF (6 edge vars, unit contradiction) so
    invocation finishes in <0.1s and verifies which CLI syntax `smsg` accepts.
    """
    global _CACHED_PARTITION_STYLE
    if _CACHED_PARTITION_STYLE is not None:
        return _CACHED_PARTITION_STYLE, [{"cached": _CACHED_PARTITION_STYLE}]

    probe_log: List[dict] = []
    with tempfile.TemporaryDirectory(prefix="smsg_probe_") as td:
        td_path = Path(td)
        tiny_cnf = td_path / "tiny_unsat.cnf"
        write_dimacs(tiny_cnf, 6, [[1], [-1]], comments=["tiny 4-vertex probe"])
        for style in candidates:
            sb_tmp = td_path / f"sb_{style}.clauses"
            cmd = build_smsg_cmd(
                dimacs_path=tiny_cnf,
                n=4,
                partition_sizes=[1, 1, 2],
                sym_break_path=sb_tmp,
                frequency=30,
                cutoff=200000,
                partition_style=style,
                hide_graphs=True,
                smsg_bin=smsg_bin,
            )
            try:
                proc = subprocess.run(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    timeout=timeout_s,
                )
                out = proc.stdout or ""
                out_low = out.lower()
                has_cli_err = any(m in out_low for m in _CLI_ERROR_MARKERS)
                entry = {
                    "style": style,
                    "cmd": cmd,
                    "returncode": proc.returncode,
                    "has_cli_err": has_cli_err,
                    "output_head": out[:300],
                }
                probe_log.append(entry)
                # Accept if return code is 0, 10 (SAT), or 20 (UNSAT) and no CLI error text
                if proc.returncode in (0, 10, 20) and not has_cli_err:
                    _CACHED_PARTITION_STYLE = style
                    return style, probe_log
            except FileNotFoundError as exc:
                probe_log.append({"style": style, "cmd": cmd, "error": str(exc)})
                raise
            except subprocess.TimeoutExpired:
                probe_log.append({"style": style, "cmd": cmd, "error": "timeout"})
    raise RuntimeError(
        f"All `--initial-partition` styles {list(candidates)} failed probe: {probe_log}"
    )


def run_smsg(
    dimacs_path: Path,
    out_dir: Path,
    n: int,
    partition_sizes: Sequence[int],
    seconds: int = 300,
    frequency: int = DEFAULT_FREQUENCY,
    cutoff: int = DEFAULT_CUTOFF,
    partition_style: str = "auto",
    all_graphs: bool = False,
    colex_ordering: bool = False,
    no_sms: bool = False,
    smsg_bin: str = "smsg",
    dry_run: bool = False,
) -> dict:
    """Execute `smsg` with `--sym-break-clauses` and return structured metadata."""
    out_dir.mkdir(parents=True, exist_ok=True)
    sb_path = out_dir / "sym_break.clauses"
    log_path = out_dir / "smsg.log"

    probe_log: List[dict] = []
    if partition_style == "auto":
        if dry_run:
            chosen_style = "space"
        else:
            chosen_style, probe_log = probe_initial_partition_style(smsg_bin=smsg_bin)
    else:
        chosen_style = partition_style

    cmd = build_smsg_cmd(
        dimacs_path=dimacs_path,
        n=n,
        partition_sizes=partition_sizes,
        sym_break_path=sb_path,
        frequency=frequency,
        cutoff=cutoff,
        partition_style=chosen_style,
        hide_graphs=True,
        all_graphs=all_graphs,
        colex_ordering=colex_ordering,
        no_sms=no_sms,
        smsg_bin=smsg_bin,
    )

    if dry_run:
        return {
            "status": "DRY_RUN",
            "partition_style": chosen_style,
            "cmd": cmd,
            "sym_break_path": str(sb_path),
        }

    t0 = time.monotonic()
    timed_out = False
    returncode: Optional[int] = None
    with open(log_path, "w", encoding="utf-8") as log:
        try:
            proc = subprocess.run(
                cmd,
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=seconds,
            )
            returncode = proc.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
    wall_s = round(time.monotonic() - t0, 3)

    sb_clauses = parse_sym_break_clauses(sb_path, max_var=num_edge_vars(n), deduplicate=True)
    log_tail = log_path.read_text(encoding="utf-8", errors="replace")[-1000:] if log_path.exists() else ""

    status = "TIMEOUT" if timed_out else "COMPLETED"
    if not timed_out:
        low = log_tail.lower()
        if "unsatisfiable" in low or "0 solutions" in low or "found 0" in low or returncode == 20:
            status = "SMSG_UNSAT"
        elif returncode not in (0, 10, 20):
            status = f"SMSG_EXIT_{returncode}"

    return {
        "status": status,
        "returncode": returncode,
        "timed_out": timed_out,
        "wall_s": wall_s,
        "partition_style": chosen_style,
        "probe_log": probe_log,
        "cmd": cmd,
        "sym_break_path": str(sb_path),
        "sym_break_clauses": len(sb_clauses),
        "sym_break_sha256": sha256_file(sb_path) if sb_path.exists() else None,
        "log_path": str(log_path),
    }


def run_kissat_and_lrat(
    cnf_path: Path,
    out_dir: Path,
    seconds: int = 900,
    kissat_bin: str = "kissat",
    drat_trim_bin: str = "drat-trim",
    lrat_check_bin: str = "lrat-check",
    max_fsize_mb: int = 2048,
    dry_run: bool = False,
) -> dict:
    """Solve `cnf_path` with Kissat (emitting DRAT) and upgrade/verify to LRAT."""
    out_dir.mkdir(parents=True, exist_ok=True)
    drat_path = out_dir / "proof.drat"
    kissat_log = out_dir / "kissat.log"
    kissat_cmd = [kissat_bin, f"--time={seconds}", str(cnf_path), str(drat_path)]

    if dry_run:
        return {
            "status": "DRY_RUN",
            "kissat_cmd": kissat_cmd,
            "drat_path": str(drat_path),
        }

    def _cap_fsize() -> None:
        if resource is not None:
            lim = max_fsize_mb * 1024 * 1024
            resource.setrlimit(resource.RLIMIT_FSIZE, (lim, lim))

    t0 = time.monotonic()
    timed_out = False
    returncode: Optional[int] = None
    with open(kissat_log, "w", encoding="utf-8") as log:
        try:
            proc = subprocess.run(
                kissat_cmd,
                stdout=log,
                stderr=subprocess.STDOUT,
                timeout=seconds + 30,
                preexec_fn=_cap_fsize if resource is not None else None,
            )
            returncode = proc.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
    kissat_s = round(time.monotonic() - t0, 3)

    res: dict = {
        "kissat_cmd": kissat_cmd,
        "kissat_exit": returncode,
        "kissat_s": kissat_s,
        "timed_out": timed_out,
        "certificate": "NOT_VERIFIED",
    }

    if returncode == 20 and drat_path.exists():
        # Import sibling lrat_upgrade_runner cleanly
        if str(HERE) not in sys.path:
            sys.path.insert(0, str(HERE))
        import lrat_upgrade_runner as lur

        lrat_res = lur.upgrade_and_verify_lrat(
            cnf_path=cnf_path,
            drat_path=drat_path,
            out_dir=out_dir,
            timeout_s=max(seconds, 600),
            drat_trim_bin=drat_trim_bin,
            lrat_check_bin=lrat_check_bin,
            compress_lrat=True,
            remove_raw_drat=True,
        )
        res["lrat"] = lrat_res
        res["certificate"] = lrat_res.get("status", "NOT_VERIFIED")
    elif returncode == 10:
        res["certificate"] = "SAT_MODEL_FOUND"
        drat_path.unlink(missing_ok=True)
    else:
        drat_path.unlink(missing_ok=True)
    return res


def _load_task_and_build_cnf(
    tasks_json: Path,
    task_id: str,
    out_dir: Path,
    include_xy_codeg: bool = True,
) -> Tuple[Path, List[int], dict]:
    if str(AGENT3_DIR) not in sys.path:
        sys.path.insert(0, str(AGENT3_DIR))
    import lean_cnf_sms as lc

    all_tasks = json.loads(tasks_json.read_text(encoding="utf-8"))
    if task_id not in all_tasks:
        raise KeyError(f"Task {task_id!r} not found in {tasks_json}")
    task = all_tasks[task_id]
    z, meta = lc.build_lean_cnf(
        task,
        sym_mode="sms",
        include_xy_codeg=include_xy_codeg,
    )
    cnf_path = out_dir / f"{task_id}.sms.cnf"
    z.write_dimacs(cnf_path)
    return cnf_path, list(meta["sms_partition_sizes"]), meta


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="SMS (`smsg`) partition driver + symmetry-breaking clause harvester + Kissat/LRAT certifier."
    )
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--dimacs", type=Path, help="Input DIMACS CNF file.")
    src.add_argument("--tasks-json", type=Path, help="Path to V8 all_tasks.json.")
    ap.add_argument("--task", type=str, help="Task ID in --tasks-json (required with --tasks-json).")
    ap.add_argument("--vertices", type=int, default=DEFAULT_N, help="Number of graph vertices (default: 40).")
    ap.add_argument(
        "--initial-partition",
        type=int,
        nargs="+",
        help="Integer partition sizes summing to --vertices (auto-derived if --tasks-json is used).",
    )
    ap.add_argument(
        "--mode",
        choices=["solve", "harvest-and-certify"],
        default="harvest-and-certify",
        help="Run `smsg` directly or harvest symmetry-breaking clauses for Kissat + drat-trim + lrat-check.",
    )
    ap.add_argument("--frequency", type=int, default=DEFAULT_FREQUENCY)
    ap.add_argument("--cutoff", type=int, default=DEFAULT_CUTOFF)
    ap.add_argument(
        "--partition-style",
        choices=["auto", "space", "comma", "repeat"],
        default="auto",
        help="CLI format for --initial-partition (auto probes space vs comma vs repeat).",
    )
    ap.add_argument("--smsg-seconds", type=int, default=240, help="Wall-clock budget for smsg (seconds).")
    ap.add_argument("--kissat-seconds", type=int, default=900, help="Wall-clock budget for Kissat + LRAT (seconds).")
    ap.add_argument("--colex-ordering", action="store_true")
    ap.add_argument("--no-sms", action="store_true")
    ap.add_argument("--all-graphs", action="store_true")
    ap.add_argument("--out", type=Path, default=Path("out_sms"))
    ap.add_argument("--dry-run", action="store_true", help="Validate inputs and print planned commands without executing.")
    args = ap.parse_args(argv)

    args.out.mkdir(parents=True, exist_ok=True)
    build_meta: dict = {}

    if args.tasks_json is not None:
        if not args.task:
            ap.error("--task is required when using --tasks-json")
        cnf_path, part_sizes, build_meta = _load_task_and_build_cnf(
            args.tasks_json, args.task, args.out
        )
        n = DEFAULT_N
    else:
        cnf_path = args.dimacs
        n = args.vertices
        if not args.initial_partition:
            ap.error("--initial-partition is required when using --dimacs")
        part_sizes = list(args.initial_partition)

    mapper = PartitionMapper.from_sizes(part_sizes)
    if mapper.n != n:
        raise ValueError(f"Partition sum {mapper.n} != --vertices {n}")

    summary: dict = {
        "mode": args.mode,
        "vertices": n,
        "partition_sizes": list(mapper.partition_sizes),
        "base_cnf": str(cnf_path),
        "build_meta": build_meta,
    }

    if build_meta.get("unsat_by_prefilter"):
        summary["status"] = "UNSAT_BY_V8_KONIG_PREFILTER"
        (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(summary, indent=2), flush=True)
        return 0

    smsg_res = run_smsg(
        dimacs_path=cnf_path,
        out_dir=args.out,
        n=n,
        partition_sizes=mapper.partition_sizes,
        seconds=args.smsg_seconds,
        frequency=args.frequency,
        cutoff=args.cutoff,
        partition_style=args.partition_style,
        all_graphs=args.all_graphs,
        colex_ordering=args.colex_ordering,
        no_sms=args.no_sms,
        dry_run=args.dry_run,
    )
    summary["smsg"] = smsg_res

    if args.mode == "harvest-and-certify":
        merged_cnf = args.out / "merged_with_sms.cnf"
        if args.dry_run:
            summary["merge"] = {"status": "DRY_RUN", "out_cnf": str(merged_cnf)}
            summary["certify"] = run_kissat_and_lrat(
                merged_cnf, args.out, seconds=args.kissat_seconds, dry_run=True
            )
        else:
            sb_path = Path(smsg_res["sym_break_path"])
            merge_meta = merge_cnf_with_sym_break(cnf_path, sb_path, merged_cnf, n=n, mapper=mapper)
            summary["merge"] = merge_meta
            summary["certify"] = run_kissat_and_lrat(
                merged_cnf, args.out, seconds=args.kissat_seconds, dry_run=False
            )

    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
