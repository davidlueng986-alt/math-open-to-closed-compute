import json
import hashlib
import os
import re
import sys

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    log_path = sys.argv[1]
    lean_path = sys.argv[2]
    out_json = sys.argv[3]

    with open(log_path, "r", encoding="utf-8") as f:
        text = f.read()

    allowed = {"propext", "Classical.choice", "Quot.sound"}
    axioms = {}
    pattern = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        re.MULTILINE | re.DOTALL,
    )
    for m in pattern.finditer(text):
        name = m.group(1)
        ax_str = m.group(2)
        if ax_str is None:
            ax_list = []
        else:
            ax_list = [a.strip() for a in ax_str.split(",") if a.strip()]
        axioms[name] = sorted(ax_list)

    if not axioms:
        print("ERROR: No axiom lines parsed from Lean output!", file=sys.stderr)
        sys.exit(1)

    bad = {}
    for name, ax_list in axioms.items():
        disallowed = [a for a in ax_list if a not in allowed]
        if disallowed:
            bad[name] = disallowed

    with open(lean_path, "r", encoding="utf-8") as f:
        src = f.read()
    if re.search(r"\bsorry\b", src) or re.search(r"\badmit\b", src) or re.search(r"\bnative_decide\b", src):
        print("ERROR: Forbidden token (sorry/admit/native_decide) found in source!", file=sys.stderr)
        sys.exit(1)

    if bad:
        print(f"ERROR: Disallowed axioms detected: {bad}", file=sys.stderr)
        sys.exit(1)

    report = {
        "status": "PASS",
        "module": "Wave7Agent1Girth5Adjusters",
        "theorem_count": len(axioms),
        "axioms": axioms,
        "source_sha256": {os.path.basename(lean_path): sha256_file(lean_path)},
    }
    os.makedirs(os.path.dirname(out_json), exist_ok=True)
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
    print(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
