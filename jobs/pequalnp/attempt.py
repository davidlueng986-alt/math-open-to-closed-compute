"""One bounded, reproducible attempt; no external model calls or credentials."""
import json
import os
import pathlib
import re
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request

ROOT = pathlib.Path(os.environ["GITHUB_WORKSPACE"])
TMP = pathlib.Path(os.environ["RUNNER_TEMP"])
PUBLIC = TMP / "pnp-public"
PRIVATE = TMP / "pnp-private"
PUBLIC.mkdir(exist_ok=True)
PRIVATE.mkdir(mode=0o700, exist_ok=True)
DESK = "https://pequalnp.com/desk/"
HANDLE = "davidlueng986-alt"
REPO = ROOT / "upstream"
LEAN = REPO / "lean"

def write(name, data):
    (PUBLIC / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")

def request(endpoint, params, method="GET"):
    url = DESK + endpoint + "?" + urllib.parse.urlencode(params)
    # Use the official documented curl client. Keep the response in memory;
    # lease IDs, headers and raw error bodies are never written to public logs.
    try:
        p = subprocess.run(
            ["curl","--proto","=https","-sS","--max-time","25",
             "-X",method,"-w","\\n%{http_code}",url],
            capture_output=True, text=True, timeout=30)
        if p.returncode:
            return 0, {}
        body, code = p.stdout.rsplit("\n",1)
        status = int(code)
        try:
            data = json.loads(body)
            if isinstance(data,dict):
                if status != 200:
                    # Do not publish arbitrary server text or credentials.
                    print("Desk response: HTTP %d (JSON)" % status, flush=True)
                return status, data
        except ValueError:
            pass
        print("Desk response: HTTP %d (non-JSON)" % status, flush=True)
        return status, {}
    except (OSError, ValueError, subprocess.TimeoutExpired):
        return 0, {}


def state():
    p = PRIVATE / "assignment.json"
    return json.loads(p.read_text()) if p.exists() else {}

def beat(d):
    return request("beat", {"lease": d["lease"]["id"]}, "POST")[0]

def release(d, reason):
    return request("release", {"lease": d["lease"]["id"], "reason": reason}, "POST")[0]

def result(status, **kw):
    write("result.json", {"status": status, **kw})

def claim():
    code, d = request("next", {"handle": HANDLE, **({"hard": "1"} if os.environ.get("HARD") == "true" else {})})
    if code != 200 or not d.get("gap") or not d.get("lease"):
        result("no_assignment", http_status=code)
        return
    g = d["gap"]
    # Lease credentials never enter logs, repository files, or artifacts.
    token = str(d["lease"]["id"])
    print("::add-mask::" + token, flush=True)
    p = PRIVATE / "assignment.json"
    p.write_text(json.dumps(d))
    p.chmod(0o600)
    public = {k:g[k] for k in ("id","file","module","title","statement","imports","context","sketch","dead","refutation","unlocks","shard_spec") if k in g}
    public.update({k:d[k] for k in ("shard","shards") if k in d})
    public["upstream_commit"] = subprocess.check_output(["git","rev-parse","HEAD"], cwd=REPO, text=True).strip()
    public["lean_toolchain"] = (LEAN/"lean-toolchain").read_text().strip()
    write("assignment.json", public)
    print("Claimed " + str(g.get("id", ""))[:80], flush=True)

TACTICS = [
    "exact?",
    "solve | rfl | assumption | trivial | decide | omega | norm_num | positivity | ring | linear_combination",
    "aesop",
    "intros\n  first | (rfl; done) | (simp_all; done) | (omega; done) | (norm_num; done) | (linarith; done) | (nlinarith; done)",
    "intros\n  aesop",
    "intros\n  exact?",
    "intros\n  grind",
    "intros\n  simp_all <;> first | omega | ring | norm_num | linarith | aesop",
    "intros\n  first | (fun_prop; done) | (positivity; done) | (exact?; done) | (omega; done)",
]

def prove():
    d = state()
    if not d:
        return
    g = d["gap"]
    gid, path, module = g["id"], g["file"], g["module"]
    statement = g["statement"]
    imports = g.get("imports") or []
    if (not re.fullmatch(r"L-[a-z]+-\d+",gid)
        or not re.fullmatch(r"lean/PEqualNP/Outside/L_[a-z0-9_]+\.lean",path)
        or not re.fullmatch(r"PEqualNP\.Outside\.L_[a-z0-9_]+",module)
        or any(not re.fullmatch(r"[A-Za-z0-9_.]+",m) for m in imports)
        or len(statement)>16000
        or re.search(r'["#]|\b(?:sorry|axiom|native_decide|initialize|macro|elab|syntax|notation|attribute|import)\b',statement)):
        result("manual_review_required")
        return
    if "shard" in d:
        result("search_shard_requires_specialized_program")
        return
    stop = threading.Event()
    lost = threading.Event()
    def heartbeat():
        while not stop.wait(9*60):
            if beat(d) == 410:
                lost.set()
                return
    thread = threading.Thread(target=heartbeat,daemon=True)
    thread.start()
    try:
        if beat(d) != 200:
            result("lease_unavailable")
            return
        proof = REPO / path
        if proof.exists():
            result("path_already_exists")
            return
        proof.parent.mkdir(parents=True, exist_ok=True)
        prefix = "import Mathlib\n" + "".join("import "+m+"\n" for m in imports if m!="Mathlib")
        prefix += "\nset_option maxHeartbeats 800000 in\ntheorem "+module+" : "+statement+" := by\n  "
        # Build only permitted dependency modules before trying the exact statement.
        def run(args, seconds):
            try:
                p=subprocess.run(args, cwd=LEAN, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=seconds)
                return p.returncode,p.stdout[-16000:]
            except subprocess.TimeoutExpired:
                return 124,"timeout"
        if imports:
            rc, log = run(["lake","build",*imports], 480)
            if rc:
                result("dependency_build_failed",exit_code=rc)
                (PUBLIC/"dependency.log").write_text(log)
                return
        for i, tactic in enumerate(TACTICS):
            if lost.is_set():
                result("lease_withdrawn")
                return
            candidate = prefix+tactic+"\n"
            proof.write_text(candidate)
            rc, log=run(["lake","env","lean","-DwarningAsError=true",str(proof)],60)
            (PUBLIC/("try-%02d.log"%i)).write_text(log)
            if rc:
                continue
            # A separate audit file may contain a print command; the submission never does.
            audit=LEAN/"PnpAudit.lean"
            audit.write_text(candidate+"\n#print axioms "+module+"\n")
            rc, log=run(["lake","env","lean","-DwarningAsError=true",str(audit)],90)
            audit.unlink(missing_ok=True)
            (PUBLIC/"axioms.log").write_text(log)
            if rc or "sorryAx" in log:
                continue
            if "depends on axioms:" in log:
                match=re.search(r"depends on axioms:\s*\[([^\]]*)\]", log)
                if not match or set(x.strip() for x in match.group(1).split(",") if x.strip())-{"propext","Classical.choice","Quot.sound"}:
                    continue
            elif "does not depend on any axioms" not in log:
                continue
            rc, log=run(["lake","build",module],180)
            (PUBLIC/"build.log").write_text(log)
            if rc:
                continue
            if beat(d)!=200:
                result("lease_withdrawn")
                return
            (PUBLIC/"proof.lean").write_text(candidate)
            result("local_kernel_checked",gap=gid,module=module,attempt=i,upstream_acceptance=False)
            return
        result("tactic_search_exhausted",gap=gid)
    finally:
        stop.set()
        thread.join(timeout=1)

def finish():
    d=state()
    if not d:
        return
    try:
        if not (PUBLIC/"proof.lean").exists():
            release(d,"out_of_time")
            return
        # Do not pretend that a local Lean pass is an upstream submission.
        # Keep lease available briefly for the human/connector to create the PR.
        gap=d["gap"]["id"]
        for i in range(8):
            if i:
                time.sleep(60)
            q=urllib.parse.urlencode({"state":"open","head":HANDLE+":"+gap})
            url="https://api.github.com/repos/open-goat/pequalnp-proofs/pulls?"+q
            try:
                with urllib.request.urlopen(urllib.request.Request(url,headers={"User-Agent":"pequalnp-compute"}),timeout=15) as r:
                    prs=json.load(r)
                if prs:
                    release(d,"submitted")
                    return
            except (OSError,ValueError):
                pass
            if beat(d)==410:
                return
        release(d,"out_of_time")
    finally:
        (PRIVATE/"assignment.json").unlink(missing_ok=True)

if __name__=="__main__":
    {"claim":claim,"prove":prove,"finish":finish}[sys.argv[1]]()
