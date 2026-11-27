"""Validate the Hadamard obligation graph and list research tasks ready to claim."""

import argparse
from datetime import date
from graphlib import CycleError, TopologicalSorter
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


NODE_FIELDS = {
    "id", "status", "scope", "statement", "all_of", "any_of",
    "evidence", "composition", "role",
}
TASK_FIELDS = {
    "id", "node", "needs", "uses", "mode", "priority", "claim", "title",
    "inputs", "deliverable", "acceptance", "fallback",
}
PROOF_STATUSES = {"PROVED", "PUBLISHED"}
STATUSES = PROOF_STATUSES | {"OPEN", "CHECKED"}
ROLES = {"goal", "gate", "lemma", "obligation", "diagnostic"}
ID_PATTERN = re.compile(r"[A-Z0-9]+(?:[-_][A-Z0-9]+)*")
HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON field {key!r}")
        result[key] = value
    return result


def exact_fields(item, expected, label):
    require(isinstance(item, dict), f"{label} must be an object")
    missing = expected - item.keys()
    extra = item.keys() - expected
    require(not missing and not extra,
            f"{label} has missing fields {sorted(missing)} and extra fields {sorted(extra)}")


def string(value):
    return isinstance(value, str) and bool(value.strip())


def string_list(value, label):
    require(isinstance(value, list) and all(map(string, value)), f"{label} must be a list of strings")
    require(len(set(value)) == len(value), f"{label} has duplicate entries")


def record_index(items, fields, label):
    require(isinstance(items, list), f"{label} records must be an array")
    result = {}
    for index, item in enumerate(items):
        exact_fields(item, fields, f"{label} record {index + 1}")
        identifier = item["id"]
        require(string(identifier) and ID_PATTERN.fullmatch(identifier),
                f"invalid {label} ID: {identifier!r}")
        require(identifier not in result, f"duplicate {label} ID: {identifier}")
        result[identifier] = item
    return result


def selection(value, allowed, label):
    require(string(value) and value in allowed, f"{label} must be one of {sorted(allowed)}")


def check_date(value, label):
    require(string(value), f"{label} must be an ISO date")
    try:
        parsed = date.fromisoformat(value)
    except ValueError:
        raise ValueError(f"{label} must be an ISO date") from None
    require(parsed.isoformat() == value, f"{label} must use YYYY-MM-DD")


def check_evidence(reference, directory, repo, label):
    url = urlsplit(reference)
    if url.scheme == "https":
        require(url.hostname, f"{label} has an invalid HTTPS source: {reference}")
        return
    path = Path(unquote(url.path))
    require(not url.scheme and not url.netloc and not url.query and not path.is_absolute(),
            f"{label} evidence must be a repository-relative path or HTTPS URL: {reference}")
    target = (directory / path).resolve()
    require(target.is_relative_to(repo) and target.is_file(),
            f"{label} evidence file missing or outside repository: {reference}")


def prerequisites(node):
    return node["all_of"] + node["any_of"]


def check_references(references, nodes, label):
    string_list(references, label)
    unknown = set(references) - nodes.keys()
    require(not unknown, f"{label} references unknown nodes: {', '.join(sorted(unknown))}")


def proved(node):
    return node["status"] in PROOF_STATUSES


def unmet(node, nodes):
    missing = [identifier for identifier in node["all_of"] if not proved(nodes[identifier])]
    alternatives = node["any_of"]
    if alternatives and not any(proved(nodes[identifier]) for identifier in alternatives):
        missing.append("one of (" + ", ".join(alternatives) + ")")
    return missing


def ancestors(root, nodes):
    visited = set()
    waiting = list(prerequisites(nodes[root]))
    while waiting:
        identifier = waiting.pop()
        if identifier not in visited:
            visited.add(identifier)
            waiting.extend(prerequisites(nodes[identifier]))
    return visited


def check_nodes(graph, nodes, directory, repo):
    for identifier, node in nodes.items():
        selection(node["status"], STATUSES, f"{identifier}.status")
        selection(node["role"], ROLES, f"{identifier}.role")
        for field in ("scope", "statement", "composition"):
            require(string(node[field]), f"{identifier}.{field} must be a nonempty string")
        for field in ("all_of", "any_of"):
            check_references(node[field], nodes, f"{identifier}.{field}")
        require(not set(node["all_of"]).intersection(node["any_of"]),
                f"{identifier} lists the same prerequisite in all_of and any_of")
        string_list(node["evidence"], f"{identifier}.evidence")
        if node["status"] != "OPEN":
            require(node["evidence"], f"{identifier} has {node['status']} status without evidence")
        for reference in node["evidence"]:
            check_evidence(reference, directory, repo, identifier)
        if node["status"] == "CHECKED":
            require(node["role"] == "diagnostic", f"{identifier} CHECKED status requires diagnostic role")

    try:
        tuple(TopologicalSorter({identifier: prerequisites(node)
                                for identifier, node in nodes.items()}).static_order())
    except CycleError as error:
        raise ValueError("dependency cycle: " + " -> ".join(error.args[1])) from None

    require(graph["root"] == "RESOLUTION" and {"RESOLUTION", "YES", "NO"} <= nodes.keys(),
            "the graph must contain RESOLUTION, YES and NO, with RESOLUTION as root")
    root = nodes["RESOLUTION"]
    require(root["role"] == "goal" and not root["all_of"] and set(root["any_of"]) == {"YES", "NO"},
            "RESOLUTION must be the disjunction of YES and NO")
    yes, no = ancestors("YES", nodes), ancestors("NO", nodes)
    require("NO" not in yes and "YES" not in no, "YES and NO must have independent conclusions")
    for identifier in yes | no | {"YES", "NO"}:
        require(nodes[identifier]["role"] != "diagnostic",
                f"{identifier} is diagnostic and cannot be in closure ancestry")
    for identifier in yes & no:
        require(proved(nodes[identifier]) and nodes[identifier]["role"] == "lemma",
                f"{identifier} can be shared by YES and NO only as an established lemma")

    for identifier, node in nodes.items():
        if proved(node):
            missing = unmet(node, nodes)
            require(not missing, f"{identifier} is marked established but requires {', '.join(missing)}")

    resolution = graph["resolution"]
    selection(resolution, {"OPEN", "YES", "NO"}, "resolution")
    solved = [identifier for identifier in ("YES", "NO") if proved(nodes[identifier])]
    require(len(solved) <= 1, "YES and NO cannot both be established")
    if resolution == "OPEN":
        require(root["status"] == "OPEN", "OPEN resolution requires an OPEN root")
    else:
        require(proved(root) and solved == [resolution],
                f"{resolution} resolution requires an established root and {resolution} conclusion")


def check_tasks(tasks, nodes):
    for identifier, task in tasks.items():
        for field in ("title", "inputs", "deliverable", "acceptance", "fallback"):
            require(string(task[field]), f"{identifier}.{field} must be a nonempty string")
        target = task["node"]
        require(string(target) and target in nodes, f"{identifier} targets an unknown node: {target!r}")
        selection(task["mode"], {"research", "synthesis"}, f"{identifier}.mode")
        selection(task["priority"], {"P0", "P1", "P2"}, f"{identifier}.priority")
        for field in ("needs", "uses"):
            check_references(task[field], nodes, f"{identifier}.{field}")
        require(target not in task["needs"], f"{identifier} must not require its own target")
        require(not set(task["needs"]).intersection(task["uses"]),
                f"{identifier} lists the same prerequisite in needs and uses")
        for needed in task["needs"]:
            require(nodes[needed]["role"] != "diagnostic",
                    f"{identifier} needs diagnostic {needed}; list supporting diagnostics in uses")
            require(target not in ancestors(needed, nodes),
                    f"{identifier} needs {needed}, which depends on its target {target}")
        claim = task["claim"]
        if claim is not None:
            require(isinstance(claim, dict) and {"owner", "branch"} <= claim.keys()
                    and claim.keys() <= {"owner", "branch", "claimed_at"},
                    f"{identifier}.claim must be null or a claim with owner and branch")
            require(string(claim["owner"]) and string(claim["branch"]),
                    f"{identifier}.claim needs nonempty owner and branch")
            if "claimed_at" in claim:
                check_date(claim["claimed_at"], f"{identifier}.claim.claimed_at")

    assigned = {task["node"] for task in tasks.values()}
    unassigned = {identifier for identifier, node in nodes.items()
                  if node["status"] == "OPEN" and not prerequisites(node)} - assigned
    require(not unassigned, f"open leaves without task cards: {', '.join(sorted(unassigned))}")


def check_task_headings(path, tasks):
    pattern = re.compile(r"^#{2,6}\s+(T-[A-Z0-9_-]+)(?=\s|$)", re.MULTILINE)
    headings = pattern.findall(path.read_text(encoding="utf-8"))
    require(len(set(headings)) == len(headings), "TASKS.md has duplicate task headings")
    missing = tasks.keys() - set(headings)
    extra = set(headings) - tasks.keys()
    require(not missing and not extra,
            f"TASKS.md has missing task headings {sorted(missing)} and extra headings {sorted(extra)}")


def ready_tasks(tasks, nodes):
    for identifier, task in sorted(tasks.items(), key=lambda entry: (entry[1]["priority"], entry[0])):
        target = nodes[task["node"]]
        if target["status"] != "OPEN" or task["claim"] is not None:
            continue
        if any(not proved(nodes[needed]) for needed in task["needs"]):
            continue
        if task["mode"] == "synthesis" and unmet(target, nodes):
            continue
        yield identifier, task


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dag", type=Path, default=HERE / "dag.json")
    parser.add_argument("--check-tasks", action="store_true", help="check TASKS.md heading coverage")
    args = parser.parse_args()
    try:
        path = args.dag.resolve()
        graph = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
        exact_fields(graph, {"version", "updated", "root", "resolution", "nodes", "tasks"}, "graph")
        require(type(graph["version"]) is int and graph["version"] == 1, "graph version must be 1")
        check_date(graph["updated"], "updated")
        nodes = record_index(graph["nodes"], NODE_FIELDS, "node")
        tasks = record_index(graph["tasks"], TASK_FIELDS, "task")
        check_nodes(graph, nodes, path.parent, HERE.parents[2])
        check_tasks(tasks, nodes)
        if args.check_tasks:
            check_task_headings(path.with_name("TASKS.md"), tasks)
    except (OSError, ValueError) as error:
        print(f"DAG verification failed: {error}", file=sys.stderr)
        return 1

    eligible = list(ready_tasks(tasks, nodes))
    print(f"Verified {len(nodes)} nodes and {len(tasks)} tasks. Resolution {graph['resolution']}.")
    print(f"{len(eligible)} claimable tasks:")
    for identifier, task in eligible:
        print(f"  {task['priority']} {identifier} [{task['mode']}] {task['title']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
