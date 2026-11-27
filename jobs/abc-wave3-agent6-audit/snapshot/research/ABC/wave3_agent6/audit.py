#!/usr/bin/env python3
"""Independent, fail-closed Wave 3 closure-metadata audit.

This checks a frozen source snapshot and declared logical interfaces. It does
not decide mathematical truth and never promotes an arithmetic premise.
It does not import the canonical frontier checker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path

ESTABLISHED = {"PROVED", "LEAN_VERIFIED"}
STATUSES = ESTABLISHED | {"CHECKED", "CONDITIONAL", "BLOCKED", "FAILED"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def minimal(families):
    unique = set(families)
    return {s for s in unique if not any(t < s for t in unique)}


def conjoin(families):
    result = {frozenset()}
    for choices in families:
        result = minimal({left | right for left in result for right in choices})
    return result


def inspect(dag, constraints):
    require(dag.get("problem_id") == "ABC", "Wrong original problem")
    require(dag.get("resolution") == "unknown", "Original resolution changed")
    nodes = {n["id"]: n for n in dag["nodes"]}
    require(len(nodes) == len(dag["nodes"]), "Duplicate node IDs")
    rules = {r["id"]: r for r in dag.get("refinement_rules", [])}
    require(len(rules) == len(dag.get("refinement_rules", [])), "Duplicate rule IDs")
    routes = {r["id"]: r for r in dag["routes"]}
    require(len(routes) == len(dag["routes"]), "Duplicate route IDs")

    for key, node in nodes.items():
        require(node["status"] in STATUSES, f"Unknown status on {key}")
        if key.startswith("W3-"):
            require(not any(isinstance(item, list) for item in node.get("evidence", [])),
                    f"Nested evidence list: {key}")
        for dep in node.get("depends_on", []):
            require(dep in nodes, f"Unknown proof dependency {key}: {dep}")
        for antecedent in node.get("assumptions", []):
            require(antecedent in nodes, f"Unknown antecedent {key}: {antecedent}")

    for key, status in constraints["baseline_core_statuses"].items():
        require(key in nodes and nodes[key]["status"] == status,
                f"Baseline core status changed without a new review: {key}")
    for key in constraints["required_open"]:
        require(key in nodes and nodes[key]["status"] == "BLOCKED",
                f"Open original/core estimate was promoted: {key}")
    for key, expected in constraints["required_conditional_antecedents"].items():
        require(key in nodes, f"Missing reviewed implication: {key}")
        require(nodes[key]["status"] in ESTABLISHED,
                f"Implication proof is not established: {key}")
        require(set(expected) <= set(nodes[key].get("assumptions", [])),
                f"Open antecedent lost from implication: {key}")

    # True proof edges must be acyclic, and a proved theorem cannot depend on
    # an unproved theorem via its proof-edge field. Open hypotheses belong in
    # assumptions instead.
    visited, active = set(), set()
    def proof_dfs(key):
        require(key not in active, f"Circular proof dependency: {key}")
        if key in visited:
            return
        active.add(key)
        for dep in nodes[key].get("depends_on", []):
            if nodes[key]["status"] in ESTABLISHED:
                require(nodes[dep]["status"] in ESTABLISHED,
                        f"Unproved theorem used as proof dependency: {key} -> {dep}")
            proof_dfs(dep)
        active.remove(key)
        visited.add(key)
    for key in nodes:
        proof_dfs(key)

    for rule in rules.values():
        for key in [rule["conclusion"], rule["proof"], *rule["all_of"]]:
            require(key in nodes, f"Unknown refinement reference: {key}")

    # Review-authorized explicit bridge for the historical FH route. This is
    # not an inferred equivalence from text and is recorded in constraints.
    bridges = list(rules.values()) + constraints.get("reviewed_implicit_bridges", [])
    independent = []
    for route in routes.values():
        require(route.get("conclusion") in {"ABC-TRUE", "ABC-FALSE"},
                f"Wrong route conclusion: {route['id']}")
        require(route.get("status") == "CONDITIONAL", f"Route status changed: {route['id']}")
        require(bool(route.get("all_of")), f"Vacuous route: {route['id']}")
        selected = []
        for rid in route.get("frontier_expansions", []):
            require(rid in rules, f"Unknown selected rule: {rid}")
            selected.append(rules[rid])
        by_goal = {}
        for rule in selected:
            by_goal.setdefault(rule["conclusion"], []).append(rule)

        def frontier(goal, stack=()):
            require(goal in nodes, f"Unknown route node: {goal}")
            require(goal not in stack, f"Circular selected refinement: {stack + (goal,)}")
            status = nodes[goal]["status"]
            if status in ESTABLISHED:
                return {frozenset()}
            if status == "FAILED":
                return set()
            if goal not in by_goal:
                return {frozenset({goal})}
            alternatives = set()
            for rule in by_goal[goal]:
                premises = [rule["proof"], *rule["all_of"]]
                alternatives |= conjoin(frontier(p, stack + (goal,)) for p in premises)
            return minimal(alternatives)

        fronts = conjoin(frontier(key) for key in route["all_of"])
        require(bool(fronts), f"FAILED live route premise: {route['id']}")
        require(frozenset() not in fronts, f"A route was falsely closed: {route['id']}")

        live = set()
        def collect(key):
            if key in live:
                return
            require(key in nodes, f"Unknown live dependency: {key}")
            require(nodes[key]["status"] != "FAILED",
                    f"FAILED live transitive proof dependency: {route['id']} -> {key}")
            live.add(key)
            for dep in nodes[key].get("depends_on", []):
                collect(dep)
            for rule in by_goal.get(key, []):
                for dep in [rule["proof"], *rule["all_of"]]:
                    collect(dep)
        for key in route["all_of"]:
            collect(key)

        # Check the declared open hypotheses of every applied conditional
        # implication. A proved implication is a known theorem, but its open
        # antecedent is not granted merely by that theorem's PROVED status.
        for front in fronts:
            known = set(front) | {key for key, n in nodes.items() if n["status"] in ESTABLISHED}
            changed = True
            while changed:
                changed = False
                for bridge in bridges:
                    proof = bridge["proof"]
                    if proof not in live or nodes[proof]["status"] not in ESTABLISHED:
                        continue
                    antecedents = set(bridge["all_of"]) | set(nodes[proof].get("assumptions", []))
                    if antecedents <= known and bridge["conclusion"] not in known:
                        known.add(bridge["conclusion"])
                        changed = True
            for key in live:
                if nodes[key]["status"] in ESTABLISHED:
                    missing = set(nodes[key].get("assumptions", [])) - known
                    require(not missing,
                            f"Undischarged conditional antecedent on {route['id']}, {key}: {sorted(missing)}")

        independent.append({"id": route["id"], "conclusion": route["conclusion"],
                            "frontiers": sorted([sorted(f) for f in fronts]),
                            "closed": False, "live_dependency_count": len(live),
                            "conditional_antecedents_preserved": True})

    root_route = constraints["required_root_route"]
    require(root_route in routes, "Reviewed ROOT-only route missing")
    expected = [sorted(constraints["expected_root_frontier"])]
    r = next(row for row in independent if row["id"] == root_route)
    require(r["frontiers"] == expected, f"Wrong ROOT frontier: {r['frontiers']}")
    old = next(row for row in independent if row["id"] == "W2-TRUE-VIA-ROOT-ORBIT")
    require(old["frontiers"] == expected, "Historical ROOT route was not deduplicated through ROOT⇒GROWTH")
    for row in independent:
        for front in row["frontiers"]:
            require(not (set(front) & set(constraints.get("forbidden_new_frontier", []))),
                    f"A diagnostic was added as a new sufficient-route obligation: {row['id']}")
    route_ids = set(constraints.get("active_five_routes", []))
    active_frontier = set()
    for row in independent:
        if row["id"] in route_ids:
            require(len(row["frontiers"]) == 1, "Active-route alternative count changed")
            active_frontier.update(row["frontiers"][0])
    require(len(active_frontier) == 7, f"Active five-route frontier count changed: {sorted(active_frontier)}")
    projection = {key: dag[key] for key in ("nodes", "routes", "refinement_rules")}
    serialized = json.dumps(projection, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    lean_names = {name for node in nodes.values() if node["status"] == "LEAN_VERIFIED"
                  for name in node.get("lean_theorems", [])}
    new_lean_names = {name for key, node in nodes.items() if key.startswith("W3-") and node["status"] == "LEAN_VERIFIED"
                      for name in node.get("lean_theorems", [])}
    require(len(lean_names) == 47 and len(new_lean_names) == 9,
            "Exact distinct Lean declaration counts changed without review")
    return {"node_count": len(nodes), "route_count": len(routes),
            "closed_route_count": 0, "resolution": "unknown", "routes": independent,
            "root_frontier": expected[0], "baseline_core_statuses_preserved": True,
            "failed_live_transitive_dependencies": 0,
            "proof_dependency_cycles": 0, "new_global_core_estimates_closed": 0,
            "active_five_route_frontier": sorted(active_frontier),
            "active_five_route_distinct_targets": len(active_frontier),
            "distinct_lean_declarations": len(lean_names),
            "wave3_distinct_lean_declarations": len(new_lean_names),
            "status_counts": dict(sorted(Counter(n["status"] for n in nodes.values()).items())),
            "wave3_status_counts": dict(sorted(Counter(n["status"] for key, n in nodes.items() if key.startswith("W3-")).items())),
            "mathematical_projection": {
                "definition": "{'nodes': d['nodes'], 'routes': d['routes'], 'refinement_rules': d['refinement_rules']}",
                "serialization": "json.dumps(projection, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8')",
                "sha256": hashlib.sha256(serialized).hexdigest(), "bytes": len(serialized)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--dag", default="research/ABC/closure-dag/obligations.json")
    parser.add_argument("--frontier", default="research/ABC/closure-dag/frontier.json")
    parser.add_argument("--constraints", default="research/ABC/wave3_agent6/constraints.json")
    parser.add_argument("--manifest", default="research/ABC/wave3_agent6/reviewed-files.json")
    parser.add_argument("--lock", default="research/ABC/wave3_agent6/snapshot-lock.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    def local(name):
        path = (root / name).resolve()
        require(path.is_relative_to(root), f"Path outside snapshot: {name}")
        require(path.is_file(), f"Missing snapshot source: {name}")
        return path

    lock = read_json(local(args.lock))
    manifest = read_json(local(args.manifest))
    require(bool(manifest), "Empty reviewed source manifest")
    for name, expected in manifest.items():
        require(digest(local(name)) == expected, f"Reviewed source changed: {name}")
    for name in [args.dag, args.frontier, args.constraints, args.manifest]:
        require(name in lock["sha256"], f"Input not frozen in audit lock: {name}")
        require(digest(local(name)) == lock["sha256"][name], f"Frozen snapshot changed: {name}")

    dag = read_json(local(args.dag))
    result = inspect(dag, read_json(local(args.constraints)))
    require(result["mathematical_projection"]["sha256"] == lock["expected_mathematical_projection_sha256"],
            "Reviewed mathematical projection changed")
    declared = read_json(local(args.frontier))
    require(declared.get("closed_route_count") == 0, "Declared frontier falsely closed a route")
    require(declared.get("counts_are_difficulty_percentages") is False, "Misleading progress percentage")
    require(declared.get("node_count") == result["node_count"], "Stale frontier node count")
    require(declared.get("route_count") == result["route_count"], "Stale frontier route count")
    published = {r["id"]: r for r in declared["routes"]}
    require(len(published) == len(result["routes"]), "Frontier route IDs mismatch")
    for row in result["routes"]:
        require(row["id"] in published, f"Missing declared route: {row['id']}")
        original = published[row["id"]]
        ids = sorted([sorted(f["ids"]) for f in original["minimal_declared_frontiers"]])
        require(ids == row["frontiers"], f"Frontier mismatch: {row['id']}")
        require(original["closed"] is False, f"False closure: {row['id']}")
        require(original.get("invalid_due_to_failed_premise") is False,
                f"Declared invalid route: {row['id']}")

    result.update({"status": "CHECKED", "scope": "Frozen-source metadata and logical-interface audit only; not a mathematical proof checker or Lean verification.",
                   "source_sha256": digest(Path(__file__)),
                   "snapshot_sha256": lock["sha256"],
                   "reviewed_source_count": len(manifest),
                   "reviewed_source_sha256": manifest,
                   "independent_frontier_agrees": True,
                   "run_id": os.environ.get("GITHUB_RUN_ID"),
                   "compute_commit": os.environ.get("GITHUB_SHA")})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in {"routes", "reviewed_source_sha256", "snapshot_sha256"}}, indent=2))


if __name__ == "__main__":
    main()
