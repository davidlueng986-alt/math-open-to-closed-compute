#!/usr/bin/env python3
"""Build one bounded v7 continuation from exact prior plans and mandatory checkpoints.

The source manifest records worker outcomes, not an independent encoding audit.
Certified tasks retain their source artifacts; only OPEN tasks enter the matrix.
"""
import argparse
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys


CERTIFIED = 'ALL_CUBES_CERTIFIED_UNSAT_PENDING_ENCODING_AUDIT'
PRIORITY = 'D8-N8-B0-P000-T01'
TOTAL_TASKS = 279
OPEN_TASKS = 232
CERTIFIED_TASKS = 47


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path):
    return json.loads(Path(path).read_text())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def task_key(task):
    data = {k: v for k, v in task.items() if k != 'key'}
    text = json.dumps(data, sort_keys=True, separators=(',', ':'))
    return hashlib.sha256(text.encode()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def index_tasks(plan):
    tasks = plan['tasks']
    indexed = {task['id']: task for task in tasks}
    require(len(indexed) == len(tasks), 'Duplicate task IDs')
    for task in tasks:
        require(task['key'] == task_key(task), 'Task identity mismatch: ' + task['id'])
    return indexed


def index_manifest(manifest):
    entries = manifest['tasks']
    indexed = {entry['id']: entry for entry in entries}
    require(len(indexed) == len(entries) == TOTAL_TASKS, 'Manifest task set is not 279 unique tasks')
    counts = Counter(entry['status'] for entry in entries)
    require(dict(counts) == {'OPEN': OPEN_TASKS, CERTIFIED: CERTIFIED_TASKS}, 'Unexpected source status counts')
    ids = set()
    for entry in entries:
        task_id = entry['id']
        require(entry['artifact_name'] == 'checkpoint-' + task_id, 'Artifact/task name mismatch')
        require(isinstance(entry['artifact_id'], int) and entry['artifact_id'] > 0, 'Invalid artifact ID')
        require(entry['artifact_id'] not in ids, 'Repeated artifact ID')
        ids.add(entry['artifact_id'])
        require(re.fullmatch(r'sha256:[0-9a-f]{64}', entry['artifact_digest']) is not None, 'Missing artifact digest')
        require(entry['cuts'] >= 0 and entry['models'] >= 0, 'Negative source counts')
        terminals = entry['terminals']
        require(terminals and set(terminals) <= {'OPEN', 'CERTIFIED_UNSAT', 'UNSAT_UNCERTIFIED'}, 'Unexpected terminal status')
        require(all(isinstance(v, int) and v > 0 for v in terminals.values()), 'Invalid terminal counts')
        closed = set(terminals) == {'CERTIFIED_UNSAT'}
        require(closed == (entry['status'] == CERTIFIED), 'Task/terminal statuses disagree')
    return indexed


def continuation_order(tasks):
    """Put the proof-completion opportunity first, then round-robin root leaves."""
    indexed = {t['id']: t for t in tasks}
    require(PRIORITY in indexed, 'Expected proof-completion task is missing')
    result = [indexed.pop(PRIORITY)]
    groups = defaultdict(list)
    for task in indexed.values():
        groups[(task['d'], task['q'])].append(task)
    queues = {key: deque(sorted(group, key=lambda t: t['id'])) for key, group in groups.items()}
    while any(queues.values()):
        for key in sorted(queues):
            if queues[key]:
                result.append(queues[key].popleft())
    require(len(result) == len(tasks), 'Continuation ordering lost a task')
    return result


def build(args):
    manifest = load(args.manifest)
    entries = index_manifest(manifest)
    source_specs = {s['name']: s for s in manifest['sources']}
    require(set(source_specs) == {'pilot', 'rollout'}, 'Unexpected source plans')
    plans = {'pilot': Path(args.pilot_plan), 'rollout': Path(args.rollout_plan)}
    expected_counts = {'pilot': 32, 'rollout': 247}
    all_tasks = {}
    source_evidence = {}
    for name, path in plans.items():
        spec = source_specs[name]
        require(digest(path) == spec['plan_sha256'], 'Source plan digest mismatch: ' + name)
        indexed = index_tasks(load(path))
        require(len(indexed) == expected_counts[name], 'Source plan count mismatch: ' + name)
        require(not (set(all_tasks) & set(indexed)), 'Source task plans overlap')
        expected_ids = {i for i, e in entries.items() if e['source'] == name}
        require(set(indexed) == expected_ids, 'Manifest/source task coverage mismatch: ' + name)
        for task_id, task in indexed.items():
            entry = entries[task_id]
            require(entry['task_key'] == task['key'], 'Manifest/task key mismatch: ' + task_id)
            require(entry['source_run'] == spec['run_id'], 'Manifest/source run mismatch: ' + task_id)
            source_evidence[task_id] = entry
        all_tasks.update(indexed)
    require(set(all_tasks) == set(entries), 'Combined task coverage is incomplete')
    require(digest(args.cert) == manifest['profile_cert_sha256'], 'Profile certificate digest mismatch')
    selected = continuation_order([t for task_id, t in all_tasks.items() if entries[task_id]['status'] == 'OPEN'])
    require(len(selected) == OPEN_TASKS <= 256, 'Continuation exceeds matrix bound or loses OPEN work')
    require({t['id'] for t in selected} == {i for i, e in entries.items() if e['status'] == 'OPEN'}, 'OPEN task set mismatch')
    matrix = []
    for task in selected:
        entry = entries[task['id']]
        matrix.append({
            'id': task['id'],
            'task_key': task['key'],
            'source_run': str(entry['source_run']),
            'artifact_id': str(entry['artifact_id']),
            'artifact_name': entry['artifact_name'],
            'artifact_digest': entry['artifact_digest'],
            'proof_seconds': 900 if task['id'] == PRIORITY else 240,
        })
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    write(out / 'plan.json', {
        'schema': 1, 'engine': 'v7', 'continuation': True,
        'source_manifest_sha256': digest(args.manifest),
        'source_runs': [source_specs[n]['run_id'] for n in ('pilot', 'rollout')],
        'tasks': [all_tasks[i] for i in sorted(all_tasks)],
    })
    write(out / 'matrix.json', {'include': matrix})
    write(out / 'source-evidence.json', source_evidence)
    shutil.copyfile(args.manifest, out / 'source-manifest.json')
    shutil.copyfile(args.cert, out / 'profile_cert.json')
    print(json.dumps({
        'status': 'EXACT_CONTINUATION_COVERAGE_VERIFIED',
        'all_tasks': len(all_tasks), 'resume_tasks': len(matrix),
        'certified_tasks_retained_at_source': CERTIFIED_TASKS,
        'priority_task': matrix[0]['id'],
    }), flush=True)


def validate_tree(checkpoint, allow_witness=False):
    nodes = checkpoint['nodes']
    require('r' in nodes and nodes['r']['cube'] == [], 'Missing root cube')
    stack, seen, terminals = ['r'], set(), Counter()
    while stack:
        key = stack.pop()
        require(key not in seen, 'Repeated tree node')
        seen.add(key)
        node = nodes[key]
        cube = node['cube']
        require(all(type(v) is int and 1 <= abs(v) <= 780 for v in cube), 'Invalid cube literals')
        require(len(set(map(abs, cube))) == len(cube), 'Repeated cube variable')
        require(type(node['attempts']) is int and node['attempts'] >= 0, 'Invalid attempt count')
        if node['status'] == 'SPLIT':
            var = node['split_var']
            require(type(var) is int and 1 <= var <= 780 and var not in map(abs, cube), 'Invalid split variable')
            require(nodes[key + '0']['cube'] == cube + [-var], 'Missing negative split branch')
            require(nodes[key + '1']['cube'] == cube + [var], 'Missing positive split branch')
            stack.extend([key + '0', key + '1'])
        else:
            allowed = {'OPEN', 'CERTIFIED_UNSAT', 'UNSAT_UNCERTIFIED'}
            if allow_witness:
                allowed.add('VERIFIED_WITNESS')
            require(node['status'] in allowed, 'Unexpected terminal status')
            terminals[node['status']] += 1
    require(seen == set(nodes), 'Unreachable tree nodes')
    require(dict(terminals) == checkpoint['terminal_counts'], 'Tree/manifest terminal totals disagree')
    status = ('VERIFIED_WITNESS' if terminals['VERIFIED_WITNESS'] else
              CERTIFIED if set(terminals) == {'CERTIFIED_UNSAT'} else 'OPEN')
    require(checkpoint['status'] == status, 'Checkpoint status disagrees with its terminal nodes')


def preflight(args):
    manifest = load(args.manifest)
    entries = index_manifest(manifest)
    tasks = index_tasks(load(args.plan))
    require(set(tasks) == set(entries), 'Combined plan task set differs from manifest')
    require(args.task in entries, 'Unknown task')
    entry, task = entries[args.task], tasks[args.task]
    require(entry['status'] == 'OPEN', 'Certified source task must not be scheduled again')
    resume = Path(args.resume)
    checkpoint_path = resume / 'checkpoint.json'
    require(checkpoint_path.is_file(), 'Requested resume checkpoint.json is missing')
    checkpoint = load(checkpoint_path)
    require(checkpoint['schema'] == 1, 'Unsupported checkpoint schema')
    require(checkpoint['task'] == task, 'Restored task identity changed')
    require(task['key'] == entry['task_key'], 'Restored task key differs from source manifest')
    require(checkpoint['status'] == entry['status'], 'Restored status differs from source log')
    for key in ('cuts', 'models'):
        require(checkpoint[key] == entry[key], 'Restored ' + key + ' differs from source log')
    require(checkpoint['terminal_counts'] == entry['terminals'], 'Restored terminal counts differ from source log')
    require(re.fullmatch(r'[0-9a-f]{64}', checkpoint['base_sha256']) is not None, 'Invalid base CNF digest')
    validate_tree(checkpoint)
    cut_path = resume / 'cuts.jsonl'
    require(cut_path.is_file(), 'Requested resume cuts.jsonl is missing')
    # A stream can contain valid cuts flushed immediately before its atomic
    # manifest update. The worker validates and retains the entire prefix.
    with cut_path.open() as stream:
        cut_rows = sum(1 for line in stream if line.strip())
    require(cut_rows >= checkpoint['cuts'], 'Restored cut stream is truncated')
    for key, node in checkpoint['nodes'].items():
        if node['status'] != 'CERTIFIED_UNSAT':
            continue
        proof = node['proof']
        require(proof['certificate'] == 'VERIFIED_UNSAT', 'Missing proof certificate metadata')
        require(0 <= proof['cut_count'] <= checkpoint['cuts'], 'Invalid proof cut prefix')
        require((resume / 'proofs' / key / 'leaf.drat.gz').is_file(), 'Restored proof file is missing: ' + key)
    print(json.dumps({
        'status': 'MANDATORY_CHECKPOINT_PREFLIGHT_VERIFIED', 'task': args.task,
        'source_run': entry['source_run'], 'artifact_id': entry['artifact_id'],
        'cuts': checkpoint['cuts'], 'cut_rows': cut_rows,
        'models': checkpoint['models'], 'terminals': checkpoint['terminal_counts'],
    }), flush=True)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def cut_prefix(old_path, new_path):
    with old_path.open('rb') as old, new_path.open('rb') as new:
        while True:
            block = old.read(1 << 20)
            if not block:
                return
            require(new.read(len(block)) == block, 'Prior cut stream prefix was changed or truncated')


def validate_report_checkpoint(args):
    manifest = load(args.manifest)
    entry = index_manifest(manifest)[args.task]
    task = index_tasks(load(args.plan))[args.task]
    require(entry['status'] == 'OPEN', 'Only an OPEN source task can be continued')
    old_dir, new_dir = Path(args.resume), Path(args.out)
    old = load(old_dir / 'checkpoint.json')
    new = load(new_dir / 'checkpoint.json')
    require(old['task'] == new['task'] == task, 'Checkpoint task identity changed')
    require(task['key'] == entry['task_key'], 'Checkpoint/source task key mismatch')
    require(old['base_sha256'] == new['base_sha256'], 'Base CNF identity changed')
    for field in ('cuts', 'models'):
        require(old[field] == entry[field], 'Source checkpoint differs from observed source ' + field)
        require(new[field] >= old[field], 'Checkpoint ' + field + ' decreased')
    require(old['status'] == entry['status'], 'Source status differs from observed source')
    require(old['terminal_counts'] == entry['terminals'], 'Source terminals differ from observed source')
    validate_tree(old)
    validate_tree(new, allow_witness=True)
    for key, node in old['nodes'].items():
        require(key in new['nodes'], 'Old tree node disappeared: ' + key)
        continued = new['nodes'][key]
        require(node['cube'] == continued['cube'], 'Old cube changed: ' + key)
        require(continued['attempts'] >= node['attempts'], 'Old attempt count decreased: ' + key)
        if node['status'] == 'SPLIT':
            require(continued['status'] == 'SPLIT' and continued['split_var'] == node['split_var'], 'Old split changed: ' + key)
    cut_prefix(old_dir / 'cuts.jsonl', new_dir / 'cuts.jsonl')
    with (new_dir / 'cuts.jsonl').open() as stream:
        cut_rows = sum(1 for line in stream if line.strip())
    require(cut_rows >= new['cuts'], 'Output cut stream is truncated')
    for key, node in new['nodes'].items():
        if node['status'] != 'CERTIFIED_UNSAT':
            continue
        proof = node['proof']
        require(proof['certificate'] == 'VERIFIED_UNSAT', 'Output certificate metadata is incomplete')
        require(0 <= proof['cut_count'] <= new['cuts'], 'Output proof cut prefix is invalid')
        require((new_dir / 'proofs' / key / 'leaf.drat.gz').is_file(), 'Output proof file is missing: ' + key)
    old_certified = {k for k, n in old['nodes'].items() if n['status'] == 'CERTIFIED_UNSAT'}
    new_certified = {k for k, n in new['nodes'].items() if n['status'] == 'CERTIFIED_UNSAT'}
    result = {
        'schema': 1, 'task': args.task, 'task_key': task['key'],
        'recorded_at_utc': utc_now(), 'report_valid': True,
        'status': new['status'], 'terminals': new['terminal_counts'],
        'cuts': new['cuts'], 'cut_rows': cut_rows, 'models': new['models'],
        'source': {
            'run_id': entry['source_run'], 'artifact_id': entry['artifact_id'],
            'artifact_name': entry['artifact_name'], 'artifact_digest': entry['artifact_digest'],
            'status': entry['status'], 'cuts': entry['cuts'], 'models': entry['models'],
            'terminals': entry['terminals'],
        },
        'nodes': {
            'source': len(old['nodes']), 'output': len(new['nodes']),
            'split': sum(n['status'] == 'SPLIT' for n in new['nodes'].values()),
            'terminals': sum(new['terminal_counts'].values()),
            'max_depth': max(len(n['cube']) for n in new['nodes'].values()),
        },
        'certified_terminals': len(new_certified),
        'previous_certified_nodes_reopened': sorted(old_certified - new_certified),
        'source_cut_prefix_preserved': True,
        'actions_worker_outcome': args.worker_outcome,
        'run_id': os.environ.get('GITHUB_RUN_ID'),
        'checkpoint_artifact_name': 'checkpoint-' + args.task,
        'result_artifact_name': 'result-' + args.task,
        'certificate_scope': 'CNF proof status pending mathematical encoding audit',
    }
    if new['status'] == 'VERIFIED_WITNESS':
        witness = new_dir / 'witness.txt'
        check_path = new_dir / 'witness-check.json'
        require(witness.is_file() and check_path.is_file(), 'Witness files are missing')
        verification = load(check_path)
        require(verification.get('closure_witness') is True, 'Witness replay did not certify closure_witness')
        result['witness'] = {
            'file': 'witness.txt', 'sha256': digest(witness),
            'verification_file': 'witness-check.json',
            'verification': verification,
            'checkpoint_artifact_name': 'checkpoint-' + args.task,
            'root_status': 'WITNESS_FOUND_PENDING_FINAL_MATHEMATICAL_AUDIT',
        }
    return result


def report(args):
    try:
        result = validate_report_checkpoint(args)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        result = {
            'schema': 1, 'task': args.task, 'recorded_at_utc': utc_now(),
            'report_valid': False, 'status': 'ERROR', 'error': str(exc),
            'actions_worker_outcome': args.worker_outcome,
            'run_id': os.environ.get('GITHUB_RUN_ID'),
            'checkpoint_artifact_name': 'checkpoint-' + args.task,
        }
    destination = Path(args.report_file)
    destination.parent.mkdir(parents=True, exist_ok=True)
    write(destination, result)
    print(json.dumps(result), flush=True)
    if not result['report_valid']:
        raise SystemExit(1)


def aggregate(args):
    manifest = load(args.manifest)
    entries = index_manifest(manifest)
    tasks = index_tasks(load(args.plan))
    require(set(tasks) == set(entries), 'Aggregate plan and manifest differ')
    expected = {i for i, entry in entries.items() if entry['status'] == 'OPEN'}
    reports, errors = {}, []
    invalid = set()
    for path in sorted(Path(args.results_dir).rglob('result.json')):
        result = None
        try:
            result = load(path)
            task_id = result['task']
            require(task_id in expected, 'Unexpected result task: ' + str(task_id))
            require(task_id not in reports, 'Duplicate result task: ' + task_id)
            reports[task_id] = result
            require(result['report_valid'] is True, 'Checkpoint report failed: ' + str(result.get('error')))
            require(result['task_key'] == tasks[task_id]['key'] == entries[task_id]['task_key'], 'Result task key mismatch')
            require(result['source']['run_id'] == entries[task_id]['source_run'], 'Result source run mismatch')
            require(result['source']['artifact_id'] == entries[task_id]['artifact_id'], 'Result source artifact mismatch')
            require(result['status'] in {'OPEN', CERTIFIED, 'VERIFIED_WITNESS'}, 'Unexpected result status')
            terminal_counts = result['terminals']
            require(terminal_counts and all(type(n) is int and n > 0 for n in terminal_counts.values()), 'Invalid result terminal counts')
            require(set(terminal_counts) <= {'OPEN', 'CERTIFIED_UNSAT', 'UNSAT_UNCERTIFIED', 'VERIFIED_WITNESS'}, 'Unexpected result terminal status')
            status = ('VERIFIED_WITNESS' if terminal_counts.get('VERIFIED_WITNESS') else
                      CERTIFIED if set(terminal_counts) == {'CERTIFIED_UNSAT'} else 'OPEN')
            require(result['status'] == status, 'Result status and terminals disagree')
            require(result['cuts'] >= entries[task_id]['cuts'] and result['models'] >= entries[task_id]['models'], 'Result progress decreased')
            require(result['source_cut_prefix_preserved'] is True, 'Source cut prefix was not verified')
            if status == 'VERIFIED_WITNESS':
                require(result['witness']['verification']['closure_witness'] is True, 'Witness verification is missing')
        except (OSError, ValueError, KeyError, TypeError) as exc:
            errors.append({'path': str(path), 'error': str(exc)})
            if isinstance(result, dict) and result.get('task') in expected:
                invalid.add(result['task'])
    missing = sorted(expected - set(reports))
    combined, status_counts, terminals, outcomes = [], Counter(), Counter(), Counter()
    witnesses = []
    for task_id in sorted(entries):
        entry = entries[task_id]
        if entry['status'] == CERTIFIED:
            row = {'task': task_id, 'status': CERTIFIED, 'evidence': 'retained_source_artifact', 'source': entry,
                   'terminals': entry['terminals'], 'cuts': entry['cuts'], 'models': entry['models']}
        elif task_id in missing or task_id in invalid:
            row = {'task': task_id, 'status': 'MISSING_OR_INVALID_CONTINUATION_RESULT', 'source': entry}
        else:
            row = dict(reports[task_id])
            row['evidence'] = 'validated_continuation_report'
            outcomes[row.get('actions_worker_outcome', 'unknown')] += 1
            if row['status'] == 'VERIFIED_WITNESS':
                witnesses.append({'task': task_id, **row['witness']})
        status_counts[row['status']] += 1
        terminals.update(row.get('terminals', {}))
        combined.append(row)
    require(sum(status_counts.values()) == TOTAL_TASKS, 'Aggregate lost task coverage')
    complete = not missing and not errors
    progress = {
        'schema': 1, 'recorded_at_utc': utc_now(), 'run_id': args.run_id,
        'repository': manifest['repository'], 'task_count': TOTAL_TASKS,
        'expected_continuation_results': OPEN_TASKS, 'received_results': len(reports),
        'valid_continuation_results': len(reports) - len(invalid),
        'report_collection': 'COMPLETE' if complete else 'INCOMPLETE',
        'retained_source_cnf_certified_tasks': CERTIFIED_TASKS,
        'task_status_counts': dict(status_counts), 'terminal_status_counts': dict(terminals),
        'actions_worker_outcomes': dict(outcomes),
        'mathematical_root_status': ('WITNESS_FOUND_PENDING_FINAL_MATHEMATICAL_AUDIT' if witnesses else
                                     'OPEN' if status_counts['OPEN'] or not complete else
                                     'ALL_TASK_CNFS_CERTIFIED_PENDING_ENCODING_AND_ROOT_COVERAGE_AUDIT'),
        'missing_tasks': missing, 'invalid_tasks': sorted(invalid), 'errors': errors,
        'witnesses': witnesses, 'tasks': combined,
        'scope': 'D678 v7 source plan coverage; D9 and the full Ramsey root require separate accounting',
        'interpretation': 'Actions execution success and CNF certificate status are separate; no mathematical closure is asserted.',
    }
    lines = ['# Ramsey R(3,10) v7 continuation progress', '',
             'This report distinguishes job execution from mathematical certificates.', '',
             '| Measure | Count / status |', '|---|---:|',
             f'| Task coverage | {TOTAL_TASKS} |',
             f'| Prior CNF-certified tasks retained at source | {CERTIFIED_TASKS} |',
             f'| Continuation reports received | {len(reports)} / {OPEN_TASKS} |',
             f'| Report collection | {progress["report_collection"]} |',
             f'| CNF-certified tasks, including retained sources | {status_counts[CERTIFIED]} |',
             f'| OPEN tasks | {status_counts["OPEN"]} |',
             f'| Witness tasks | {status_counts["VERIFIED_WITNESS"]} |',
             f'| Missing or invalid task reports | {status_counts["MISSING_OR_INVALID_CONTINUATION_RESULT"]} |', '',
             'CNF certificates remain pending mathematical encoding audit. The covered D678 task set does not by itself close the full Ramsey root.', '',
             '## Worker execution outcomes', '',
             *[f'- `{key}`: {value}' for key, value in sorted(outcomes.items())], '',
             '## Search terminal outcomes', '',
             *[f'- `{key}`: {value}' for key, value in sorted(terminals.items())], '']
    if witnesses:
        lines.extend(['## Witnesses requiring final mathematical audit', ''])
        for witness in witnesses:
            lines.append(f'- `{witness["task"]}`: `witness.txt` and `witness-check.json` in `{witness["checkpoint_artifact_name"]}`; closure_witness verification passed.')
        lines.append('')
    if missing or errors:
        lines.extend(['## Incomplete evidence', '', 'Missing or invalid reports must be resolved before treating the continuation as fully accounted for.', '',
                      *[f'- Missing: `{task_id}`' for task_id in missing],
                      *[f'- Error: {error["path"]}: {error["error"]}' for error in errors], ''])
    if args.run_id:
        lines.extend([f'[Workflow run](https://github.com/{manifest["repository"]}/actions/runs/{args.run_id})', ''])
    out = Path(args.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    write(out / 'progress.json', progress)
    (out / 'summary.md').write_text('\n'.join(lines))
    print(json.dumps({k: progress[k] for k in ('report_collection', 'task_count', 'received_results', 'task_status_counts', 'mathematical_root_status')}), flush=True)
    if not complete:
        raise SystemExit(1)


def main():
    command = sys.argv[1] if len(sys.argv) > 1 else ''
    if command == 'preflight':
        parser = argparse.ArgumentParser(description='Validate a mandatory restored checkpoint before worker execution')
        for name in ('manifest', 'plan', 'task', 'resume'):
            parser.add_argument('--' + name, required=True)
        preflight(parser.parse_args(sys.argv[2:]))
    elif command == 'report':
        parser = argparse.ArgumentParser(description='Validate preserved progress and write a compact continuation result')
        for name in ('manifest', 'plan', 'task', 'resume', 'out', 'report-file'):
            parser.add_argument('--' + name, required=True)
        parser.add_argument('--worker-outcome', choices=('success', 'failure', 'cancelled', 'skipped', 'unknown'), default='unknown')
        report(parser.parse_args(sys.argv[2:]))
    elif command == 'aggregate':
        parser = argparse.ArgumentParser(description='Account for every source task and continuation result')
        for name in ('manifest', 'plan', 'results-dir', 'out-dir'):
            parser.add_argument('--' + name, required=True)
        parser.add_argument('--run-id', default=os.environ.get('GITHUB_RUN_ID'))
        aggregate(parser.parse_args(sys.argv[2:]))
    else:
        parser = argparse.ArgumentParser(description=__doc__)
        for name in ('manifest', 'pilot-plan', 'rollout-plan', 'cert', 'out-dir'):
            parser.add_argument('--' + name, required=True)
        build(parser.parse_args())


if __name__ == '__main__':
    main()
