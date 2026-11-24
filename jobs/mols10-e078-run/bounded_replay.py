#!/usr/bin/env python3
"""Bound a fresh exact-queue replay and bind success to the unchanged state."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def stop_group(child):
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        child.wait(timeout=30)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--stage', required=True, choices=['initial', 'final'])
    parser.add_argument('--seconds', required=True, type=int)
    parser.add_argument('--certificate-seconds', default=900, type=int)
    parser.add_argument('--queue-dir', type=Path,
                        default=Path(__file__).resolve().parents[1]/'mols10-e077-exact')
    args = parser.parse_args()
    exact = args.queue_dir.resolve()
    sys.path.insert(0, str(exact))
    from encode import sha256_file
    from queue_search import atomic_json, queue_summary, save_state

    state = args.state.resolve()
    state.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    timed_out = args.seconds <= 0
    qpath = state/'queue.json'
    before = sha256_file(qpath) if qpath.is_file() else None
    command = [sys.executable, str(exact/'queue_search.py'), 'verify',
               '--state', str(state), '--check-seconds', str(args.certificate_seconds)]
    if timed_out:
        code = 124
    else:
        with (state/('replay-'+args.stage+'.log')).open('wb') as output:
            child = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            try:
                code = child.wait(timeout=args.seconds)
            except subprocess.TimeoutExpired:
                timed_out = True
                stop_group(child)
                code = 124
    record = {
        'stage': args.stage, 'verify_returncode': code, 'timed_out': timed_out,
        'overall_budget_seconds': args.seconds,
        'per_certificate_seconds': args.certificate_seconds,
        'elapsed_seconds': time.monotonic()-started,
        'queue_sha256_before': before,
        'source': 'Fresh bounded queue_search.py verify; cached closure is not accepted.'}
    current = sha256_file(qpath) if qpath.is_file() else None
    if code == 0 and (state/'verification.json').is_file() and before == current:
        queue = json.loads(qpath.read_text())
        verification = json.loads((state/'verification.json').read_text())
        verification['record_binding'] = {
            'queue_sha256': current, 'base_cnf_sha256': queue['base_cnf_sha256'],
            'mapping_sha256': queue['mapping_sha256'], 'shard': queue['shard'],
            'n': queue['n'], 'squares': queue['squares'], 'parts': queue['parts'],
            'even_row_normalization': queue['even_row_normalization'],
            'verify_returncode': 0, 'stage': args.stage, 'verified_unix': time.time()}
        atomic_json(state/'verification.json', verification)
        record['status'] = 'VERIFIED_CURRENT_STATE'
    else:
        if (state/'verification.json').is_file():
            (state/'verification.json').replace(state/'verification.previous.json')
        record['status'] = ('PENDING_VERIFICATION_TIMEOUT' if timed_out
                            else 'FAILED_REPLAY_REQUIRES_REVIEW')
        record['certified_leaves_deferred'] = 0
        if qpath.is_file():
            queue = json.loads(qpath.read_text())
            for node in queue.get('nodes', {}).values():
                if node.get('status') == 'UNSAT_VERIFIED':
                    node['status'] = 'UNSAT_AWAITING_VERIFICATION'
                    node['verification_deferred_reason'] = record['status']
                    record['certified_leaves_deferred'] += 1
            queue_summary(queue)
            save_state(state, queue)
        if code == 0:
            code = 1
    record['queue_sha256_after'] = sha256_file(qpath) if qpath.is_file() else None
    atomic_json(state/'replay_status.json', record)
    print(json.dumps(record, ensure_ascii=False), flush=True)
    # Timeout preserves pending work. Actual checker/identity errors stop this step.
    return 0 if timed_out or code == 0 else code


if __name__ == '__main__':
    raise SystemExit(main())
