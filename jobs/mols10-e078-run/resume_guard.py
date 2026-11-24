#!/usr/bin/env python3
"""Verify the fixed E077 resume identity and preserve its ten closed leaves."""
import argparse
import hashlib
import json
from pathlib import Path


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def contained(root, relative):
    path = (root/relative).resolve()
    path.relative_to(root.resolve())
    return path


def atomic_json(path, value):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')
    temporary.replace(path)


def snapshot(state, manifest, shard):
    data = json.loads(manifest.read_text())
    assert data['source_run_id'] == 45301881745
    expected = {item['shard']: item for item in data['shards']}[shard]
    queue = json.loads((state/'queue.json').read_text())
    assert sha256(state/'queue.json') == expected['source_queue_sha256'], 'source queue differs'
    for key, wanted in [('shard', shard), ('n', 10), ('squares', 3),
                        ('even_row_normalization', True), ('parts', expected['parts'])]:
        assert queue[key] == wanted, 'source identity differs: '+key
    assert len(queue['nodes']) == expected['node_count']
    for filename, key in [('base.cnf', 'base_cnf_sha256'), ('mapping.json', 'mapping_sha256')]:
        assert sha256(state/filename) == queue[key] == expected[key], filename+' differs'
    original = {key for key, node in queue['nodes'].items() if node['status'] == 'UNSAT_VERIFIED'}
    assert original == set(expected['certified_nodes']), 'original closed-leaf set differs'
    certificates = []
    for key, prior in expected['certified_nodes'].items():
        node = queue['nodes'][key]
        assert all(node[name] == prior[name] for name in ['cube', 'parent', 'evidence'])
        evidence = contained(state, node['evidence'])
        result = json.loads(evidence.read_text())
        assert result['status'] == 'UNSAT_VERIFIED' and result['cube'] == node['cube']
        proof = result['proof_check']
        assert proof['status'] == 'UNSAT_VERIFIED'
        cnf = contained(state, str(evidence.parent.relative_to(state)/'instance.cnf'))
        lrat = contained(state, str(evidence.parent.relative_to(state)/proof['lrat']))
        assert sha256(cnf) == result['cnf_sha256'] == proof['cnf_sha256']
        assert sha256(lrat) == proof['lrat_sha256']
        files = {cnf.relative_to(state).as_posix(): sha256(cnf),
                 lrat.relative_to(state).as_posix(): sha256(lrat)}
        drat = evidence.parent/'proof.drat'
        if drat.is_file():
            files[drat.relative_to(state).as_posix()] = sha256(drat)
        certificates.append({'node': key, 'cube': node['cube'], 'parent': node['parent'],
                             'evidence': node['evidence'], 'files_sha256': files})
    return {'status': 'SOURCE_IDENTITY_VERIFIED', 'shard': shard,
            'source_run_id': data['source_run_id'],
            'source_queue_sha256': expected['source_queue_sha256'],
            'source_manifest_sha256': sha256(manifest),
            'source_leaf_status_counts': expected['leaf_status_counts'],
            'imported_certified_count': len(certificates),
            'imported_certificates': certificates,
            'meaning': 'Identity and certificate-byte preservation only; fresh replay is still required.'}


def preserve(state, source_record, manifest, shard):
    source = json.loads(source_record.read_text())
    assert source['status'] == 'SOURCE_IDENTITY_VERIFIED'
    assert source['shard'] == shard and source['source_run_id'] == 45301881745
    assert source['source_manifest_sha256'] == sha256(manifest)
    expected = {item['shard']: item for item in json.loads(manifest.read_text())['shards']}[shard]
    assert source['source_queue_sha256'] == expected['source_queue_sha256']
    assert {item['node'] for item in source['imported_certificates']} == set(expected['certified_nodes'])
    queue = json.loads((state/'queue.json').read_text())
    states = {}
    for prior in source['imported_certificates']:
        node = queue['nodes'][prior['node']]
        assert all(node[name] == prior[name] for name in ['cube', 'parent', 'evidence'])
        assert node['status'] in {'UNSAT_VERIFIED', 'UNSAT_AWAITING_VERIFICATION'}, 'imported closure was discarded'
        for relative, digest in prior['files_sha256'].items():
            assert sha256(contained(state, relative)) == digest, 'imported certificate bytes changed: '+relative
        states[prior['node']] = node['status']
    return {'status': 'IMPORTED_CERTIFICATES_PRESERVED', 'shard': shard,
            'source_run_id': 45301881745, 'source_manifest_sha256': sha256(manifest),
            'source_queue_sha256': source['source_queue_sha256'],
            'current_queue_sha256': sha256(state/'queue.json'),
            'preserved_count': len(states), 'node_statuses': states,
            'meaning': 'Original evidence bytes remain intact; deferred replay is not closure.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=['snapshot', 'preserve'])
    parser.add_argument('--state', required=True, type=Path)
    parser.add_argument('--shard', required=True, type=int)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--manifest', type=Path, default=Path(__file__).with_name('resume_manifest.json'))
    args = parser.parse_args()
    state = args.state.resolve()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    target = output/('resume_source.json' if args.phase == 'snapshot' else 'preservation.json')
    try:
        record = (snapshot(state, args.manifest, args.shard) if args.phase == 'snapshot'
                  else preserve(state, output/'resume_source.json', args.manifest, args.shard))
    except Exception as error:
        atomic_json(target, {'status': 'FAILED_'+args.phase.upper(), 'shard': args.shard,
                             'source_run_id': 45301881745, 'error': type(error).__name__+': '+str(error)})
        raise
    atomic_json(target, record)
    print(json.dumps(record, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
