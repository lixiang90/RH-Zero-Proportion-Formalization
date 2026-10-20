"""Freeze one same-hor target elaboration repair; text/hash operations only."""
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REL = 'StructuralW9A220261020/Localization.lean'
OLD = b'      simpa only [reverse8] using (le_of_lt (lt_of_not_ge ho))\n'
NEW = '      change g 7 ≤ g 0\n      exact le_of_lt (lt_of_not_ge ho)\n'.encode()
JOB = ROOT / 'tmp/w9a2-20261020/candidate-ordinary-v3'
SEEN = {}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    value = {'path': key, 'bytes': len(raw), 'sha256': sha(raw)}
    assert SEEN.setdefault(key, value) == value, key
    return raw


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream: stream.write(raw)


def dump(value): return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()


def main():
    old = read(ROOT / REL)
    assert len(old) == 13294 and sha(old) == '95138259450a504e9db184baa3b1e3b5cd1bdb8e11c8990d4b20a94cc7643a2d'
    assert old.count(OLD) == 1 and NEW not in old
    new = old.replace(OLD, NEW)
    assert new.replace(NEW, OLD) == old and new.count(NEW) == 1
    assert old[:old.index(OLD)] == new[:new.index(NEW)]
    assert old[old.index(OLD)+len(OLD):] == new[new.index(NEW)+len(NEW):]
    assert len(old[:old.index(OLD)].splitlines()) + 1 == 262
    theorem = re.compile(rb'(?ms)^theorem located_state (.*?) := by\n')
    st0, st1 = theorem.findall(old), theorem.findall(new)
    assert len(st0) == 1 and st0 == st1
    hor = b'    have hor : reverse8 g 0 \xe2\x89\xa4 reverse8 g 7 := by\n'
    assert old.count(hor) == new.count(hor) == 1
    graph = ROOT / 'research-goal-20261020-w9a2-graph-repair-v2/StructuralW9A220261020/Graph.lean'
    graphraw = read(graph)
    assert sha(graphraw) == '2e259252f7fa993954bd52c4a6d6ec58594116a500a576910d6fa671d6521966'
    for name in ['Core','Graph','Counting','Final']:
        read(ROOT / ('StructuralW9A220261020/' + name + '.lean'))
    core = ROOT / 'research-goal-20261020-w9a2-core-repair-v1/development-split/StructuralW9A220261020/Core.lean'
    assert sha(read(core)) == '26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f'
    names = ['started.json','terminal.json'] + [f'StructuralW9A220261020_{m}.{s}'
        for m in ['Graph','Localization'] for s in ['command.json','child.json','log','receipt.json']]
    evidence = {name: read(JOB / name) for name in names}
    log = evidence['StructuralW9A220261020_Localization.log']
    receipt = json.loads(evidence['StructuralW9A220261020_Localization.receipt.json'])
    graph_pass = json.loads(evidence['StructuralW9A220261020_Graph.receipt.json'])
    terminal = json.loads(evidence['terminal.json'])
    start = json.loads(evidence['started.json'])
    errors = re.findall(rb'(?m)^.*:[0-9]+:[0-9]+: error:.*$', log)
    assert len(errors) == 1 and b'Localization.lean:262:6: error: Type mismatch:' in errors[0]
    assert receipt['source_sha256'] == sha(old) and receipt['source_unchanged'] is True
    assert receipt['exit_code'] == 1 and receipt['elapsed_seconds'] == 16.875
    assert receipt['log_sha256'] == sha(log) == 'a6d14663d72d18095ca2819a8552ff62727fc744a139f8802792802f91fd9cfe'
    assert graph_pass['exit_code'] == 0 and graph_pass['ordinary_compile_passed'] is True
    assert graph_pass['source_sha256'] == sha(graphraw)
    assert graph_pass['olean_sha256'] == '9bfb52462f64be80158c143ac110fa2b0b23ca8c8577f37ea067280875ab4e0e'
    assert terminal['passed'] is False and terminal['modules_completed'] == 2
    assert start['gate_sha256'] == '8c890760d99414bccf6357571e85b1c1857e192d58af8fa41c9232ada6fcdde1'
    before = list(SEEN.values())
    for item in before: read(ROOT / item['path'])
    report = {'status': 'PREPARED_PROOF_ONLY_REPAIR_NOT_COMPILED',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'failure': {'module': receipt['module'], 'gate_sha256': start['gate_sha256'],
            'root_observed_parent_session': 46495, 'root_observed_actual_parent_exit_code': 1,
            'parent_exit_evidence_scope': 'Explicit root task message reports the terminal tool handle; actual child receipt and ordinary terminal are copied here.',
            'module_exit_code': 1, 'elapsed_seconds': receipt['elapsed_seconds'],
            'log_sha256': sha(log), 'sole_error': errors[0].decode()},
        'change': {'theorem': 'StructuralW9A220261020.Localization.located_state',
            'local_claim': 'hor : reverse8 g 0 <= reverse8 g 7', 'old_line': 262,
            'old_text': OLD.decode(), 'new_text': NEW.decode(), 'byte_delta': len(new)-len(old),
            'scope': 'Replace simpa with explicit definitionally equal reflected endpoint target, retaining the original inequality proof term.'},
        'old_source': {'bytes': len(old), 'sha256': sha(old)},
        'new_source': {'path': REL, 'bytes': len(new), 'sha256': sha(new)},
        'located_state_statement_unchanged_sha256': sha(st0[0]),
        'hor_statement_byte_identical': True, 'forward_and_reverse_projection_exact': True,
        'all_bytes_outside_one_existing_hor_proof_unchanged': True,
        'root_exterior_reflection_coverage_StateAt_costs_payload_threshold_roots_changes': 0,
        'graph_previous_ordinary_pass': graph_pass,
        'inputs_before': before, 'inputs_after': list(SEEN.values()), 'original_inputs_unchanged': True,
        'compiler_export_kernel_search_runs': 0, 'round_counter_changed': False,
        'ordinary_passed_for_new_Localization': False, 'Comparator_passed': False,
        'independent_kernel_passed': False, 'website_submission_ready': False,
        'requires_new_root_frozen_gate_before_compile': True}
    write(HERE / REL, new)
    write(HERE / 'Localization-v0.lean', old)
    delta = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),
        fromfile='canonical-v0/' + REL,tofile='localization-repair-v1/' + REL))
    write(HERE / 'Localization-v0-to-v1.diff', delta.encode())
    write(HERE / 'repair.json', dump(report))
    for name, raw in evidence.items(): write(HERE / 'failed-ordinary-v3-evidence' / name, raw)
    print(json.dumps({'source_bytes': len(new), 'source_sha256': sha(new), 'delta_bytes': len(new)-len(old),
        'repair_json_sha256': sha(dump(report)), 'proof_execution_runs': 0}))


if __name__ == '__main__': main()
