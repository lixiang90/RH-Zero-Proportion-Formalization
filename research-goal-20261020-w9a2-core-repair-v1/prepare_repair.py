"""One source-only Bool simplification repair, with exact reversible projections.

No compiler, exporter, kernel, solver, threshold change or numeric replay.
Canonical v0, development v0, Prefix and the failed job remain unchanged.
"""
from pathlib import Path
from datetime import datetime, timezone
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
FULL = ROOT / 'StructuralW9A220261020/Core.lean'
SPLIT = ROOT / 'research-goal-20261020-w9a2-formal-static-review/development-split/StructuralW9A220261020/Core.lean'
PREFIX = SPLIT.with_name('Prefix.lean')
SPLIT_AUDIT = ROOT / 'research-goal-20261020-w9a2-formal-static-review/split-audit.json'
JOB = ROOT / 'tmp/w9a2-20261020/candidate-ordinary-v0'
FULL_SHA = 'c5180e8cb9d219bec5cf29e4d65e0cfc304f4d40a12ad6d52332603e115fccd6'
SPLIT_SHA = 'b2f536448f48a50d3994cbccf7b3bd94ea54f388664d98e120c112130794ff1e'
PREFIX_SHA = 'bfd774658f3f855596a5453f86f4d98fbc884ca651b3e595d68f70b9553f5b3c'
OLD = '      simpa only [qTargetFrom, hs, ↓reduceIte] using h\n'.encode()
NEW = '      simpa only [qTargetFrom, hs, Bool.false_eq_true, ↓reduceIte] using h\n'.encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path):
    raw = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(raw)


def block(raw, start, end):
    assert raw.count(start) == raw.count(end) == 1
    return raw[raw.index(start):raw.index(end)]


def main():
    evidence_names = ['started.json', 'terminal.json',
        'StructuralW9A220261020_Prefix.receipt.json',
        'StructuralW9A220261020_Core.log', 'StructuralW9A220261020_Core.receipt.json',
        'StructuralW9A220261020_Core.command.json']
    bool_source = ROOT / 'tmp/lean-toolchain/src/lean/Init/Data/Bool.lean'
    paths = [FULL, SPLIT, PREFIX, SPLIT_AUDIT, bool_source] + [JOB / name for name in evidence_names]
    before = [pin(path) for path in paths]
    full0, split0, prefix = FULL.read_bytes(), SPLIT.read_bytes(), PREFIX.read_bytes()
    assert sha(full0) == FULL_SHA and sha(split0) == SPLIT_SHA and sha(prefix) == PREFIX_SHA
    assert full0.count(OLD) == split0.count(OLD) == 1
    assert NEW not in full0 and NEW not in split0
    bool_text = bool_source.read_text(encoding='utf-8')
    assert '@[simp] theorem false_eq_true : (false = true) = False := by simp' in bool_text
    old_log = (JOB / 'StructuralW9A220261020_Core.log').read_bytes()
    assert sha(old_log) == 'db0d88a8a2bc407caa915490512c7312de78b2ad6be7f8b31479af51c3380461'
    core_receipt = json.loads((JOB / 'StructuralW9A220261020_Core.receipt.json').read_bytes())
    prefix_receipt = json.loads((JOB / 'StructuralW9A220261020_Prefix.receipt.json').read_bytes())
    assert core_receipt['exit_code'] == 1 and core_receipt['source_sha256'] == SPLIT_SHA
    assert core_receipt['source_unchanged'] is True and core_receipt['ordinary_compile_passed'] is False
    assert prefix_receipt['ordinary_compile_passed'] is True and prefix_receipt['source_sha256'] == PREFIX_SHA
    full1, split1 = full0.replace(OLD, NEW), split0.replace(OLD, NEW)
    audit = json.loads(SPLIT_AUDIT.read_bytes())
    prologue = audit['suffix_prologue'].encode()
    close = audit['prefix_added_closing_command'].encode()
    assert split0.startswith(prologue) and split1.startswith(prologue) and prefix.endswith(close)
    assert prefix[:-len(close)] + split0[len(prologue):] == full0
    assert prefix[:-len(close)] + split1[len(prologue):] == full1
    assert full1.replace(NEW, OLD) == full0 and split1.replace(NEW, OLD) == split0
    assert block(full0, b'theorem qTargetFrom_sound ', b':= by\n  induction ks with') == \
        block(full1, b'theorem qTargetFrom_sound ', b':= by\n  induction ks with')
    data_start, data_end = b'namespace AMW.Cert.PC9QB6MData\n', b'end AMW.Cert.PC9QB6MData\n'
    assert block(full0, data_start, data_end) == block(full1, data_start, data_end)
    old_lines, new_lines = full0.splitlines(), full1.splitlines()
    changed = [(i+1, a, b) for i, (a, b) in enumerate(zip(old_lines, new_lines)) if a != b]
    assert len(old_lines) == len(new_lines) and len(changed) == 1
    assert changed[0][1] + b'\n' == OLD and changed[0][2] + b'\n' == NEW
    destinations = {
        HERE / 'canonical-full/StructuralW9A220261020/Core.lean': full1,
        HERE / 'development-split/StructuralW9A220261020/Core.lean': split1,
    }
    for dest, raw in destinations.items():
        write(dest, raw)
    for label, old, new in [('canonical-full', full0, full1), ('development-split', split0, split1)]:
        diff = ''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),
            new.decode().splitlines(keepends=True), fromfile='v0/'+label+'/Core.lean',
            tofile='v1/'+label+'/Core.lean'))
        write(HERE / (label+'.diff'), diff.encode())
    for name in evidence_names:
        write(HERE / 'failed-v0-evidence' / name, (JOB / name).read_bytes())
    bool_excerpt = '\n'.join(bool_text.splitlines()[198:208])+'\n'
    write(HERE / 'Bool-source-excerpt.txt', bool_excerpt.encode())
    after = [pin(path) for path in paths]
    assert before == after
    result = {
        'status': 'PREPARED_PROOF_ONLY_REPAIR_NOT_COMPILED',
        'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
        'failure': {'gate_sha256': json.loads((JOB / 'started.json').read_bytes())['gate_sha256'],
            'module': core_receipt['module'], 'exit_code': 1,
            'elapsed_seconds': core_receipt['elapsed_seconds'], 'log_sha256': sha(old_log),
            'diagnostic': 'At split Core line143:6, simp only leaves the Bool coercion condition false = true unreduced in qTargetFrom_sound.'},
        'change': {'theorem': 'AMW.Cert.PC9QB6M.qTargetFrom_sound',
            'full_source_line': changed[0][0], 'development_source_line': 143,
            'old_line': OLD.decode().rstrip('\n'), 'new_line': NEW.decode().rstrip('\n'),
            'scope': 'Add only the existing Init.Data.Bool.false_eq_true simp theorem, retaining the identical theorem statement and all definitions/data.'},
        'canonical_full_v0_unchanged_sha256': FULL_SHA,
        'development_split_v0_unchanged_sha256': SPLIT_SHA,
        'prefix_v0_unchanged_sha256': PREFIX_SHA,
        'prefix_previous_ordinary_pass': prefix_receipt,
        'new_artifacts': [pin(path) for path in destinations],
        'exact_projections': {'full_v0_to_v1_only_single_line': True,
            'split_v0_to_v1_only_single_line': True,
            'full_v1_reverse_projection_equals_v0': True,
            'split_v1_reverse_projection_equals_v0': True,
            'old_prefix_plus_new_suffix_equals_new_full_bytes': True,
            'new_full_source_sha256': sha(full1), 'new_split_source_sha256': sha(split1)},
        'theorem_statement_unchanged': True, 'entire_Data_namespace_byte_identical': True,
        'threshold_cost_state_potential_payload_guard_cursor_changes': 0,
        'source_inputs_before': before, 'source_inputs_after': after, 'original_inputs_unchanged': True,
        'compiler_export_kernel_search_runs': 0, 'main_round_counter_changed': False,
        'ordinary_pass_claimed_for_v1': False, 'finite_rc_pass_claimed_from_error_log': False,
        'requires_new_root_frozen_gate_before_compile': True,
    }
    write(HERE / 'repair.json', (json.dumps(result, ensure_ascii=False, indent=2)+'\n').encode())
    print(json.dumps({'status': result['status'], 'full_bytes': len(full1), 'full_sha256': sha(full1),
                      'split_bytes': len(split1), 'split_sha256': sha(split1),
                      'repair_json_sha256': sha((HERE / 'repair.json').read_bytes())}))


if __name__ == '__main__':
    main()
