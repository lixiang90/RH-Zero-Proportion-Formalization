"""Windows file-only repair of the first explicit tactic; no compiler/cache access."""
from pathlib import Path
import difflib, hashlib, json, re

ROOT = Path(r'E:\codex-build\RH-Weil\tmp\primitive-bound-shadow-probe-20261010-r1')
OUT = Path(__file__).resolve().parent
SOURCE = Path(r'E:\codex-build\RH-Zero-Proportion-Formalization\tmp\global-sync-except-am8-source-only-20261010\Solution.global-sync-except-am8.lean')
SHA_SOURCE = '5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2'
SHA_ORIGINAL = '092c03d88e8c0ef8661209e85da9b9f9ac538c126f8e191948a101bc45cf8e63'
SHA_FAILED = '367cf64d36d1883a583672b8a61a6192246e8a23f98712fb2cf9df2efcfe9fa9'
SHA_META = '571f6174f4ea596bf8640751cd349d2a3eddbcd901191a5b9670a8cd2758790e'
SHA_DECL = 'd91fbe36009a8fd4746da2bac8c5c766731cd025433e7dda8c7bca94e76276ea'

def sha(data): return hashlib.sha256(data).hexdigest()
def checked(path, count, pin):
    data = path.read_bytes()
    assert len(data) == count and sha(data) == pin, str(path)
    return data
def put(name, data):
    dest = OUT / name
    assert not dest.exists(), 'Immutable output already exists: ' + str(dest)
    dest.write_bytes(data)
    return {'path': str(dest), 'bytes': len(data), 'sha256': sha(data)}

source = checked(SOURCE, 1993837, SHA_SOURCE)
original = checked(ROOT / 'PrimitiveOriginal.lean', 3917, SHA_ORIGINAL)
failed = checked(ROOT / 'PrimitiveExplicit.lean', 4018, SHA_FAILED)
metadata_blob = checked(ROOT / 'metadata.json', 6610, SHA_META)
decl = checked(ROOT / 'original-extracted-declaration.txt', 2862, SHA_DECL)
old_meta = json.loads(metadata_blob)
assert source[1933916:1936778] == decl

before = b'        simpa only [neg_mul] using hrev\n'
after = b'        linear_combination hrev\n'
assert failed.count(before) == 1
repaired = failed.replace(before, after)
assert repaired.replace(after, before) == failed
failed_lines = failed.splitlines(keepends=True)
new_lines = repaired.splitlines(keepends=True)
assert len(failed_lines) == len(new_lines)
repair_lines = [i + 1 for i, (a, b) in enumerate(zip(failed_lines, new_lines)) if a != b]
assert repair_lines == [43]
assert new_lines[42] == after
assert len(repaired) - len(failed) == -8
for line, tactic in [(60, b'        linear_combination hd + 163840 * hs\n'), (70, b'        linear_combination 163840 * hs - hd\n'), (85, b'    linear_combination 163840 * ht - hd\n')]:
    assert failed_lines[line - 1] == new_lines[line - 1] == tactic

normalized = repaired.replace(b'primitiveBound_sound_probe_explicit', b'primitiveBound_sound_probe_original')
old_lines = original.splitlines(keepends=True)
norm_lines = normalized.splitlines(keepends=True)
assert len(old_lines) == len(norm_lines)
four_lines = [i + 1 for i, (a, b) in enumerate(zip(old_lines, norm_lines)) if a != b]
assert four_lines == [43, 60, 70, 85]
assert len(repaired) - len(original) == 93
original_sig = original.split(b' := by\n', 1)[0].replace(b'primitiveBound_sound_probe_original', b'primitiveBound_sound')
explicit_sig = repaired.split(b' := by\n', 1)[0].replace(b'primitiveBound_sound_probe_explicit', b'primitiveBound_sound')
assert original_sig == explicit_sig
start = repaired.index(b' := by\n') + len(b' := by\n')
end = repaired.index(b'run_cmd do\n', start)
body = repaired[start:end]
assert not re.search(rb'\b(?:sorry|axiom|native_decide|primitiveBound_sound)\b', body)
raw_start = decl.index(b' := by\n') + len(b' := by\n')
raw_body = decl[raw_start:]
orig_start = original.index(b' := by\n') + len(b' := by\n')
orig_end = original.index(b'run_cmd do\n', orig_start)
assert original[orig_start:orig_end] == raw_body
restored = list(norm_lines)
for i in four_lines: restored[i - 1] = old_lines[i - 1]
assert b''.join(restored) == original

outputs = {}
outputs['original'] = put('PrimitiveOriginal.lean', original)
outputs['explicit'] = put('PrimitiveExplicit.lean', repaired)
outputs['failed_r1_explicit_preserved'] = put('r1-failed-PrimitiveExplicit.lean', failed)
outputs['r1_metadata_preserved'] = put('r1-metadata.json', metadata_blob)
outputs['original_extracted_declaration'] = put('original-extracted-declaration.txt', decl)
repair_diff = ''.join(difflib.unified_diff(failed.decode().splitlines(keepends=True), repaired.decode().splitlines(keepends=True), fromfile='r1-failed-PrimitiveExplicit.lean', tofile='r2-PrimitiveExplicit.lean')).encode()
outputs['one_line_repair_diff'] = put('r1-to-r2.diff', repair_diff)
four_diff = ''.join(difflib.unified_diff(original.decode().splitlines(keepends=True), normalized.decode().splitlines(keepends=True), fromfile='PrimitiveOriginal.lean', tofile='PrimitiveExplicit.name-normalized.lean')).encode()
outputs['four_line_body_diff'] = put('four-line-body.diff', four_diff)
new_meta = dict(old_meta)
new_meta.update({
    'status': 'PREPARED_R2_SOURCE_ONLY_NOT_LEAN_CHECKED',
    'lean_run': False, 'runtime_started': False, 'cache_accessed': False,
    'public_candidate_modified': False, 'prior_r1_files_modified': False,
    'repair_from_failed_r1': {'source_sha256': SHA_FAILED, 'source_bytes': len(failed), 'changed_probe_line': 43, 'original_frozen_source_line': 23138, 'before': before.decode().rstrip('\n'), 'after': after.decode().rstrip('\n'), 'delta_bytes': -8, 'exact_old_bytes_recovered_by_inverse_replacement': True, 'only_one_line_changed_vs_failed_r1': True, 'other_three_explicit_tactics_preserved_exactly': True},
    'explicit_body': {'bytes': len(body), 'sha256': sha(body)},
    'whole_probe_delta_bytes': 93,
    'raw_proposed_candidate_headroom_bytes': 6070,
    'outputs': outputs,
    'preparation_script': {'path': str(Path(__file__).resolve()), 'bytes': len(Path(__file__).read_bytes()), 'sha256': sha(Path(__file__).read_bytes())},
    'prior_actual_results_reported_by_parent_not_read_here': {
        'original_body_checked_seconds': 0.875,
        'original_body_checked_pass': True,
        'original_fresh_type_same_and_std3_and_no_shortcut_pass': True,
        'original_dependency_closure_count': 9492,
        'failed_explicit_lean_exit_code': 1,
        'failed_explicit_hrev_type': 'gapPotential g j - gapPotential g i <= -(5 * (cellLower left j i : Real))',
        'failed_explicit_norm_num_goal': '5 * (cellLower left j i : Real) + gapPotential g j <= gapPotential g i',
        'failed_explicit_body_seconds': 0.499,
        'failed_explicit_seconds_are_speed_evidence': False,
        'failed_explicit_env_has_sorryAx': True,
        'failed_explicit_fresh_audit_run': False,
        'failed_explicit_fresh_olean_present': False,
        'r2_actual_validation': 'NOT_RUN_PREPARED_ONLY',
    },
    'static_linear_combination_reason': 'The supplied hrev difference inequality and the normalized goal are equivalent after moving the same linear Real terms. linear_combination hrev uses coefficient +1. This is static algebraic justification only; Lean elaboration, exact type, standard axioms and no-shortcut dependency audit remain unrun for r2.'
})
new_meta['four_line_changes'] = [dict(v) for v in old_meta['four_line_changes']]
new_meta['four_line_changes'][0].update({'after': after.decode().rstrip('\n'), 'delta_bytes': 15})
new_meta['comparison_limits'] = [v.replace('+101 bytes', '+93 bytes') for v in old_meta['comparison_limits']]
new_meta['comparison_limits'].append('The failed r1 explicit run is retained as a failure; neither its 0.499 seconds nor absence of errors at the other three lines establishes a successful r2 proof or any timing improvement.')
put('metadata.json', (json.dumps(new_meta, ensure_ascii=False, indent=2) + '\n').encode())
readme = '''# Prepared r2 primitiveBound_sound shadow probe

This is an uncompiled file-only repair. The original baseline, r1 metadata,
and failed r1 explicit source are copied byte-for-byte. Nothing in r1 or in the
public submission is modified. Reproduce in a fresh directory by placing this
prepare.py there and invoking Windows Python; every frozen input is SHA-guarded.

Only probe line 43 changes from `simpa only [neg_mul] using hrev` to
`linear_combination hrev`. The normalized goal had moved the same Real terms
to the opposite side, so direct coefficient +1 is the intended algebraic proof.
The other three explicit tactics are unchanged. Static algebra does not establish
Lean acceptance: compile, exact theorem type, standard-only transitive axioms,
and exclusion of the original target from dependencies remain required.

The parent reports the original shadow proof and audit passed. The earlier
explicit proof failed, produced an environment with sorryAx, and had no fresh
artifact or audit. Its 0.499 seconds is not speed evidence. This repaired r2 has
not been tested. Independent tiny-probe timing cannot establish a whole-file,
default Lean replay, serial Nano, memory-fit, or website-acceptance improvement.

The new source is 8 bytes smaller than the failed explicit and 93 bytes larger
than the unchanged baseline. A raw four-line whole-source proposal would have
6070 bytes headroom, but no complete numeral-dictionary rebundling is performed.
The context, import, options, paired BEGIN/END instrumentation and post-import
environment limitations are preserved in metadata.json and r1-metadata.json.
'''
put('README.md', readme.encode())
print(json.dumps({'status': new_meta['status'], 'outputs': outputs, 'metadata_sha256': sha((OUT / 'metadata.json').read_bytes()), 'metadata_bytes': (OUT / 'metadata.json').stat().st_size, 'delta_vs_failed_r1_bytes': -8, 'delta_vs_original_bytes': 93}, indent=2))
