"""Independent prepared-source audit. No Lean, walker, kernel or solver runs.

The full finite scan below reads only previously frozen sorted leaf metadata.
It checks proposed target debits; it does not re-establish metadata soundness.
"""
from pathlib import Path
import difflib
import gzip
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OFFICIAL = ROOT / 'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
CORE = ROOT / 'StructuralW9A220261020/Core.lean'
GEOMETRY = ROOT / 'research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json'
LEAVES = ROOT / 'research-goal-20261019-w9a2-certificate-analysis/numeric-leaves-sorted.jsonl.gz'
SOURCE_SHA = '241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7'
GEOMETRY_SHA = '7d860bb023594ecc4dc84308435acbdcdeb5da7d8d81991220045955575b9c67'
LEAVES_SHA = 'f2acd938535e00216de3585c85e7c06d9ac213698088a2dc7374005a335a94ae'
SLOPE = 335544320000000000


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def block(text, a, b):
    assert text.count(a) == text.count(b) == 1, (a, b)
    return text[text.index(a):text.index(b)]


def main():
    source_files = [OFFICIAL, CORE, GEOMETRY, LEAVES]
    source_files += [ROOT / f'StructuralW9A220261020/{name}.lean'
                     for name in ['Graph', 'Localization', 'Counting', 'Final']]
    before = {p.relative_to(ROOT).as_posix(): sha(p) for p in source_files}
    assert sha(OFFICIAL) == SOURCE_SHA
    assert sha(GEOMETRY) == GEOMETRY_SHA
    assert sha(LEAVES) == LEAVES_SHA
    old = OFFICIAL.read_text(encoding='utf-8')
    new = CORE.read_text(encoding='utf-8')
    geo = json.loads(GEOMETRY.read_text(encoding='utf-8'))
    states = {int(k): list(map(int, re.findall(r'\d+', raw))) for k, raw in
              re.findall(r'\| (\d+) => ⟨([^⟩]+)⟩',
                         block(new, 'def qState', 'def qCost'))}
    costs = {int(k): int(v) for k, v in re.findall(r'\| (\d+) => (\d+)',
             block(new, 'def qCost', 'def qCell'))}
    assert set(states) == set(costs) == set(range(24))
    lookup = {}
    for k in range(24):
        assert states[k] == geo['first24'][k]['state']
        assert len(states[k]) == 73 and states[k][-1] == 0
        assert costs[k] == geo['first24'][k]['margin'] // SLOPE
        assert tuple(states[k]) not in lookup
        lookup[tuple(states[k])] = k

    # Preserve all pre-certificate analytic mathematics and literal payloads.
    old_start = old[:old.index('abbrev Covered : Cl → Prop')]
    new_start = new[:new.index('structure St where')]
    new_start = new_start[new_start.index('/-\nR. Arun Chandru'):]
    assert old_start.replace('import ChallengeDeps.CandidateSpec\n', '') == new_start
    data_a = 'namespace AMW.Cert.PC9QB6MData\n'
    data_b = 'end AMW.Cert.PC9QB6MData\n'
    assert block(old, data_a, data_b) == block(new, data_a, data_b)
    packed_old = [x for x in old.splitlines() if ' := zfNat64 ' in x]
    packed_new = [x for x in new.splitlines() if ' := zfNat64 ' in x]
    assert packed_old == packed_new
    rc_old = re.findall(r'^theorem rc\d+[^\n]+', old, re.M)
    rc_new = re.findall(r'^theorem rc\d+[^\n]+', new, re.M)
    assert rc_old == rc_new and len(rc_new) == 48
    assert block(old, 'def stEq (a b : St)', 'theorem covered_of_walkCP') == \
        block(new, 'def stEq (a b : St)', 'def qTargetFrom')

    # Directly normalize only the goal argument; the checker remains identical.
    old_checker = block(old, 'def mcheckP ', 'theorem mcheckP_ok')
    new_checker = block(new, 'def mcheckP ', 'theorem mcheckP_ok')
    assert new_checker.replace('(goalN : ℕ) ', '', 1).replace('goalN', 'cN') == old_checker
    old_leaf = block(old, 'def mleafP ', 'theorem mleafP_ok ')
    new_leaf = block(new, 'def mleafP ', 'theorem mleafP_target_ok ')
    assert new_leaf.replace('(goalN : ℕ) ', '', 1).replace('mcheckP goalN', 'mcheckP') == old_leaf
    assert block(old, 'def fleaf ', 'def leafStep ') == block(new, 'def fleaf ', 'def leafStep ')
    for name, end in [('def walk ', 'theorem walk_ok '),
                      ('def walkC ', 'theorem walkC_ok ')]:
        assert block(old, name, end) == block(new, name, end)

    # Every old metadata row must be safe for its single deterministic selector.
    selected_counts = [0] * 24
    rows = 0
    good_rows = 0
    min_good_residual = None
    minimum_residual = None
    duplicate_states = 0
    seen = {}
    violations = []
    sorted_previous = None
    uncompressed_hash = hashlib.sha256()
    with gzip.open(LEAVES, 'rb') as stream:
        for raw in stream:
            uncompressed_hash.update(raw)
            leaf = json.loads(raw)
            state = tuple(leaf['state'])
            assert len(state) == 73 and state[-1] == 0
            order = (leaf['margin'], leaf['root'], leaf['pos'])
            assert sorted_previous is None or sorted_previous <= order
            sorted_previous = order
            rank = lookup.get(state)
            increment = 10**12 if rank is None else costs[rank]
            residual = leaf['margin'] - SLOPE * increment
            if residual < 0:
                violations.append({'root': leaf['root'], 'pos': leaf['pos'],
                                   'rank': rank, 'residual': residual})
            if rank is None:
                good_rows += 1
                min_good_residual = residual if min_good_residual is None else min(min_good_residual, residual)
            else:
                selected_counts[rank] += 1
            if state in seen:
                duplicate_states += 1
            else:
                seen[state] = (leaf['root'], leaf['pos'], leaf['margin'])
            minimum_residual = residual if minimum_residual is None else min(minimum_residual, residual)
            rows += 1
    assert rows == 11794 and not violations
    assert all(n >= 1 for n in selected_counts)
    clean = re.sub(r'/-[\s\S]*?-/', '', new)
    clean = re.sub(r'--[^\n]*', '', clean)
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b', clean)
    assert not re.search(r'^\s*axiom\b', clean, re.M)
    assert before == {p.relative_to(ROOT).as_posix(): sha(p) for p in source_files}
    result = {
        'status': 'PASS_STATIC_SOURCE_AND_ALL_FROZEN_TARGET_DEBITS_NOT_LEAN',
        'scope': 'Static literal/source identity and all 11794 pre-existing sorted metadata rows only; no walk replay, kernel evaluation, numerical search, solver or Lean invocation.',
        'input_hashes': before,
        'analytic_prefix_unchanged_except_stale_spec_import': True,
        'entire_Data_namespace_identical': True,
        'packed_literal_declarations_identical_count': len(packed_new),
        'rc_theorems_byte_identical_count': len(rc_new),
        'St_eq_moved_verbatim': True,
        'mcheckP_only_goal_parameter_changed': True,
        'mleafP_only_goal_parameter_changed': True,
        'fleaf_walk_walkC_definitions_identical': True,
        'qState_qCost_equal_original_first24': True,
        'metadata_rows': rows,
        'metadata_uncompressed_sha256': uncompressed_hash.hexdigest(),
        'metadata_unique_states': len(seen),
        'metadata_repeated_state_rows': duplicate_states,
        'selected_rank_row_counts': selected_counts,
        'good_target_rows': good_rows,
        'minimum_target_residual': minimum_residual,
        'minimum_good_target_residual': min_good_residual,
        'unsafe_target_rows': violations,
        'all_48_rc_decisions_and_actual_proof_elaboration_remain_unverified': True,
        'compiler_runs': 0,
        'kernel_runs': 0,
        'candidate_source_bytes': {p.name: p.stat().st_size for p in source_files
                                  if p.parent.name == 'StructuralW9A220261020'},
    }
    output = HERE / 'audit.json'
    with output.open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(result, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    print(json.dumps({k: result[k] for k in ['status', 'metadata_rows',
          'metadata_unique_states', 'metadata_repeated_state_rows',
          'selected_rank_row_counts', 'good_target_rows', 'minimum_target_residual',
          'minimum_good_target_residual']}))


if __name__ == '__main__':
    main()
