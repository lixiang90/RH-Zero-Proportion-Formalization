"""Future-gated exact recovery of immutable N/N2; no mathematics at import."""
from hashlib import sha256
from collections import Counter
from fractions import Fraction as F
import json
import struct

EXPECTED_PREFIX = 2375
OLD_CALLS = 2374

def recovery(driver, n2, old, model_for, rawcheck, alg, cells, indices, commit, limit):
    """No native solve/support reconstruction; complete raw checks, not hashes alone."""
    N, N2 = driver.N, driver.N2
    original = list(n2.old_members(N / 'case-records.jsonl.gz'))
    assert len(original) == 676
    assert [r['G_index'] for r, _ in original] == indices[:676]
    native = {}; intents = {}; called = set()
    for directory, intentfile, nativefile, expected in [
        (N, 'call-intents.jsonl', 'native-results.jsonl.gz', 675),
        (N2, 'new-call-intents.jsonl', 'new-native-results.jsonl.gz', 1699)]:
        count = 0
        with (directory / intentfile).open('rb') as handle:
            for line in handle:
                assert line.endswith(b'\n')
                item = json.loads(line); count += 1; index = item['G_index']
                key = 'linprog_call_number' if directory == N else 'new_call_number'
                assert item[key] == count and index not in called
                assert item['method'] == old.METHOD and item['options'] == old.OPTIONS
                called.add(index); intents[index] = item
        assert count == expected
        count = 0
        for value, desc in n2.old_members(directory / nativefile):
            count += 1; index = value['G_index']
            assert index in intents and index not in native
            key = 'call_number' if directory == N else 'new_call_number'
            ikey = 'linprog_call_number' if directory == N else 'new_call_number'
            assert value[key] == intents[index][ikey]
            assert value['native_row_ids'] == intents[index]['native_row_ids']
            native[index] = (value, desc)
        assert count == expected
    assert set(native) == called and len(called) == OLD_CALLS
    proof_members = iter(n2.old_members(N2 / 'case-records.jsonl.gz'))
    head = '0' * 64; ihash = sha256(); counts = Counter(); ordinal = 0
    with (N2 / 'progress-commits.jsonl').open('rb') as handle:
        for line in handle:
            limit(); assert line.endswith(b'\n')
            envelope = json.loads(line); assert driver.canonical(envelope) == line
            body = envelope['body']; ordinal += 1; index = body['G_index']
            assert body['ordinal'] == ordinal and index == indices[ordinal - 1]
            assert body['old_LP_calls'] == 675 and body['new_LP_calls'] == max(0, ordinal - 676)
            assert body['total_LP_calls'] == 675 + max(0, ordinal - 676)
            assert body['previous_commit_sha256'] == head
            head = sha256(driver.canonical(body)).hexdigest(); assert head == envelope['commit_sha256']
            ihash.update(struct.pack('<I', index))
            assert body['committed_index_sequence_sha256'] == ihash.hexdigest()
            counts[body['outcome']] += 1; assert body['counts'] == dict(counts)
            published, published_ref = next(proof_members)
            assert body['proof_record'] == published_ref and published['G_index'] == index
            record, record_ref = published, published_ref
            if ordinal <= 676:
                record, record_ref = original[ordinal - 1]
                assert published['recovered_original_record'] == record_ref
                assert published['was_originally_published'] is (ordinal <= 675)
            assert record['G_index'] == index
            if record['outcome'] == 'deduction_Lower':
                assert index == 2417 and record['dependency'] == old.DEDUCTIONS[index]
                verification = {'Lower': True, 'Below': False, 'deduction': record['dependency']}
            else:
                assert index in called
                model, _, _, _ = model_for(index)
                digest = sha256(driver.canonical(model)).hexdigest()
                assert digest == record['model_sha256'] == intents[index]['model_sha256']
                nv, nd = native[index]
                for key in ['offset', 'bytes', 'decoded_sha256', 'compressed_member_sha256']:
                    assert record['native_record'][key] == nd[key]
                verification = rawcheck.verify(model, record['normalized_exact_reconstruction'])
                assert verification == record['separate_raw_verification']
                primal = record['normalized_exact_reconstruction'].get('exact_primal')
                if primal is not None:
                    assert alg.sparse_primal_check(model, list(map(F, primal['raw_primal'])), cells) == primal['checks']
                outcome = 'Lower' if verification['Lower'] else 'Below' if verification['Below'] else 'unresolved'
                assert outcome == record['outcome']
                if ordinal <= 676:
                    assert published['separate_raw_replay'] == verification
            assert body['outcome'] == record['outcome']
            closure = record['outcome']
            if closure == 'Below':
                assert index == 1322606 and ordinal == EXPECTED_PREFIX
                driver.check_frozen_O(record, verification)
                closure = 'curvature_Lower'
            assert closure in ['Lower', 'deduction_Lower', 'curvature_Lower']
            commit(index, closure, {'recovered_N2_record': published_ref, 'original_case_record': record_ref,
                'original_outcome': record['outcome'], 'separate_raw_replay': verification,
                'old_LP_calls_repeated': 0, 'curvature_dependency': driver.O_DEPENDENCY if closure == 'curvature_Lower' else None}, record)
    assert next(proof_members, None) is None
    result = driver.load(N2 / 'result.json')
    assert ordinal == EXPECTED_PREFIX == result['committed_records']
    assert head == result['commit_head_sha256'] and ihash.hexdigest() == result['committed_index_sequence_sha256']
    assert dict(counts) == result['counts'] == {'Lower': 2373, 'deduction_Lower': 1, 'Below': 1}
    assert len(called) == result['total_LP_calls'] == OLD_CALLS
    assert result['old_LP_calls'] == 675 and result['new_LP_calls'] == 1699 and result['repeated_old_LP_calls'] == 0
    assert set(indices[:EXPECTED_PREFIX]) - called == {2417}
    for snapshot in body['streams'].values():
        path = driver.checked(snapshot['path'])
        assert path.stat().st_size == snapshot['bytes'] and driver.pin(path) == snapshot['sha256']
    return called, {'recovered_records': ordinal, 'original_commit_head_sha256': head,
        'recovered_original_LP_calls': OLD_CALLS, 'repeated_old_LP_calls': 0,
        'all_original_intents_native_complete_members_raw_and_primal_checks': True,
        'original_Below_bound_to_independently_verified_O_Lower': 1322606,
        'unprocessed_suffix': len(indices) - ordinal}
