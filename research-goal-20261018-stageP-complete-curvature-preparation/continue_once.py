"""Prepared P full remaining range, same pooled model plus fixed O rule.

Definitions only at import. A separate immutable root gate is mandatory.
Frozen N mathematics and O CellA/network helpers are never modified.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import importlib.util
import json
import os
import struct
import sys
import time
import traceback

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
N = ROOT / 'research-goal-20261018-stageN-complete-component-preparation'
N2 = ROOT / 'research-goal-20261018-stageN2-pooled-component-resumption'
O = ROOT / 'research-goal-20261018-stageO-fixed-curvature-preparation'
M = ROOT / 'research-goal-20261018-stageM-component-envelope-preparation'
H = ROOT / 'research-goal-20261018-stageH-ordered-transport'
SOURCE = ROOT / 'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
EXPECTED = 15378
RECOVERED = 2375
OLD_CALLS = 2374
MAX_NEW_CALLS = 13002
CURVATURE_INDEX = 1322606
MAX_REG_CELLS = 266
O_DEPENDENCY = 'independently_verified_fixed_O1322606_curvature_Lower'
PINS = {
 'research-goal-20261018-stageN-complete-component-preparation/files.json':'181473343e98152ab01e622b6346cd37516bb9724477ac26ade56e15dc9b7377',
 'research-goal-20261018-stageN2-pooled-component-resumption/files.json':'327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f',
 'research-goal-20261018-stageN-independent-v1/audit-files.json':'4cd8af33a892f0f038a81d07110d4a86e08d3bbaba97ecd0849af765a9b649e8',
 'research-goal-20261018-stageN2-independent-below/audit-files.json':'8a793215fd7d0e64e8fbcaa388cb99c384d007584a9acdcf78a303ac9a61c39b',
 'research-goal-20261018-stageO-fixed-curvature-preparation/files.json':'9eeb39270ad6853ee7ad3472c0446237ad21b64be0db442815e2566bfe97191b',
 'research-goal-20261018-stageO-fixed-curvature-preparation/curvature-packet.json':'a952a8bd239bddaa0c8d1f24b45a5096cb3a3b6ff19f067baaba46686eb11cbf',
 'research-goal-20261018-stageO-independent/audit-files.json':'1720e8263e960db1fcd3b0089f5a858cb60e1b14cd2198707f25cc00fd1ed645',
 'research-goal-20261018-stageO-independent/independent-review.json':'97aa2c964580433ad73054cadc901f84982e12404d5d235cc8cf6e7f46969b56',
 'research-goal-20261018-stageO-delivery-byte-inventory/files.json':'24aa8d6b9e251d5ce92650024d7e5fddc62fc1ff675b2aa23792976470add810',
}

def pin(path):
    h = sha256()
    with path.open('rb') as handle:
        for block in iter(lambda: handle.read(1048576), b''): h.update(block)
    return h.hexdigest()

def load(path): return json.loads(path.read_text(encoding='utf-8'))
def rel(path): return path.relative_to(ROOT).as_posix()
def canonical(value): return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode('ascii') + b'\n'
def checked(name):
    path = (ROOT / name).resolve(); assert path.is_relative_to(ROOT); return path
def write(path, value):
    with path.open('xb') as handle: handle.write(canonical(value)); handle.flush(); os.fsync(handle.fileno())
def imported(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module

def package(path, expected, refs):
    assert pin(path) == expected; refs[rel(path)] = expected
    value = load(path)
    for field in ['files', 'owned_files', 'read_only_dependencies', 'read_only_existing_references', 'dependencies', 'read_only_whole_file_dependencies']:
        for item in value.get(field, []):
            p = checked(item['path']); actual = pin(p); assert actual == item['sha256']
            if 'bytes' in item: assert p.stat().st_size == item['bytes']
            if rel(p) in refs: assert refs[rel(p)] == actual
            refs[rel(p)] = actual

def check_frozen_O(record, verification):
    packet = load(O / 'curvature-packet.json')
    assert record['G_index'] == packet['G_index'] == CURVATURE_INDEX
    assert record['pair'] == packet['pair'] == [278, 665] and record['chart'] == packet['chart'] == 'rev/id'
    assert verification['Below'] and verification['dual_valid'] and not verification['Lower']
    weights = record['normalized_exact_reconstruction']['exact_dual']['raw_row_weights']
    assert all(F(row['raw_dual_weight']) == F(weights[row['row_id']]) for row in packet['all_original_component_rows'])
    assert F(verification['raw_lower_bound']) == F(packet['frozen_raw_dual_cost'])
    assert packet['conditional_fixed_pair_floor_closes'] and F(packet['minus_target']) > 0
    assert F(packet['uniform_raw_lower_bound']) == F(packet['raw_target']) + F(packet['minus_target'])
    # The external O audit is a pinned dependency, not re-executed here.

class WorkLimit(Exception): pass

def size(): return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
def limit(start, gate):
    if time.monotonic() - start > gate['work_limits']['elapsed_seconds']: raise WorkLimit('soft_elapsed_limit')
    if size() > gate['work_limits']['closed_output_bytes']: raise WorkLimit('soft_output_limit')

class Stream:
    def __init__(self, path):
        self.path = path; self.f = path.open('xb'); self.hash = sha256(); self.records = 0
    def append(self, value):
        raw = canonical(value); data = gzip.compress(raw, compresslevel=6, mtime=0); offset = self.f.tell()
        self.f.write(data); self.f.flush(); os.fsync(self.f.fileno()); self.hash.update(data); self.records += 1
        return {'path': rel(self.path), 'offset': offset, 'bytes': len(data),
                'decoded_sha256': sha256(raw).hexdigest(), 'compressed_member_sha256': sha256(data).hexdigest()}
    def descriptor(self):
        return {'path': rel(self.path), 'bytes': self.f.tell(), 'sha256': self.hash.hexdigest(), 'records': self.records}
    def close(self): self.f.close()

class Commits:
    def __init__(self, path, indices, streams):
        self.f = path.open('xb'); self.path = path; self.indices = indices; self.streams = streams
        self.count = 0; self.head = '0' * 64; self.indexhash = sha256(); self.counts = Counter()
    def append(self, index, closure, calls, proof, selectors):
        assert index == self.indices[self.count]
        self.count += 1; self.counts[closure] += 1; self.indexhash.update(struct.pack('<I', index))
        body = {'schema': 'P-durable-progress-commit-v1', 'ordinal': self.count, 'G_index': index, 'outcome': closure,
            'previous_commit_sha256': self.head, 'counts': dict(self.counts), 'original_LP_calls': OLD_CALLS,
            'new_LP_calls': calls, 'total_LP_calls': OLD_CALLS + calls, 'proof_record': proof, 'selector_record': selectors,
            'committed_index_sequence_sha256': self.indexhash.hexdigest(),
            'streams': {s.path.name: s.descriptor() for s in self.streams}, 'unvisited_suffix_not_classified': True}
        digest = sha256(canonical(body)).hexdigest()
        self.f.write(canonical({'body': body, 'commit_sha256': digest})); self.f.flush(); os.fsync(self.f.fileno()); self.head = digest
    def summary(self):
        return {'committed_records': self.count, 'counts': dict(self.counts), 'commit_head_sha256': self.head,
                'journal_path': rel(self.path), 'journal_bytes': self.f.tell(),
                'committed_index_sequence_sha256': self.indexhash.hexdigest()}
    def close(self): self.f.close()

def inputs(gate_path, gate_sha):
    assert pin(gate_path) == gate_sha; gate = load(gate_path)
    assert gate['same_model_complete_curvature_passes_authorized'] == 1
    assert gate['expected_original_H_records'] == EXPECTED and gate['recovered_N_N2_records'] == RECOVERED
    assert gate['previous_LP_calls'] == OLD_CALLS and gate['maximum_new_LP_calls'] == MAX_NEW_CALLS
    assert gate['maximum_total_LP_calls'] == 15376 and gate['repeated_previous_LP_calls_authorized'] == 0
    assert gate['per_new_case_maximum_LP_calls'] == 1 and gate['auxiliary_or_retry_calls_authorized'] == 0
    assert gate['stop_policy'] == 'first_nonclosed_case_after_at_most_one_fixed_curvature_attempt'
    assert gate['fixed_O_index'] == CURVATURE_INDEX and gate['maximum_original_REG_cells_total'] == MAX_REG_CELLS
    assert gate['curvature_seed_policy'] == 'reuse_23_independently_audited_O_cells_no_reevaluation'
    assert gate['new_FS_anchors_kernel_points_precision_support_or_Lean_authorized'] == 0
    assert gate['payment_methods'] == ['group_variance_clamp', 'one_exact_component_gauge_Laplace']
    assert gate['progress_protocol'] == 'append_only_fsync_commit_chain_no_replace'
    assert gate['actual_quantitative_and_strongTaylor_bridge_review_complete'] is True
    assert isinstance(gate['actual_bridge_dependency_pins'], dict) and gate['actual_bridge_dependency_pins']
    assert gate['work_limits']['elapsed_seconds'] < gate['resource_limits']['elapsed_seconds']
    assert 0 < gate['work_limits']['closed_output_bytes'] < gate['resource_limits']['closed_output_bytes']
    refs = {rel(gate_path): gate_sha}
    for name, expected in PINS.items(): package(checked(name), expected, refs)
    for name, expected in gate['actual_bridge_dependency_pins'].items():
        p = checked(name); assert pin(p) == expected; refs[name] = expected
    package(HERE / 'prepared-files.json', gate['prepared_manifest_sha256'], refs)
    old = imported(N / 'discover_complete.py', 'P_frozen_N_utilities')
    assert gate['solver_method'] == old.METHOD and gate['solver_options'] == old.OPTIONS
    assert int(gate['target_c_numerator']) == 893766123055294719 and int(gate['denominator']) == 10**20
    runtime = load(M / 'external-runtime.json'); external = old.runtime_hashes(runtime)
    assert str(Path(sys.executable)) == runtime['python_executable']
    data = (H / 'remaining-indices.u32.bin').read_bytes()
    indices = [v[0] for v in struct.iter_unpack('<I', data)]
    assert len(indices) == EXPECTED and indices == sorted(set(indices))
    result = load(N2 / 'result.json'); terminal = load(N2 / 'terminal.json')
    assert result['committed_records'] == RECOVERED and result['total_LP_calls'] == OLD_CALLS
    assert result['counts'] == {'Lower': 2373, 'deduction_Lower': 1, 'Below': 1}
    assert result['first_exact_Below_found'] and terminal['exit_code'] == 0 and terminal['limit_stop'] is None
    assert terminal['inputs_unchanged_after_terminal'] and terminal['external_runtime_unchanged_after_terminal']
    assert indices[RECOVERED - 1] == CURVATURE_INDEX and 5331088 in indices[RECOVERED:]
    return gate, refs, old, runtime, external, indices

def execute(gate_path, gate_sha):
    assert __debug__
    for name in ['started.json', 'result.json', 'failure.json', 'inconclusive.json', 'progress-commits.jsonl', 'new-call-intents.jsonl']:
        assert not (HERE / name).exists(), ('single_attempt_no_retry', name)
    start = time.monotonic(); stage = 'inputs'; refs = {}; external = {}; streams = []; commits = None; intents = None
    new_calls = 0; new_cell_queries = 0; curvature_attempts = 0; stop_reason = None; query_intents = None
    try:
        gate, refs, old, runtime, external, indices = inputs(gate_path, gate_sha)
        write(HERE / 'started.json', {'schema': 'P-same-model-complete-curvature-start-v1', 'pid': os.getpid(),
            'inputs_sha256': refs, 'external_runtime_sha256_start': external, 'old_LP_calls': OLD_CALLS,
            'new_process_caches_start_empty_then_recover_frozen_evidence': True,
            'old_hint_trajectory_not_claimed_continued': True, 'no_source_runtime_or_global_proof_claim': True})
        alg = imported(N / 'component_model.py', 'P_frozen_pooled_math')
        recon = imported(N / 'reconstruct_support.py', 'P_frozen_support_policy')
        rawcheck = imported(N / 'check_raw_certificate.py', 'P_frozen_raw_check')
        n2 = imported(N2 / 'resume_once.py', 'P_frozen_N2_member_reader')
        recovery = imported(HERE / 'recover_frozen.py', 'P_recover_exact_old_evidence')
        curved = imported(HERE / 'fixed_curvature.py', 'P_fixed_O_generalization')
        frozen_O = imported(O / 'audit_once.py', 'P_frozen_O_chain_rule')
        provider = imported(O / 'cellA_quantitative.py', 'P_frozen_CellA_arithmetic')
        network = imported(O / 'weighted_network.py', 'P_frozen_fixed_quadratic_payment')
        stage = 'initialize_original_source_and_recover_component_cache'; limit(start, gate)
        source, mathmod, core, cells, traces, jcache = old.initialize_originals(refs)
        cache = {}; cache_refs = {}
        for directory, filename in [(N, 'original-components.jsonl.gz'), (N2, 'new-original-components.jsonl.gz')]:
            for window, desc in n2.old_members(directory / filename):
                cid = window['cell_id']; assert cid not in cache; jc = jcache[cid]
                assert window['canonical_Cstar'] == jc['canonical_Cstar'] and window['canonical_J'] == jc['canonical_J']
                assert sha256(canonical(window['terms'])).hexdigest() == jc['original_term_components_sha256']
                assert window['state_sha256'] == cells[cid]['state_sha256'] == jc['state_sha256']
                assert window['witness'] == cells[cid]['witness'] == jc['witness']
                cache[cid] = window; cache_refs[cid] = desc
        originals = Stream(HERE / 'new-original-components.jsonl.gz')
        native = Stream(HERE / 'new-native-results.jsonl.gz')
        records = Stream(HERE / 'case-records.jsonl.gz')
        curvature_stream = Stream(HERE / 'curvature-records.jsonl.gz')
        candidates = Stream(HERE / 'Below-candidates.jsonl.gz')
        cell_stream = Stream(HERE / 'new-CellA-cells.jsonl.gz')
        selectors = Stream(HERE / 'selector-records.jsonl.gz')
        streams = [originals, native, records, curvature_stream, candidates, cell_stream, selectors]
        commits = Commits(HERE / 'progress-commits.jsonl', indices, streams)
        intents = (HERE / 'new-call-intents.jsonl').open('xb')
        query_intents = (HERE / 'new-CellA-query-intents.jsonl').open('xb')
        def model_for(index):
            pair, chart = divmod(index, 4); i, j = divmod(pair, old.N); windows = []
            for cid in (i, j):
                if cid not in cache:
                    w, _ = core.extract_original_affine(cells[cid], source, mathmod, traces); jc = jcache[cid]
                    assert w['canonical_Cstar'] == jc['canonical_Cstar'] and w['canonical_J'] == jc['canonical_J']
                    assert sha256(canonical(w['terms'])).hexdigest() == jc['original_term_components_sha256']
                    assert w['state_sha256'] == jc['state_sha256'] and w['witness'] == jc['witness']
                    cache_refs[cid] = originals.append(w); cache[cid] = w
                windows.append(cache[cid])
            model = alg.assemble(windows, cells, source, mathmod.ALL, chart)
            assert model['group_count'] == 42 and model['columns_count'] == 51 and model['full_balance_coordinates'] == 52
            return model, i, j, chart
        def commit_recovered(index, closure, proof, original_record):
            if closure == 'curvature_Lower':
                packet = load(O / 'curvature-packet.json')
                sel = curved.selector(original_record, closure, packet)
            else: sel = curved.selector(original_record, closure)
            record_ref = records.append({'G_index': index, 'outcome': closure, **proof})
            selector_ref = selectors.append(sel)
            commits.append(index, closure, new_calls, record_ref, selector_ref)
        stage = 'recover_2375_original_cases_no_LP_no_curvature'
        driver = sys.modules[__name__]
        called, recovery_receipt = recovery.recovery(driver, n2, old, model_for, rawcheck, alg, cells, indices,
            commit_recovered, lambda: limit(start, gate))
        write(HERE / 'recovery.json', recovery_receipt)
        assert commits.count == RECOVERED and len(called) == OLD_CALLS
        stage = 'initialize_original_REG_catalog_and_audited_23_cell_seed'
        params = provider.parameters(SOURCE.read_text(encoding='utf-8'))
        assert len(params['REG']['cells']) == MAX_REG_CELLS
        catalog = {(c['L'], c['U']) for c in params['REG']['cells']}
        seed = load(O / 'curvature-packet.json'); cell_cache = {}; cell_refs = {}
        for ordinal, value in enumerate(seed['selected_original_CellA_cells']):
            key = (value['L'], value['U']); assert key in catalog and key not in cell_cache
            cell_cache[key] = value
            cell_refs[key] = {'path': rel(O / 'curvature-packet.json'), 'sha256': PINS[rel(O / 'curvature-packet.json')],
                              'selected_original_CellA_cells_index': ordinal, 'independently_audited_seed': True}
        assert len(cell_cache) == 23
        queried = set()
        def before_cell(cell):
            nonlocal new_cell_queries
            key = (cell['L'], cell['U']); assert key in catalog and key not in cell_cache and key not in queried
            queried.add(key)
            new_cell_queries += 1; assert new_cell_queries <= MAX_REG_CELLS - 23
            query_intents.write(canonical({'original_REG_cell': cell, 'new_query_number': new_cell_queries,
                'same_original_REG_catalog_no_subdivision': True})); query_intents.flush(); os.fsync(query_intents.fileno())
        def append_cell(value):
            key = (value['L'], value['U']); assert key in queried and key not in cell_cache
            return cell_stream.append(value)
        stage = 'new_runtime_import'
        import numpy as np
        import scipy
        from scipy.optimize import linprog
        assert np.__version__ == '2.5.2' and scipy.__version__ == '1.18.1'
        assert old.runtime_hashes(runtime) == external
        for index in indices[commits.count:]:
            stage = 'new_case_' + str(index); limit(start, gate)
            if index in old.DEDUCTIONS:
                assert index == 5331088
                proof = records.append({'G_index': index, 'outcome': 'deduction_Lower', 'dependency': old.DEDUCTIONS[index]})
                sr = selectors.append({'G_index': index, 'closure': 'deduction_Lower', 'dependency': old.DEDUCTIONS[index]})
                commits.append(index, 'deduction_Lower', new_calls, proof, sr); continue
            assert index not in called, 'never_repeat_any_previous_or_new_LP_index'
            model, i, j, chart = model_for(index); digest = sha256(canonical(model)).hexdigest()
            c, A, b, selected = alg.native_arrays(model, np); limit(start, gate)
            assert new_calls < MAX_NEW_CALLS; new_calls += 1; called.add(index)
            intent = {'G_index': index, 'new_call_number': new_calls, 'total_call_number': OLD_CALLS + new_calls,
                'model_sha256': digest, 'method': old.METHOD, 'options': old.OPTIONS, 'native_row_ids': selected}
            intents.write(canonical(intent)); intents.flush(); os.fsync(intents.fileno())
            result = linprog(c, A_ub=A, b_ub=b, bounds=[(None, None)] * model['columns_count'], method=old.METHOD, options=old.OPTIONS)
            raw = old.safe_native(dict(result)); nr = native.append({'G_index': index, 'new_call_number': new_calls,
                'native_row_ids': selected, 'result': raw})
            hint = dict(raw); ineq = dict(raw.get('ineqlin', {})); marg = ineq.get('marginals')
            if isinstance(marg, list) and len(marg) == len(selected):
                full = [0.0] * len(model['rows'])
                for rid, value in zip(selected, marg): full[rid] = value
                ineq['marginals'] = full
            hint['ineqlin'] = ineq
            exact = recon.reconstruct(hint, model, alg, cells); verification = rawcheck.verify(model, exact)
            record = {'G_index': index, 'pair': [i, j], 'chart': old.CHARTS[chart], 'native_record': nr,
                'model_sha256': digest, 'original_components': {str(cid): cache_refs[cid] for cid in (i, j)},
                'normalized_exact_reconstruction': exact, 'separate_raw_verification': verification,
                'native_status_not_mathematical_evidence': raw.get('status'), 'actual_F_counterexample': False}
            outcome = 'Lower' if verification['Lower'] else 'unresolved'; packet = None; cref = None
            reason = None
            if not verification['Lower'] and verification['Below']:
                stage = 'fixed_curvature_after_Below_' + str(index)
                record['durable_exact_Below_candidate'] = candidates.append(record)
                if verification.get('dual_valid'):
                    curvature_attempts += 1
                    packet, reason = curved.attempt(record, model, [cache[i], cache[j]], source, params,
                        frozen_O, provider, network, cell_cache, cell_refs, before_cell, append_cell, lambda: limit(start, gate))
                    if packet is not None:
                        cref = curvature_stream.append(packet)
                        if packet['conditional_pair_floor_closes']: outcome = 'curvature_Lower'
                else: reason = 'exact_Below_has_no_valid_fixed_raw_dual'
            elif not verification['Lower']: reason = 'fixed_support_did_not_produce_exact_Lower_or_exact_Below'
            record.update({'outcome': outcome, 'original_model_outcome': 'Lower' if verification['Lower'] else 'Below' if verification['Below'] else 'unresolved',
                'curvature_record': cref, 'nonclosure_reason': reason})
            proof = records.append(record)
            sr = selectors.append(curved.selector(record, outcome, packet)) if outcome != 'unresolved' else None
            commits.append(index, outcome, new_calls, proof, sr)
            if commits.count % 25 == 0 or packet is not None or outcome == 'unresolved':
                print(json.dumps({**commits.summary(), 'last_G_index': index, 'new_LP_calls': new_calls,
                    'total_LP_calls': OLD_CALLS + new_calls, 'unique_REG_cells_including_seed': len(cell_cache),
                    'curvature_attempts': curvature_attempts, 'seconds': time.monotonic() - start}), flush=True)
            if outcome == 'unresolved':
                stop_reason = reason; break
        stage = 'final_input_and_runtime_identity'
        after = {name: pin(ROOT / name) for name in refs}; assert after == refs
        assert old.runtime_hashes(runtime) == external
        complete = commits.count == EXPECTED
        write(HERE / 'result.json', {'schema': 'P-complete-pooled-plus-fixed-curvature-result-v1', 'pid': os.getpid(),
            'seconds': time.monotonic() - start, **commits.summary(), 'complete_original_H_range': complete,
            'all_range_conditional_Lower_candidate': complete and not commits.counts['unresolved'],
            'first_nonclosed_case_stop_reason': stop_reason, 'unvisited_suffix': EXPECTED - commits.count,
            'previous_LP_calls': OLD_CALLS, 'new_LP_calls': new_calls, 'total_LP_calls': OLD_CALLS + new_calls,
            'repeated_previous_LP_calls': 0, 'curvature_attempts': curvature_attempts,
            'new_original_REG_cell_queries': new_cell_queries, 'audited_seed_cells_reused_without_evaluation': 23,
            'unique_original_REG_cells_including_seed': len(cell_cache),
            'inputs_sha256_start': refs, 'inputs_sha256_end': after, 'external_runtime_sha256_start': external,
            'external_runtime_sha256_end': old.runtime_hashes(runtime), 'independent_allrange_replay_pending': True,
            'whole_domain_Lean_unconditional_record_or_submission_acceptance_proven': False,
            'source_runtime_payload_budget': 'unknown', 'automatic_retry_or_resume': False})
    except WorkLimit as exc:
        write(HERE / 'inconclusive.json', {'stage': stage, 'reason': str(exc), 'seconds': time.monotonic() - start,
            'progress': commits.summary() if commits else None, 'new_LP_calls_started': new_calls,
            'new_CellA_queries_started': new_cell_queries, 'curvature_attempts_started': curvature_attempts,
            'previous_LP_calls': OLD_CALLS, 'unvisited_suffix_not_classified': True, 'automatic_retry': False})
    except BaseException as exc:
        write(HERE / 'failure.json', {'stage': stage, 'error': repr(exc), 'traceback': traceback.format_exc(),
            'pid': os.getpid(), 'seconds': time.monotonic() - start, 'progress': commits.summary() if commits else None,
            'new_LP_calls_started': new_calls, 'new_CellA_queries_started': new_cell_queries,
            'curvature_attempts_started': curvature_attempts, 'previous_LP_calls': OLD_CALLS, 'automatic_retry': False})
        raise
    finally:
        if commits: commits.close()
        if intents: intents.close()
        if query_intents: query_intents.close()
        for stream in streams: stream.close()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--execute-authorized-complete-curvature-P', action='store_true')
    ap.add_argument('--gate'); ap.add_argument('--gate-sha256'); args = ap.parse_args()
    if not args.execute_authorized_complete_curvature_P:
        print(json.dumps({'prepared_only': True, 'mathematical_runs': 0})); return
    assert args.gate and args.gate_sha256
    execute(checked(args.gate), args.gate_sha256)

if __name__ == '__main__': main()
