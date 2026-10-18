"""One authorized fixed Stage B classification; no pairs, new witnesses or queries.

Original Stage A Python is reused as a producer, not called an independent audit.
All original leaves/guards are replayed at their original cN.  The only new test
is margin - 335544320000000000 * 300000000000000 >= 0.  Source analytic
soundness and future formal consumers remain separate proof obligations.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from collections import Counter
from contextlib import ExitStack
import gzip
import json
import os
import sys
import time
import traceback

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BASE = ROOT / 'research-goal-20261018-record-baseline-replay'
sys.path.insert(0, str(BASE))
import packing_parser_v3 as parser
import record_math as math
import replay_baseline as original

CN = 893616123055294719
TAU_N = 893916123055294719
DELTA_N = 300000000000000
SA = 10**20
SC = 32768
SEP = F(17, 20)
SLOPE = 335544320000000000
DEBIT = SLOPE * DELTA_N
TRACE_SHA = 'c486090f64a67eccae8de6914688626738e212ebe7ade515d6825efa28abc10e'
MAX_SECONDS = 180
MAX_BYTES = 32000000
PINS = {
    'research-goal-20261018-record-baseline-replay/files.json': '03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f',
    'research-goal-20261018-record-baseline-independent/audit-files.json': '2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c',
    'research-goal-20261018-stageB-static-contract/contract-files.json': 'b9d9315cd76e9be9d4c860fe1368d06433e8ccabdeb5740b0109140ffa8c17f8',
    'research-goal-20261016/gates/stageB-20261018.json': '1548e22dcd1446a7110cb3c2452a574d0edc323c3bb81b35591a1d0e93324273',
}


def digest(path):
    h = sha256()
    with path.open('rb') as f:
        for part in iter(lambda: f.read(1024*1024), b''): h.update(part)
    return h.hexdigest()


def dump_new(path, data):
    with path.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(data, f, ensure_ascii=True, indent=2)
        f.write('\n'); f.flush(); os.fsync(f.fileno())


def load(path): return json.loads(path.read_text(encoding='utf-8'))
def canon(data): return original.canonical(data)
def rel(path): return path.relative_to(ROOT).as_posix()
def output_bytes(): return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())


def check_inputs():
    """Verify both full closed A packages and the written fixed authorization."""
    checked = {rel(Path(__file__)): digest(Path(__file__)),
               rel(HERE/'run_once.py'): digest(HERE/'run_once.py')}
    def one(row):
        path = ROOT / row['path']; actual = digest(path)
        assert actual == row['sha256'], ('input_sha', row['path'], actual)
        if 'bytes' in row: assert path.stat().st_size == row['bytes'], ('input_size', row['path'])
        if row['path'] in checked: assert checked[row['path']] == actual
        checked[row['path']] = actual
    packages = {}
    for path, expected in PINS.items():
        one({'path': path, 'sha256': expected})
        data = load(ROOT / path); packages[path] = data
        for field in ['files', 'package_files', 'dependency_files', 'dependencies', 'read_only_existing_references']:
            for row in data.get(field, []): one(row)
    decision = packages['research-goal-20261016/gates/stageB-20261018.json']
    assert decision['classification_passes_authorized'] == 1
    assert int(decision['tau_numerator']) == TAU_N
    assert int(decision['delta_numerator']) == DELTA_N
    assert int(decision['SLOPE']) == SLOPE
    assert decision['resource_limits'] == {'elapsed_seconds': MAX_SECONDS, 'closed_output_bytes': MAX_BYTES}
    a = load(BASE / 'baseline-replay.json')
    ai = load(ROOT / 'research-goal-20261018-record-baseline-independent/independent-replay.json')
    wz = load(BASE / 'root-wz-replay.json')
    assert a['passed'] and ai['passed'] and wz['passed']
    assert ai['producer_manifest_sha256'] == PINS['research-goal-20261018-record-baseline-replay/files.json']
    assert ai['canonical_trace_sha256'] == a['trace']['uncompressed_canonical_jsonl_sha256'] == TRACE_SHA
    assert ai['all160_WZ_values_and_margins_equal_producer']
    assert ai['corrected_independent_WD_identity_count'] == 48
    assert ai['original_cN'] == a['original_cN'] == CN
    assert type(ai['producer_Python_modules_imported']) is int and ai['producer_Python_modules_imported'] == 0
    return checked, a, ai, wz


def debit_identity():
    tree = math.direct_mcheck_tree()
    assert tree[0] == 'Nat.ble' and len(tree) == 3
    def occurrences(t):
        return int(t == 'cN') if isinstance(t, str) else sum(map(occurrences, t))
    assert occurrences(tree) == 1 and occurrences(tree[2]) == 0
    path = []
    def extract(t):
        if t == ['Nat.mul', str(SLOPE), 'cN']: return
        assert isinstance(t, list) and t[0] == 'Nat.add' and len(t) == 3, ('cN_nonadditive_path', t[:2])
        sides = [i for i in [1, 2] if occurrences(t[i])]
        assert len(sides) == 1
        path.append(sides[0]); extract(t[sides[0]])
    extract(tree[1])
    assert CN + DELTA_N == TAU_N and math.CN == CN and math.SLOPE == SLOPE
    return {'original_printed_Nat_ble_AST_sha256': sha256(canon(tree)).hexdigest(),
            'cN_occurrences': 1, 'cN_in_rhs': False, 'lhs_additive_path': path,
            'unique_threshold_term': ['Nat.mul', str(SLOPE), 'cN'],
            'source_mcheckP_definition_sha256': math_model['definitions']['mcheckP'],
            'other_AST_subexpressions_unchanged': True, 'source_cN_not_modified': True,
            'delta_numerator': DELTA_N, 'integer_debit': DEBIT,
            'identity': 'M_tau = RHS-LHS(cN)-SLOPE*DeltaN', 'passed': True}


def root_outside(model, wz):
    """Only arithmetic on original proven COV guards; never evaluate WZ anew."""
    bs = model['BS']; B = F(sum(bs), SA); tau = F(TAU_N, SA); c = F(CN, SA)
    known = {(r['gap'], r['lo'], r['hi']): r for r in wz['all_guard_rows']}
    assert len(known) == 160 and len(bs) == 8 and all(b > 0 for b in bs)
    assert all(a > 0 for _i, _j, a, _slot in model['TS'])
    rows = []; covkeys = set(); outside_floor = c + SEP*B
    assert outside_floor >= tau
    for r in range(8):
        edge = [a for i,j,a,_ in model['TS'] if (i,j) == (r,r+1)]
        assert len(edge) == 1
        cursor = 16384
        for lo, hi, truth in model['COV'][r]:
            assert cursor == lo <= hi < 1048576
            cursor = hi
            if not truth: continue
            k = (r,lo,hi); g = known[k]; covkeys.add(k)
            assert g['adjacent_coefficient'] == edge[0]
            assert g['left_cN_times_SW'] == CN * 10**13
            assert g['right_a_times_WZ'] == edge[0] * g['WZ']
            assert g['margin'] == g['right_a_times_WZ'] - g['left_cN_times_SW'] >= 0
            rows.append({'kind':'original_true_COV_plus_pressure', 'gap':r, 'lo':lo,'hi':hi,
                         'original_WZ_guard_margin':g['margin'], 'lower_bound':str(outside_floor),
                         'margin_over_tau':str(outside_floor-tau), 'passed':True})
        assert cursor == model['SMAX'][r]
        tail = F(bs[r]*model['SMAX'][r], SC*SA) + SEP*(B-F(bs[r],SA))
        assert tail >= tau, ('tail_raised_payment',r,str(tail-tau))
        rows.append({'kind':'pressure_tail', 'gap':r, 'SMAX':model['SMAX'][r],
                     'lower_bound':str(tail), 'margin_over_tau':str(tail-tau),
                     'same_gap_pressure_counted_once':True,'passed':True})
        assert SEP > F(1,2)
        rows.append({'kind':'small_gap_disjoint_from_separation','gap':r,
                     'small_gap_upper':'1/2','separation':str(SEP),'passed':True})
    assert covkeys == set(known) and len(rows) == 176
    return {'rows':rows,'COV_original_true_count':160,'pressure_tails':8,
            'small_gap_empty_cases':8,'COV_continuity_all_rows_checked':True,
            'all_false_COV_root_products_covered_by_original48':True,
            'sum_pressure_B':str(B),'true_COV_common_lower_bound':str(outside_floor),
            'new_WZ_evaluations':0,'original_stageA_guard_values_only':True,
            'all_raised_root_outside_payments_passed':True,
            'boundaries':'Original closed COV/root/tail endpoints retained; small branch h<=1/2 is empty even with its endpoint.'}


def witness_identity(walker, pos, node, model):
    flat = node['state']; state = (list(flat[0:72:2]), list(flat[1:72:2]))
    word = walker.bits(pos) >> 2; offset = 0; fs = []
    for i,j,_a,_slot in model['TS']:
        lower,upper = math.term_bounds(state,i,j)
        f,offset = math.dec(word,offset,lower,upper); fs.append(f)
    P,S,Cp,Cm,consumed = math.ydec(word,offset,state)
    assert consumed == node['end']-pos-2 and 0 < consumed <= 478
    semantic = {'FS':fs,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':consumed}
    packed = {'bits':consumed,'value':str(word & ((1<<consumed)-1))}
    return {'WD':walker.r,'original_leaf_position':pos,'payload_bit_position':pos+2,
            'consumed_payload_bits':consumed,'original_rdw_block':pos//32768,
            'original_rdw_shift':pos%32768,'packed_payload_sha256':sha256(canon(packed)).hexdigest(),
            'decoded_semantic_sha256':sha256(canon(semantic)).hexdigest()}


def main():
    assert __debug__
    assert sys.argv[1:] == ['--execute-fixed-stage-B'], 'Explicit fixed execution flag required'
    assert not any((HERE/n).exists() for n in ['started.json','classification.json','failure.json',
        'all-node-events.jsonl.gz','numeric-classification.jsonl.gz','exception-cells.jsonl.gz'])
    started = time.monotonic(); walker = None; rootrows = []; totals=Counter(); ready=Counter()
    classcounts=Counter(); provenance=[]; last_stage='input_guards'; before={}
    before,a,ai,wz = check_inputs()
    begin={'schema':'fixed-new-record-stageB-start-v1','pid':os.getpid(),'time_unix':time.time(),
           'source_sha256':parser.SOURCE_SHA,'script_sha256':digest(Path(__file__)),
           'original_cN':CN,'tau_numerator':TAU_N,'denominator':SA,
           'fixed_delta_numerator':DELTA_N,'classification_attempt':1,'inputs_sha256':before,
           'limits':{'seconds':MAX_SECONDS,'closed_output_bytes':MAX_BYTES}}
    dump_new(HERE/'started.json',begin); print(json.dumps(begin),flush=True)
    def limits():
        assert time.monotonic()-started <= MAX_SECONDS, '180_second_resource_limit'
        assert output_bytes() <= MAX_BYTES, '32000000_closed_output_limit'
    def progress(root,pos,counts):
        limits()
        p={'pid':os.getpid(),'stage':last_stage,'root':root,'position':pos,'completed_roots':len(rootrows),
           'completed_counts':dict(totals),'current_root_counts':dict(counts),
           'classification_counts':dict(classcounts),'seconds':time.monotonic()-started,'rss':original.rss()}
        (HERE/'progress.json').write_text(json.dumps(p,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(p),flush=True)
    digests={name:sha256() for name in ['trace','numeric','exceptions']}; raw_bytes=Counter()
    try:
        global math_model
        last_stage='load_original_source_model'; math_model=parser.load_model(); model=math_model; math.configure(model)
        assert model['CN']==CN and model['SA']==SA
        last_stage='printed_AST_threshold_identity'; astidentity=debit_identity()
        last_stage='raised_root_outside_payments'; outside=root_outside(model,wz)
        dump_new(HERE/'root-outside-payments.json',outside)
        names={'trace':'all-node-events.jsonl.gz','numeric':'numeric-classification.jsonl.gz','exceptions':'exception-cells.jsonl.gz'}
        with ExitStack() as stack:
            streams={}
            for key,name in names.items():
                raw=stack.enter_context((HERE/name).open('xb'))
                streams[key]=stack.enter_context(gzip.GzipFile(fileobj=raw,mode='wb',filename='',mtime=0))
            def write(key,row):
                data=canon(row);streams[key].write(data);digests[key].update(data);raw_bytes[key]+=len(data)
            for r in range(48):
                last_stage='original_tree_guards_and_fixed_classification'
                walker=original.FullWalker(r,model,streams['trace'],digests['trace'],progress)
                rec=model['roots'][r]
                end,height=walker.walk(math.root(rec['indices']),rec['pos'],rec['fuel'])
                assert end==rec['expected']
                contracts,stats=walker.ready_contracts(); ready.update(stats)
                assert contracts == [c for c in a['all70_ready_contracts'] if c['root']==r]
                provenance.extend(contracts)
                paths={}
                def assign(pos,path):
                    paths[pos]=path; node=walker.nodes[pos]
                    if node['kind']=='branch':
                        assign(node['left'],path+'0');assign(node['right'],path+'1')
                assign(1,'r'); rc=Counter()
                for pos,node in sorted(walker.nodes.items()):
                    if node['kind']=='reflection':
                        assert node['state'][15] < node['state'][0]
                        rc['reflection_ordered_half_exclusions']+=1; continue
                    if node['kind']=='branch':continue
                    assert node['kind']=='numeric', ('unexpected_leaf_kind',r,pos,node['kind'])
                    m0=node['margin']; mt=m0-DEBIT
                    kind='closed_numeric_at_tau' if mt>=0 else 'exception'
                    rc[kind]+=1
                    state_sha=original.FullWalker.last_state_hash(node)
                    nested=[{'name':c['name'],'state':c['state'],'start':c['pos'],'end':c['expected'],
                             'fuel':c['fuel'],'state_sha256':c['state_sha256']}
                            for c in contracts if c['pos']<=pos<c['expected']]
                    witness=witness_identity(walker,pos,node,model)
                    common={'root':r,'position':pos,'end':node['end'],'path':paths[pos],
                            'kind':kind,'original_margin':str(m0),'tau_margin':str(mt),
                            'state_sha256':state_sha,'witness':witness}
                    write('numeric',common)
                    if mt<0:
                        flat=node['state'];lo=list(flat[0:72:2]);hi=list(flat[1:72:2])
                        assert flat[-1]==0 and len(lo)==len(hi)==36
                        # Do not round sep*SC or drop any non-adjacent interval.
                        exception={**common,'exception_id':classcounts['exception']+rc['exception']-1,
                            'state':{'L':lo[:8],'U':hi[:8],'A':lo[8:],'B':hi[8:],'M':0},
                            'coordinate_scale':SC,'nested_provenance':nested,
                            'root_provenance':{'indices':rec['indices'],'fuel':rec['fuel'],'start':rec['pos'],'end':end},
                            'separation':'17/20','relaxed_orientation':True,
                            'omitted_orientation_condition':'h0 <= h7',
                            'original_cell_is_closed':True,'actual_low_energy_point_claimed':False}
                        write('exceptions',exception)
                totals.update(walker.count);classcounts.update(rc)
                row={'root':r,'end':end,'expected':rec['expected'],'height':height,
                     'counts':dict(walker.count),'classification_counts':dict(rc),
                     'min_original_margin':walker.minmargin,'min_margin_position':walker.minpos}
                old=a['per_root'][r]
                assert all(row[k]==old[k] for k in ['root','end','expected','height','counts','min_original_margin','min_margin_position'])
                rootrows.append(row)
                for stream in streams.values():stream.flush()
                progress(r,end,Counter())
        last_stage='closed_outputs_and_identity_checks'
        assert dict(totals)==a['derived_counts']==ai['derived_counts']
        assert dict(ready)==a['ready_contract_counts']==ai['ready_contract_counts']
        assert len(rootrows)==48 and len(provenance)==70
        assert totals.get('farkas_leaves',0)==0 and classcounts['reflection_ordered_half_exclusions']==595
        assert classcounts['closed_numeric_at_tau']+classcounts['exception']==totals['numeric_leaves']==13046
        assert digests['trace'].hexdigest()==TRACE_SHA
        after={path:digest(ROOT/path) for path in before};assert before==after
        outputs={k:{'path':rel(HERE/name),'bytes':(HERE/name).stat().st_size,'sha256':digest(HERE/name),
                    'uncompressed_canonical_jsonl_sha256':digests[k].hexdigest(),
                    'uncompressed_bytes':raw_bytes[k] if k!='trace' else None}
                 for k,name in names.items()}
        # This is a concrete geometry syntax measurement, not a formal consumer.
        literal_bytes=0
        with gzip.open(HERE/names['exceptions'],'rt',encoding='ascii') as f:
            for line in f:
                e=json.loads(line);s=e['state']
                flat=[v for pair in zip(s['L']+s['A'],s['U']+s['B']) for v in pair]+[s['M']]
                literal_bytes+=len(('<'+','.join(map(str,flat))+'>,\n').encode('ascii'))
        assert parser.SOURCE.stat().st_size==1818411
        budget={'baseline_source_bytes':1818411,'decimal_site_cap':2000000,
                'baseline_only_remaining_bytes':181589,
                'old_three_bridge_bodies_reference_bytes':38361,
                'remaining_after_reference_bridges':143228,
                'exception_73_decimal_integer_literal_payload_bytes':literal_bytes,
                'literal_syntax_is_not_a_validated_Lean_encoding':True,
                'new_formal_consumer_bytes':None,'DBM_pair_proof_bytes':None,
                'new_actual_kernel_bridges_and_wrapper_bytes':None,
                'complete_flattened_Lean_source_bytes':None,'kernel_export_Nano_seconds':None,
                'complete_source_and_runtime_gate_passed':False,
                'small_JSON_or_gzip_is_not_a_source_budget_proof':True}
        result={'schema':'fixed-record-stageB-complete-classification-v1','passed':True,
            'stage':'all_original_roots_and_fixed_classification_finished','pid':os.getpid(),
            'seconds':time.monotonic()-started,'rss':original.rss(),'classification_passes':1,
            'inputs_sha256_start':before,'inputs_sha256_end':after,
            'source_sha256_start':parser.SOURCE_SHA,'source_sha256_end':digest(parser.SOURCE),
            'original_cN':CN,'tau_numerator':TAU_N,'denominator':SA,'separation':'17/20',
            'integer_debit':str(DEBIT),'threshold_AST_identity':astidentity,
            'derived_counts':dict(totals),'ready_contract_counts':dict(ready),'classification_counts':dict(classcounts),
            'pair_order_from_source':math.ALL,'PR_order_from_source':model['PR'],
            'per_root':rootrows,'all70_ready_contracts':provenance,
            'all_original_guards_and_witnesses_replayed_unchanged':True,
            'canonical_all_node_trace_equal_StageA':True,'canonical_all_node_trace_sha256':TRACE_SHA,
            'root_outside_payments_path':rel(HERE/'root-outside-payments.json'),
            'root_outside_payments_sha256':digest(HERE/'root-outside-payments.json'),
            'all_raised_root_outside_payments_passed':True,'outputs':outputs,
            'reflection_leaves_used_as_energy_payments':0,'orientation_relaxed_for_exception_cells':True,
            'outer_cover_domain':'Every arbitrary 8-gap h>=17/20 with F9(h)<tau; no minimizer assumption.',
            'outer_cover_statement':'In ordered h0<=h7 each sublevel point lies in one closed exception cell. Reversal gives union of these cells and their reversals for the whole separated sublevel.',
            'orientation_note':'Dropping h0<=h7 enlarges each closed cell; it is not encoded as a single difference edge. At equality choose the identity orientation.',
            'source_analytic_LB_PT_WZ_and_reversal_soundness_retained':True,
            'source_analytic_proofs_or_Lean_kernel_replayed_here':False,
            'source_budget':budget,'exception_pairs_scanned':0,'new_kernel_queries':0,
            'new_witnesses':0,'optimizer_calls':0,'Lean_runs':0,'new_separated_floor_proven':False,
            'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'website_submission_ready':False,'independent_StageB_review_pending':True}
        limits();dump_new(HERE/'classification.json',result);limits()
        print(json.dumps({k:result[k] for k in ['passed','stage','pid','seconds','classification_counts','rss']}),flush=True)
    except BaseException as exc:
        failure={'schema':'fixed-record-stageB-failure-v1','passed':False,'stage':last_stage,
            'pid':os.getpid(),'seconds':time.monotonic()-started,'error':repr(exc),
            'traceback':traceback.format_exc(),'completed_roots':len(rootrows),
            'completed_counts':dict(totals),'classification_counts':dict(classcounts),
            'last_node':walker.last if walker else None,'inputs_sha256_start':before,
            'source_sha256_end':digest(parser.SOURCE),'automatic_retry_allowed':False}
        dump_new(HERE/'failure.json',failure);print(json.dumps(failure),flush=True);raise


if __name__=='__main__':main()
