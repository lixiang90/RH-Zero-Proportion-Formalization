"""Independent stdlib audit of the clipped potential discovery/recovery.

Reconstruct the frozen29171 gap-pool byte hash from NPZ rows without
NumPy, check output-only source fork and raw OptimizeResult hashes,
and replay exact rational potential antisymmetry/range/budget arithmetic.
No optimizer import/call, kernel evaluation, adversary or global-floor proof.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, ast, gzip, hashlib, json, math, struct, time, zipfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'independent-replay.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();p=json.loads((HERE/'recovery-pilot.json').read_bytes());start=json.loads((HERE/'recovery-LP-started.json').read_bytes())
    failed=json.loads((HERE/'failure-receipt.json').read_bytes());failurepin=json.loads((HERE/'failure-files.json').read_bytes())
    inputs={**p['source_sha256_start'],Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__)),
        (HERE/'recovery-pilot.json').relative_to(ROOT).as_posix():digest(HERE/'recovery-pilot.json'),
        (HERE/'recovery-LP-started.json').relative_to(ROOT).as_posix():digest(HERE/'recovery-LP-started.json'),
        (HERE/'raw-result.json.gz').relative_to(ROOT).as_posix():digest(HERE/'raw-result.json.gz')}
    assert p['source_sha256_start']==p['source_sha256_end']==start['source_sha256_start']and p['all_sources_unchanged']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    for row in failurepin['package_files']:assert digest(ROOT/row['path'])==row['sha256']and (ROOT/row['path']).stat().st_size==row['bytes']
    assert failed['LP_calls_started']==1 and failed['LP_result_object_not_persisted']and failed['no_retry_performed']
    assert p['actual_total_LP_calls_including_failed_output']==2 and p['this_recovery_LP_calls']==p['LP_calls']==1
    assert p['serialization_preflight_passed']and start['complete_JSON_schema_preflight_passed']and start['no_further_retry_authorized']
    original=(HERE/'clipped_pilot.py').read_text();recovery=(HERE/'clipped_recovery.py').read_text()
    def solve_calls(source):return [ast.dump(n,include_attributes=False)for n in ast.walk(ast.parse(source))if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='linprog']
    assert len(solve_calls(original))==len(solve_calls(recovery))==1 and solve_calls(original)==solve_calls(recovery)
    left='    rows=[];counts=[];gram=';right="    startdoc={'scope':"
    assert original[original.index(left):original.index(right)]==recovery[recovery.index(left):recovery.index(right)]
    rawbytes=gzip.decompress((HERE/'raw-result.json.gz').read_bytes());raw=json.loads(rawbytes)
    rawsha=hashlib.sha256(rawbytes).hexdigest();assert rawsha==p['raw_result_sha256']=='3b67809953e3460ca103a428e6a834714bb628138f0da56cf95a7c19ee792e7c'
    assert raw['source_sha256_start']==p['source_sha256_start']and raw['actual_total_LP_calls_including_failed_output']==2
    result=raw['result'];x=result['x'];assert len(x)==9 and all(math.isfinite(v)for v in x)
    assert result['status']==p['LP_status']==0 and result['success']==p['LP_success']is True
    assert x==p['raw_variables']and x[:4]==p['raw_v']and x[4:8]==p['raw_absolute_auxiliaries']and x[8]==p['sample_floor_hint']
    assert result['fun']==-x[8]and raw['LP_seconds']==p['LP_seconds']
    assert len(result['ineqlin']['residual'])==len(result['ineqlin']['marginals'])==29180
    assert abs(-min(result['ineqlin']['residual'])-p['maximum_LP_row_violation_hint'])<1e-12
    assert p['time_limit_seconds']==30 and p['method']=='highs'and p['variables']==9 and p['inequalities']==29180
    assert p['sample_count']==29171 and p['fixed_sample_gap_array_sha256']=='7ff5940c1b622d1da96a6ffa1840b578c1f81617fbd766760b208cf93d449f8e'
    # Reconstruct exactly the old sample order and native little-endian f64 bytes.
    h=hashlib.sha256();count=0;counts=[];SEP=F(123,128)
    gram_path=ROOT/'research-goal-20261016/cover-newwindow-gram.json';gram=json.loads(gram_path.read_bytes())
    for row in gram['results']:
        values=[float(F(v))for v in row['anchor']];assert len(values)==9;h.update(struct.pack('<9d',*values));count+=1
    counts.append({'source':gram_path.relative_to(ROOT).as_posix(),'legal_rows':len(gram['results'])})
    for name in ['research-20261016-followup/window_reweight_challenge.json','research-20261016-followup/window_profile_24_challenge.json']:
        values=json.loads((ROOT/name).read_bytes())['best_gaps'];assert len(values)==9 and min(values)>=float(SEP)
        h.update(struct.pack('<9d',*values));count+=1;counts.append({'source':name,'legal_rows':1})
    for name in ['research-20261016-followup/window_profile_24.npz','research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz']:
        legal=0
        with zipfile.ZipFile(ROOT/name)as z,z.open('gaps.npy')as stream:
            assert stream.read(6)==b'\x93NUMPY';version=tuple(stream.read(2));length=struct.unpack('<H'if version==(1,0)else'<I',stream.read(2 if version==(1,0)else 4))[0]
            head=ast.literal_eval(stream.read(length).decode().strip());assert head['descr']=='<f8'and not head['fortran_order']and head['shape'][1]==9
            total=head['shape'][0]
            for _ in range(total):
                block=stream.read(72);assert len(block)==72;values=struct.unpack('<9d',block)
                if min(values)>=float(SEP):h.update(block);legal+=1;count+=1
            assert not stream.read(1)
        counts.append({'source':name,'original_rows':total,'legal_rows':legal})
    assert count==29171 and h.hexdigest()==p['fixed_sample_gap_array_sha256']and counts==p['sample_sources']
    # Formal phi coefficients, valid for arbitrary actual clipped values.
    columns=[]
    for j in range(4):
        v=[0]*9;v[j]+=1;v[j+1]-=1;v[7-j]-=1;v[8-j]+=1
        assert v==v[::-1]and sum(v)==0;columns.append(v)
    assert columns==[[1,-1,0,0,0,0,0,-1,1],[0,1,-1,0,0,0,-1,1,0],[0,0,1,-1,0,-1,1,0,0],[0,0,0,1,-2,1,0,0,0]]
    D=p['rational_common_denominator'];assert D==10**12
    nums=[int(round(float(v)*D))for v in x[:4]];cn=math.floor(x[8]*D);v=[F(n,D)for n in nums];c=F(cn,D);osc=2*sum(map(abs,v),F(0))
    assert nums==p['rational_v_numerators']and cn==p['rational_c_numerator']and list(map(str,v))==p['rational_v']and str(c)==p['rational_c']
    assert osc==F(p['rational_oscillation_upper'])and osc<=c and 0<=c<=F(1,64)
    assert F(p['rational_budget_slack'])==c-osc and p['rational_oscillation_le_c']and p['rational_c_in_range']
    assert not p['floor_upper_cap_active_hint']and not p['oscillation_budget_active_hint']
    assert abs(p['sample_floor_hint']-p['minimum_sample_G_hint']-p['maximum_LP_row_violation_hint'])<1e-12
    assert p['sample_floor_gain_over_zero_V_hint']==p['sample_floor_hint']-p['zero_potential_sample_minimum_hint']
    for n,hsh in inputs.items():assert digest(ROOT/n)==hsh
    out={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
        'actual_total_LP_calls_recorded':2,'original_LP_result_lost_by_serialization':True,'authorized_identical_recovery_calls':1,
        'LP_model_and_settings_unchanged_between_calls':True,'raw_result_uncompressed_sha256':rawsha,
        'frozen_sample_pool_rebuilt_without_numpy':True,'sample_count':count,'pool_sha256':h.hexdigest(),
        'same_current24_profile_and_ledger_input':True,'four_features_reverse_symmetric_and_zero_sum':True,
        'rational_v':list(map(str,v)),'rational_c':str(c),'exact_rational_oscillation_upper':str(osc),'exact_oscillation_le_c':True,
        'recorded_zeroV_sample_minimum_hint':p['zero_potential_sample_minimum_hint'],'recorded_LP_floor_hint':p['sample_floor_hint'],
        'recorded_gain_hint':p['sample_floor_gain_over_zero_V_hint'],'recorded_row_violation_hint':p['maximum_LP_row_violation_hint'],
        'comparison':'The tiny apparent sampled-floor gain is of the same scale as the LP row tolerance; no reliable structural gain is established.',
        'floor_upper_cap_active':False,'oscillation_budget_active':False,'LP_calls':0,'kernel_evaluations':0,
        'candidate_actual_scalar_constraints_independently_checked':False,'new_Lean_invocations':0,
        'old_minimizer_KKT_or_Newton_certificate_reused':False,'global_mean_floor_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'actual_total_LP_calls':2,'pool_sha256':h.hexdigest(),'rational_oscillation_le_c':True,
        'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
