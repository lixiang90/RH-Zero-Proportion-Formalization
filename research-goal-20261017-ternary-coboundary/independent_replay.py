"""Independent stdlib replay of the fixed ternary potential discovery.

No solver/producer imports or kernel evaluation. Reconstruct the frozen
sample pool and ternary words from NPZ/JSON bytes; check canonical
antisymmetry, sparse layout counts, raw-result hashes and exact rational
range bounds. Exact sample residuals below use saved binary float F,
not actual analytic F enclosures and do not certify a global floor.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,ast,gzip,hashlib,json,math,struct,time,zipfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'independent-replay.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rev8(s):
    d=[]
    for _ in range(8):d.append(s%3);s//=3
    return sum(x*3**i for i,x in enumerate(d[::-1]))
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();p=json.loads((HERE/'ternary-pilot.json').read_bytes());start=json.loads((HERE/'LP-started.json').read_bytes())
    inputs={**p['source_sha256_start'],Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__)),
        (HERE/'ternary-pilot.json').relative_to(ROOT).as_posix():digest(HERE/'ternary-pilot.json'),
        (HERE/'LP-started.json').relative_to(ROOT).as_posix():digest(HERE/'LP-started.json'),
        (HERE/'raw-result.json.gz').relative_to(ROOT).as_posix():digest(HERE/'raw-result.json.gz')}
    assert p['source_sha256_start']==p['source_sha256_end']==start['source_sha256_start']and p['all_sources_unchanged']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    assert p['LP_calls']==start['LP_calls_authorized']==1 and start['complete_JSON_schema_preflight_passed']and start['no_retry_authorized']
    assert p['method']=='highs'and p['time_limit_seconds']==30 and p['LP_status']==0 and p['LP_success']
    assert p['variables']==3241 and p['sample_rows']==29171 and p['state_bound_rows']==6480 and p['inequalities']==35651 and p['matrix_nonzeros']==95930
    calls=[n for n in ast.walk(ast.parse((HERE/'ternary_pilot.py').read_text()))if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='linprog']
    assert len(calls)==1 and {v.arg:ast.unparse(v.value)for v in calls[0].keywords}['options']=="{'time_limit': 30.0}"
    rawbytes=gzip.decompress((HERE/'raw-result.json.gz').read_bytes());raw=json.loads(rawbytes)
    assert hashlib.sha256(rawbytes).hexdigest()==p['raw_result_sha256']=='3121ebecebf75f05c32d13eb5d0d6633d98ae51ce79b66cc2c8cf037fbafd522'
    assert raw['LP_calls_this_model']==1 and raw['source_sha256_start']==p['source_sha256_start']and raw['derived_fixed_sample_data']==p['derived_fixed_sample_data']
    result=raw['result'];x=result['x'];assert len(x)==3241 and all(isinstance(v,(int,float))and math.isfinite(v)for v in x)
    assert x==p['raw_variables']and x[:3240]==p['raw_canonical_potentials']and x[3240]==p['sample_floor_hint']and result['fun']==-x[3240]
    assert result['status']==p['LP_status']and result['success']and raw['LP_seconds']==p['LP_seconds']
    assert len(result['ineqlin']['residual'])==len(result['ineqlin']['marginals'])==35651
    assert abs(-min(result['ineqlin']['residual'])-p['maximum_LP_row_violation_hint'])<1e-12
    derived={}
    for name,info in p['derived_fixed_sample_data'].items():
        path=HERE/name;assert digest(path)==info['sha256']and path.stat().st_size==info['bytes']
        data=gzip.decompress(path.read_bytes());assert hashlib.sha256(data).hexdigest()==info['uncompressed_sha256']and len(data)==info['uncompressed_bytes']
        derived[name]=data;inputs[path.relative_to(ROOT).as_posix()]=digest(path)
    fvals=struct.unpack('<29171d',derived['float-F.bin.gz']);assert all(math.isfinite(v)for v in fvals)
    assert min(fvals)==p['zero_potential_sample_minimum_hint']
    head_tail=list(struct.iter_unpack('<HH',derived['sample-words.bin.gz']));assert len(head_tail)==29171
    # Exact fixed-pool reconstruction, preserving the old sample order.
    rows=[];gram=json.loads((ROOT/'research-goal-20261016/cover-newwindow-gram.json').read_bytes())
    rows.extend(tuple(float(F(v))for v in a['anchor'])for a in gram['results'])
    for name in ['research-20261016-followup/window_reweight_challenge.json','research-20261016-followup/window_profile_24_challenge.json']:
        rows.append(tuple(json.loads((ROOT/name).read_bytes())['best_gaps']))
    for name in ['research-20261016-followup/window_profile_24.npz','research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz']:
        with zipfile.ZipFile(ROOT/name)as z,z.open('gaps.npy')as stream:
            assert stream.read(6)==b'\x93NUMPY';version=tuple(stream.read(2));length=struct.unpack('<H'if version==(1,0)else'<I',stream.read(2 if version==(1,0)else 4))[0]
            header=ast.literal_eval(stream.read(length).decode().strip());assert header['descr']=='<f8'and not header['fortran_order']and header['shape'][1]==9
            for _ in range(header['shape'][0]):
                data=stream.read(72);assert len(data)==72;g=struct.unpack('<9d',data)
                if min(g)>=123/128:rows.append(g)
            assert not stream.read(1)
    assert len(rows)==29171 and hashlib.sha256(b''.join(struct.pack('<9d',*g)for g in rows)).hexdigest()==p['fixed_sample_gap_array_sha256']=='7ff5940c1b622d1da96a6ffa1840b578c1f81617fbd766760b208cf93d449f8e'
    canonical=[s for s in range(6561)if s<rev8(s)];assert canonical==p['canonical_states']and len(canonical)==3240
    assert sum(rev8(s)==s for s in range(6561))==p['palindromic_states_forced_zero']==81;col={s:k for k,s in enumerate(canonical)}
    def atom(s):
        r=rev8(s)
        return None if s==r else(col[min(s,r)],1 if s<r else -1)
    hist={1:0,2:0,3:0};states=set();words=set();boundary=[0,0]
    for g,(head,tail)in zip(rows,head_tail):
        cl=tuple(0 if v<=1.5 else 1 if v<=2.5 else 2 for v in g)
        assert head==sum(v*3**i for i,v in enumerate(cl[:8]))and tail==sum(v*3**i for i,v in enumerate(cl[1:]))
        states.update([head,tail]);words.add(cl);boundary[0]+=sum(v==1.5 for v in g);boundary[1]+=sum(v==2.5 for v in g);terms={}
        for code,sgn in [(head,-1),(tail,1)]:
            item=atom(code)
            if item is not None:k,s=item;terms[k]=terms.get(k,0)+sgn*s
        hist[1+sum(v!=0 for v in terms.values())]+=1
    assert len(states)==6561 and len(words)==19683 and boundary==[0,0]
    assert hist=={1:404,2:3735,3:25032}and sum(k*v for k,v in hist.items())+12960==95930
    D=p['rational_common_denominator'];assert D==10**12
    nums=[int(round(float(v)*D))for v in x[:3240]];cn=math.floor(x[3240]*D);v=[F(n,D)for n in nums];c=F(cn,D)
    assert nums==p['rational_potential_numerators']and cn==p['rational_c_numerator']and str(c)==p['rational_c']
    maxabs=max(map(abs,v));assert 2*maxabs==F(p['rational_oscillation_upper'])and str(maxabs)==p['rational_maximum_potential_absolute_value']
    assert 2*maxabs<=c and 0<=c<=F(1,64)and p['rational_all_state_bounds_absV_le_c_half']and p['rational_state_bound_violation_count']==0
    full=[]
    for s in range(6561):
        item=atom(s);full.append(F(0)if item is None else item[1]*v[item[0]])
    assert all(full[rev8(s)]==-full[s]and 2*abs(full[s])<=c for s in range(6561))
    minimum=None;violations=0;worst=None
    for row,((head,tail),ff)in enumerate(zip(head_tail,fvals)):
        slack=F.from_float(ff)+full[head]-full[tail]-c
        if minimum is None or slack<minimum:minimum=slack;worst=row
        if slack<0:violations+=1
    assert p['sample_floor_above_existing_short_pair_hint']and c>F(221,25000)and not p['floor_upper_cap_active_hint']
    assert p['larger_mean_floor_does_not_alone_improve_unconditional_kappa']and not p['actual_unconditional_kappa_inferred']
    for n,h in inputs.items():assert digest(ROOT/n)==h
    out={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
        'LP_calls_recorded_this_model':1,'read_only_replay_LP_calls':0,'pool_and_sample_word_hashes_rebuilt':True,
        'sample_rows':29171,'covered_8gap_states':6561,'covered_9gap_words':19683,'palindromic_states_zero':81,
        'canonical_potential_variables':3240,'variables':3241,'inequalities':35651,'matrix_nonzeros_recomputed':95930,
        'exact_rational_antisymmetry_checked':True,'exact_rational_all_state_bounds_checked':True,
        'rational_c':str(c),'rational_oscillation_upper':str(2*maxabs),
        'binary_float_F_finite_surrogate_rows_checked_exactly':29171,'rational_surrogate_negative_rows':violations,
        'rational_surrogate_minimum_slack':str(minimum),'rational_surrogate_worst_row':worst,
        'finite_surrogate_is_not_actual_scalar_enclosure':True,'kernel_evaluations':0,
        'recorded_sample_floor_gain_hint':p['sample_floor_gain_over_zero_V_hint'],
        'existing_short_pair_floor':'221/25000','mean_candidate_above_short_pair_floor':True,
        'unconditional_kappa_not_inferred':True,'old_F_KKT_or_Newton_certificate_reused':False,
        'new_Lean_invocations':0,'global_mean_floor_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'recorded_LP_calls':1,'exact_state_bounds':True,'rational_surrogate_negative_rows':violations,
        'minimum_surrogate_slack_hint':float(minimum),'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
