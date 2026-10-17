"""Read-only support audit: distinguish class-word cycles from real cycles.

Only existing float-F/word arrays, OptimizeResult and saved sample records
are read. No kernel evaluation, optimizer, new point or potential fit.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,struct,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'support-audit.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rev(s):
    d=[]
    for _ in range(8):d.append(s%3);s//=3
    return sum(v*3**i for i,v in enumerate(d[::-1]))
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();paths=[Path(__file__),HERE/'ternary-pilot.json',HERE/'float-F.bin.gz',HERE/'sample-words.bin.gz',HERE/'raw-result.json.gz',
        ROOT/'research-goal-20261016/cover-newwindow-gram.json',ROOT/'research-20261016-followup/window_reweight_challenge.json']
    pins={p.relative_to(ROOT).as_posix():digest(p)for p in paths}
    p=json.loads(paths[1].read_bytes());fs=struct.unpack('<29171d',gzip.decompress(paths[2].read_bytes()));words=list(struct.iter_unpack('<HH',gzip.decompress(paths[3].read_bytes())))
    raw=json.loads(gzip.decompress(paths[4].read_bytes()))['result'];gram=json.loads(paths[5].read_bytes())['results'];challenge=json.loads(paths[6].read_bytes())
    assert p['LP_calls']==1 and p['zero_potential_minimum_sample_index']==69 and min(range(len(fs)),key=fs.__getitem__)==69
    g=challenge['best_gaps'];assert len(g)==9;classes=[0 if v<=1.5 else 1 if v<=2.5 else 2 for v in g]
    head=sum(v*3**i for i,v in enumerate(classes[:8]));tail=sum(v*3**i for i,v in enumerate(classes[1:]));assert words[69]==(head,tail)==(271,2277)
    assert head!=tail and len(set(g))>1 and g[:8]!=g[1:]
    sameword=[i for i,w in enumerate(words)if w==(head,tail)and fs[i]<=fs[69]+1e-9];assert sameword==[39,69]
    loops=[i for i,(h,t)in enumerate(words)if h==t];loopmin=min(loops,key=fs.__getitem__)
    assert len(loops)==404 and loopmin==17232 and words[loopmin]==(3280,3280)
    support_weights=[(1,F(2,9)),(2,F(1,9)),(7,F(2,9)),(13,F(2,9)),(15,F(2,9))]
    active=[i for i,v in enumerate(raw['ineqlin']['marginals'])if abs(v)>1e-12];assert active==[i for i,w in support_weights]
    coeff={};actualcoeff={};weight=F(0);avg=F(0);support=[]
    def add_actual(state,amount):
        r=state[::-1]
        if state==r:return
        key=min(state,r);orientation=1 if state<r else -1;actualcoeff[key]=actualcoeff.get(key,F(0))+amount*orientation
    for i,mu in support_weights:
        h,t=words[i];assert abs(raw['ineqlin']['marginals'][i]+float(mu))<1e-15 and abs(raw['ineqlin']['residual'][i])<1e-15
        weight+=mu;avg+=mu*F.from_float(fs[i])
        for s,sgn in [(h,-1),(t,1)]:
            r=rev(s)
            if s!=r:k=min(s,r);coeff[k]=coeff.get(k,F(0))+mu*sgn*(1 if s<r else -1)
        values=[float(F(v))for v in gram[i]['anchor']];exact=tuple(F.from_float(v)for v in values)
        cl=[0 if v<=1.5 else 1 if v<=2.5 else 2 for v in values]
        assert words[i]==(sum(v*3**k for k,v in enumerate(cl[:8])),sum(v*3**k for k,v in enumerate(cl[1:])))
        add_actual(exact[:8],-mu);add_actual(exact[1:],mu)
        support.append({'sample_row':i,'weight':str(mu),'head_word':h,'tail_word':t,'saved_binary_float_F':str(F.from_float(fs[i])),
            'F_hint':fs[i],'integer_gap_pattern':gram[i]['integer_gaps'],'saved_anchor':gram[i]['anchor'],'sample_float_gaps':values})
    coeff={k:v for k,v in coeff.items()if v};actualcoeff={k:v for k,v in actualcoeff.items()if v}
    assert weight==1 and not coeff and actualcoeff
    assert avg==F(15300638307052189,1729382256910270464)and abs(float(avg)-p['sample_floor_hint'])<1e-18
    for path in paths:assert digest(path)==pins[path.relative_to(ROOT).as_posix()]
    out={'scope':__doc__,'passed':True,'source_sha256_start':pins,'source_sha256_end':pins,'all_inputs_unchanged':True,
        'zeroV_minimum_sample_row':69,'source':'research-20261016-followup/window_reweight_challenge.json:best_gaps',
        'zeroV_minimum_sample_float_gaps':g,'zeroV_minimum_sample_exact_binary_float_gaps':[str(F.from_float(v))for v in g],
        'zeroV_minimum_saved_binary_float_F':str(F.from_float(fs[69])),'zeroV_minimum_F_hint':fs[69],
        'zeroV_minimum_gap_classes':classes,'zeroV_head_word':head,'zeroV_tail_word':tail,
        'zeroV_head_equals_tail':False,'zeroV_actual_uniform_gap_period1':False,'same_word_near_minimum_samples':[{'row':i,'F_hint':fs[i]}for i in sameword],
        'selfloop_rows':len(loops),'minimum_selfloop_sample':{'row':loopmin,'head':words[loopmin][0],'tail':words[loopmin][1],'F_hint':fs[loopmin]},
        'nonzero_dual_sample_support':support,'support_weight_sum':'1','weighted_class_potential_coefficients_cancel_exactly':True,
        'finite_binary_float_F_model_upper_bound':str(avg),'finite_model_upper_hint':float(avg),
        'actual_8gap_state_coefficients_do_not_cancel':True,'nonzero_actual_state_coefficients':len(actualcoeff),
        'scope_of_obstruction':'Only the fixed ternary antisymmetric word-potential finite surrogate; no obstruction to arbitrary bounded real8-gap potentials is proved.',
        'actual_scalar_upper_bounds_proven':False,'new_uniform_actual_point_evaluated':False,'kernel_evaluations':0,'LP_calls':0,'new_Lean_invocations':0,
        'global_mean_floor_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'zeroV_head':head,'zeroV_tail':tail,'uniform_period1':False,'support_rows':active,
        'finite_model_upper_hint':float(avg),'actual_state_coefficients_nonzero':len(actualcoeff),'receipt_sha256':digest(OUT)if args.write_receipt else None}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
