"""Independent stdlib replay of the fixed Bernstein/retained-ray payment K.

No producer imports or alternative bound. This consumes the independently
audited epsilon packet and retained Gram data; no solver/oracle/Lean.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,sys,time
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;BASE=ROOT/'research-goal-20261017-edge6-bernstein-transfer'
OUT=HERE/'independent-replay.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    b=p.read_bytes();return json.loads(gzip.decompress(b)if p.suffix=='.gz'else b)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();path=BASE/'budget.json';assert sha(path)=='c85dbb9f4be621d28bbe1c835e2b3bec005378dbd24a2fbb6785f0be0b700fd3'
    budget=read(path);pins={**budget['source_sha256_start'],path.relative_to(ROOT).as_posix():sha(path),Path(__file__).relative_to(ROOT).as_posix():sha(Path(__file__))}
    assert budget['source_sha256_start']==budget['source_sha256_end']and budget['all_inputs_unchanged']
    for n,h in pins.items():assert sha(ROOT/n)==h
    for name,h in [('research-goal-20261017-edge6-transfer-audit/independent-replay.json','773aad785b583ab8965313b7153d744f6a571e7831c39d66aaf59120adcbdfea'),('research-goal-20261017-fixed-gram-tail-audit/independent-replay.json','c32b9b741f3bdbc0eabaec9bbfcd7a5d1d8e73fc508b0134d27f33be03e61f9c')]:
        assert sha(ROOT/name)==h;rr=read(ROOT/name);assert rr['passed'];pins[name]=h
    packet=read(BASE/'packet.json.gz');ray=read(ROOT/'research-goal-20261017-fixed-gram-tail/retained-ray.json.gz')
    cert=read(ROOT/'research-goal-20261017-fixed-gram-tail/retained-enclosure-certificate.json')
    old=read(ROOT/'research-goal-20261017-quartic/quartic-model.json.gz');model=read(ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz')
    full=read(ROOT/'research-goal-20261017-actual-sextic-exact-ray/quantized-ray.json.gz')
    eps=list(map(lambda r:F(r['epsilon']),packet['coordinates']));e0=F(packet['q0']['epsilon']);assert len(eps)==9 and min(eps+[e0])>=0
    weights=ray['scalar_weight_numerators'];D=10**12;assert weights==full['scalar_weight_numerators']and ray['scalar_weight_denominator']==D
    assert len(weights)==14564 and all(type(x)is int and x>=0 for x in weights)and [i for i,x in enumerate(weights)if not x]==[5793,5794]
    scalar=[];ks=F(0)
    for rid,row in enumerate(old['linear_rows']):
        if row['meta'][0]!='free_KKT_with_dynamic_error':continue
        _,r,t,s=row['meta'];scale=F(row['scale']);assert scale>0 and 0<=r<9 and 0<=t<10 and s in[-1,1]
        payment=F(weights[rid],D)*eps[r]/scale;ks+=payment
        scalar.append({'scalar_row':rid,'coordinate':r,'test':t,'sign':s,'lambda_numerator':weights[rid],'row_scale':str(scale),'epsilon':str(eps[r]),'payment':str(payment)})
    assert len(scalar)==180 and scalar==budget['scalar_KKT_payments']
    gr=[];kg=F(0);k0=F(0)
    for bid,(block,factor)in enumerate(zip(model['blocks'],ray['PSD_factors'])):
        q=model['multipliers'][block['multiplier_id']];kind=q['meta'][0]
        if bid!=1 and kind!='free_gradient_E_plus_sign_P':continue
        assert factor['block_id']==bid and factor['multiplier_id']==block['multiplier_id']
        n=block['size'];rank=factor['column_count'];ints=factor['factor_numerators_by_row'];assert factor['factor_denominator']==D and len(ints)==n and all(len(v)==rank for v in ints)
        retained=factor['retained_original_column_ids'];assert retained==sorted(set(retained))and len(retained)==rank
        assert ints==[[row[k]for k in retained]for row in full['PSD_factors'][bid]['factor_numerators_by_row']]
        div=max([F(1)]+[abs(F(v))for mid,v in q['terms']]);assert div==F(factor['positive_rational_block_divisor'])>0
        normsum=sum(sum(abs(ints[i][j]*ints[k][j])for i in range(n)for k in range(n))for j in range(rank))
        assert normsum==sum(sum(abs(row[j])for row in ints)**2 for j in range(rank))
        B=F(normsum,D*D)/div
        if bid==1:assert q['meta']==['old_PSD_upgrade',1];r=None;epsilon=e0;k0+=epsilon*B
        else:_,r,s=q['meta'];assert 0<=r<9 and s in[-1,1];epsilon=eps[r];kg+=epsilon*B
        gr.append({'block_id':bid,'basis_size':n,'retained_columns':rank,'coordinate':r,'integer_column_l1_squared_sum':normsum,'factor_denominator':D,'positive_block_divisor':str(div),'SOS_upper_B':str(B),'epsilon':str(epsilon),'payment':str(epsilon*B)})
    assert len(gr)==19 and len([v for v in gr if v['coordinate']is not None])==18 and gr==budget['Gram_payments']
    margin=F(-cert['constant_upper_numerator'],cert['fixed_interval_denominator']);assert margin==F(cert['strict_margin'])==F(budget['retained_exact_margin'])and margin>0
    K=ks+kg+k0;assert str(ks)==budget['scalar180_total']and str(kg)==budget['Gram18_KKT_total']and str(k0)==budget['Gram_q0_total']and str(K)==budget['K_total']and str(margin-K)==budget['margin_minus_K']
    assert K>59>1>margin and not budget['strict_budget_passed']and budget['fixed_mathematical_candidates']==1 and budget['K_arithmetic_evaluations_including_failed_serialization']==2
    assert budget['initial_attempt_failed_after_total_K_at_str_serialization']and not budget['new_frontier_closure_claimed']
    for n,h in pins.items():assert sha(ROOT/n)==h
    out={'scope':__doc__,'passed':True,'arithmetic_replay_passed':True,'transfer_budget_gate_passed':False,'source_sha256_start':pins,'source_sha256_end':pins,'all_inputs_unchanged':True,
        'scalar_costs_checked':180,'gradient_Gram_costs_checked':18,'q0_Gram_costs_checked':1,'all_19_column_product_l1_squared_bounds_checked':True,'all_scales_and_divisors_checked':True,'epsilon_1_over_c_paid_once':True,
        'K_fraction_sha256':hashlib.sha256(str(K).encode()).hexdigest(),'K_denominator_bits':K.denominator.bit_length(),'K_hint':float(K),'scalar_hint':float(ks),'gradient_Gram_hint':float(kg),'q0_hint':float(k0),'retained_margin':str(margin),'exact_comparison':'K>59>1>margin',
        'producer_arithmetic_executions_including_serialization_failure':2,'producer_mathematical_candidates':1,'same_bound_same_inputs_unchanged':True,'old_analytic_premises_not_removed':True,'alternative_bound_tested':False,
        'failure_scope':'This fixed degree6 Bernstein whole-span/column-l1 retained-ray payment is insufficient; no impossibility of transfer or the actual claim is inferred.',
        'fixed_cell_already_closed_in_historical_baseline':True,'new_frontier_closure_claimed':False,'producer_imports':0,'solver_calls':0,'eigh_calls':0,'new_points':0,'Lean_invocations':0,'global_cover_completed':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'K_hint':float(K),'scalar_hint':float(ks),'gradient_Gram_hint':float(kg),'q0_hint':float(k0),'transfer_budget_gate_passed':False,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
