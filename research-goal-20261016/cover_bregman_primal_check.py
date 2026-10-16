"""Closed-form rational Bregman cut selected from one frozen LP primal.

No LP, optimizer, scalar sample, jet query, or Lean run. Reuse the original
first-remaining midpoint packet and the already derived upper-curvature
packet. A positive violation only cuts this saved moment vector; it is not
a proof that the stronger relaxation is infeasible or the cell excluded.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def matvec(A,x):return [dot(row,x) for row in A]

def solve(A,b):
    rows=[row.copy()+[v] for row,v in zip(A,b)];pivots=[]
    for k in range(9):
        pivot=rows[k][k];assert pivot>0,('HL not strictly positive on this elimination',k,pivot);pivots.append(pivot)
        rows[k]=[v/pivot for v in rows[k]]
        for i in range(k+1,9):
            v=rows[i][k];rows[i]=[x-v*y for x,y in zip(rows[i],rows[k])]
    x=[F(0)]*9
    for i in range(8,-1,-1):x[i]=rows[i][-1]-sum(rows[i][j]*x[j] for j in range(i+1,9))
    assert matvec(A,x)==b
    return x,pivots

def main():
    began=time.monotonic();old_path=HERE/'cover-cross-moment-remaining-six.json';reverse_path=HERE/'cover-reverse-taylor-pilot.json'
    param_path=ROOT/'research-20261016-followup/window_reweight_rational.json';paths=[old_path,reverse_path,param_path,Path(__file__)]
    initial={p.name:sha(p) for p in paths};old=json.loads(old_path.read_text())['rows'][0];reverse=json.loads(reverse_path.read_text())
    assert reverse['path']==old['path'] and reverse['phase']=='completed_bounded_pilot' and reverse['LP']['energy_slack_hint']==0
    assert old['base_result']['strict_free_coordinates']==list(range(9))
    packet=old['energy_packets'][0];upper=reverse['energy_packets'][1];assert upper['centre']==packet['centre']
    point=list(map(F,packet['centre']));state=old['cell'];lower=[F(v,SC) for v in state[0][:9]];high=[F(v,SC) for v in state[1][:9]]
    gradient=[(F(l)+F(u))/2 for l,u in packet['gradient_interval']];error=[(F(u)-F(l))/2 for l,u in packet['gradient_interval']]
    params=json.loads(param_path.read_text());D=params['denominator'];terms=[(i,j,F(a,D)) for i,j,a in params['a_upper'] if a]
    assert len(terms)==41 and len(upper['whole_span_second_bounds'])==41
    Hm=[[F(0) for _ in range(9)] for _ in range(9)];HL=[[F(0) for _ in range(9)] for _ in range(9)]
    for (i,j,a),(mm,MM) in zip(terms,upper['whole_span_second_bounds']):
        m,M=F(mm),F(MM);assert m<=M
        for r in range(i,j):
            for s in range(i,j):Hm[r][s]+=a*m;HL[r][s]+=a*(M-m)
    primal=list(map(lambda v:F(str(v)),old['dual_hint']['raw_primal_with_energy_slack'][:464]))
    delta=[x-y for x,y in zip(primal[:9],point)];v=[a+b for a,b in zip(gradient,matvec(Hm,delta))]
    inverse,pivots=solve(HL,v);hstar=[-x for x in inverse];q=2**20;h=[F(round(x*q),q) for x in hstar]
    payment0=sum(e*max(abs(l-p),abs(u-p)) for e,l,u,p in zip(error,lower,high,point))
    paymenth=sum(e*max(abs(l-p-z),abs(u-p-z)) for e,l,u,p,z in zip(error,lower,high,point,h))
    assert payment0==F(packet['uniform_gradient_error_payment'])
    ideal_gain=dot(v,inverse)/2;rounded_gain=-dot(v,h)-dot(h,matvec(HL,h))/2
    oldrow={i:F(c) for i,c in packet['row']};newrow=oldrow.copy();mh=matvec(Hm,h)
    for r in range(9):
        value=newrow.get(r,F(0))-mh[r]
        if value:newrow[r]=value
        else:newrow.pop(r,None)
    oldC=F(packet['quadratic_constant']);newC=oldC-dot(gradient,h)+dot(mh,point)-dot(h,matvec(HL,h))/2-(paymenth-payment0)
    old_value=oldC+sum(c*primal[i] for i,c in oldrow.items());new_value=newC+sum(c*primal[i] for i,c in newrow.items())
    assert new_value-old_value==rounded_gain-(paymenth-payment0)
    output={'scope':__doc__,'path':old['path'],'input_sha256_start':initial,'all_nine_coordinates_strictly_free':True,
        'selected_primal':'original immutable remaining-six first case, exact decimal interpretation',
        'Hm':[[str(v) for v in row] for row in Hm],'HL':[[str(v) for v in row] for row in HL],
        'HL_positive_elimination_pivots':list(map(str,pivots)),'anchor_gradient_midpoints':list(map(str,gradient)),
        'saved_primal_mean_delta':list(map(str,delta)),'closed_form_h_star':list(map(str,hstar)),
        'fixed_rational_h':list(map(str,h)),'h_denominator':q,'ideal_quadratic_gain_exact':str(ideal_gain),
        'rounded_h_gain_exact':str(rounded_gain),'old_gradient_error_payment':str(payment0),
        'recomputed_shifted_gradient_error_payment':str(paymenth),'new_gradient_payment_difference':str(paymenth-payment0),
        'old_energy_lower_polynomial_at_saved_primal':str(old_value),'new_energy_lower_polynomial_at_saved_primal':str(new_value),
        'old_energy_lower_display':float(old_value),'new_energy_lower_display':float(new_value),
        'target':'11/1250','new_row_violation_exact':str(new_value-F(11,1250)),
        'new_row_strictly_cuts_saved_decimal_primal':new_value>F(11,1250),
        'proposed_KKT_energy_packet':{'kind':'Bregman_fixed_shared_h_free_KKT','centre':packet['centre'],
            'row':[[i,str(v)] for i,v in sorted(newrow.items())],'quadratic_constant':str(newC),
            'bound':str(F(11,1250)-newC),'fixed_h':list(map(str,h)),
            'uniform_gradient_error_payment':str(paymenth),
            'formula':'F>=F0+grad0.(g-g0-h)+0.5*sum a*m*span(g-g0-h)^2-0.5*sum a*M*span(h)^2 at all-free KKT'},
        'actual_Bregman_bridge_formalized':False,'cell_exclusion_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    output['input_sha256_end']={p.name:sha(p) for p in paths};assert output['input_sha256_end']==initial;output['all_inputs_unchanged']=True
    output['seconds']=time.monotonic()-began;path=HERE/'cover-bregman-primal-check.json';assert not path.exists()
    path.write_text(json.dumps(output,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:output[k] for k in ['path','old_energy_lower_display','new_energy_lower_display','new_row_strictly_cuts_saved_decimal_primal','new_row_violation_exact','seconds']}),flush=True)

if __name__=='__main__':main()
