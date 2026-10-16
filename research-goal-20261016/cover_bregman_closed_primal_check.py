"""Exact closed-form affine-h Bregman row at the latest saved LP primal.

No LP/optimizer, scalar query, new point, Lean, or cover job. The chosen
h(g) is affine, so the KKT-only lower bound is still quadratic in the old
position moments. Its gradient uncertainty is paid over the entire cell.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import cover_bregman_primal_check as a

HERE=Path(__file__).parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def trans(A):return list(map(list,zip(*A)))

def mm(A,B):return [[a.dot(row,col) for col in zip(*B)] for row in A]

def main():
    started=time.monotonic();pilot=HERE/'cover-bregman-energy-pilot.json';model=HERE/'cover-bregman-primal-check.json'
    oldpath=HERE/'cover-cross-moment-remaining-six.json';watched=[pilot,model,oldpath,Path(__file__),Path(a.__file__)]
    initial={p.name:sha(p) for p in watched};data=json.loads(pilot.read_text());m=json.loads(model.read_text());prior=json.loads(oldpath.read_text())['rows'][0]
    assert data['phase']=='completed_bounded_pilot' and len(data['rounds'])==2
    assert data['path']==m['path']==prior['path'] and data['all_nine_coordinates_strictly_free']
    packet=prior['energy_packets'][0];point=list(map(F,packet['centre']));q=[(F(l)+F(u))/2 for l,u in packet['gradient_interval']]
    err=[(F(u)-F(l))/2 for l,u in packet['gradient_interval']]
    Hm=[[F(v) for v in row] for row in m['Hm']];HL=[[F(v) for v in row] for row in m['HL']]
    columns=[]
    for j in range(9):
        col,pivots=a.solve(HL,[F(int(i==j)) for i in range(9)]);columns.append(col)
    B=trans(columns);assert B==trans(B)
    assert mm(HL,B)==[[F(int(i==j)) for j in range(9)] for i in range(9)]
    BHm=mm(B,Hm);D=[[BHm[i][j]+int(i==j) for j in range(9)] for i in range(9)];z=a.matvec(B,q)
    HmBHm=mm(Hm,BHm);K=[[Hm[i][j]+HmBHm[i][j] for j in range(9)] for i in range(9)];assert K==trans(K)
    linear=[x+y for x,y in zip(q,a.matvec(Hm,z))]
    state=prior['cell'];center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])];radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    delta=[c-p for c,p in zip(center,point)];Ddelta=a.matvec(D,delta)
    absbounds=[abs(v+w)+sum(abs(D[i][j])*radius[j] for j in range(9)) for i,(v,w) in enumerate(zip(Ddelta,z))]
    payment=a.dot(err,absbounds)
    c=F(packet['F_interval'][0])+a.dot(q,z)/2+a.dot(linear,delta)+a.dot(delta,a.matvec(K,delta))/2-payment
    row={};glinear=[x+y for x,y in zip(linear,a.matvec(K,delta))]
    for r,v in enumerate(glinear):
        if v:row[r]=v
    c-=a.dot(glinear,center);pairs=[(r,s) for r in range(9) for s in range(r,9)]
    for index,(r,s) in enumerate(pairs):
        v=K[r][s]*radius[r]*radius[s]/(2 if r==s else 1)
        if v:row[50+index]=v
    primal=list(map(lambda x:F(str(x)),data['rounds'][-1]['raw_primal_with_slack'][:464]))
    value=c+sum(v*primal[i] for i,v in row.items());target=F(11,1250)
    original_value=F(packet['quadratic_constant'])+sum(F(v)*primal[i] for i,v in packet['row'])
    fixed_values=[F(p['quadratic_constant'])+sum(F(v)*primal[i] for i,v in p['row']) for p in data['energy_packets'][1:]]
    # At a rank-one rational test, compare the compact polynomial to the
    # direct closed square formula. This is algebra, no actual kernel call.
    test=[F(i-3,11) for i in range(9)];g=[x+y for x,y in zip(center,[r*t for r,t in zip(radius,test)])]
    d=[x-y for x,y in zip(g,point)];v=[x+y for x,y in zip(q,a.matvec(Hm,d))]
    h=[-x for x in a.matvec(B,v)]
    direct=F(packet['F_interval'][0])+a.dot(q,d)+a.dot(d,a.matvec(Hm,d))/2+a.dot(v,a.matvec(B,v))/2-payment
    factor=[F(0)]*464;factor[:9]=g
    for index,(r,s) in enumerate(pairs):factor[50+index]=test[r]*test[s]
    assert c+sum(v*factor[i] for i,v in row.items())==direct
    assert [d[i]-h[i] for i in range(9)]==[x+y for x,y in zip(a.matvec(D,d),z)]
    result={'scope':__doc__,'path':prior['path'],'input_sha256_start':initial,'all_nine_free_KKT_required':True,
        'HL_inverse':[[str(v) for v in r] for r in B],'closed_quadratic_K':[[str(v) for v in r] for r in K],
        'closed_linear_in_delta':list(map(str,linear)),'delta_minus_h_affine_matrix':[[str(v) for v in r] for r in D],
        'delta_minus_h_affine_constant':list(map(str,z)),'uniform_abs_delta_minus_h_coordinate_bounds':list(map(str,absbounds)),
        'new_gradient_error_payment':str(payment),'original_energy_at_latest_primal':str(original_value),
        'two_fixed_h_energy_at_latest_primal':list(map(str,fixed_values)),
        'closed_energy_at_latest_primal':str(value),'closed_energy_at_latest_primal_display':float(value),
        'closed_row_violation_exact':str(value-target),'closed_row_strictly_cuts_latest_primal':value>target,
        'factorized_polynomial_identity_checked':True,
        'proposed_KKT_energy_packet':{'kind':'Bregman_closed_affine_h_all_free_KKT','centre':packet['centre'],
            'row':[[i,str(v)] for i,v in sorted(row.items())],'quadratic_constant':str(c),'bound':str(target-c),
            'uniform_gradient_error_payment':str(payment),'new_scalar_points':0,
            'formula':'F>=F0+q.d+0.5*d.Hm.d+0.5*(q+Hm.d).HLinv.(q+Hm.d)-uniform_error'},
        'actual_closed_Bregman_bridge_formalized':False,'cell_exclusion_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    result['input_sha256_end']={p.name:sha(p) for p in watched};assert result['input_sha256_end']==initial;result['all_inputs_unchanged']=True
    result['seconds']=time.monotonic()-started;out=HERE/'cover-bregman-closed-primal-check.json';assert not out.exists()
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['path','closed_energy_at_latest_primal_display','closed_row_strictly_cuts_latest_primal','closed_row_violation_exact','seconds']}),flush=True)

if __name__=='__main__':main()
