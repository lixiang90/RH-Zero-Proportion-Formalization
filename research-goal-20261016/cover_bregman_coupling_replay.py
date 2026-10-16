"""Independent stdlib edgewise expansion of four new energy/KKT packets.

No producer, matrix solver, optimizer, jet, or Lean module is imported.
Actual scalar enclosures and curvature tuples remain analytic inputs.
Checks reverse, two fixed-h, and closed affine-h coefficient identities.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def dot(x,y):return sum(a*b for a,b in zip(x,y))

def matvec(A,x):return [dot(r,x) for r in A]

def add(poly,key,value):
    value=poly.get(key,F(0))+value
    if value:poly[key]=value
    else:poly.pop(key,None)

def affine_add(poly,a,scale=F(1)):
    add(poly,(),scale*a[0])
    for i,c in enumerate(a[1:]):add(poly,(i,),scale*c)

def square_add(poly,a,scale):
    for i,v in enumerate(a):
        for j,w in enumerate(a):
            mon=tuple(sorted(k-1 for k in [i,j] if k));add(poly,mon,scale*v*w)

def moment(poly,center,radius):
    row={};c=poly.get((),F(0));pairs=[(i,j) for i in range(9) for j in range(i,9)];h={p:50+k for k,p in enumerate(pairs)}
    for mon,value in poly.items():
        if len(mon)==1:
            i=mon[0];add(row,i,value/radius[i]);c-=value*center[i]/radius[i]
        elif len(mon)==2:add(row,h[mon],value)
    return row,c

def check_packet(row,c,packet):
    assert row=={i:F(v) for i,v in packet['row']};assert c==F(packet['quadratic_constant'])
    assert F(packet['bound'])==F(11,1250)-c

def main():
    began=time.monotonic();names=['cover-cross-moment-remaining-six.json','cover-reverse-taylor-pilot.json',
        'cover-bregman-primal-check.json','cover-bregman-energy-pilot.json','cover-bregman-closed-primal-check.json',
        'cover-bregman-closed-energy-pilot.json']
    paths=[HERE/n for n in names]+[ROOT/'research-20261016-followup/window_reweight_rational.json',Path(__file__)]
    initial={p.name:sha(p) for p in paths};docs={n:json.loads((HERE/n).read_text()) for n in names}
    prior=docs[names[0]]['rows'][0];rev=docs[names[1]];fixed=docs[names[3]];closed=docs[names[4]];cpilot=docs[names[5]]
    assert all(d['path']==prior['path'] for d in [rev,fixed,closed,cpilot]);state=prior['cell'];assert all(x>123*SC//128 for x in state[0][:9])
    old=prior['energy_packets'][0];point=list(map(F,old['centre']));center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])];radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    q=[(F(l)+F(u))/2 for l,u in old['gradient_interval']];error=[(F(u)-F(l))/2 for l,u in old['gradient_interval']]
    lower=[F(v,SC) for v in state[0][:9]];upper=[F(v,SC) for v in state[1][:9]]
    param=json.loads(paths[-2].read_text());den=param['denominator'];terms=[(i,j,F(v,den)) for i,j,v in param['a_upper'] if v]
    intervals=[tuple(map(F,p)) for p in rev['energy_packets'][1]['whole_span_second_bounds']]
    assert len(intervals)==len(terms)==41 and all(m<=M for m,M in intervals)
    d=[[center[i]-point[i]]+[radius[i] if i==j else F(0) for j in range(9)] for i in range(9)]
    # Reverse row, expanded per edge rather than through a matrix Hessian.
    poly={():F(old['F_interval'][0])};pressure=[F(b,den) for b in param['b_numerators']]
    for i in range(9):affine_add(poly,d[i],pressure[i])
    reverse_u={}
    for e,((i,j,a),(m,M)) in enumerate(zip(terms,intervals)):
        ds=[sum(d[r][k] for r in range(i,j)) for k in range(10)];square_add(poly,ds,-a*M/2)
        add(reverse_u,9+e,a*ds[0])
        for r in range(9):add(reverse_u,95+41*r+e,a*ds[r+1])
    row,c=moment(poly,center,radius)
    for i,v in reverse_u.items():add(row,i,v)
    check_packet(row,c,rev['energy_packets'][1]);checks=[{'kind':'reverse','exact_edgewise_expansion':True}]
    # Fixed h rows: no producer's Hm/HL matrices are needed for expansion.
    for packet in fixed['energy_packets'][1:]:
        h=list(map(F,packet['fixed_h']));dh=[[a[0]-h[i]]+a[1:] for i,a in enumerate(d)]
        payment=sum(e*max(abs(l-p-v),abs(u-p-v)) for e,l,u,p,v in zip(error,lower,upper,point,h))
        assert payment==F(packet['uniform_gradient_error_payment'])
        poly={():F(old['F_interval'][0])-payment}
        for i in range(9):affine_add(poly,dh[i],q[i])
        for (i,j,a),(m,M) in zip(terms,intervals):
            edge=[sum(dh[r][k] for r in range(i,j)) for k in range(10)];square_add(poly,edge,a*m/2)
            add(poly,(),-a*M*sum(h[i:j])**2/2)
        row,c=moment(poly,center,radius);check_packet(row,c,packet);checks.append({'kind':'fixed_h','exact_edgewise_expansion':True})
    # Closed affine h(g): independently expand the original edgewise (15),
    # rather than using the producer's compact K and linear coefficients.
    B=[[F(v) for v in rr] for rr in closed['HL_inverse']];Hm=[[F(0) for j in range(9)] for i in range(9)];HL=[[F(0) for j in range(9)] for i in range(9)]
    for (i,j,a),(m,M) in zip(terms,intervals):
        for r in range(i,j):
            for s in range(i,j):Hm[r][s]+=a*m;HL[r][s]+=a*(M-m)
    assert all(dot(HL[i],[B[k][j] for k in range(9)])==int(i==j) for i in range(9) for j in range(9))
    # Each h_i is represented as an affine function of y.
    affgrad=[[q[i]+sum(Hm[i][j]*d[j][0] for j in range(9))]+[sum(Hm[i][j]*d[j][k] for j in range(9)) for k in range(1,10)] for i in range(9)]
    h=[[-sum(B[i][j]*affgrad[j][k] for j in range(9)) for k in range(10)] for i in range(9)]
    dh=[[d[i][k]-h[i][k] for k in range(10)] for i in range(9)]
    payment=sum(error[i]*(abs(dh[i][0])+sum(map(abs,dh[i][1:]))) for i in range(9));assert payment==F(closed['new_gradient_error_payment'])
    assert [str(abs(v[0])+sum(map(abs,v[1:]))) for v in dh]==closed['uniform_abs_delta_minus_h_coordinate_bounds']
    poly={():F(old['F_interval'][0])-payment}
    for i in range(9):affine_add(poly,dh[i],q[i])
    for (i,j,a),(m,M) in zip(terms,intervals):
        dd=[sum(dh[r][k] for r in range(i,j)) for k in range(10)];hh=[sum(h[r][k] for r in range(i,j)) for k in range(10)]
        square_add(poly,dd,a*m/2);square_add(poly,hh,-a*M/2)
    row,c=moment(poly,center,radius);check_packet(row,c,closed['proposed_KKT_energy_packet'])
    assert cpilot['energy_packets'][1]==closed['proposed_KKT_energy_packet'];checks.append({'kind':'closed_affine_h','exact_edgewise_expansion':True})
    latest=[F(str(v)) for v in fixed['rounds'][-1]['raw_primal_with_slack'][:464]];value=c+sum(v*latest[i] for i,v in row.items())
    assert value==F(closed['closed_energy_at_latest_primal']) and value-F(11,1250)==F(closed['closed_row_violation_exact'])>0
    final={p.name:sha(p) for p in paths};assert final==initial
    result={'scope':__doc__,'input_sha256_start':initial,'input_sha256_end':final,'all_inputs_unchanged':True,'passed':True,
        'rows_checked':len(checks),'checks':checks,'all_nine_free_KKT_hypotheses_checked_from_cell':True,
        'closed_inverse_identity_checked':True,'closed_gradient_error_box_payment_checked':True,
        'actual_scalar_interval_semantics_independently_verified':False,'cell_exclusion_proven':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    path=HERE/'cover-bregman-coupling-replay.json';assert not path.exists();path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k not in ['input_sha256_start','input_sha256_end']}),flush=True)

if __name__=='__main__':main()
