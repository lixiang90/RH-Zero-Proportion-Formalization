"""Independent stdlib replay of fixed swap67 quadratic coarsening.

Reconstruct the common nine-variable arguments, all sixteen signed scalar
quartics and quadratic upper bounds, the original450-term difference,
and all55 independent localizer entries. No producer imports, eigensolve,
optimizer or Lean. Default read-only; --write-receipt writes an absent file.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
import argparse, gzip, hashlib, json, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;SC=32768
PACKET=ROOT/'research-goal-20261017-swap67-quadratic-localizer/swap67-q2-localizer.json'
SHA='ecbcdb6af8d2e902c7ee9e0b6f005f08c3fda7bc9c35fac0535113ba57f9067c'
OUT=HERE/'independent-replay.json'
PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(9)for j in range(i+2,10)]
SLOT={e:k for k,e in enumerate(PAIRS)}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,q,s=F(1)):
    r=p.copy()
    for m,v in q.items():
        r[m]=r.get(m,F(0))+s*v
        if not r[m]:del r[m]
    return r
def mul(p,q):
    r={}
    for m,v in p.items():
        for n,w in q.items():
            k=tuple(sorted(m+n));assert len(k)<=4;r[k]=r.get(k,F(0))+v*w
    return {m:v for m,v in r.items()if v}
def scale(p,s):return {m:v*s for m,v in p.items()if v*s}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert digest(PACKET)==SHA;p=json.loads(PACKET.read_bytes())
    paths={**p['source_sha256_start'],PACKET.relative_to(ROOT).as_posix():SHA,
        Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['source_sha256_start']==p['source_sha256_end'] and p['all_sources_unchanged']
    extra=['research-goal-20261017-quartic/quartic-model.json.gz',
        'research-20261016-followup/window_reweight_rational.json',
        'research-goal-20261017-swap-family-audit/independent-replay.json']
    for name in extra:paths[name]=digest(ROOT/name)
    for name,h in paths.items():assert digest(ROOT/name)==h,('changed input',name)
    family=json.loads(gzip.decompress((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz').read_bytes()))
    model=json.loads(gzip.decompress((ROOT/extra[0]).read_bytes()));pars=json.loads((ROOT/extra[1]).read_bytes())
    gate=json.loads((ROOT/extra[2]).read_bytes());assert gate['passed'] and gate['packet_sha256']==paths['research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz']
    proof=json.loads((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-exact-primal.json').read_bytes())
    single=json.loads((ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json').read_bytes())
    assert proof['exact_eight_swap_quartic_outer_relaxation_feasible']
    mon=[m for d in range(5)for m in combinations_with_replacement(range(9),d)];idx={m:k for k,m in enumerate(mon)}
    assert list(map(list,mon))==family['monomials']==model['monomials'] and len(mon)==715
    basis=[()]+[(i,)for i in range(9)];assert p['basis']==list(map(list,basis))
    moments=[F(1)]+list(map(F,proof['rational_714_moments']));assert len(moments)==715
    def unpack(raw):
        assert len({k for k,_ in raw})==len(raw)
        out={mon[k]:F(v)for k,v in raw};assert all(out.values());return out
    def pack(poly):return [[idx[m],str(v)]for m,v in sorted(poly.items(),key=lambda z:idx[z[0]])]
    def expect(poly):return sum((v*moments[idx[m]]for m,v in poly.items()),F(0))
    state=model['cell'];c=list(map(F,model['normalized_gap_center']));r=list(map(F,model['normalized_gap_radius']))
    assert c==list(map(F,family['normalized_gap_center'])) and r==list(map(F,family['normalized_gap_radius']))
    assert all(c[i]==F(state[0][i]+state[1][i],2*SC) and r[i]==F(state[1][i]-state[0][i],2*SC)>0 for i in range(9))
    gaps=[{():c[i],(i,):r[i]}for i in range(9)]
    def span(ids):
        v={}
        for i in ids:v=add(v,gaps[i])
        return v
    def bound(i,j):return (0,0)if i==j else(state[0][SLOT[i,j]],state[1][SLOT[i,j]])
    perm=list(range(9));perm[6],perm[7]=7,6;item=family['maps'][6]
    assert p['path']==family['path']==model['path']==proof['path'] and item['swap_zero_based']==p['swap_zero_based']==[6,7]
    pressure=scale(add(gaps[7],gaps[6],F(-1)),F(pars['b_numerators'][6]-pars['b_numerators'][7],pars['denominator']))
    assert pack(pressure)==item['pressure_difference_polynomial']==p['pressure_difference_polynomial']
    q4=pressure;q2=pressure;count=0
    assert len(item['changed_edge_packets'])==8 and len(p['signed_scalar_reductions'])==16
    for e in item['changed_edge_packets']:
        i,j=e['edge'];w=F(e['weight']);assert w>0
        assert w==F(next(a for ii,jj,a in pars['a_upper']if(ii,jj)==(i,j)),pars['denominator'])
        for side,sign in [('new',1),('old',-1)]:
            s=family['scalar_packets'][e[side+'_scalar_packet']];a=p['signed_scalar_reductions'][count];count+=1
            image=span(perm[i:j])if side=='new'else span(range(i,j));assert pack(image)==s['span_polynomial']
            if side=='old':lo,hi=bound(i,j)
            else:
                candidates=[(sum(state[0][k]for k in perm[i:j]),sum(state[1][k]for k in perm[i:j]))]
                if j==7:
                    l,u=bound(i,6);candidates.append((l+state[0][7],u+state[1][7]));l,u=bound(i,8);candidates.append((l-state[1][6],u-state[0][6]))
                else:
                    assert i==7;l,u=bound(8,j);candidates.append((state[0][6]+l,state[1][6]+u));l,u=bound(6,j);candidates.append((l-state[1][7],u-state[0][7]))
                lo=max(l for l,u in candidates);hi=min(u for l,u in candidates)
            assert s['whole_span_integer_bounds']==[lo,hi]
            anchor=F(lo+hi,2*SC);R=F(hi-lo,2*SC);assert R>0 and F(s['anchor'])==anchor and F(s['radius_about_anchor'])==R
            d=add(image,{():anchor},F(-1));assert pack(d)==s['d_polynomial']==a['d_polynomial']
            mu=list(map(F,s['anchor_derivative_midpoints']));eps=list(map(F,s['anchor_derivative_errors']));M5=F(s['whole_span_absolute_w5_bound'])
            assert len(mu)==len(eps)==5 and min(eps)>=0 and M5>=0
            coeff=[sign*mu[0]+eps[0]+eps[1]*R,sign*mu[1],sign*mu[2]/2+eps[2]/2+eps[3]*R/6,
                sign*mu[3]/6,sign*mu[4]/24+eps[4]/24+M5*R/120]
            powers=[{():F(1)}]
            for k in range(4):powers.append(mul(powers[-1],d))
            local4={}
            for k in range(5):local4=add(local4,powers[k],coeff[k])
            target=unpack(s['scalar_upper_quartic'])if sign==1 else scale(unpack(s['scalar_lower_quartic']),F(-1))
            assert local4==target
            payment=abs(coeff[3])*R+max(coeff[4],F(0))*R*R
            local2=add(add({():coeff[0]},d,coeff[1]),powers[2],coeff[2]+payment)
            # c3*d3 <= |c3|*R*d2 and c4*d4 <= max(c4,0)*R2*d2 for |d|<=R.
            diff=add(add(scale(powers[2],payment),powers[3],-coeff[3]),powers[4],-coeff[4])
            assert add(local2,local4,F(-1))==diff
            assert a=={'edge':[i,j],'side':side,'sign':sign,'scalar_packet_id':s['id'],'weight':str(w),'radius':str(R),
                'd_polynomial':pack(d),'signed_quartic_coefficients_in_d':list(map(str,coeff)),
                'upper_quadratic_coefficients_in_d':[str(coeff[0]),str(coeff[1]),str(coeff[2]+payment)],
                'upper_quadratic_polynomial':pack(local2),'quadratic_minus_signed_quartic':pack(diff)}
            q4=add(q4,local4,w);q2=add(q2,local2,w)
    assert pack(q4)==item['difference_upper_quartic']==single['difference_upper_quartic']==p['quartic_upper_difference'] and len(q4)==450
    assert pack(q2)==p['quadratic_upper_difference'] and all(len(m)<=2 for m in q2)and len(q2)==44
    assert pack(add(q2,q4,F(-1)))==p['Q2_minus_D4']
    matrix=[[F(0)for _ in basis]for _ in basis];entries=0
    for i,bi in enumerate(basis):
        for j in range(i,10):
            # Independently multiply Q2 by the two basis monomials before applying the functional.
            value=expect(mul(q2,{tuple(sorted(bi+basis[j])):F(1)}));matrix[i][j]=matrix[j][i]=value;entries+=1
    text=[[str(v)for v in row]for row in matrix]
    matrixsha=hashlib.sha256(json.dumps(text,separators=(',',':')).encode()).hexdigest()
    assert entries==55 and text==p['localizer_matrix'] and matrixsha==p['localizer_matrix_sha256']=='5e0d15bd91b6940e00a35977b8007f03e1194d29c62862ecd546f59856901934'
    e4=expect(q4);e2=expect(q2);assert e4==F(p['new_point_expected_D4'])and e2==F(p['new_point_expected_Q2'])and e4>0 and e2>0
    assert p['integer_vector_attempts']==0 and p['exact_negative_vector']is None and not p['new_exact714_separated']
    for name,h in paths.items():assert digest(ROOT/name)==h
    result={'scope':__doc__,'passed':True,'source_sha256':digest(Path(__file__)),'packet_sha256':SHA,
        'source_sha256_start':paths,'source_sha256_end':paths,'all_sources_unchanged':True,
        'signed_scalar_reductions_checked':16,'shared_normalized_gap_variables':9,'whole_image_bounds_checked':True,
        'quartic_terms':len(q4),'original450_term_row_matches':True,'quadratic_terms':len(q2),
        'matrix_size':10,'independent_matrix_entries_rebuilt':55,'full_symmetric_entries_checked':100,'matrix_sha256':matrixsha,
        'expected_D4':str(e4),'expected_Q2':str(e2),'expected_Q2_positive':True,
        'producer_imports':0,'eigh_calls':0,'solver_calls':0,'Lean_invocations':0,
        'positive_definiteness_independently_proven':False,'point_separation_proven':False,
        'new_actual_scalar_enclosures_Lean_proved':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'signed_scalars':16,'independent_entries':55,'matrix_sha256':matrixsha,'expected_Q2':float(e2),
        'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':result['seconds']}),flush=True)

if __name__=='__main__':
    assert __debug__
    main()
