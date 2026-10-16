"""Independent integer/rational replay of the selected actual curvature feed.

No discovery jet evaluator, producer oracle, NumPy, SciPy, or optimizer is
imported. Horner corner witnesses and all final three flow signs are checked.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import gzip,hashlib,json,re,time
HERE=Path(__file__).parent;ROOT=HERE.parent
Q=10**30;DS=10**15;SC=32768;M=F(44,7)**24
sha=lambda b:hashlib.sha256(b).hexdigest()
ceil=lambda v:-((-v.numerator)//v.denominator)
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
INDEX={p:k for k,p in enumerate(PAIRS)}

def selected(W,n,q,a,b,mask):
    assert 1<=n<=32 and -(F(1,2))<=a-n<=b-n<=F(1,2)
    low=(a-n)*Q;high=(b-n)*Q;X=(low.numerator//low.denominator,ceil(high));d=23-q
    assert 0<=mask<16**d
    coeff=[tuple(v*(factorial(j+q)//factorial(j)) for v in W[n][j+q]) for j in range(d+1)];value=coeff[d]
    for j in range(d-1,-1,-1):
        products=[value[0]*X[0],value[0]*X[1],value[1]*X[0],value[1]*X[1]];word=(mask//16**j)%16;lo=word%4;hi=word//4
        assert all(products[lo]<=v<=products[hi] for v in products)
        value=(coeff[j][0]+products[lo]//Q,coeff[j][1]-((-products[hi])//Q))
    return value

def main():
    start=time.monotonic();path=HERE/'cover-curvature-actual-feed.json'
    raw=path.read_bytes() if path.exists() else gzip.decompress((HERE/'cover-curvature-actual-feed.json.gz').read_bytes());doc=json.loads(raw)
    for name,digest in doc['sources'].items():assert sha((ROOT/name).read_bytes())==digest,name
    normalized=json.loads((HERE/'window_normalized_interval.json').read_bytes());W={}
    for n,rows in normalized['integer_w_Taylor_coefficients'].items():
        row=[(F(l)*Q,F(u)*Q) for l,u in rows];assert all(x.denominator==1 for pair in row for x in pair);W[int(n)]=[(int(l),int(u)) for l,u in row]
    lean=(ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean').read_text(encoding='utf8')
    literal=[(int(l),int(l)+int(w)) for l,w in re.findall(r'iw \((-?\d+)\) \((\d+)\)',lean)]
    assert literal==[pair for n in range(1,33) for pair in W[n]]
    grids={};checks=0
    for row in doc['grid_rows']:
        k=row['cell'];n=row['center'];assert n==(k+32)//64 and k not in grids;grids[k]=row
        for q in [2,4]:
            if 'q'+str(q) not in row:continue
            item=row['q'+str(q)];assert item['degree']==23-q
            poly=selected(W,n,q,F(k,64),F(k+1,64),item['mask']);assert list(map(str,poly))==item['poly']
            R=M*F(1,2)**(24-q)/factorial(24-q);lo=F(poly[0],Q)-R;hi=F(poly[1],Q)+R
            if q==2:
                assert F(item['old_lower'],DS)<=lo<=hi<=F(item['old_upper'],DS)
                assert item['actual_lower']==(lo*DS).__floor__() and item['actual_upper']==ceil(hi*DS)
            else:
                assert max(abs(lo),abs(hi))<=F(item['old_abs_bound'],DS)
                assert item['actual_abs_bound']==ceil(max(abs(lo),abs(hi))*DS)
            checks+=1
    points={}
    for row in doc['point_rows']:
        P=row['P'];p=F(P,2*SC);n=row['center'];assert n==round(p) and P not in points;points[P]=row
        for q in [2,3]:
            item=row['q'+str(q)];poly=selected(W,n,q,p,p,item['mask']);assert list(map(str,poly))==item['poly']
            R=M*abs(p-n)**(24-q)/factorial(24-q);payment=ceil(R*Q)
            assert int(item['point_lower_Q'])==poly[0]-payment and int(item['point_upper_Q'])==poly[1]+payment
            checks+=1
    folder=HERE/'cover-targeted-curvature-evidence';first=json.loads(gzip.decompress((folder/'proof.json.gz').read_bytes()));extension=json.loads((folder/'cross-extension.json').read_bytes())
    cases=extension['cases']+[{'path':first['path'],'cell':first['cell'],'curvature':first['curvature']}];cases={r['path']:r for r in cases};assert len(cases)==3
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());terms=[r for r in params['a_upper'] if r[2]]
    rows_checked=active_checked=0;margins=[];results=[]
    for leaf in doc['leaves']:
        case=cases[leaf['path']];state=case['cell'];original=case['curvature'];assert leaf['direction']==original['direction'] and len(leaf['rows'])==len(terms)==41
        C=E=0;coeff=[0]*9;d=leaf['direction'];assert all(not v or state[0][i]>123*SC//128 for i,v in enumerate(d))
        for t,row in enumerate(leaf['rows']):
            i,j,aw=terms[t];z=INDEX[i,j];l,u=state[0][z],state[1][z];P=l+u;m0=int(row['m0']);m1=int(row['m1']);err=int(row['error'])
            assert row['term']==t and row['lower_gap_units']==l and row['upper_gap_units']==u and row['P']==P
            assert [P,str(m0),str(m1),str(err),row['kind']]==original['scalar_affine_data'][t]
            firstk=l//(SC//64);lastk=(max(l+1,u)+(SC//64)-1)//(SC//64)-1
            assert row['first_grid_cell']==firstk and row['last_grid_cell']==lastk
            if row['kind']=='interval':
                lo=min(grids[k]['q2']['actual_lower'] for k in range(firstk,lastk+1));hi=max(grids[k]['q2']['actual_upper'] for k in range(firstk,lastk+1))
                assert m1==0 and m0-err<=lo and hi<=m0+err;margin=F(min(lo-(m0-err),m0+err-hi))
            else:
                assert row['kind']=='affine';point=points[P];r=F(u-l,2*SC);unit=Q//DS
                e0=F(max(abs(int(point['q2']['point_lower_Q'])-m0*unit),abs(int(point['q2']['point_upper_Q'])-m0*unit)),unit)
                e1=F(max(abs(int(point['q3']['point_lower_Q'])-m1*unit),abs(int(point['q3']['point_upper_Q'])-m1*unit)),unit)
                B=max(grids[k]['q4']['old_abs_bound'] for k in range(firstk,lastk+1));assert B==row['old_fourth_bound']
                assert e0==F(row['point_value_error_units']) and e1==F(row['point_slope_error_units'])
                margin=F(err)-e0-e1*r-F(B)*r*r/2;assert margin>=0
            s=sum(d[i:j]);assert row['active']==(s!=0);rows_checked+=1;active_checked+=bool(s);margins.append(margin)
            weight=aw*s*s;C+=weight*(2*SC*m0-m1*P);E+=2*SC*weight*err
            for k in range(i,j):coeff[k]+=2*weight*m1
        exact=original['exact_flow'];assert C==int(exact['constant']) and E==int(exact['error']) and coeff==list(map(int,exact['coefficient']))
        desired=[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,9)]+[-coeff[-1]];balance=[0]*10;cost=0
        for i,j,amount,endpoint in exact['flow']['nonzero_flow']:
            amount=int(amount);assert amount>=0 and i!=j;edge=state[1][INDEX[i,j]] if i<j else -state[0][INDEX[j,i]]
            assert edge==endpoint;balance[i]+=amount;balance[j]-=amount;cost+=amount*endpoint
        assert balance==desired==list(map(int,exact['flow']['divergence'])) and cost==int(exact['flow']['cost'])
        upper=C+E+cost;assert upper==int(original['upper_numerator'])<0
        results.append({'path':leaf['path'],'upper_numerator':str(upper),'denominator':str(2*SC*10**10*DS)})
    active_raw=(HERE/'cover-curvature-actual-active.json').read_bytes();active=json.loads(active_raw);assert active['full_audit_sha256']==sha(raw)
    assert {r['k'] for r in active['grid_rows']}==set(doc['active_q2_grid_indices'])|set(doc['active_q4_grid_indices'])
    assert {r['P'] for r in active['point_rows']}==set(doc['active_point_P'])
    for row in active['grid_rows']:
        full=grids[row['k']];assert full['center']==row['n']
        if 'q2' in row:assert row['q2']==[full['q2'][k] for k in ['mask','old_lower','old_upper']]
        if 'q4' in row:assert row['q4']==[full['q4'][k] for k in ['mask','old_abs_bound']]
    for row in active['point_rows']:
        full=points[row['P']];assert full['center']==row['n']
        for q in ['q2','q3']:assert row[q]==[full[q][k] for k in ['mask','point_lower_Q','point_upper_Q']]
    assert rows_checked==123 and active_checked==51
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'active_input_sha256':sha(active_raw),'all_passed':True,
      'raw_Lean_literals_checked':len(literal),'selected_grid_union':len(grids),'selected_horner_checks':checks,'selected_points':len(points),
      'scalar_rows_checked':rows_checked,'active_scalar_rows':active_checked,'all_original_m0_m1_errors_preserved':True,
      'minimum_scalar_margin_using_original_fourth_bound':str(min(margins)),'strict_actual_feed_curvature_bounds':results,
      'ordinary_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-curvature-actual-feed-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
