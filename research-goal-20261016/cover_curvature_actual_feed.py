"""Audit only the actual normalized jets used by three frozen curvature leaves.

The 10^-30 normalized W literals are compared byte-for-value with the frozen
Lean raw table. Fixed-integer Horner masks, point derivative errors and
selected q=2/q=4 grid bounds are recomputed without any Lean execution.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import functools,gzip,hashlib,json,re,time
HERE=Path(__file__).parent;ROOT=HERE.parent
Q=10**30;DS=10**15;SC=32768;WIDTH=SC//64;M=F(44,7)**24
sha=lambda b:hashlib.sha256(b).hexdigest()
ceil=lambda x:-((-x.numerator)//x.denominator)

def add(x,y):return x[0]+y[0],x[1]+y[1]
def mul(x,y):
    z=[a*b for a in x for b in y];return min(z),max(z)

def load():
    data=json.loads((HERE/'window_normalized_interval.json').read_bytes())
    W={int(n):[(F(l)*Q,F(u)*Q) for l,u in rows] for n,rows in data['integer_w_Taylor_coefficients'].items()}
    assert all(x.denominator==1 for rows in W.values() for r in rows for x in r)
    W={n:[(int(l),int(u)) for l,u in rows] for n,rows in W.items()}
    text=(ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean').read_text(encoding='utf8')
    pairs=[(int(l),int(l)+int(width)) for l,width in re.findall(r'iw \((-?\d+)\) \((\d+)\)',text)]
    assert len(pairs)==32*24 and pairs==[z for n in range(1,33) for z in W[n]]
    old=json.loads((HERE/'cover_newjet.json').read_bytes())
    oldW={int(n):[(F(l),F(u)) for l,u in rows] for n,rows in old['integer_taylor_coefficients'].items()}
    return W,oldW

def fixed(W,n,q,a,b):
    assert 1<=n<=32 and q in [2,3,4] and -F(1,2)<=a-n<=b-n<=F(1,2)
    xl=(a-n)*Q;xu=(b-n)*Q;X=(xl.numerator//xl.denominator,ceil(xu));d=23-q
    cs=[tuple(v*(factorial(j+q)//factorial(j)) for v in W[n][j+q]) for j in range(d+1)]
    value=cs[-1];mask=0
    for j in range(d-1,-1,-1):
        products=[value[0]*X[0],value[0]*X[1],value[1]*X[0],value[1]*X[1]]
        lo=products.index(min(products));hi=products.index(max(products));mask+=(lo+4*hi)*16**j
        value=add(cs[j],(products[lo]//Q,-((-products[hi])//Q)))
    return value,mask

def old_poly(old,n,q,a,b):
    derivative=q-1;cs=old[n];v=(F(0),F(0));x=(a-n,b-n)
    for j in range(len(cs)-1,derivative-1,-1):
        scale=factorial(j)//factorial(j-derivative)
        v=add(mul(v,x),(cs[j][0]*scale,cs[j][1]*scale))
    return v

def main():
    start=time.monotonic();W,old=load();folder=HERE/'cover-targeted-curvature-evidence'
    base=json.loads(gzip.decompress((folder/'proof.json.gz').read_bytes()));ext=json.loads((folder/'cross-extension.json').read_bytes())
    cases=[{'path':base['path'],'cell':base['cell'],'curvature':base['curvature']}]+ext['cases'];assert len(cases)==3
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());terms=[r for r in params['a_upper'] if r[2]]
    from cover_correlated_replay import a
    need2=set();need4=set();active2=set();active4=set();points=set();activepoints=set()
    for case in cases:
        for t,((i,j,aw),row) in enumerate(zip(terms,case['curvature']['scalar_affine_data'])):
            z=a.INDEX[i,j];l,u=case['cell'][0][z],case['cell'][1][z];P,m0,m1,err,kind=row;active=sum(case['curvature']['direction'][i:j])!=0
            cells=set(range(l//WIDTH,(max(l+1,u)+WIDTH-1)//WIDTH))
            if kind=='interval':need2.update(cells);active2.update(cells if active else [])
            else:
                need4.update(cells);points.add(P)
                if active:active4.update(cells);activepoints.add(P)
    grid=[];cache={};oldfail2=[];oldfail4=[];margins2=[];margins4=[]
    for k in sorted(need2|need4):
        n=(k+32)//64;lo=F(k,64);hi=F(k+1,64);entry={'cell':k,'center':n}
        for q,needed in [(2,need2),(4,need4)]:
            if k not in needed:continue
            poly,mask=fixed(W,n,q,lo,hi);R=M*F(1,2)**(24-q)/factorial(24-q)
            bounds=(F(poly[0],Q)-R,F(poly[1],Q)+R);v=old_poly(old,n,q,lo,hi);oldbounds=(v[0]-R,v[1]+R)
            if q==2:
                oldL=(oldbounds[0]*DS).__floor__();oldU=ceil(oldbounds[1]*DS);newL=(bounds[0]*DS).__floor__();newU=ceil(bounds[1]*DS)
                margin=min(bounds[0]-F(oldL,DS),F(oldU,DS)-bounds[1]);margins2.append(margin)
                if margin<0:oldfail2.append(k)
                entry['q2']={'degree':21,'mask':mask,'poly':list(map(str,poly)),'old_lower':oldL,'old_upper':oldU,'actual_lower':newL,'actual_upper':newU,'old_margin':str(margin)}
                cache[2,k]=(newL,newU,oldL,oldU)
            else:
                oldB=ceil(max(map(abs,oldbounds))*DS);newB=ceil(max(map(abs,bounds))*DS);margin=F(oldB,DS)-max(map(abs,bounds));margins4.append(margin)
                if margin<0:oldfail4.append(k)
                entry['q4']={'degree':19,'mask':mask,'poly':list(map(str,poly)),'old_abs_bound':oldB,'actual_abs_bound':newB,'old_margin':str(margin)}
                cache[4,k]=(newB,oldB)
        grid.append(entry)
    pointrows=[];pcache={}
    for P in sorted(points):
        p=F(P,2*SC);n=round(p);entry={'P':P,'center':n,'x':str(p)}
        for q in [2,3]:
            poly,mask=fixed(W,n,q,p,p);R=M*abs(p-n)**(24-q)/factorial(24-q);payment=ceil(R*Q)
            bounds=(poly[0]-payment,poly[1]+payment)
            entry['q'+str(q)]={'degree':23-q,'mask':mask,'poly':list(map(str,poly)),'Taylor_remainder':str(R),
              'point_lower_Q':str(bounds[0]),'point_upper_Q':str(bounds[1])}
            pcache[P,q]=bounds
        pointrows.append(entry)
    details=[];failed=[];active_failed=[];original_reference_failed=[];rowmargins=[]
    for case in cases:
        rows=[]
        for t,((i,j,aw),source) in enumerate(zip(terms,case['curvature']['scalar_affine_data'])):
            P,m0,m1,err,kind=source;P,m0,m1,err=map(int,[P,m0,m1,err]);z=a.INDEX[i,j];l,u=case['cell'][0][z],case['cell'][1][z]
            cells=list(range(l//WIDTH,(max(l+1,u)+WIDTH-1)//WIDTH));active=sum(case['curvature']['direction'][i:j])!=0
            row={'term':t,'pair':[i,j],'active':active,'lower_gap_units':l,'upper_gap_units':u,'P':P,'m0':str(m0),'m1':str(m1),'error':str(err),'kind':kind,'first_grid_cell':cells[0],'last_grid_cell':cells[-1]}
            if kind=='interval':
                lo=min(cache[2,k][0] for k in cells);hi=max(cache[2,k][1] for k in cells)
                oldlo=min(cache[2,k][2] for k in cells);oldhi=max(cache[2,k][3] for k in cells)
                margin=F(min(lo-(m0-err),(m0+err)-hi));required=max(m0-lo,hi-m0)
                oldok=m1==0 and m0-err<=oldlo and oldhi<=m0+err
                row.update(actual_lower=lo,actual_upper=hi,required_error=required)
            else:
                r=F(u-l,2*SC);v=pcache[P,2];s=pcache[P,3];unit=Q//DS
                e0=F(max(abs(v[0]-m0*unit),abs(v[1]-m0*unit)),unit)
                e1=F(max(abs(s[0]-m1*unit),abs(s[1]-m1*unit)),unit)
                B=max(cache[4,k][0] for k in cells);oldB=max(cache[4,k][1] for k in cells)
                needed=e0+e1*r+F(B)*r*r/2;margin=F(err)-needed;required=ceil(needed)
                p=F(P,2*SC);n=round(p);oldv=old_poly(old,n,2,p,p);olds=old_poly(old,n,3,p,p)
                R2=M*abs(p-n)**22/factorial(22);R3=M*abs(p-n)**21/factorial(21)
                olde0=max(abs((oldv[0]-R2)*DS-m0),abs((oldv[1]+R2)*DS-m0));olde1=max(abs((olds[0]-R3)*DS-m1),abs((olds[1]+R3)*DS-m1))
                oldok=err>=ceil(olde0+olde1*r+F(oldB)*r*r/2)
                row.update(point_value_error_units=str(e0),point_slope_error_units=str(e1),fourth_bound=B,old_fourth_bound=oldB,
                  radius=str(r),required_error=required)
            row['error_margin']=str(margin);row['original_row_preserved']=margin>=0
            if margin<0:
                failed.append([case['path'],t])
                if active:active_failed.append([case['path'],t])
            if not oldok:original_reference_failed.append([case['path'],t])
            rows.append(row);rowmargins.append(margin)
        details.append({'path':case['path'],'direction':case['curvature']['direction'],'rows':rows})
    sources={str(p.relative_to(ROOT)).replace('\\','/'):sha(p.read_bytes()) for p in [Path(__file__),HERE/'window_normalized_interval.json',
      ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean',HERE/'cover_newjet.json',HERE/'window_generate_choice_grid.py',folder/'proof.json.gz',folder/'cross-extension.json',
      ROOT/'research-20261016-followup/window_reweight_rational.json']}
    out={'scope':__doc__,'sources':sources,'Q':Q,'DS':DS,'SC':SC,'global_derivative24_bound':str(M),'raw_Lean_literal_table_matches_normalized_JSON':True,
      'all_original_reference_rows_revalidated':not original_reference_failed,'original_reference_failures':original_reference_failed,
      'leaf_count':3,'scalar_row_count':sum(len(r['rows']) for r in details),'active_scalar_rows':sum(r['active'] for c in details for r in c['rows']),
      'selected_q2_grid_indices':sorted(need2),'selected_q4_grid_indices':sorted(need4),'active_q2_grid_indices':sorted(active2),'active_q4_grid_indices':sorted(active4),
      'selected_point_P':sorted(points),'active_point_P':sorted(activepoints),'selected_grid_union_count':len(need2|need4),
      'q2_grid_old_bound_failures':oldfail2,'q4_grid_old_bound_failures':oldfail4,
      'minimum_q2_grid_margin':str(min(margins2)) if margins2 else None,'minimum_q4_grid_margin':str(min(margins4)) if margins4 else None,
      'all_original_scalar_rows_preserved':not failed,'all_active_scalar_rows_preserved':not active_failed,'scalar_failures':failed,'active_scalar_failures':active_failed,
      'minimum_scalar_error_margin':str(min(rowmargins)),'grid_rows':grid,'point_rows':pointrows,'leaves':details,
      'ordinary_Lean_proven':False,'actual_analytic_Lean_bridges_complete':False,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-start}
    target=HERE/'cover-curvature-actual-feed.json';target.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['leaf_count','scalar_row_count','active_scalar_rows','selected_grid_union_count','all_original_reference_rows_revalidated',
      'q2_grid_old_bound_failures','q4_grid_old_bound_failures','all_original_scalar_rows_preserved','all_active_scalar_rows_preserved','scalar_failures','seconds']}),flush=True)
    print(json.dumps({'point_count':len(points),'q2_cells':len(need2),'q4_cells':len(need4),'bytes':target.stat().st_size,'sha256':sha(target.read_bytes())}),flush=True)
if __name__=='__main__':main()
