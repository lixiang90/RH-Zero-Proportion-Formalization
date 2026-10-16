"""Independent stdlib audit of exact full-U face reduction and every row map.

No reduction producer or numerical package is imported.  Verify the KKT
null equations as exact combinations of retained equalities, the T/J/S
identities, all old moment maps, all 1326 Gram entries, and every one of
50221 original row/box pullbacks including removed tautologies/duplicates.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'cover-full-u-face-replay.json';SC=32768


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(a,k,v):
    z=a.get(k,F(0))+v
    if z:a[k]=z
    else:a.pop(k,None)
def add(A,B,s=F(1)):
    c=A[0]+s*B[0];a=A[1].copy()
    for k,v in B[1].items():put(a,k,s*v)
    return c,a
def scale(A,s):return A[0]*s,{k:v*s for k,v in A[1].items() if v*s}
def unpack(A):return F(A['constant']),{i:F(v) for i,v in A['coefficients']}
def lhs(row):return -F(row['bound']),{k:F(v) for k,v in row['coefficients']}


def main():
    assert not OUT.exists();began=time.monotonic()
    facepath=HERE/'cover-full-u-face-model.json.gz';buildpath=HERE/'cover-full-u-face-build.json'
    fullpath=HERE/'cover-full-u-model.json';inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    scspath=HERE/'cover-full-u-joint-cone.json'
    paths=[Path(__file__),facepath,buildpath,fullpath,inputpath,parampath,scspath,Path(exact.__file__)]
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    raw=gzip.decompress(facepath.read_bytes());face=json.loads(raw);build=json.loads(buildpath.read_bytes())
    assert sha(facepath)==build['compressed_model_sha256'] and hashlib.sha256(raw).hexdigest()==build['uncompressed_model_sha256']
    full=json.loads(fullpath.read_bytes());inputs=json.loads(inputpath.read_bytes());params=json.loads(parampath.read_bytes());scs=json.loads(scspath.read_bytes())
    for p,h in face['source_sha256_start'].items():assert sha(ROOT/p)==h
    assert face['source_sha256_start']==face['source_sha256_end']
    old=exact.inputs(inputs['cell'],inputs['old_integer_rows'],inputs['old_meta'],inputs['u_bounds'],inputs['energy_packets'])
    terms=[tuple(t) for t in params['a_upper'] if t[2]];D=params['denominator']
    mu=[F(v['midpoint']) for v in full['derivative_normalization']];rad=[F(v['radius']) for v in full['derivative_normalization']]
    adj=[next(e for e,(i,j,_) in enumerate(terms) if i==r and j==r+1) for r in range(9)]
    keep=list(range(10))+[10+e for e in range(41) if e not in adj]
    assert keep==face['kept_Gram_feature_indices'] and adj==face['adjacent_derivative_indices']
    T=[{k:F(v) for k,v in row} for row in face['T_rows']]
    A=[{k:F(v) for k,v in row} for row in face['KKT_feature_forms_A']]
    J=[{k:F(v) for k,v in row} for row in face['pivot_right_inverse_J']]
    slot={i:k for k,i in enumerate(keep)}
    for r,e0 in enumerate(adj):
        inc=[e for e,(i,j,_) in enumerate(terms) if i<=r<j]
        h={0:F(params['b_numerators'][r],D)+sum(F(terms[e][2],D)*mu[e] for e in inc)}
        for e in inc:h[10+e]=F(terms[e][2],D)*rad[e]
        assert h==A[r] and h[10+e0]>0
        assert T[10+e0]=={slot[k]:-v/h[10+e0] for k,v in h.items() if k!=10+e0 and v}
    assert all(T[i]=={k:F(1)} for k,i in enumerate(keep))
    for i in range(51):
        for j in range(51):
            left=F(i==j)-(T[i].get(slot[j],F(0)) if j in slot else F(0))
            assert left==sum(J[i].get(r,F(0))*A[r].get(j,F(0)) for r in range(9))
    assert all(sum(A[r].get(i,F(0))*T[i].get(k,F(0)) for i in range(51))==0 for r in range(9) for k in range(42))
    # Confirm M*A=0 is already supplied by original equality pairs.
    M=[[None for j in range(51)] for i in range(51)]
    for i,j,entry in full['joint_PSD_affine_entries']:M[i][j]=M[j][i]=unpack(entry)
    for r in range(9):
        n=next(n for n,m in enumerate(inputs['old_meta']) if m==['KKT',r,1])
        base=old['rows'][19*n];H=(-base['bound'],base['coeff'])
        for i in range(51):
            ma=(F(0),{})
            for j,a in A[r].items():ma=add(ma,M[i][j],a)
            if i==0:expected=H
            elif i<10:
                row=old['rows'][19*n+2+2*(i-1)]
                assert row['meta'][0]=='RLT' and row['meta'][3]==1
                expected=add((-row['bound'],row['coeff']),H,F(-1))
            else:
                e=i-10;row=full['new_linear_rows'][82+3444+2*(r*41+e)]
                assert row['meta']==['u_multiplied_free_KKT',r,e,1]
                expected=scale(add(lhs(row),H,-mu[e]),1/rad[e])
            assert ma==expected,(r,i)
    rid={(min(i,j),max(i,j)):k for i,j,k in face['reduced_Gram_entry_variables']}
    assert len(rid)==902 and set(rid.values())==set(range(902))
    memo={}
    def moment(i,j):
        key=tuple(sorted([i,j]))
        if key not in memo:
            c=F(0);a={}
            for r,v in T[i].items():
                for s,w in T[j].items():
                    if r==s==0:c+=v*w
                    else:put(a,rid[min(r,s),max(r,s)],v*w)
            memo[key]=(c,a)
        return memo[key]
    maps=[None]*1326
    center=old['center'];radius=old['radius']
    for r in range(9):maps[r]=add((center[r],{}),moment(0,1+r),radius[r])
    for e in range(41):maps[9+e]=add((mu[e],{}),moment(0,10+e),rad[e])
    for r,s in exact.PAIRS:maps[exact.hindex(r,s)]=moment(1+r,1+s)
    for r in range(9):
        for e in range(41):maps[exact.qindex(r,e)]=add(scale(moment(0,1+r),mu[e]),moment(1+r,10+e),rad[e])
    for e,t,k in full['W_variable_pairs']:maps[k]=moment(10+e,10+t)
    maps[1325]=(F(0),{902:F(1)})
    assert maps[:1325]==[unpack(v) for v in face['original_1325_variable_maps']]
    def substitute(a):
        out=(F(0),{})
        for k,v in a.items():out=add(out,maps[k],v)
        return out
    for i,j,entry in full['joint_PSD_affine_entries']:
        c,a=unpack(entry);assert add(substitute(a),(c,{}))==moment(i,j)
    for i,j,k in face['reduced_Gram_entry_variables']:assert moment(keep[i],keep[j])==(F(0),{k:F(1)})
    rows=face['reduced_distinct_linear_rows'];origin=face['original_row_to_reduced_or_tautology'];counter=taut=dups=0;seen=set();digest=hashlib.sha256()
    def verify(coeff,bound,source_scale,label):
        nonlocal counter,taut,dups
        digest.update(json.dumps([label,str(bound),str(source_scale),[[k,str(v)] for k,v in sorted(coeff.items())]],separators=(',',':')).encode())
        cc,a=substitute(coeff);B=bound-cc;index,rawscale=origin[counter];counter+=1;s=F(rawscale)
        if index==-1:
            assert not a and B==s and B>=0;taut+=1;return
        assert s>0 and s==max([abs(B)]+list(map(abs,a.values())))
        rcoeff,rbound=rows[index]
        assert a=={k:s*F(v) for k,v in rcoeff} and B==s*F(rbound)
        if index in seen:dups+=1
        else:assert index==len(seen);seen.add(index)
    for n,row in enumerate(old['rows']):
        a=row['coeff'].copy()
        if row['meta'][0]=='energy':a[1325]=F(-1,1000)
        verify(a,row['bound'],row['scale'],['old',n,row['meta']])
    for n,row in enumerate(full['new_linear_rows']):verify({k:F(v) for k,v in row['coefficients']},F(row['bound']),F(row['scale']),['new',n,row['meta']])
    bounds=old['bounds']+[(F(l),F(u)) for _,l,u in full['new_variable_bounds']]
    for k,(l,u) in enumerate(bounds):verify({k:F(-1)},-l,F(1),['box',k,-1]);verify({k:F(1)},u,F(1),['box',k,1])
    verify({1325:F(-1)},F(0),F(1),['slack_nonnegative'])
    assert counter==50221 and len(seen)==46347 and taut==1080 and dups==2794
    assert digest.hexdigest()==face['original_linear_digest']==scs['exact_linear_row_serialization_sha256']
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'exact_full_U_face_and_all_row_box_pullbacks_independently_verified',
        'path':face['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'old_variables':1325,'reduced_variables':902,'old_PSD_size':51,'reduced_PSD_size':42,
        'KKT_null_equations_identified_as_retained_linear_combinations':459,
        'full_Gram_entries_verified':1326,'reduced_coordinate_left_inverse_checks':902,
        'original_rows_checked':counter,'distinct_rows':len(seen),'tautologies_removed':taut,'positive_duplicates_removed':dups,
        'all_original_boxes_retained_under_substitution':True,'mathematical_model_changes':0,
        'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','original_rows_checked','distinct_rows','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
