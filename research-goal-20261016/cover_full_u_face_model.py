"""Exact free-KKT face reduction of the frozen full-U model, no solver.

Nine nonzero adjacent-edge derivative pivots reduce 51 Gram features to 42
and all 1325 moments to 902.  Substitute every frozen linear row and box,
drop exact tautologies and positive-proportional duplicates, and verify
M=T*Q*T^T entrywise.  This changes representation, not mathematical scope.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,time
import cover_cross_moment_exact_rows as exact
from cover_dynamic_sector_static import form,add,mul,pack

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
NV=902;FV=1325;SC=32768
OUT=HERE/'cover-full-u-face-model.json.gz';RECEIPT=HERE/'cover-full-u-face-build.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unpack(A):return [F(A['constant']),{i:F(v) for i,v in A['coefficients']}]


def main():
    assert not OUT.exists() and not RECEIPT.exists()
    began=time.monotonic();modelpath=HERE/'cover-full-u-model.json';inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    fullscspath=HERE/'cover-full-u-joint-cone.json';parampath=ROOT/'research-20261016-followup/window_reweight_rational.json'
    sealpath=HERE/'cover-full-u-files.json'
    paths=[Path(__file__),modelpath,inputpath,fullscspath,parampath,sealpath,Path(exact.__file__),HERE/'cover_dynamic_sector_static.py']
    pins={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    assert sha(sealpath)=='fef4caa3f4566b398d66a3d9e8b12e846e128fb5bf8188bca1e0284267db1e46'
    model=json.loads(modelpath.read_bytes());inputs=json.loads(inputpath.read_bytes())
    fullscs=json.loads(fullscspath.read_bytes());params=json.loads(parampath.read_bytes())
    assert model['path']==inputs['path']==fullscs['path'] and model['variables']==FV
    terms=[tuple(t) for t in params['a_upper'] if t[2]];D=params['denominator']
    norm=model['derivative_normalization'];mu=[F(v['midpoint']) for v in norm];rad=[F(v['radius']) for v in norm]
    adj=[next(e for e,(i,j,_) in enumerate(terms) if i==r and j==r+1) for r in range(9)]
    nonadj=[e for e in range(41) if e not in adj]
    keep=list(range(10))+[10+e for e in nonadj];assert len(keep)==42
    slot={i:k for k,i in enumerate(keep)}
    T=[{} for _ in range(51)]
    for full,k in slot.items():T[full]={k:F(1)}
    A=[];J=[{} for _ in range(51)];pivots=[]
    for r,e0 in enumerate(adj):
        inc=[e for e,(i,j,_) in enumerate(terms) if i<=r<j]
        C=F(params['b_numerators'][r],D)+sum(F(terms[e][2],D)*mu[e] for e in inc)
        h={0:C}
        for e in inc:h[10+e]=F(terms[e][2],D)*rad[e]
        pivot=h[10+e0];assert pivot>0;pivots.append(pivot);A.append(h);J[10+e0][r]=1/pivot
        T[10+e0]={slot[f]:-v/pivot for f,v in h.items() if f!=10+e0 and v}
    assert all(sum(h.get(i,F(0))*T[i].get(k,F(0)) for i in range(51))==0 for h in A for k in range(42))
    assert all(T[i]=={k:F(1)} for k,i in enumerate(keep))
    # I-T*S=J*A^T; S selects the kept feature rows.  This proves the face
    # factorization for every symmetric M with M*A=0, independent of PSD.
    for i in range(51):
        for j in range(51):
            lhs=F(i==j)-T[i].get(slot[j],F(0)) if j in slot else F(i==j)
            rhs=sum(J[i].get(r,F(0))*A[r].get(j,F(0)) for r in range(9))
            assert lhs==rhs
    rp=[(i,j) for j in range(42) for i in range(j,42) if (i,j)!=(0,0)]
    rid={tuple(sorted(p)):k for k,p in enumerate(rp)};assert len(rp)==NV
    cache={}
    def moment(i,j):
        key=tuple(sorted([i,j]))
        if key not in cache:
            ans=form()
            for a,v in T[i].items():
                for b,w in T[j].items():
                    if a==b==0:ans=add(ans,form(v*w))
                    else:ans=add(ans,form(0,{rid[min(a,b),max(a,b)]:v*w}))
            cache[key]=ans
        return cache[key]
    maps=[None]*(FV+1)
    center=[F(l+u,2*SC) for l,u in zip(inputs['cell'][0][:9],inputs['cell'][1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(inputs['cell'][0][:9],inputs['cell'][1][:9])]
    for r in range(9):maps[r]=add(form(center[r]),moment(0,1+r),radius[r])
    for e in range(41):maps[9+e]=add(form(mu[e]),moment(0,10+e),rad[e])
    for r,s in exact.PAIRS:maps[exact.hindex(r,s)]=moment(1+r,1+s)
    for r in range(9):
        for e in range(41):maps[exact.qindex(r,e)]=add(mul(moment(0,1+r),mu[e]),moment(1+r,10+e),rad[e])
    for e,t,k in model['W_variable_pairs']:maps[k]=moment(10+e,10+t)
    maps[FV]=form(0,{NV:F(1)})
    assert all(v is not None for v in maps)
    def substitute(coeff):
        ans=form()
        for k,v in coeff.items():ans=add(ans,maps[k],v)
        return ans
    for i,j,entry in model['joint_PSD_affine_entries']:
        c,a=unpack(entry);assert add(substitute(a),form(c))==moment(i,j)
    old=exact.inputs(inputs['cell'],inputs['old_integer_rows'],inputs['old_meta'],inputs['u_bounds'],inputs['energy_packets'])
    kkt=[m for m in inputs['old_meta'] if m[0]=='KKT']
    assert len(kkt)==18 and all(sorted(m[2] for m in kkt if m[1]==r)==[-1,1] for r in range(9))
    reduced=[];lookup={};origin=[];tautologies=duplicates=0;original_digest=hashlib.sha256()
    def append(coeff,bound,source_scale,label):
        nonlocal tautologies,duplicates
        original_digest.update(json.dumps([label,str(bound),str(source_scale),[[k,str(v)] for k,v in sorted(coeff.items())]],separators=(',',':')).encode())
        c,a=substitute(coeff);B=bound-c
        if not a:
            assert B>=0,('constant contradiction',label,B)
            tautologies+=1;origin.append([-1,str(B)]);return
        scale=max([abs(B)]+list(map(abs,a.values())));assert scale>0
        row=[[[k,str(v/scale)] for k,v in sorted(a.items())],str(B/scale)]
        key=json.dumps(row,separators=(',',':'))
        if key in lookup:index=lookup[key];duplicates+=1
        else:
            index=len(reduced);lookup[key]=index;reduced.append(row)
        origin.append([index,str(scale)])
    for n,row in enumerate(old['rows']):
        coeff=row['coeff'].copy()
        if row['meta'][0]=='energy':coeff[FV]=F(-1,1000)
        append(coeff,row['bound'],row['scale'],['old',n,row['meta']])
    for n,row in enumerate(model['new_linear_rows']):append({k:F(v) for k,v in row['coefficients']},F(row['bound']),F(row['scale']),['new',n,row['meta']])
    bounds=old['bounds']+[(F(l),F(u)) for _,l,u in model['new_variable_bounds']]
    for k,(l,u) in enumerate(bounds):
        append({k:F(-1)},-l,F(1),['box',k,-1]);append({k:F(1)},u,F(1),['box',k,1])
    append({FV:F(-1)},F(0),F(1),['slack_nonnegative'])
    assert len(origin)==50221 and original_digest.hexdigest()==fullscs['exact_linear_row_serialization_sha256']
    final={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths};assert final==pins
    result={'scope':__doc__,'status':'exact_51_to_42_face_and_1325_to_902_map_verified',
        'path':model['path'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'original_variables':FV,'reduced_variables':NV,'original_PSD_size':51,'reduced_PSD_size':42,
        'old_slack_index':FV,'reduced_slack_index':NV,
        'adjacent_derivative_indices':adj,'nonadjacent_derivative_indices':nonadj,'kept_Gram_feature_indices':keep,
        'nonzero_positive_pivots':list(map(str,pivots)),
        'T_rows':[[[k,str(v)] for k,v in sorted(row.items())] for row in T],
        'KKT_feature_forms_A':[[[k,str(v)] for k,v in sorted(row.items())] for row in A],
        'pivot_right_inverse_J':[[[k,str(v)] for k,v in sorted(row.items())] for row in J],
        'projection_identity':'I-T*S=J*A^T; S*T=I42; A^T*T=0',
        'reduced_Gram_entry_variables':[[i,j,rid[min(i,j),max(i,j)]] for i,j in rp],
        'original_1325_variable_maps':[pack(a) for a in maps[:FV]],
        'joint_PSD_entries_verified':1326,'all_original_boxes_pulled_back':True,
        'original_rows_including_boxes':len(origin),'original_linear_digest':original_digest.hexdigest(),
        'reduced_distinct_linear_rows':reduced,'original_row_to_reduced_or_tautology':origin,
        'exact_tautology_rows_removed':tautologies,'positive_proportional_duplicates_removed':duplicates,
        'same_mathematical_model':True,'new_mathematical_constraints':0,'solver_calls':0,'Lean_invocations':0,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    raw=(json.dumps(result,separators=(',',':'),allow_nan=False)+'\n').encode()
    OUT.write_bytes(gzip.compress(raw,mtime=0))
    summary={k:result[k] for k in ['status','path','source_sha256_start','source_sha256_end','original_variables','reduced_variables',
        'original_PSD_size','reduced_PSD_size','joint_PSD_entries_verified','original_rows_including_boxes',
        'exact_tautology_rows_removed','positive_proportional_duplicates_removed','same_mathematical_model','elapsed_milliseconds']}
    summary.update({'reduced_distinct_linear_rows':len(reduced),'compressed_model_sha256':sha(OUT),
                    'uncompressed_model_sha256':hashlib.sha256(raw).hexdigest(),'uncompressed_bytes':len(raw),'compressed_bytes':OUT.stat().st_size})
    RECEIPT.write_text(json.dumps(summary,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:summary[k] for k in ['status','reduced_variables','reduced_PSD_size','reduced_distinct_linear_rows',
        'exact_tautology_rows_removed','positive_proportional_duplicates_removed','elapsed_milliseconds','compressed_bytes']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
