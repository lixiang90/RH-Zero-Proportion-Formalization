"""Sparse and cross-cell direction reuse on only five fixed residual cells."""
from pathlib import Path
import hashlib,json,time
import numpy as np
import cover_correlated_curvature as curv
HERE=Path(__file__).parent;g=curv.g;SC=g.SC;DS=curv.DS
def main():
    start=time.monotonic();raw=(HERE/'cover-targeted-quadratic-gradient.json').read_bytes();doc=json.loads(raw)
    snap=(HERE/'cover-current-frontier-20261017b.json').read_bytes();assert hashlib.sha256(snap).hexdigest()==doc['snapshot_sha256']
    states={r['path']:tuple(r['state']) for r in json.loads(snap)['frontier']};oracle=curv.CurvatureOracle(curv.first.TaylorOracle(HERE/'cover_newjet.json'))
    global_dirs=[]
    for row in doc['results']:
        if row['uniform_negative_curvature_certificate']:global_dirs.append(row['uniform_negative_curvature_certificate']['direction'])
        for label in ['constrained_smallest_gradient_hint','root_hint']:
            x=row[label]['point'];H=np.zeros((9,9))
            for i,j,aw in g.TERMS:
                v,_=oracle.point(round(2*SC*sum(x[i:j])));H[i:j,i:j]+=(aw/g.D)*float((v.l+v.u)/2)
            values,vectors=np.linalg.eigh(H)
            for k,ev in enumerate(values):
                if ev>=-1e-10:break
                vec=vectors[:,k]
                global_dirs.append([round(v/max(abs(vec))*65536) for v in vec])
    rows=[];total=closed=0
    for row in doc['results']:
        if row['uniform_negative_curvature_certificate']:continue
        state=states[row['path']];free=[i for i in range(9) if state[0][i]>g.SEP];directions=set()
        for i in free:
            d=[0]*9;d[i]=1;directions.add(tuple(d))
            for j in free:
                if j<=i:continue
                for sign in [-1,1]:d=[0]*9;d[i]=1;d[j]=sign;directions.add(tuple(d))
        for old in global_dirs:
            for count in [1,2,3,9]:
                ids=sorted(free,key=lambda i:abs(old[i]),reverse=True)[:count];d=[old[i] if i in ids else 0 for i in range(9)]
                if any(d):directions.add(tuple(d))
        data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,aw in g.TERMS];best=float('inf');result=None
        for d in sorted(directions):
            upper,flow=curv.exact_upper(state,data,list(d));total+=1;normalized=upper/(2*SC*g.D*DS*sum(v*v for v in d));best=min(best,normalized)
            if upper<0:
                result={'kind':'correlated_negative_curvature','direction':list(d),'direction_scale':1,'upper_numerator':str(upper),
                  'denominator':str(2*SC*g.D*DS),'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
                  'exact_flow':flow,'affine_terms':sum(v[4]=='affine' for v in data)};closed+=1;break
        rows.append({'path':row['path'],'directions':len(directions),'best_normalized_upper':best,'result':result})
        print(json.dumps({'paths':len(rows),'new_candidates':closed,'directions_tested':total,'seconds':time.monotonic()-start}),flush=True)
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'paths':5,'directions_tested':total,'new_negative_curvature_candidates':closed,'independent_replay_passed':False,'rows':rows,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-targeted-curvature-crossprobe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)
if __name__=='__main__':main()
