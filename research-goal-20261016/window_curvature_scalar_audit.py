"""Replay exactly the rational point-scaling choices in CurvatureScalar.

This is a preflight audit, not a replacement for ordinary Lean checking.
The fixed point consumer scales by the exact rational offset, which is
tighter than the interval-offset point probe used during discovery.
"""
from pathlib import Path
import json,math,hashlib
from fractions import Fraction as F
HERE=Path(__file__).parent;Q=10**30;DS=10**15;SC=32768;M=F(44,7)**24
raw=json.loads((HERE/'window_normalized_interval.json').read_bytes())
W={int(n):[(int(F(l)*Q),int(F(u)*Q))for l,u in rows]for n,rows in raw['integer_w_Taylor_coefficients'].items()}
P=HERE/'cover-curvature-actual-active.json';feed=json.loads(P.read_bytes())

def point_error(n,q,p,v):
    cs=[tuple(z*(math.factorial(j+q)//math.factorial(j))for z in W[n][j+q])for j in range(24-q)]
    z=cs[-1];delta=p-n
    for c in cs[-2::-1]:
        products=[F(x)*delta for x in z];l,u=min(products),max(products)
        z=(c[0]+math.floor(l),c[1]+math.ceil(u))
    return max(abs(F(z[0],Q)-v),abs(F(z[1],Q)-v))+M*abs(delta)**(24-q)/math.factorial(24-q)

def main():
    points={p['P']:p for p in feed['point_rows']};G={r['k']:r for r in feed['grid_rows']};margins=[]
    for leaf in feed['leaves']:
        for row in leaf['rows']:
            if row['kind']=='affine':
                p=F(row['P'],2*SC);n=points[row['P']]['n'];v=F(int(row['m0']),DS);s=F(int(row['m1']),DS)
                rad=max(abs(F(row['l'],SC)-p),abs(F(row['u'],SC)-p))
                bound=point_error(n,2,p,v)+point_error(n,3,p,s)*rad+F(row['B4'],DS)*rad*rad/2
                margin=F(int(row['err']),DS)-bound
                assert F(row['l'],SC)<=p<=F(row['u'],SC)
                assert all(G[k]['q4'][1]<=row['B4']for k in range(row['first'],row['last']+1))
            else:
                lo=int(row['m0'])-int(row['err']);hi=int(row['m0'])+int(row['err'])
                assert int(row['m1'])==0
                assert all(lo<=G[k]['q2'][1]and G[k]['q2'][2]<=hi for k in range(row['first'],row['last']+1))
                margin=F(min(min(G[k]['q2'][1]-lo,hi-G[k]['q2'][2])for k in range(row['first'],row['last']+1)),DS)
            assert margin>=0,(leaf['path'],row['t'],margin)
            assert F(row['first'],64)<=F(row['l'],SC) and F(row['u'],SC)<=F(row['last']+1,64)
            margins.append(margin)
    out={'scope':__doc__,'input_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),
        'all_exact_rational_scalar_checks_hold':True,'rows':len(margins),'minimum_error_margin':str(min(margins)),
        'ordinary_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    (HERE/'window_curvature_scalar_audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'rows':len(margins),'all_checks_hold':True,'minimum_error_margin':float(min(margins))}))
if __name__=='__main__':main()
