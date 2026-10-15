"""Research-only exact lower replay using inherited univariate tangents.

Floating LP duals discover convex mixtures.  The final arithmetic rounds their
weights down, checks the pair-weight capacities exactly and minimizes the
resulting affine expression by integer min-cost flow.  Analytic soundness and
coverage of these extracted supports still require separate Lean proofs.
"""
from pathlib import Path
import argparse, ast, re, json, gzip, time
import numpy as np
from scipy.optimize import linprog
import affine_leaf_replay as old

f=old.f; DEN=old.DEN; SC=32768; WD=10**11*SC; LD=10**12

def tangent_library():
    pool={}
    fullpt={}
    for j,l in re.findall(r'\.lf (\d+) (\[[^\]]*\])',f.cert):
        for k,v in ast.literal_eval(l):fullpt[1024*int(j)+k]=v
    def walk(walker,s,pos=1):
        w=walker.bits(pos)
        if w&1:
            ax=(w>>1)&63;md=(w>>7)&1;i,j=f.ALL[ax]
            q=f.bcut(s[0][ax],s[1][ax]) if md else (s[0][ax]+s[1][ax])>>1
            end=walk(walker,f.split(s,i,j,q,True),pos+8)
            return walk(walker,f.split(s,i,j,q,False),end)
        if s[1][7]<s[0][0]:return pos+1
        assert not (w>>1)&1
        off=0
        for i,j,a,k in f.TS:
            l,u=f.term_bounds(s,i,j);(k,m,p,r),off=f.dec(w>>2,off,l,u)
            for weight,q in zip(f.weights(k,m),(p,r)):
                if weight:
                    assert l<=q<=u and q in f.PT
                    if q in pool:pool[q]=(min(pool[q][0],l),max(pool[q][1],u))
                    else:pool[q]=(l,u)
        *_,off=f.ydec(w>>2,off,s)
        return pos+2+off
    for r,(idx,end) in f.rootrecords.items():assert walk(f.Walker(r),f.root(idx))==end
    # The attributed table already certifies a full validity interval for each
    # tangent, in its upper packed fields. All inherited uses must lie inside.
    for p,(l,u) in pool.items():
        # Serialized PTrD leaves use offset packing (pwD), not PT's absolute
        # ivA/ivB packing. Preserve this distinction when decoding the source.
        a=max(0,p-((fullpt[p]>>96)&((1<<20)-1)))
        b=p+(fullpt[p]>>116)
        assert a<=l<=p<=u<=b and b>0
        assert (fullpt[p]&((1<<96)-1))==f.PT[p]
    return sorted((p,l,u) for p,(l,u) in pool.items())

def term_lines(l,u,pool):
    lines=[]
    for p,pl,pu in pool:
        if pl*10<=l and u<=pu*10:
            v=f.PT[p];sp=(v>>32)&f.MASK32;dp=v>>64
            slope=sp-2000000000;err=4000000000-sp-dp
            assert err>=0
            const=10*SC*(v&f.MASK32)-100*slope*p-10*err*max(10*p-l,0)
            lines.append((const,10*slope,p))
    # Existing global interval table, with integer outer rounding.
    lb=f.lb(l//10,(u+9)//10)
    if lb:lines.append((lb*10*SC,0,-1))
    return lines

def certify(cell,word,pool,psi,export=False):
    bounds=[(278528,491520),(491520,819200),(819200,13107200)]
    lo=[x*10 for x in cell['lo']];hi=[x*10 for x in cell['hi']]
    for r,t in enumerate(word):lo[r]=max(lo[r],bounds[t][0]);hi[r]=min(hi[r],bounds[t][1])
    cl=old.close(lo,hi)
    if cl is None:return None
    terms=[];indices=[]
    for i,j,a,_ in f.TS:
        lines=term_lines(-cl[j][i],cl[i][j],pool)
        terms.append(lines);indices.append((i,j,a))
    pc,pg=psi(word)
    # g variables are physical gaps, t variables are individual w values.
    obj=np.r_[np.array(f.BS)/1e20+np.array(pg,dtype=float)*SC/DEN,
              [a/1e20 for i,j,a in indices]]
    rows=[];rhs=[];meta=[]
    for t,((i,j,a),lines) in enumerate(zip(indices,terms)):
        for const,slope,p in lines:
            row=np.zeros(8+len(terms));row[i:j]=slope*(10*SC)/WD;row[8+t]=-1
            rows.append(row);rhs.append(-const/WD);meta.append((t,const,slope,p))
    for (i,j),l,u in zip(f.ALL,lo,hi):
        row=np.zeros(8+len(terms));row[i:j]=1
        rows.extend([row,-row]);rhs.extend([u/(10*SC),-l/(10*SC)])
    lp=linprog(obj,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*8+[(0,None)]*len(terms),
               method='highs',options={'dual_feasibility_tolerance':1e-9,
                                     'primal_feasibility_tolerance':1e-9})
    assert lp.success,lp.message
    lam=np.floor(np.maximum(0,-lp.ineqlin.marginals[:len(meta)])*LD).astype(np.int64)
    for t,(i,j,a) in enumerate(indices):
        js=[k for k,m in enumerate(meta) if m[0]==t]
        total=sum(int(lam[k]) for k in js);cap=a*LD//10**20
        if total>cap:
            k=max(js,key=lambda k:lam[k]);assert lam[k]>=total-cap
            lam[k]-=total-cap
        assert sum(int(lam[k]) for k in js)<=cap
    # All terms now have common denominator LD*WD.  The pressure and potential
    # are converted without approximation before the affine flow bound.
    cd=LD*WD
    assert cd%(10**20*10*SC)==0 and DEN%cd==0
    # DEN is a multiple of cd for the chosen powers of ten.
    outden=DEN
    intercept=pc;coeff=[b*(DEN//(10**20*10*SC))+g//10 for b,g in zip(f.BS,pg)]
    for weight,(t,const,slope,p) in zip(lam,meta):
        if not weight:continue
        i,j,_=indices[t];fac=int(weight)*(DEN//cd)
        intercept+=fac*const
        for r in range(i,j):coeff[r]+=fac*slope
    exact=old.minimize_exact(intercept,coeff,lo,hi,return_dual=export)
    dual=None
    if export:exact,dual=exact
    result={'floor_numerator':str(exact),'floor':exact/DEN,
            'lp_floor':float(lp.fun+pc/DEN),'gaps':lp.x[:8].tolist(),
            'active_lines':sum(int(x)>0 for x in lam),'constraint_count':len(rows)}
    if export:
        result['certificate']={'flow':dual,'intercept':str(intercept),
            'gap_coefficients':list(map(str,coeff)),
            'lower_bounds':lo,'upper_bounds':hi,'mixture_denominator':LD,
            'mixture':[[t,p,str(int(weight)),str(const),str(slope)]
                for weight,(t,const,slope,p) in zip(lam,meta) if weight]}
    return result

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=0)
    ap.add_argument('--offset',type=int,default=0)
    ap.add_argument('--export',action='store_true')
    ap.add_argument('--output',default='tangent-envelope-replay.json');args=ap.parse_args()
    start=time.time();inp=json.loads(Path(__file__).with_name('affine-leaf-replay.json').read_text())
    cells=old.collect();psi,hashes=old.potential();pool=tangent_library()
    failures=inp['unresolved'][args.offset:];failures=failures[:args.limit] if args.limit else failures
    print(json.dumps({'inherited_tangents':len(pool),'cells_to_check':len(failures)}),flush=True)
    result=[]
    for k,r in enumerate(failures):
        rec=certify(cells[r['leaf']],r['word'],pool,psi,export=args.export)
        result.append({**r,'envelope':rec})
        if k%100==0:print(json.dumps({'checked':k,'seconds':time.time()-start,
             'unresolved':sum(x['envelope'] is not None and x['envelope']['floor']<.008598 for x in result)}),flush=True)
    unresolved=[r for r in result if r['envelope'] is not None and r['envelope']['floor']<.008598]
    out={'status':'research replay only; analytic support extraction not Lean proved',
         'target':'4299/500000','inherited_tangent_count':len(pool),'input_hashes':hashes,
         'offset':args.offset,'checked':len(result),'unresolved_count':len(unresolved),'results':result,
         'elapsed_seconds':time.time()-start}
    outpath=Path(__file__).with_name(args.output)
    if outpath.suffix=='.gz':
        with gzip.open(outpath,'wt',encoding='utf8') as stream:json.dump(out,stream,separators=(',',':'))
    else:outpath.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)

if __name__=='__main__':main()
