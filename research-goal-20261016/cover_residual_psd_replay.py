"""Stdlib-only arithmetic replay of the fixed residual-PSD pilot cuts.

No optimizer or producer is imported. Taylor tuples are declared analytic
inputs; this checks their centering/scale and all rational cut expansions,
not the actual transcendental enclosure or primal PSD feasibility.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768;DS=10**15

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def add(p,k,v):
    v=p.get(k,F(0))+v
    if v:p[k]=v
    else:p.pop(k,None)

def multiply(p,q):
    result={}
    for a,v in p.items():
        for b,w in q.items():add(result,tuple(sorted(a+b)),v*w)
    return result

def main():
    began=time.monotonic();path=HERE/'cover-residual-psd-pilot.json';data=json.loads(path.read_text())
    watched=[path,Path(__file__)];initial={p.name:sha(p) for p in watched}
    assert data['phase']=='completed_bounded_pilot' and data['target']=='11/1250'
    assert data['maximum_cut_rounds']==2 and data['maximum_cuts_per_round']==16
    assert data['LP_method']=='highs-ipm' and data['LP_time_limit_seconds']==45
    source=HERE/'cover-cross-moment-remaining-six.json';prior=json.loads(source.read_text())['rows'][0]
    assert data['path']==prior['path'] and data['cell']==prior['cell'] and data['energy_packet']==prior['energy_packets'][0]
    cell=data['cell'];center=[F(a+b,2*SC) for a,b in zip(cell[0][:9],cell[1][:9])];radius=[F(b-a,2*SC) for a,b in zip(cell[0][:9],cell[1][:9])]
    betas=[]
    for slab in data['scalar_slabs']:
        i,j=slab['edge'];P,m0,m1,err,kind=slab['data'];m0,m1,err=map(int,[m0,m1,err])
        beta=[F(m0,DS)+F(m1,DS)*(sum(center[i:j])-F(P,2*SC))]
        beta += [F(m1,DS)*radius[r] if i<=r<j else F(0) for r in range(9)]
        assert beta==list(map(F,slab['beta'])) and F(err,DS)==F(slab['epsilon'])>=0
        betas.append((beta,F(err,DS)))
    hpairs=[(r,s) for r in range(9) for s in range(r,9)];hidx={p:50+k for k,p in enumerate(hpairs)}
    checked=[]
    for cut in data['cuts']:
        e=cut['term'];v=cut['integer_vector'];assert len(v)==11 and all(isinstance(x,int) for x in v)
        beta,eps=betas[e];t=v[10]
        vx={():F(v[0]),**{(r,):F(v[r+1]) for r in range(9)}}
        delta={():-beta[0],**{(r,):-beta[r+1] for r in range(9)},(9,):F(1)}
        poly=multiply(vx,vx)
        for mon,c in multiply(vx,delta).items():add(poly,mon,2*t*c)
        add(poly,(),F(t*t)*eps*eps)
        row={};constant=F(0)
        for mon,c in poly.items():
            if not mon:constant+=c
            elif len(mon)==1:
                r=mon[0]
                if r==9:add(row,9+e,c)
                else:add(row,r,c/radius[r]);constant-=c*center[r]/radius[r]
            else:
                r,s=mon;assert len(mon)==2 and (r,s)!=(9,9)
                add(row,95+41*r+e if s==9 else hidx[r,s],c)
        row={i:-c for i,c in row.items()};assert row=={i:F(c) for i,c in cut['coefficients']}
        assert constant==F(cut['bound'])
        assert max([F(1),abs(constant)]+list(map(abs,row.values())))==F(cut['scale'])
        checked.append({'term':e,'iteration':cut['discovery_iteration'],'integer_vector':v,
            'centered_fraction_expansion_matches':True,'squared_factor_soundness_requires_actual_slab':True})
    counts={i:sum(c['iteration']==i for c in checked) for i in [0,1]};assert all(v<=16 for v in counts.values())
    assert len(data['rounds'])<=3 and len(checked)<=32
    final={p.name:sha(p) for p in watched};assert final==initial
    result={'scope':__doc__,'input_sha256_start':initial,'input_sha256_end':final,'all_inputs_unchanged':True,
        'passed':True,'cases':1,'cuts_checked':len(checked),'cut_counts_by_iteration':counts,
        'scalar_centering_scales_checked':len(betas),'cut_results':checked,
        'actual_scalar_enclosures_independently_verified':False,'actual_Lean_exclusion_proven':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    output=HERE/'cover-residual-psd-replay.json';assert not output.exists();output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in result.items() if k!='cut_results'}),flush=True)

if __name__=='__main__':main()
