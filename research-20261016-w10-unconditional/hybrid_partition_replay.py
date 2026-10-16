"""Independent stdlib replay of the partial hybrid finite partitions.

Every branch child, normalization step, integer leaf and exact rational
basin inclusion is replayed. Frontier cells are retained explicitly. This
does not establish the generic real quadratic lemma or a global Lean cover.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,collections,hashlib,importlib.util,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
spec=importlib.util.spec_from_file_location('pure_integer_auditor',ROOT/'research-20261016-w10-cert/independent_integer_audit.py')
a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('pilot',type=Path);ap.add_argument('--certificate',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();start=time.monotonic()
    before=sha(args.pilot);certsha=sha(args.certificate);doc=json.loads(args.pilot.read_text());meta=doc['stats'];cert=json.loads(args.certificate.read_text())
    assert certsha in meta['input_sha256'].values()
    assert all(sha(ROOT/p)==v for p,v in meta['input_sha256'].items())
    assert any(sha(p)==meta['script_sha256'] for p in HERE.glob('hybrid_phase_pilot*.py'))
    param=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_text())
    terms=[tuple(t) for t in param['a_upper'] if t[2]];bs=param['b_numerators'];points,lower=a.load_analytic_library()
    branches={r['path']:r for r in doc['branches']};leaves={r['path']:r for r in doc['accepted']};frontier={r['path']:r for r in doc['unresolved']}
    assert len(branches)==len(doc['branches']) and len(leaves)==len(doc['accepted']) and len(frontier)==len(doc['unresolved'])
    assert not(set(branches)&set(leaves) or set(branches)&set(frontier) or set(leaves)&set(frontier))
    def numeric(state,r):
        lo,hi=state;a.closure_valid(state);data=r['certificate']
        assert data['lower_bounds']==lo and data['upper_bounds']==hi
        pos=[0]*9;neg=[0]*9;cp=cm=0
        for i,j,upper,weight in r['multiplier']['steps']:
            y=int(weight);assert y>=0 and (i,j) in a.INDEX and j>=i+2 and isinstance(upper,bool)
            z=a.INDEX[i,j];base=sum(lo[i:j])
            for k in range(i,j):(neg if upper else pos)[k]+=y
            if upper:cp+=y*max(hi[z]-base,0);cm+=y*max(base-hi[z],0)
            else:cp+=y*max(base-lo[z],0);cm+=y*max(lo[z]-base,0)
        dual=r['multiplier'];assert pos==list(map(int,dual['P'])) and neg==list(map(int,dual['S'])) and cp==int(dual['Cp']) and cm==int(dual['Cm'])
        value=loss=gain=0;slopes=[0]*9;mass=[0]*9
        assert len(r['FS'])==len(terms)==39
        for (i,j,weight),(kind,m,p,q) in zip(terms,r['FS']):
            assert kind in range(4) and 0<=m<=1024 and p>=0 and q>=0
            w1,w2=([0,0] if kind==0 else [1024,0] if kind==1 else [m,0] if kind==2 else [1024-m,m])
            z=a.INDEX[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]));base=sum(lo[i:j])
            total=(1024-w1-w2)*lower(left,max(left+1,right));derivative=0
            for w,anchor in [(w1,p),(w2,q)]:
                word,l,u=points.get(anchor,(0,0,0))
                if w:assert u>0 and l<=left<=anchor<=right<=u
                v=word&a.MASK;sl=(word>>32)&a.MASK;d=word>>64
                total+=w*v;derivative+=w*sl
                loss+=weight*w*max(2000000000-d,0)*max(anchor-base,0)
                gain+=weight*w*max(d-2000000000,0)*max(anchor-base,0)
            value+=weight*total
            for k in range(i,j):slopes[k]+=weight*derivative;mass[k]+=weight*(w1+w2)
        pen=sum(max(hi[k]-lo[k],0)*max(2000000000*mass[k]+pos[k]-1024000000000*bs[k]-slopes[k]-neg[k],0) for k in range(9))
        total=10240000000000*sum(bs[k]*lo[k] for k in range(9))+32768*value+10*(gain+cm)-10*(loss+cp+pen)
        assert total==int(r['floor_numerator'])==int(r['mcheck_numerator']) and total>=a.TARGET
    used_b=set();used_l=set();used_f=set();counts=collections.Counter();stack=[('r',a.initial_root(bs))]
    while stack:
        path,raw=stack.pop()
        if path in frontier:
            assert frontier[path]['state']==raw;used_f.add(path);continue
        state,cuts=a.normalize_ordered(raw)
        if path in branches:
            r=branches[path];assert r['normalize_cuts']==cuts;used_b.add(path)
            axis=r['axis'];cut=r['cut'];assert 0<=axis<45 and state[0][axis]<cut<state[1][axis]
            for digit,upper in [('0',True),('1',False)]:stack.append((path+digit,a.raw_child(state,axis,cut,upper)))
        else:
            assert path in leaves,path
            r=leaves[path];assert r['normalize_cuts']==cuts;used_l.add(path);kind=r['kind'];counts[kind]+=1
            if kind=='numeric':numeric(state,r['result'])
            elif kind=='empty':assert 0<=r['axis']<45 and state[1][r['axis']]<state[0][r['axis']]
            elif kind=='reflection':assert state[1][8]<state[0][0]
            elif kind=='basin':
                row=cert['results'][r['basin_index']];assert row['integer_gaps']==r['integer_gaps'] and r['state']==state
                assert row['Gram_lower_bound_exact']==r['Gram_lower_bound_exact'] and F(row['Gram_lower_bound_exact'])>=F(433,50000)
                hull={h['integer_center']:h for h in cert['hulls']}
                for (i,j,w),term in zip(terms,row['terms']):
                    assert term['pair']==[i,j] and sum(row['integer_gaps'][i:j])==term['center']
                    h=hull[term['center']];z=a.INDEX[i,j]
                    assert F(h['lower'])<=F(state[0][z],32768)<=F(state[1][z],32768)<=F(h['upper'])
            else:raise AssertionError(kind)
    assert used_b==set(branches) and used_l==set(leaves) and used_f==set(frontier)
    assert len(leaves)+len(frontier)==len(branches)+1 and len(branches)+len(leaves)==meta['checked']
    assert sha(args.pilot)==before and sha(args.certificate)==certsha
    result={'scope':__doc__,'passed':True,'pilot_sha256':before,'certificate_sha256':certsha,'script_sha256':sha(Path(__file__)),
        'branches_replayed':len(branches),'accepted_leaves_replayed':dict(counts),'frontier_cells_retained':len(frontier),
        'all_partition_edges_and_normalization_replayed':True,'all_numeric_arithmetic_and_tangent_domains_recomputed':True,
        'all_basin_inclusions_exact_rational_checked':True,'all_inputs_unchanged':True,'global_cover_complete':not frontier,
        'generic_basin_real_soundness_formalized':False,'new_unconditional_zeta_bound_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
