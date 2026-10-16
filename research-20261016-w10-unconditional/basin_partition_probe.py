"""Count maximal existing subtrees inside rational convex lattice chambers.

This only measures a possible replacement partition. No Hessian positivity,
quadratic lower bound, Lean proof, or unconditional zeta result is asserted.
"""
from pathlib import Path
import argparse,bisect,collections,hashlib,json,sys,time
ROOT=Path(__file__).resolve().parents[1];OLD=ROOT/'research-20261016-w10-cert';HERE=Path(__file__).parent
sys.path.insert(0,str(HERE));from prune_floor_probe import branches_only
import ordered_generate as ordered
g=ordered.g
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert __debug__
    ap=argparse.ArgumentParser();ap.add_argument('--radius-hundredths',type=int,default=21)
    ap.add_argument('--output',type=Path,default=HERE/'basin-partition-probe.json');args=ap.parse_args()
    assert 0<args.radius_hundredths<50
    radius=args.radius_hundredths
    start=time.monotonic();source=OLD/'ordered-proof-input.json';source_sha=sha(source)
    names=['generate.py','ordered_generate.py'];bound={n:sha(OLD/n) for n in names}
    branches=branches_only(source);paths=sorted(branches)
    def leaves(path):return bisect.bisect_left(paths,path+'2')-bisect.bisect_left(paths,path)+1
    rows=[];todo=[('r',g.root())];visits=0;uncovered_numeric=0;uncovered_empty=0
    while todo:
        path,state=todo.pop();visits+=1
        state,_=ordered.normalize(state);lo,hi=state
        ni=[(lo[i]+hi[i]+g.SC)//(2*g.SC) for i in range(9)]
        inside=all(100*lo[g.LOOK[i,j]] >= (100*sum(ni[i:j])-radius)*g.SC and
                   100*hi[g.LOOK[i,j]] <= (100*sum(ni[i:j])+radius)*g.SC for i,j,a in g.TERMS)
        if inside:
            rows.append({'path':path,'center_gaps':ni,'old_leaves':leaves(path),
                         'lower_bounds':lo,'upper_bounds':hi})
        elif path in branches:
            node=branches[path]
            todo.extend((path+digit,ordered.rawsplit(state,node['axis'],node['cut'],upper))
                        for digit,upper in [('1',False),('0',True)])
        elif any(l>u for l,u in zip(lo,hi)) or hi[8]<lo[0]:uncovered_empty+=1
        else:uncovered_numeric+=1
    counts=collections.Counter()
    for r in rows:counts[tuple(r['center_gaps'])]+=r['old_leaves']
    total=sum(r['old_leaves'] for r in rows)
    stats={'scope':__doc__,'source_sha256':source_sha,'helper_sha256':bound,
        'script_sha256':sha(Path(__file__)),'seconds':time.monotonic()-start,'radius_hundredths':radius,
        'original_total_leaves':len(branches)+1,'visited_cells':visits,'maximal_basin_subtrees':len(rows),
        'distinct_lattice_centers':len(counts),'leaves_in_basin_subtrees':total,
        'leaves_outside':uncovered_numeric+uncovered_empty,'uncovered_nonempty_leaves':uncovered_numeric,
        'uncovered_empty_leaves':uncovered_empty,'hypothetical_leaf_saving':total-len(rows),
        'largest_basin_subtree_leaves':max((r['old_leaves'] for r in rows),default=0),
        'top_centers':[{'gaps':list(k),'old_leaves':v} for k,v in counts.most_common(25)],
        'quadratic_certificates_verified':False,'global_floor_proven':False}
    assert total+uncovered_numeric+uncovered_empty==len(branches)+1
    assert source_sha==sha(source) and bound=={n:sha(OLD/n) for n in names}
    args.output.write_text(json.dumps({'stats':stats,'subtrees':rows},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(stats),flush=True)

if __name__=='__main__':main()
