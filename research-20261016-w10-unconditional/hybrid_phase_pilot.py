"""Pilot an exact partition using the independently audited rational basins.

The quadratic basin data are exact rational evidence, but their generic real
soundness and a full partition are not yet Lean proofs. Numeric leaves use
the inherited exact checker. A floating LP solution chooses splits only.
Every raw branch child is retained, so no complement region is discarded.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OLD=ROOT/'research-20261016-w10-cert'
sys.path.insert(0,str(OLD));sys.path.insert(0,str(HERE))
import ordered_generate as ordered
from prune_floor_probe import independently_check
from reduce_proof_input import sha
g=ordered.g

def load_basins(certificate,replay):
    doc=json.loads(certificate.read_text());audit=json.loads(replay.read_text())
    assert audit['passed'] and audit['certificate_sha256']==sha(certificate)
    assert doc['parameter_sha256']==sha(g.PAR) and doc['candidate_floor_pass_count']==69
    radius=F(doc.get('chamber_span_radius_exact','21/100'))
    basins={}
    for k,row in enumerate(doc['results']):
        assert row['passes_candidate_floor_exact'] and F(row['Gram_lower_bound_exact'])>=F(433,50000)
        key=tuple(row['integer_gaps']);bounds=[]
        for (i,j,a),term in zip(g.TERMS,row['terms']):
            assert term['pair']==[i,j] and sum(key[i:j])==term['center']
            n=term['center'];l=max(F(17,20),F(n)-radius);u=F(n)+radius
            # Inward rounding ensures every point in the emitted Nat cell
            # belongs to the exact rational chamber. This only costs slivers.
            low=-(-(l.numerator*g.SC)//l.denominator)
            high=(u.numerator*g.SC)//u.denominator
            assert F(low,g.SC)>=l and F(high,g.SC)<=u
            bounds.append((g.LOOK[i,j],low,high))
        basins[key]={'index':k,'key':list(key),'bounds':bounds,'Gram_lower_bound_exact':row['Gram_lower_bound_exact'],
                     'anchor_numerators':row['anchor_numerators'],'anchor_denominator':row['anchor_denominator']}
    assert len(basins)==69
    return basins

def contained(state,basin):
    lo,hi=state
    return all(low<=lo[z] and hi[z]<=high for z,low,high in basin['bounds'])

def anchor_contained(state,basin):
    lo,hi=state;d=basin['anchor_denominator'];q=basin['anchor_numerators']
    return all(lo[z]*d<=sum(q[i:j])*g.SC<=hi[z]*d for z,(i,j) in enumerate(g.ALL))

def carve_cut(state,basin):
    lo,hi=state;choices=[]
    for z,low,high in basin['bounds']:
        width=hi[z]-lo[z]
        if lo[z]<low<hi[z]:choices.append(((low-lo[z])/max(width,1),z,low,False))
        if lo[z]<high<hi[z]:choices.append(((hi[z]-high)/max(width,1),z,high,True))
    if not choices:return None
    # The score only chooses among exact sound boundary splits.
    _,axis,cut,inside_upper=max(choices)
    return axis,cut,inside_upper

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=3000)
    ap.add_argument('--output',type=Path,default=HERE/'hybrid-phase-pilot.json')
    ap.add_argument('--certificate',type=Path,default=HERE/'analytic_gram_minorant.json')
    ap.add_argument('--replay',type=Path,default=HERE/'analytic_gram_replay.json')
    ap.add_argument('--initial-basin-index',type=int,default=None,
                    help='Research control: deliberately carve this one basin from the root before LP guidance.')
    ap.add_argument('--anchor-guidance',action='store_true',help='Choose any exact rational basin anchor still in a failed cell.')
    ap.add_argument('--finish-carved-basin',action='store_true',help='Finish an active basin carve even if an intermediate affine leaf could already close.')
    args=ap.parse_args();started=time.monotonic()
    inputs={str(p.resolve().relative_to(ROOT)):sha(p) for p in [args.certificate,args.replay,g.PAR,
        OLD/'generate.py',OLD/'ordered_generate.py',OLD/'compact_thin.py',OLD/'tree_flow.py',
        OLD/'independent_integer_audit.py',HERE/'prune_floor_probe.py']}
    basins=load_basins(args.certificate,args.replay)
    initial=next((b['key'] for b in basins.values() if b['index']==args.initial_basin_index),None)
    assert args.initial_basin_index is None or initial is not None
    todo=[{'path':'r','state':g.root(),'basin_key':initial}];accepted=[];branches=[]
    counters={'numeric':0,'basin':0,'empty':0,'reflection':0,'phase_split':0,'heuristic_split':0,
              'basin_hint_selected':0,'basin_hint_point_in_region':0,'basin_hint_missed':0,'anchor_hint_selected':0}
    done=0
    def save():
        report={'scope':__doc__,'input_sha256':inputs,'script_sha256':sha(Path(__file__)),
            'checked':done,'accepted':len(accepted),'unresolved':len(todo),'branches':len(branches),
            'counters':counters,'basins_used':sorted({r['basin_index'] for r in accepted if r['kind']=='basin'}),
            'root':g.root(),'target':'433/50000','denominator':str(g.DEN),
            'initial_basin_index':args.initial_basin_index,
            'anchor_guidance':args.anchor_guidance,
            'finish_carved_basin':args.finish_carved_basin,
            'all_numeric_leaves_independently_integer_checked':True,
            'all_basin_inclusions_exact_integer_checked':True,
            'both_children_of_every_branch_retained':True,
            'all_input_hashes_unchanged':all(sha(ROOT/p)==v for p,v in inputs.items()),
            'global_cover_complete':not todo,'generic_basin_real_soundness_formalized':False,
            'new_unconditional_zeta_bound_proven':False,'seconds':time.monotonic()-started}
        assert report['all_input_hashes_unchanged']
        args.output.write_text(json.dumps({'stats':report,'branches':branches,'accepted':accepted,'unresolved':todo},separators=(',',':'))+'\n',encoding='utf8')
        return report
    while todo and done<args.max_nodes:
        item=todo.pop();path=item['path'];state,cuts=ordered.normalize(item['state']);done+=1
        bad=next((z for z,(l,u) in enumerate(zip(*state)) if u<l),None)
        if bad is not None:
            counters['empty']+=1;accepted.append({'path':path,'normalize_cuts':cuts,'kind':'empty','axis':bad});continue
        if state[1][8]<state[0][0]:
            counters['reflection']+=1;accepted.append({'path':path,'normalize_cuts':cuts,'kind':'reflection'});continue
        active=basins.get(tuple(item['basin_key'])) if item['basin_key'] is not None else None
        whole=active if active and contained(state,active) else next((b for b in basins.values() if contained(state,b)),None)
        if whole:
            assert all(low<=state[0][z] and state[1][z]<=high for z,low,high in whole['bounds'])
            counters['basin']+=1;accepted.append({'path':path,'normalize_cuts':cuts,'kind':'basin',
                'basin_index':whole['index'],'integer_gaps':whole['key'],'state':state,
                'Gram_lower_bound_exact':whole['Gram_lower_bound_exact']});continue
        rec=g.certify(state,True)
        if (not active or not args.finish_carved_basin) and int(rec.get('floor_numerator','-1'))>=g.TARGET:
            independently_check(state,rec);counters['numeric']+=1
            exact={k:rec[k] for k in ['FS','multiplier','floor_numerator','mcheck_numerator']}
            exact['certificate']={'lower_bounds':state[0],'upper_bounds':state[1]}
            accepted.append({'path':path,'normalize_cuts':cuts,'kind':'numeric','result':exact});continue
        if not active:
            point=rec.get('gaps')
            key=tuple(round(x) for x in point) if point else ()
            active=basins.get(key)
            if active:
                counters['basin_hint_selected']+=1
                if all(low<=sum(point[i:j])*g.SC<=high for (i,j,a),(z,low,high) in zip(g.TERMS,active['bounds'])):
                    counters['basin_hint_point_in_region']+=1
                else:active=None;counters['basin_hint_missed']+=1
            if not active and args.anchor_guidance:
                available=[b for b in basins.values() if anchor_contained(state,b)]
                if available:
                    active=min(available,key=lambda b:sum((n/b['anchor_denominator']-x)**2 for n,x in zip(b['anchor_numerators'],point)))
                    assert anchor_contained(state,active)
                    counters['anchor_hint_selected']+=1
        carve=carve_cut(state,active) if active else None
        if carve:
            axis,cut,inside_upper=carve;counters['phase_split']+=1
            inside_bit='0' if inside_upper else '1';outside_bit='1' if inside_upper else '0'
            # DFS visits the inside branch first; its complement remains pending.
            child_specs=[(outside_bit,not inside_upper,None),(inside_bit,inside_upper,active['key'])]
        else:
            axis,cut=g.cut(state,rec);counters['heuristic_split']+=1
            child_specs=[('1',False,None),('0',True,None)]
        assert state[0][axis]<cut<state[1][axis]
        branches.append({'path':path,'axis':axis,'cut':cut,'normalize_cuts':cuts,'phase_basin_index':active['index'] if carve else None})
        for bit,upper,key in child_specs:
            todo.append({'path':path+bit,'state':ordered.rawsplit(state,axis,cut,upper),'basin_key':key})
        if done%100==0:print(json.dumps({'checked':done,'accepted':len(accepted),'pending':len(todo),**counters,'seconds':time.monotonic()-started}),flush=True)
        if done%500==0:save()
    report=save();print(json.dumps({k:v for k,v in report.items() if k!='root'}),flush=True)
if __name__=='__main__':main()
