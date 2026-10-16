"""Standalone python -S replay of the strict two-child graph disjunction."""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_exact_scalar_replay as scalar_adapter
scalar_adapter.install()
import cover_lifted_graph_verify as graph
import cover_compact_codec as codec
import cover_sublevel_obbt_verify as obbt
import cover_contractor_verify as newton
HERE=Path(__file__).parent;ROOT=HERE.parent;a=graph.a
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    start=time.monotonic();folder=HERE/'cover-lifted-disjunction-evidence';mr=(folder/'manifest.json').read_bytes();manifest=json.loads(mr);packed=(folder/'proof.json.gz').read_bytes();assert sha(packed)==manifest['proof_gzip_sha256']
    raw=gzip.decompress(packed);assert sha(raw)==manifest['uncompressed_sha256'];doc=json.loads(raw);assert doc['schema']=='lifted-graph-disjunction-projection-v1'
    source=doc['source'];params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    for name,digest in source['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    checker=graph.GraphReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));target=F(source['target'])*obbt.shared.g.DEN;assert target.denominator==1;target=target.numerator
    records={r['path']:r for r in doc['records']};before,counts=graph.reconstruct(source,records,params,checker,target);details=[];prior=doc['previous_graph_parent_paths'];controlbounds=controlsteps=0
    controls={r['path']:r['control'] for r in doc['controls']};assert set(controls)==set(records)
    for p,row in records.items():
        assert all(not p.startswith(q) and not q.startswith(p) for q in prior);axis,cut=row['axis'],row['cut'];parent=before[p];assert parent[0][axis]<cut<parent[1][axis]
        assert len(row['children'])==2
        for k,cert in enumerate(row['children']):
            child=a.child(parent,axis,cut,k==0);assert child is not None;details.append({'path':p,'child':k,**graph.verify(child,cert,params,checker)})
        control=controls[p];assert control['outcome'] is None;state=parent
        if control['OBBT']:
            step=codec.unpack_obbt(state,control['OBBT'],target,obbt.shared.w);obbt.verify({**step,'result':None},target,checker.scalar);state=step['new_cell'];controlbounds+=len(step['certificates'])
        for ps in control['Newton']:
            step=codec.unpack_newton(state,ps,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);controlsteps+=1
        assert state is not None and codec.digest(state)==control['final_state_sha256'];b=control['branch'];assert state[0][b['axis']]<b['cut']<state[1][b['axis']]
    assert not any(name in sys.modules for name in ['numpy','scipy','networkx'])
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'archive_manifest_sha256':sha(mr),'all_passed':True,'no_site_packages':sys.flags.no_site,
      'parent_closures':len(records),'split_nodes':len(records),'strict_graph_leaves':len(details),'ancestor_counts':counts,'paired_nonclosing_controls':len(controls),
      'control_OBBT_bounds':controlbounds,'control_Newton_steps':controlsteps,'disjoint_from_original13_parent_paths':True,'strict_certificates':details,
      'requires_full_parent64_snapshot':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
