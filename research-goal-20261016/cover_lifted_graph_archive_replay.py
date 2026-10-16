"""Standalone stdlib replay of ancestor-only lifted-graph Farkas archives."""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_lifted_graph_verify as checker_api
import cover_compact_codec as codec
import cover_sublevel_obbt_verify as obbt
import cover_contractor_verify as newton
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path,default=HERE/'cover-lifted-graph8-evidence');args=ap.parse_args();start=time.monotonic()
    manifest_raw=(args.archive/'manifest.json').read_bytes();manifest=json.loads(manifest_raw);packed=(args.archive/'proof.json.gz').read_bytes()
    assert sha(packed)==manifest['proof_gzip_sha256'] and len(packed)==manifest['proof_gzip_bytes'];raw=gzip.decompress(packed)
    assert sha(raw)==manifest['uncompressed_sha256'] and len(raw)==manifest['uncompressed_bytes'];doc=json.loads(raw);assert doc['schema']=='lifted-graph-ancestor-projection-v1'
    source=doc['source'];params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();params=json.loads(params_raw)
    for name,digest in source['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    tabraw=(HERE/'cover_newjet.json').read_bytes();table=json.loads(tabraw);assert table['receipt']['parameter_sha256']==sha(params_raw)
    checker=checker_api.GraphReplay(table);target=F(doc['target'])*obbt.shared.g.DEN;assert target.denominator==1;target=target.numerator
    records={r['path']:r for r in doc['records']};assert len(records)==manifest['witnesses']
    assert not any(p!=q and p.startswith(q) for p in records for q in records)
    before,counts=checker_api.reconstruct(source,records,params,checker,target);details=[];controls={r['path']:r['control'] for r in doc['paired_controls']}
    assert set(records)==set(controls);cases={r['path']:r for r in source['cases']};savings={k:0 for k in source['cases'][0]['recorded_old_work']};control_bounds=control_steps=0
    for path,row in records.items():
        assert row['baseline'] is None and row['graph']
        details.append({'path':path,**checker_api.verify(before[path],row['graph'],params,checker)})
        state=before[path];control=controls[path];assert control['outcome'] is None
        if control['OBBT']:
            step=codec.unpack_obbt(state,control['OBBT'],target,obbt.shared.w);obbt.verify({**step,'result':None},target,checker.scalar)
            state=step['new_cell'];control_bounds+=len(step['certificates'])
        for packedstep in control['Newton']:
            step=codec.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);control_steps+=1
        assert state is not None and codec.digest(state)==control['final_state_sha256'];b=control['branch'];assert state[0][b['axis']]<b['cut']<state[1][b['axis']]
        branch_count=sum(r['path'].startswith(path) for r in doc['source_recorded_descendant_branches']);assert branch_count==cases[path]['recorded_old_work']['branches']
        for k,v in cases[path]['recorded_old_work'].items():savings[k]+=v
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'archive_manifest_sha256':sha(manifest_raw),'all_passed':True,
      'witnesses':len(records),'ancestor_counts':counts,'paired_nonclosing_controls':len(controls),'control_OBBT_bounds':control_bounds,'control_Newton_steps':control_steps,
      'independently_recomputed_derivative_grid_cells':len(checker.checked_grid),'strict_certificates':details,
      'source_recorded_descendant_work':savings,'descendant_counts_are_source_projection_metrics':True,
      'requires_full_parent64_snapshot':False,'requires_original_large_checkpoint':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (args.archive/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
