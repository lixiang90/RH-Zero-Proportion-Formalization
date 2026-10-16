"""Standalone stdlib replay of the stopped six-case single-midpoint batch.

Reconstruct all required ancestors and check actual midpoint interval
inputs, complete-span second-derivative lower bounds and energy-row algebra.
Point transcendental evaluation deliberately reruns the shared provider
kernel helper. Floating zero-slack LPs remain inconclusive hints; there are
no strict certificates or exact moment-primal feasibility claims here.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_cross_moment_old_rows_replay as support
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    start=time.monotonic();folder=HERE/'cover-cross-moment-remaining-evidence'
    packed=(folder/'proof.json.gz').read_bytes();manifest=json.loads((folder/'manifest.json').read_bytes());raw=gzip.decompress(packed)
    assert sha(packed)==manifest['proof_gzip_sha256'] and sha(raw)==manifest['uncompressed_sha256']
    doc=json.loads(raw);assert doc['schema']=='cross-moment-single-midpoint-negative-six-v1' and len(doc['records'])==6
    text=json.dumps({'receipt':doc['receipt'],'rows':doc['records']},separators=(',',':'))
    candidates=[(text+ending).encode() for ending in ['\n','\r\n']]
    recovered=next(b for b in candidates if sha(b)==manifest['source_batch_sha256'])
    assert sha(recovered)==doc['provenance']['full_batch_sha256']
    source=doc['source'];assert source['target']=='11/1250'
    for name,digest in doc['receipt']['source_guards'].items():assert sha((HERE/name).read_bytes())==digest,name
    for name,digest in source['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();params=json.loads(params_raw)
    table_raw=(HERE/'cover_newjet.json').read_bytes();checker=support.graph.GraphReplay(json.loads(table_raw))
    second=support.curvature.CurvatureReplay(checker.scalar)
    wanted={r['path'] for r in doc['records']};assert len(wanted)==6
    assert wanted=={'r001000001000100110011001','r001000001000100110110110','r001000001000100111100011',
      'r001000001000100111101110','r001000001000100111111111','r001000001000101011110111'}
    target=F(source['target'])*support.graph.energy.g.DEN;assert target.denominator==1
    states,ancestor_counts=support.graph.reconstruct(source,wanted,params,checker,target.numerator)
    print(json.dumps({'stage':'six_path_ancestor_replay','counts':ancestor_counts,'seconds':time.monotonic()-start}),flush=True)
    rows=[]
    for row in doc['records']:
        state=states[row['path']];assert state==row['cell'] and len(row['energy_packets'])==1
        packet=row['energy_packets'][0];prefix=[F(0)]+[F(state[0][support.graph.a.INDEX[0,j]]+state[1][support.graph.a.INDEX[0,j]],2*support.SC) for j in range(1,10)]
        assert list(map(F,packet['centre']))==[prefix[j+1]-prefix[j] for j in range(9)]
        point_check=support.point_intervals(packet,params);energy_check=support.energy_audit.verify_packet(state,packet,params,second)
        assert row['position_PSD_cut_rounds']==row['sample_points_evaluated']==0
        assert row['integer_certificate'] is None and not row['integer_attempts']
        assert row['dual_hint']['LP_success'] and row['dual_hint']['minimum_energy_slack_hint']==0
        assert not row['base_result']['integer_PSD_cut_vectors'] and len(row['base_result']['history'])==1
        rows.append({'path':row['path'],'all_point_and_packet_checks_passed':True,'energy_packets':1,
          'point_interval_checks':point_check,'energy_row_checks':energy_check,
          'floating_energy_slack_hint':0,'strict_exclusions':0,'exact_LP_primal_feasibility_verified':False})
        print(json.dumps({'stage':'single_midpoint_packet_replayed','path':row['path'],'seconds':time.monotonic()-start}),flush=True)
    assert not any(name in sys.modules for name in ['numpy','scipy','networkx'])
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'archive_sha256':sha(packed),
      'archive_manifest_sha256':sha((folder/'manifest.json').read_bytes()),'parameters_sha256':sha(params_raw),'table_sha256':sha(table_raw),
      'recovered_full_batch_sha256':sha(recovered),'full_batch_recovered_byte_identical':True,
      'dependency_sources_sha256':support.dependency_hashes(),'all_supply_and_ancestor_checks_passed':True,'cases':rows,
      'ancestor_counts':ancestor_counts,'independent_derivative_grid_cells':len(checker.checked_grid),
      'no_site_packages':sys.flags.no_site,'no_optimization_packages_imported':True,
      'point_intervals_use_shared_provider_kernel_helper':True,'implementation_independent_point_transcendental_audit':False,
      'exact_LP_primal_feasibility_verified':False,'new_strict_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=folder/'independent-replay.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'all_supply_and_ancestor_checks_passed':True,'cases':len(rows),'seconds':out['seconds'],'receipt_sha256':sha(p.read_bytes())}),flush=True)
if __name__=='__main__':main()
