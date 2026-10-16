"""Freeze the explicitly bounded KKT projection/variance/Bregman package."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).parent;ROOT=HERE.parent
NAMES=['window_kkt_projection_variance_note.txt',
    'cover_residual_psd_pilot.py','cover-residual-psd-pilot.json',
    'cover_residual_psd_replay.py','cover-residual-psd-replay.json',
    'cover_reverse_taylor_pilot.py','cover-reverse-taylor-pilot.json',
    'cover_bregman_primal_check.py','cover-bregman-primal-check.json',
    'cover_bregman_energy_pilot.py','cover-bregman-energy-pilot.json',
    'cover_bregman_closed_primal_check.py','cover-bregman-closed-primal-check.json',
    'cover_bregman_closed_energy_pilot.py','cover-bregman-closed-energy-pilot.json',
    'cover_bregman_coupling_replay.py','cover-bregman-coupling-replay.json',
    'window_kkt_projection_variance_manifest.py']

def digest(path):
    data=path.read_bytes();return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

def main():
    result=[]
    for n in ['cover-residual-psd-pilot.json','cover-reverse-taylor-pilot.json','cover-bregman-energy-pilot.json','cover-bregman-closed-energy-pilot.json']:
        data=json.loads((HERE/n).read_text());assert data['phase']=='completed_bounded_pilot' and data['all_inputs_unchanged']
        lp=data['rounds'] if 'rounds' in data else [data['LP']];assert all(r['success'] for r in lp)
        vals=[r.get('energy_slack_hint',r.get('minimum_energy_slack_hint')) for r in lp];assert vals and all(v==0 for v in vals)
        assert data['strict_integer_certificate'] is None
        result.append({'file':n,'LP_calls':len(lp),'energy_slack_hints':vals,'new_exclusions':0})
    for n in ['cover-residual-psd-replay.json','cover-bregman-coupling-replay.json']:
        data=json.loads((HERE/n).read_text());assert data['passed'] and data['all_inputs_unchanged']
        for name,value in data['input_sha256_end'].items():
            p=HERE/name
            if not p.exists():p=ROOT/'research-20261016-followup'/name
            assert hashlib.sha256(p.read_bytes()).hexdigest()==value
    frozen=['cover-cross-moment-remaining-six.json','cover_cross_moment_probe.py','cover_lifted_graph_probe.py',
        'cover_cross_moment_exact_rows.py','cover_correlated_direction.py','cover_second_order.py','cover_newjet.json']
    out={'scope':__doc__,'schema':'kkt-projection-variance-bregman-bounded-v1','package_files':[digest(HERE/n) for n in NAMES],
        'frozen_input_files':[digest(HERE/n) for n in frozen]+[digest(ROOT/'research-20261016-followup/window_reweight_rational.json')],
        'cases':1,'path':'r001000001000100110011001','target':'11/1250','bounded_pilot_outcomes':result,
        'residual_cuts_exactly_replayed':32,'Bregman_reverse_closed_rows_exactly_replayed':4,
        'new_actual_Lean_exclusions':0,'new_integer_Farkas_exclusions':0,
        'actual_Bregman_semantic_bridge_verified_by_this_package':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False,
        'stopped_at_authorized_bounded_budget':True}
    p=HERE/'window-kkt-projection-variance-files.json';assert not p.exists()
    p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'files':len(NAMES),'manifest_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'all_bounded_pilots_zero_slack':True}),flush=True)

if __name__=='__main__':main()
