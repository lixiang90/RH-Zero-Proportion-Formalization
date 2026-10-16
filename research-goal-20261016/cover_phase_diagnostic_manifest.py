"""Freeze separate stopped strong-phase and actual-gradient diagnostics."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def row(path):
    p=ROOT/path;b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':sha(b)}


def freeze(names,out,scope,dependencies):
    files=[row('research-goal-20261016/'+n) for n in names]
    document={'scope':scope,'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files),
      'external_frozen_dependencies':[row(p) for p in dependencies],
      'new_strict_cell_exclusions':0,'PSD_feasible_primal_verified':False,'origin_in_actual_gradient_hull_proven':False,
      'complete_global_cover':False,'new_unconditional_zero_proportion_proven':False,'submission_ready':False}
    path=HERE/out;path.write_text(json.dumps(document,indent=2)+'\n',encoding='utf8');print(json.dumps({'manifest':path.relative_to(ROOT).as_posix(),'sha256':sha(path.read_bytes()),'files':len(files),'bytes':document['total_bytes']}),flush=True)


def main():
    variants=['case0','case1','graph-case0','graph-case1']
    for name in variants:
        packed=(HERE/f'cover-phase-kkt-{name}.json.gz').read_bytes();raw=gzip.decompress(packed)
        receipt=json.loads((HERE/f'cover-phase-kkt-{name}-cut-replay.json').read_bytes())
        assert receipt['input_sha256']==sha(raw) and receipt['input_archive_sha256']==sha(packed) and receipt['all_constraint_ingredient_checks_passed']
        assert receipt['script_sha256']==sha((HERE/'cover_phase_kkt_cut_replay.py').read_bytes())
    common=['research-goal-20261016/cover-curvature-parent64.input.json.gz',
      'research-goal-20261016/cover_newjet.json','research-20261016-followup/window_reweight_rational.json']
    strong=['cover_phase_kkt_probe.py','cover_phase_kkt_graph_probe.py','cover_phase_kkt_cut_replay.py',
      'cover_phase_kkt_diagnostic.md','cover_phase_diagnostic_manifest.py']
    strong += [f'cover-phase-kkt-{n}.json.gz' for n in variants]+[f'cover-phase-kkt-{n}-cut-replay.json' for n in variants]
    freeze(strong,'cover-phase-kkt-files.json','Stopped two-cell shared-phase KKT models: 20 finite PSD-cut rounds, inconclusive outer LP; exact arithmetic ingredient replay only.',
      common+['research-goal-20261016/window-phase-uniform-progress-files.json',
      'research-goal-20261016/cover_lifted_graph_probe.py','research-goal-20261016/cover_phase_psd_obstruction.py'])
    gradient=['cover_gradient_mixture_probe.py','cover_gradient_mixture_direction_probe.py','cover_gradient_mixture_replay.py',
      'cover-gradient-mixture.json','cover-gradient-mixture-direction.json','cover-gradient-mixture-replay.json',
      'cover_gradient_mixture_diagnostic.md','cover_phase_diagnostic_manifest.py']
    receipt=json.loads((HERE/'cover-gradient-mixture-replay.json').read_bytes());assert receipt['passed']
    assert receipt['script_sha256']==sha((HERE/'cover_gradient_mixture_replay.py').read_bytes())
    freeze(gradient,'cover-gradient-mixture-files.json','Stopped two-cell finite actual-gradient diagnosis: 256 exact-feasible points, no origin-in-hull witness and no whole-cell exclusion.',
      common+['research-goal-20261016/cover_phase_psd_obstruction.py',
      'research-goal-20261016/window_interval_kernel.py',
      'research-20261016-followup/global_periodic_upper_bound.py',
      'research-goal-20261016/cover_correlated_direction.py',
      'research-goal-20261016/cover_correlated_replay.py',
      'research-20261016-w10-cert/independent_integer_audit.py'])
if __name__=='__main__':main()
