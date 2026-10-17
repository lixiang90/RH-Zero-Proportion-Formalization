"""Freeze the static removable-pole review; never compile or run a solver."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def row(path):
    raw = path.read_bytes()
    return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(raw),
            'sha256':hashlib.sha256(raw).hexdigest()}


def frozen_write(path,value):
    raw = (json.dumps(value,indent=2,ensure_ascii=False,allow_nan=False)+'\n').encode('utf8')
    if path.exists():
        assert path.read_bytes()==raw, 'Frozen output differs; use a new path.'
    else:
        path.write_bytes(raw)


def main():
    sources = [
        ('StructuralGoal20261016/WindowKernel.lean',
         ['K_eq_sinc','K_zero','K_zero_pos','k','d24']),
        ('StructuralGoal20261016/WindowEnergy.lean',['v','integral_v']),
        ('StructuralGoal20261016/WindowSincJet.lean',
         ['sincMoment_zero_order','sincMoment_at_zero','iterated_k_eq_finiteJet']),
        ('StructuralGoal20261016/WindowGramExpansion.lean',
         ['actual_energy_expansion','weight_nonneg']),
        ('StructuralGoal20261016/WindowGlobalCompetitor.lean',
         ['swapGap_feasible','swap_energy_le','upper_change_nonneg']),
        ('StructuralW10Followup20261016/NewWindows.lean',['nums24','c24']),
        ('StructuralW10Followup20261016/NewLedger.lean',['aN','bN']),
        ('formal/upstream/ajp88-reweighted-nine-point.lean',
         ['AMW.KMT','AMW.term_closed','AMW.KMT_eq_gamma'])]
    receipts = json.loads((ROOT/'research-goal-20261016/lean_verification.json').read_bytes())
    known = {r['module']:r for r in receipts['modules']}
    actual = []
    for path,keys in sources:
        item = row(ROOT/path)
        item['relevant_definitions_or_theorems'] = keys
        module = path[:-5].replace('/','.')
        if module in known:
            r = known[module]
            assert r['passed'] and r['source_sha256']==item['sha256']
            log = ROOT/'research-goal-20261016'/r['log']
            assert row(log)['sha256']==r['log_sha256']
            item.update(current_ordinary_module_passed=True,ordinary_log=row(log))
        actual.append(item)
    reviewed = [
        'window_phase_hermitian_audit.txt','window_phase_hermitian_diagnostic.py',
        'window_phase_hermitian_diagnostic.json','window_joint_cycle_projection_note.txt',
        'window_joint_cycle_projection_audit.txt','window_joint_cycle_projection_probe.py',
        'window_phase_obstruction_and_PSD_weight_route.txt',
        'cover_phase_kkt_diagnostic.md','cover_phase_kkt_probe.py',
        'cover_phase_kkt_graph_probe.py','window_phase_coefficients.py']
    prior = [row(ROOT/'research-goal-20261016'/p) for p in reviewed]
    symbolic = json.loads((HERE/'symbolic-identity-audit.json').read_bytes())
    assert symbolic['all_cross_multiplied_polynomials_exactly_zero']
    assert symbolic['source_sha256']==row(HERE/'local_phase_symbolic.py')['sha256']
    ledger = (ROOT/'StructuralW10Followup20261016/NewLedger.lean').read_text(encoding='utf8')
    block = ledger.split('def aN',1)[1].split('def bN',1)[0]
    weights = {(int(i),int(j)):F(int(a),10**10)
               for i,j,a in re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)',block)}
    g = [F(1)]*9
    g[6],g[7] = F(65,32),F(31,32)
    assert min(g)>F(123,128)
    triangles = [(6,7,2),(7,8,1),(6,8,3)]
    fixed = []
    for i,j,n in triangles:
        x = sum(g[i:j]);delta = x-n
        assert abs(delta)<=F(1,4) and weights[i,j]>0
        fixed.append({'edge':[i,j],'weight':str(weights[i,j]),'span':str(x),
                      'integer_label':n,'delta':str(delta),
                      'raw_cosine_sign':1 if n%2==0 else -1})
    out = {'scope':__doc__,'actual_identity_sources':actual,'prior_work_reviewed':prior,
           'fixed_pilot_design_only':{'gaps':list(map(str,g)),'triangle':[6,7,8],
               'all_gaps_strictly_above_sep':True,'edges':fixed,
               'band':['abs(g6-2)<=1/32','abs(g7-1)<=1/32','abs(g6+g7-3)<=1/32'],
               'pilot_executed':False,'solver_calls':0},
           'novelty_assessment':'The regular sinc/cos form is algebraically identical to the previous local phase audit; only a demonstrated joint phase-position/rank constraint or reduced uniform payment could strengthen a relaxation.',
           'all_new_actual_coefficients_rational_numbers':False,
           'coefficients_are_rational_functions_with_fixed_actual_real_constants':True,
           'symbolic_audit':row(HERE/'symbolic-identity-audit.json'),
           'new_point_evaluations':0,'new_Lean_invocations':0,'solver_calls':0,
           'new_actual_kernel_identity_Lean_proven':False,'new_exclusion':False,
           'new_global_cover':False,'new_zero_proportion_proven':False}
    deps = HERE/'identity-dependencies.json'
    frozen_write(deps,out)
    files = [row(p) for p in [HERE/'DERIVATION.md',HERE/'local_phase_symbolic.py',
                              HERE/'symbolic-identity-audit.json',Path(__file__),deps]]
    pin = HERE/'local-phase-files.json'
    frozen_write(pin,{'scope':'Static local regular phase derivation and exact symbolic rational algebra audit; one fixed pilot design, no pilot run.',
                      'files':files,'dependency_index':row(deps),
                      'new_Lean_invocations':0,'solver_calls':0,'new_point_evaluations':0,
                      'new_math_lower_bound':False,'new_exclusion':False,
                      'new_zero_proportion_proven':False})
    print(json.dumps({'pin':row(pin),'files':len(files),'bytes':sum(x['bytes'] for x in files),
                      'actual_source_dependencies':len(actual),'prior_work_dependencies':len(prior)}))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
