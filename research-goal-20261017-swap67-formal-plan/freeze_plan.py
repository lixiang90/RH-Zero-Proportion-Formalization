"""Freeze the static actual-interface plan and its one finite M5 audit.

This reads current proof receipts; it runs no Lean, numerical model or solver.
Existing package output bytes must match exactly and are never overwritten.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODULES = [
    'WindowGlobalCompetitor', 'WindowMinimizerCover', 'WindowGapEnergy',
    'WindowGramExpansion', 'WindowValueFlow', 'WindowScalarLine', 'WindowDifferenceCell',
    'WindowConvexityCertificate', 'WindowTaylorBridge', 'WindowScalarMinorant',
    'WindowRationalInterval', 'WindowPointTableArithmetic', 'WindowDerivativeTableArithmetic',
    'WindowFixedPolynomial', 'WindowFixedInterval', 'WindowFixedDerivative',
    'WindowFixedHornerChoice', 'WindowCellDerivative', 'WindowRawCoefficientData',
    'WindowRawCoefficients', 'WindowJetTableData', 'WindowFixedTablesAll',
    'WindowDerivativeAffineOracle', 'WindowGridRange']


def row(path):
    raw = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(raw),
            'sha256': hashlib.sha256(raw).hexdigest()}


def frozen_write(path, value):
    raw = (json.dumps(value,indent=2,ensure_ascii=False,allow_nan=False)+'\n').encode('utf8')
    if path.exists():
        assert path.read_bytes()==raw, 'Frozen output differs; choose a new output path.'
    else:
        path.write_bytes(raw)


def main():
    canonical = json.loads((ROOT/'research-goal-20261016/lean_verification.json').read_bytes())
    records = {r['module']:r for r in canonical['modules']}
    dependencies = []
    for name in MODULES:
        module = 'StructuralGoal20261016.'+name
        source = ROOT/'StructuralGoal20261016'/(name+'.lean')
        r = records[module]
        entry = row(source)
        assert r['passed'] and r['exit_code']==0 and r['source_sha256']==entry['sha256'],module
        log = ROOT/'research-goal-20261016'/r['log']
        assert row(log)['sha256']==r['log_sha256']
        entry.update(module=module,current_source_matches_passed_receipt=True,
                     ordinary_log=row(log),olean_sha256=r['olean_sha256'])
        dependencies.append(entry)
    packet = ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json'
    inputs = [packet,ROOT/'research-goal-20261016/window_normalized_interval.json',
              ROOT/'research-goal-20261016/cover_newjet.json',
              ROOT/'research-goal-20261016/window_global_competitor_formal_index.json']
    audit = json.loads((HERE/'m5-compatibility-audit.json').read_bytes())
    assert audit['static_cell_checks']==391 and audit['unique_anchor_points']==14
    assert audit['all_packet_M5_preserved_by_normalized_FI']
    assert audit['max_extra_FI_ticks_per_packet']==0 and audit['Lean_invocations']==0
    for name,expected in audit['source_sha256_start'].items():
        assert row(ROOT/name)['sha256']==expected
    out = {'scope':'Static actual hD bridge plan; exact current dependency sources and ordinary receipt bindings.',
           'dependencies':dependencies,'input_files':[row(p) for p in inputs],
           'compiler_sha256_of_reused_ordinary_proofs':canonical['compiler_sha256'],
           'static_audit':row(HERE/'m5-compatibility-audit.json'),
           'new_packet_Lean_invocations':0,'new_actual_quartic_hD_proven':False,
           'new_actual_cell_exclusion':False,'new_global_floor':False,'new_zero_proportion_proven':False}
    dep_path = HERE/'plan-dependencies.json'
    frozen_write(dep_path,out)
    files = [row(p) for p in [HERE/'PLAN.md',HERE/'audit_m5_compatibility.py',
                              HERE/'m5-compatibility-audit.json',Path(__file__),dep_path]]
    pin = HERE/'formal-plan-files.json'
    frozen_write(pin,{'scope':'Frozen static plan plus one authorized 391-cell normalized-W M5 compatibility audit.',
                      'files':files,'external_dependency_index':row(dep_path),
                      'new_Lean_invocations':0,'solver_calls':0,'old_producer_executed':False,
                      'source_files_modified_outside_new_package':0,
                      'new_actual_quartic_hD_proven':False,'new_actual_cell_exclusion':False,
                      'new_zero_proportion_proven':False})
    print(json.dumps({'pin':row(pin),'retained_files':len(files),
                      'retained_bytes':sum(x['bytes'] for x in files),
                      'reused_current_passed_modules':len(dependencies),
                      'static_M5_receipt':row(HERE/'m5-compatibility-audit.json')}))


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    main()
