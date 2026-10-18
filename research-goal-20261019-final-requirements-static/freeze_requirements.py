"""Freeze a static requirements map; no live Linux, proof or network access."""
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}

def write(name,obj):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')

def main():
    assert not (HERE/'requirements-map.json').exists() and not (HERE/'files.json').exists()
    refs=[ROOT/'AGENTS.md',ROOT/'research-goal-20261016/DIRECTION.zh.md',
      ROOT/'research-goal-20261016/macro-reviews/006-20261018.zh.md',
      ROOT/'research-goal-20261019-tiny-kernel-evidence/checks.json',
      ROOT/'research-goal-20261019-tiny-kernel-evidence/files.json',
      ROOT/'research-goal-20261019-tiny-flatten-preparation-v4/prepared-files.json',
      ROOT/'research-goal-20261019-tiny-production-preparation-v2/prepared-files.json',
      ROOT/'research-goal-20261019-tiny-production-preparation-v2/run_production.py',
      ROOT/'submission/single-exception-overlap-20261019/files.json']
    before=[row(p) for p in refs]
    assert sha(refs[2])=='7dacb03bef8fdbbb90fb6c95e5b843e55602c7dbd106b35be7c585160b704c76'
    checks=json.loads(refs[3].read_text(encoding='utf-8'))
    assert checks['full_cold3200s_passed'] is False
    assert checks['independent_complete_nanoda_passed'] is True
    assert checks['source']['sha256']=='024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
    write('requirements-map.json',{
      'schema':'final-delivery-requirements-static-map-v1',
      'prepared_at_utc':datetime.now(timezone.utc).isoformat(),
      'is_macro_review':False,'counter_changed':False,
      'root_instruction_status_snapshot':{'main_round':3,'v4_session':84529,'v4_status':'still running; no live artifact read here'},
      'human_goal':{'nontrivial_unconditional_strict_record_improvement':True,
        'minimum_gain_of_one_millionth_still_required':False,
        'submission_materials_required':True,'official_acceptance_added_as_completion_condition':False},
      'retained_delivery_evidence_requirements':['actual kernel and global argument',
        'dyadic and cumulative distinct-zero statements','fresh exact strict gain/provenance',
        'three permitted axioms','ordinary Lean/Comparator/default kernel/nanoda',
        'actual one UTF-8 source <=2MB','single generation-through-fsynced-receipt <=3200s',
        'GitHub final bytes match','usable final submission materials'],
      'supported_now':{'v3_math_and_all_individual_replayers':True,
        'v3_total3200_passed':False,'v4_text_equivalence_only_static':True},
      'not_yet_supported_at_this_snapshot':['v4 actual complete84529 terminal proof',
        'v4 final material collection','final selected bytes GitHub/public consistency'],
      'current_completion_claim_permitted':False,
      'website_acceptance_status':'pending/unconfirmed; report honestly, do not make it an extra gate',
      'if_current_record_equals_our_kappa':'Bind trusted accepted own job/source provenance and prior baseline; do not demand kappa>itself',
      'if_equal_record_is_external_or_unattributed':'Do not claim strict latest-record improvement; root reassesses',
      'historical_read_provenance':before,
      'mutable_governance_not_runtime_dependencies':True,
      'live_Linux_reads_compilers_experiments_network_runs':0})
    assert before==[row(p) for p in refs]
    write('files.json',{'schema':'final-requirements-static-files-v1',
      'files':[row(HERE/'REQUIREMENTS.zh.md'),row(HERE/'freeze_requirements.py'),row(HERE/'requirements-map.json')],
      'scope':'Static final requirement/status mapping only; not a completion or execution authorization',
      'external_refs_are_historical_read_provenance_not_mutable_pins':True})
    print(json.dumps({'manifest_sha256':sha(HERE/'files.json'),'completion_claimed':False}))

if __name__=='__main__':main()
