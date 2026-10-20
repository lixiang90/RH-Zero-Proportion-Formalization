"""Freeze two existing StateAt endpoint proof repairs; text/hash only."""
from datetime import datetime, timezone
import difflib
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REL = 'StructuralW9A220261020/Final.lean'
JOB = ROOT / 'tmp/w9a2-20261020/candidate-ordinary-v4'
OLD = '''    · simpa only [StructuralW9A220261020.Counting.leftGaps,
        StructuralW9A220261020.Graph.leftGaps] using hs
    · simpa only [StructuralW9A220261020.Counting.rightGaps,
        StructuralW9A220261020.Graph.rightGaps] using ht
'''.encode()
NEW = '''    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.leftGaps g) s
      exact hs
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.rightGaps g) t
      exact ht
'''.encode()
SEEN = {}


def sha(raw): return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes();key = path.resolve().relative_to(ROOT.resolve()).as_posix()
    val = {'path':key,'bytes':len(raw),'sha256':sha(raw)}
    assert SEEN.setdefault(key,val) == val,key
    return raw


def write(path,raw):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as stream:stream.write(raw)


def dump(obj):return (json.dumps(obj,ensure_ascii=False,indent=2)+'\n').encode()


def main():
    original = read(ROOT/REL)
    assert len(original)==5512 and sha(original)=='9f9cb13f409ac82ddb1a00ca99d27c98921633b999b82da38cdbd00ea21f5c85'
    assert original.count(OLD)==1 and NEW not in original
    repaired=original.replace(OLD,NEW)
    assert repaired.count(NEW)==1 and repaired.replace(NEW,OLD)==original
    assert len(original[:original.index(OLD)].splitlines())+1==69
    assert original[:original.index(OLD)]==repaired[:repaired.index(NEW)]
    assert original[original.index(OLD)+len(OLD):]==repaired[repaired.index(NEW)+len(NEW):]
    types=[]
    for name in ['actual_summed','strict_improvement','actual_dyadic','actual_cumulative']:
        pattern=rb'(?ms)^theorem '+name.encode()+rb'\s*:\s*(.*?) := by\n'
        before,after=re.findall(pattern,original),re.findall(pattern,repaired)
        assert len(before)==1 and before==after
        types.append({'name':name,'unchanged_type_sha256':sha(before[0])})
    graph=read(ROOT/'research-goal-20261020-w9a2-graph-repair-v2/StructuralW9A220261020/Graph.lean')
    counting=read(ROOT/'StructuralW9A220261020/Counting.lean')
    defs=[]
    for name in ['leftGaps','rightGaps']:
        pattern=rb'(?m)^def '+name.encode()+rb'[^\n]*\r?\n[^\n]*'
        a,b=re.findall(pattern,graph),re.findall(pattern,counting)
        assert len(a)==len(b)==1 and b''.join(a[0].split())==b''.join(b[0].split())
        defs.append({'name':name,'Graph_exact_definition':a[0].decode(),
            'Counting_exact_definition':b[0].decode(),'equal_mod_whitespace':True,
            'normalized_definition_sha256':sha(b''.join(a[0].split()))})
    for name in ['Core','Graph','Localization']:
        read(ROOT/('StructuralW9A220261020/'+name+'.lean'))
    read(ROOT/'research-goal-20261020-w9a2-localization-repair-v1/StructuralW9A220261020/Localization.lean')
    names=['started.json','terminal.json']+[f'StructuralW9A220261020_{m}.{s}'
        for m in ['Localization','Counting','Final']for s in ['command.json','child.json','log','receipt.json']]
    evidence={name:read(JOB/name)for name in names}
    failure=json.loads(evidence['StructuralW9A220261020_Final.receipt.json'])
    log=evidence['StructuralW9A220261020_Final.log']
    errors=re.findall(rb'(?m)^.*:[0-9]+:[0-9]+: error:.*$',log)
    assert len(errors)==2 and b'Final.lean:69:6:'in errors[0] and b'Final.lean:71:6:'in errors[1]
    assert failure['exit_code']==1 and failure['elapsed_seconds']==18.5
    assert failure['source_sha256']==sha(original) and failure['source_unchanged'] is True
    assert failure['log_sha256']==sha(log)=='10841ebe99a2a69efbffeae50b698c93d4eba7c2ef6b1c07fee353c24563a4c9'
    assert failure['axiom_audit_passed'] is False and not failure['ordinary_compile_passed']
    rejected=[name for name,axs in failure['observed_axioms'].items()if 'sorryAx'in axs]
    assert rejected==['StructuralW9A220261020.Final.actual_summed','StructuralW9A220261020.Final.actual_dyadic','StructuralW9A220261020.Final.actual_cumulative']
    passes={name:json.loads(evidence[f'StructuralW9A220261020_{name}.receipt.json'])for name in ['Localization','Counting']}
    for name,receipt in passes.items():assert receipt['exit_code']==0 and receipt['ordinary_compile_passed'] is True
    assert passes['Counting']['axiom_audit_passed']is True and len(passes['Counting']['observed_axioms'])==5
    assert all(set(axs)<= {'propext','Classical.choice','Quot.sound'}for axs in passes['Counting']['observed_axioms'].values())
    start=json.loads(evidence['started.json']);terminal=json.loads(evidence['terminal.json'])
    assert start['gate_sha256']=='9ed847edf10614f5bada1791551ed2874771add9b5532d57bb8acfb365047ac4'
    assert terminal['passed']is False and terminal['modules_completed']==3
    before=list(SEEN.values())
    for item in before:read(ROOT/item['path'])
    report={'status':'PREPARED_PROOF_ONLY_REPAIR_NOT_COMPILED','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
        'failure':{'module':failure['module'],'gate_sha256':start['gate_sha256'],
            'root_observed_parent_session':90216,'root_observed_actual_parent_exit_code':1,
            'parent_exit_evidence_scope':'Explicit root task message reports the terminal tool handle; actual module receipt and ordinary terminal copied here.',
            'module_exit_code':1,'elapsed_seconds':18.5,'log_sha256':sha(log),
            'errors':[x.decode()for x in errors],
            'error_placeholder_roots_rejected_not_accepted':rejected},
        'change':{'theorem':'StructuralW9A220261020.Final.actual_summed','old_start_line':69,
            'old_text':OLD.decode(),'new_text':NEW.decode(),'byte_delta':len(repaired)-len(original),
            'scope':'Explicit definitionally equal StateAt target for both left/right endpoints; exact original hs/ht proof terms.'},
        'old_source':{'bytes':len(original),'sha256':sha(original)},
        'new_source':{'path':REL,'bytes':len(repaired),'sha256':sha(repaired)},
        'theorem_types':types,'Graph_Counting_endpoint_definition_comparison':defs,
        'forward_and_reverse_projection_exact':True,'all_bytes_outside_two_existing_endpoint_proofs_identical':True,
        'mathematical_definitions_literals_quotients_costs_pressure_boundary_threshold_roots_changes':0,
        'previous_ordinary_passes':passes,'source_inputs_before':before,'source_inputs_after':list(SEEN.values()),
        'original_inputs_unchanged':True,'compiler_export_kernel_search_runs':0,'round_counter_changed':False,
        'ordinary_passed_for_new_Final':False,'Comparator_passed':False,'independent_kernel_passed':False,
        'website_submission_ready':False,'requires_new_root_frozen_gate_before_compile':True}
    write(HERE/REL,repaired);write(HERE/'Final-v0.lean',original)
    diff=''.join(difflib.unified_diff(original.decode().splitlines(keepends=True),repaired.decode().splitlines(keepends=True),
        fromfile='canonical-v0/'+REL,tofile='final-repair-v1/'+REL))
    write(HERE/'Final-v0-to-v1.diff',diff.encode());write(HERE/'repair.json',dump(report))
    for name,raw in evidence.items():write(HERE/'failed-ordinary-v4-evidence'/name,raw)
    print(json.dumps({'source_bytes':len(repaired),'source_sha256':sha(repaired),'delta_bytes':len(repaired)-len(original),
        'repair_json_sha256':sha(dump(report)),'proof_execution_runs':0}))


if __name__=='__main__':main()
