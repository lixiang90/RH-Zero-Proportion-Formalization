"""Read-only source/binary inspection with new JSON receipts; no child process.

This does not inspect executable dependency closure or prove runtime viability.
Only this directory receives output. No compiler, installer, network or proof
evaluator is imported or invoked.
"""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ROOTS = ['candidate_strict_improvement', 'candidate_critical_line_bound',
         'candidate_critical_line_bound_cumulative']
ALLOWED = ['propext', 'Quot.sound', 'Classical.choice']
PRIMITIVES = ['Nat', 'String', 'String.mk', 'Char', 'Quot', 'Quot.mk', 'Quot.lift',
              'Quot.ind', *ALLOWED, 'Nat.add', 'Nat.sub', 'Nat.mul', 'Nat.pow',
              'Nat.gcd', 'Nat.div', 'Nat.mod', 'Nat.beq', 'Nat.ble', 'Nat.land',
              'Nat.lor', 'Nat.xor', 'Nat.shiftLeft', 'Nat.shiftRight', 'String.ofList',
              'Char.ofNat', 'List', 'eagerReduce']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def new(name, obj):
    raw = (json.dumps(obj, ensure_ascii=False, indent=2)+'\n').encode()
    with (HERE/name).open('xb') as stream:
        stream.write(raw)


def identity(path):
    path = Path(path)
    result = {'path': str(path), 'exists': path.is_file()}
    if path.is_file():
        data = path.read_bytes()
        result.update({'bytes':len(data), 'sha256':sha(data),
                       'file_header_hex':data[:16].hex()})
    return result


draft = HERE/'draft-v0'
solution = (draft/'Solution.lean').read_bytes()
plan = json.loads((draft/'candidate-parameters.json').read_bytes())
assert sha(solution) == plan['solution_sha256']
challenge = (draft/'trusted/Challenge/Candidate.lean').read_text(encoding='utf-8')
wrapper = (HERE/'public-wrapper.lean.txt').read_text(encoding='utf-8')
statement = lambda source,name: re.search(r'(?m)^theorem '+name+r'\s*:\s*(.*?)\s*:= by',source,re.S)[1]
checks = []
for name in ROOTS:
    left,right = statement(challenge,name),statement(wrapper,name)
    assert re.sub(r'\s+','',left) == re.sub(r'\s+','',right)
    checks.append({'root':name,'whitespace_normalized_statements_equal':True,
                   'challenge_statement_sha256':sha(left.encode()),
                   'wrapper_statement_sha256':sha(right.encode())})
segments = []
for item in plan['body_segments']:
    part = solution[item['start']:item['end']]
    assert sha(part) == item['retained_non_import_sha256']
    segments.append({'module':item['module'],'retained_bytes_verified':True})
new('static-source-audit.json',{
    'scope':'Text identity only; no elaboration, semantic or kernel claim',
    'solution_sha256':sha(solution),'solution_bytes':len(solution),
    'source_slack_bytes':2_000_000-len(solution),
    'public_statement_text_checks':checks,'flatten_segments':segments,
    'all_non_text_proof_runs':0,'upload_ready':False})
gate = json.loads((ROOT/'research-goal-20261020-w9a2-runtime/trusted-setup-gate.json').read_bytes())
binary_paths = [gate['lean']['path'],
    ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe',
    ROOT/'tmp/Comparator/.lake/build/bin/comparator.exe',
    ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin']
source_paths = ['tools/ComparatorCoreAudit.lean','tmp/Comparator/Comparator.lean',
    'tmp/Comparator/Comparator/Axioms.lean','tmp/Comparator/Comparator/Compare.lean',
    'tmp/Comparator/Comparator/Util.lean','tmp/Comparator/Main.lean',
    'tmp/lean4export/Export.lean','tmp/lean4export/Export/Parse.lean','tmp/lean4export/Main.lean']
new('runtime-inventory.json',{
    'scope':'Existing file bytes only. No execution, DLL closure audit, compatibility test or install.',
    'lean_version_from_prior_root_gate':gate['lean']['version'],
    'binaries':[identity(p) for p in binary_paths],
    'trusted_tool_sources':[identity(ROOT/p) for p in source_paths],
    'dependency_packages_from_root_gate':gate['packages'],
    'package_libs_from_root_gate':gate['package_libs'],
    'full_dynamic_runtime_closure_bound':False,
    'native_CoreAudit_installed_in_current_environment':False,
    'old_Linux_runtime_reusable':False,
    'Windows_export_and_WSL_nanoda_path_prepared_only':True})
new('nanoda-config.json',{
    'use_stdin':True,'permitted_axioms':ALLOWED,
    'unpermitted_axiom_hard_error':True,'nat_extension':True,'string_extension':True,
    'num_threads':0,'unsafe_permit_all_axioms':False,'print_success_message':True,
    'print_axioms':True,'pp_to_stdout':True})
new('verification-contract.json',{
    'scope':'Prepared command/acceptance contract; no execution',
    'public_roots':ROOTS,'allowed_axioms':ALLOWED,'export_primitives':PRIMITIVES,
    'module_order':['ChallengeDeps','ChallengeDeps.CandidateSpec','Challenge.Candidate','Solution.Candidate'],
    'ordinary_flags':['-j1','-M13500','--tstack=262144','-DrelaxedAutoImplicit=false','-DElab.async=false'],
    'export_argv_template':['<lean4export>','<challenge-or-solution-module>','--',*ROOTS,*PRIMITIVES],
    'core_audit_native_argv_template':['<bound-native-CoreAudit>','<challenge.ndjson>','<solution.ndjson>',*ROOTS],
    'core_audit_interpreted_argv_template':['<bound-same-version-lean>','--run','<bound-ComparatorCoreAudit.lean>',
                                         '<challenge.ndjson>','<solution.ndjson>',*ROOTS],
    'nanoda_argv_template':['wsl.exe','--distribution','Ubuntu','--exec','<mapped-bound-nanoda>',
                            '<mapped-nanoda-config.json>'],
    'nanoda_stdin':'Exact bytes of solution.ndjson',
    'monotonic_budget_seconds':3200,
    'budget_start':'Before all production pin checks, source generation and trusted CandidateSpec generation',
    'budget_end':'After final immutable hashes and fsynced verification/deadline/terminal receipts',
    'automatic_repairs':0,'automatic_retries':0,'cached_user_oleans':False,
    'complete_local_chain_passed':False,'official_website_acceptance':False})
print(json.dumps({'text_statement_checks':len(checks),'all_equal':True,'binary_executions':0}))
