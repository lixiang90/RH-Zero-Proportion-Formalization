"""AST/hash/byte-inventory preparation only. Does not import/run generator."""
import ast
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODULE_PINS = {
 'StructuralS1RM20261018/CurrentPrefix.lean': 'ea8e01118d19158ba8313504910645ad467ea86eb2ea65a897859ae98101df21',
 'StructuralS1RTiny20261018/Dev/Core.lean': '1e144c848b39c85277af45c590cb0e54e93b2f098d44f5eb40bcb2e1b8d216ac',
 'StructuralS1RTiny20261018/Phase1/Localization.lean': 'ad722eca53b43ff28ccfe9f66e338979ac05ff7088fe067dc395ea5e1c9cf758',
 'StructuralS1RTiny20261018/Phase2/Counting.lean': '2bda5c9df708b4568f8f08447894cb73a3c6ecb9d2c77be67e2eb46387be868e',
 'StructuralS1RTiny20261018/Phase4/Final.lean': 'd477fd3181e0d4d5a3c89bcbcb987dd6cad00fbdde1946d01c26ac0c279489ed',
}
MODULE_NAMES = [p[:-5].replace('/', '.') for p in MODULE_PINS]
DEPS = list(MODULE_PINS) + [
 'research-goal-20261018-tiny-runtime-preparation/compiler-prepared.json',
 'research-goal-20261018-tiny-runtime-preparation/phase1-prepared.json',
 'research-goal-20261018-tiny-runtime-preparation/phase2-prepared.json',
 'research-goal-20261018-tiny-runtime-preparation/phase3-prepared.json',
 'research-goal-20261018-tiny-runtime-preparation/phase4-prepared.json',
 'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json',
 'tmp/current-s1r-tiny-20261018/phase4-v0/terminal.json',
 'research-goal-20261018-tiny-flatten-preparation-v2/prepared-files.json',
 'research-goal-20261018-tiny-flatten-preparation-v2/generate_draft.py',
 'research-goal-20261018-tiny-flatten-preparation-v1/prepared-files.json',
 'research-goal-20261018-tiny-flatten-preparation-v1/generate_draft.py',
 'research-goal-20261016/gates/tiny-phase1-ordinary-20261018.json',
 'research-goal-20261018-tiny-flatten-preparation/prepared-files.json',
 'research-goal-20261018-tiny-flatten-preparation/generate_draft.py',
 'research-goal-20261018-tiny-runtime-preparation/dev-source-files.json',
 'research-goal-20261018-tiny-runtime-preparation/runtime-CandidateSpec.json',
 'research-goal-20261018-tiny-runtime-preparation/runtime-CandidateSpec.snapshot.lean',
 'research-goal-20261018-tiny-localization-preparation/prepared-files.json',
 'research-goal-20261016/gates/tiny-dev-ordinary-v0-20261018.json',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean',
 'research-goal-20261017-w10-generator-policy/policy-snapshot.json',
 'research-goal-20261017-w10-generator-policy/snapshot/CONTRIBUTING.md',
 'research-goal-20261017-w10-generator-policy/snapshot/challenge/contract.json',
 'research-goal-20261017-w10-generator-policy/snapshot/scripts/prepare-candidate.ts',
 'research-20261016-w10-cert/website-snapshot/provenance.json',
 'research-20261016-w10-cert/website-snapshot/challenge/templates/CandidateSpec.lean.tmpl',
 'research-20261016-w10-cert/website-snapshot/challenge/templates/Challenge.Candidate.lean',
]

def sha(b):
    return hashlib.sha256(b).hexdigest()

def row(path):
    data = path.read_bytes()
    return {'path': path.relative_to(ROOT).as_posix(), 'bytes': len(data), 'sha256': sha(data)}

def exclusive(name, obj):
    with (HERE/name).open('x', encoding='utf-8', newline='\n') as h:
        json.dump(obj, h, ensure_ascii=False, indent=2)
        h.write('\n')

def main():
    assert len(sys.argv) == 2 and sys.argv[1] == '--prepare-static-only'
    for out in ['input-pins.json','candidate-parameters.json','preparation.json','prepared-files.json']:
        assert not (HERE/out).exists(), out
    assert not (HERE/'draft').exists()
    trees = {}
    for name in ['generate_draft.py', 'prepare_only.py']:
        trees[name] = ast.parse((HERE/name).read_text(encoding='utf-8'), filename=name)
    gen = trees['generate_draft.py']
    literals = {}
    for n in gen.body:
        if isinstance(n, ast.Assign) and isinstance(n.targets[0],ast.Name):
            if n.targets[0].id == 'HEADER':
                literals['HEADER'] = ast.literal_eval(n.value.func.value).encode('utf-8')
    # This is read-only source inventory, not execution of the generator.
    imports = []
    internal = []
    module_bytes = 0
    import_bytes = 0
    body_bytes = []
    notice_counts = []
    for name, expected in MODULE_PINS.items():
        data = (ROOT/name).read_bytes()
        assert sha(data) == expected, name
        text = data.decode('utf-8')
        module_bytes += len(data)
        nimports = 0
        for line in data.splitlines(keepends=True):
            if not line.startswith(b'import '):
                continue
            target = line.decode('ascii').strip()[7:]
            assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',target)
            nimports += len(line)
            import_bytes += len(line)
            if target in MODULE_NAMES:
                internal.append({'path':name,'module':target,'bytes':len(line)})
            else:
                imports.append({'module':target,'bytes':len(line)})
        assert not re.search(r'(?m)^theorem candidate_(?:strict_improvement|critical_line_bound)',text)
        body_bytes.append(len(data)-nimports)
        notice_counts.append({'path':name,'Copyright_mentions':text.count('Copyright'),
                              'SPDX_mentions':text.count('SPDX-License-Identifier'),
                              'license_case_insensitive_mentions':text.lower().count('license')})
    assert module_bytes == 1_977_052
    assert len(internal) == 5
    assert imports[0]['module'] == 'ChallengeDeps'
    assert imports[1]['module'] == 'ChallengeDeps.CandidateSpec'
    official = ROOT/'research-20261016-w10-cert/website-snapshot'
    provenance = json.loads((official/'provenance.json').read_text())
    for name in ['CandidateSpec.lean.tmpl','Challenge.Candidate.lean']:
        p = 'challenge/templates/'+name
        assert sha((official/p).read_bytes()) == provenance['files'][p]['sha256']
    contract = json.loads((ROOT/'research-goal-20261017-w10-generator-policy/snapshot/challenge/contract.json').read_text())
    names = ['candidate_strict_improvement','candidate_critical_line_bound','candidate_critical_line_bound_cumulative']
    assert list(contract['theorems'].values()) == names
    wrapper = (HERE/'official-wrapper.lean.txt').read_bytes()
    template = (official/'challenge/templates/Challenge.Candidate.lean').read_text(encoding='utf-8')
    for name in names:
        pattern = r'theorem '+re.escape(name)+r'\s*:(.*?) := by'
        a = re.search(pattern, template, re.S).group(1)
        b = re.search(pattern, wrapper.decode('utf-8'), re.S).group(1)
        assert re.sub(r'\s+','',a) == re.sub(r'\s+','',b), name
    assert not re.search(rb'(?m)^def (candidateKappa|currentRecordKappa)\b',wrapper)
    imported_bytes = sum(r['bytes'] for r in imports)
    separator_bytes = sum(len(('\n/- BEGIN FLATTENED MODULE '+name+' -/\n').encode())+1 for name in MODULE_NAMES)
    predicted = len(literals['HEADER']) + imported_bytes + 1 + sum(body_bytes) + separator_bytes + 1 + len(wrapper)
    assert predicted <= 2_000_000
    inputpins = {'schema':'tiny-flatten-input-pins-v1','module_sha256':MODULE_PINS,
                 'external_imports':[x['module'] for x in imports],
                 'input_total_bytes':module_bytes,'internal_imports_removed':internal}
    exclusive('input-pins.json',inputpins)
    params = {
      'schema':'tiny-official-spec-request-v1', 'upload_ready':False,
      'score':{'numerator':'3337839448633819172184136761695440236797',
               'denominator':'4955319193827760237900000000000000000000'},
      'expected_current_record':{'numerator':'3337839448633819172184136761695440236797',
                                 'denominator':'4955319193847235264050000000000000000000'},
      'public_theorem_names':names,
      'trusted_spec_template':{'path':str((official/'challenge/templates/CandidateSpec.lean.tmpl').relative_to(ROOT)).replace('\\','/'),
                               'sha256':provenance['files']['challenge/templates/CandidateSpec.lean.tmpl']['sha256'],
                               'origin_url':provenance['files']['challenge/templates/CandidateSpec.lean.tmpl']['url']},
      'CURRENT_EXPRESSION_source':'Official current kernel-verified ledger exactExpression, not contributor-defined',
      'template_parameters':{'NUMERATOR':'score.numerator','DENOMINATOR':'score.denominator',
                             'CURRENT_EXPRESSION':'trusted currentRecord.exactExpression'},
      'trusted_CandidateSpec_written_or_modified':False,
      'local_old_CandidateSpec_usable':False,
      'fresh_official_template_check_completed':False,
      'official_generation_or_submission_executed':False,
      'scope':'Proposed exact score and unverified draft only; no accepted record claim',
      'unclosed_gates':['four ordinary modules','actual flatten and independent source audit',
                        'fresh record/template/dependency pins and official CandidateSpec',
                        'single-source ordinary elaboration/axioms','export/Comparator/nanoda',
                        'full website time/memory/source/request limits','GitHub/final submission materials']}
    exclusive('candidate-parameters.json',params)
    exclusive('preparation.json',{
      'schema':'tiny-flatten-static-preparation-v4','passed':True,
      'AST_sources':['generate_draft.py','prepare_only.py'],
      'source_input_bytes':module_bytes,'external_import_count':len(imports),
      'internal_import_count':len(internal),'wrapper_bytes':len(wrapper),
      'predicted_solution_bytes':predicted,'predicted_headroom_bytes':2_000_000-predicted,
      'notice_inventory':notice_counts,
      'three_wrapper_statements_whitespace_normalized_equal_official_template':True,
      'generator_executions':0,'draft_exists':False,'Lean_runs':0,'Comparator_runs':0,
      'Nano_runs':0,'mathematical_evaluations':0,'compiler_inputs_modified':False,
      'upload_ready':False,'read_dependencies_sha256_before':{p:row(ROOT/p)['sha256'] for p in DEPS}})
    owned = ['generate_draft.py','prepare_only.py','adapt_v3.py','v2-to-v3.diff','version-delta.json','official-wrapper.lean.txt','SPEC.zh.md',
             'input-pins.json','candidate-parameters.json','preparation.json']
    readdeps = [row(ROOT/p) for p in DEPS]
    runtime = Path(sys.executable)
    exclusive('prepared-files.json',{
      'schema':'tiny-flatten-generator-prepared-v4', 'scope':'Static source preparation only',
      'files':[row(HERE/p) for p in owned], 'read_dependencies':readdeps,
      'external_runtime_identity':{'path':str(runtime),'bytes':runtime.stat().st_size,
                                  'sha256':sha(runtime.read_bytes()),'version':sys.version},
      'upload_ready':False,'generator_executions':0,'production_executions':0})
    print(json.dumps({'prepared_sha256':sha((HERE/'prepared-files.json').read_bytes()),
                      'predicted_solution_bytes':predicted,'upload_ready':False}))

if __name__ == '__main__':
    main()
