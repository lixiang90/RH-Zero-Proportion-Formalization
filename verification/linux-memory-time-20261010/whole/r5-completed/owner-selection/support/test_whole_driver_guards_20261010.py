"""Pure-Python negative fixtures; no Lean/Nano, cache eviction, or proof claims."""
from pathlib import Path
import argparse, importlib.util, json, shutil, time

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--fixture-root',type=Path,required=True)
    args=parser.parse_args();fixture=args.fixture_root.resolve()
    assert fixture.parent==Path('/tmp/rh-proportion-memory-20261010') and fixture.name.startswith('whole-guard-fixture-')
    assert not fixture.exists();fixture.mkdir()
    real=Path('/tmp/rh-proportion-memory-20261010/whole-native-20261010-r5')
    spec=importlib.util.spec_from_file_location('whole_driver',real/'whole_candidate_native_driver_20261010.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    config=json.loads((real/'config.json').read_text());realtools=Path(config['toolroot']);tools=fixture/'tools';tools.mkdir()
    plan=json.loads((realtools/'prepared-plan.json').read_text())
    for row in plan['source_bindings']:
        source=realtools/row['prepared'];dest=tools/row['prepared'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
    shutil.copyfile(realtools/'prepared-plan.json',tools/'prepared-plan.json')
    bindings={}
    for src,expected in config['sources'].items():
        dest=fixture/Path(src).relative_to(real);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);bindings[str(dest)]=expected
    configs={}
    for src,expected in config['tool_config_bindings'].items():
        dest=tools/Path(src).relative_to(realtools);shutil.copyfile(src,dest);configs[str(dest)]=expected
    config.update(root=str(fixture),toolroot=str(tools),sources=bindings,tool_config_bindings=configs,native_plan_sha256=mod.sha(tools/'prepared-plan.json'))
    mod.write_json(fixture/'config.json',config)
    argsload=argparse.Namespace(native_root=fixture,config_sha=mod.sha(fixture/'config.json'))
    rows=[]
    def denied(label,fn):
        try:fn()
        except AssertionError as e:rows.append({'case':label,'rejected_before_proof_start':True,'reason':str(e)});return
        raise AssertionError('Negative guard did not reject '+label)
    mod.load_config(argsload)
    path=fixture/'source/Solution/Candidate.lean';old=path.read_bytes();path.write_bytes(old+b'\n-- negative fixture\n')
    denied('candidate-source-byte-mismatch',lambda:mod.load_config(argsload));path.write_bytes(old)
    path=tools/'tool-source/Export.lean';old=path.read_bytes();path.write_bytes(old+b'\n-- negative fixture\n')
    denied('pinned-tool-source-byte-mismatch',lambda:mod.load_config(argsload));path.write_bytes(old)
    path=tools/'nanoda-official-default-config.json';old=path.read_bytes();obj=json.loads(old);obj['num_threads']=4;mod.write_json(path,obj)
    denied('nano-config-byte-mismatch',lambda:mod.load_config(argsload))
    changed=dict(config);changed['tool_config_bindings']=dict(configs);changed['tool_config_bindings'][str(path)]=mod.sha(path)
    mod.write_json(fixture/'config.json',changed);argsload.config_sha=mod.sha(fixture/'config.json')
    denied('nano-config-semantic-mismatch-even-after-new-byte-binding',lambda:mod.load_config(argsload))
    path.write_bytes(old);mod.write_json(fixture/'config.json',config);argsload.config_sha=mod.sha(fixture/'config.json');mod.load_config(argsload)
    lib=fixture/'lib';ledgers=fixture/'phase-ledgers';ledgers.mkdir()
    for rel in ('ChallengeDeps.olean','ChallengeDeps/CandidateSpec.olean','Challenge/Candidate.olean'):
        path=lib/rel;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'SYNTHETIC NONPROOF FIXTURE ONLY\n')
    mod.write_json(ledgers/'contract.json',{'proof_succeeded':True,'artifact_family_after':mod.family(lib)})
    path=lib/'ChallengeDeps.olean';old=path.read_bytes();path.write_bytes(b'MISMATCH FIXTURE\n')
    denied('current-contract-artifact-family-mismatch-before-compile',lambda:mod.prereq(config,'compile'));path.write_bytes(old)
    path=lib/'Solution/Candidate.olean';path.parent.mkdir();path.write_bytes(b'SYNTHETIC NONPROOF FIXTURE ONLY\n')
    mod.write_json(ledgers/'compile.json',{'proof_succeeded':True,'artifact_family_after':mod.family(lib)})
    old=path.read_bytes();path.write_bytes(b'MISMATCH FIXTURE\n')
    denied('fresh-solution-artifact-family-mismatch-before-deps',lambda:mod.prereq(config,'deps'));path.write_bytes(old)
    path=tools/'tool-lib/Export.olean';path.parent.mkdir();path.write_bytes(b'SYNTHETIC NONPROOF FIXTURE ONLY\n')
    mod.write_json(ledgers/'tools.json',{'proof_succeeded':True,'tool_family_after':mod.family(tools/'tool-lib')})
    old=path.read_bytes();path.write_bytes(b'MISMATCH FIXTURE\n')
    denied('tool-artifact-family-mismatch-before-export',lambda:mod.prereq(config,'challenge-export'));path.write_bytes(old)
    mod.write_json(ledgers/'deps.json',{'deps_fresh_current_contract_only':True});mod.write_json(ledgers/'audit.json',{'fresh_three_roots_standard_axioms':True})
    for name in ('challenge','solution'):
        path=tools/f'exports/{name}.ndjson';path.parent.mkdir(exist_ok=True);path.write_bytes(b'SYNTHETIC NONPROOF FIXTURE ONLY\n')
        mod.write_json(ledgers/f'{name}-export.json',{'proof_succeeded':True,'export_file_after':{'path':str(path),'bytes':path.stat().st_size,'sha256':mod.sha(path)}})
    path=tools/'exports/solution.ndjson';path.write_bytes(b'MISMATCH FIXTURE\n')
    denied('export-attribution-mismatch-before-core',lambda:mod.prereq(config,'core'))
    denied('previous-boot-clock-reuse',lambda:mod.clock_elapsed({'boot_id':'SYNTHETIC OTHER BOOT','start_monotonic':time.monotonic()}))
    denied('future-monotonic-clock-reuse',lambda:mod.clock_elapsed({'boot_id':Path('/proc/sys/kernel/random/boot_id').read_text().strip(),'start_monotonic':time.monotonic()+1000000}))
    result={'status':'PURE_PYTHON_GUARD_FIXTURES_PASS','fixture_root':str(fixture),'driver_sha256':mod.sha(real/'whole_candidate_native_driver_20261010.py'),'tests':rows,'lean_nano_or_cache_evictions_executed':False,'synthetic_files_are_proofs':False}
    mod.write_json(fixture/'guard-test-result.json',result);print(json.dumps(result,indent=2))

if __name__=='__main__':main()
