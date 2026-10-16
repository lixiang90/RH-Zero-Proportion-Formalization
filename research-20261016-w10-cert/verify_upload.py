"""Fresh single-file W10 verification against the pinned attempt-024 record.

Runs the inherited pinned Comparator, default Lean kernel and nanoda workflow.
Run under WSL python3.  No website submission or acceptance is performed.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,os,re,shutil,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
import verify_record_20261015 as legacy
import verify_single_solution as base
from bundle_gram_defect_solution import code_mask
from final_artifact_gate import finite_binding
P='3338842690820594373879991756052499665323'
Q='4956700000000000000000000000000000000000'
RECORD=Fraction(34191001116882886388531117129201664,50760020691785094633026544189453125)

def prepare(args,info):
  w=args.work_dir
  if w.exists() and any(w.iterdir()) and not args.resume:raise ValueError('Use a fresh work directory, or --resume for hash-checked reuse')
  modules=['ChallengeDeps','ChallengeDeps.CandidateSpec','Challenge.Candidate','Solution.Candidate']
  for name in ['source/ChallengeDeps','source/Challenge','source/Solution','lib','logs']:(w/name).mkdir(parents=True,exist_ok=True)
  legacy.validate_overlay(w,modules)
  prov=json.loads((args.website_repo/'provenance.json').read_text())
  hashes={n:v['sha256'] for n,v in prov['files'].items() if not v.get('missing')}
  for n,v in hashes.items():assert base.sha(args.website_repo/n)==v
  assert prov['commit']=='9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb'
  contract=json.loads((args.website_repo/'challenge/contract.json').read_text())
  assert contract['theorems']=={'strictImprovement':'candidate_strict_improvement','dyadicBound':'candidate_critical_line_bound','cumulativeBound':'candidate_critical_line_bound_cumulative'}
  assert set(contract['permittedAxioms'])==set(base.ALLOWED)
  assert contract['trustedUpstream']['leanToolchain']=='leanprover/lean4:v4.33.0-rc2'
  assert contract['trustedUpstream']['commit']==base.PINS['Zeta23']
  assert contract['trustedUpstream']['mathlibCommit']==base.PINS['mathlib']
  for k,p in [('comparatorCommit','Comparator'),('lean4exportCommit','lean4export'),('nanodaCommit','nanoda')]:assert contract['verifier'][k]==base.PINS[p]
  record=json.loads((args.website_repo/'submissions/attempt-024/submission.json').read_text())
  assert Fraction(int(record['score']['numerator']),int(record['score']['denominator']))==RECORD<Fraction(int(P),int(Q))
  (w/'source/ChallengeDeps.lean').write_bytes(legacy.archive_blob('Zeta23','comparator/ChallengeDeps.lean'))
  spec=(args.website_repo/'challenge/templates/CandidateSpec.lean.tmpl').read_text()
  spec=spec.replace('{{CURRENT_EXPRESSION}}',f'{RECORD.numerator} / {RECORD.denominator}').replace('{{NUMERATOR}}',P).replace('{{DENOMINATOR}}',Q)
  assert '{{' not in spec
  (w/'source/ChallengeDeps/CandidateSpec.lean').write_text(spec,encoding='utf8')
  (w/'source/Challenge/Candidate.lean').write_bytes((args.website_repo/'challenge/templates/Challenge.Candidate.lean').read_bytes())
  data=args.upload.read_bytes();assert len(data)<=2_000_000
  manifest=json.loads((ROOT/'submission/w10-20261016/manifest.json').read_bytes())
  assert manifest['source_sha256']==hashlib.sha256(data).hexdigest()
  assert manifest['source_bytes']==len(data)
  assert manifest['numerator']==P and manifest['denominator']==Q
  binding=finite_binding(manifest)
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',code_mask(data.decode('utf8')))
  (w/'source/Solution/Candidate.lean').write_bytes(data)
  bound=[Path(__file__).resolve(),Path(base.__file__).resolve(),Path(legacy.__file__).resolve(),args.upload,
    args.runtime_manifest,args.sources_manifest,args.dependencies_manifest,args.nanoda_provenance,args.package_manifest,
    args.website_repo/'provenance.json']
  bound += [Path(__file__).with_name('final_artifact_gate.py')]
  bound += [ROOT/name for name in binding['file_sha256']]
  receipt={'stage':'prepared','scope':'Fresh isolated W10 single-file verification; no website upload',
    'runtime':info,'pins':base.PINS,'score':{'numerator':P,'denominator':Q},'current_record':record,
    'website_source_commit':prov['commit'],'website_source_sha256':hashes,
    'solution':str(w/'source/Solution/Candidate.lean'),'solution_sha256':hashlib.sha256(data).hexdigest(),
    'solution_bytes':len(data),'upload_sha256':base.sha(args.upload),'finite_certificate_binding':binding,
    'additional_bound_source_sha256':{str(p):base.sha(p) for p in bound},
    'generated_source_sha256':{str(p.relative_to(w)):base.sha(p) for p in (w/'source').rglob('*.lean')},
    'ordinary_single_file_lean_passed':False,'local_single_file_verified':False,
    'statement_equality_proved':False,'independent_nanoda_passed':False,
    'default_kernel_replay_passed':False,'official_website_acceptance':False,'submitted':False}
  base.write_json(w/'prepared.json',receipt)
  return receipt,modules

def main():
  if not __debug__:raise RuntimeError('Upload verification assertions must remain enabled')
  assert os.name!='nt'
  ap=argparse.ArgumentParser(description=__doc__)
  ap.add_argument('--work-dir',type=Path,default=Path('/var/tmp/rh-zero-20261015/w10-upload-verification'))
  ap.add_argument('--receipt-dir',type=Path,default=ROOT/'verification/w10-20261016/single')
  ap.add_argument('--upload',type=Path,default=ROOT/'submission/w10-20261016/proof/Solution.lean')
  ap.add_argument('--resume',action='store_true');ap.add_argument('--prepare-only',action='store_true');ap.add_argument('--compile-only',action='store_true')
  ap.add_argument('--timeout',type=int,default=14400)
  ap.add_argument('--nanoda-threads',type=int,default=4,choices=[1,2,4])
  args=ap.parse_args();args.work_dir=args.work_dir.resolve()
  assert args.work_dir.is_relative_to(Path('/var/tmp/rh-zero-20261015'))
  setup=ROOT/'tmp/setup-20261015'
  args.runtime_manifest=setup/'runtime.json';args.sources_manifest=setup/'sources.json';args.dependencies_manifest=setup/'dependencies.json'
  args.package_manifest=ROOT/'lake-manifest.json';args.nanoda_provenance=setup/'nanoda-build.json'
  args.nanoda_bin=Path('/var/tmp/rh-zero-20261015/nanoda-target/release/nanoda_bin')
  args.nanoda_sha256=None;args.distribution='Ubuntu'
  args.website_repo=Path(__file__).with_name('website-snapshot')
  receipt={'passed':False,'stage':'preparation'}
  args.receipt_dir.mkdir(parents=True,exist_ok=True)
  try:
    lean,packages,info=legacy.runtime(args)
    args.compile_runtime_basis={n:info[n] for n in ['compiler_sha256','runtime_manifest_sha256','sources_manifest_sha256','package_manifest_sha256','dependency_build_receipt_sha256']}
    receipt,modules=prepare(args,info)
    if args.prepare_only:return
    paths=[str(args.work_dir/'lib'),*packages];receipt['compiled_modules']=[]
    for m in modules:
      receipt['stage']='compilation:'+m
      entry=legacy.compile_module(args,lean,paths,args.work_dir,m,receipt['compiled_modules'])
      receipt['compiled_modules'].append(entry)
      base.write_json(args.work_dir/'compile-progress.json',receipt)
      print(m,'passed',flush=True)
    receipt.update(stage='compiled',ordinary_single_file_lean_passed=True,whole_submission_compiled=True)
    if args.compile_only:return
    args.solution=args.work_dir/'source/Solution/Candidate.lean';base.copy_tools=legacy.copy_tools
    base.audit_replay(args,args.work_dir,lean,packages,receipt)
    receipt['local_single_file_verified']=True
    receipt['passed']=all(receipt[k] for k in ['statement_equality_proved','independent_nanoda_passed','default_kernel_replay_passed'])
    print(json.dumps({k:receipt[k] for k in ['passed','solution_bytes','solution_sha256','stage']}),flush=True)
  except Exception as e:
    receipt.update(passed=False,error_type=type(e).__name__,error=str(e));raise
  finally:
    args.work_dir.mkdir(parents=True,exist_ok=True)
    base.write_json(args.work_dir/'verification.json',receipt)
    for sub in ['', 'logs', 'tools/logs']:
      for p in (args.work_dir/sub).glob('*'):
        if p.is_file() and p.suffix in ['.json','.log']:
          out=args.receipt_dir/sub/p.name;out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,out)
if __name__=='__main__':main()
