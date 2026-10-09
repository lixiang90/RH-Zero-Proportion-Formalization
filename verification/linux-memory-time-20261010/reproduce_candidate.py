#!/usr/bin/env python3
"""Rebuild the pinned bounded8 candidate from committed inputs, in fresh tmp only.

Source generation only: no Lean process, runtime cache access, proof checking,
commit, upload, or website acceptance. Gzipped review components are not inputs.
"""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,re,subprocess,sys,tempfile
from pathlib import Path
# Dynamic imports must not write bytecode into frozen public script directories.
sys.dont_write_bytecode = True
if not __debug__:raise SystemExit('Run without -O: fixed-source guards are mandatory.')
HERE=Path(__file__).resolve().parent
RECIPE_SHA='e31ba79741921f96465883d8fee02a1c19544cf5b857a837c772257e491e17ef'
def digest(blob):return hashlib.sha256(blob).hexdigest()
def sha(path):return digest(path.read_bytes())
def require(ok,message):
 if not ok:raise ValueError(message)
def load(path,label):
 spec=importlib.util.spec_from_file_location(label,path)
 require(spec is not None and spec.loader is not None,'Cannot load fixed source generator')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def read_only_git(repo,*args):
 # Git2.34 ownership backports ignore -c safe.directory. Use only an ephemeral,
 # subprocess-local config; never edit the user's global or repository config.
 with tempfile.TemporaryDirectory(prefix='rh-source-repro-git-')as temporary:
  config=Path(temporary)/'safe.gitconfig'
  config.write_text('[safe]\n  directory = '+json.dumps(repo.as_posix())+'\n')
  env=os.environ.copy();env['GIT_CONFIG_GLOBAL']=str(config)
  return subprocess.run(['git','-C',str(repo),*args],capture_output=True,env=env)
def git(repo,*args):
 run=read_only_git(repo,*args)
 require(run.returncode==0,'Read-only Git guard failed: '+run.stderr.decode(errors='replace'))
 return run.stdout
def put(path,data):
 path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data if isinstance(data,bytes)else data.encode('utf8'))
def safe_destination(repo,relative):
 require(not relative.is_absolute()and '..'not in relative.parts,'Output must be a relative fresh path')
 require(len(relative.parts)>=2 and relative.parts[0]=='tmp','Output must be strictly below repository tmp')
 target=repo
 for part in relative.parts:
  target=target/part
  require(not target.is_symlink()and not getattr(target,'is_junction',lambda:False)(),'Symlink/junction output route refused')
 require(target.resolve()==target,'Resolved output leaves the requested route')
 require(not target.exists(),'Refusing any existing output file or directory')
 require(not git(repo,'ls-files','-z','--',relative.as_posix()),'Refusing a tracked output target')
 ignored=read_only_git(repo,'check-ignore','--quiet','--',relative.as_posix())
 require(ignored.returncode==0,'Output must already be ignored by repository rules')
 return target

def make_alias_am(pruned,alias_diff):
 text=pruned.decode('utf8');hunks=re.split(r'(?m)^@@ .*@@[^\n]*\n',alias_diff)[1:]
 require(len(hunks)>0,'Missing explicit alias edits')
 for hunk in hunks:
  before=''.join(line[1:]+'\n'for line in hunk.splitlines()if line[:1]in [' ','-'])
  after=''.join(line[1:]+'\n'for line in hunk.splitlines()if line[:1]in [' ','+'])
  require(text.count(before)==1,'Alias edit no longer matches one exact frozen source span')
  text=text.replace(before,after,1)
 require(text.count('exact Zeta23.XiPrime.')==8,'Expected exactly eight ordinary aliases')
 return text.encode('utf8')

def make_bounded8(raw,recipe):
 boundary=(HERE/'recipe/command-boundaries.tsv').read_bytes()
 check=json.loads((HERE/'recipe/command-boundaries-check.json').read_text())
 known=json.loads((HERE/'recipe/candidate-batch8.json').read_text())
 require(check['status']=='PASS'and check['parser_exit_code']==0 and check['source_before_after_unchanged']is True,'Actual parser gate required')
 require(check['parsed_source_sha256']==digest(raw)==known['base_sha256'],'Parser byte offsets belong to another source')
 require(check['boundaries_sha256']==digest(boundary)==known['boundary_source_sha256'],'Parser boundary input changed')
 require(check['parser_source_sha256']==sha(HERE/'recipe/ParseBoundariesLinux.lean'),'Parser source provenance changed')
 rows=[]
 for line in boundary.decode().splitlines():
  start,stop,proof,kind=line.split('\t');rows.append({'start':int(start),'stop':int(stop),'proof':proof=='true','kind':kind})
 require(len(rows)==4787 and all(0<=r['start']<r['stop']<=len(raw)for r in rows),'Invalid actual command intervals')
 require(all(x['stop']<=y['start']for x,y in zip(rows,rows[1:])),'Overlapping command intervals')
 proofs=[r for r in rows if r['proof']];require(len(proofs)==1289,'Proof boundary count changed')
 points=[r['stop']for i,r in enumerate(proofs,1)if i%8==0]
 if proofs[-1]['stop']not in points:points.append(proofs[-1]['stop'])
 require(points==known['points']and len(points)==162,'Pinned bounded8 offsets changed')
 result=raw
 for point in reversed(points):result=result[:point]+b'\nam_wait\n'+result[point:]
 barrier=('elab "am_wait" : command => do\n  let env ← Lean.getEnv\n  discard <| IO.wait env.checked\n  let ms ← IO.monoMsNow\n  IO.println s!"AM_BARRIER {ms}"\n').encode('utf8')
 needle=b'set_option Elab.async false\n';require(result.count(needle)==1,'AM option boundary changed')
 result=result.replace(needle,barrier+b'set_option Elab.async true\n',1)
 reset=b'\nset_option Elab.async false\n';result+=reset
 require(result[:-len(reset)].replace(barrier+b'set_option Elab.async true\n',needle,1).replace(b'\nam_wait\n',b'')==raw,'Scheduling changes did not reconstruct the alias source')
 require(digest(result)==recipe['bounded8_am_sha256'],'Bounded8 source differs from checked component')
 return result

def pivot_hints(certificate):
 data=json.loads(certificate);reps=[p for p in data['pairs']if(p['left'],p['right'])<=((p['right']+241)%482,(p['left']+241)%482)]
 require(len(reps)==1224,'Original representative count changed')
 long=[(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(1,6),(1,7),(2,4),(2,5),(2,6),(2,7),(3,5),(3,6),(3,7),(4,6),(4,7),(5,7)]
 slots={pair:2*i for i,pair in enumerate([(i,i+1)for i in range(7)]+long)};cells=data['captured_cells']
 def bound(label,i,j,side):
  if label>=241:i,j=7-j,7-i
  return (cells[label%241]['gap_bounds']+cells[label%241]['span_bounds'])[slots[i,j]+side]
 def primitive(left,right,i,j):
  if i==j:return 0
  first=(5*bound(left,i,j,1)if i<j else -5*bound(left,j,i,0))if i<=7 and j<=7 else 10**30
  second=(5*bound(right,i-1,j-1,1)if i<j else -5*bound(right,j-1,i-1,0))if i>=1 and j>=1 else 10**30
  value=min(first,second);return min(value,-4*32768)if i==j+1 else value
 indices=[3,4,35,54,57,59,86,90,134,157,161,164,167,182,271,333,355,370,419,420,478,480,562,570,571,601,701,780,806,808,877,890,892,894,901,926,929,933,934,939,940,1010,1013,1078,1097,1199,1200,1203,1213]
 hints={}
 for i in indices:
  left,right=reps[i]['left'],reps[i]['right'];matrix=[[primitive(left,right,a,b)for b in range(9)]for a in range(9)]
  low=[min(range(9),key=lambda k:matrix[c+1][k]+matrix[k][c])for c in range(8)]
  high=[min(range(9),key=lambda k:matrix[c][k]+matrix[k][c+1])for c in range(8)]
  hints[i]=(sum(k<<(4*c)for c,k in enumerate(low)),sum(k<<(4*c)for c,k in enumerate(high)))
 return indices,hints

def chosen_extension(original):
 basic=original.split('noncomputable def basicIntegerCertificateLower (index : Nat) : Int :=\n',1)[1].split('\n\nnoncomputable def basicIntegerCertificateCheck',1)[0]
 basic=basic.replace('primitiveBound left right (column+1) column','chosenBound left right (column+1) column (bits lowWord (4*column) 4 % 9)').replace('primitiveBound left right column (column+1)','chosenBound left right column (column+1) (bits highWord (4*column) 4 % 9)')
 proof=original.split('theorem basicIntegerCertificateLower_le (index : Nat) :\n',1)[1].split('\ntheorem integerCheck_of_basic',1)[0]
 proof=proof.replace('unfold basicIntegerCertificateLower','unfold chosenLower').replace('basicIntegerCertificateLower index','chosenLower index lowWord highWord').replace('have hentry := pairClosure_le_primitive packet.1 packet.2.1','have hentry := chosen_bound_le packet.1 packet.2.1')
 proof=proof.replace('exact hentry (column+1) column (by omega) (by omega)','exact hentry (column+1) column (bits lowWord (4*column) 4 % 9) (by omega) (by omega) (by omega)').replace('exact hentry column (column+1) (by omega) (by omega)','exact hentry column (column+1) (bits highWord (4*column) 4 % 9) (by omega) (by omega) (by omega)')
 return '''noncomputable def chosenBound (left right i j k : Nat) : Int :=
  primitiveBound left right i k + primitiveBound left right k j

theorem chosen_bound_le (left right i j k : Nat) (hi : i < 9) (hj : j < 9) (hk : k < 9) :
    ((pairClosure left right)[9*i+j]?).getD 0 ≤ chosenBound left right i j k := by
  have h := RHWeilRecord.FloydTwoEdge.closure_le_two_edge
    (primitiveBounds left right) i j k hi hj hk
  change ((pairClosure left right)[9*i+j]?).getD 0 ≤
    ((primitiveBounds left right)[9*i+k]?).getD 0 +
    ((primitiveBounds left right)[9*k+j]?).getD 0 at h
  rw [primitiveBounds_entry left right i k hi hk,
      primitiveBounds_entry left right k j hk hj] at h
  exact h

noncomputable def chosenLower (index lowWord highWord : Nat) : Int :=
'''+basic+'''

 theorem chosen_lower_le (index lowWord highWord : Nat) :
'''+proof+'''
theorem integerCheck_of_chosen (index lowWord highWord : Nat)
    (h : decide (2*805260*(5*10000000000*32768)*1000000000 ≤ chosenLower index lowWord highWord) = true) :
    integerCertificateCheck index = true := by
  apply decide_eq_true
  exact (of_decide_eq_true h).trans (chosen_lower_le index lowWord highWord)
'''

def add_chosen(data,original,certificate,expected):
 text=data.decode('utf8');marker='/- The command emits ordinary theorem declarations.';prefix,tail=text.split(marker,1);tail=marker+tail
 indices,hints=pivot_hints(certificate);low=[hints[i][0]for i in indices];high=[hints[i][1]for i in indices]
 old='''      let proof := if fullIndices.contains index then "decide +kernel"
        else if twoIndices.contains index then "exact integerCheck_of_twoEdge (by decide +kernel)"
        else "exact integerCheck_of_basic (by decide +kernel)"'''
 new='''      let lowWords : List Nat := '''+str(low)+'''
      let highWords : List Nat := '''+str(high)+'''
      let proof := if fullIndices.contains index then "decide +kernel"
        else if twoIndices.contains index then
          let pos := twoIndices.idxOf index
          let lo := (lowWords[pos]?).getD 0
          let hi := (highWords[pos]?).getD 0
          "exact integerCheck_of_chosen " ++ toString index ++ " " ++ toString lo ++ " " ++ toString hi ++ " (by decide +kernel)"
        else "exact integerCheck_of_basic (by decide +kernel)"'''
 require(tail.count(old)==1,'Finite routing boundary changed')
 helper=chosen_extension(original);result=(prefix+helper+'\n'+tail.replace(old,new)).encode('utf8')
 require(result.decode().replace(helper+'\n','',1).replace(new,old,1)==text,'Old computational prefix or proof types changed')
 require(digest(result)==expected,'Chosen Data differs from prepared source')
 return result

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--repo-root',required=True,type=Path)
 parser.add_argument('--output-dir',required=True,type=Path)
 parser.add_argument('--variant',choices=['bounded8','bounded8-chosen49'],default='bounded8')
 args=parser.parse_args();repo=args.repo_root.resolve()
 require((repo/'.git').exists(),'Repository root with Git metadata required')
 recipe_path=HERE/'source-recipe.json';require(sha(recipe_path)==RECIPE_SHA,'Recipe manifest changed')
 recipe=json.loads(recipe_path.read_text());pins=recipe['public_pins']
 before={rel:(repo/rel).read_bytes()for rel in pins}
 require(all(digest(blob)==pins[rel]for rel,blob in before.items()),'Frozen committed input changed')
 tracked={name.decode()for name in git(repo,'ls-files','-z','--',*pins).split(b'\0')if name}
 require(set(pins)<=tracked,'Every fixed public source must be tracked')
 for name,expected in recipe['recipe_files'].items():require(sha(HERE/'recipe'/name)==expected,'Explicit recipe edit/provenance changed: '+name)
 dest=safe_destination(repo,args.output_dir)
 optimized=load(repo/'scripts/bundle_optimized_candidate.py','frozen_optimized_source')
 bundler=load(repo/'scripts/bundle_solution.py','frozen_public_bundler')
 point=load(repo/'scripts/generate_reflected_point_candidate.py','frozen_reflected_point')
 pruned=optimized.prune_am(before['RecordProportion/ImportedAM.lean'],bundler)
 require(digest(pruned)==recipe['pruned_am_sha256'],'Guarded21 pruning differs')
 alias=make_alias_am(pruned,(HERE/'recipe/aliases-eight.diff').read_text());require(digest(alias)==recipe['alias_am_sha256'],'Eight-alias source differs')
 am=make_bounded8(alias,recipe)
 # Create only a fresh ignored tree. Public sources and frozen scripts are read-only.
 dest.mkdir()
 for rel,blob in before.items():
  if rel.startswith('RecordProportion/')or rel in ['NOTICE','scripts/bundle_solution.py','submission/candidate-entry.lean.in']:put(dest/rel,blob)
 put(dest/'RecordProportion/ImportedAM.lean',am)
 datafile=dest/'RecordProportion/FiniteCertificateData.lean'
 generated=subprocess.run([sys.executable,'-B','-X','utf8',str(repo/'scripts/generate_two_edge_candidate.py'),'--output',args.output_dir.as_posix()+'/RecordProportion/FiniteCertificateData.lean'],cwd=repo,capture_output=True)
 put(dest/'twoedge-source-generation.stdout.log',generated.stdout);put(dest/'twoedge-source-generation.stderr.log',generated.stderr)
 require(generated.returncode==0,'Finite source generator failed; logs preserved')
 data=datafile.read_text();pattern=r'\nrun_cmd Lean.Elab.Command.liftIO <\| do\n  let now ← IO.monoMsNow\n  IO.eprintln s!"COST PROOFS_(?:BEGIN|END) \{now\}"\n'
 data,count=re.subn(pattern,'\n',data);require(count==2,'Timing-command guard changed');require(digest(data.encode())==recipe['data_twoedge_sha256'],'Two-edge Data differs')
 if args.variant=='bounded8-chosen49':data=add_chosen(data.encode(),before['RecordProportion/FiniteCertificateData.lean'].decode(),before['output/am-expanded-nine-point-certificate.json'],recipe['data_chosen49_sha256']).decode()
 put(datafile,data)
 reflected=point.candidate(point.pinned_inputs());require(digest(reflected)==recipe['point_sha256'],'Reflected Point differs');put(dest/'RecordProportion/PointSoundness.lean',reflected)
 expected=recipe['known_outputs'][args.variant]
 command=[sys.executable,'-B','-X','utf8',str(dest/'scripts/bundle_solution.py'),'--entry','submission/candidate-entry.lean.in','--compact-layout','--compact-nat-calls','--compact-numeral-dictionary','--output',expected['name']]
 run=subprocess.run(command,cwd=dest,capture_output=True);put(dest/'bundler.stdout.log',run.stdout);put(dest/'bundler.stderr.log',run.stderr)
 require(run.returncode==0,'Fresh numeral-dictionary bundler failed; logs preserved')
 output=dest/expected['name'];require(sha(output)==expected['sha256']and output.stat().st_size==expected['bytes'],'Exact known whole source reproduction failed')
 require(all((repo/rel).read_bytes()==blob for rel,blob in before.items()),'Frozen public input changed during generation')
 record={'status':'SOURCE_REPRODUCTION_ONLY','variant':args.variant,'bytes':output.stat().st_size,'sha256':sha(output),'fresh_numeric_dictionary':True,'generated_from_committed_public_inputs':True,'public_inputs_unchanged':True,'wrapper_sha256':sha(Path(__file__)),'recipe_sha256':RECIPE_SHA,'am_source_sha256':digest(am),'data_source_sha256':sha(datafile),'point_source_sha256':digest(reflected),'gzip_review_components_used_as_inputs':False,'lean_executed':False,'whole_proof_checked':False,'nano_checked':False,'comparator_checked':False,'website_acceptance':False,'submitted':False}
 put(dest/'source-reproduction.json',json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if __name__=='__main__':
 try:main()
 except (ValueError,OSError,KeyError)as error:raise SystemExit(str(error))