"""Stage a reproducible research checkpoint, excluding evolving/failed proofs."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def main():
    receipt=json.loads((HERE/'ordinary-verified-current.json').read_bytes())
    files=['.gitattributes','README.md','submission/goal-20261016/STATUS.zh.md']
    names=['README.md','ordinary-verified-current.json','seal_ordinary_progress.py','prepare_progress_sync.py',
      'window_interval_kernel.py','window_interval_kernel.json','window_jet_crosscheck.py','window_jet_crosscheck.json',
      'window_global_cover.py','window_lower_global_cover.py','window_make_lower_variant.py','window_make_lower_variant.json',
      'window_minimizer_cover.py','window_correlated_minimizer_cover.py','window_make_correlated_variant.py','window_make_correlated_variant.json',
      'window_cover_replay.py','window_direction_probe.py','window_snapshot.py',
      'cover_newjet.py','cover_newjet.json','cover_correlated_api.py','cover_correlated_direction.py',
      'cover_correlated_verify.py','cover_correlated_replay.py','cover_contractor_api.py','cover_contractor_verify.py',
      'cover_newton_contractor.py','cover_projection_archive.py','cover_archive_replay.py',
      'lean_generate.py','lean_verify.py']
    files+=['research-goal-20261016/'+s for s in names]
    for row in receipt['modules']:
        for key,sha_key in [('source','source_sha256'),('log','log_sha256')]:
            p=ROOT/row[key];assert hashlib.sha256(p.read_bytes()).hexdigest()==row[sha_key]
            files.append(row[key])
    files += [str(p.relative_to(ROOT)).replace('\\','/') for folder in ['cover-compact-archive','snapshots']
              for p in sorted((HERE/folder).glob('*')) if p.is_file()]
    # Keep the generation programs that reproduce the verified actual profile.
    files += ['research-goal-20261016/'+s for s in ['window_generate_energy.py','window_generate_energy_bound.py','window_generate_profile.py']]
    files=sorted(set(files));assert all((ROOT/p).is_file() for p in files)
    subprocess.run(['git','add','-f','--',*files],cwd=ROOT,check=True)
    subprocess.run(['git','add','--renormalize','-f','--',*files],cwd=ROOT,check=True)
    entries=[]
    for path in files:
        raw=git('show',':'+path);sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        actual=(ROOT/path).read_bytes()
        assert raw==actual or (path in ['README.md','.gitattributes'] and raw==actual.replace(b'\r\n',b'\n')),('Index differs from selected source',path)
        try:raw.decode('utf8');binary=b'\0' in raw
        except UnicodeDecodeError:binary=True
        entries.append({'path':path,'sha':sha,'bytes':len(raw),'binary':binary})
    out={'base_commit':git('rev-parse','HEAD').decode().strip(),'tree_sha':git('write-tree').decode().strip(),
         'files':entries,'file_count':len(entries),'bytes':sum(x['bytes'] for x in entries),
         'submission_ready':False,'new_unconditional_zero_proportion_proven':False}
    dest=ROOT/'tmp/goal-20261016/staged.json';dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['base_commit','tree_sha','file_count','bytes']}))
if __name__=='__main__':main()
