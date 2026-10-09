from pathlib import Path
import hashlib,json,argparse
if not __debug__:raise SystemExit('Run without -O: byte and boundary-provenance guards must stay enabled.')
p=argparse.ArgumentParser();p.add_argument('--batch',type=int,default=8);a=p.parse_args();assert a.batch>=1
out=Path(__file__).resolve().parent;base=out/'AMSyncAlias8.lean';boundary=out/'command-boundaries.tsv'
raw=base.read_bytes();assert hashlib.sha256(raw).hexdigest()=='40f0fb440a3673aa36ba81361e1db7ef31471851bae63b82d77f434605a769f5'
check_path=out/'command-boundaries-check.json'
check=json.loads(check_path.read_text(encoding='utf-8'))
assert check['status']=='PASS' and check['parser_exit_code']==0 and check['source_before_after_unchanged'] is True
assert check['parsed_source_sha256']==hashlib.sha256(raw).hexdigest()
assert check['boundaries_sha256']==hashlib.sha256(boundary.read_bytes()).hexdigest()
assert check['parser_source_sha256']==hashlib.sha256((out/'ParseBoundariesLinux.lean').read_bytes()).hexdigest()
rows=[]
for line in boundary.read_text(encoding='utf-8').splitlines():
    start,stop,is_proof,kind=line.split('\t');rows.append({'start':int(start),'stop':int(stop),'proof':is_proof=='true','kind':kind})
assert rows and all(0<=r['start']<r['stop']<=len(raw) for r in rows)
assert all(x['stop']<=y['start'] for x,y in zip(rows,rows[1:]))
proofs=[r for r in rows if r['proof']];assert len(proofs)>1000,len(proofs)
points=[r['stop'] for i,r in enumerate(proofs,1) if i%a.batch==0]
if proofs[-1]['stop'] not in points:points.append(proofs[-1]['stop'])
result=raw
for point in reversed(points):result=result[:point]+b'\nam_wait\n'+result[point:]
barrier=('elab "am_wait" : command => do\n  let env \u2190 Lean.getEnv\n  discard <| IO.wait env.checked\n  let ms \u2190 IO.monoMsNow\n  IO.println s!"AM_BARRIER {ms}"\n').encode('utf-8')
needle=b'set_option Elab.async false\n';assert result.count(needle)==1
result=result.replace(needle,barrier+b'set_option Elab.async true\n',1)
reset=b'\nset_option Elab.async false\n'
result+=reset
# Removing exactly the inserted wrapper and waits reconstructs the unchanged alias source.
assert result[:-len(reset)].replace(barrier+b'set_option Elab.async true\n',needle,1).replace(b'\nam_wait\n',b'')==raw
path=out/f'AMBoundedAsync{a.batch}.lean';assert not path.exists();path.write_bytes(result)
record={'batch':a.batch,'source':str(path),'source_bytes':len(result),'source_sha256':hashlib.sha256(result).hexdigest(),'base_source':str(base),'base_sha256':hashlib.sha256(raw).hexdigest(),'boundary_source_sha256':hashlib.sha256(boundary.read_bytes()).hexdigest(),'parser_check_record_sha256':hashlib.sha256(check_path.read_bytes()).hexdigest(),'actual_complete_command_parser_gate_passed':True,'command_count':len(rows),'proof_command_count':len(proofs),'inserted_barrier_count':len(points),'only_scheduling_changes_after_exact_eight_aliases':True,'proof_validation':'PENDING: generated candidate has not been compiled or independently checked','points':points}
(out/f'candidate-batch{a.batch}.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k!='points'}),flush=True)
