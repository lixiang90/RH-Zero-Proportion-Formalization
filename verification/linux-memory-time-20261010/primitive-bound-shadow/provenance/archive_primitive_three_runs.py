"""Archive completed primitive-bound Windows text records; no proof execution."""
import gzip,hashlib,json,re,zlib
from pathlib import Path

BASE=Path(r'E:\codex-build\RH-Weil\tmp')
OUT=BASE/'primitive-bound-publication-20261010'
HANDOFF=BASE/'primitive-bound-shadow-native-prepared-20261010-r3/completed-three-run-handoff.json'
HANDOFF_SHA='8b6ef65927ad12d015ec6ff63b4600c0e3f98fccb728a4e4a8b39ec5afaba351'
ORIGINAL_SHA='d52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a'
REPO=Path(r'E:\codex-build\RH-Zero-Proportion-Formalization')
STD={'propext','Quot.sound','Classical.choice'}
FORBIDDEN=('.olean','.olean.private','.olean.server','.ilean','.ir','.exe','.dll','.so','.a','.o','.obj','.bin','.pyc','.tar','.zip','.7z')
SECRETS=re.compile(rb'(?:gh[pousr]_[A-Za-z0-9_]{20,}|github_pat_[A-Za-z0-9_]{20,}|\bsk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{25,}|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----|(?i:authorization\s*:\s*bearer\s+[A-Za-z0-9_.~-]{20,}))')

def sha(data):return hashlib.sha256(data).hexdigest()
def load(path):return json.loads(path.read_text(encoding='utf-8-sig'))
def json_write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def inspect(raw):
    assert len(raw)<=128_000_000
    raw.decode('utf-8-sig')
    assert b'\x00' not in raw and not raw.startswith((b'MZ',b'\x7fELF',b'PK\x03\x04',b'olean',b'\x00asm'))
    assert not SECRETS.search(raw),'credential pattern; value suppressed'
def inflate(blob):
    assert blob[:4]==b'\x1f\x8b\x08\x00' and blob[4:8]==b'\x00'*4
    d=zlib.decompressobj(31)
    raw=d.decompress(blob,128_000_001)
    assert d.eof and not d.unused_data and not d.unconsumed_tail
    inspect(raw)
    return raw

assert sha(HANDOFF.read_bytes())==HANDOFF_SHA
handoff=load(HANDOFF)
assert handoff['status']=='THREE_SHADOW_RUNS_COMPLETED_TWO_PROOFS_PASS_ONE_SOURCE_ERROR'
assert OUT.parent.resolve()==BASE.resolve() and not OUT.exists()
assert not OUT.parent.is_symlink()
OUT.mkdir()
bindings=[]
relocations=[]
def copy(source,rel,expected=None,role='completed text/source',compressed=False):
    source=Path(source)
    assert source.is_file() and not source.is_symlink()
    assert not any(source.name.removesuffix('.gz').endswith(x) for x in FORBIDDEN)
    before=source.stat()
    blob=source.read_bytes()
    source_blob_sha=sha(blob)
    if expected:
        size=expected.get('archived_bytes',expected.get('bytes'))
        digest=expected.get('archived_sha256',expected.get('sha256'))
        assert (len(blob),sha(blob))==(size,digest),str(source)
    raw=inflate(blob) if source.suffix=='.gz' else blob
    inspect(raw)
    if expected and 'raw_sha256' in expected:
        assert (len(raw),sha(raw))==(expected['raw_bytes'],expected['raw_sha256'])
    if compressed and source.suffix!='.gz':blob=gzip.compress(raw,compresslevel=6,mtime=0)
    dest=OUT/rel
    assert dest.resolve().is_relative_to(OUT.resolve()) and not dest.exists()
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(blob)
    assert sha(source.read_bytes())==source_blob_sha
    assert (before.st_size,before.st_mtime_ns)==(source.stat().st_size,source.stat().st_mtime_ns)
    encoded=dest.suffix=='.gz'
    if encoded:assert inflate(blob)==raw
    entry={'path':rel,'bytes':len(blob),'sha256':sha(blob),'encoding':'gzip' if encoded else 'identity',
        'raw_bytes':len(raw),'raw_sha256':sha(raw),'source_origin':str(source),'role':role,
        'original_compressed_bytes_preserved':source.suffix=='.gz'}
    bindings.append(entry)
    relocations.append({'historical_path':str(source),'published_path':rel,'path_scope':'historical Windows origin; relative packet path is usable'})
    return entry

copy(HANDOFF,'provenance/completed-three-run-handoff.json',{'bytes':HANDOFF.stat().st_size,'sha256':HANDOFF_SHA},'trusted completed handoff')
owners={}
for key,ident in [('previous_pair_archive_manifest','owner-r2'),('repaired_archive_manifest','owner-r3')]:
    spec=handoff[key];path=Path(spec['path']);root=path.parent
    owner=load(path);owners[ident]=owner
    copy(path,ident+'/archive-manifest.json',spec,'byte-identical original producer manifest')
    for row in owner['files']:
        source=Path(row['archived'])
        assert source.resolve().is_relative_to(root.resolve())
        rel=source.relative_to(root).as_posix()
        copy(source,ident+'/'+rel,row,'byte-identical completed owner record')
        relocations.append({'historical_path':row['source'],'published_path':ident+'/'+rel,'path_scope':'historical Linux/runtime origin; no runtime path opened'})
copy(handoff['three_run_analysis']['path'],'provenance/three-run-analysis.original.json',handoff['three_run_analysis'],'byte-identical owner analysis; timing terminology interpreted separately')
copy(BASE/'primitive-bound-shadow-native-prepared-20261010-r2/frozen-input-manifest.json',
     'provenance/frozen-r2-input-manifest.json',role='historical pre-run input bindings')
for version in ['r1','r2']:
    source_root=BASE/('primitive-bound-shadow-probe-20261010-'+version)
    for source in sorted(source_root.iterdir()):
        assert source.is_file(),'Only explicit flat source/preparation metadata directory is selected.'
        assert source.suffix in ['.lean','.json','.txt','.md','.py','.diff']
        copy(source,'source-'+version+'/'+source.name,role='exact historical source-only preparation')

# Preserve the imported module's reconstructible text; never copy its .olean.
r6root=REPO/'verification/linux-memory-time-20261010/whole/r6-completed'
r6manifest=load(r6root/'archive-manifest.json')
for spec in r6manifest['files']:
    if spec['decompressed_sha256'] in {
        '5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2',
        '14d359e1ba8336bc81d4722a7030a073ea78ffad523168b616af6f42840ddc05',
        '0618216894744f91d73330883af75eafe6937a8a871dd4cc385ebdaf32982e24',
        'e77513b7751460054be21697d06b5ffff142d109b65b131e392aa568ccf22378',
        'ec3cc48754945e0fb7361bd88edced444bd8a491fce20bc6452b4a465c61afbf',
        'db28df608ce9dac67b5f94798beaa1ca9c35f28e92f49e1068cd6f30796bfd79'}:
        names={
            '5227a25ea2c5f18c83e0a85c756e34ec9a0176a1ba9d1cd5f5556aab836ba7a2':'source/Solution/Candidate.lean.gz',
            '14d359e1ba8336bc81d4722a7030a073ea78ffad523168b616af6f42840ddc05':'source/ChallengeDeps.lean.gz',
            '0618216894744f91d73330883af75eafe6937a8a871dd4cc385ebdaf32982e24':'source/ChallengeDeps/CandidateSpec.lean.gz',
            'e77513b7751460054be21697d06b5ffff142d109b65b131e392aa568ccf22378':'source/Challenge/Candidate.lean.gz',
            'ec3cc48754945e0fb7361bd88edced444bd8a491fce20bc6452b4a465c61afbf':'config.json.gz',
            'db28df608ce9dac67b5f94798beaa1ca9c35f28e92f49e1068cd6f30796bfd79':'whole_candidate_native_driver_20261010.py.gz'}
        row={'bytes':spec['gzip_bytes'],'sha256':spec['gzip_sha256'],'raw_bytes':spec['decompressed_bytes'],'raw_sha256':spec['decompressed_sha256']}
        copy(r6root/spec['path'],'dependency-source/r6/'+names[spec['decompressed_sha256']],row,'exact frozen dependency source/config/driver only; no runtime artifact')
copy(REPO/'verification/linux-memory-time-20261010/am/environment/linux_cgroup_resource_harness_v3_20261010.py',
    'dependency-source/runtime/linux_cgroup_resource_harness_v3_20261010.py',
    {'bytes':17179,'sha256':'e192787f00ea5ceb0c77a06969bb832136b751337a475dd0e63619743f4d24ec'},
    'exact already-published V3 harness source text; not executed')
for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
    copy(REPO/name,'dependency-source/project/'+name,role='pinned project environment source metadata')

run_rows=[]
for run in handoff['runs']:
    ledger=load(Path(run['ledger']['path']));raw=load(Path(run['result']['path']))
    log=Path(run['process_log']['path']).read_text(encoding='utf-8')
    native='owner-r3' if 'native-r3' in run['run_id'] else 'owner-r2'
    variant='original' if run['source_version']=='original_source_r1' else 'explicit'
    tasks=load(OUT/native/variant/'records/worker-tasks.json')
    assert isinstance(tasks,list)
    assert raw['inputs_before']==raw['inputs_after'] and raw['inputs_unchanged'] is True
    assert raw['log_sha256']==sha(log.encode('utf-8'))
    assert ledger['dependency_family']==owners['owner-r2'].get('dependency_family',ledger['dependency_family'])
    plan=load(OUT/native/'plan.json')
    assert ledger['plan_sha256']==sha((OUT/native/'plan.json').read_bytes())
    assert ledger['dependency_family']==plan['dependency_family']
    for name,wanted in plan['source_bindings'].items():assert raw['inputs_before'].get(name)==wanted
    match=re.search(r'PRIMITIVE_PROBE_BEGIN (\d+).*PRIMITIVE_PROBE_END (\d+)',log,re.S)
    assert match
    body=(int(match.group(2))-int(match.group(1)))/1000
    successful=raw['proof_succeeded'] is True
    if successful:
        assert 'PROBE_TYPE_IDENTICAL true' in log and 'ORIGINAL_TARGET_PRESENT false' in log
        ax=re.search(r'PROBE_STANDARD_AXIOMS #\[([^\]]+)\]',log)
        assert ax and {x.strip() for x in ax.group(1).split(',')}==STD
        assert 'sorryAx' not in log
        closure=int(re.search(r'PROBE_CLOSURE_CHECKED (\d+)',log).group(1))
        assert ledger['fresh_same_type_standard_axioms_no_original_target'] is True
    else:
        assert ':43:8: error: Type mismatch' in log and 'sorryAx' in log
        assert not ledger['compiler_artifacts_after'] and not ledger['audit_artifacts_after']
        closure=None
    for role,key in [('ledger','ledger'),('result','result'),('process','process_log')]:
        spec=run[key]
        suffix='.log' if role=='process' else '.json'
        copy(spec['path'],'runs/'+run['run_id']+'/'+role+suffix+'.gz',spec,'normalized exact-byte completed '+role,compressed=True)
    fields=['actual_exit_code','resource_fit','sampled_tree_peak_pss_bytes','cgroup_peak_bytes',
            'outside_cgroup_peak_pss_bytes','timeout','oom_kill_count','sampled_tree_peak_swap_bytes','boot_id',
            'compiler_artifacts_after','audit_artifacts_after','dependency_family']
    row={k:ledger.get(k) for k in fields}
    row.update({'run_id':run['run_id'],'source_version':run['source_version'],'proof_succeeded':successful,
        'owned_worker_elapsed_seconds':raw['elapsed_seconds'],'cold_preparation_seconds':raw['scoped_eviction']['elapsed_seconds'],
        'phase_total_seconds':ledger['actual_phase_total_wall_seconds'],'recorded_body_marker_span_seconds':body,
        'successful_body_marker_seconds':body if successful else None,
        'body_failure_time_excluded_from_speed_comparison':not successful,
        'lean_tasks':tasks,'actual_lean_command_sum_seconds':round(sum(x['elapsed_seconds'] for x in tasks),3),
        'fresh_same_type_standard_axioms_and_no_original_target':successful,'checked_closure_constants':closure,
        'axioms':sorted(STD) if successful else ['sorryAx observed during failed elaboration; no accepted proof'],
        'raw_log_archive':'runs/'+run['run_id']+'/process.log.gz',
        'compiler_artifact_bytes_in_packet':False})
    run_rows.append(row)
baseline,failed,repaired=run_rows
assert (baseline['owned_worker_elapsed_seconds'],repaired['owned_worker_elapsed_seconds'])==(29.763,29.677)
assert (baseline['actual_lean_command_sum_seconds'],repaired['actual_lean_command_sum_seconds'])==(29.110,29.361)
assert (baseline['successful_body_marker_seconds'],repaired['successful_body_marker_seconds'])==(.875,.528)
assert baseline['boot_id']!=repaired['boot_id'] and baseline['boot_id']==failed['boot_id']
assert baseline['dependency_family']==repaired['dependency_family']
assert sha((REPO/'submission/proof/Solution.lean').read_bytes())==ORIGINAL_SHA
summary={'status':'COMPLETED_SHADOW_PROOFS_TWO_PASS_ONE_SOURCE_ERROR_NOT_ADOPTED',
    'completed_handoff_sha256':HANDOFF_SHA,'runs':run_rows,
    'successful_pair_observations':{'owned_worker_elapsed_seconds_saved':.086,
        'actual_lean_command_sum_seconds_increase':.251,'body_marker_seconds_saved':.347,
        'pss_bytes_increase':repaired['sampled_tree_peak_pss_bytes']-baseline['sampled_tree_peak_pss_bytes'],
        'cross_boot_single_pair':True,'uninterrupted_same_boot_controlled_pair':False},
    'timing_field_scope':{'owned_worker_elapsed':'V3 owned process elapsed includes driver/bindings/cleanup and compilation plus audit, rather than pure Lean task sums.',
        'actual_lean_command_sum':'Recorded task elapsed fields summed; imports included. Original 26.190+2.920; repaired 26.403+2.958.',
        'body_marker_span':'Per-process BEGIN/END monotonic marker span after the imported module; only a successful proof span enters comparison.',
        'phase_total':'Outer completed phase includes cold preparation and supervision.'},
    'owner_terminology_correction':'Immutable owner analysis calls 0.086 worker_plus_audit savings; interpret as owned-worker elapsed. Pure Lean task sum increased by 0.251 seconds.',
    'dependency_scope':'Exact completed r6 source 5227a25e and artifact 10b3102a were reused; no runtime artifact was read or copied by this file-only archiver.',
    'scope_limits':['One successful comparison across different boots; fixed artifacts/cold preparation do not establish uninterrupted identical-host state.',
        'Both probes import the full post-module environment. Actual used-constant checks exclude the original target, but this is not in-situ prefix timing.',
        'Failure span 0.499 seconds is not successful proof timing; sorryAx is failed elaboration recovery, not an admitted new axiom.',
        'PSS increased slightly; no RAM improvement or stable overall gain is established.',
        'No whole candidate replacement, fresh whole compile, live-contract check, export/core/default-kernel/Nanoda replay or official acceptance is claimed.'],
    'formal_adoption':False,'candidate_modified':False,'r6_compile_resource_fit_remains':False,
    'live_contract_validated':False,'website_acceptance':False,'original_d52_unchanged':True,
    'independent_file_review_pending':True,'proof_execution_by_archiver':False}
json_write(OUT/'summary.json',summary)
json_write(OUT/'path-relocation.json',{'scope':'Absolute paths in immutable sources/producer metadata are historical origins, not clone-runnable paths.',
    'text_records':relocations,'runtime_dependencies':'Compiled runtime/tool/cache paths identify metadata bindings only. No binary/cache payload is shipped; reconstruct in a separate pinned environment before updating historical plans.'})
copy(Path(__file__),'provenance/archive_primitive_three_runs.py',role='file-only archive generator; no proof runner invocation')
json_write(OUT/'archive-bindings.json',{'status':'EXACT_TEXT_AND_SOURCE_BINDINGS_ONLY','files':bindings,
    'gzip_policy':'mtime0, no filename/comment/extra header, one complete bounded member; existing gzip bytes preserved, newly compressed copies level6',
    'producer_manifests_preserved':{'owner-r2/archive-manifest.json':handoff['previous_pair_archive_manifest']['sha256'],
        'owner-r3/archive-manifest.json':handoff['repaired_archive_manifest']['sha256']},
    'no_binaries_or_runtime_cache':True,'no_Lean_WSL_or_runtime_execution':True})
readme='''# Primitive-bound shadow probe: three completed runs

The original proof passed. The first explicit rewrite failed at source line 43:
`simpa only [neg_mul] using hrev` did not match the normalized inequality. Its
error log prints `sorryAx` during failed elaboration; no compiler artifact or
fresh audit was produced. This is retained as a failed source experiment.
Replacing that line with `linear_combination hrev` produced a passing repaired
proof and a fresh audit of the identical type, standard three axioms and absence
of the original theorem from its used-constant closure.

| Recorded diagnostic | Original r1 | Failed explicit r1 | Repaired explicit r2 |
|---|---:|---:|---:|
| Lean exit / accepted proof | 0 / PASS | 1 / FAIL | 0 / PASS |
| Owned-worker elapsed, including driver/bindings/cleanup | 29.763 s | 26.005 s | 29.677 s |
| Actual Lean command sum | 29.110 s | failed compile only | 29.361 s |
| Successful checked-body marker span | 875 ms | not applicable | 528 ms |
| Peak sampled process-tree PSS | 7,129,774,080 B | 7,019,896,832 B | 7,151,198,208 B |
| Fresh closure constants checked | 9,492 | none | 9,509 |

The owned-worker difference is only **0.086 seconds**, while the actual Lean
command sum increased **0.251 seconds** (26.190 + 2.920 versus 26.403 + 2.958).
The successful body-marker difference of 347 ms is one observation. The failed
499 ms span is excluded from proof-performance comparisons. PSS increased by
21,424,128 bytes; this does not establish a RAM improvement or stable overall
gain. The immutable owner's earlier timing label is interpreted precisely in
[summary.json](summary.json); its original analysis is preserved unchanged.

The successful original and failed r1 share boot
`6caf73ed-1ebc-467a-ba2a-dd9aa31b1417`; the repaired result used boot
`5122a683-459b-4584-8073-e57b69843ef0`. This is a single comparison across boots
with the same pinned dependencies, not an uninterrupted same-boot controlled
pair. Cold preparation is recorded separately (28.363 / 28.907 / 27.717 s).
The complete phase totals were 59.104 / 56.096 / 59.098 s. Separate memory peaks
are not added; caller/supervisor PSS outside the proof cgroup is recorded.

Both successful probes use only `propext`, `Quot.sound`, `Classical.choice`.
They import the exact completed r6 module, whose own memory gate remains failed.
They exclude a direct dependency on the original target but operate after the
whole imported module; they do not reproduce its command-prefix environment.
No replacement is adopted, no whole-file speedup is inferred, and no fresh
live-contract, export, Comparator/default replay, Nanoda or website acceptance
is asserted. The original public d52 submission remains unchanged.

[Original source preparation](source-r1/README.md) and
[repaired source preparation](source-r2/README.md) retain their historical
pre-run labels. [Original completed pair](owner-r2/archive-manifest.json),
[repaired completed record](owner-r3/archive-manifest.json), and
[completed handoff](provenance/completed-three-run-handoff.json) are immutable
producer snapshots. [Exact raw/compressed bindings](archive-bindings.json) and
[inventory](archive-manifest.json) cover every selected source/log and generated
record. [Reproduction scope](reproduction/README.md) explains the preserved
runner/plans and frozen dependency sources. No compiled binary or cache is
included. Absolute paths in retained input metadata are historical provenance;
[path-relocation.json](path-relocation.json) maps selected records to usable
packet-relative paths. File-only packaging did not run a compiler or verifier.
'''
(OUT/'README.md').write_text(readme,encoding='utf-8')
repro='''# Reproduction inputs and limits

The packet preserves both historical source preparations, their generation
scripts, the exact three tested theorem sources, audit sources, two native
runner versions, plans and frozen bindings. The prepared-only metadata is
historical; the completed owner records and top-level summary state outcomes.

- [Original/failed plan](../owner-r2/plan.json) and
  [runner](../owner-r2/primitive_bound_shadow_driver_20261010.py).
- [Repaired plan](../owner-r3/plan.json) and
  [runner](../owner-r3/primitive_bound_shadow_driver_20261010.py).
- [One-line repair diff](../source-r2/r1-to-r2.diff) and
  [four-line original-to-repaired proof diff](../source-r2/four-line-body.diff).
- [Repaired frozen bindings](../owner-r3/frozen-input-manifest.json) and
  [original frozen bindings](../provenance/frozen-r2-input-manifest.json).
- [Exact imported r6 source](../dependency-source/r6/source/Solution/Candidate.lean.gz),
  [frozen r6 config](../dependency-source/r6/config.json.gz),
  [whole runner text](../dependency-source/r6/whole_candidate_native_driver_20261010.py.gz),
  and project [Lean pin](../dependency-source/project/lean-toolchain),
  [package definition](../dependency-source/project/lakefile.toml),
  [dependency pins](../dependency-source/project/lake-manifest.json).

The four frozen r6 source texts are included as exact gzip payloads, including
ChallengeDeps and the generated historical CandidateSpec/Challenge. They use
the historical 6735015/10000000 current-record contract, not the observed new
live record. The `.olean` family is bound in the plans and completed records;
its bytes are deliberately absent. All cache/package paths are historical.

The exact [V3 scoped-cache harness source](../dependency-source/runtime/linux_cgroup_resource_harness_v3_20261010.py)
matches both plans' harness binding e192787f…f4d24ec and is included as text.
These runners depend on the original scoped-cache harness and runtime layout,
pinned compiler, matching r6 dependency artifacts and isolated resource setup.
The source/config/runner texts are evidence, not a portable one-command clone
recipe. Reproduction requires a separately prepared pinned environment and
explicit regenerated path bindings; editing paths changes a plan hash and must
be documented. No script here was executed during packaging. The tested flags
were -j4 and --tstack=32768, with a 240-second per-probe guard and a 4 CPU/8 GiB/
no-swap proof cgroup. Imported pages were checked cold; outer caller memory and
cold-preparation work remain separate. This does not establish official sandbox
fit. Source generation or file-hash checks alone do not verify a proof.
'''
(OUT/'reproduction').mkdir()
(OUT/'reproduction/README.md').write_text(repro,encoding='utf-8')
files={p.relative_to(OUT).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
       for p in sorted(OUT.rglob('*')) if p.is_file()}
json_write(OUT/'archive-manifest.json',{'status':summary['status'],'manifest_self_excluded':True,
    'completed_handoff_sha256':HANDOFF_SHA,'files':files,'selected_completed_owner_payloads':30,
    'producer_manifests_preserved_byte_identically':2,'original_public_d52_unchanged':True,
    'scope':'File-only selected text/source/log archive; no compiler, runtime/cache/binary copy, formal adoption or public mutation.'})
print(json.dumps({'packet':str(OUT),'manifest_sha256':sha((OUT/'archive-manifest.json').read_bytes()),
    'files':len(files)+1,'bytes_including_manifest':sum(x['bytes'] for x in files.values())+(OUT/'archive-manifest.json').stat().st_size,
    'bindings':len(bindings),'status':summary['status']},indent=2))
