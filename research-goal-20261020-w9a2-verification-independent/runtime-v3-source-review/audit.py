"""Read/hash/AST only; no DLL load, PE rescan, SDK member walk or assembler run."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
V2=ROOT/'research-goal-20261020-w9a2-runtime-closure-v2'
V3=ROOT/'research-goal-20261020-w9a2-runtime-closure-v3'
SEEN={}


def sha(raw):return hashlib.sha256(raw).hexdigest()


def read(path):
    raw=path.read_bytes();key=path.resolve().relative_to(ROOT.resolve()).as_posix()
    val={'bytes':len(raw),'sha256':sha(raw)}
    assert SEEN.setdefault(key,val)==val,key
    return raw


def manifest(path,expected):
    raw=read(path);assert sha(raw)==expected
    rows=json.loads(raw)['files'];assert len(rows)==len({r['path']for r in rows})
    for row in rows:
        p=(path.parent/row['path']).resolve();assert p.is_relative_to(path.parent.resolve())
        actual=read(p);assert len(actual)==row['bytes']and sha(actual)==row['sha256']
    return rows


def main():
    m2=manifest(V2/'prepared-files.json','868fc97c702f8918d7b7fb8506334af7cad3b06050cb017521021ffc26d6b545')
    m3=manifest(V3/'prepared-files.json','be1227fe2606b4a8cb22a9bbeecec93fcc39eac10df96a856d804b61b6c70613')
    src2,src3=read(V2/'assemble.py'),read(V3/'assemble.py')
    hash2,hash3=read(V2/'cache_binding.py'),read(V3/'cache_binding.py')
    assert sha(src2)=='276107a5c4baecb8e8dccc94e0bd127132ede9cf2b879054c4a1d19da6c30158'
    assert sha(src3)=='cc7ca38250d42c74ef25f3d68dabc536d75e3f2c8557fda482375005b29ddaa3'
    assert sha(hash2)=='76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62'
    assert sha(hash3)=='6b4ff6cde5c64c0d12a37a51728c04a31acc5779ad8d0a4050f09ce52c18edf5'
    diff=''
    for name,a,b in [('assemble.py',src2,src3),('cache_binding.py',hash2,hash3)]:
        ast.parse(a);ast.parse(b)
        diff+=''.join(difflib.unified_diff(a.decode().splitlines(keepends=True),b.decode().splitlines(keepends=True),
            fromfile='v2/'+name,tofile='v3/'+name))
    assert diff.replace('\r\n','\n')==read(V3/'v2-to-v3.diff').decode().replace('\r\n','\n')
    scan=json.loads(read(V3/'sdk-export-scan.json'))
    gate=json.loads(read(V3/'gate-template.json'))
    assert gate['authorized']is False and gate['allow_compiler_main']is False and gate['allow_export_or_kernel_main']is False
    prior_path=ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v2/official-sdk-check.json'
    prior_raw=read(prior_path);assert sha(prior_raw)=='f052fabe7dad7ba4962056ffdbed4a1c63c7061b4abffcf51a304da1db49e373'
    prior=json.loads(prior_raw)
    assert prior['all_selected_members_identical']is True and prior['archive_sha256']=='022576004ed8a4fc81ee8d375419064b54d4475931429d989519fd847ee053f6'
    selected={row['path'].casefold():row for row in prior['selected_members']}
    assert len(selected)==len(prior['selected_members'])==13951
    assert scan['SDK_archive_check']['sha256']==sha(prior_raw)and len(scan['DLLs'])==9
    exports=[]
    for row in scan['DLLs']:
        saved=selected[row['path'].casefold()]
        assert all(saved[key]==row[key]for key in ['bytes','sha256','resolved_path'])
        exports.extend((Path(row['path']).name,entry)for entry in row['selected_exact_exports'])
    assert len(exports)==2 and {entry['name']for _,entry in exports}=={'lean_byte_array_hash','lean_string_hash'}
    assert all(name=='libInit_shared.dll'and entry['forwarder']is None for name,entry in exports)
    assert gate['reuse_previous_sdk_archive_check']['sha256']==sha(prior_raw)
    assert gate['previous_sdk_archive_component_accepted']is True
    before=dict(SEEN)
    for name in list(before):read(ROOT/name)
    report={'scope':'Independent static runtime v3 delta and existing SDK component receipt metadata review only',
        'status':'PASS_STATIC_EXECUTION_REQUIRED','v2_manifest_rows':len(m2),'v3_manifest_rows':len(m3),
        'input_count':len(before),'input_before_after_identical':True,'inputs':before,
        'assembler_sha256':sha(src3),'helper_sha256':sha(hash3),'actual_source_diff_matches_frozen_patch':True,
        'DLL_selection':'Both exact direct C exports are recorded only in libInit_shared.dll by the pinned pure PE scan; code now loads and checks that exact path.',
        'prior_actual_archive_selected_members':13951,'nine_scan_DLL_metadata_matches_prior_actual_archive_check':True,
        'component_reuse_scope':'Actual completed archive-member equality component from a later-failed setup; not a claim that the old whole setup passed.',
        'revalidation_requirements':'New root gate accepts this component; current archive hard SHA and every selected member SHA/size/resolved path are rechecked; selected sets must be exactly equal. Tar fallback remains.',
        'remaining_known_deterministic_delta_blockers':[],'assembler_or_hash_API_or_DLL_loads_by_reviewer':0,
        'PE_rescans_by_reviewer':0,'SDK_member_file_walks_by_reviewer':0,'compiler_export_kernel_runs_by_reviewer':0,
        'actual_full_runtime_closure_accepted_by_this_report':False,'round_counter_changes':0}
    with(HERE/'review.json').open('x',encoding='utf-8',newline='\n')as stream:json.dump(report,stream,ensure_ascii=False,indent=2);stream.write('\n')
    print(json.dumps({k:report[k]for k in['status','input_count','assembler_sha256','helper_sha256','prior_actual_archive_selected_members']}))


if __name__=='__main__':main()
