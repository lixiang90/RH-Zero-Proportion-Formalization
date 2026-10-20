"""Static-only gate assembler diff/manifest audit; never imports the assembler."""
import ast
import difflib
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OLD=ROOT/'research-goal-20261020-w9a2-fullchain-gate-preparation'
NEW=ROOT/'research-goal-20261020-w9a2-fullchain-gate-preparation-v1'
SEEN={}


def sha(raw):return hashlib.sha256(raw).hexdigest()


def read(path):
    raw=path.read_bytes();key=path.resolve().relative_to(ROOT.resolve()).as_posix()
    row={'bytes':len(raw),'sha256':sha(raw)}
    assert SEEN.setdefault(key,row)==row,key
    return raw


def manifest(path,expected):
    raw=read(path);assert sha(raw)==expected
    data=json.loads(raw);rows=data['files']
    assert len(rows)==len({r['path']for r in rows})
    for row in rows:
        p=(path.parent/row['path']).resolve();assert p.is_relative_to(path.parent.resolve())
        value=read(p);assert len(value)==row['bytes']and sha(value)==row['sha256']
    return data


def main():
    oldmanifest=manifest(OLD/'prepared-files.json','cd24cfac979fb6bbb572903c4de02b84f172107dbbd88e5da8f961f7cbd3b89e')
    newmanifest=manifest(NEW/'prepared-files.json','e16ef51b40b0ed7618857095330724061801ae4cc364ce3a0622c7c0bec90da3')
    old,new=read(OLD/'assemble_gate.py'),read(NEW/'assemble_gate.py')
    assert sha(old)=='5ac8d7040eb48615fece34db7b4997c1fa2898ab23bda3f1f794f2e072a30242'
    assert sha(new)=='588c1812de91886e5fdfd14f44d3f75485f11ab06e552553b18968a747c1899c'
    exact=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),
        fromfile='frozen-v0/assemble_gate.py',tofile='prepared-v1/assemble_gate.py')).encode()
    assert exact==read(NEW/'exact-source-diff.patch')
    tree0,tree1=ast.parse(old),ast.parse(new)
    functions0={n.name:ast.dump(n,include_attributes=False)for n in tree0.body if isinstance(n,ast.FunctionDef)}
    functions1={n.name:ast.dump(n,include_attributes=False)for n in tree1.body if isinstance(n,ast.FunctionDef)}
    changed=[name for name in functions0 if functions0[name]!=functions1[name]]
    assert set(functions0)==set(functions1)and set(changed)=={'printed_axioms','ordinary_preflight'}
    other0=[ast.dump(n,include_attributes=False)for n in tree0.body if not isinstance(n,ast.FunctionDef)]
    other1=[ast.dump(n,include_attributes=False)for n in tree1.body if not isinstance(n,ast.FunctionDef)]
    assert other0==other1
    runner=ROOT/'research-goal-20261020-w9a2-verification-preparation-v1'
    manifest(runner/'prepared-files.json','3dc697cd99c9a38730b4e32cef02fd1f780f74ffeaa1512e6e52500d9e6e3e53')
    assert sha(read(runner/'run_verification.py'))=='92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
    formal=ROOT/'research-goal-20261020-w9a2-verification-independent/formal-completion/files.json'
    manifest(formal,'2db147ef0e6d26efece5645544e385c7d7d4106145cea4c2a92581222c9cb90e')
    before=dict(SEEN)
    for key in list(before):read(ROOT/key)
    report={'scope':'Independent static disabled-gate assembler authority/preflight review only',
        'status':'PASS_STATIC_NO_ASSEMBLER_EXECUTION',
        'old_manifest_rows':len(oldmanifest['files']),'new_manifest_rows':len(newmanifest['files']),
        'assembler_sha256':sha(new),'exact_supplied_diff_matches_actual_source_diff':True,
        'changed_function_names_only':changed,'all_other_function_and_module_AST_identical':True,
        'old_frozen_package_preserved':True,'input_count':len(before),'input_before_after_identical':True,'inputs':before,
        'resolved_blocker':'Historical failed Final sorryAx placeholders can be parsed and retained as rejected diagnostics, while all real PASS and selected proof roots remain restricted to ALLOWED.',
        'authority_boundary':'Produces only a disabled proposal. Root must separately review exact artifacts and authorize a new execution gate. JSON external-handle attestations remain an explicit root trust boundary.',
        'preflight_scope':'Per-source exact actual module PASS chain, source/olean/command/log/root matching, earlier PASS-only reused artifact paths, real whole-parent exits and fresh record; no cold production proof reused.',
        'runtime_scope':'Actual completed setup/parent exit0, source-bound closure with pinned executables and clean data/tool overlays; closure.files rebound by unchanged runner setup_runtime.',
        'production_contract':'Frozen runner unchanged: fresh source/spec/four ordinary compiles, two native exports, locked CoreAudit statement/deps/primitives/default Lean, serial Nano, unified 3200s and fsynced three receipts remain required.',
        'documentation_correction':'README copied example still names original preparation directory; use research-goal-20261020-w9a2-fullchain-gate-preparation-v1/assemble_gate.py with manifest e16ef51b40b0ed7618857095330724061801ae4cc364ce3a0622c7c0bec90da3.',
        'remaining_known_deterministic_code_blockers':[],'assembler_executions_by_reviewer':0,
        'compiler_export_kernel_runs_by_reviewer':0,'round_counter_changes':0,
        'actual_fullchain_proposal_assembled_by_this_report':False,'production_verification_accepted':False}
    with(HERE/'review.json').open('x',encoding='utf-8',newline='\n')as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({k:report[k]for k in['status','input_count','assembler_sha256','changed_function_names_only','remaining_known_deterministic_code_blockers']}))


if __name__=='__main__':main()
