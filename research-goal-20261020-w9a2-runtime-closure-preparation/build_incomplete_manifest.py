"""Merge read-only evidence into a v1-compatible INCOMPLETE closure candidate.

Never grants approval. No compiler/export/kernel/install/network subprocess.
Root must separately resolve missing provenance and observe actual setup exit0.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def load(p):return json.loads(Path(p).read_text(encoding='utf-8'))


def pin(p,role):
    p=Path(p).absolute();raw=p.read_bytes()
    return {'path':str(p),'resolved_path':str(p.resolve()),'bytes':len(raw),
            'sha256':hashlib.sha256(raw).hexdigest(),'role':role}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--write-incomplete-once',required=True,action='store_true')
    ap.add_argument('--output-name',required=True)
    args=ap.parse_args()
    if Path(args.output_name).name!=args.output_name:raise RuntimeError('Output must be one file name')
    output=HERE/args.output_name
    if output.exists():raise RuntimeError('Exclusive output already exists')
    inventory=load(HERE/'review-v1/runtime-file-inventory.json')
    elf=load(HERE/'evidence/WSL-ELF-loader-resolution.json')
    package_gate=load(ROOT/'research-goal-20261020-w9a2-runtime/trusted-setup-gate.json')
    files={row['path'].casefold():row for row in inventory['files']}
    nano=ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin'
    files[str(nano).casefold()]=pin(nano,'nanoda-existing-source-pinned-binary')
    for row in elf['files']:
        if row['path'].startswith('/mnt/e/'):continue
        windows=row['Windows_read_path']
        # Exact Linux target SHA is evidence; Windows runner will rehash via UNC.
        files[windows.casefold()]={'path':windows,'bytes':row['bytes'],'sha256':row['sha256'],
            'role':'ELF-loader-or-launcher-runtime','Linux_path':row['path'],
            'Linux_resolved_path':row['resolved_path']}
    sources=[]
    for package,names in [('Comparator',['Comparator.lean','Comparator/Axioms.lean',
                          'Comparator/Compare.lean','Comparator/Util.lean','Main.lean']),
                         ('lean4export',['Export.lean','Export/Parse.lean','Main.lean'])]:
        for name in names:
            row=pin(ROOT/'tmp'/package/name,'pinned-trusted-tool-source')
            row['logical_name']=package+'/'+name;sources.append(row)
            files[row['path'].casefold()]=row
    for p,role in [(ROOT/'tools/ComparatorCoreAudit.lean','locked-CoreAudit-source'),
                   (ROOT/'tmp/nanoda/Cargo.toml','nanoda-build-source'),
                   (ROOT/'tmp/nanoda/Cargo.lock','nanoda-dependency-lock')]:
        row=pin(p,role);files[row['path'].casefold()]=row
    result={'schema':'w9a2-trusted-runtime-closure-v1',
        'complete_source_bound_runtime_closure_verified':False,
        'user_proofs_compiled_or_reused_in_setup':False,
        'official_runtime_equivalence_claimed':False,
        'tool_commits':inventory['tool_commits'],
        'package_source_revisions':{Path(p['path']).name:p['actual_HEAD'] for p in inventory['package_git_identity_only']},
        'coreaudit_source_sha256':'7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2',
        'trusted_tool_sources':sources,'files':list(files.values()),
        'candidate_package_libs':[str((ROOT/p).absolute()) for p in package_gate['package_libs']],
        'interpreted_tool_libs':[str((ROOT/p).absolute()) for p in [
            'tmp/Comparator/.lake/build/lib/lean','tmp/lean4export/.lake/build/lib/lean']],
        'trusted_setup_receipt':{'path':'ROOT_MUST_SUPPLY_REAL_REVIEWED_SETUP_RECEIPT.json',
                                 'sha256':'ROOT_MUST_FILL'},
        'root_confirmed_setup_exit0':False,'candidate_pipeline_runs':0,
        'missing_evidence':[
            'Current source-bound Mathlib/Zeta23/package cache closure and all split olean/private/server/IR file pins; HEAD alone is insufficient',
            'Current source-bound Comparator/Export interpreted overlay artifact pins; source files and commits alone do not prove cached module provenance',
            'Final native exporter source-to-current-binary/SDK closure audit (historical same-hash receipts and link trace are archived evidence, not automatic approval)',
            'Static Windows API-set compatible-revision mapping needs root review; no native exporter was started to observe its actual loaded modules',
            '84 unresolved optional OS delay-import entries in broad static traversal remain documented; all ordinary imports resolved in this static model',
            'Python VCRUNTIME140 search ambiguity resolved by a separate actual current-Python loaded-path query, still needs binding into root review',
            'Genuine terminal exit0 of the root-owned trusted setup/review process and a new affirmative root gate'
        ]}
    with output.open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(result,stream,ensure_ascii=False,indent=2);stream.write('\n')
    print(json.dumps({'path':str(output),'sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
                      'complete_runtime_approved':False,'candidate_pipeline_runs':0}))


if __name__=='__main__':main()
