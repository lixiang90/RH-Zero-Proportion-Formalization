"""Capture source evidence only; no SDK API, compiler, assembler or proof run."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
SOURCES=[('tmp/lean-toolchain/src/lean/Lean/Setup.lean',180,192),
    ('tmp/lean-toolchain/src/lean/lake/Lake/Config/Package.lean',159,161),
    ('tmp/lean-toolchain/src/lean/Init/Data/Hashable.lean',32,35),
    ('tmp/lean-toolchain/src/lean/lake/Lake/Build/Trace.lean',168,170),
    ('research-goal-20261020-w9a2-runtime-closure-v3/assemble.py',232,237)]


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    rows=[]
    for rel,first,last in SOURCES:
        p=ROOT/rel;raw=p.read_bytes()
        rows.append({'path':rel,'bytes':len(raw),'sha256':sha(raw),'first_line':first,'last_line':last,
            'exact_excerpt':''.join(raw.decode().splitlines(keepends=True)[first-1:last])})
    assert 'abbrev PkgId := String' in rows[0]['exact_excerpt']
    assert 'Option PkgId' in rows[1]['exact_excerpt'] and 'origName.toString' in rows[1]['exact_excerpt']
    assert 'mixHash (hash a) 13' in rows[2]['exact_excerpt']
    assert 'mix nil <| mk <| hash a' in rows[3]['exact_excerpt']
    assert 'mix(name_hash("Zeta23"),13)' in rows[4]['exact_excerpt']
    for row in rows:
        raw=(ROOT/row['path']).read_bytes();assert len(raw)==row['bytes'] and sha(raw)==row['sha256']
    data={'scope':'Independent static type-directed diagnosis of actual runtime v3 Package.id? failure',
        'sources':rows,'input_before_after_identical':True,
        'diagnosis':'Package.id? is Option PkgId, and PkgId is String, while Module.name is Name. The old package-name expression incorrectly inserted Name.anonymous mixing before Option.some hashing.',
        'old_expression':'mix(1723, mix(name_hash("Zeta23"), 13))',
        'correct_expression':'mix(1723, mix(self.sdk_hash.string("Zeta23"), 13))',
        'Module_name_hash_change_required':False,'trace_or_cached_data_change_required':False,
        'supersedes_prior_review_specific_claim':'runtime-source-review legacy Package.id? formula endorsement only; the prior review assumed Option Name and missed Lean.PkgId := String.',
        'runtime_v3_files_modified':False,'actual_SDK_hash_calls_by_reviewer':0,'compiler_export_kernel_or_assembler_runs_by_reviewer':0,
        'corrected_formula_actual_runtime_control_pass_claimed':False,'round_counter_changes':0}
    with(HERE/'evidence.json').open('x',encoding='utf-8',newline='\n')as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'input_count':len(rows),'correct_expression':data['correct_expression'],'execution_count':0}))


if __name__=='__main__':main()
