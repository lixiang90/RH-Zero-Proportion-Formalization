"""Independent frozen-source and existing ordinary receipt audit; no proof run."""
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
D = ROOT/'research-goal-20261020-w9a2-delivery'
V0,V5 = D/'draft-v0',D/'draft-v5'
SEEN = {}
MODULES = ['Core','Graph','Localization','Counting','Final']
NAMES = ['StructuralW9A220261020.'+n for n in MODULES]
ALLOWED = {'propext','Classical.choice','Quot.sound'}


def sha(raw):return hashlib.sha256(raw).hexdigest()


def read(path):
    raw=path.read_bytes();key=path.resolve().relative_to(ROOT.resolve()).as_posix()
    row={'bytes':len(raw),'sha256':sha(raw)}
    assert SEEN.setdefault(key,row)==row,key
    return raw


def load(path):return json.loads(read(path))


def manifest(path,expected):
    raw=read(path);assert sha(raw)==expected
    obj=json.loads(raw);rows=obj['files']
    assert len(rows)==len({r['path']for r in rows})
    for row in rows:
        target=(path.parent/row['path']).resolve();assert target.is_relative_to(path.parent.resolve())
        value=read(target);assert len(value)==row['bytes']and sha(value)==row['sha256']
    return obj


def statement(raw,name):
    hits=re.findall(rb'(?ms)^theorem '+name.encode()+rb'\s*:\s*(.*?)\s*:= by',raw)
    assert len(hits)==1,name
    return hits[0]


def axioms(raw):
    text=raw.decode();rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
    out={name:[s.strip()for s in values.split(',')if s.strip()]for name,values in rows}
    assert len(out)==len(rows)and all(set(v)<=ALLOWED for v in out.values())
    assert 'error:'not in text
    return out


def main():
    v0=manifest(V0/'files.json','71dce9f3714334dd1f525f037f18ee1c6a4ba25a2b3ac9838df49cc6934879f7')
    v5=manifest(V5/'files.json','497f905f1742380a38c8f5c93ac293d9a0d67717ea5e89e43067751631fe1527')
    outer=manifest(D/'draft-v5-prepared-files.json','4f6bc4b1a777cd92c8e417fbcbfe3563622a23d656adda2f8a61b823bf0d8cc9')
    packages=[('core-repair-v1','9aafa909450a60295a0864982d8f3f596217fba54c8e04eeeb3a21eede8f5114'),
        ('graph-repair-v2','5e5162d27f6e99347c425b954135db00f4e729b53ba4a430c2b26b4a8eb186a9'),
        ('localization-repair-v1','e68e29c644e019de387e8570db5c86c9af80cc9fc9a13224e928c6e3d2f1fd31'),
        ('final-repair-v1','c9a946281b01f9f8d1159345a475a831eacc92fea7e9e1ca7bf13a1332f525e8')]
    for label,digest in packages:manifest(ROOT/('research-goal-20261020-w9a2-'+label)/'files.json',digest)
    c0=b'      simpa only [qTargetFrom, hs, \xe2\x86\x93reduceIte] using h\n'
    c1=c0.replace(b'hs, ',b'hs, Bool.false_eq_true, ')
    g0=b'  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring\r\n'
    g1=g0.replace(b'<;> ring',b'<;> (try simp only [Fin.reduceFinMk]) <;> ring')
    l0=b'      simpa only [reverse8] using (le_of_lt (lt_of_not_ge ho))\n'
    l1='      change g 7 ≤ g 0\n      exact le_of_lt (lt_of_not_ge ho)\n'.encode()
    f0='''    · simpa only [StructuralW9A220261020.Counting.leftGaps,
        StructuralW9A220261020.Graph.leftGaps] using hs
    · simpa only [StructuralW9A220261020.Counting.rightGaps,
        StructuralW9A220261020.Graph.rightGaps] using ht
'''.encode()
    f1='''    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.leftGaps g) s
      exact hs
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.rightGaps g) t
      exact ht
'''.encode()
    changes={'Core':(c0,c1),'Graph':(g0,g1),'Localization':(l0,l1),'Final':(f0,f1)}
    repaired_inputs={
        'Core':'research-goal-20261020-w9a2-core-repair-v1/canonical-full/StructuralW9A220261020/Core.lean',
        'Graph':'research-goal-20261020-w9a2-graph-repair-v2/StructuralW9A220261020/Graph.lean',
        'Localization':'research-goal-20261020-w9a2-localization-repair-v1/StructuralW9A220261020/Localization.lean',
        'Counting':'StructuralW9A220261020/Counting.lean',
        'Final':'research-goal-20261020-w9a2-final-repair-v1/StructuralW9A220261020/Final.lean'}
    sources=[]
    for name in MODULES:
        rel='frozen-inputs/StructuralW9A220261020/'+name+'.lean'
        old,new=read(V0/rel),read(V5/rel)
        assert read(ROOT/('StructuralW9A220261020/'+name+'.lean'))==old
        assert new==read(ROOT/repaired_inputs[name])
        if name in changes:
            a,b=changes[name];assert old.count(a)==new.count(b)==1
            assert old.replace(a,b)==new and new.replace(b,a)==old
        else:assert old==new
        sources.append({'module':'StructuralW9A220261020.'+name,'bytes':len(new),'sha256':sha(new),
            'change_bytes':len(new)-len(old),'all_other_source_bytes_equal':True})
    flat0,flat5=read(V0/'Solution.lean'),read(V5/'Solution.lean')
    forward,back=flat0,flat5
    for a,b in changes.values():
        assert forward.count(a)==back.count(b)==1
        forward=forward.replace(a,b);back=back.replace(b,a)
    assert forward==flat5 and back==flat0 and len(flat5)-len(flat0)==66
    assert len(flat5)==1830001 and sha(flat5)=='650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13'
    for row in v0['files']:
        rel=row['path']
        if rel.startswith('trusted/')or rel.startswith('frozen-inputs/')and not rel.startswith('frozen-inputs/StructuralW9A220261020/'):
            assert read(V0/rel)==read(V5/rel)
    runner=read(ROOT/'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py')
    assert sha(runner)=='92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
    headers=[ast.literal_eval(n.value)for n in ast.parse(runner).body if isinstance(n,ast.Assign)
        and any(isinstance(t,ast.Name)and t.id=='HEADER'for t in n.targets)]
    assert len(headers)==1
    external,parts,moves=[],[],[]
    for name in NAMES:
        rel=name.replace('.','/')+'.lean';raw=read(V5/'frozen-inputs'/rel);body=[]
        for line in raw.splitlines(keepends=True):
            if line.startswith(b'import '):
                target=line[7:].strip().decode();internal=target in NAMES
                assert not internal or NAMES.index(target)<NAMES.index(name)
                if not internal:external.append(line)
                moves.append({'source':rel,'import':target,'internal':internal,
                    'removed_line_bytes':len(line),'removed_line_sha256':sha(line)})
            else:body.append(line)
        parts.append((name,b''.join(body)))
    rebuilt=headers[0]+b'import ChallengeDeps.CandidateSpec\n'+b''.join(external)+b'\n';segments=[]
    for name,body in parts:
        rebuilt+=('\n/- BEGIN FLATTENED MODULE '+name+' -/\n').encode();start=len(rebuilt);rebuilt+=body
        segments.append({'module':name,'start':start,'end':len(rebuilt),'retained_non_import_sha256':sha(body)});rebuilt+=b'\n'
    wrapper=read(V5/'frozen-inputs/public-wrapper.lean.txt');rebuilt+=b'\n'+wrapper;assert rebuilt==flat5
    plan=load(V5/'candidate-parameters.json');assert plan['body_segments']==segments and plan['import_lines_moved']==moves
    official=read(V5/'frozen-inputs/Challenge.Candidate.lean');public=[]
    for name in ['candidate_strict_improvement','candidate_critical_line_bound','candidate_critical_line_bound_cumulative']:
        s=statement(flat5,name);assert s==statement(flat0,name)==statement(wrapper,name)
        assert b''.join(s.split())==b''.join(statement(official,name).split());public.append({'name':name,'type_sha256':sha(s)})
    splitroot=ROOT/'research-goal-20261020-w9a2-formal-static-review'
    split=load(splitroot/'split-audit.json');prefix=read(splitroot/'development-split/StructuralW9A220261020/Prefix.lean')
    core=read(ROOT/'research-goal-20261020-w9a2-core-repair-v1/development-split/StructuralW9A220261020/Core.lean')
    ending,prologue=split['prefix_added_closing_command'].encode(),split['suffix_prologue'].encode()
    assert prefix.endswith(ending)and core.startswith(prologue)
    assert prefix[:-len(ending)]+core[len(prologue):]==read(V5/'frozen-inputs/StructuralW9A220261020/Core.lean')
    archive_pins={0:'7269533eb0caa968b9fdbf496f7da96bd54639e384cac9bd96cad4646d91c1cf',
        1:'272ddcae631c5380a46581e409300dbc0d27ad68f2562a951896ea6fd16660cc',
        3:'b18f012d4883d322a45a3305955e1a27bbc60339974dad2b4d9299eed79104ca',
        4:'850c47ebfaa520b9760f9b7cc4f0fe5de340f64f475a6e5668e0466ba85bd009',
        5:'d01330c8f0a39df81c7095f49db8e2afa8f6fe40d3683ea6f155b232df371a5d'}
    allroots={};passes=[]
    selected=[(0,'Prefix',prefix),(1,'Core',core),(3,'Graph',read(ROOT/repaired_inputs['Graph'])),
        (4,'Localization',read(ROOT/repaired_inputs['Localization'])),(4,'Counting',read(ROOT/repaired_inputs['Counting'])),
        (5,'Final',read(ROOT/repaired_inputs['Final']))]
    done=set()
    for stage,name,source in selected:
        archive=ROOT/f'research-goal-20261020-w9a2-ordinary-v{stage}-terminal'
        if stage not in done:manifest(archive/'files.json',archive_pins[stage]);done.add(stage)
        job=ROOT/f'tmp/w9a2-20261020/candidate-ordinary-v{stage}'
        base='StructuralW9A220261020_'+name
        receipt=load(archive/(base+'.receipt.json'));log=read(archive/(base+'.log'))
        assert read(job/(base+'.receipt.json'))==read(archive/(base+'.receipt.json'))
        assert read(job/(base+'.log'))==log and read(job/(base+'.lean'))==source
        assert receipt['exit_code']==0 and receipt['ordinary_compile_passed']is True and receipt['source_unchanged']is True
        assert receipt['source_sha256']==sha(source)and receipt['log_sha256']==sha(log)
        output=job/'lib/StructuralW9A220261020'/(name+'.olean');assert sha(read(output))==receipt['olean_sha256']
        observed=axioms(log);assert receipt['observed_axioms']==observed and set(receipt['expected_roots'])==set(observed)
        assert not(set(allroots)&set(observed));allroots.update(observed)
        assert (receipt['axiom_audit_passed']is True)if observed else(receipt['axiom_audit_passed']is None)
        terminal=load(archive/'terminal.json')
        attestation=load(archive/'root-parent-exit-attestation.json')if(archive/'root-parent-exit-attestation.json').exists()else load(archive/'files.json')
        assert attestation['actual_parent_exit_code']==(0 if stage==5 else 1)
        passes.append({'stage':stage,'module':receipt['module'],'source_sha256':sha(source),
            'olean_sha256':receipt['olean_sha256'],'elapsed_seconds':receipt['elapsed_seconds'],
            'module_exit_code':0,'whole_stage_passed':terminal['passed'],
            'root_attested_actual_parent_exit_code':attestation['actual_parent_exit_code'],
            'receipt_path':str((archive/(base+'.receipt.json')).relative_to(ROOT))})
    assert len(allroots)==12 and len(passes)==6
    before=dict(SEEN)
    for name in list(before):read(ROOT/name)
    report={'scope':'Completed modular Lean proof and frozen draft static byte review only; not a cold single-file or independent-kernel acceptance',
        'status':'PASS_MODULAR_FORMAL_AND_STATIC_SOURCE','input_count':len(before),'input_before_after_identical':True,'inputs':before,
        'draft_v5_bytes':len(flat5),'draft_v5_sha256':sha(flat5),'source_limit_bytes':2000000,'source_slack_bytes':2000000-len(flat5),
        'draft_v0_to_v5_total_proof_only_delta_bytes':66,'four_repairs_bidirectional_exact':True,'all_other_source_bytes_unchanged':True,
        'frozen_original_canonical_files_unchanged':True,'source_modules':sources,'independent_flatten_reconstruction_exact':True,
        'trusted_wrapper_templates_unchanged':True,'three_public_types':public,
        'Prefix_plus_development_Core_exact_full_Core_projection':True,
        'selected_existing_ordinary_module_passes':passes,'actual_twelve_printed_roots':allroots,'all_roots_standard_axioms_only':True,
        'Final_actual_summed_strict_dyadic_cumulative_modular_Lean_passed':True,
        'candidate_olean_reuse_scope':'Development only; the selected PASS artifacts span five actual batches, four whole batches failed later modules.',
        'cold_single_file_passed':False,'three_public_wrapper_theorems_compiled_in_production':False,
        'Comparator_passed':False,'default_kernel_replay_passed':False,'independent_NanoDa_passed':False,
        'unified_3200s_passed':False,'fresh_record_rechecked_by_this_report':False,'official_accepted':False,
        'compiler_export_kernel_search_runs_by_reviewer':0,'round_counter_changes':0}
    with(HERE/'review.json').open('x',encoding='utf-8',newline='\n')as stream:json.dump(report,stream,ensure_ascii=False,indent=2);stream.write('\n')
    print(json.dumps({k:report[k]for k in['status','input_count','draft_v5_bytes','draft_v5_sha256','source_slack_bytes','all_roots_standard_axioms_only']}))


if __name__=='__main__':main()
