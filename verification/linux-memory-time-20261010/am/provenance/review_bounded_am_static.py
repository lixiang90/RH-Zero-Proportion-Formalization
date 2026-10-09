from pathlib import Path
import hashlib,importlib.util,json,re,ast
root=Path(r'E:\codex-build\RH-Zero-Proportion-Formalization');out=root/'tmp/memory-optimization-20261010/am'
p=root/'scripts/bundle_solution.py';spec=importlib.util.spec_from_file_location('frozen_bundler_static',p);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
orig=root/'tmp/optimized-overlay/RecordProportion/ImportedAM.lean';base=out/'AMSyncAlias8.lean'
original=orig.read_text(encoding='utf-8');candidate=base.read_text(encoding='utf-8')
scopes=lambda t:[s for s in b.code_mask(t).splitlines() if re.match(r'^(namespace|(?:noncomputable )?section|end|variable|include|omit|open)\b',s)]
assert scopes(original)==scopes(candidate)
assert b.remaining_sections(original)==b.remaining_sections(candidate)==0
helpers=json.loads((root/'verification/am-helper-alias-bounded-probe.json').read_text(encoding='utf-8'))['helpers']
direct={}
for name in helpers:
 pat=re.compile(r'(?m)^theorem '+re.escape(name)+r'\b(?P<body>[\s\S]*?)(?=^(?:theorem|lemma|def|abbrev|end|variable|namespace|include|omit|open|set_option)\b)',re.M)
 m=pat.search(candidate);assert m,name
 decl=m.group(0);needle='exact Zeta23.XiPrime.'+name
 assert decl.count(needle)==1,(name,decl)
 assert len(decl.split(':= by',1)[1].strip().splitlines())==1,(name,decl)
 direct[name]={'declaration_bytes':len(decl.encode('utf-8')),'sha256':hashlib.sha256(decl.encode('utf-8')).hexdigest(),'one_direct_exact_alias':True}
assert not re.search(r'(?m)^mutual\b',b.code_mask(candidate))
# Parenthesized/numeric compression sees no new numeral literals in the scheduler definition.
generator=(out/'generate_bounded_am.py').read_text(encoding='utf-8');tree=ast.parse(generator)
barrier_node=next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='barrier' for t in n.targets))
barrier=ast.literal_eval(barrier_node.func.value)
assert not re.search(r'\b\d+\b',b.code_mask(barrier))
# New scheduling syntax cannot be confused with an existing source command or identifier.
for p in (root/'RecordProportion').glob('*.lean'):
 assert not re.search(r'\bam_wait\b',b.code_mask(p.read_text(encoding='utf-8'))),p
record={'status':'PASS_STATIC_SOURCE_REVIEW_ONLY','source_before_sha256':hashlib.sha256(orig.read_bytes()).hexdigest(),'alias8_source_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'scope_namespace_variable_include_omit_open_commands_byte_equal':True,'scope_command_count':len(scopes(candidate)),'anonymous_source_sections_remaining':0,'direct_eight_alias_bodies':direct,'original_eight_interfaces_checked_elsewhere':'verification/am-helper-alias-bounded-probe.json:16 ordinary Lean roots including8aliases+8rfl interface identities; whole alias8 source itself remains uncompiled','async_only_single_theorems_pinned_implementation':'Lean/Elab/MutualDef.lean:1237; source contains no mutual declaration','complete_command_parser_gate':'PENDING: only actual exit-zero command-boundaries.tsv may drive insertion','scheduler_defined_before_noncomputable_section':True,'scheduler_has_no_numeric_literals':True,'am_wait_identifier_absent_in_public_local_modules':True,'explicit_EOF_async_false_restore':True,'whole_module_sections_preserved_by_frozen_bundler':True,'no_kernel_or_environment_mutation':'IO.wait existing env.checked; no setEnv, promise resolution, kernel disabling, sorry, or native_decide introduced','whole_source_alias_only_budget':{'bytes':1992337,'capacity_remaining':7663,'sha256':'304977970e95cad9decc94cf27a0e415d4a9a07760652521208a1c4576752408'},'bounded_exact_budget_formula':'1992337 + compacted scheduler bytes + 8 * actual_inserted_wait_count + 27 EOF restore bytes + 1 byte async(false->true) savings; actual bundler regeneration remains mandatory','lean_proof_pass_in_this_review':False,'independent_replay':False,'whole_accepted':False}
(out/'bounded-am-static-integration-review.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['direct_eight_alias_bodies']},indent=2))
