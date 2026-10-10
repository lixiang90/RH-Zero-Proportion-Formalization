#!/usr/bin/env python3
"""Archive explicitly completed Windows text records of a local whole-file attempt.

Do not execute until root supplies a completion handoff. This helper invokes no
compiler, verifier, subprocess, network or runtime-cache operation. It writes
only a fresh scratch packet and never edits the published Solution/preflight.
"""
from __future__ import annotations
import argparse, codecs, gzip, hashlib, json, re, struct, zlib
from pathlib import Path

PHASES = ('tools','contract','compile','deps','audit','challenge-export',
          'solution-export','core','nano')
WHOLE_PHASES = PHASES[1:]
STANDARD = {'propext','Quot.sound','Classical.choice'}
TARGETS = ('candidate_strict_improvement','candidate_critical_line_bound',
           'candidate_critical_line_bound_cumulative')
ORIGINAL_SHA = 'd52f013f7edcc8536a28ef3908e64a967e5b9184d6546952cb5a541dc6d65e8a'
ALLOWED_SUFFIXES = {'.json','.log','.txt','.csv','.md','.lean','.py','.ts','.toml','.sha256','.tsv'}
FORBIDDEN_SUFFIXES = ('.olean','.olean.private','.olean.server','.ir','.ir.sig',
    '.exe','.dll','.so','.a','.o','.obj','.lib','.pdb','.pyc','.pyo','.tar','.zip','.7z')
CREDENTIALS = {
 'GitHub token': re.compile(rb'(?:gh[pousr]_[A-Za-z0-9_]{20,}|github_pat_[A-Za-z0-9_]{20,})'),
 'secret API key': re.compile(rb'\bsk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{25,}'),
 'bearer header': re.compile(rb'(?i)authorization\s*:\s*bearer\s+[A-Za-z0-9_.~-]{20,}'),
 'private key': re.compile(rb'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----'),
 'AWS key': re.compile(rb'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b'),
 'credential URL': re.compile(rb'(?i)[?&](?:access_token|api_key|auth_token|password)=[A-Za-z0-9_.~%+-]{12,}')
}

def sha_file(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1_048_576),b''): h.update(chunk)
    return h.hexdigest()
def digest_bytes(blob): return hashlib.sha256(blob).hexdigest()
def load_json(path): return json.loads(path.read_text(encoding='utf-8-sig'))
def number(value): return value if isinstance(value,(int,float)) and not isinstance(value,bool) else None
def compact_sum(values):
    values = [v for v in values if number(v) is not None]
    return round(sum(values),3) if values else None
def safe_id(value):
    if not isinstance(value,str) or not re.fullmatch(r'[a-z0-9][a-z0-9-]{0,70}',value):
        raise ValueError('Record ids must be short lowercase hyphenated identifiers.')
    return value
def write_json(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
def payload_suffix(spec):
    value = {'path':spec} if isinstance(spec,str) else spec
    path = Path(value.get('logical_name',value['path']))
    if path.suffix.lower()=='.gz': path = Path(path.stem)
    return path.suffix if path.suffix.lower() in ALLOWED_SUFFIXES else '.txt'
def validate_route(path, scratch):
    unresolved = path.absolute()
    current = unresolved.anchor and Path(unresolved.anchor)
    if current:
        for part in unresolved.parts[1:]:
            current /= part
            if current.is_symlink() or getattr(current,'is_junction',lambda:False)():
                raise ValueError('Output route contains a symlink/junction.')
    resolved = unresolved.resolve()
    if not resolved.is_relative_to(scratch) or resolved == scratch or resolved.exists():
        raise ValueError('Output must be a new path strictly below supplied scratch root.')
    return resolved

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--handoff',required=True,type=Path)
    parser.add_argument('--expected-handoff-sha256',required=True)
    parser.add_argument('--selection-supplement',required=True,type=Path)
    parser.add_argument('--scratch-root',required=True,type=Path)
    parser.add_argument('--output-dir',required=True,type=Path)
    parser.add_argument('--expected-source-sha256',default=None)
    parser.add_argument('--expected-config-sha256',default=None)
    parser.add_argument('--expected-config-sha256-prefix',default=None)
    args = parser.parse_args()
    handoff_path = args.handoff.resolve()
    if sha_file(handoff_path) != args.expected_handoff_sha256:
        raise SystemExit('Trusted completed handoff SHA256 mismatch; no files archived.')
    handoff = load_json(handoff_path)
    supplement = load_json(args.selection_supplement)
    if supplement.get('original_completed_handoff_sha256') != args.expected_handoff_sha256:
        raise SystemExit('Reviewer selection does not bind the trusted completed handoff.')
    allowed = {'original_completed_handoff_sha256','diagnostic_id','owner_archives',
        'additional_extra_files','completion_classification','diagnostic_note',
        'live_contract_comparison','environment_diagnostics'}
    if set(supplement)-allowed:
        raise SystemExit('Selection supplement may not alter original phases/config/repo.')
    handoff = dict(handoff)
    handoff['extra_files'] = list(handoff.get('extra_files',[]))+supplement.get('additional_extra_files',[])
    for key in allowed-{'original_completed_handoff_sha256','additional_extra_files'}:
        if key in supplement: handoff[key] = supplement[key]
    if handoff.get('completed_records_handoff') is not True:
        raise SystemExit('Explicit completed-record handoff is required; do not archive running files.')
    diagnostic_id = safe_id(handoff.get('diagnostic_id','completed-whole-attempt'))
    expected_source_pin = args.expected_source_sha256 or handoff.get('expected_source_sha256')
    expected_config_pin = args.expected_config_sha256 or handoff.get('expected_config_sha256')
    expected_config_prefix = args.expected_config_sha256_prefix or handoff.get('expected_config_sha256_prefix')
    for pin in (expected_source_pin,expected_config_pin):
        if pin is not None and (not isinstance(pin,str) or not re.fullmatch(r'[a-f0-9]{64}',pin)):
            raise SystemExit('Expected source/config SHA256 must be a complete lowercase hash.')
    if expected_config_prefix is not None and (not isinstance(expected_config_prefix,str) or not re.fullmatch(r'[a-f0-9]{6,63}',expected_config_prefix)):
        raise SystemExit('An explicitly supplied partial config pin must have 6..63 lowercase hex digits.')
    repo = Path(handoff['repo_root']).resolve()
    scratch = args.scratch_root.resolve()
    if scratch.name != 'tmp' or scratch == repo or scratch.is_relative_to(repo/'verification'):
        raise SystemExit('Supply workspace tmp as scratch root, outside public verification paths.')
    out = validate_route(args.output_dir,scratch)
    out.mkdir(parents=True)
    issues, archives = [], []
    def problem(subject,reason):
        value = {'subject':str(subject),'reason':reason}
        if value not in issues: issues.append(value)
    def input_spec(value):
        return {'path':value} if isinstance(value,str) else value
    def archive(value, relative, role, phase=None):
        spec = input_spec(value)
        source = Path(spec['path']).resolve()
        if not source.is_file():
            problem(source,'Supplied completed text record is missing; no phase success inferred.')
            return None
        lower = source.name.lower()
        source_is_gzip = source.suffix.lower()=='.gz'
        payload_name = lower[:-3] if source_is_gzip else lower
        if any(payload_name.endswith(ext) for ext in FORBIDDEN_SUFFIXES) or (not source_is_gzip and source.suffix.lower() not in ALLOWED_SUFFIXES):
            raise ValueError('Only explicit text/source metadata is archived; compiled/cache/binary input refused.')
        target = out/relative
        if target.exists() or not target.resolve().is_relative_to(out):
            raise ValueError('Archive destination is duplicated or escapes fresh packet.')
        target.parent.mkdir(parents=True,exist_ok=True)
        before = source.stat()
        h, total = hashlib.sha256(), 0
        source_h, source_total = hashlib.sha256(), 0
        decoder = codecs.getincrementaldecoder('utf8')('strict')
        tail, first, secrets = b'', True, set()
        def inspect(blob):
            nonlocal tail, first, total
            if first and blob:
                if blob.startswith((b'\x7fELF',b'MZ',b'PK\x03\x04',b'olean',b'\x00asm')):
                    raise ValueError('Runtime/binary magic refused in text archive.')
                first = False
            decoder.decode(blob)
            for name, pattern in CREDENTIALS.items():
                if pattern.search(tail+blob): secrets.add(name)
            tail = (tail+blob)[-512:]
            h.update(blob);total += len(blob)
        with source.open('rb') as src, target.open('xb') as dst:
            if source_is_gzip:
                header = src.read(10);src.seek(0)
                if len(header)!=10 or header[:3]!=b'\x1f\x8b\x08' or header[3]!=0 or struct.unpack('<I',header[4:8])[0]!=0:
                    raise ValueError('Selected gzip must have mtime0 and no optional filename/comment/extra header fields.')
                inflater = zlib.decompressobj(31)
                limit = spec.get('decompressed_bytes',128_000_000)
                for block in iter(lambda:src.read(65_536),b''):
                    source_h.update(block);source_total += len(block);dst.write(block)
                    pending = block
                    while pending:
                        blob = inflater.decompress(pending,1_048_576)
                        pending = inflater.unconsumed_tail
                        inspect(blob)
                        if total>limit: raise ValueError('Selected gzip exceeds declared decompressed size/safety bound.')
                        if inflater.unused_data: raise ValueError('Selected gzip has trailing bytes or multiple members.')
                inspect(inflater.flush())
                if not inflater.eof or total>limit: raise ValueError('Selected gzip is incomplete or exceeds safety bound.')
            else:
                with gzip.GzipFile(filename='',mode='wb',fileobj=dst,compresslevel=6,mtime=0) as compressed:
                    for blob in iter(lambda:src.read(1_048_576),b''):
                        source_h.update(blob);source_total += len(blob)
                        inspect(blob);compressed.write(blob)
            decoder.decode(b'',final=True)
        after = source.stat()
        if (before.st_size,before.st_mtime_ns)!=(after.st_size,after.st_mtime_ns) or sha_file(source)!=source_h.hexdigest():
            problem(source,'Record changed during archiving; packet is not publishable as an immutable completed snapshot.')
        if ('bytes' in spec and spec['bytes'] != source_total) or ('sha256' in spec and spec['sha256'] != source_h.hexdigest()):
            problem(source,'Completion handoff hash/byte binding disagrees with the supplied record.')
        if source_is_gzip:
            if ('gzip_bytes' in spec and spec['gzip_bytes']!=source_total) or ('gzip_sha256' in spec and spec['gzip_sha256']!=source_h.hexdigest()):
                problem(source,'Selected owner gzip binding disagrees with exact preserved compressed bytes.')
            if ('decompressed_bytes' in spec and spec['decompressed_bytes']!=total) or ('decompressed_sha256' in spec and spec['decompressed_sha256']!=h.hexdigest()):
                problem(source,'Selected owner decompressed binding disagrees with payload.')
        for name in sorted(secrets): problem(source,'Credential pattern detected: '+name+'; value suppressed, archive must not be published.')
        check, check_bytes = hashlib.sha256(), 0
        with gzip.open(target,'rb') as stream:
            for blob in iter(lambda:stream.read(1_048_576),b''):
                check.update(blob);check_bytes += len(blob)
        if (check_bytes,check.hexdigest())!=(total,h.hexdigest()):
            problem(target,'Independent decompressed archive binding mismatch.')
        item = {'path':relative,'role':role,'phase':phase,'source_origin':str(source),
            'gzip_bytes':target.stat().st_size,'gzip_sha256':sha_file(target),
            'decompressed_bytes':total,'decompressed_sha256':h.hexdigest(),
            'gzip_mtime':0,'gzip_filename_header':'','encoding':'gzip',
            'source_was_gzip':source_is_gzip,'owner_compressed_bytes_preserved':source_is_gzip,
            'source_file_bytes':source_total,'source_file_sha256':source_h.hexdigest()}
        archives.append(item)
        return item
    def parse_record(spec):
        if spec is None: return None
        try:
            path = Path(input_spec(spec)['path'])
            if path.suffix.lower()=='.gz':
                with gzip.open(path,'rt',encoding='utf-8-sig') as stream: return json.load(stream)
            return load_json(path)
        except (OSError,ValueError) as error:
            problem(input_spec(spec).get('path','unknown'),'Completed JSON record is unreadable: '+type(error).__name__)
            return None

    archive(str(handoff_path),'provenance/completion-handoff.json.gz','byte-exact original trusted completed-record handoff')
    archive(str(args.selection_supplement),'provenance/reviewer-selection-supplement.json.gz','reviewer-only selection and relocation metadata')
    config_spec = handoff.get('config')
    config = parse_record(config_spec) if config_spec else {}
    config_binding = archive(config_spec,'provenance/config.json.gz','frozen completed-attempt configuration') if config_spec else None
    if not config:
        config = {};problem('config','Frozen configuration not supplied; source/contract provenance cannot be fully reviewed.')
    if set(config.get('permitted_axioms',[])) != STANDARD:
        problem('config','Permitted axiom configuration must be exactly the three standard axioms.')
    if set(config.get('targets',[])) != set(TARGETS):
        problem('config','Configured final roots must be exactly the three website declarations.')
    expected_source = config.get('source_sha256')
    actual_config_sha = config_binding['decompressed_sha256'] if config_binding else None
    if expected_source_pin and expected_source != expected_source_pin:
        problem('config','Configured source differs from caller/root handoff exact source pin.')
    if expected_config_pin and actual_config_sha != expected_config_pin:
        problem('config','Archived configuration differs from caller/root handoff exact config pin.')
    if expected_config_prefix and not (actual_config_sha or '').startswith(expected_config_prefix):
        problem('config','Archived configuration differs from the explicitly partial trusted config pin.')
    if not isinstance(expected_source,str) or not re.fullmatch(r'[a-f0-9]{64}',expected_source):
        problem('config','A complete candidate source hash is required; no source identity inferred.')
    if not isinstance(config.get('source_bytes'),int) or config.get('source_bytes',0)<=0:
        problem('config','An exact positive candidate byte count is required.')
    cutoff_classification = handoff.get('completion_classification','')
    intentional_cutoff = (handoff.get('intentional_local_resource_cutoff') is True
        or (isinstance(cutoff_classification,str) and cutoff_classification.endswith('_INTENTIONAL_RESOURCE_CUTOFF')))
    cutoff = None
    for item in handoff.get('extra_files',[]):
        if item.get('id')=='intentional-resource-cutoff': cutoff = parse_record(item)
    for index,item in enumerate(handoff.get('extra_files',[])):
        label = safe_id(item.get('id','extra-'+str(index)))
        archive(item,'provenance/'+label+payload_suffix(item)+'.gz',item.get('role','additional text provenance'))

    phase_summaries, selected, ids = [], {}, set()
    for entry in handoff.get('phases',[]):
        ident = safe_id(entry['id']);phase = entry['phase']
        if ident in ids or phase not in PHASES: raise ValueError('Duplicate record id or unknown whole-file phase.')
        ids.add(ident)
        summary = {'id':ident,'phase':phase,'selected_for_final_check':entry.get('selected_for_final_check',True),
                   'completed_handoff':entry.get('completed') is True,'archive_paths':{},'proof_gate_passed':False,
                   'independent_after_resource_gate_false':entry.get('independent_after_resource_gate_false') is True}
        phase_summaries.append(summary)
        if entry.get('completed') is not True:
            summary['status']='NOT_COMPLETED_NOT_ARCHIVED';continue
        files = entry.get('files',{})
        bound = {}
        for role,spec in files.items():
            safe_id(role)
            if spec is None: continue
            suffix = payload_suffix(spec)
            item = archive(spec,'runs/'+ident+'/'+role+suffix+'.gz',role,phase)
            if item:
                bound[role]=item;summary['archive_paths'][role]=item['path']
        ledger, raw = parse_record(files.get('ledger')), parse_record(files.get('result'))
        data = ledger or raw or {}
        summary.update({key:data.get(key) for key in [
            'run_id','actual_exit_code','supervisor_exit_code','timeout','postcondition_error',
            'elapsed_seconds','actual_phase_total_wall_seconds','actual_shared_elapsed_seconds',
            'actual_shared_wall_clock_elapsed_seconds','enforce_shared_budget','resource_fit',
            'cgroup_peak_bytes','sampled_tree_peak_pss_bytes','sampled_tree_peak_rss_bytes',
            'sampled_tree_peak_swap_bytes','oom_kill_count','memory_limit_hit',
            'outside_cgroup_peak_pss_bytes','source_sha256','source_bytes','config_sha256',
            'artifact_family_after','tool_family_after','export_file_after','shared_clock']})
        summary['final_cgroup'] = data.get('final_cgroup')
        summary['final_failed_memory_charges'] = (data.get('final_cgroup') or {}).get('memory.failcnt')
        summary['proof_process_result_present'] = raw is not None
        summary['phase_ledger_present'] = ledger is not None
        summary['ledger_proof_succeeded'] = ledger.get('proof_succeeded') if ledger else None
        summary['raw_proof_succeeded'] = raw.get('proof_succeeded') if raw else None
        summary['inputs_unchanged'] = raw.get('inputs_unchanged') if raw else None
        summary['scoped_eviction_summary'] = (raw or data).get('scoped_eviction')
        summary['proof_stage_seconds'] = number((raw or data).get('elapsed_seconds'))
        summary['cold_preparation_seconds'] = number(((raw or data).get('scoped_eviction') or {}).get('elapsed_seconds'))
        summary['configuration'] = (raw or data).get('configuration')
        summary['compiler_tasks'] = parse_record(files.get('tasks')) if files.get('tasks') else None
        summary['worker_record'] = parse_record(files.get('worker')) if files.get('worker') else None
        summary['proof_gate_passed'] = bool(ledger and raw and ledger.get('proof_succeeded') is True
            and raw.get('proof_succeeded') is True and raw.get('inputs_unchanged') is True)
        if summary['timeout'] is True: summary['status']='COMPLETED_TIMEOUT'
        elif summary['proof_gate_passed']:
            summary['status']='COMPLETED_PROOF_PASS' if summary['resource_fit'] is True else 'COMPLETED_PROOF_PASS_RESOURCE_GATE_FAILED'
        elif ledger is None or raw is None: summary['status']='COMPLETED_PARTIAL_RECORDS_NO_PASS_ESTABLISHED'
        else: summary['status']='COMPLETED_FAILED'
        if phase=='compile' and intentional_cutoff:
            if cutoff and cutoff.get('classification')=='INTENTIONAL_RESOURCE_CUTOFF_BY_ROOT_ALLOCATION':
                summary['status']='COMPLETED_INTENTIONAL_LOCAL_RESOURCE_CUTOFF'
                summary['intentional_cutoff_record']=cutoff
                summary['cutoff_interpretation']='Verified owned Lean was deliberately SIGTERM stopped by root after resource pressure. This interruption establishes no complete proof, no mathematical rejection, no observed OOM kill and no official timeout.'
            else: problem(ident,'Intentional-cutoff handoff lacks its exact root-allocation signal record.')
            if cutoff and cutoff.get('source_sha256') != expected_source:
                problem(ident,'Intentional-cutoff source identity disagrees with frozen configuration.')
            if cutoff and cutoff.get('run_id') != summary.get('run_id'):
                problem(ident,'Intentional-cutoff run identity disagrees with this compile record.')
            if summary['proof_gate_passed']:
                problem(ident,'Intentional-cutoff classification contradicts a completed compile proof pass.')
                summary['proof_gate_passed']=False
        for field,role in [('log_sha256','process'),('scoped_eviction_sha256','eviction')]:
            wanted = (raw or {}).get(field)
            if wanted and (role not in bound or bound[role]['decompressed_sha256'] != wanted):
                problem(ident,'Raw result '+field+' disagrees with archived '+role+' bytes.')
                summary['proof_gate_passed']=False
        if expected_source and data.get('source_sha256') not in (None,expected_source):
            problem(ident,'Phase ledger belongs to a different candidate source.')
            summary['proof_gate_passed']=False
        summary['source_inputs_bound_to_config'] = None
        if raw:
            before, after = raw.get('inputs_before',{}), raw.get('inputs_after',{})
            configured_bindings = dict(config.get('sources',{}))
            configured_bindings.update(config.get('tool_config_bindings',{}))
            missing = [name for name,wanted in configured_bindings.items()
                       if before.get(name)!=wanted or after.get(name)!=wanted]
            summary['source_inputs_bound_to_config'] = not missing
            if missing:
                problem(ident,'Completed raw result lacks exact before/after bindings for configured source inputs.')
                summary['proof_gate_passed']=False
            if before != after:
                problem(ident,'Completed raw result has unequal complete before/after input maps.')
                summary['proof_gate_passed']=False
            if expected_source and data.get('source_sha256') != expected_source:
                problem(ident,'Completed phase lacks its exact configured candidate-source hash.')
                summary['proof_gate_passed']=False
            if config_binding and data.get('config_sha256') != config_binding['decompressed_sha256']:
                problem(ident,'Completed phase ledger lacks the exact archived configuration hash.')
                summary['proof_gate_passed']=False
        log = ''
        if files.get('process'):
            try:
                path = Path(input_spec(files['process'])['path'])
                if path.suffix.lower()=='.gz':
                    with gzip.open(path,'rt',encoding='utf-8-sig') as stream: log = stream.read()
                else: log = path.read_text(encoding='utf-8-sig')
            except (OSError,UnicodeError): problem(ident,'Completed process log is unreadable.')
        if phase=='audit':
            roots = []
            for target in config.get('targets',TARGETS):
                match = re.search(re.escape(target)+r"' depends on axioms: \[([^\]]*)\]",log)
                values = None if not match else sorted({re.sub(r'\.\{[^}]*\}$','',x.strip())
                    for x in match.group(1).split(',') if x.strip()})
                roots.append({'root':target,'axioms':values})
            actual_standard = len(roots)==3 and all(root['axioms'] is not None and set(root['axioms'])<=STANDARD for root in roots)
            summary['actual_axiom_roots']=roots
            summary['fresh_three_roots_standard_axioms_checked'] = actual_standard and data.get('fresh_three_roots_standard_axioms') is True
            summary['proof_gate_passed'] &= summary['fresh_three_roots_standard_axioms_checked']
            if data.get('fresh_three_roots_standard_axioms') is True and not actual_standard:
                problem(ident,'Claimed axiom audit pass lacks all three standard-only printed roots.')
        if phase=='deps':
            fresh = data.get('deps_fresh_current_contract_only') is True
            summary['fresh_current_contract_dependencies_checked']=fresh
            summary['proof_gate_passed'] &= fresh
        if phase=='core':
            markers = ['Pinned Comparator statement, dependency and primitive comparison passed',
                       'Pinned Comparator transitive axiom check passed','Lean default kernel replay passed']
            core_pass = data.get('exact_types_primitives_axioms_default_kernel_passed') is True and all(x in log for x in markers)
            summary['actual_comparator_core_markers_checked']=core_pass
            summary['proof_gate_passed'] &= core_pass
            if data.get('exact_types_primitives_axioms_default_kernel_passed') is True and not core_pass:
                problem(ident,'Claimed core pass lacks the pinned comparison/axiom/default-replay log markers.')
        if phase=='nano':
            count = re.search(r'Checked\s+([0-9]+)\s+declarations',log)
            summary['printed_declaration_count'] = int(count.group(1)) if count else None
            summary['declaration_count_not_invented']=True
            actual_replay = summary['printed_declaration_count'] is not None and summary['printed_declaration_count']>0
            summary['actual_independent_replay_success_marker_checked']=actual_replay
            if summary['proof_gate_passed'] and not actual_replay:
                problem(ident,'Claimed independent replay pass lacks a positive checked-declaration log marker.')
                summary['proof_gate_passed']=False
        if phase in ('challenge-export','solution-export'):
            export_binding = summary.get('export_file_after')
            bound_export = (isinstance(export_binding,dict) and isinstance(export_binding.get('bytes'),int)
                and export_binding['bytes']>0 and isinstance(export_binding.get('sha256'),str)
                and re.fullmatch(r'[a-f0-9]{64}',export_binding['sha256']) is not None)
            summary['completed_export_metadata_binding_present']=bound_export
            if summary['proof_gate_passed'] and not bound_export:
                problem(ident,'Claimed export pass lacks its exact nonempty export-file metadata binding.')
                summary['proof_gate_passed']=False
        if not summary['proof_gate_passed'] and summary['status'].startswith('COMPLETED_PROOF_PASS'):
            summary['status']='COMPLETED_PROCESS_PASS_FINAL_GATE_NOT_ESTABLISHED'
        if summary['selected_for_final_check']:
            if phase in selected: problem(phase,'More than one selected attempt; no unambiguous final gate decision.')
            else: selected[phase]=summary

    # Preserve each family hash independently; no compiled artifact is opened.
    tools_family = (selected.get('tools') or {}).get('tool_family_after')
    if tools_family is None:
        tools_family = (selected.get('contract') or {}).get('tool_family_after')
    if tools_family is not None:
        for phase,value in selected.items():
            if value['proof_gate_passed'] and value.get('tool_family_after') != tools_family:
                problem(value['id'],'Selected phase tool artifact-family hashes differ from frozen prebuild/contract family.')
                value['proof_gate_passed']=False
                value['status']='COMPLETED_PROCESS_PASS_FINAL_GATE_NOT_ESTABLISHED'
    compile_family = (selected.get('compile') or {}).get('artifact_family_after')
    if compile_family is not None:
        for phase in ('deps','audit','challenge-export','solution-export','core','nano'):
            value = selected.get(phase)
            expected_family = compile_family
            compile_time = number((selected.get('compile') or {}).get('actual_shared_elapsed_seconds'))
            phase_time = number((value or {}).get('actual_shared_elapsed_seconds'))
            if phase=='challenge-export' and compile_time is not None and phase_time is not None and phase_time<compile_time:
                expected_family = (selected.get('contract') or {}).get('artifact_family_after')
            if value and value['proof_gate_passed'] and expected_family is not None and value.get('artifact_family_after') != expected_family:
                problem(value['id'],'Post-compile project artifact family changed; fresh-artifact provenance is not established.')
                value['proof_gate_passed']=False
                value['status']='COMPLETED_PROCESS_PASS_FINAL_GATE_NOT_ESTABLISHED'
    missing = [phase for phase in WHOLE_PHASES if phase not in selected]
    local_proof_gates = not missing and all(selected[phase]['proof_gate_passed'] for phase in WHOLE_PHASES)
    original = repo/'submission/proof/Solution.lean'
    original_now = sha_file(original) if original.is_file() else None
    if original_now != ORIGINAL_SHA:
        problem(original,'Original public d52 submission changed; archive helper never authorizes replacement.')
    owner_identity_files = []
    owner_producers = []
    for owner_selection in handoff.get('owner_archives',[]):
        owner_id = safe_id(owner_selection['id'])
        owner_spec = owner_selection['owner_archive_manifest']
        owner_path = Path(input_spec(owner_spec)['path']).resolve()
        owner_root = Path(owner_selection['owner_archive_root']).resolve()
        owner_prefix = owner_selection['owner_archive_record_prefix'].rstrip('/')+'/'
        owner = parse_record(owner_spec) or {}
        owner_blob = owner_path.read_bytes()
        if 'sha256' in input_spec(owner_spec) and digest_bytes(owner_blob)!=input_spec(owner_spec)['sha256']:
            problem(owner_path,'Original owner manifest hash mismatch.')
        reviewed_raw = {record['decompressed_sha256'] for record in archives}
        for item in owner.get('files',[]):
            declared = item['archived']
            if not declared.startswith(owner_prefix): raise ValueError('Owner archive path leaves explicitly selected record prefix.')
            relative = declared[len(owner_prefix):]
            src = (owner_root/relative).resolve()
            if not src.is_relative_to(owner_root): raise ValueError('Owner selected record escapes completed archive root.')
            blob = src.read_bytes()
            if len(blob)!=item['archived_bytes'] or digest_bytes(blob)!=item['archived_sha256']:
                problem(src,'Original selected owner archive bytes/hash mismatch.')
            if item['gzip']:
                if len(blob)<20 or blob[:3]!=b'\x1f\x8b\x08' or blob[3]!=0 or struct.unpack('<I',blob[4:8])[0]!=0:
                    raise ValueError('Preserved owner gzip must be a deterministic filename-free stream.')
                inflater = zlib.decompressobj(31)
                raw_hash, raw_size = hashlib.sha256(), 0
                for start in range(0,len(blob),65_536):
                    pending = blob[start:start+65_536]
                    while pending:
                        chunk = inflater.decompress(pending,1_048_576)
                        pending = inflater.unconsumed_tail
                        raw_hash.update(chunk);raw_size += len(chunk)
                        if raw_size>item['raw_bytes'] or inflater.unused_data:
                            raise ValueError('Preserved owner gzip size/trailing-member safety failure.')
                chunk = inflater.flush();raw_hash.update(chunk);raw_size += len(chunk)
                if not inflater.eof or (raw_size,raw_hash.hexdigest())!=(item['raw_bytes'],item['raw_sha256']):
                    problem(src,'Independent owner gzip decompressed identity mismatch.')
            elif (len(blob),digest_bytes(blob))!=(item['raw_bytes'],item['raw_sha256']):
                problem(src,'Original identity owner record does not match its raw binding.')
            if item['raw_sha256'] not in reviewed_raw:
                problem(src,'Owner raw hash has no corresponding reviewed completed input in this packet.')
            dest = out/'owner-selection'/owner_id/relative
            if not dest.resolve().is_relative_to(out) or dest.exists(): raise ValueError('Duplicate/escaping preserved owner record path.')
            dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(blob)
            owner_identity_files.append({'path':dest.relative_to(out).as_posix(),'bytes':len(blob),
                'sha256':digest_bytes(blob),'original_manifest_raw_sha256':item['raw_sha256'],
                'original_archived_path':declared,'owner_archive_gzip':item['gzip']})
        preserved_owner_manifest = out/'owner-selection'/owner_id/'archive-manifest.json'
        if preserved_owner_manifest.exists(): raise ValueError('Owner manifest collision.')
        preserved_owner_manifest.parent.mkdir(parents=True,exist_ok=True)
        preserved_owner_manifest.write_bytes(owner_blob)
        owner_identity_files.append({'path':preserved_owner_manifest.relative_to(out).as_posix(),
            'bytes':len(owner_blob),'sha256':digest_bytes(owner_blob),'role':'byte-identical original owner manifest'})
        owner_producers.append({'id':owner_id,'producer_manifest_sha256':digest_bytes(owner_blob),
            'manifest_path':preserved_owner_manifest.relative_to(out).as_posix(),
            'record_count':len(owner.get('files',[]))})
    if owner_producers:
        write_json(out/'owner-selection-relocation.json',{'producer_manifests':owner_producers,
            'all_selected_records_preserved_byte_identically':not issues,'files':owner_identity_files})
    chosen = [selected[phase] for phase in WHOLE_PHASES if phase in selected]
    clocks = {(json.dumps(row['shared_clock'],sort_keys=True)) for row in chosen if row.get('shared_clock') is not None}
    shared_elapsed = [number(row.get('actual_shared_elapsed_seconds')) for row in chosen]
    shared_elapsed = [value for value in shared_elapsed if value is not None]
    actual_elapsed = max(shared_elapsed) if shared_elapsed and len(clocks)==1 else None
    proof_sum = compact_sum(row['proof_stage_seconds'] for row in chosen)
    phase_total_sum = compact_sum(row.get('actual_phase_total_wall_seconds') for row in chosen)
    cold_sum = compact_sum(row['cold_preparation_seconds'] for row in chosen)
    summary = {
      'status':'COMPLETE_LOCAL_PROOF_GATES_PASS' if local_proof_gates and not issues else 'LOCAL_CHECKS_INCOMPLETE_FAILED_OR_REVIEW_REQUIRED',
      'review_status':'PASS' if not issues else 'ACTIONABLE_ISSUES',
      'phases':phase_summaries,'missing_selected_whole_phases':missing,
      'complete_local_proof_gates_passed':local_proof_gates and not issues,
      'all_selected_local_component_resource_fit':not missing and all(selected[p].get('resource_fit') is True for p in WHOLE_PHASES),
      'actual_shared_elapsed_seconds':actual_elapsed,
      'actual_shared_clock_count':len(clocks),
      'actual_shared_elapsed_scope':'Latest observed shared-clock elapsed among supplied selected completed phases; absent phases/timestamps remain unknown and are not extrapolated.',
      'all_supplied_selected_shared_timestamps_present':bool(chosen) and all(number(row.get('actual_shared_elapsed_seconds')) is not None and row.get('shared_clock') is not None for row in chosen),
      'sum_observed_proof_stage_seconds_excluding_tools':proof_sum,
      'sum_observed_phase_total_seconds_excluding_tools':phase_total_sum,
      'sum_observed_cold_preparation_seconds_excluding_tools':cold_sum,
      'actual_minus_sum_proof_stage_seconds':round(actual_elapsed-proof_sum,3) if actual_elapsed is not None and proof_sum is not None else None,
      'elapsed_interpretation':'Actual shared elapsed includes preparation, bindings, wrappers and caller delays; summed proof-stage time is not an official end-to-end runtime. Tools prebuild is outside the shared clock. Separate phases/order/retained-string lifetimes differ from Comparator.',
      'proof_stage_field_definition':'Raw v3 result.elapsed_seconds starts at owned-process launch and includes its cleanup/postcondition timing; cold preparation is recorded separately. It is not a per-theorem CPU total.',
      'memory_interpretation':'Per-phase cgroup and PSS peaks remain separate from caller/supervisor PSS outside the group. Noncontemporaneous maxima are not summed. Kernel, unrelated file-cache ownership and host processes are not fully covered. An enclosing VM size is only recorded when explicitly supplied by the trusted handoff; the cgroup is not an official sandbox.',
      'handoff_environment_diagnostics':handoff.get('environment_diagnostics'),
      'explicit_experimental_compiler_flags':config.get('explicit_experimental_compiler_flags'),
      'official_stack_flag_established':config.get('official_stack_flag_established',False),
      'official_stack_or_worker_equivalence_claimed':False,
      'official_inner_budget_seconds':3200,
      'local_shared_clock_exceeds_3200':actual_elapsed>3200 if actual_elapsed is not None else None,
      'official_resource_fit_established':False,'website_acceptance_established':False,
      'source_sha256':expected_source,'source_bytes':config.get('source_bytes'),
      'diagnostic_id':diagnostic_id,'config_sha256':actual_config_sha,
      'original_completed_handoff_sha256':sha_file(handoff_path),
      'frozen_old_current_record':handoff.get('frozen_old_current_record'),
      'live_contract_comparison':handoff.get('live_contract_comparison'),
      'live_current_contract_claimed':False,
      'caller_expected_source_sha256':expected_source_pin,
      'caller_expected_config_sha256':expected_config_pin,
      'caller_expected_config_sha256_prefix':expected_config_prefix,
      'config_pin_scope':'Complete caller SHA256 pins bind this source, config and original completed handoff; all phase input bindings are retained.',
      'original_public_solution_sha256':original_now,'original_public_solution_unchanged':original_now==ORIGINAL_SHA,
      'candidate_or_preflight_replaced':False,
      'completion_classification':handoff.get('completion_classification'),
      'root_diagnostic_note':handoff.get('diagnostic_note'),
      'intentional_local_cutoff_record':cutoff,
      'follow_up_experiment':handoff.get('follow_up_experiment'),
      'follow_up_running_records_read_or_archived':False,
      'read_page_snapshot_interpretation':'A proc snapshot supplies sampled process/thread states and cumulative faults/read_bytes at that instant. Cumulative read_bytes is not resident memory; wait_on_page_bit_common and high major faults are consistent with page pressure, but a single snapshot does not establish deadlock or identify one theorem as the cause. It does not replace a complete proof check.',
      'only_permitted_axioms':sorted(STANDARD),
      'axiom_scope':'Only an actual completed fresh audit of all three printed final roots establishes their transitive axiom lists. Missing audit is not a pass.',
      'scope':'File-only archive/review of explicitly completed local whole-file diagnostics; no new proof, official E2B/Landlock run, submission or acceptance.',
      'helper_sha256':sha_file(Path(__file__)),'issues':issues
    }
    write_json(out/'summary.json',summary)
    table = []
    for phase in WHOLE_PHASES:
        value = selected.get(phase)
        table.append('| '+phase+' | '+(value['status'] if value else 'NOT SUPPLIED')+' | '+
                     (str(value.get('proof_stage_seconds')) if value else '—')+' |')
    readme = '''# Completed local whole-file records\n\nThis packet preserves explicitly completed local text records. Failed, timed-out\nand intentionally stopped attempts remain distinguishable. Missing phases stay\nunverified. It does not replace preflight history or the original d52 public\nsubmission.\n\n| Selected phase | Recorded outcome | Proof-stage seconds |\n|---|---|---:|\n'''+ '\n'.join(table)+f'''\n\nDiagnostic identifier: **{diagnostic_id}**.\nCandidate source: `{expected_source}`, {config.get('source_bytes')} bytes.\nFrozen configuration: `{actual_config_sha}`.\nComplete local proof gates passed: **{summary['complete_local_proof_gates_passed']}**.\nFile-integrity/provenance review: **{summary['review_status']}**.\nActual shared elapsed: **{actual_elapsed} s**; sum of observed proof-stage time\nexcluding tools: **{proof_sum} s**; observed cold preparation sum: **{cold_sum} s**.\nThe sums cover only supplied selected phases and must not be presented as an\nend-to-end official runtime. Shared elapsed includes local preparation, wrappers\nand caller delays; tools were prebuilt outside that clock.\n\nThe exact compiler flags and commands are preserved in `summary.json`; official\nstack/worker equivalence is not established. The independent local phases differ\nfrom the official retained-strings pipeline and may use a different order.\nPer-phase cgroup settings and separately sampled outside-group caller/supervisor\nPSS do not cover unrelated cache ownership, kernel or host memory. An enclosing\nVM size is reported only when supplied in handoff metadata. Separate memory\nmaxima are not added.\n\nOnly an actual completed fresh audit of all three final roots can establish\nstandard-only transitive axioms (`propext`, `Quot.sound`, `Classical.choice`).\nMissing, failed or timed-out compilation/audit/export/independent replay/core\nphases do not satisfy the complete gates. No website acceptance or official\nresource-fit claim is made even if local proof gates pass.\n\n`archive-manifest.json` binds exact compressed/decompressed raw bytes; gzip\nmtime is zero and filenames are omitted from headers. No executables, compiled\nartifacts, dependency caches or live partial logs are copied. `summary.json`\npreserves source/artifact provenance and discrepancies. Review issues, if any,\nmake this scratch packet unpublishable until reviewed.\n'''
    readme += '\nCompletion classification: **'+str(handoff.get('completion_classification','not supplied'))+'**.\nRoot diagnostic note: '+str(handoff.get('diagnostic_note','No diagnostic note supplied.'))+'\n'
    if intentional_cutoff:
        readme += '\nThis attempt was intentionally resource-cut off and leaves no completed\nmathematical proof result. Failed memory charges and sampled peaks do not by\nthemselves establish a kernel OOM kill, a mathematical rejection or an official\nwebsite timeout.\n'
    readme += '\nA proc snapshot, when supplied, records sampled states and cumulative\nread_bytes/fault counters. Those counters are not resident-memory peaks. A page\nwait can be consistent with pressure; one snapshot does not establish deadlock\nor identify a single proof culprit. Follow-up metadata, when supplied, comes\nonly from the root handoff. No running record is read or included, and no future\nattempt result is inferred. Completed proof claims concern only this packet\nand only gates actually checked above.\n'
    readme += '\nThe completed r6 compile proof passed, but its configured memory resource gate\nfailed: final memory.failcnt is 64, with no observed OOM kill, timeout or swap.\nIndependent deps and three-root axiom audit subsequently passed. Challenge and\nsolution exports, Comparator/default-kernel replay and Nanoda remain unrun, so\nthe whole pipeline has not passed. The shared clock continued during separately\nauthorized diagnostic phases after the failed resource gate. Its final elapsed\ntime exceeds 3200 seconds; this is not an observed official timeout.\n'
    readme += '\nThis is a historical contract diagnostic: the frozen current record is\n6735015/10000000 at website commit 6664d243005e12e155c19775b83f53721757414b.\nThe subsequently observed live accepted record is 66812491/99194876\n(master-of-puppets, verified 2026-10-09 17:13:57.608 UTC; fixed public source\ncommit d95a6d7d11d7836306ec7ec1eb5be3478663718e). Our fixed score\n66812491/99194740 remains larger, but a fresh current-contract validation has\nnot been performed here. Existing old-current deps/root audit passes must not\nbe presented as live-contract or website acceptance.\n'
    readme += '\nThe local compiler explicitly used -j4 and --tstack=32768, in a 4 CPU/8 GiB/no\nswap cgroup inside a locally configured 32 GiB WSL VM. Cold preparation and\nsampled caller/supervisor memory are outside the proof cgroup. Official worker,\nstack, retained-string and VM equivalence are not established.\n'
    (out/'README.md').write_text(readme,encoding='utf8')
    (out/'provenance').mkdir(exist_ok=True)
    helper_copy = out/'provenance/archive_completed_whole_result_v2_r6.py'
    helper_copy.write_bytes(Path(__file__).read_bytes())
    manifest = {'status':'FRESH_SCRATCH_ARCHIVE_OF_COMPLETED_LOCAL_RECORDS',
      'files':archives,'gzip_policy':{'mtime':0,'filename_header':'','compression_level':6,
      'compressed_and_decompressed_counts_hashes_verified':True},
      'generated_text':{str(path.relative_to(out)).replace('\\','/'):{'bytes':path.stat().st_size,'sha256':sha_file(path)}
        for path in [out/'README.md',out/'summary.json',helper_copy,out/'owner-selection-relocation.json'] if path.exists()},
      'review_status':summary['review_status'],'no_binaries_or_cache_artifacts':True,
      'preserved_owner_files':owner_identity_files,
      'no_compiler_verifier_subprocess_network_or_public_mutation':True,
      'producer_preflight_manifests_overwritten':False,'website_acceptance':False}
    write_json(out/'archive-manifest.json',manifest)
    print(json.dumps({'packet':str(out),'status':summary['status'],'review_status':summary['review_status'],
          'complete_local_proof_gates_passed':summary['complete_local_proof_gates_passed'],'issues':issues},indent=2))
    raise SystemExit(0 if not issues else 1)

if __name__=='__main__': main()
