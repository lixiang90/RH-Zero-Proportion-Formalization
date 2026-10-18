"""Independent byte/text audit only. Never imports or runs any producer."""
import ast
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DEDUP = ROOT/'research-goal-20261019-tiny-dedup-source-preparation'
V3 = ROOT/'research-goal-20261018-tiny-flatten-preparation-v3'
V4 = ROOT/'research-goal-20261019-tiny-flatten-preparation-v4'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def read(path):
    return path.read_bytes()

def info(path):
    b = read(path)
    return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':digest(b)}

def load(path):
    return json.loads(read(path))

def imports_and_body(b):
    imp, body = [], []
    for line in b.splitlines(keepends=True):
        (imp if line.startswith(b'import ') else body).append(line)
    return imp, b''.join(body)

def section(b, start, end):
    assert b.count(start) == 1, start[:80]
    a = b.index(start)
    z = b.index(end,a) + len(end)
    return b[a:z]

def block_comments(b):
    """Lean nested block-comment scanner; do not mistake strings for comments."""
    out = []
    i = 0
    string = False
    while i < len(b):
        if string:
            if b[i:i+1] == b'\\': i += 2; continue
            if b[i:i+1] == b'"': string = False
            i += 1; continue
        if b[i:i+2] == b'--':
            j = b.find(b'\n',i)
            i = len(b) if j < 0 else j+1
            continue
        if b[i:i+1] == b'"': string = True; i += 1; continue
        if b[i:i+2] != b'/-': i += 1; continue
        a = i; depth = 1; i += 2
        while depth:
            assert i < len(b), 'unclosed block comment'
            if b[i:i+2] == b'/-': depth += 1; i += 2
            elif b[i:i+2] == b'-/': depth -= 1; i += 2
            else: i += 1
        out.append(b[a:i])
    assert not string
    return out

def ast_without_module_paths(path):
    tree = ast.parse(read(path).decode('utf-8'),filename=str(path))
    modules = None
    header = None
    for node in tree.body:
        if not isinstance(node,ast.Assign) or not isinstance(node.targets[0],ast.Name):
            continue
        if node.targets[0].id == 'MODULES':
            modules = ast.literal_eval(node.value)
            node.value = ast.Constant(value='ONLY THE PINNED MODULE LIST IS ABSTRACTED')
        elif node.targets[0].id == 'HEADER':
            header = ast.literal_eval(node.value.func.value).encode('utf-8')
    assert modules and header
    return ast.dump(tree,include_attributes=False),modules,header

def exclusive_json(path,obj):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2); f.write('\n')

def main():
    assert not (HERE/'independent-review.json').exists()
    assert not (HERE/'audit-files.json').exists()
    dedup_manifest = DEDUP/'prepared-files.json'
    flatten_manifest = V4/'prepared-files.json'
    assert digest(read(dedup_manifest)) == '98a9dfe125cfdb4febc24fb8666bb73228e4f27fcbac9fe66506c1c7720f99d6'
    assert digest(read(flatten_manifest)) == '2b77159157e500b0177c3c2294860830a495248ce3e3b216a813524032509d72'
    bound = {}
    for manifest in [dedup_manifest,flatten_manifest]:
        bound[manifest.relative_to(ROOT).as_posix()] = digest(read(manifest))
        m = load(manifest)
        for group in ['files','dependencies','read_dependencies']:
            for row in m.get(group,[]):
                p = ROOT/row['path']
                b = read(p)
                assert digest(b) == row['sha256'] and len(b) == row['bytes'],row['path']
                assert row['path'] not in bound or bound[row['path']] == row['sha256']
                bound[row['path']] = row['sha256']
    extras = [V3/'official-wrapper.lean.txt', V3/'candidate-parameters.json',
              V3/'generate_draft.py', V3/'draft/Solution.lean', V3/'draft/generation.json',
              ROOT/'StructuralS1RTiny20261018/Phase4/Final.lean',
              ROOT/'research-20261016-w10-cert/website-snapshot/challenge/templates/Challenge.Candidate.lean']
    for p in extras: bound[p.relative_to(ROOT).as_posix()] = digest(read(p))
    original = read(ROOT/'StructuralS1RTiny20261018/Core.lean')
    production = read(ROOT/'StructuralS1RTiny20261018/Production/Core.lean')
    inverse = production.replace(b'PC9Tiny',b'PC9QB6M')
    assert len(b'PC9Tiny') == len(b'PC9QB6M') == 7
    closing = b'end OpethN.Counting\nend\n'
    assert original.count(closing) == 1
    cut = original.index(closing)+len(closing)
    trailer_marker = b'/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'
    assert original.count(trailer_marker) == 1
    trailer = original.index(trailer_marker)
    retired = original[cut:trailer]
    comments = block_comments(retired)
    assert len(comments) == 2
    assert all(b'Copyright (c) 2026 R. Arun Chandru.' in c and b'Apache-2.0' in c for c in comments)
    # A direct inverse byte equality, independent of the preparation generator.
    assert inverse == original[:cut] + b''.join(c+b'\n' for c in comments) + original[trailer:]
    assert len(original)-len(production) == 6092
    notices = [c for c in block_comments(original)
               if b'copyright' in c.lower() or b'license' in c.lower()]
    assert all(c in production for c in notices), 'notice changed or removed'
    assert original[trailer:] == production[-(len(original)-trailer):]
    assert b'PC9QB6M' not in production
    assert not any(b'PC9QB6M' in q for q in re.findall(rb'"[^"\n]*"',original[:cut]))
    assert not re.search(rb'(?m)^(?:private )?theorem candidate_', production)
    retired_code = retired
    for c in comments: retired_code = retired_code.replace(c,b'')
    retired_declarations = re.findall(rb'(?m)^(?:private )?(?:noncomputable )?(theorem|def|abbrev)\s+([^\s:(]+)',retired_code)
    dev = read(ROOT/'StructuralS1RTiny20261018/Dev/Core.lean')
    segments = [
      ('strengthened_concrete',b'namespace AMW.Cert.PC9Tiny\n',b'end AMW.Cert.PC9Tiny\n'),
      ('COV_all_payload_cut_ready_and_walk',b'noncomputable def COV :',b'end AMW.Cert.PC9TinyData\n'),
      ('actual_reflection_W9_and_generic_counting',b'theorem PC9Tiny_G_rev',b'end OpethN.Counting\nend\n'),
    ]
    segment_results = []
    for name,a,z in segments:
        x,y = section(production,a,z),section(dev,a,z)
        assert x == y,name
        segment_results.append({'name':name,'bytes':len(x),'sha256':digest(x)})
    payload = lambda b: re.findall(rb'zfNat64\s+[0-9]+\s+"[^"\n]*"',b)
    assert len(payload(production)) == 137
    assert payload(production) == payload(original) == payload(dev)
    # Data cursor/ready lines are also covered by the complete COV segment equality.
    cursor_lines = [line for line in production.splitlines()
                    if re.match(rb'^(?:theorem |noncomputable def )(?:ready_|rc[0-9]+\b)',line)]
    aliases = ['TOP','BK','lbS','TOPD','BKD','lbD','REG','hR','PT','ptS']
    data_a = production.index(b'namespace AMW.Cert.PC9TinyData\n')
    data_z = production.index(b'noncomputable def COV :',data_a)
    table = production[data_a:data_z]
    for name in aliases:
        assert re.search(rb'(?m)^(?:noncomputable )?(?:def|theorem) '+name.encode()+rb'\b',table),name
    client_results = []
    for name,prior in [('Localization.lean','Phase1'),('Counting.lean','Phase2'),('Final.lean','Phase4')]:
        old = read(ROOT/'StructuralS1RTiny20261018'/prior/name)
        new = read(ROOT/'StructuralS1RTiny20261018/Production'/name)
        oi,ob = imports_and_body(old); ni,nb = imports_and_body(new)
        assert ob == nb,name
        assert all(b'StructuralS1RTiny20261018.Production.' in x for x in ni)
        client_results.append({'name':name,'non_import_body_sha256':digest(nb),
                               'old_imports':[x.decode().strip() for x in oi],
                               'new_imports':[x.decode().strip() for x in ni]})
    a3,m3,h3 = ast_without_module_paths(V3/'generate_draft.py')
    a4,m4,h4 = ast_without_module_paths(V4/'generate_draft.py')
    assert a3 == a4, 'generator algorithm AST changed'
    assert h3 == h4
    expected = tuple(('StructuralS1RTiny20261018.Production.'+n,
                       'StructuralS1RTiny20261018/Production/'+n+'.lean')
                      for n in ['Core','Localization','Counting','Final'])
    assert m4 == expected
    wrapper = read(V4/'official-wrapper.lean.txt')
    assert wrapper == read(V3/'official-wrapper.lean.txt')
    assert load(V4/'candidate-parameters.json') == load(V3/'candidate-parameters.json')
    template = read(extras[-1]).decode('utf-8')
    public_roots = ['candidate_strict_improvement','candidate_critical_line_bound',
                    'candidate_critical_line_bound_cumulative']
    for name in public_roots:
        p = r'theorem '+name+r'\s*:(.*?) := by'
        x,y = re.search(p,template,re.S).group(1),re.search(p,wrapper.decode(),re.S).group(1)
        assert ''.join(x.split()) == ''.join(y.split()),name
    final = read(ROOT/'StructuralS1RTiny20261018/Production/Final.lean')
    assert b'_root_.Ncount' in final and b'_root_.N0star' in final
    declarations = {}
    for name in ['tinyKappa','baselineKappa','pressure']:
        pat = rb'def '+name.encode()+rb' : .*?:=\s*(.*?)(?=\n\n)'
        declarations[name] = re.search(pat,final,re.S).group(1).decode()
    assert '3337839448633819172184136761695440236797' in declarations['tinyKappa']
    assert '4955319193827760237900000000000000000000' in declarations['tinyKappa']
    assert b'theorem actual_dyadic :\n    \xe2\x88\x80 epsilon > (0 : ' in final
    assert b'theorem actual_cumulative :\n    \xe2\x88\x80 epsilon > (0 : ' in final
    # Byte length calculation only: do not construct or write a flattened source.
    internal_names = {module for module,_ in m4}
    retained_total = 0; external_bytes = 0; externals = []; internal_count = 0
    for module,name in m4:
        blob = read(ROOT/name)
        ii,bb = imports_and_body(blob)
        retained_total += len(bb)
        for line in ii:
            target = line.decode().strip()[7:]
            if target in internal_names: internal_count += 1
            else: external_bytes += len(line); externals.append(target)
    separators = sum(len(('\n/- BEGIN FLATTENED MODULE '+m+' -/\n').encode())+1 for m,_ in m4)
    predicted = len(h4)+external_bytes+1+retained_total+separators+1+len(wrapper)
    assert predicted == 1_856_430
    assert internal_count == 4 and len(externals) == 24
    assert externals == load(V4/'input-pins.json')['external_imports']
    assert predicted == load(V4/'preparation.json')['predicted_solution_bytes']
    old_upload = V3/'draft/Solution.lean'
    assert digest(read(old_upload)) == '024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
    after = {p:digest(read(ROOT/p)) for p in bound}
    assert after == bound
    report = {
      'schema':'tiny-dedup-independent-byte-review-v1','passed':True,
      'scope':'Pure source byte/text/AST identity; no theorem checking or runtime claim',
      'canonical_to_production_inverse_exact':True,
      'canonical_kept_prefix_bytes':cut,'removed_retired_code_bytes':6092,
      'retained_retired_copyright_comments':len(comments),
      'canonical_copyright_license_blocks_retained':len(notices),
      'license_trailer_bytes':len(original)-trailer,
      'same_seven_byte_name_family_replacement':True,
      'retired_declarations':[[k.decode(),n.decode()] for k,n in retired_declarations],
      'independently_compared_Dev_segments':segment_results,
      'packed_payload_count':137,'all_packed_payload_bytes_identical':True,
      'cursor_ready_matching_lines_count':len(cursor_lines),
      'ten_table_definition_or_proof_names_retained':aliases,
      'client_import_only':client_results,
      'generator_AST_equal_modulo_MODULES':True,'wrapper_identical':True,
      'three_public_statements_match_official_template':True,
      'candidate_parameters_identical':True,'Final_literal_expressions':declarations,
      'Final_root_count_functions_unchanged':True,
      'Final_actual_theorems_no_extra_premises_relative_passed_Phase4':True,
      'predicted_solution_bytes':predicted,'predicted_headroom_bytes':2_000_000-predicted,
      'external_import_count':24,'internal_import_count':4,
      'v3_upload_sha256_unchanged':digest(read(old_upload)),
      'all_bound_source_hashes_start_end_equal':True,'bound_inputs_sha256':bound,
      'producer_modules_imported':0,'generator_executions':0,'Lean_runs':0,
      'mathematical_evaluations':0,'network_requests':0,
      'official_website_acceptance':False,'total_3200s_success_inferred':False}
    exclusive_json(HERE/'independent-review.json',report)
    exclusive_json(HERE/'audit-files.json',{
      'schema':'tiny-dedup-independent-review-files-v1',
      'files':[info(Path(__file__)),info(HERE/'NOTE.zh.md'),info(HERE/'independent-review.json')],
      'read_dependencies':[info(ROOT/p) for p in sorted(bound)],
      'scope':report['scope'],'all_bound_inputs_unchanged':True})
    print(json.dumps({'passed':True,'predicted_solution_bytes':predicted,
                      'audit_manifest_sha256':digest(read(HERE/'audit-files.json'))}))

if __name__ == '__main__':
    main()
