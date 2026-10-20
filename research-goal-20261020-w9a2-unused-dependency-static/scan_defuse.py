"""Source-only lexical def-use for a fixed list of deletion candidates.
No Lean import, compiler, generated export, proof evaluation or source mutation.
The lexical graph is supplementary to the separately read existing export.
"""
from pathlib import Path
import collections
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'submission/w9a2-weighted-potential-20261020-prepared-v6/proof/Solution.lean'
OUT = Path(__file__).resolve().parent
TARGETS = {
    'AMW.Cert.PCell.root_cover', 'AMW.Cert.PC9QB6M.quant_forget',
    'AMW.Cert.PC9QB6M.cert_of', 'AMW.Cert.PC9QB6MData.cert',
    'AMW.Cert.PC9QB6M_half', 'AMW.Cert.PC9QB6M_cert_full', 'RiemannFail.cert_AM',
    'OpethN.remainder_bound_n', 'OpethN.block_remainder_bound_n',
    'OpethN.matching_defect_bound_n',
    'OpethN.ActualDefect.actual_defect_estimate', 'OpethN.ActualDefect.actual_dyadic',
    'OpethN.ActualDefect.actual_cumulative', 'Opeth.AMFinal.actual_dyadic',
    'Opeth.AMFinal.actual_cumulative', 'StructuralW9A220261020.Localization.base_floor',
    'StructuralW9A220261020.Localization.dagThreshold',
    'StructuralW9A220261020.Localization.dag_cost_of_late',
    'StructuralW9A220261020.Localization.low_DAG_state',
}


def masked(s):
    out = list(s); i = 0; depth = 0; string = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; step = 2
            elif s.startswith('-/', i): depth -= 1; step = 2
            else: step = 1
        elif string:
            if s[i] == '\\': step = min(2, len(s)-i)
            else:
                if s[i] == '"': string = False
                step = 1
        elif s.startswith('/-', i): depth = 1; step = 2
        elif s.startswith('--', i):
            step = s.find('\n', i)-i if '\n' in s[i:] else len(s)-i
        elif s[i] == '"': string = True; step = 1
        else: i += 1; continue
        for k in range(i, i+step):
            if s[k] not in '\r\n': out[k] = ' '
        i += step
    assert not depth and not string
    return ''.join(out)


raw = SOURCE.read_bytes(); text = raw.decode('utf-8'); code = masked(text)
lines = code.splitlines(keepends=True); original = text.splitlines(keepends=True)
offsets = [0]
for line in original: offsets.append(offsets[-1] + len(line.encode('utf-8')))
declpat = re.compile(r'^(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|opaque|axiom|instance|structure|class|inductive)\s+([^\s(:{\[]+)')
contextpat = re.compile(r'^(?:namespace\s+|(?:noncomputable\s+)?section\b|end\b|open\b|variable\b|set_option\b|attribute\b|#)')
stack = []; ns = ''; commands = []; declarations = []; errors = []
for no, line in enumerate(lines, 1):
    stripped = line.strip()
    # Namespace/section commands in this frozen source begin at column zero.
    if not stripped or line[0].isspace(): continue
    m = declpat.match(line)
    if m:
        name = (ns+'.' if ns else '') + m[2]
        d = dict(name=name, namespace=ns, kind=m[1], line=no, offset=offsets[no-1])
        declarations.append(d); commands.append((no, d))
    elif contextpat.match(line): commands.append((no, None))
    m = re.fullmatch(r'namespace\s+(\S+)', stripped)
    if m:
        stack.append(('namespace', ns)); ns = (ns+'.' if ns else '')+m[1]
    elif re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+\S+)?', stripped):
        stack.append(('section', ns))
    elif re.fullmatch(r'end(?:\s+\S+)?', stripped):
        if not stack: errors.append(dict(line=no,error='unmatched end'))
        else: _, ns = stack.pop()
for j,(no,d) in enumerate(commands):
    if d:
        end = commands[j+1][0]-1 if j+1 < len(commands) else len(lines)
        d.update(end_line=end, bytes=offsets[end]-d['offset'])
        d['text'] = ''.join(lines[no-1:end])
byname = {d['name']:d for d in declarations}
byleaf = collections.defaultdict(list)
for d in declarations: byleaf[d['name'].split('.')[-1]].append(d['name'])
refs = collections.defaultdict(list); uncertain = []
tokenpat = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
for caller in declarations:
    body = caller['text']; first = True
    for m in tokenpat.finditer(body):
        token = m[0]
        if first and token in {'theorem','lemma','def','abbrev','opaque','axiom','instance','structure','class','inductive'}:
            first = False; continue
        # Ignore the declaration's own header name, not body recursion.
        if '\n' not in body[:m.start()] and token == caller['name'].split('.')[-1]: continue
        leaf = token.split('.')[-1]
        if leaf not in {n.split('.')[-1] for n in TARGETS}: continue
        candidates = []
        parts = caller['namespace'].split('.') if caller['namespace'] else []
        for k in range(len(parts),-1,-1):
            trial = '.'.join(parts[:k]+[token])
            if trial in byname: candidates=[trial]; break
        if not candidates and len(byleaf[leaf]) == 1: candidates=byleaf[leaf]
        if not candidates:
            uncertain.append(dict(caller=caller['name'], token=token)); continue
        if candidates[0] in TARGETS:
            refs[candidates[0]].append(dict(caller=caller['name'], token=token,
                line=caller['line']+body[:m.start()].count('\n')))
selected=[]
for n in sorted(TARGETS):
    if n not in byname:
        selected.append(dict(name=n,missing_from_lexical_names=True));continue
    d=byname[n]
    selected.append({k:d[k] for k in ['name','kind','line','end_line','offset','bytes']} |
        dict(incoming=refs[n], incoming_outside_selected=[r for r in refs[n] if r['caller'] not in TARGETS]))
result=dict(scope='Lexical source references; no Lean name elaboration. All selected are ordinary theorem/def declarations. Existing root-export absence is a separate complementary check.',
    source_sha256=hashlib.sha256(raw).hexdigest(),source_bytes=len(raw),
    parsed_declarations=len(declarations),scope_stack_at_end=stack,scope_errors=errors,
    candidates=selected,total_candidate_declaration_bytes=sum(r.get('bytes',0) for r in selected),
    uncertain_selected_leaf_tokens=uncertain,compiler_or_proof_or_source_edits=0)
path=OUT/'source-def-use.json'
with path.open('x',encoding='utf-8') as f: json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'candidates','uncertain_selected_leaf_tokens'}}))
print(json.dumps(selected))
