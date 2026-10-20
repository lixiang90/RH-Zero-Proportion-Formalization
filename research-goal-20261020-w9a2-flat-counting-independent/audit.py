"""Static frozen flat Counting diagnosis only. No Lean/compiler/proof execution."""
import hashlib
import json
from pathlib import Path
import re
from collections import Counter

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
SOURCE=ROOT/'tmp/w9a2-20261020/fullchain-v1/source/Solution/Candidate.lean'
LOG=ROOT/'tmp/w9a2-20261020/fullchain-v1/logs/ordinary-Solution.Candidate.log'
def pin(p):
    raw=p.read_bytes();return dict(path=str(p),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def mask(text):
    out=list(text);i=0;depth=0;quoted=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;out[i:i+2]='  ';i+=2
            elif text.startswith('-/',i):depth-=1;out[i:i+2]='  ';i+=2
            else:
                if text[i]!='\n':out[i]=' '
                i+=1
        elif quoted:
            if text[i]=='\\':out[i]=' ';i+=1
            elif text[i]=='"':quoted=False;out[i]=' ';i+=1;continue
            if i<len(text):
                if text[i]!='\n':out[i]=' '
                i+=1
        elif text.startswith('/-',i):depth=1;out[i:i+2]='  ';i+=2
        elif text.startswith('--',i):
            stop=text.find('\n',i);stop=len(text) if stop<0 else stop
            out[i:stop]=' '*(stop-i);i=stop
        elif text[i]=='"':quoted=True;out[i]=' ';i+=1
        else:i+=1
    assert not depth and not quoted
    return ''.join(out)
text=SOURCE.read_text(encoding='utf-8');clean=mask(text);lines=clean.splitlines()
begin=text.index('/- BEGIN FLATTENED MODULE StructuralW9A220261020.Counting -/')
end=text.index('/- BEGIN FLATTENED MODULE StructuralW9A220261020.Final -/')
first=text[:begin].count('\n')+1;last=text[:end].count('\n')
stack=[dict(header='',namespace='',opens=[])];scope_errors=[];declarations=[];contexts={}
for number,line in enumerate(lines,1):
    value=line.strip();cur=stack[-1]
    nm=re.match(r'^namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$',value)
    sec=re.match(r'^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_.]*))?\s*$',value)
    stop=re.match(r'^end(?:\s+([A-Za-z_][A-Za-z0-9_.]*))?\s*$',value)
    if nm or sec:
        parts=(nm.group(1) if nm else sec.group(1) or '').split('.')
        for part in parts:
            ns='.'.join(filter(None,[stack[-1]['namespace'],part])) if nm else stack[-1]['namespace']
            stack.append(dict(header=part,namespace=ns,opens=list(stack[-1]['opens'])))
    elif stop:
        parts=stop.group(1).split('.') if stop.group(1) else ['']
        actual=[s['header'] for s in stack[-len(parts):]]
        if actual!=parts:scope_errors.append(dict(line=number,end=parts,actual=actual))
        if len(stack)>len(parts):del stack[-len(parts):]
        else:scope_errors.append(dict(line=number,error='scope underflow'))
    elif value.startswith('open ') and not value.startswith('open scoped ') and not re.search(r'\bin\s*$',value):
        for name in re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',value[5:]):
            if '(' not in value:stack[-1]['opens'].append(dict(name=name,line=number))
    decl=re.match(r'^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:def|abbrev|lemma|theorem|structure|class|inductive)\s+([A-Za-z_][A-Za-z0-9_.]*)',value)
    if decl:
        name='.'.join(filter(None,[stack[-1]['namespace'],decl.group(1)]))
        declarations.append(dict(name=name,line=number))
    if first<=number<=last:contexts[number]=list(stack[-1]['opens'])
all_decls={d['name'] for d in declarations};potential={}
counting_clean='\n'.join(lines[first-1:last])
for number in range(first,last+1):
    line=lines[number-1]
    for token in set(re.findall(r'(?<![A-Za-z0-9_.])[A-Za-z_][A-Za-z0-9_]*',line)):
        candidates=sorted({o['name']+'.'+token for o in contexts[number] if o['name']+'.'+token in all_decls})
        if len(candidates)>1:potential.setdefault(token,dict(candidates=candidates,lines=[]))['lines'].append(number)
log=LOG.read_text(encoding='utf-8');errors=re.findall(r'Candidate\.lean:(\d+):(\d+): error: ([^\n]+)',log)
assert [int(e[0]) for e in errors]==[16765,16785,16812,16842]
wfun_lines=[first+i for i,line in enumerate(lines[first-1:last]) if re.search(r'(?<![A-Za-z0-9_.])wfun\b',line)]
assert wfun_lines==[16765,16785,16812]
assert 'then sorry else 0' in log and 'he :' in log and 'hb :' in log
assert 'theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl' in text
# Pure symbolic linear certificate after restoring one shared band sum Q.
inequalities=[dict(Q=1,P=1,cm=-1,ck=1,C=1),dict(D=1,A=1,Q=-1),dict(BR=1,P=-1),dict(F=1,D=-1)]
total=Counter()
for poly in inequalities:total.update(poly)
total={k:v for k,v in total.items() if v}
assert total==dict(cm=-1,ck=1,C=1,A=1,BR=1,F=1)
result=dict(scope='Independent static name-resolution/source/algebra review; not flat Lean PASS',
  compiler_runs=0,proof_runs=0,source=pin(SOURCE),log=pin(LOG),Counting_flat_lines=[first,last],
  exact_errors=[dict(line=int(a),column=int(b),message=c) for a,b,c in errors],
  bare_wfun_lines=wfun_lines,correct_qualified_name='Zeta23Ext.Bridge.wfun',
  kernel_aliases_definitionally_equal=True,existing_rfl_theorem='RiemannFail.cert_wfun_eq',
  linarith_failure_is_downstream_of_ambiguous_he_sum=True,
  restored_shared_band_sum_linear_certificate=total,
  lexical_scope_scan_errors=scope_errors,
  active_Cert_opens_at_first_wfun=[o for o in contexts[16765] if o['name'].startswith('AMW.Cert')],
  active_Bridge_opens_at_first_wfun=[o for o in contexts[16765] if o['name']=='Zeta23Ext.Bridge'],
  text_declared_open_namespace_collision_candidates=potential,
  limitation='Lexical collision inventory covers declarations in this frozen flat source, not all imported library overloads or a substitute for Lean elaboration')
with (HERE/'audit.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(bare_wfun_lines=wfun_lines,scope_errors=len(scope_errors),collision_candidates=potential,shared_sum_certificate=total)))
