"""Static declaration comparison only: no WZ evaluation, payload decode or Lean."""
from pathlib import Path
import ast, hashlib, importlib.util, json, re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
NEW=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
OLD=ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean'
LIB=ROOT/'research-goal-20261018-record-source-audit/extract_static.py'
spec=importlib.util.spec_from_file_location('static_text_helpers',LIB)
helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
def sha(b):return hashlib.sha256(b).hexdigest()
def record(p):
 b=p.read_bytes();return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':sha(b)}
def norm(s):
 return re.sub(r'\s+','',re.sub(r'\bnoncomputable\s+(?=def\b)','',helpers.comments_masked(s)))
texts={k:p.read_text(encoding='utf-8') for k,p in [('old',OLD),('new',NEW)]}
masked={k:helpers.comments_masked(t) for k,t in texts.items()}
def decl(k,name,marker):
 t=texts[k];cm=masked[k];start=cm.index(marker) if marker else 0
 matches=[m for m in helpers.DECL.finditer(cm) if m.start()>=start and m.group(1)==name]
 assert matches,(k,name,marker)
 m=matches[0];end=helpers.BOUND.search(cm,m.end());z=end.start() if end else len(t)
 raw=t[m.start():z].rstrip()
 return raw,{'line':t.count('\n',0,m.start())+1,'bytes':len(raw.encode()),
             'text_sha256':sha(raw.encode()),'normalized_sha256':sha(norm(raw).encode())}
BASE='namespace AMW.G\n'
groups=[('AMW.G',BASE,['DZ','ndivc','SC','DZ2','PLN','PUN','E20','ERRD','E9',
 'CDEN','SDEN','SCDEN','DZp','cosP','cosN','sinP','sinN','scP','scN',
 'GAM0','GAM1','RHOC','SIGC','CE','CJ','Acc.put','mnum','hden','mneg','hneg','farJ','farAcc','CellA']),
 ('AMW.G.SZ','namespace SZ\n',['ofN','add','sub','neg','mul','muln','le','nonneg','min','max','fl','ce']),
 ('AMW.G.IV','namespace IV\n',['ofN','zero','add','sub','neg','muln','mul','mulc','divn','divp','scl']),
 ('AMW.G.CellA','namespace CellA\n',['k','side','LLO','UHI','AD','RLO','RHI','TLZ','TUZ',
 'CI','SI','km4','CX','SX','BLZ','BUZ','BI','PG','NI','E0','E1','EI','ok','FA',
 'nearOn','S0','j0','B0','SF0','K0','KA','KAn']),
 ('AMW.Cert.CellN','namespace CellN\n',['LN','UN','A','okC','NLOZ','DHIZ','WZ']),
 ('AMW.Cert','namespace AMW.Cert\n',['KB','SC','SW']),
 ('AMW.Cert.PCell','',['coverChk','badOf','coverChk_sound'])]
rows=[];raws={}
for prefix,marker,names in groups:
 for name in names:
  label=prefix+'.'+name;vals={k:decl(k,name,marker) for k in ['old','new']}
  raws[label]={k:v[0] for k,v in vals.items()}
  rows.append({'name':label,**{k:v[1] for k,v in vals.items()},
               'same_after_comments_whitespace_noncomputable':norm(vals['old'][0])==norm(vals['new'][0])})
coeff={}
for k in ['old','new']:
 raw,meta=decl(k,'cAMn','');coeff[k]={int(j):int(v) for j,v in re.findall(r'\| (\d+) => (-?\d+)',raw)}
 assert list(coeff[k])==list(range(13))
changes={str(abs(coeff['old'][j])):str(abs(coeff['new'][j])) for j in range(1,13)}
different=[r['name'] for r in rows if not r['same_after_comments_whitespace_noncomputable']]
assert set(different)=={'AMW.G.CE','AMW.G.CJ','AMW.G.CellA.FA'},different
for label in different:
 oldraw=raws[label]['old'];mapped=re.sub(r'\b\d+\b',lambda m:changes.get(m.group(),m.group()),oldraw)
 assert norm(mapped)==norm(raws[label]['new']),label
ce_raw=raws['AMW.G.CE']['new'];cj_raw=raws['AMW.G.CJ']['new']
ce=[(int(j),int(e),sg=='true') for j,e,sg in re.findall(r'\((\d+), (\d+), (true|false)\)',ce_raw)]
cj=[(int(j),int(e),sg=='true') for j,e,sg in re.findall(r'\| (\d+) => \((\d+), (true|false)\)',cj_raw)]
assert len(ce)==len(cj)==12
assert all(e==abs(coeff['new'][j]) and sg==((coeff['new'][j]<0) != bool(j%2)) for j,e,sg in ce)
assert all(e==abs(coeff['new'][j]) and sg==(coeff['new'][j]<0) for j,e,sg in cj)
constants={}
for label in ['AMW.G.DZ','AMW.G.SC','AMW.G.DZ2','AMW.G.PLN','AMW.G.PUN','AMW.G.E20',
              'AMW.G.ERRD','AMW.G.E9','AMW.G.GAM0','AMW.G.GAM1','AMW.G.RHOC',
              'AMW.G.SIGC','AMW.Cert.KB','AMW.Cert.SC','AMW.Cert.SW']:
 constants[label]=raws[label]['new']
script=ROOT/'scripts/finite_margin_20261015.py'
pytext=script.read_text(encoding='utf-8');tree=ast.parse(pytext)
functions={n.name:ast.get_source_segment(pytext,n) for n in tree.body
           if isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in ['IV','cell_wz','cover_thresholds']}
assert set(functions)=={'IV','cell_wz','cover_thresholds'}
obj={'scope':'Static source normalization and dependency comparison. No integer WZ query evaluated.',
 'source_records':[record(NEW),record(OLD),record(script),record(LIB)],'declarations':rows,
 'declaration_count':len(rows),'same_count':len(rows)-len(different),'different':different,
 'differences_exactly_profile_magnitude_literals':True,'old_to_new_magnitude_map':changes,
 'new_cAMn':coeff['new'],'new_CE':ce,'new_CJ':cj,'new_shared_constants_raw':constants,
 'old_Python_source_excerpts':functions,
 'claim':'Same source WZ dependency structure except CE/CJ/FA profile literals. Python WZ translation is statically reviewed, not executed or kernel-proved here.',
 'new_root_true_COV_replayed':False,'Lean_invocations':0,'solver_calls':0,
 'kernel_function_sampling_calls':0,'leaf_payload_decoded':False}
out=HERE/'comparison.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':record(out)['sha256'],
                  'declarations':len(rows),'same':len(rows)-len(different),'different':different},ensure_ascii=False))
