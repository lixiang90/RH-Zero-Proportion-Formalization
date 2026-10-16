"""Conservative packaging graph from existing Lean .ilean source indexes.

These are syntactic references, not a kernel dependency assertion. Definitions
and theorems pruned using them must subsequently compile and replay in a fresh
overlay; implicit elaborator dependencies may require restoring declarations.
"""
from pathlib import Path
import bisect,hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
BASE=Path('/var/tmp/rh-zero-20261015')
MODULES=['GramDefect20261015.Core','GramDefect20261015.SharpWindow','GramDefect20261015.RefinedCounting',
 'StructuralResearch20261016.W10RefinedCandidate','StructuralResearch20261016.Coboundary',
 'StructuralResearch20261016.CoboundaryCounting','StructuralW10Cert20261016.LocalChecker',
 'StructuralW10Cert20261016.RootBounds','StructuralW10Cert20261016.TreeCoverage',
 'StructuralW10Cert20261016.CompactLeaf','StructuralW10Cert20261016.RelCompactLeaf',
 'StructuralW10Cert20261016.EncodedLiteral']
LIBS=[BASE/'w10-cert/lib',BASE/'research-20261016/lib',BASE/'record-verification/modular/lib']
def main():
  graphs={};documents={};provenance={};starts={};fallback=[]
  for module in MODULES:
    rel=Path(*module.split('.')).with_suffix('.ilean')
    files=[lib/rel for lib in LIBS if (lib/rel).exists()]
    if not files:
      p=ROOT/Path(*module.split('.')).with_suffix('.lean')
      assert p.exists(),('Missing module source',module)
      fallback.append(p);continue
    p=files[0];raw=p.read_bytes();j=json.loads(raw);assert j['module']==module
    documents[module]=j;provenance[module]={'path':str(p),'sha256':hashlib.sha256(raw).hexdigest()}
    starts[module]=sorted((v[0],v[1],n) for n,v in j['decls'].items())
  for module,j in documents.items():
    for key,ref in j['references'].items():
      key=json.loads(key)
      if 'c' not in key:continue
      c=key['c'];target=(c['m'],c['n'])
      if target[0] not in MODULES:continue
      for u in ref.get('usages',[]):
        if len(u)>4 and isinstance(u[4],str):parent=u[4]
        else:
          # Keep position-labelled references without a declaration parent by
          # making their target a root.  This includes attributes and notation.
          parent='__global__'
        graphs.setdefault((module,parent),set()).add(target)
  core='GramDefect20261015.Core'
  roots=[(m,n) for m,j in documents.items() if m!=core for n in j['decls']]
  roots += [(m,'__global__') for m in documents]
  # Some auxiliary builds did not request .ilean output.  Keep every Core
  # declaration whose final identifier is mentioned in those module sources;
  # ambiguity deliberately retains extra declarations.
  tokens=set()
  for p in fallback:tokens.update(re.findall(r"[\w']+(?:\.[\w']+)*",p.read_text(encoding='utf8')))
  suffixes={t.rsplit('.',1)[-1] for t in tokens}
  roots += [(core,n) for n in documents[core]['decls'] if n.rsplit('.',1)[-1] in suffixes]
  seen=set();todo=list(roots)
  while todo:
    key=todo.pop()
    if key in seen:continue
    seen.add(key);todo.extend(graphs.get(key,()))
  source=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf8');lines=source.splitlines()
  def cp(line,col):return len(lines[line].encode('utf-16-le')[:2*col].decode('utf-16-le'))
  rows=[]
  for n,r in documents[core]['decls'].items():
    sl,sc,el,ec=r[:4]
    if el>=len(lines):assert el==len(lines) and ec==0;endcol=0
    else:endcol=cp(el,ec)
    prefix=lines[sl][cp(sl,sc):].lstrip()
    keep=not re.match(r'(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|abbrev)\b',prefix)
    rows.append({'name':n,'used':keep or (core,n) in seen,
      'range':{'startLine':sl+1,'startColumn':cp(sl,sc),'endLine':el+1,'endColumn':endcol}})
  (HERE/'core-dependencies.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf8')
  result={'scope':__doc__,'index_provenance':provenance,'rows':len(rows),'retained_rows':sum(x['used'] for x in rows),
    'reachable_syntactic_declarations':len(seen),'kernel_dependency_metadata':False,
    'conservative_source_fallback':[str(p) for p in fallback]}
  (HERE/'ilean-dependencies.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
  print(json.dumps({k:v for k,v in result.items() if k not in ['scope','index_provenance']}))
if __name__=='__main__':main()
