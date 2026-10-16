"""Delete only complete unused declaration ranges reported by Lean itself.

Namespace, section, option, notation and attribution text is preserved.
The pruned result must compile afresh; dependency metadata is a packaging aid,
not an additional trusted premise of the mathematical result.
"""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent
# The source-index graph does not record the dependency of the retained
# attributed blockOf_apply declaration.  An isolated preflight found this
# omission; retain its definition explicitly and recompile the generated file.
FORCED_KEEP={'Meshuggah.Gram.blockOf'}

def unused_ranges(source):
  rows=json.loads((HERE/'core-dependencies.json').read_text())
  groups={}
  lines=source.splitlines(keepends=True);offsets=[0]
  for line in lines:offsets.append(offsets[-1]+len(line))
  for row in rows:
    r=row['range']
    if r is None:continue
    key=(r['startLine'],r['startColumn'],r['endLine'],r['endColumn'])
    groups.setdefault(key,[]).append(row)
  unused=[]
  used_intervals=[]
  for (sl,sc,el,ec),rs in groups.items():
    if any(r['used'] or r['name'] in FORCED_KEEP for r in rs):used_intervals.append((offsets[sl-1]+sc,offsets[el-1]+ec))
  for (sl,sc,el,ec),rs in groups.items():
    if any(r['used'] or r['name'] in FORCED_KEEP for r in rs):continue
    a=offsets[sl-1]+sc;b=offsets[el-1]+ec
    if any(a<=ua and ub<=b for ua,ub in used_intervals):continue
    # Restrict deletion to top-level declaration commands.  Auxiliary clauses
    # and local declarations often share a parent range; never cut those.
    prefix=source[a:min(b,a+160)].lstrip()
    if not __import__('re').match(r'(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:def|theorem|lemma|abbrev|instance|structure|inductive|opaque)\b',prefix):continue
    unused.append((a,b,[r['name'] for r in rs]))
  # Parent ranges subsume automatically generated companion declarations.
  merged=[]
  for a,b,names in sorted(unused,key=lambda t:(t[0],-t[1])):
    if merged and a<merged[-1][1]:
      assert b<=merged[-1][1],('Partially overlapping Lean declarations',a,b,merged[-1])
      continue
    merged.append((a,b,names))
  return merged

def prune_slice(source,start,end,ranges):
  cursor=start;parts=[]
  for a,b,_ in ranges:
    if a<start or b>end:continue
    parts.append(source[cursor:a]);cursor=b
  parts.append(source[cursor:end])
  return ''.join(parts)

def report(source,ranges):
  result={'scope':'Packaging-only declaration pruning; fresh isolated compilation required',
    'core_sha256':hashlib.sha256(source.encode('utf8')).hexdigest(),
    'metadata_sha256':hashlib.sha256((HERE/'core-dependencies.json').read_bytes()).hexdigest(),
    'forced_keep':sorted(FORCED_KEEP),
    'unused_declaration_ranges':len(ranges),'deletable_source_characters':sum(b-a for a,b,_ in ranges),
    'ranges':[{'start':a,'end':b,'names':names} for a,b,names in ranges]}
  (HERE/'core-pruning.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
  return result

if __name__=='__main__':
  source=(HERE.parent/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
  r=report(source,unused_ranges(source))
  print(json.dumps({k:v for k,v in r.items() if k!='ranges'}))
