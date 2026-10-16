"""Convert a closed ordered W10 search tree to verified compact leaf payloads.

Every changed support is rechecked with exact integers. This does not replace
Lean's check of all leaves and coverage. The input and all helper scripts are
SHA256-bound in the resulting receipt.
"""
from pathlib import Path
import argparse,hashlib,json,time
import relative_codec as codec
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'ordered-complete.json')
 ap.add_argument('--output',type=Path,default=HERE/'ordered-compact.json');ap.add_argument('--rounds',type=int,default=4)
 ap.add_argument('--allow-partial',action='store_true');args=ap.parse_args();raw=args.input.read_bytes();doc=json.loads(raw)
 pending=doc.get('unresolved',[])
 if pending and not args.allow_partial:raise SystemExit('Input tree is not closed: '+str(len(pending))+' unresolved cells')
 started=time.monotonic();leaves=[];seen=set();numbers=sourcebytes=fsbits=0
 for idx,x in enumerate(doc['accepted']):
  path=x['path'];assert path not in seen,path;seen.add(path);rec=x['result']
  if 'FS' in rec:
   c=codec.prepare(rec,args.rounds);assert int(c['after_numerator'])>=codec.thin.THRESH
   leaves.append({'path':path,'kind':'numeric','text':c['text'],'support_hex':c['support_hex'],
    'tree_code':c['tree_code'],'after_numerator':c['after_numerator'],'source_bytes':c['text_source_bytes']})
   numbers+=1;sourcebytes+=c['text_source_bytes'];fsbits+=c['support_bits']
  elif rec.get('empty'):
   leaves.append({'path':path,'kind':'reflection' if rec.get('reflection') else 'empty',
    'violation_axis':rec.get('violation_axis')})
  else:raise AssertionError(('Unsupported accepted leaf',path,rec.keys()))
  if (idx+1)%2000==0:print(json.dumps({'converted':idx+1,'numeric':numbers,'seconds':time.monotonic()-started}),flush=True)
 receipt={'scope':'Exact compact payload preparation; Lean global proof is a separate required check.',
  'input':str(args.input),'input_sha256':sha(raw),'input_closed':not bool(pending),'accepted_count':len(leaves),
  'numeric_count':numbers,'unresolved_count':len(pending),'rounds':args.rounds,'relative_FS_bits':fsbits,
  'base92_payload_source_bytes':sourcebytes,'average_numeric_source_bytes':sourcebytes/max(numbers,1),
  'all_numeric_integer_checks_passed':True,'elapsed_seconds':time.monotonic()-started,
  'helpers_sha256':{p:sha((HERE/p).read_bytes()) for p in ['convert_ordered.py','relative_codec.py','compact_thin.py','tree_flow.py','generate.py']},
  'encoding':'39-bit presence; nonzero kind 0=single,10=table+tangent,11=two tangents; cell-relative 32-grid point; second-point tags; low-first 8 decimal Prüfer digits; base92(support*10^8+treecode).'}
 args.output.write_text(json.dumps({'receipt':receipt,'leaves':leaves},ensure_ascii=False,separators=(',',':'))+'\n',encoding='utf8')
 print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
