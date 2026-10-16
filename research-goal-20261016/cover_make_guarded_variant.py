"""Keep the verified compact runner frozen; add bounded Windows save retries."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def main():
    source=HERE/'window_compact_obbt_cover.py';original=source.read_text(encoding='utf8')
    needle="temp=args.output.with_suffix('.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\\n',encoding='utf8');temp.replace(args.output)"
    replacement="""temp=args.output.with_suffix('.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\\n',encoding='utf8')
        for attempt in range(80):
            try:temp.replace(args.output);break
            except PermissionError:
                if attempt==79:raise
                time.sleep(.25)"""
    assert original.count(needle)==1
    target=HERE/'window_compact_obbt_guarded_cover.py';target.write_text(original.replace(needle,replacement),encoding='utf8',newline='\n')
    out={'scope':__doc__,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'output_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'mathematical_search_changed':False}
    (HERE/'cover-compact-guarded-generated.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))
if __name__=='__main__':main()
