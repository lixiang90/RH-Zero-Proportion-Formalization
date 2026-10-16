"""Keep the gamma-positive attribution pilot; add all energy-only bound cases."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def main():
    source=HERE/'cover_global_cut_contractor.py';text=source.read_text(encoding='utf8');needle='            if not any(gamma):continue'
    assert text.count(needle)==1
    text=text.replace(needle,'            # Gamma=0 retains ordinary energy OBBT bounds alongside new global cuts.')
    text=text.replace("default=HERE/'cover-global-cut-contractor.json'","default=HERE/'cover-global-cut-full-contractor.json'")
    target=HERE/'cover_global_cut_full_contractor.py';target.write_text(text,encoding='utf8',newline='\n')
    oldverify=HERE/'cover_global_cut_verify.py';v=oldverify.read_text(encoding='utf8');needle=' and any(gamma)';assert v.count(needle)==1
    v=v.replace(needle,'').replace("default=HERE/'cover-global-cut-contractor.json'","default=HERE/'cover-global-cut-full-contractor.json'").replace("default=HERE/'cover-global-cut-contractor-replay.json'","default=HERE/'cover-global-cut-full-contractor-replay.json'")
    newverify=HERE/'cover_global_cut_full_verify.py';newverify.write_text(v,encoding='utf8',newline='\n')
    oldcontrol=HERE/'cover_global_cut_control.py';c=oldcontrol.read_text(encoding='utf8').replace('identical seventeen refined cells','identical refined cells')
    c=c.replace("HERE/'cover-global-cut-contractor.json'","HERE/'cover-global-cut-full-contractor.json'").replace("HERE/'cover-global-cut-control.json'","HERE/'cover-global-cut-full-control.json'")
    newcontrol=HERE/'cover_global_cut_full_control.py';newcontrol.write_text(c,encoding='utf8',newline='\n')
    files=[source,oldverify,oldcontrol,target,newverify,newcontrol];out={'scope':__doc__,'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    (HERE/'cover-global-cut-full-generated.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))
if __name__=='__main__':main()
