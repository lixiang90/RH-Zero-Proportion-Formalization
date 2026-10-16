"""Seal only current, actually passed ordinary-kernel modules and their logs."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    records=[]
    for name in ['lean_verification.json','lean_priority_verification.json']:
        p=HERE/name
        if p.exists():records.extend(json.loads(p.read_bytes()).get('modules',[]))
    selected={}
    for row in records:
        source=ROOT/(row['module'].replace('.','/')+'.lean')
        log=HERE/row.get('log','missing')
        if not(row.get('passed') and source.exists() and log.is_file()):continue
        if sha(source)!=row.get('source_sha256') or sha(log)!=row.get('log_sha256'):continue
        text=log.read_bytes().decode('utf8',errors='replace').replace('\x00','')
        ax=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
        assert ax,('No axiom output in successful log',log)
        axioms=sorted({x.strip() for group in ax for x in group.split(',') if x.strip()})
        assert set(axioms)<=set(['propext','Classical.choice','Quot.sound']),(source,axioms)
        selected[row['module']]={**row,'source':str(source.relative_to(ROOT)).replace('\\','/'),
            'log':str(log.relative_to(ROOT)).replace('\\','/'),'printed_axioms':axioms,
            'independent_nanoda_replay_run':False}
    out={'scope':__doc__,'seal_script_sha256':sha(Path(__file__)),
         'verified_module_count':len(selected),'modules':list(selected.values()),
         'complete_global_cover_proven':False,'new_unconditional_zero_proportion_proven':False,
         'submission_ready':False}
    dest=HERE/'ordinary-verified-current.json';dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'verified_module_count':len(selected),'modules':list(selected)}))
if __name__=='__main__':main()
