"""Freeze the stopped minimal phase challenge and its model-scope audit."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
FILES=['cover_phase_psd_obstruction.py','cover-phase-psd-obstruction.json','cover_phase_psd_challenge.md','cover_phase_psd_manifest.py']
def main():
    rows=[]
    for name in FILES:
        p=HERE/name;b=p.read_bytes();rows.append({'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
    out={'scope':'Stopped fixed-eight phase proxy challenge, exact two-node toy and explicit missing-link audit; no new bound.',
      'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'floating_diagnostics_only':True,
      'PSD_dual_lower_bound_proven':False,'uniform_coefficient_upper_bounds_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-phase-psd-files.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'files':len(rows),'bytes':out['total_bytes']}))
if __name__=='__main__':main()
