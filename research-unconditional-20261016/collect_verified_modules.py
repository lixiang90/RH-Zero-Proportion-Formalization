"""Summarize only successful receipts matching current source and log bytes."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    rows={}
    for path in sorted(HERE.glob('*verification.json')):
        record=json.loads(path.read_text(encoding='utf8'))
        for item in record.get('modules',[]):
            source=ROOT/(item.get('module','').replace('.','/')+'.lean')
            if not item.get('passed') or not item.get('source_unchanged') or not source.is_file():
                continue
            if sha(source)!=item.get('source_sha256'):
                continue
            log=HERE/item.get('log','')
            if not log.is_file() or sha(log)!=item.get('log_sha256'):
                continue
            row={'source_sha256':item['source_sha256'],'ordinary_lean_passed':True,
                 'receipt':str(path.relative_to(ROOT)).replace('\\','/'),
                 'whole_process_seconds':item['whole_process_seconds'],
                 'synchronous_elaboration':item['synchronous_elaboration'],
                 'current_log_matches_receipt':True}
            if 'certificate_seconds' in item:
                row['certificate_seconds']=item['certificate_seconds']
            rows[item['module']]=row
    basin_source=ROOT/'StructuralW10Unconditional20261016/BasinPolynomials.lean'
    basin_generated=ROOT/'research-20261016-w10-unconditional/basin-polynomials-generated.json'
    basin_log=HERE/'BasinPolynomials.log'
    basin={}
    if basin_generated.is_file() and basin_log.is_file():
        generated=json.loads(basin_generated.read_text(encoding='utf8'))
        text=basin_log.read_bytes().decode('utf8',errors='replace')
        basin={'source_matches_generated_receipt':sha(basin_source)==generated['output_sha256'],
               'polynomial_count':generated['polynomial_count'],
               'axiom_outputs':text.count("'StructuralW10Unconditional20261016.BasinPolynomials.lower"),
               'sorryAx_in_log':'sorryAx' in text,
               'global_chamber_coverage_proven':False,'new_unconditional_zeta_bound_proven':False}
    result={'scope':'Current-source ordinary Lean module checks only; no global concrete cover or zeta record is claimed.',
            'website_ready':False,'global_w10_floor_proven':False,'modules':rows,
            'basin_polynomials':basin,
            'matched_32_leaf_comparison':{'adaptive_full_old_seconds':16.691,
                'adaptive_geometry_seconds':4.084,'fixed_full_seconds':11.770,
                'fixed_geometry_seconds':1.854,'streaming_dual_full_seconds':12.303,
                'cached_slope_full_seconds':13.770,
                'caveat':'Old ForcedCoverage2 geometry 12.246s always normalized; it is not an adaptive geometry baseline. Per-move dual and slope caching were slower and are negative experiments.'}}
    (HERE/'verified-module-summary.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'modules':len(rows),'basin_polynomials':basin}),flush=True)

if __name__=='__main__':
    main()
