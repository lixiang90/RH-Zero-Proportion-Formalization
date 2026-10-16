"""Seal the actual lifted pilot only after every current source has passed.

This records ordinary Lean verification. It deliberately does not claim a
new independent Nanoda replay, a complete global cover, or a zero record.
"""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    proof=json.loads((HERE/'lean_verification.json').read_bytes())
    results={x['module']:x for x in proof['modules']}
    names=['WindowLiftedPilotData']+[f'WindowLiftedPilotAtoms{k:02}'for k in range(6)]+[
        'WindowLiftedPilotAtomsAll','WindowLiftedPilotAggregate','WindowLiftedPilot']
    upstream=['WindowLiftedFarkas','WindowDerivativeGraph','WindowLiftedKKT','WindowGraphCover']
    allowed={'propext','Classical.choice','Quot.sound'};bound=[];roots=[]
    for name in upstream+names:
        module='StructuralGoal20261016.'+name;p=ROOT/(module.replace('.','/')+'.lean');r=results[module]
        assert r['passed'] and r.get('source_unchanged',True),module+' has not passed'
        digest=sha(p);assert digest==r['source_sha256'],module+' current source changed'
        log=HERE/r['log'];text=log.read_bytes().decode('utf8',errors='replace')
        actual=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
        expected=p.read_text(encoding='utf8').count('#print axioms ')
        assert len(actual)==expected,(module,expected,len(actual))
        for symbol,axs in actual:
            axiomset={a.strip()for a in axs.split(',')if a.strip()}
            assert axiomset<=allowed,(symbol,axiomset)
            roots.append({'symbol':symbol,'axioms':sorted(axiomset),'module':module})
        bound.append({'module':module,'source':str(p.relative_to(ROOT)).replace('\\','/'),
            'source_sha256':digest,'source_bytes':p.stat().st_size,'log':r['log'],'log_sha256':sha(log),
            'ordinary_Lean_passed':True,'proof_roots_printed':len(actual),'seconds':r.get('whole_process_seconds')})
    inputs=['cover-lifted-graph-pilot.json','window_generate_lifted_pilot.py','window_generate_lifted_pilot_proofs.py',
        'window_lifted_pilot_generation.json',Path(__file__).name]
    out={'scope':__doc__,'actual_theorem':'StructuralGoal20261016.WindowLiftedPilot.exclude',
        'ordinary_Lean_complete':True,'fully_actual_scalar_and_facet_premises_discharged':True,
        'local_exclusion_requires':['Relevant (123/128) g','WindowDifferenceCell.Contains WindowLiftedPilotData.cell g'],
        'atoms':43,'slabs':10,'graph_facets':22,'facet_grid_cells':623,'active_derivative_variables':31,
        'strict_integer_margin':'12310810974159504285408296960000000000',
        'modules':bound,'roots':roots,'inputs':{p:sha(HERE/p)for p in inputs},
        'independent_Nanoda_replayed':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    dest=HERE/'window_lifted_pilot_formal_manifest.json';dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    files=[x['source']for x in bound]+['research-goal-20261016/'+x['log']for x in bound]+[
        'research-goal-20261016/'+p for p in inputs]+['research-goal-20261016/'+dest.name,
        'research-goal-20261016/lean_verification.json','research-goal-20261016/window_lifted_pilot_sync_files.json']
    (HERE/'window_lifted_pilot_sync_files.json').write_text(json.dumps(files,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'ordinary_Lean_complete':True,'modules':len(bound),'roots':len(roots),'owned_source_bytes':sum(x['source_bytes']for x in bound if x['module'].rsplit('.',1)[1]in names),
        'manifest_sha256':sha(dest),'new_zero_proportion_proven':False}),flush=True)
if __name__=='__main__':main()
