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
    # A single fully qualified audit resolves scope-dependent pretty-printer
    # abbreviations (e.g. `choice` under `open Classical`). Bind it to exactly
    # the source hashes imported by that audit rather than assuming an alias.
    audit_rows={};audit_roots={};audit_receipt=None
    manifest=HERE/'ordinary-axiom-audit-dependencies.json'
    if manifest.exists():
        dep=json.loads(manifest.read_bytes())
        for row in records:
            if row['module']!='StructuralGoal20261016.WindowAxiomAudit' or not row.get('passed'):continue
            source=ROOT/'StructuralGoal20261016/WindowAxiomAudit.lean';log=HERE/row['log']
            if not (source.exists() and log.exists() and sha(source)==row['source_sha256']==dep['audit_source_sha256'] and sha(log)==row['log_sha256']):continue
            text=log.read_bytes().decode('utf8',errors='replace').replace('\x00','')
            parsed=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
            audit_roots={name:sorted({x.strip() for x in group.split(',') if x.strip()}) for name,group in parsed}
            assert set(dep['printed_roots'])<=set(audit_roots)
            assert all(set(v)<=set(['propext','Classical.choice','Quot.sound']) for v in audit_roots.values())
            audit_rows={x['module']:x['source_sha256'] for x in dep['modules']}
            audit_receipt={'source_sha256':row['source_sha256'],'log_sha256':row['log_sha256'],
                'dependencies_manifest_sha256':sha(manifest),'root_count':len(audit_roots)}
    selected={};data_only={};unresolved={}
    for row in records:
        source=ROOT/(row['module'].replace('.','/')+'.lean')
        log=HERE/row.get('log','missing')
        if not(row.get('passed') and source.exists() and log.is_file()):continue
        if sha(source)!=row.get('source_sha256') or sha(log)!=row.get('log_sha256'):continue
        text=log.read_bytes().decode('utf8',errors='replace').replace('\x00','')
        ax=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
        axioms=sorted({x.strip() for group in ax for x in group.split(',') if x.strip()})
        roots=re.findall(r"'([^']+)' depends on axioms:",text)
        resolved=False
        if ax and audit_rows.get(row['module'])==row['source_sha256'] and set(roots)<=set(audit_roots):
            axioms=sorted({a for root in roots for a in audit_roots[root]});resolved=True
        canonical=set(axioms)<=set(['propext','Classical.choice','Quot.sound'])
        sealed={**row,'source':str(source.relative_to(ROOT)).replace('\\','/'),
            'log':str(log.relative_to(ROOT)).replace('\\','/'),'printed_axioms':axioms,
            'has_printed_axiom_audit':bool(ax),
            'resolved_by_full_name_audit':resolved,
            'independent_nanoda_replay_run':False}
        # A compiled table definition is not a proof that its entries enclose
        # actual derivatives. Keep its receipt, but count it separately.
        (selected if canonical and ax else unresolved if ax else data_only)[row['module']]=sealed
    out={'scope':__doc__,'seal_script_sha256':sha(Path(__file__)),
         'verified_module_count':len(selected),'modules':list(selected.values()),
         'compiled_without_printed_axiom_audit_count':len(data_only),
         'compiled_without_printed_axiom_audit':list(data_only.values()),
         'compiled_pending_full_name_axiom_audit':list(unresolved.values()),
         'full_name_audit':audit_receipt,
         'complete_global_cover_proven':False,'new_unconditional_zero_proportion_proven':False,
         'submission_ready':False}
    dest=HERE/'ordinary-verified-current.json';dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'verified_module_count':len(selected),'modules':list(selected)}))
if __name__=='__main__':main()
