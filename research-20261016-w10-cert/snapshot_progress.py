"""Bind the completed auxiliary proofs without claiming the unfinished floor."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def main():
  modules=['LocalChecker','Smoke','Coercivity','TreeCoverage','RootBounds',
    'Reflection','FinalConditional','FloorTransfer','OrderCoverage','LeafDispatch',
    'CompactLeaf','RelCompactLeaf','NumeralCodec','EncodedLiteral','CompactSmoke','ClosedTreeSmoke']
  inputs={str(p.relative_to(ROOT)).replace('\\','/'):hashlib.sha256(p.read_bytes()).hexdigest()
    for n in modules if (p:=ROOT/'StructuralW10Cert20261016'/f'{n}.lean').exists()}
  receipts=['root-modules-verification.json','review-lean-verification.json','closed-tree-smoke-lean.json']
  for n in receipts:
    p=HERE/n;j=json.loads(p.read_text());assert j.get('passed') is True,n
    inputs[str(p.relative_to(ROOT)).replace('\\','/')]=hashlib.sha256(p.read_bytes()).hexdigest()
  result={'scope':'Completed auxiliary formalization and partial finite research only',
    'candidate_exact': '3338842690820594373879991756052499665323/4956700000000000000000000000000000000000',
    'candidate_percent_rounded':'67.3601930886','current_site_percent_truncated':'67.3581307708',
    'complete_global_floor_proven':False,'higher_kappa_proven':False,'upload_ready':False,
    'completed':['Exact weight admissibility and pressure','Initial coercive domain',
      'Executable integer leaf checker and its soundness','Reversal invariance',
      'Sound ordered endpoint tightening','Conditional counting transfer',
      'Compact numeral expansion and selected leaf/subtree kernel checks'],
    'remaining':['Complete finite partition and its kernel proof','Source-size compliant standalone proof',
      'Trusted-statement comparison','Full default-kernel and nanoda replay','Final submission materials'],
    'bound_source_and_receipt_sha256':inputs,
    'partial_integer_audits':'Checkpoint audits are partial and are never a global proof. Raw search checkpoints remain local until complete compressed archival.',
    'submitted':False,'official_website_acceptance':False}
  (HERE/'progress.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
  print(json.dumps({k:v for k,v in result.items() if k!='bound_source_and_receipt_sha256'}))
if __name__=='__main__':main()
