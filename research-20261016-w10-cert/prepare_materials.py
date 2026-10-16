"""Prepare upload fields only after the exact standalone proof passes all replays."""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal,localcontext,ROUND_DOWN,ROUND_HALF_UP
import hashlib,json
from final_artifact_gate import finite_binding
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
DEST=ROOT/'submission/w10-20261016'
P=3338842690820594373879991756052499665323
Q=4956700000000000000000000000000000000000
PREVIOUS=Fraction(34191001116882886388531117129201664,50760020691785094633026544189453125)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,j):p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
def main():
  if not __debug__:raise RuntimeError('Material preparation assertions must remain enabled')
  proof=DEST/'proof/Solution.lean';manifest=json.loads((DEST/'manifest.json').read_text())
  verified=ROOT/'verification/w10-20261016/single/verification.json'
  v=json.loads(verified.read_text())
  for key in ['passed','local_single_file_verified','ordinary_single_file_lean_passed',
              'statement_equality_proved','permitted_axioms_checked','default_kernel_replay_passed',
              'independent_nanoda_passed','inputs_unchanged']:
    assert v.get(key) is True,('Verification required',key)
  assert v['solution_sha256']==manifest['source_sha256']==sha(proof)
  assert v['solution_bytes']==manifest['source_bytes']==proof.stat().st_size<=2_000_000
  assert v['stage']=='complete' and v['checked_declarations']>0
  assert v['score']=={'numerator':str(P),'denominator':str(Q)}
  assert manifest['numerator']==str(P) and manifest['denominator']==str(Q)
  binding=finite_binding(manifest)
  assert v['finite_certificate_binding']==binding
  contract_path=HERE/'website-snapshot/challenge/contract.json'
  contract=json.loads(contract_path.read_bytes())
  assert v['website_source_sha256']['challenge/contract.json']==sha(contract_path)
  assert v['website_source_commit']=='9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb'
  assert set(v['observed_axioms'])<=set(contract['permittedAxioms'])=={'propext','Classical.choice','Quot.sound'}
  assert set(contract['theorems'].values())<=set(v['export_roots'])
  assert Fraction(P,Q)>PREVIOUS
  audit_path=HERE/'independent-audit-complete.json'
  decode_path=None
  if 'expanded_base_sha256' in manifest:
    decode_path=HERE/'independent-source-decode-complete.json'
    decoded=json.loads(decode_path.read_bytes())
    assert decoded['passed'] is True and decoded['decoded_body_exact_readable_region'] is True
    assert decoded['upload_sha256']==sha(proof)
    assert decoded['readable_sha256']==manifest['expanded_source_sha256']==sha(DEST/'uncompressed/ExpandedSolution.lean')
    assert decoded['decoded_body_sha256']==manifest['expanded_base_sha256']
    assert decoded['source_expansion_commands']==manifest['source_block_count']
    for actual,expected in zip(decoded['blocks'],manifest['source_blocks'],strict=True):
      assert all(actual[key]==expected[key] for key in ['decoded_bytes','decoded_sha256','compressed_bytes','command_sha256'])
    assert decoded['script_sha256']==sha(HERE/'independent_source_decode.py')
    core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
    notice=core[core.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS'):]
    assert notice in proof.read_text(encoding='utf8'), 'Inherited license trailer must remain readable'
  with localcontext() as ctx:
    ctx.prec=100;percent=Decimal(100*P)/Decimal(Q)
    decimal=str(percent);truncated=str(percent.quantize(Decimal('0.0000000001'),rounding=ROUND_DOWN))
    rounded=str(percent.quantize(Decimal('0.0000000001'),rounding=ROUND_HALF_UP))
    gain=str(percent-Decimal(100*PREVIOUS.numerator)/Decimal(PREVIOUS.denominator))
  fields={'status':'LOCALLY_VERIFIED_NOT_SUBMITTED','upload_ready':True,
    'title':'Ten-point Gram-defect certificate with rank-distance nine interactions',
    'numerator':str(P),'denominator':str(Q),'author':'Li Xiang (lixiang90)',
    'model':'GPT-6','harness':'Codex','license':'Apache-2.0',
    'summary':'A re-optimised ten-point weighted Gram-defect certificate, including rank-distance nine pairs, proves the exact separated local floor 433/50000 at pressure 10999681/2500000000. A complete finite ordered-cell partition is checked with exact integer tangent and tree-flow certificates; reflection covers the remaining endpoint order. The inherited AM kernel, sharpened window enclosure and proved matching/counting chain yield the stated unconditional dyadic and cumulative critical-line bound. All inherited attribution and license notices are retained.',
    'method':'Ten-point weighted Gram-defect model; certified finite coverage; exact ordered symmetry reduction; integer tangent mixtures and tree-flow duals.',
    'display_percent':decimal,'display_percent_truncated_10_decimal_places':truncated,
    'display_percent_rounded_10_decimal_places':rounded,'gain_percentage_points':gain,
    'prior_record_numerator':str(PREVIOUS.numerator),'prior_record_denominator':str(PREVIOUS.denominator),
    'prior_record_source_commit':'9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb',
    'source_file':'proof/Solution.lean','source_bytes':proof.stat().st_size,'source_sha256':sha(proof),
    'submitted':False,'official_website_acceptance':False}
  write(DEST/'submission-fields.json',fields)
  manifest.update(upload_ready=True,locally_verified=True,verification_receipt_sha256=sha(verified),
    complete_integer_audit_sha256=sha(audit_path),submitted=False,official_website_acceptance=False)
  if decode_path:manifest['independent_source_decode_sha256']=sha(decode_path)
  write(DEST/'manifest.json',manifest)
  text=f'''# W10 submission materials

Locally verified; not uploaded to or accepted by the website.

Upload only [proof/Solution.lean](proof/Solution.lean) at
[riemannzeta.fun/submit](https://www.riemannzeta.fun/submit), and copy the exact
numerator and denominator from [submission-fields.json](submission-fields.json).

- Numerator: `{P}`
- Denominator: `{Q}`
- Percentage: **{decimal}%**
- Website truncation: **{truncated}%**; rounded: **{rounded}%**
- Gain over attempt-024: **{gain} percentage points**
- Source: **{proof.stat().st_size} bytes**, SHA256 `{sha(proof)}`

The file contains all finite data and all three required website declarations.
It imports only pinned Lean/Mathlib/Zeta23/challenge packages. Lossless source
literals expand into ordinary Lean commands and data literals into integers;
the default Lean kernel and independent
nanoda replay verify the resulting proof. No local repository import, local
floor assumption, Riemann hypothesis or added axiom is needed.

The exact comparison was verified against the archived
[attempt-024](https://www.riemannzeta.fun/submissions/attempt-024) record.
The website regenerates its current record at submission time. The fixed
statement comparison, transitive axiom check, default kernel and nanoda passed
locally, as recorded in [verification.json](../../verification/w10-20261016/single/verification.json).
The website's own sandbox limits and acceptance are separate.
'''
  (DEST/'README.md').write_text(text,encoding='utf8')
  print(json.dumps({'upload_ready':True,'source_sha256':sha(proof),'source_bytes':proof.stat().st_size,'percentage':decimal}))
if __name__=='__main__':main()
