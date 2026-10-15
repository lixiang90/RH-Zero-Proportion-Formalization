"""Generate revised parameter admissibility only; no analytic-floor declaration."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
path=HERE/'spectral-w10-refined-rational.json';doc=json.loads(path.read_text());D=doc['denominator']
text=(ROOT/'StructuralResearch20261016/W10Candidate.lean').read_text()
start=text.index('def aN :');end=text.index('def a (',start)
tables=['def aN : Fin 10 → Fin 10 → ℕ']
tables += [f'  | {i}, {j} => {v}' for i,j,v in doc['a_upper'] if v]
tables += ['  | _, _ => 0','def bN : Fin 9 → ℕ']
tables += [f'  | {i} => {v}' for i,v in enumerate(doc['b_numerators'])]
text=text[:start]+'\n'.join(tables)+'\n'+text[end:]
text=text.replace('W10Candidate','W10RefinedCandidate')
text=re.sub(r'(theorem bN_sum : \(∑ i : Fin 9, bN i\) = )\d+',r'\g<1>'+str(sum(doc['b_numerators'])),text)
B=Q(doc['B_exact'])
text=re.sub(r'(theorem pressure_eq : W.B = \()\d+( : ℝ\) / )\d+',
    r'\g<1>'+str(B.numerator)+r'\g<2>'+str(B.denominator),text)
text=text.replace('/- Exact research parameters only; the analytic Fw floor is not claimed. -/',
    '/- Revised exact parameters only; the analytic Fw floor remains unproved.\n'
    '   Parameter JSON SHA256: '+hashlib.sha256(path.read_bytes()).hexdigest()+' -/')
(ROOT/'StructuralResearch20261016/W10RefinedCandidate.lean').write_text(text,encoding='utf8')
print(hashlib.sha256(text.encode()).hexdigest())
