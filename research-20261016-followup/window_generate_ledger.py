"""Generate only exact ledger admissibility, never a new-kernel floor."""
from pathlib import Path
import hashlib,json,re
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[1]
source=ROOT/'research-20261016-followup/window_reweight_rational.json'
data=json.loads(source.read_text(encoding='utf8'));D=data['denominator'];assert D==10**10
template=(ROOT/'StructuralResearch20261016/W10RefinedCandidate.lean').read_text(encoding='utf8')
prefix='''/- Redesigned-window ledger: exact admissibility and reflection only.
   Parameter JSON SHA256: %s
   IMPORTANT: Core.Fw still denotes the OLD AM kernel. W is only a numerical
   pair/pressure ledger; no Fw lower bound or redesigned analytic bridge is
   asserted here. All new-window local floors remain unproved. -/'''%hashlib.sha256(source.read_bytes()).hexdigest()
text=re.sub(r'^/-.*?-/',prefix,template,count=1,flags=re.S)
text=text.replace('StructuralResearch20261016.W10RefinedCandidate','StructuralW10Followup20261016.NewLedger')
a='def aN : Fin 10 → Fin 10 → ℕ\n'+''.join(f'  | {i}, {j} => {v}\n' for i,j,v in data['a_upper'])+'  | _, _ => 0\n'
b='def bN : Fin 9 → ℕ\n'+''.join(f'  | {i} => {v}\n' for i,v in enumerate(data['b_numerators']))
text,n=re.subn(r'^def aN :.*?(?=^def bN)',a,text,flags=re.S|re.M);assert n==1
text,n=re.subn(r'^def bN :.*?(?=^def a )',b,text,flags=re.S|re.M);assert n==1
text=re.sub(r'theorem bN_sum :.*?:= by decide',f"theorem bN_sum : (∑ i : Fin 9, bN i) = {sum(data['b_numerators'])} := by decide",text)
B=F(data['B_exact']);assert B==F(sum(data['b_numerators']),D)
assert '(10999681 : ℝ) / 2500000000' in text
text=text.replace('(10999681 : ℝ) / 2500000000',f'({B.numerator} : ℝ) / {B.denominator}')
reflection='''
theorem aN_reflection (i j : Fin 10) : aN i j = aN j.rev i.rev := by
  fin_cases i <;> fin_cases j <;> decide

theorem bN_reflection (i : Fin 9) : bN i = bN i.rev := by
  fin_cases i <;> decide

theorem pair_reflection (i j : Fin 10) : W.a i j = W.a j.rev i.rev := by
  change (aN i j : ℝ) / 10000000000 = (aN j.rev i.rev : ℝ) / 10000000000
  rw [aN_reflection]

theorem pressure_reflection (i : Fin 9) : W.b i = W.b i.rev := by
  change (bN i : ℝ) / 10000000000 = (bN i.rev : ℝ) / 10000000000
  rw [bN_reflection]

'''
text=text.replace('-- No analytic floor or zeta proportion theorem is asserted in this module.',reflection+'-- No analytic floor or zeta proportion theorem is asserted in this module.')
text=text.replace('#print axioms pressure_eq','#print axioms pressure_eq\n#print axioms pair_reflection\n#print axioms pressure_reflection')
out=ROOT/'StructuralW10Followup20261016/NewLedger.lean';out.write_text(text,encoding='utf8',newline='\n')
# Independently parse the actual emitted bytes, not the interpolation strings.
actual=out.read_text(encoding='utf8')
ablock=re.search(r'^def aN :.*?(?=^def bN)',actual,re.M|re.S).group()
bblock=re.search(r'^def bN :.*?(?=^def a )',actual,re.M|re.S).group()
actual_a={(int(i),int(j)):int(v) for i,j,v in re.findall(r'^\s*\| (\d+), (\d+) => (\d+)$',ablock,re.M)}
actual_b={int(i):int(v) for i,v in re.findall(r'^\s*\| (\d+) => (\d+)$',bblock,re.M)}
expected_a={(i,j):v for i,j,v in data['a_upper']}
assert len(actual_a)==len(expected_a)==45 and actual_a==expected_a
assert all(actual_a.get((i,j),0)==expected_a.get((i,j),0) for i in range(10) for j in range(10))
assert actual_b==dict(enumerate(data['b_numerators'])) and len(actual_b)==9
caps=[sum(actual_a.get((i,j),0) for i in range(10) for j in range(10) if j-i==s) for s in range(1,10)]
assert caps==data['span_capacity_numerators'] and max(caps)<=2*D
assert all(actual_a.get((i,j),0)==actual_a.get((9-j,9-i),0) for i in range(10) for j in range(10))
assert [actual_b[i] for i in range(9)]==[actual_b[8-i] for i in range(9)]
nat_sum=int(re.search(r'theorem bN_sum :.*?= (\d+) :=',actual).group(1))
assert nat_sum==sum(actual_b.values()) and F(nat_sum,D)==B
receipt={'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,
    'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'proof_scope':'admissibility and reflection only; new kernel floor unproved',
    'emitted_explicit_pair_cases':len(actual_a),'all_100_pair_values_match_JSON':True,
    'all_9_pressures_match_JSON':True,'actual_nat_pressure_sum':nat_sum,'actual_pressure_exact':str(B),
    'capacity_reflection_pressure_checks_passed':True,'all_roundtrip_checks_passed':True,'Lean_checked':False}
(ROOT/'research-20261016-followup/window_new_ledger_roundtrip.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
print(json.dumps(receipt))
