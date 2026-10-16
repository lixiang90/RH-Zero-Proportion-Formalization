"""Emit 69 new-window rational diagonal polynomial lower bounds for Lean.

Only algebra is asserted by WindowGramBasins. Its actual-kernel scalar
minorants and complete global coverage remain separate obligations.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def lit(x):
    x=F(x);return f'({x.numerator} : ℝ) / {x.denominator}'
def vector(v):return '!['+', '.join(lit(x) for x in v)+']'
def main():
    source=HERE/'cover-newwindow-gram-replay.json';doc=json.loads(source.read_bytes());rows=doc['diagonal_bounds']
    assert doc['receipt']['passed'] and doc['receipt']['all_diagonal_bounds_also_pass_original_884_floor'] and len(rows)==69
    out=['''/- SPDX-License-Identifier: Apache-2.0
Generated pure algebraic lower bounds for the new-window 69 basin polynomials.
This module assumes no analytic kernel inequalities and proves no global cover.
-/
import StructuralW10Unconditional20261016.DiagonalPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowGramBasins
''']
    for k,row in enumerate(rows):
        out.extend([f'def C{k} : ℝ := {lit(row["constant"])}\n',f'def b{k} : Fin 9 → ℝ := {vector(row["gradient"])}\n',
          f'def d{k} : Fin 9 → ℝ := {vector(row["diagonal"])}\n',f'def q{k} : Fin 9 → ℝ := {vector(row["anchor"])}\n',
          f'''theorem lower{k} (x : Fin 9 → ℝ) :
    (221 : ℝ)/25000 ≤ C{k}+∑ i, (b{k} i*x i+d{k} i*(x i)^2) := by
  apply StructuralW10Unconditional20261016.DiagonalPolynomial.lower
  · intro i
    fin_cases i <;> norm_num [d{k}]
  · norm_num [C{k}, b{k}, d{k}, Fin.sum_univ_succ]
#print axioms lower{k}
'''])
    out.append('end StructuralGoal20261016.WindowGramBasins\nend\n')
    target=ROOT/'StructuralGoal20261016/WindowGramBasins.lean';target.write_bytes(''.join(out).encode('utf8'))
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'output_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'source_bytes':target.stat().st_size,'polynomials':69,'target':'221/25000',
      'ordinary_Lean_compiled':False,'actual_scalar_bridge':False,'global_cover':False}
    (HERE/'cover-window-gram-generated.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt))
if __name__=='__main__':main()
