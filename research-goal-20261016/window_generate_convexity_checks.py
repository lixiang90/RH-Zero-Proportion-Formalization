"""Emit the 16 actual convexity interval proofs from checked W coefficients.

All numeric lower comparisons are exact Lean checks of the interval recipe.
The Python evidence is used to choose the rational target, never as a premise.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json
ROOT=Path(__file__).resolve().parents[1]
DATA=json.loads((Path(__file__).parent/'window_normalized_interval.json').read_bytes())
def real(q):q=F(q);return f'({q.numerator}/{q.denominator}:ℚ)'
mods=[]
rem=F(44,7)**16*F(21,100)**14/factorial(14)
for n in range(1,17):
    lower=F(DATA['curvature_checks'][n-1]['original_twice_alpha'])
    name=f'WindowConvexityPiece{n:02}'
    text=f'''/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well {n}.
-/
import StructuralGoal20261016.WindowConvexityArithmetic
import StructuralGoal20261016.WindowKernelJetTables{(n-1)//4:02}
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowConvexityPieces
open WindowRationalInterval WindowNormalizedJets WindowConvexityCertificate
open WindowConvexityArithmetic WindowJetTableData WindowKernelJetTables
def coeff{n} (j : ℕ) : QI := rmul (point ((j+1)*(j+2))) (W {n} (j+2))
theorem coeff{n}_sound (j : ℕ) (hj : j < 14) :
 Holds (coeff{n} j) (iteratedDeriv j wSecond ({n}:ℝ)/(j.factorial:ℝ)) := by
 rw [second_coeff]
 have h := rmul_sound (point_sound ((j+1)*(j+2):ℚ)) (w_{n} (j+2) (by omega))
 convert h using 1 <;> push_cast <;> ring
'''
    for k in range(8):
        a=F(n)-F(21,100)+F(42,100)*F(k,8)
        b=F(n)-F(21,100)+F(42,100)*F(k+1,8)
        text+=f'''theorem piece{n}_{k} : ∀ x ∈ Icc ({real(a)}:ℝ) ({real(b)}:ℝ),
 ({real(lower)}:ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff{n} {real(a)} {real(b)} {real(n)} (21/100) {real(rem)} {real(lower)}
 · norm_num
 · norm_num
 · exact coeff{n}_sound
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · have h : ∀ k : Fin 14, {real(lower)}+{real(rem)} ≤
       (WindowConvexityArithmetic.betaI coeff{n} {real(a-n)} {real(b-a)} k).1 := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
'''
    a0=F(n)-F(21,100);b8=F(n)+F(21,100)
    text+=f'''theorem second_lower_{n} : ∀ x ∈ Icc ({real(a0)}:ℝ) ({real(b8)}:ℝ),
 ({real(lower)}:ℝ) ≤ wSecond x := by
 intro x hx
'''
    indent=' '
    for k in range(7):
        b=a0+F(42,100)*F(k+1,8)
        text+=indent+f'by_cases h{k} : x ≤ ({real(b)}:ℝ)\n'
        text+=indent+f'· apply piece{n}_{k} x\n'
        text+=indent+'  constructor <;> push_cast at * <;> linarith [hx.1,hx.2]\n'
        text+=indent+'· '
        if k<6:text+='\n'
        indent+='  '
    text+=f'apply piece{n}_7 x\n'+indent+'constructor <;> push_cast at * <;> linarith [hx.1,hx.2]\n'
    text+=f'set_option pp.fullNames true\n#print axioms second_lower_{n}\nend StructuralGoal20261016.WindowConvexityPieces\nend\n'
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(text,encoding='utf8',newline='\n')
    mods.append('StructuralGoal20261016.'+name)
(Path(__file__).parent/'window_convexity_modules.json').write_text(json.dumps(mods,indent=2)+'\n',encoding='utf8')
print(json.dumps({'modules':len(mods),'checks':128}))
