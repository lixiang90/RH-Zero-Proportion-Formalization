"""Assemble the separately checked compact anchor certificate chunks."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s='/- SPDX-License-Identifier: Apache-2.0\nAll 1567 actual value and slope certificates.\n-/\n'
s+=''.join(f'import StructuralGoal20261016.WindowAnchorChecks{g:02}\n'for g in range(25))
s+='''set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowAnchorAll
open WindowAnchorCertificate WindowAnchorCertificateData WindowAnchorChecks WindowScalarMinorant

theorem checks : ∀ g : Fin 25, ∀ j : Fin 64, (g:ℕ)*64+(j:ℕ) < 1567 →
 check (row ((g:ℕ)*64+(j:ℕ))) = true := by
 intro g
 fin_cases g
'''
for g in range(25):s+=f' · exact checks{g:02}\n'
s+='''
theorem valid (i : ℕ) (hi : i < 1567) : Valid (row i) := by
 have hg : i/64 < 25 := by omega
 have hj : i%64 < 64 := Nat.mod_lt i (by decide)
 have he : i/64*64+i%64 = i := by omega
 have hc := checks ⟨i/64,hg⟩ ⟨i%64,hj⟩ (by change i/64*64+i%64 < 1567; omega)
 change check (row (i/64*64+i%64)) = true at hc
 rw [he] at hc
 exact WindowAnchorCertificate.sound hc

theorem value (i : ℕ) (hi : i < 1567) : ((row i).lower:ℝ) ≤ f (row i).anchor := (valid i hi).1
theorem slope (i : ℕ) (hi : i < 1567) :
 |iteratedDeriv 1 f (row i).anchor-((row i).slope:ℝ)| ≤ ((row i).error:ℝ) := (valid i hi).2

set_option pp.fullNames true
#print axioms valid
#print axioms value
#print axioms slope
end StructuralGoal20261016.WindowAnchorAll
end
'''
(ROOT/'StructuralGoal20261016/WindowAnchorAll.lean').write_text(s,encoding='utf8',newline='\n')
print(len(s.encode()))
