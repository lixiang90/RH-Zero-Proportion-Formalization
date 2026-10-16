/- SPDX-License-Identifier: Apache-2.0
Pilot of the cached linear Bernstein actual convexity certificate.
-/
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowLinearConvexityPilot
open WindowRationalInterval (Holds)
open WindowFixedPolynomial WindowBernsteinLinear WindowBernsteinFastWeights WindowConvexityCertificate
open WindowFixedConvexity (secondCoeff secondCoeff_sound)

theorem cell : ∀ x ∈ Icc ((79/100:ℚ):ℝ) ((337/400:ℚ):ℝ), ((3873922399/20000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece (secondCoeff 1) (79/100) (337/400) 1 (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (3873922399/20000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   have hw := fun r hr => WindowFixedTablesAll.w_sound (n := 1) (by decide) (by decide) r hr
   have hh := secondCoeff_sound hw j hj
   convert hh using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro k hk i hi
   have hh := weights0_eq k i
   convert hh using 1 <;> norm_num
 · have hc : ∀ k : Fin 14, lowerCheck (weighted (secondCoeff 1) (weights0 k)) ((3873922399/20000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by decide +kernel
   intro k hk
   exact hc ⟨k,hk⟩

set_option pp.fullNames true
#print axioms cell
end StructuralGoal20261016.WindowLinearConvexityPilot
end
