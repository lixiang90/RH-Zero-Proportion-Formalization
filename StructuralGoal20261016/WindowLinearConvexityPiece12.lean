/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 12.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter12
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowLinearConvexityPieces
open WindowRationalInterval (Holds)
open WindowNormalizedJets WindowConvexityCertificate WindowJetTableData WindowFixedKernelCenters
open WindowFixedInterval (FI decode)
open WindowFixedConvexity (secondCoeff secondCoeff_sound)
open WindowBernsteinLinear WindowBernsteinFastWeights
open WindowFixedPolynomial (lowerCheck)
def coeff12 (j : ℕ) : FI := secondCoeff 12 j

theorem coeff12_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff12 j)) (iteratedDeriv j wSecond (12:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 12 j) (wc 24 WindowKernel.d24 j ((12:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_12 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff12,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece12_0 : ∀ x ∈ Icc ((1179/100:ℚ):ℝ) ((4737/400:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (1179/100:ℚ) (4737/400:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights0 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_1 : ∀ x ∈ Icc ((4737/400:ℚ):ℝ) ((2379/200:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (4737/400:ℚ) (2379/200:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights1 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_2 : ∀ x ∈ Icc ((2379/200:ℚ):ℝ) ((4779/400:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (2379/200:ℚ) (4779/400:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights2 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_3 : ∀ x ∈ Icc ((4779/400:ℚ):ℝ) ((12/1:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (4779/400:ℚ) (12/1:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights3 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_4 : ∀ x ∈ Icc ((12/1:ℚ):ℝ) ((4821/400:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (12/1:ℚ) (4821/400:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights4 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_5 : ∀ x ∈ Icc ((4821/400:ℚ):ℝ) ((2421/200:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (4821/400:ℚ) (2421/200:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights5 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_6 : ∀ x ∈ Icc ((2421/200:ℚ):ℝ) ((4863/400:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (2421/200:ℚ) (4863/400:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights6 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece12_7 : ∀ x ∈ Icc ((4863/400:ℚ):ℝ) ((1221/100:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff12 (4863/400:ℚ) (1221/100:ℚ) (12/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (658634521/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff12_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff12 (weights7 u)) ((658634521/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_12 : ∀ x ∈ Icc ((1179/100:ℚ):ℝ) ((1221/100:ℚ):ℝ),
 ((658634521/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((4737/400:ℚ):ℝ)
 · apply piece12_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((2379/200:ℚ):ℝ)
   · apply piece12_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((4779/400:ℚ):ℝ)
     · apply piece12_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((12/1:ℚ):ℝ)
       · apply piece12_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((4821/400:ℚ):ℝ)
         · apply piece12_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((2421/200:ℚ):ℝ)
           · apply piece12_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((4863/400:ℚ):ℝ)
             · apply piece12_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece12_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_12
end StructuralGoal20261016.WindowLinearConvexityPieces
end
