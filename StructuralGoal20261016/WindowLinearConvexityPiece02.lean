/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 2.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter02
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
def coeff2 (j : ℕ) : FI := secondCoeff 2 j

theorem coeff2_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff2 j)) (iteratedDeriv j wSecond (2:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 2 j) (wc 24 WindowKernel.d24 j ((2:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_2 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff2,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece2_0 : ∀ x ∈ Icc ((179/100:ℚ):ℝ) ((737/400:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (179/100:ℚ) (737/400:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights0 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_1 : ∀ x ∈ Icc ((737/400:ℚ):ℝ) ((379/200:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (737/400:ℚ) (379/200:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights1 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_2 : ∀ x ∈ Icc ((379/200:ℚ):ℝ) ((779/400:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (379/200:ℚ) (779/400:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights2 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_3 : ∀ x ∈ Icc ((779/400:ℚ):ℝ) ((2/1:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (779/400:ℚ) (2/1:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights3 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_4 : ∀ x ∈ Icc ((2/1:ℚ):ℝ) ((821/400:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (2/1:ℚ) (821/400:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights4 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_5 : ∀ x ∈ Icc ((821/400:ℚ):ℝ) ((421/200:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (821/400:ℚ) (421/200:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights5 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_6 : ∀ x ∈ Icc ((421/200:ℚ):ℝ) ((863/400:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (421/200:ℚ) (863/400:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights6 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece2_7 : ∀ x ∈ Icc ((863/400:ℚ):ℝ) ((221/100:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff2 (863/400:ℚ) (221/100:ℚ) (2/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (74465922661/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff2_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff2 (weights7 u)) ((74465922661/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_2 : ∀ x ∈ Icc ((179/100:ℚ):ℝ) ((221/100:ℚ):ℝ),
 ((74465922661/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((737/400:ℚ):ℝ)
 · apply piece2_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((379/200:ℚ):ℝ)
   · apply piece2_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((779/400:ℚ):ℝ)
     · apply piece2_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((2/1:ℚ):ℝ)
       · apply piece2_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((821/400:ℚ):ℝ)
         · apply piece2_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((421/200:ℚ):ℝ)
           · apply piece2_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((863/400:ℚ):ℝ)
             · apply piece2_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece2_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_2
end StructuralGoal20261016.WindowLinearConvexityPieces
end
