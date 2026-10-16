/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 8.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter08
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
def coeff8 (j : ℕ) : FI := secondCoeff 8 j

theorem coeff8_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff8 j)) (iteratedDeriv j wSecond (8:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 8 j) (wc 24 WindowKernel.d24 j ((8:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_8 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff8,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece8_0 : ∀ x ∈ Icc ((779/100:ℚ):ℝ) ((3137/400:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (779/100:ℚ) (3137/400:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights0 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_1 : ∀ x ∈ Icc ((3137/400:ℚ):ℝ) ((1579/200:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (3137/400:ℚ) (1579/200:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights1 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_2 : ∀ x ∈ Icc ((1579/200:ℚ):ℝ) ((3179/400:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (1579/200:ℚ) (3179/400:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights2 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_3 : ∀ x ∈ Icc ((3179/400:ℚ):ℝ) ((8/1:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (3179/400:ℚ) (8/1:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights3 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_4 : ∀ x ∈ Icc ((8/1:ℚ):ℝ) ((3221/400:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (8/1:ℚ) (3221/400:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights4 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_5 : ∀ x ∈ Icc ((3221/400:ℚ):ℝ) ((1621/200:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (3221/400:ℚ) (1621/200:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights5 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_6 : ∀ x ∈ Icc ((1621/200:ℚ):ℝ) ((3263/400:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (1621/200:ℚ) (3263/400:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights6 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece8_7 : ∀ x ∈ Icc ((3263/400:ℚ):ℝ) ((821/100:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff8 (3263/400:ℚ) (821/100:ℚ) (8/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (405269201/200000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff8_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff8 (weights7 u)) ((405269201/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_8 : ∀ x ∈ Icc ((779/100:ℚ):ℝ) ((821/100:ℚ):ℝ),
 ((405269201/200000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((3137/400:ℚ):ℝ)
 · apply piece8_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((1579/200:ℚ):ℝ)
   · apply piece8_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((3179/400:ℚ):ℝ)
     · apply piece8_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((8/1:ℚ):ℝ)
       · apply piece8_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((3221/400:ℚ):ℝ)
         · apply piece8_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((1621/200:ℚ):ℝ)
           · apply piece8_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((3263/400:ℚ):ℝ)
             · apply piece8_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece8_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_8
end StructuralGoal20261016.WindowLinearConvexityPieces
end
