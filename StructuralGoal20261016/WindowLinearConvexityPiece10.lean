/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 10.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter10
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
def coeff10 (j : ℕ) : FI := secondCoeff 10 j

theorem coeff10_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff10 j)) (iteratedDeriv j wSecond (10:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 10 j) (wc 24 WindowKernel.d24 j ((10:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_10 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff10,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece10_0 : ∀ x ∈ Icc ((979/100:ℚ):ℝ) ((3937/400:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (979/100:ℚ) (3937/400:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights0 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_1 : ∀ x ∈ Icc ((3937/400:ℚ):ℝ) ((1979/200:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (3937/400:ℚ) (1979/200:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights1 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_2 : ∀ x ∈ Icc ((1979/200:ℚ):ℝ) ((3979/400:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (1979/200:ℚ) (3979/400:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights2 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_3 : ∀ x ∈ Icc ((3979/400:ℚ):ℝ) ((10/1:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (3979/400:ℚ) (10/1:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights3 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_4 : ∀ x ∈ Icc ((10/1:ℚ):ℝ) ((4021/400:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (10/1:ℚ) (4021/400:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights4 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_5 : ∀ x ∈ Icc ((4021/400:ℚ):ℝ) ((2021/200:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (4021/400:ℚ) (2021/200:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights5 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_6 : ∀ x ∈ Icc ((2021/200:ℚ):ℝ) ((4063/400:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (2021/200:ℚ) (4063/400:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights6 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece10_7 : ∀ x ∈ Icc ((4063/400:ℚ):ℝ) ((1021/100:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff10 (4063/400:ℚ) (1021/100:ℚ) (10/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (166439793/250000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff10_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff10 (weights7 u)) ((166439793/250000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_10 : ∀ x ∈ Icc ((979/100:ℚ):ℝ) ((1021/100:ℚ):ℝ),
 ((166439793/250000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((3937/400:ℚ):ℝ)
 · apply piece10_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((1979/200:ℚ):ℝ)
   · apply piece10_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((3979/400:ℚ):ℝ)
     · apply piece10_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((10/1:ℚ):ℝ)
       · apply piece10_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((4021/400:ℚ):ℝ)
         · apply piece10_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((2021/200:ℚ):ℝ)
           · apply piece10_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((4063/400:ℚ):ℝ)
             · apply piece10_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece10_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_10
end StructuralGoal20261016.WindowLinearConvexityPieces
end
