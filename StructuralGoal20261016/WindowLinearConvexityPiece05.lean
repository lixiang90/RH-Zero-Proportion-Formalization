/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 5.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter05
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
def coeff5 (j : ℕ) : FI := secondCoeff 5 j

theorem coeff5_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff5 j)) (iteratedDeriv j wSecond (5:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 5 j) (wc 24 WindowKernel.d24 j ((5:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_5 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff5,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece5_0 : ∀ x ∈ Icc ((479/100:ℚ):ℝ) ((1937/400:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (479/100:ℚ) (1937/400:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights0 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_1 : ∀ x ∈ Icc ((1937/400:ℚ):ℝ) ((979/200:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (1937/400:ℚ) (979/200:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights1 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_2 : ∀ x ∈ Icc ((979/200:ℚ):ℝ) ((1979/400:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (979/200:ℚ) (1979/400:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights2 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_3 : ∀ x ∈ Icc ((1979/400:ℚ):ℝ) ((5/1:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (1979/400:ℚ) (5/1:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights3 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_4 : ∀ x ∈ Icc ((5/1:ℚ):ℝ) ((2021/400:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (5/1:ℚ) (2021/400:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights4 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_5 : ∀ x ∈ Icc ((2021/400:ℚ):ℝ) ((1021/200:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (2021/400:ℚ) (1021/200:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights5 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_6 : ∀ x ∈ Icc ((1021/200:ℚ):ℝ) ((2063/400:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (1021/200:ℚ) (2063/400:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights6 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece5_7 : ∀ x ∈ Icc ((2063/400:ℚ):ℝ) ((521/100:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff5 (2063/400:ℚ) (521/100:ℚ) (5/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (757401027/100000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff5_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff5 (weights7 u)) ((757401027/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_5 : ∀ x ∈ Icc ((479/100:ℚ):ℝ) ((521/100:ℚ):ℝ),
 ((757401027/100000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((1937/400:ℚ):ℝ)
 · apply piece5_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((979/200:ℚ):ℝ)
   · apply piece5_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((1979/400:ℚ):ℝ)
     · apply piece5_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((5/1:ℚ):ℝ)
       · apply piece5_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((2021/400:ℚ):ℝ)
         · apply piece5_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((1021/200:ℚ):ℝ)
           · apply piece5_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((2063/400:ℚ):ℝ)
             · apply piece5_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece5_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_5
end StructuralGoal20261016.WindowLinearConvexityPieces
end
