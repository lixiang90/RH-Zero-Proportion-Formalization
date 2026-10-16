/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 11.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter11
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
def coeff11 (j : ℕ) : FI := secondCoeff 11 j

theorem coeff11_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff11 j)) (iteratedDeriv j wSecond (11:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 11 j) (wc 24 WindowKernel.d24 j ((11:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_11 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff11,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece11_0 : ∀ x ∈ Icc ((1079/100:ℚ):ℝ) ((4337/400:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (1079/100:ℚ) (4337/400:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights0 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_1 : ∀ x ∈ Icc ((4337/400:ℚ):ℝ) ((2179/200:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (4337/400:ℚ) (2179/200:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights1 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_2 : ∀ x ∈ Icc ((2179/200:ℚ):ℝ) ((4379/400:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (2179/200:ℚ) (4379/400:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights2 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_3 : ∀ x ∈ Icc ((4379/400:ℚ):ℝ) ((11/1:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (4379/400:ℚ) (11/1:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights3 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_4 : ∀ x ∈ Icc ((11/1:ℚ):ℝ) ((4421/400:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (11/1:ℚ) (4421/400:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights4 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_5 : ∀ x ∈ Icc ((4421/400:ℚ):ℝ) ((2221/200:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (4421/400:ℚ) (2221/200:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights5 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_6 : ∀ x ∈ Icc ((2221/200:ℚ):ℝ) ((4463/400:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (2221/200:ℚ) (4463/400:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights6 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece11_7 : ∀ x ∈ Icc ((4463/400:ℚ):ℝ) ((1121/100:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff11 (4463/400:ℚ) (1121/100:ℚ) (11/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (920206897/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff11_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff11 (weights7 u)) ((920206897/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_11 : ∀ x ∈ Icc ((1079/100:ℚ):ℝ) ((1121/100:ℚ):ℝ),
 ((920206897/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((4337/400:ℚ):ℝ)
 · apply piece11_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((2179/200:ℚ):ℝ)
   · apply piece11_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((4379/400:ℚ):ℝ)
     · apply piece11_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((11/1:ℚ):ℝ)
       · apply piece11_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((4421/400:ℚ):ℝ)
         · apply piece11_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((2221/200:ℚ):ℝ)
           · apply piece11_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((4463/400:ℚ):ℝ)
             · apply piece11_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece11_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_11
end StructuralGoal20261016.WindowLinearConvexityPieces
end
