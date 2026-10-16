/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 16.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter16
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
def coeff16 (j : ℕ) : FI := secondCoeff 16 j

theorem coeff16_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff16 j)) (iteratedDeriv j wSecond (16:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 16 j) (wc 24 WindowKernel.d24 j ((16:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_16 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff16,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece16_0 : ∀ x ∈ Icc ((1579/100:ℚ):ℝ) ((6337/400:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (1579/100:ℚ) (6337/400:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights0 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_1 : ∀ x ∈ Icc ((6337/400:ℚ):ℝ) ((3179/200:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (6337/400:ℚ) (3179/200:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights1 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_2 : ∀ x ∈ Icc ((3179/200:ℚ):ℝ) ((6379/400:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (3179/200:ℚ) (6379/400:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights2 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_3 : ∀ x ∈ Icc ((6379/400:ℚ):ℝ) ((16/1:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (6379/400:ℚ) (16/1:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights3 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_4 : ∀ x ∈ Icc ((16/1:ℚ):ℝ) ((6421/400:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (16/1:ℚ) (6421/400:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights4 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_5 : ∀ x ∈ Icc ((6421/400:ℚ):ℝ) ((3221/200:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (6421/400:ℚ) (3221/200:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights5 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_6 : ∀ x ∈ Icc ((3221/200:ℚ):ℝ) ((6463/400:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (3221/200:ℚ) (6463/400:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights6 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece16_7 : ∀ x ∈ Icc ((6463/400:ℚ):ℝ) ((1621/100:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff16 (6463/400:ℚ) (1621/100:ℚ) (16/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1367944761/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff16_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff16 (weights7 u)) ((1367944761/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_16 : ∀ x ∈ Icc ((1579/100:ℚ):ℝ) ((1621/100:ℚ):ℝ),
 ((1367944761/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((6337/400:ℚ):ℝ)
 · apply piece16_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((3179/200:ℚ):ℝ)
   · apply piece16_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((6379/400:ℚ):ℝ)
     · apply piece16_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((16/1:ℚ):ℝ)
       · apply piece16_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((6421/400:ℚ):ℝ)
         · apply piece16_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((3221/200:ℚ):ℝ)
           · apply piece16_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((6463/400:ℚ):ℝ)
             · apply piece16_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece16_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_16
end StructuralGoal20261016.WindowLinearConvexityPieces
end
