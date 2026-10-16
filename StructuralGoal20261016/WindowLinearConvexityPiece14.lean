/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 14.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter14
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
def coeff14 (j : ℕ) : FI := secondCoeff 14 j

theorem coeff14_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff14 j)) (iteratedDeriv j wSecond (14:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 14 j) (wc 24 WindowKernel.d24 j ((14:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_14 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff14,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece14_0 : ∀ x ∈ Icc ((1379/100:ℚ):ℝ) ((5537/400:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (1379/100:ℚ) (5537/400:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights0 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_1 : ∀ x ∈ Icc ((5537/400:ℚ):ℝ) ((2779/200:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (5537/400:ℚ) (2779/200:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights1 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_2 : ∀ x ∈ Icc ((2779/200:ℚ):ℝ) ((5579/400:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (2779/200:ℚ) (5579/400:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights2 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_3 : ∀ x ∈ Icc ((5579/400:ℚ):ℝ) ((14/1:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (5579/400:ℚ) (14/1:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights3 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_4 : ∀ x ∈ Icc ((14/1:ℚ):ℝ) ((5621/400:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (14/1:ℚ) (5621/400:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights4 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_5 : ∀ x ∈ Icc ((5621/400:ℚ):ℝ) ((2821/200:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (5621/400:ℚ) (2821/200:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights5 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_6 : ∀ x ∈ Icc ((2821/200:ℚ):ℝ) ((5663/400:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (2821/200:ℚ) (5663/400:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights6 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece14_7 : ∀ x ∈ Icc ((5663/400:ℚ):ℝ) ((1421/100:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff14 (5663/400:ℚ) (1421/100:ℚ) (14/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1391207459/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff14_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff14 (weights7 u)) ((1391207459/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_14 : ∀ x ∈ Icc ((1379/100:ℚ):ℝ) ((1421/100:ℚ):ℝ),
 ((1391207459/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((5537/400:ℚ):ℝ)
 · apply piece14_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((2779/200:ℚ):ℝ)
   · apply piece14_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((5579/400:ℚ):ℝ)
     · apply piece14_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((14/1:ℚ):ℝ)
       · apply piece14_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((5621/400:ℚ):ℝ)
         · apply piece14_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((2821/200:ℚ):ℝ)
           · apply piece14_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((5663/400:ℚ):ℝ)
             · apply piece14_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece14_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_14
end StructuralGoal20261016.WindowLinearConvexityPieces
end
