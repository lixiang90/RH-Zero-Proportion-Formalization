/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 13.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter13
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
def coeff13 (j : ℕ) : FI := secondCoeff 13 j

theorem coeff13_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff13 j)) (iteratedDeriv j wSecond (13:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 13 j) (wc 24 WindowKernel.d24 j ((13:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_13 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff13,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece13_0 : ∀ x ∈ Icc ((1279/100:ℚ):ℝ) ((5137/400:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (1279/100:ℚ) (5137/400:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights0 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_1 : ∀ x ∈ Icc ((5137/400:ℚ):ℝ) ((2579/200:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (5137/400:ℚ) (2579/200:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights1 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_2 : ∀ x ∈ Icc ((2579/200:ℚ):ℝ) ((5179/400:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (2579/200:ℚ) (5179/400:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights2 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_3 : ∀ x ∈ Icc ((5179/400:ℚ):ℝ) ((13/1:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (5179/400:ℚ) (13/1:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights3 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_4 : ∀ x ∈ Icc ((13/1:ℚ):ℝ) ((5221/400:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (13/1:ℚ) (5221/400:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights4 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_5 : ∀ x ∈ Icc ((5221/400:ℚ):ℝ) ((2621/200:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (5221/400:ℚ) (2621/200:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights5 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_6 : ∀ x ∈ Icc ((2621/200:ℚ):ℝ) ((5263/400:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (2621/200:ℚ) (5263/400:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights6 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece13_7 : ∀ x ∈ Icc ((5263/400:ℚ):ℝ) ((1321/100:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff13 (5263/400:ℚ) (1321/100:ℚ) (13/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (126662011/100000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff13_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff13 (weights7 u)) ((126662011/100000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_13 : ∀ x ∈ Icc ((1279/100:ℚ):ℝ) ((1321/100:ℚ):ℝ),
 ((126662011/100000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((5137/400:ℚ):ℝ)
 · apply piece13_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((2579/200:ℚ):ℝ)
   · apply piece13_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((5179/400:ℚ):ℝ)
     · apply piece13_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((13/1:ℚ):ℝ)
       · apply piece13_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((5221/400:ℚ):ℝ)
         · apply piece13_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((2621/200:ℚ):ℝ)
           · apply piece13_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((5263/400:ℚ):ℝ)
             · apply piece13_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece13_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_13
end StructuralGoal20261016.WindowLinearConvexityPieces
end
