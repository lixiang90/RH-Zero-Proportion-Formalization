/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 9.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter09
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
def coeff9 (j : ℕ) : FI := secondCoeff 9 j

theorem coeff9_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff9 j)) (iteratedDeriv j wSecond (9:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 9 j) (wc 24 WindowKernel.d24 j ((9:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_9 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff9,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece9_0 : ∀ x ∈ Icc ((879/100:ℚ):ℝ) ((3537/400:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (879/100:ℚ) (3537/400:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights0 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_1 : ∀ x ∈ Icc ((3537/400:ℚ):ℝ) ((1779/200:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (3537/400:ℚ) (1779/200:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights1 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_2 : ∀ x ∈ Icc ((1779/200:ℚ):ℝ) ((3579/400:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (1779/200:ℚ) (3579/400:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights2 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_3 : ∀ x ∈ Icc ((3579/400:ℚ):ℝ) ((9/1:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (3579/400:ℚ) (9/1:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights3 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_4 : ∀ x ∈ Icc ((9/1:ℚ):ℝ) ((3621/400:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (9/1:ℚ) (3621/400:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights4 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_5 : ∀ x ∈ Icc ((3621/400:ℚ):ℝ) ((1821/200:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (3621/400:ℚ) (1821/200:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights5 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_6 : ∀ x ∈ Icc ((1821/200:ℚ):ℝ) ((3663/400:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (1821/200:ℚ) (3663/400:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights6 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece9_7 : ∀ x ∈ Icc ((3663/400:ℚ):ℝ) ((921/100:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff9 (3663/400:ℚ) (921/100:ℚ) (9/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (810151971/1000000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff9_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff9 (weights7 u)) ((810151971/1000000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_9 : ∀ x ∈ Icc ((879/100:ℚ):ℝ) ((921/100:ℚ):ℝ),
 ((810151971/1000000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((3537/400:ℚ):ℝ)
 · apply piece9_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((1779/200:ℚ):ℝ)
   · apply piece9_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((3579/400:ℚ):ℝ)
     · apply piece9_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((9/1:ℚ):ℝ)
       · apply piece9_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((3621/400:ℚ):ℝ)
         · apply piece9_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((1821/200:ℚ):ℝ)
           · apply piece9_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((3663/400:ℚ):ℝ)
             · apply piece9_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece9_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_9
end StructuralGoal20261016.WindowLinearConvexityPieces
end
