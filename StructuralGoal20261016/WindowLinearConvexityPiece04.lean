/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 4.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter04
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
def coeff4 (j : ℕ) : FI := secondCoeff 4 j

theorem coeff4_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff4 j)) (iteratedDeriv j wSecond (4:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 4 j) (wc 24 WindowKernel.d24 j ((4:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_4 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff4,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece4_0 : ∀ x ∈ Icc ((379/100:ℚ):ℝ) ((1537/400:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (379/100:ℚ) (1537/400:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights0 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_1 : ∀ x ∈ Icc ((1537/400:ℚ):ℝ) ((779/200:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (1537/400:ℚ) (779/200:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights1 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_2 : ∀ x ∈ Icc ((779/200:ℚ):ℝ) ((1579/400:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (779/200:ℚ) (1579/400:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights2 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_3 : ∀ x ∈ Icc ((1579/400:ℚ):ℝ) ((4/1:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (1579/400:ℚ) (4/1:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights3 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_4 : ∀ x ∈ Icc ((4/1:ℚ):ℝ) ((1621/400:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (4/1:ℚ) (1621/400:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights4 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_5 : ∀ x ∈ Icc ((1621/400:ℚ):ℝ) ((821/200:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (1621/400:ℚ) (821/200:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights5 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_6 : ∀ x ∈ Icc ((821/200:ℚ):ℝ) ((1663/400:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (821/200:ℚ) (1663/400:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights6 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece4_7 : ∀ x ∈ Icc ((1663/400:ℚ):ℝ) ((421/100:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff4 (1663/400:ℚ) (421/100:ℚ) (4/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (1855049847/200000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff4_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff4 (weights7 u)) ((1855049847/200000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_4 : ∀ x ∈ Icc ((379/100:ℚ):ℝ) ((421/100:ℚ):ℝ),
 ((1855049847/200000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((1537/400:ℚ):ℝ)
 · apply piece4_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((779/200:ℚ):ℝ)
   · apply piece4_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((1579/400:ℚ):ℝ)
     · apply piece4_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((4/1:ℚ):ℝ)
       · apply piece4_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((1621/400:ℚ):ℝ)
         · apply piece4_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((821/200:ℚ):ℝ)
           · apply piece4_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((1663/400:ℚ):ℝ)
             · apply piece4_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece4_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_4
end StructuralGoal20261016.WindowLinearConvexityPieces
end
