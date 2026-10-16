/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 6.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter06
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
def coeff6 (j : ℕ) : FI := secondCoeff 6 j

theorem coeff6_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff6 j)) (iteratedDeriv j wSecond (6:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 6 j) (wc 24 WindowKernel.d24 j ((6:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_6 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff6,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece6_0 : ∀ x ∈ Icc ((579/100:ℚ):ℝ) ((2337/400:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (579/100:ℚ) (2337/400:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights0 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_1 : ∀ x ∈ Icc ((2337/400:ℚ):ℝ) ((1179/200:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (2337/400:ℚ) (1179/200:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights1 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_2 : ∀ x ∈ Icc ((1179/200:ℚ):ℝ) ((2379/400:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (1179/200:ℚ) (2379/400:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights2 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_3 : ∀ x ∈ Icc ((2379/400:ℚ):ℝ) ((6/1:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (2379/400:ℚ) (6/1:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights3 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_4 : ∀ x ∈ Icc ((6/1:ℚ):ℝ) ((2421/400:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (6/1:ℚ) (2421/400:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights4 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_5 : ∀ x ∈ Icc ((2421/400:ℚ):ℝ) ((1221/200:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (2421/400:ℚ) (1221/200:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights5 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_6 : ∀ x ∈ Icc ((1221/200:ℚ):ℝ) ((2463/400:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (1221/200:ℚ) (2463/400:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights6 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece6_7 : ∀ x ∈ Icc ((2463/400:ℚ):ℝ) ((621/100:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff6 (2463/400:ℚ) (621/100:ℚ) (6/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (154987711/50000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff6_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff6 (weights7 u)) ((154987711/50000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_6 : ∀ x ∈ Icc ((579/100:ℚ):ℝ) ((621/100:ℚ):ℝ),
 ((154987711/50000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((2337/400:ℚ):ℝ)
 · apply piece6_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((1179/200:ℚ):ℝ)
   · apply piece6_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((2379/400:ℚ):ℝ)
     · apply piece6_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((6/1:ℚ):ℝ)
       · apply piece6_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((2421/400:ℚ):ℝ)
         · apply piece6_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((1221/200:ℚ):ℝ)
           · apply piece6_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((2463/400:ℚ):ℝ)
             · apply piece6_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece6_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_6
end StructuralGoal20261016.WindowLinearConvexityPieces
end
