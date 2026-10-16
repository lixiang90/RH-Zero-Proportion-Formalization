/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 3.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter03
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
def coeff3 (j : ℕ) : FI := secondCoeff 3 j

theorem coeff3_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff3 j)) (iteratedDeriv j wSecond (3:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 3 j) (wc 24 WindowKernel.d24 j ((3:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_3 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff3,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece3_0 : ∀ x ∈ Icc ((279/100:ℚ):ℝ) ((1137/400:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (279/100:ℚ) (1137/400:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights0 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_1 : ∀ x ∈ Icc ((1137/400:ℚ):ℝ) ((579/200:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (1137/400:ℚ) (579/200:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights1 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_2 : ∀ x ∈ Icc ((579/200:ℚ):ℝ) ((1179/400:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (579/200:ℚ) (1179/400:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights2 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_3 : ∀ x ∈ Icc ((1179/400:ℚ):ℝ) ((3/1:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (1179/400:ℚ) (3/1:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights3 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_4 : ∀ x ∈ Icc ((3/1:ℚ):ℝ) ((1221/400:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (3/1:ℚ) (1221/400:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights4 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_5 : ∀ x ∈ Icc ((1221/400:ℚ):ℝ) ((621/200:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (1221/400:ℚ) (621/200:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights5 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_6 : ∀ x ∈ Icc ((621/200:ℚ):ℝ) ((1263/400:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (621/200:ℚ) (1263/400:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights6 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece3_7 : ∀ x ∈ Icc ((1263/400:ℚ):ℝ) ((321/100:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff3 (1263/400:ℚ) (321/100:ℚ) (3/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (13320248721/500000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff3_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff3 (weights7 u)) ((13320248721/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_3 : ∀ x ∈ Icc ((279/100:ℚ):ℝ) ((321/100:ℚ):ℝ),
 ((13320248721/500000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((1137/400:ℚ):ℝ)
 · apply piece3_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((579/200:ℚ):ℝ)
   · apply piece3_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((1179/400:ℚ):ℝ)
     · apply piece3_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((3/1:ℚ):ℝ)
       · apply piece3_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((1221/400:ℚ):ℝ)
         · apply piece3_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((621/200:ℚ):ℝ)
           · apply piece3_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((1263/400:ℚ):ℝ)
             · apply piece3_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece3_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_3
end StructuralGoal20261016.WindowLinearConvexityPieces
end
