/- SPDX-License-Identifier: Apache-2.0
Actual w24 second-derivative lower bound in integer well 15.
-/
import StructuralGoal20261016.WindowBernsteinLinear
import StructuralGoal20261016.WindowBernsteinFastWeights
import StructuralGoal20261016.WindowFixedKernelCenter15
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
def coeff15 (j : ℕ) : FI := secondCoeff 15 j

theorem coeff15_sound (j : ℕ) (hj : j < 14) :
 Holds (decode (coeff15 j)) (iteratedDeriv j wSecond (15:ℝ)/(j.factorial:ℝ)) := by
 have hw : ∀ j ≤ 23, Holds (W 15 j) (wc 24 WindowKernel.d24 j ((15:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one,Nat.cast_ofNat] using w_15 j hj
 have hh := secondCoeff_sound hw j hj
 simpa only [coeff15,Nat.cast_one,Nat.cast_ofNat] using hh
theorem piece15_0 : ∀ x ∈ Icc ((1479/100:ℚ):ℝ) ((5937/400:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (1479/100:ℚ) (5937/400:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights0
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights0_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights0 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_1 : ∀ x ∈ Icc ((5937/400:ℚ):ℝ) ((2979/200:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (5937/400:ℚ) (2979/200:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights1
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights1_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights1 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_2 : ∀ x ∈ Icc ((2979/200:ℚ):ℝ) ((5979/400:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (2979/200:ℚ) (5979/400:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights2
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights2_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights2 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_3 : ∀ x ∈ Icc ((5979/400:ℚ):ℝ) ((15/1:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (5979/400:ℚ) (15/1:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights3
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights3_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights3 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_4 : ∀ x ∈ Icc ((15/1:ℚ):ℝ) ((6021/400:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (15/1:ℚ) (6021/400:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights4
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights4_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights4 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_5 : ∀ x ∈ Icc ((6021/400:ℚ):ℝ) ((3021/200:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (6021/400:ℚ) (3021/200:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights5
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights5_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights5 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_6 : ∀ x ∈ Icc ((3021/200:ℚ):ℝ) ((6063/400:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (3021/200:ℚ) (6063/400:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights6
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights6_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights6 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem piece15_7 : ∀ x ∈ Icc ((6063/400:ℚ):ℝ) ((1521/100:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 apply actual_convex_piece coeff15 (6063/400:ℚ) (1521/100:ℚ) (15/1:ℚ) (21/100) (82220775718608258633/3720879554748535156250000000:ℚ) (788462003/500000000000:ℚ) weights7
 · norm_num
 · norm_num
 · intro j hj
   convert coeff15_sound j hj using 1 <;> norm_num
 · intro x hx
   push_cast at hx ⊢
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 · norm_num
 · intro u hu i hi
   have hh := weights7_eq u i
   convert hh using 1 <;> norm_num
 · have h : ∀ u : Fin 14,
       lowerCheck (weighted coeff15 (weights7 u)) ((788462003/500000000000:ℚ)+(82220775718608258633/3720879554748535156250000000:ℚ)) = true := by
     decide +kernel
   intro k hk
   exact h ⟨k,hk⟩
theorem second_lower_15 : ∀ x ∈ Icc ((1479/100:ℚ):ℝ) ((1521/100:ℚ):ℝ),
 ((788462003/500000000000:ℚ):ℝ) ≤ wSecond x := by
 intro x hx
 by_cases h0 : x ≤ ((5937/400:ℚ):ℝ)
 · apply piece15_0 x
   constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
 · 
   by_cases h1 : x ≤ ((2979/200:ℚ):ℝ)
   · apply piece15_1 x
     constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
   · 
     by_cases h2 : x ≤ ((5979/400:ℚ):ℝ)
     · apply piece15_2 x
       constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
     · 
       by_cases h3 : x ≤ ((15/1:ℚ):ℝ)
       · apply piece15_3 x
         constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
       · 
         by_cases h4 : x ≤ ((6021/400:ℚ):ℝ)
         · apply piece15_4 x
           constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
         · 
           by_cases h5 : x ≤ ((3021/200:ℚ):ℝ)
           · apply piece15_5 x
             constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
           · 
             by_cases h6 : x ≤ ((6063/400:ℚ):ℝ)
             · apply piece15_6 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
             · apply piece15_7 x
               constructor <;> push_cast at * <;> linarith [hx.1,hx.2]
set_option pp.fullNames true
#print axioms second_lower_15
end StructuralGoal20261016.WindowLinearConvexityPieces
end
