/- SPDX-License-Identifier: Apache-2.0
Integer-capacity affine mixtures and edge-only flows for the actual Fw24.
The scalar oracle remains explicit: it must prove the actual line on its
cell, not merely return an LP optimum or an asserted smoothness constant.
-/
import StructuralGoal20261016.WindowGramExpansion
import StructuralGoal20261016.WindowRootCell
import StructuralGoal20261016.WindowDifferenceCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowValueFlow
open WindowGramTransfer
open StructuralW10Followup20261016.NewLedger (W bN aN)

def denominator : ℤ := 1000000000000*10000000000*32768
def capacity (t : Fin 41) : ℤ := 100*(aN (pairI t) (pairJ t):ℤ)
def occurs (t : Fin 41) (r : Fin 9) : Prop :=
  (pairI t:ℕ) ≤ (r:ℕ) ∧ (r:ℕ) < (pairJ t:ℕ)
instance (t : Fin 41) (r : Fin 9) : Decidable (occurs t r) := inferInstanceAs (Decidable (_ ∧ _))

structure Plane where
  constant : ℤ
  slope : ℤ

variable {m : ℕ}

def line (p : Plane) (x : ℝ) : ℝ :=
  ((p.constant:ℝ)+32768*(p.slope:ℝ)*x)/(10000000000*32768)

def massCheck (lam : Fin 41 → Fin m → ℤ) : Bool := decide (
  (∀ t k, 0 ≤ lam t k) ∧ (∀ t, (∑ k, lam t k) ≤ capacity t))

def intercept (lam : Fin 41 → Fin m → ℤ) (p : Fin 41 → Fin m → Plane) : ℤ :=
  ∑ t, ∑ k, lam t k*(p t k).constant

def coefficient (lam : Fin 41 → Fin m → ℤ) (p : Fin 41 → Fin m → Plane) (r : Fin 9) : ℤ :=
  (bN r:ℤ)*1000000000000+
    ∑ t, ∑ k, if occurs t r then lam t k*(p t k).slope else 0

def minorant (lam : Fin 41 → Fin m → ℤ) (p : Fin 41 → Fin m → Plane) (g : Fin 9 → ℝ) : ℝ :=
  pressure g+∑ t, ∑ k, ((lam t k:ℝ)/1000000000000)*line (p t k) (span g t)

theorem pair_order : ∀ t : Fin 41, (pairI t:ℕ) < (pairJ t:ℕ) := by decide +kernel

-- Reduce the ledger comparison in Rat first. Expanding the 100-entry
-- pattern-matching ledger inside 41 Real goals is needlessly expensive.
def weightQ : Fin 41 → ℚ := ![(195195711 : ℚ) / 2000000000, (1008375533 : ℚ) / 10000000000, (1879917691 : ℚ) / 5000000000, (2851965903 : ℚ) / 10000000000, (1310911881 : ℚ) / 2000000000, (1 : ℚ) / 1, (2 : ℚ) / 1, (485225937 : ℚ) / 2500000000, (784443699 : ℚ) / 5000000000, (648608813 : ℚ) / 2000000000, (506909809 : ℚ) / 1250000000, (2227433729 : ℚ) / 5000000000, (446752131 : ℚ) / 625000000, (6890881189 : ℚ) / 10000000000, (1 : ℚ) / 1, (513175917 : ℚ) / 2000000000, (4121909221 : ℚ) / 10000000000, (3824161541 : ℚ) / 10000000000, (5944721527 : ℚ) / 10000000000, (1785297159 : ℚ) / 5000000000, (446752131 : ℚ) / 625000000, (1310911881 : ℚ) / 2000000000, (2928557891 : ℚ) / 10000000000, (215460169 : ℚ) / 500000000, (1924418859 : ℚ) / 5000000000, (5944721527 : ℚ) / 10000000000, (2227433729 : ℚ) / 5000000000, (2851965903 : ℚ) / 10000000000, (79434011 : ℚ) / 250000000, (215460169 : ℚ) / 500000000, (3824161541 : ℚ) / 10000000000, (506909809 : ℚ) / 1250000000, (1879917691 : ℚ) / 5000000000, (2928557891 : ℚ) / 10000000000, (4121909221 : ℚ) / 10000000000, (648608813 : ℚ) / 2000000000, (513175917 : ℚ) / 2000000000, (784443699 : ℚ) / 5000000000, (1008375533 : ℚ) / 10000000000, (485225937 : ℚ) / 2500000000, (195195711 : ℚ) / 2000000000]

theorem weight_ledger : ∀ t : Fin 41,
    weightQ t = (aN (pairI t) (pairJ t):ℚ)/10000000000 := by decide +kernel

theorem weight_cast (t : Fin 41) : weight t = (weightQ t:ℝ) := by
  fin_cases t <;> norm_num [weight,weightQ]

theorem capacity_eq (t : Fin 41) : (capacity t:ℝ)/1000000000000 = weight t := by
  rw [weight_cast,weight_ledger]
  unfold capacity
  push_cast
  ring

#check capacity_eq

theorem span_sum (g : Fin 9 → ℝ) (t : Fin 41) :
    span g t = ∑ r : Fin 9, if occurs t r then g r else 0 := by
  have h := WindowRootCell.span_indices g (pairI t) (pairJ t) (pair_order t).le
  change span g t = _ at h
  rw [h,WindowRootCell.indices,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : (pairI t:ℕ) ≤ (r:ℕ) ∧ (r:ℕ) < (pairJ t:ℕ)
  · simp only [occurs,hr,if_pos]
  · simp only [occurs,hr,if_neg]

#check span_sum

theorem minorant_le (lam : Fin 41 → Fin m → ℤ) (p : Fin 41 → Fin m → Plane)
    (g : Fin 9 → ℝ) (hc : massCheck lam = true)
    (hline : ∀ t k, lam t k ≠ 0 → line (p t k) (span g t) ≤
      WindowKernel.w 24 WindowKernel.d24 (span g t)) :
    minorant lam p g ≤ WindowGapEnergy.Fw24 g := by
  have hh : (∀ t k, 0 ≤ lam t k) ∧ (∀ t, (∑ k, lam t k) ≤ capacity t) := of_decide_eq_true hc
  unfold minorant
  rw [actual_energy_expansion]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro t _
  have hm : (∑ k, (lam t k:ℝ)/1000000000000) ≤ weight t := by
    rw [← Finset.sum_div,← capacity_eq t]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast hh.2 t
  have hn (k : Fin m) : (0:ℝ) ≤ (lam t k:ℝ)/1000000000000 := by
    have he : (0:ℝ) ≤ (lam t k:ℝ) := by exact_mod_cast hh.1 t k
    positivity
  calc
    (∑ k, ((lam t k:ℝ)/1000000000000)*line (p t k) (span g t)) ≤
        ∑ k, ((lam t k:ℝ)/1000000000000)*WindowKernel.w 24 WindowKernel.d24 (span g t) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hz : lam t k = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (hline t k hz) (hn k)
    _ = (∑ k, (lam t k:ℝ)/1000000000000)*WindowKernel.w 24 WindowKernel.d24 (span g t) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ weight t*WindowKernel.w 24 WindowKernel.d24 (span g t) :=
      mul_le_mul_of_nonneg_right hm (sq_nonneg _)

#check minorant_le

theorem weighted_spans (B : Fin 41 → Fin m → ℝ) (g : Fin 9 → ℝ) :
    (∑ t, ∑ k, B t k*span g t) =
      ∑ r : Fin 9, (∑ t, ∑ k, if occurs t r then B t k else 0)*g r := by
  simp_rw [span_sum,Finset.mul_sum]
  calc
    (∑ t, ∑ k, ∑ r : Fin 9, B t k*(if occurs t r then g r else 0)) =
        ∑ t, ∑ r : Fin 9, ∑ k, B t k*(if occurs t r then g r else 0) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_comm
    _ = ∑ r : Fin 9, ∑ t, ∑ k, B t k*(if occurs t r then g r else 0) := Finset.sum_comm
    _ = ∑ r : Fin 9, (∑ t, ∑ k, if occurs t r then B t k else 0)*g r := by
      apply Finset.sum_congr rfl
      intro r _
      simp_rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring

#check weighted_spans

theorem affine_expansion (lam : Fin 41 → Fin m → ℤ) (p : Fin 41 → Fin m → Plane)
    (g : Fin 9 → ℝ) :
    (denominator:ℝ)*minorant lam p g =
      (intercept lam p:ℝ)+32768*(∑ r, (coefficient lam p r:ℝ)*g r) := by
  have hp : (denominator:ℝ)*pressure g =
      32768*(∑ r, (((bN r:ℤ)*1000000000000:ℤ):ℝ)*g r) := by
    unfold pressure
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    change (denominator:ℝ)*(((bN r:ℝ)/10000000000)*g r) = _
    norm_num [denominator]
    ring
  have hterm (t : Fin 41) (k : Fin m) :
      (denominator:ℝ)*(((lam t k:ℝ)/1000000000000)*line (p t k) (span g t)) =
        ((lam t k*(p t k).constant:ℤ):ℝ)+
          32768*((lam t k*(p t k).slope:ℤ):ℝ)*span g t := by
    unfold line denominator
    push_cast
    ring
  unfold minorant
  rw [mul_add,hp]
  simp_rw [Finset.mul_sum,hterm]
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  rw [weighted_spans]
  unfold intercept coefficient
  push_cast
  simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  ring_nf
  congr 1
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

#check affine_expansion

def flowCheck (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (p : Fin 41 → Fin m → Plane) (edges : List FlowBasisCodec.Edge) (target : ℤ) : Bool :=
  massCheck lam && FlowBasisCodec.checkBasis edges cell
    (WindowDifferenceCell.divergence (coefficient lam p)) (intercept lam p) target

theorem value_bound (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (p : Fin 41 → Fin m → Plane) (edges : List FlowBasisCodec.Edge) (target : ℤ)
    (g : Fin 9 → ℝ) (hg : WindowDifferenceCell.Contains cell g)
    (hc : flowCheck cell lam p edges target = true)
    (hline : ∀ t k, lam t k ≠ 0 → line (p t k) (span g t) ≤
      WindowKernel.w 24 WindowKernel.d24 (span g t)) :
    (target:ℝ)/(denominator:ℝ) ≤ WindowGapEnergy.Fw24 g := by
  have checks : massCheck lam = true ∧
      FlowBasisCodec.checkBasis edges cell (WindowDifferenceCell.divergence (coefficient lam p))
        (intercept lam p) target = true := by
    simpa only [flowCheck,Bool.and_eq_true] using hc
  have hf := WindowDifferenceCell.flow_gap_bound cell g hg edges (coefficient lam p)
    (intercept lam p) target checks.2
  rw [← affine_expansion] at hf
  have hd : (0:ℝ) < (denominator:ℝ) := by norm_num [denominator]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left (minorant_le lam p g checks.1 hline) hd.le
  nlinarith

set_option pp.fullNames true
#print axioms capacity_eq
#print axioms minorant_le
#print axioms affine_expansion
#print axioms value_bound
end StructuralGoal20261016.WindowValueFlow
end
