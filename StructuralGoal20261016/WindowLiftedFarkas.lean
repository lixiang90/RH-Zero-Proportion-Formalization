/- SPDX-License-Identifier: Apache-2.0
Nonnegative integer combinations of inequalities in the shared gaps and
the actual forty-one derivative values. Residual derivative coefficients
are paid using the proved global bound, then an integer forest flow
certifies strict separation from every point of the difference cell.
-/
import StructuralGoal20261016.WindowDirectionalFlow
import StructuralGoal20261016.WindowGridRange
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowLiftedFarkas
open WindowGramTransfer

structure Form where
  gap : Fin 9 → ℤ
  scalar : Fin 41 → ℤ
  bound : ℤ

def eval (a : Form) (g : Fin 9 → ℝ) : ℝ :=
  (∑ r, (a.gap r:ℝ)*g r)+
    ∑ e, (a.scalar e:ℝ)*WindowGapEnergy.w1 (span g e)

def aggregate {n : ℕ} (a : Fin n → Form) (mu : Fin n → ℤ) : Form where
  gap := fun r => ∑ i, mu i*(a i).gap r
  scalar := fun e => ∑ i, mu i*(a i).scalar e
  bound := ∑ i, mu i*(a i).bound

theorem weighted_dot {n p : ℕ} (a : Fin n → Fin p → ℤ)
    (mu : Fin n → ℤ) (x : Fin p → ℝ) :
    (∑ r, ((∑ i, mu i*a i r:ℤ):ℝ)*x r) =
      ∑ i, (mu i:ℝ)*(∑ r, (a i r:ℝ)*x r) := by
  simp only [Int.cast_sum,Int.cast_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem aggregate_eval {n : ℕ} (a : Fin n → Form) (mu : Fin n → ℤ)
    (g : Fin 9 → ℝ) :
    eval (aggregate a mu) g = ∑ i, (mu i:ℝ)*eval (a i) g := by
  change (∑ r, ((∑ i, mu i*(a i).gap r:ℤ):ℝ)*g r)+
    (∑ e, ((∑ i, mu i*(a i).scalar e:ℤ):ℝ)*WindowGapEnergy.w1 (span g e)) = _
  rw [weighted_dot,weighted_dot,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold eval
  ring

theorem aggregate_valid {n : ℕ} (a : Fin n → Form) (mu : Fin n → ℤ)
    (g : Fin 9 → ℝ) (hmu : ∀ i, 0 ≤ mu i)
    (ha : ∀ i, eval (a i) g ≤ ((a i).bound:ℝ)) :
    eval (aggregate a mu) g ≤ ((aggregate a mu).bound:ℝ) := by
  rw [aggregate_eval]
  change _ ≤ ((∑ i, mu i*(a i).bound:ℤ):ℝ)
  push_cast
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (ha i) (by exact_mod_cast hmu i)

def residual (a : Form) : ℤ := ∑ e, |a.scalar e|

theorem residual_lower (a : Form) (g : Fin 9 → ℝ) :
    -(7:ℝ)*(residual a:ℝ) ≤
      ∑ e, (a.scalar e:ℝ)*WindowGapEnergy.w1 (span g e) := by
  have he (e : Fin 41) : -(7:ℝ)*|(a.scalar e:ℝ)| ≤
      (a.scalar e:ℝ)*WindowGapEnergy.w1 (span g e) := by
    have hb := (WindowGridRange.fallback (span g e)).1
    have hp : |(a.scalar e:ℝ)*WindowGapEnergy.w1 (span g e)| ≤
        7*|(a.scalar e:ℝ)| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (a.scalar e:ℝ)]
    have hn := neg_abs_le ((a.scalar e:ℝ)*WindowGapEnergy.w1 (span g e))
    linarith
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => he e)
  simpa only [residual,Int.cast_sum,Int.cast_abs,Finset.mul_sum,neg_mul] using hs

def check {n : ℕ} (cell : DifferenceCell.Cell 10) (a : Fin n → Form)
    (mu : Fin n → ℤ) (minimum : ℤ) (edges : List FlowBasisCodec.Edge) : Bool :=
  (decide (∀ i, 0 ≤ mu i) &&
    decide (0 < minimum-7*32768*residual (aggregate a mu)-32768*(aggregate a mu).bound)) &&
    FlowBasisCodec.checkBasis edges cell
      (WindowDifferenceCell.divergence (aggregate a mu).gap) 0 minimum

theorem exclude {n : ℕ} (cell : DifferenceCell.Cell 10) (a : Fin n → Form)
    (mu : Fin n → ℤ) (minimum : ℤ) (edges : List FlowBasisCodec.Edge)
    (hc : check cell a mu minimum edges = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g)
    (ha : ∀ i, eval (a i) g ≤ ((a i).bound:ℝ)) : False := by
  have hh : (decide (∀ i, 0 ≤ mu i) = true ∧
      decide (0 < minimum-7*32768*residual (aggregate a mu)-32768*(aggregate a mu).bound) = true) ∧
      FlowBasisCodec.checkBasis edges cell
        (WindowDifferenceCell.divergence (aggregate a mu).gap) 0 minimum = true := by
    simpa only [check,Bool.and_eq_true] using hc
  have hm : ∀ i, 0 ≤ mu i := of_decide_eq_true hh.1.1
  have hn : 0 < minimum-7*32768*residual (aggregate a mu)-32768*(aggregate a mu).bound :=
    of_decide_eq_true hh.1.2
  have hp : (0:ℝ) < (minimum:ℝ)-7*32768*(residual (aggregate a mu):ℝ)-
      32768*((aggregate a mu).bound:ℝ) := by exact_mod_cast hn
  have hf := WindowDifferenceCell.flow_gap_bound cell g hg edges
    (aggregate a mu).gap 0 minimum hh.2
  have hv := aggregate_valid a mu g hm ha
  have hr := residual_lower (aggregate a mu) g
  unfold eval at hv
  norm_num only [Int.cast_zero,zero_add] at hf
  linarith

set_option pp.fullNames true
#print axioms aggregate_eval
#print axioms aggregate_valid
#print axioms residual_lower
#print axioms exclude
end StructuralGoal20261016.WindowLiftedFarkas
end
