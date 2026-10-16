/- SPDX-License-Identifier: Apache-2.0
Actual iterated kernel derivatives and uniform squared-kernel derivative bound.
The moment chain is identified with Mathlib's iteratedDeriv; Leibniz and the
binomial theorem give |w^(r)| ≤ (2*pi)^r without derivative premises.
-/
import StructuralGoal20261016.WindowDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
namespace StructuralGoal20261016.WindowTaylorBridge
open WindowEnergy WindowKernel WindowDerivative

theorem iterated_k_eq_jet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) :
 iteratedDeriv r (k N d) = jet N d r := by
 induction r with
 | zero => rw [iteratedDeriv_zero]; exact (jet_zero_eq N d).symm
 | succ r ih =>
   rw [iteratedDeriv_succ, ih]
   exact funext fun x => (jet_hasDerivAt N d r x).deriv

theorem k_contDiff (N : ℕ) (d : ℕ → ℝ) (r : ℕ) : ContDiff ℝ r (k N d) := by
 apply contDiff_of_differentiable_iteratedDeriv
 intro q _
 rw [iterated_k_eq_jet]
 exact fun x => (jet_hasDerivAt N d q x).differentiableAt

theorem iterated_w_eq (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 iteratedDeriv r (w N d) x = ∑ i ∈ Finset.range (r+1),
   (r.choose i : ℝ) * jet N d i x * jet N d (r-i) x := by
 have he : w N d = (k N d) * (k N d) := by
   funext y
   simp only [w, Pi.mul_apply, pow_two]
 rw [he, iteratedDeriv_mul (k_contDiff N d r).contDiffAt (k_contDiff N d r).contDiffAt]
 simp_rw [iterated_k_eq_jet]

theorem iterated_w_abs_le (N : ℕ) (d : ℕ → ℝ)
 (hpos : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v N d t) (r : ℕ) (x : ℝ) :
 |iteratedDeriv r (w N d) x| ≤ (2*π)^r := by
 rw [iterated_w_eq]
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have ht : ∀ i ∈ Finset.range (r+1),
   |(r.choose i : ℝ) * jet N d i x * jet N d (r-i) x| ≤
     (r.choose i : ℝ) * π^r := by
   intro i hi
   have hir : i ≤ r := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
   rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (r.choose i : ℝ))]
   calc
     _ ≤ (r.choose i : ℝ) * π^i * π^(r-i) :=
       mul_le_mul (mul_le_mul_of_nonneg_left (jet_abs_le N d hpos i x) (by positivity))
         (jet_abs_le N d hpos (r-i) x) (abs_nonneg _) (by positivity)
     _ = (r.choose i : ℝ) * π^r := by
       rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hir]
 refine (Finset.sum_le_sum ht).trans ?_
 have hchoose : (∑ i ∈ Finset.range (r+1), (r.choose i : ℝ)) = 2^r := by
   exact_mod_cast Nat.sum_range_choose r
 rw [← Finset.sum_mul, hchoose, ← mul_pow]

theorem w24_iterated_abs_le (r : ℕ) (x : ℝ) :
 |iteratedDeriv r (w 24 d24) x| ≤ (44/7 : ℝ)^r := by
 have h := iterated_w_abs_le 24 d24 v24_nonneg r x
 have hp : 2*π ≤ (44/7 : ℝ) := by linarith [Opeth.AMMajorant.pi_coarse.2]
 exact h.trans (pow_le_pow_left₀ (by positivity) hp r)

theorem w24_sixteen_abs_le (x : ℝ) :
 |iteratedDeriv 16 (w 24 d24) x| ≤ (44/7 : ℝ)^16 := w24_iterated_abs_le 16 x

theorem w24_twentyfour_abs_le (x : ℝ) :
 |iteratedDeriv 24 (w 24 d24) x| ≤ (44/7 : ℝ)^24 := w24_iterated_abs_le 24 x

theorem k24_second_abs_le (x : ℝ) :
 |iteratedDeriv 2 (k 24 d24) x| ≤ 4 := by
 rw [iterated_k_eq_jet]
 exact jet24_two_abs_le x

#print axioms iterated_k_eq_jet
#print axioms iterated_w_abs_le
#print axioms w24_sixteen_abs_le
#print axioms k24_second_abs_le
end StructuralGoal20261016.WindowTaylorBridge
end
