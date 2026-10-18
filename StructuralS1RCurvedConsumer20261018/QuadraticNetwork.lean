import Mathlib

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section

namespace StructuralS1RCurvedConsumer20261018.QuadraticNetwork

def linear {d : ℕ} (a : Fin d → ℝ) (p : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, a j * p j

def energy {d n : ℕ} (a : Fin n → Fin d → ℝ) (c q : Fin n → ℝ)
    (p : Fin d → ℝ) : ℝ :=
  ∑ i : Fin n, c i * (linear (a i) p - q i) ^ 2

def residual {d n : ℕ} (a : Fin n → Fin d → ℝ) (c q : Fin n → ℝ)
    (pstar : Fin d → ℝ) (j : Fin d) : ℝ :=
  ∑ i : Fin n, c i * (linear (a i) pstar - q i) * a i j

theorem linear_sub {d : ℕ} (a p pstar : Fin d → ℝ) :
    linear a (fun j => p j - pstar j) = linear a p - linear a pstar := by
  simp only [linear, mul_sub, Finset.sum_sub_distrib]

/-- Full coordinate stationarity is the only certificate needed; no inversion,
gauge uniqueness, or positive-definiteness assertion is used. -/
theorem square_completion {d n : ℕ} (a : Fin n → Fin d → ℝ)
    (c q : Fin n → ℝ) (pstar : Fin d → ℝ)
    (hstationary : ∀ j, residual a c q pstar j = 0) (p : Fin d → ℝ) :
    energy a c q p = energy a c q pstar +
      ∑ i : Fin n, c i * (linear (a i) (fun j => p j - pstar j)) ^ 2 := by
  classical
  let h : Fin d → ℝ := fun j => p j - pstar j
  have hcross : (∑ i : Fin n,
      c i * (linear (a i) pstar - q i) * linear (a i) h) = 0 := by
    calc
      (∑ i : Fin n, c i * (linear (a i) pstar - q i) * linear (a i) h) =
          ∑ i : Fin n, ∑ j : Fin d,
            (c i * (linear (a i) pstar - q i) * a i j) * h j := by
        apply Finset.sum_congr rfl
        intro i _
        unfold linear
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin d, ∑ i : Fin n,
          (c i * (linear (a i) pstar - q i) * a i j) * h j :=
        Finset.sum_comm
      _ = ∑ j : Fin d, residual a c q pstar j * h j := by
        apply Finset.sum_congr rfl
        intro j _
        unfold residual
        rw [Finset.sum_mul]
      _ = 0 := by simp only [hstationary, zero_mul, Finset.sum_const_zero]
  have hexpand (i : Fin n) : c i * (linear (a i) p - q i) ^ 2 =
      c i * (linear (a i) pstar - q i) ^ 2 +
        2 * (c i * (linear (a i) pstar - q i) * linear (a i) h) +
          c i * (linear (a i) h) ^ 2 := by
    have hlin : linear (a i) p = linear (a i) pstar + linear (a i) h := by
      dsimp [h]
      rw [linear_sub]
      ring
    rw [hlin]
    ring
  calc
    energy a c q p = ∑ i : Fin n,
        (c i * (linear (a i) pstar - q i) ^ 2 +
          2 * (c i * (linear (a i) pstar - q i) * linear (a i) h) +
            c i * (linear (a i) h) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hexpand i
    _ = energy a c q pstar +
        2 * (∑ i : Fin n, c i * (linear (a i) pstar - q i) * linear (a i) h) +
          ∑ i : Fin n, c i * (linear (a i) h) ^ 2 := by
      simp only [energy, Finset.sum_add_distrib, Finset.mul_sum]
    _ = energy a c q pstar +
        ∑ i : Fin n, c i * (linear (a i) (fun j => p j - pstar j)) ^ 2 := by
      rw [hcross]
      simp only [mul_zero, add_zero]

theorem lower_of_stationary {d n : ℕ} (a : Fin n → Fin d → ℝ)
    (c q : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (pstar : Fin d → ℝ)
    (hstationary : ∀ j, residual a c q pstar j = 0) (p : Fin d → ℝ) :
    energy a c q pstar ≤ energy a c q p := by
  rw [square_completion a c q pstar hstationary p]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _))

/-- Oriented physical spans are a special case of the finite linear network. -/
def incidence {d : ℕ} (tail head : Fin d) (j : Fin d) : ℝ :=
  (if j = head then 1 else 0) - (if j = tail then 1 else 0)

theorem linear_incidence {d : ℕ} (tail head : Fin d) (p : Fin d → ℝ) :
    linear (incidence tail head) p = p head - p tail := by
  classical
  have hsingle (k : Fin d) :
      (∑ j : Fin d, (if j = k then (1 : ℝ) else 0) * p j) = p k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact False.elim (h (Finset.mem_univ k))
  simp only [linear, incidence, sub_mul, Finset.sum_sub_distrib]
  rw [hsingle head, hsingle tail]

theorem graph_lower_of_stationary {d n : ℕ} (tail head : Fin n → Fin d)
    (c q : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (pstar : Fin d → ℝ)
    (hstationary : ∀ j,
      ∑ i : Fin n, c i * (pstar (head i) - pstar (tail i) - q i) *
        incidence (tail i) (head i) j = 0) (p : Fin d → ℝ) :
    (∑ i : Fin n, c i * (pstar (head i) - pstar (tail i) - q i) ^ 2) ≤
      ∑ i : Fin n, c i * (p (head i) - p (tail i) - q i) ^ 2 := by
  have hs : ∀ j, residual (fun i => incidence (tail i) (head i)) c q pstar j = 0 := by
    intro j
    simpa only [residual, linear_incidence] using hstationary j
  simpa only [energy, linear_incidence] using
    lower_of_stationary (fun i => incidence (tail i) (head i)) c q hc pstar hs p

end StructuralS1RCurvedConsumer20261018.QuadraticNetwork

set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.QuadraticNetwork.square_completion
set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.QuadraticNetwork.lower_of_stationary
set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.QuadraticNetwork.graph_lower_of_stationary

end
