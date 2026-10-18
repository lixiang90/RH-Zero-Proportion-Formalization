import Mathlib

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section

namespace StructuralS1RCurvedConsumer20261018.SparseDual

/-- Integer coefficients with a sparse, possibly repeated, coordinate list. -/
structure Row (d : ℕ) where
  entries : List (Fin d × ℤ)
  rhs : ℤ

def coefficients {d : ℕ} : List (Fin d × ℤ) → Fin d → ℤ
  | [], _ => 0
  | e :: es, j => (if j = e.1 then e.2 else 0) + coefficients es j

def sparseValue {d : ℕ} : List (Fin d × ℤ) → (Fin d → ℝ) → ℝ
  | [], _ => 0
  | e :: es, z => (e.2 : ℝ) * z e.1 + sparseValue es z

def coefficient {d : ℕ} (r : Row d) (j : Fin d) : ℤ := coefficients r.entries j

def eval {d : ℕ} (r : Row d) (z : Fin d → ℝ) : ℝ := sparseValue r.entries z

theorem sparseValue_eq_dot {d : ℕ} (entries : List (Fin d × ℤ))
    (z : Fin d → ℝ) :
    sparseValue entries z = ∑ j : Fin d, (coefficients entries j : ℝ) * z j := by
  classical
  induction entries with
  | nil => simp [sparseValue, coefficients]
  | cons e es ih =>
      have hsingle :
          (∑ j : Fin d, ((if j = e.1 then e.2 else 0 : ℤ) : ℝ) * z j) =
            (e.2 : ℝ) * z e.1 := by
        rw [Finset.sum_eq_single e.1]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact False.elim (h (Finset.mem_univ e.1))
      have hdot :
          (∑ j : Fin d, (coefficients (e :: es) j : ℝ) * z j) =
            (e.2 : ℝ) * z e.1 +
              ∑ j : Fin d, (coefficients es j : ℝ) * z j := by
        simp only [coefficients, Int.cast_add, add_mul, Finset.sum_add_distrib]
        rw [hsingle]
      change (e.2 : ℝ) * z e.1 + sparseValue es z = _
      rw [hdot, ih]

theorem eval_eq_dot {d : ℕ} (r : Row d) (z : Fin d → ℝ) :
    eval r z = ∑ j : Fin d, (coefficient r j : ℝ) * z j :=
  sparseValue_eq_dot r.entries z

def objectiveValue {d : ℕ} (objective : Fin d → ℤ) (z : Fin d → ℝ) : ℝ :=
  ∑ j : Fin d, (objective j : ℝ) * z j

/-- This checker contains only the finite integer identity and positivity. -/
def balanceCheck {d n : ℕ} (rows : Fin n → Row d) (weight : Fin n → ℕ)
    (den : ℕ) (objective : Fin d → ℤ) : Bool :=
  decide (0 < den ∧ ∀ j : Fin d,
    (den : ℤ) * objective j +
      ∑ i : Fin n, (weight i : ℤ) * coefficient (rows i) j = 0)

/-- Curved row inequalities pay the dual cost through their weighted remainder.
No sign assumption on an individual remainder is needed. -/
theorem remainder_sound {d n : ℕ} (rows : Fin n → Row d)
    (weight : Fin n → ℕ) (den : ℕ) (objective : Fin d → ℤ) (target : ℤ)
    (hden : 0 < den)
    (hbalance : ∀ j : Fin d, (den : ℤ) * objective j +
      ∑ i : Fin n, (weight i : ℤ) * coefficient (rows i) j = 0)
    (z : Fin d → ℝ) (remainder : Fin n → ℝ)
    (hrow : ∀ i, eval (rows i) z + remainder i ≤ ((rows i).rhs : ℝ))
    (hpayment : (den : ℝ) * (target : ℝ) +
      ∑ i : Fin n, (weight i : ℝ) * ((rows i).rhs : ℝ) ≤
        ∑ i : Fin n, (weight i : ℝ) * remainder i) :
    (target : ℝ) ≤ objectiveValue objective z := by
  classical
  have hd : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hb (j : Fin d) : (den : ℝ) * (objective j : ℝ) +
      ∑ i : Fin n, (weight i : ℝ) * (coefficient (rows i) j : ℝ) = 0 := by
    exact_mod_cast hbalance j
  have he : (∑ i : Fin n, (weight i : ℝ) * eval (rows i) z) =
      -(den : ℝ) * objectiveValue objective z := by
    calc
      (∑ i : Fin n, (weight i : ℝ) * eval (rows i) z) =
          ∑ i : Fin n, ∑ j : Fin d,
            (weight i : ℝ) * ((coefficient (rows i) j : ℝ) * z j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_eq_dot, Finset.mul_sum]
      _ = ∑ j : Fin d, ∑ i : Fin n,
          (weight i : ℝ) * ((coefficient (rows i) j : ℝ) * z j) :=
        Finset.sum_comm
      _ = ∑ j : Fin d,
          (∑ i : Fin n, (weight i : ℝ) * (coefficient (rows i) j : ℝ)) * z j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ j : Fin d, (-(den : ℝ) * (objective j : ℝ)) * z j := by
        apply Finset.sum_congr rfl
        intro j _
        have hcoef : (∑ i : Fin n,
            (weight i : ℝ) * (coefficient (rows i) j : ℝ)) =
              -(den : ℝ) * (objective j : ℝ) := by linarith [hb j]
        rw [hcoef]
      _ = -(den : ℝ) * objectiveValue objective z := by
        unfold objectiveValue
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hweighted :
      (∑ i : Fin n, (weight i : ℝ) * eval (rows i) z) +
          (∑ i : Fin n, (weight i : ℝ) * remainder i) ≤
        ∑ i : Fin n, (weight i : ℝ) * ((rows i).rhs : ℝ) := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      mul_le_mul_of_nonneg_left (hrow i) (Nat.cast_nonneg (weight i) : (0 : ℝ) ≤ _)
    simpa only [mul_add, Finset.sum_add_distrib] using h
  rw [he] at hweighted
  have hscaled : (den : ℝ) * (target : ℝ) ≤
      (den : ℝ) * objectiveValue objective z := by linarith
  by_contra hnot
  have hlt : objectiveValue objective z < (target : ℝ) := lt_of_not_ge hnot
  have hpos : 0 < (den : ℝ) * ((target : ℝ) - objectiveValue objective z) :=
    mul_pos hd (sub_pos.mpr hlt)
  nlinarith

theorem remainder_sound_of_check {d n : ℕ} (rows : Fin n → Row d)
    (weight : Fin n → ℕ) (den : ℕ) (objective : Fin d → ℤ) (target : ℤ)
    (hcheck : balanceCheck rows weight den objective = true)
    (z : Fin d → ℝ) (remainder : Fin n → ℝ)
    (hrow : ∀ i, eval (rows i) z + remainder i ≤ ((rows i).rhs : ℝ))
    (hpayment : (den : ℝ) * (target : ℝ) +
      ∑ i : Fin n, (weight i : ℝ) * ((rows i).rhs : ℝ) ≤
        ∑ i : Fin n, (weight i : ℝ) * remainder i) :
    (target : ℝ) ≤ objectiveValue objective z := by
  classical
  have h : 0 < den ∧ ∀ j : Fin d,
      (den : ℤ) * objective j +
        ∑ i : Fin n, (weight i : ℤ) * coefficient (rows i) j = 0 := by
    simpa only [balanceCheck, decide_eq_true_eq] using hcheck
  exact remainder_sound rows weight den objective target h.1 h.2 z remainder hrow hpayment

end StructuralS1RCurvedConsumer20261018.SparseDual

set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.SparseDual.eval_eq_dot
set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.SparseDual.remainder_sound
set_option pp.fullNames true in
#print axioms StructuralS1RCurvedConsumer20261018.SparseDual.remainder_sound_of_check

end
