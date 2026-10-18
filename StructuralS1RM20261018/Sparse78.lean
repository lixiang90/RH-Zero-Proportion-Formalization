import Mathlib
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace StructuralS1RM20261018.Sparse78

structure Row where
  entries : List (Fin 78 × ℤ)
  rhs : ℤ

def coefficient (r : Row) (j : Fin 78) : ℤ :=
  (r.entries.map fun e => if e.1 = j then e.2 else 0).sum

def eval (r : Row) (z : Fin 78 → ℝ) : ℝ :=
  (r.entries.map fun e => (e.2 : ℝ) * z e.1).sum

theorem eval_eq_dot (r : Row) (z : Fin 78 → ℝ) :
    eval r z = ∑ j : Fin 78, (coefficient r j : ℝ) * z j := by
  classical
  rcases r with ⟨entries, rhs⟩
  induction entries with
  | nil => simp [eval, coefficient]
  | cons e es ih =>
      simp only [eval, coefficient, List.map_cons, List.sum_cons] at *
      simp_rw [Int.cast_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp only [ite_mul, zero_mul, Int.cast_ite, Int.cast_zero]
      rw [Finset.sum_ite_eq']
      simpa using congrArg (fun x : ℝ => (e.2 : ℝ) * z e.1 + x) ih

def check {n : ℕ} (rows : Fin n → Row) (weight : Fin n → ℕ)
    (den : ℕ) (objective : Fin 78 → ℤ) (target : ℤ) : Bool :=
  decide (0 < den ∧
    (∀ j : Fin 78, (den : ℤ) * objective j +
      ∑ i : Fin n, (weight i : ℤ) * coefficient (rows i) j = 0) ∧
    (den : ℤ) * target + ∑ i : Fin n, (weight i : ℤ) * (rows i).rhs ≤ 0)

theorem sound {n : ℕ} (rows : Fin n → Row) (weight : Fin n → ℕ)
    (den : ℕ) (objective : Fin 78 → ℤ) (target : ℤ)
    (hc : check rows weight den objective target = true)
    (z : Fin 78 → ℝ) (hr : ∀ i, eval (rows i) z ≤ ((rows i).rhs : ℝ)) :
    (target : ℝ) ≤ ∑ j : Fin 78, (objective j : ℝ) * z j := by
  classical
  have hh : 0 < den ∧
      (∀ j : Fin 78, (den : ℤ) * objective j +
        ∑ i : Fin n, (weight i : ℤ) * coefficient (rows i) j = 0) ∧
      (den : ℤ) * target + ∑ i : Fin n, (weight i : ℤ) * (rows i).rhs ≤ 0 := by
    simpa only [check, decide_eq_true_eq] using hc
  have hd : (0 : ℝ) < den := by exact_mod_cast hh.1
  have hb (j : Fin 78) : (den : ℝ) * (objective j : ℝ) +
      ∑ i : Fin n, (weight i : ℝ) * (coefficient (rows i) j : ℝ) = 0 := by
    exact_mod_cast hh.2.1 j
  have hcost : (den : ℝ) * (target : ℝ) +
      ∑ i : Fin n, (weight i : ℝ) * ((rows i).rhs : ℝ) ≤ 0 := by
    exact_mod_cast hh.2.2
  have hw : (∑ i : Fin n, (weight i : ℝ) * eval (rows i) z) ≤
      ∑ i : Fin n, (weight i : ℝ) * ((rows i).rhs : ℝ) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hr i) (Nat.cast_nonneg _)
  have he : (∑ i : Fin n, (weight i : ℝ) * eval (rows i) z) =
      -(den : ℝ) * (∑ j : Fin 78, (objective j : ℝ) * z j) := by
    simp_rw [eval_eq_dot, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ j : Fin 78, ∑ i : Fin n,
        (weight i : ℝ) * ((coefficient (rows i) j : ℝ) * z j)) =
          ∑ j : Fin 78, (∑ i : Fin n,
            (weight i : ℝ) * (coefficient (rows i) j : ℝ)) * z j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ j : Fin 78, (-(den : ℝ) * (objective j : ℝ)) * z j := by
              apply Finset.sum_congr rfl
              intro j _
              have := hb j
              congr 1
              linarith
      _ = -(den : ℝ) * (∑ j : Fin 78, (objective j : ℝ) * z j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  rw [he] at hw
  apply (mul_le_mul_left hd).mp
  nlinarith

set_option pp.fullNames true
#print axioms eval_eq_dot
#print axioms sound
end StructuralS1RM20261018.Sparse78
end
