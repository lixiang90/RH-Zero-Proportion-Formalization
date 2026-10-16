/- SPDX-License-Identifier: Apache-2.0
Whole-cell quadratic energy rows from the actual scalar Taylor theorem.
Curvature lower bounds may have either sign. Point/slope uncertainties are
paid uniformly in the original gap coordinates, matching the moment packet.
Finite point/grid checks and coefficient packets are separate obligations.
-/
import StructuralGoal20261016.WindowScalarMinorant
import StructuralGoal20261016.WindowGramDiagonal
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentEnergy
open WindowGramTransfer WindowDirectionalAffine
open WindowScalarMinorant (f)

theorem pair_order : ∀ e : Fin 41, pairI e ≤ pairJ e := by decide +kernel

theorem incidence_nonneg (e : Fin 41) (r : Fin 9) : 0 ≤ incidence e r := by
  have hij := pair_order e
  have hijN : (pairI e:ℕ) ≤ (pairJ e:ℕ) := hij
  unfold incidence
  split_ifs <;> norm_num <;> omega

def spanRadius (R : Fin 9 → ℝ) (e : Fin 41) : ℝ := ∑ r, R r*incidence e r
def errorGradient (E : Fin 41 → ℝ) (r : Fin 9) : ℝ := ∑ e, weight e*E e*incidence e r
def payment (E : Fin 41 → ℝ) (R : Fin 9 → ℝ) : ℝ := ∑ r, errorGradient E r*R r

theorem span_sub_abs_le (g p : Fin 9 → ℝ) (R : Fin 9 → ℝ)
    (hR : ∀ r, |g r-p r| ≤ R r) (e : Fin 41) :
    |span g e-span p e| ≤ spanRadius R e := by
  rw [WindowGramDiagonal.span_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  unfold spanRadius
  apply Finset.sum_le_sum
  intro r _
  rw [abs_mul,abs_of_nonneg (incidence_nonneg e r)]
  exact mul_le_mul_of_nonneg_right (hR r) (incidence_nonneg e r)

theorem payment_eq (E : Fin 41 → ℝ) (R : Fin 9 → ℝ) :
    payment E R = ∑ e, weight e*E e*spanRadius R e := by
  unfold payment errorGradient spanRadius
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro r _
  ring

def scalarPolynomial (p g : Fin 9 → ℝ) (V S L E : Fin 41 → ℝ) (R : Fin 9 → ℝ) : ℝ :=
  pressure g+∑ e, weight e*(V e-E e*spanRadius R e+
    S e*(span g e-span p e)+(L e/2)*(span g e-span p e)^2)

def polynomial (p g : Fin 9 → ℝ) (V S L E : Fin 41 → ℝ) (R : Fin 9 → ℝ) : ℝ :=
  WindowGramDiagonal.constant p V+
    (∑ r, WindowGramDiagonal.linear S r*(g r-p r))+
    (∑ e, weight e*(L e/2)*(span g e-span p e)^2)-payment E R

theorem scalarPolynomial_eq (p g : Fin 9 → ℝ) (V S L E : Fin 41 → ℝ) (R : Fin 9 → ℝ) :
    scalarPolynomial p g V S L E R = polynomial p g V S L E R := by
  have hlin := WindowGramDiagonal.linear_identity g p V S
  have hsplit : scalarPolynomial p g V S L E R =
      (pressure g+∑ e, weight e*(V e+S e*(span g e-span p e)))+
      (∑ e, weight e*(L e/2)*(span g e-span p e)^2)-
      (∑ e, weight e*E e*spanRadius R e) := by
    simp only [scalarPolynomial,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    ring
  rw [hsplit,hlin,← payment_eq]
  rfl

theorem lower (p g : Fin 9 → ℝ) (V S L E : Fin 41 → ℝ) (R : Fin 9 → ℝ)
    (a b : Fin 41 → ℝ)
    (hp : ∀ e, span p e ∈ Icc (a e) (b e))
    (hg : ∀ e, span g e ∈ Icc (a e) (b e))
    (hR : ∀ r, |g r-p r| ≤ R r)
    (hV : ∀ e, V e ≤ f (span p e))
    (hS : ∀ e, |iteratedDeriv 1 f (span p e)-S e| ≤ E e)
    (hsecond : ∀ e, ∀ x ∈ Icc (a e) (b e), L e ≤ iteratedDeriv 2 f x) :
    polynomial p g V S L E R ≤ WindowGapEnergy.Fw24 g := by
  rw [← scalarPolynomial_eq]
  apply WindowGramTransfer.scalar_sum_le
  intro e
  have hE : 0 ≤ E e := (abs_nonneg _).trans (hS e)
  have hVl : (V e-E e*spanRadius R e)+E e*spanRadius R e ≤ f (span p e) := by
    linarith [hV e]
  have hc : ∀ x ∈ Icc (a e) (b e), 2*(L e/2) ≤ iteratedDeriv 2 f x := by
    intro x hx
    nlinarith [hsecond e x hx]
  exact WindowScalarMinorant.quadratic_minorant (hp e) (hg e) hE
    (span_sub_abs_le g p R hR e) hc hVl (hS e)

theorem sublevel (p g : Fin 9 → ℝ) (V S L E : Fin 41 → ℝ) (R : Fin 9 → ℝ)
    (a b : Fin 41 → ℝ) {c : ℝ}
    (hp : ∀ e, span p e ∈ Icc (a e) (b e))
    (hg : ∀ e, span g e ∈ Icc (a e) (b e))
    (hR : ∀ r, |g r-p r| ≤ R r)
    (hV : ∀ e, V e ≤ f (span p e))
    (hS : ∀ e, |iteratedDeriv 1 f (span p e)-S e| ≤ E e)
    (hsecond : ∀ e, ∀ x ∈ Icc (a e) (b e), L e ≤ iteratedDeriv 2 f x)
    (hc : WindowGapEnergy.Fw24 g < c) : polynomial p g V S L E R < c :=
  (lower p g V S L E R a b hp hg hR hV hS hsecond).trans_lt hc

set_option pp.fullNames true
#print axioms incidence_nonneg
#print axioms span_sub_abs_le
#print axioms payment_eq
#print axioms scalarPolynomial_eq
#print axioms lower
#print axioms sublevel
end StructuralGoal20261016.WindowMomentEnergy
end
