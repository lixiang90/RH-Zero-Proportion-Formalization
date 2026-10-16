/- SPDX-License-Identifier: Apache-2.0
Residual-PSD cuts in the existing actual 464-variable lift. A scalar affine
derivative enclosure gives a family of valid linear moment inequalities.
No derivative-by-derivative moments, numerical exclusion, or coverage claim
are introduced. The enclosure remains an explicit analytic hypothesis.
-/
import StructuralGoal20261016.WindowMomentPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentResidualPSD
open WindowMomentLayout WindowMomentPolynomial

def linearCoeff (v beta : Fin 9 → ℚ) (v0 beta0 t : ℚ) (s : Fin 9) : ℚ :=
  2*v0*v s-2*t*(v0*beta s+beta0*v s)

def quadraticCoeff (v beta : Fin 9 → ℚ) (t : ℚ) (s r : Fin 9) : ℚ :=
  v s*v r-2*t*v s*beta r

def constantCoeff (v0 beta0 t eps : ℚ) : ℚ :=
  v0^2-2*t*v0*beta0+t^2*eps^2

/-- The nonpositive-row convention used by the existing Farkas consumer. -/
def cut (e : Fin 41) (center radius v beta : Fin 9 → ℚ)
    (v0 beta0 t eps : ℚ) : RatForm where
  gap := fun s => -linearCoeff v beta v0 beta0 t s/radius s
  scalar := fun j => if j=e then -2*t*v0 else 0
  h := collectH (fun s r => -quadraticCoeff v beta t s r)
  q := fun s j => if j=e then -2*t*v s else 0
  bound := constantCoeff v0 beta0 t eps-
    ∑ s, linearCoeff v beta v0 beta0 t s*center s/radius s

theorem quadratic_eval (v beta : Fin 9 → ℚ) (t : ℚ) (y : Fin 9 → ℝ) :
    (∑ s, ∑ r, (quadraticCoeff v beta t s r:ℝ)*(y s*y r)) =
      dotQ v y*dotQ v y-2*(t:ℝ)*dotQ v y*dotQ beta y := by
  simp only [quadraticCoeff,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,
    sub_mul,Finset.sum_sub_distrib]
  have hprod (a b : Fin 9 → ℚ) :
      (∑ s, ∑ r, ((a s:ℝ)*(b r:ℝ))*(y s*y r)) = dotQ a y*dotQ b y := by
    unfold dotQ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hscale :
      (∑ s, ∑ r, (2*(t:ℝ)*(v s:ℝ)*(beta r:ℝ))*(y s*y r)) =
        2*(t:ℝ)*(dotQ v y*dotQ beta y) := by
    rw [← hprod v beta]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [hprod v v,hscale]
  ring

theorem linear_eval (v beta : Fin 9 → ℚ) (v0 beta0 t : ℚ) (y : Fin 9 → ℝ) :
    dotQ (linearCoeff v beta v0 beta0 t) y =
      2*(v0:ℝ)*dotQ v y-
        2*(t:ℝ)*((v0:ℝ)*dotQ beta y+(beta0:ℝ)*dotQ v y) := by
  unfold dotQ
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [linearCoeff,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_ofNat]
  ring

theorem cut_identity (e : Fin 41) (center radius v beta : Fin 9 → ℚ)
    (v0 beta0 t eps : ℚ) (g : Fin 9 → ℝ)
    (hr : ∀ s, radius s ≠ 0) :
    eval (cut e center radius v beta v0 beta0 t eps)
        (realVector center) (realVector radius) g-
      ((cut e center radius v beta v0 beta0 t eps).bound:ℝ) =
      -(((v0:ℝ)+dotQ v (normalized (realVector center) (realVector radius) g))^2+
        2*(t:ℝ)*((v0:ℝ)+dotQ v (normalized (realVector center) (realVector radius) g))*
          (u g e-((beta0:ℝ)+dotQ beta
            (normalized (realVector center) (realVector radius) g)))+
        (t:ℝ)^2*(eps:ℝ)^2) := by
  classical
  let y := normalized (realVector center) (realVector radius) g
  let L := linearCoeff v beta v0 beta0 t
  have hgap :
      dotQ (fun s => -L s/radius s) g+
        ((∑ s, L s*center s/radius s:ℚ):ℝ) = -dotQ L y := by
    dsimp [dotQ]
    push_cast
    rw [← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [y,normalized,realVector]
    have hn : (radius s:ℝ) ≠ 0 := by exact_mod_cast hr s
    field_simp [hn]
    <;> ring
  have select (a : ℚ) (x : Fin 41 → ℝ) :
      dotQ (fun j => if j=e then a else 0) x = (a:ℝ)*x e := by
    unfold dotQ
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  have hscalar :
      dotQ (fun j => if j=e then -2*t*v0 else 0) (u g) =
        -2*(t:ℝ)*(v0:ℝ)*u g e := by
    rw [select]
    push_cast
    ring
  have hq :
      (∑ s, dotQ (fun j => if j=e then -2*t*v s else 0)
        (fun j => y s*u g j)) = -2*(t:ℝ)*dotQ v y*u g e := by
    simp_rw [select]
    push_cast
    unfold dotQ
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hh :
      dotQ (collectH (fun s r => -quadraticCoeff v beta t s r))
        (fun k => y (hFirst k)*y (hSecond k)) =
      -(dotQ v y*dotQ v y-2*(t:ℝ)*dotQ v y*dotQ beta y) := by
    rw [collectH_eval]
    simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
    rw [quadratic_eval]
  rw [eval_actual]
  change
    (dotQ (fun s => -L s/radius s) g+
      (dotQ (fun j => if j=e then -2*t*v0 else 0) (u g)+
        (dotQ (collectH (fun s r => -quadraticCoeff v beta t s r))
          (fun k => y (hFirst k)*y (hSecond k))+
          ∑ s, dotQ (fun j => if j=e then -2*t*v s else 0)
            (fun j => y s*u g j))))-
      ((constantCoeff v0 beta0 t eps-
        ∑ s, L s*center s/radius s:ℚ):ℝ) = _
  rw [hscalar,hh,hq,Rat.cast_sub]
  have hl := linear_eval v beta v0 beta0 t y
  change dotQ L y = _ at hl
  have hc : (constantCoeff v0 beta0 t eps:ℝ) =
      (v0:ℝ)^2-2*(t:ℝ)*(v0:ℝ)*(beta0:ℝ)+(t:ℝ)^2*(eps:ℝ)^2 := by
    simp [constantCoeff]
  rw [hc]
  change _ = -(((v0:ℝ)+dotQ v y)^2+
    2*(t:ℝ)*((v0:ℝ)+dotQ v y)*(u g e-((beta0:ℝ)+dotQ beta y))+
      (t:ℝ)^2*(eps:ℝ)^2)
  nlinarith only [hgap,hl]

theorem residual_polynomial_nonneg (A delta t eps : ℝ)
    (hslab : |delta| ≤ eps) :
    0 ≤ A^2+2*t*A*delta+t^2*eps^2 := by
  have hab := abs_le.mp hslab
  have herr : 0 ≤ eps^2-delta^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab.2) (by linarith [hab.1] : 0 ≤ eps+delta)]
  have hpay := mul_nonneg (sq_nonneg t) herr
  nlinarith [sq_nonneg (A+t*delta)]

/-- Every actual scalar affine enclosure gives the corresponding old-layout cut. -/
theorem actual_cut_nonpos (e : Fin 41) (center radius v beta : Fin 9 → ℚ)
    (v0 beta0 t eps : ℚ) (g : Fin 9 → ℝ)
    (hr : ∀ s, radius s ≠ 0)
    (hslab : |u g e-((beta0:ℝ)+dotQ beta
      (normalized (realVector center) (realVector radius) g))| ≤ (eps:ℝ)) :
    eval (cut e center radius v beta v0 beta0 t eps)
      (realVector center) (realVector radius) g ≤
        ((cut e center radius v beta v0 beta0 t eps).bound:ℝ) := by
  apply sub_nonpos.mp
  rw [cut_identity e center radius v beta v0 beta0 t eps g hr]
  exact neg_nonpos.mpr (residual_polynomial_nonneg _ _ _ _ hslab)

set_option pp.fullNames true
#print axioms quadratic_eval
#print axioms linear_eval
#print axioms cut_identity
#print axioms residual_polynomial_nonneg
#print axioms actual_cut_nonpos
end StructuralGoal20261016.WindowMomentResidualPSD
end
