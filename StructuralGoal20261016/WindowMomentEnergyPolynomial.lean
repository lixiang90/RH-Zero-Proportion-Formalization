/- SPDX-License-Identifier: Apache-2.0
Algebraic bridge from actual signed energy Taylor polynomials to rational
four-block moment rows. The feasible Taylor anchor and its uncertainty
radius are independent of the layout midpoint and normalization radius.
All 41 scalar weights enter a rational 9 by 9 coefficient matrix; no
positivity assumption on that matrix or its curvature bounds is used.
-/
import StructuralGoal20261016.WindowMomentPolynomial
import StructuralGoal20261016.WindowMomentEnergyCertificate
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentEnergyPolynomial
open WindowMomentPolynomial WindowMomentLayout
open WindowGramTransfer WindowDirectionalAffine
open WindowMomentEnergyCertificate (Packet pointRow)

def matrixEval (M : Fin 9 → Fin 9 → ℚ) (z : Fin 9 → ℝ) : ℝ :=
  ∑ s, ∑ r, (M s r:ℝ)*z s*z r

def delta (center anchor : Fin 9 → ℚ) (r : Fin 9) : ℚ := center r-anchor r

def cross (M : Fin 9 → Fin 9 → ℚ) (d : Fin 9 → ℚ) (r : Fin 9) : ℚ :=
  (∑ s, M s r*d s)+(∑ s, M r s*d s)

def quadratic (anchor : Fin 9 → ℚ) (F0 : ℚ) (gradient : Fin 9 → ℚ)
    (payment : ℚ) (M : Fin 9 → Fin 9 → ℚ) (g : Fin 9 → ℝ) : ℝ :=
  (F0:ℝ)+dotQ gradient (fun r => g r-(anchor r:ℝ))+
    matrixEval M (fun r => g r-(anchor r:ℝ))-(payment:ℝ)

def constant (anchor center : Fin 9 → ℚ) (F0 : ℚ)
    (gradient : Fin 9 → ℚ) (payment : ℚ) (M : Fin 9 → Fin 9 → ℚ) : ℚ :=
  F0-payment-(∑ r, gradient r*anchor r)+
    (∑ s, ∑ r, M s r*delta center anchor s*delta center anchor r)-
    ∑ r, cross M (delta center anchor) r*center r

def form (anchor center radius : Fin 9 → ℚ) (F0 : ℚ)
    (gradient : Fin 9 → ℚ) (payment : ℚ) (M : Fin 9 → Fin 9 → ℚ)
    (target : ℚ) : RatForm where
  gap := fun r => gradient r+cross M (delta center anchor) r
  scalar := fun _ => 0
  h := collectH (fun s r => M s r*radius s*radius r)
  q := fun _ _ => 0
  bound := target-constant anchor center F0 gradient payment M

theorem dot_vector_sub (a : Fin 9 → ℚ) (x y : Fin 9 → ℝ) :
    dotQ a (fun r => x r-y r) = dotQ a x-dotQ a y := by
  simp only [dotQ,mul_sub,Finset.sum_sub_distrib]

theorem dot_zero {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    dotQ (fun _ => (0:ℚ)) x = 0 := by simp [dotQ]

theorem cross_dot (M : Fin 9 → Fin 9 → ℚ) (d : Fin 9 → ℚ) (z : Fin 9 → ℝ) :
    dotQ (cross M d) z =
      (∑ s, ∑ r, (M s r:ℝ)*(d s:ℝ)*z r)+
        ∑ s, ∑ r, (M s r:ℝ)*z s*(d r:ℝ) := by
  unfold dotQ cross
  push_cast
  simp_rw [add_mul,Finset.sum_add_distrib,Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring

theorem matrix_recenter (M : Fin 9 → Fin 9 → ℚ)
    (anchor center : Fin 9 → ℚ) (g : Fin 9 → ℝ) :
    matrixEval M (fun r => g r-(anchor r:ℝ)) =
      matrixEval M (fun r => g r-(center r:ℝ))+
      matrixEval M (realVector (delta center anchor))+
      dotQ (cross M (delta center anchor)) (fun r => g r-(center r:ℝ)) := by
  have hd (r : Fin 9) : (delta center anchor r:ℝ) =
      (center r:ℝ)-(anchor r:ℝ) := by
    simp only [delta,Rat.cast_sub]
  have ht (s r : Fin 9) :
      (M s r:ℝ)*(g s-(anchor s:ℝ))*(g r-(anchor r:ℝ)) =
      (M s r:ℝ)*(g s-(center s:ℝ))*(g r-(center r:ℝ))+
      (M s r:ℝ)*(delta center anchor s:ℝ)*(delta center anchor r:ℝ)+
      ((M s r:ℝ)*(delta center anchor s:ℝ)*(g r-(center r:ℝ))+
        (M s r:ℝ)*(g s-(center s:ℝ))*(delta center anchor r:ℝ)) := by
    rw [hd,hd]
    ring
  rw [cross_dot]
  unfold matrixEval
  simp_rw [ht,Finset.sum_add_distrib]
  rfl

theorem moment_matrix (M : Fin 9 → Fin 9 → ℚ)
    (center radius : Fin 9 → ℚ) (g : Fin 9 → ℝ)
    (hr : ∀ r, radius r ≠ 0) :
    dotQ (collectH (fun s r => M s r*radius s*radius r))
      (fun e => normalized (realVector center) (realVector radius) g (hFirst e)*
        normalized (realVector center) (realVector radius) g (hSecond e)) =
      matrixEval M (fun r => g r-(center r:ℝ)) := by
  rw [collectH_eval]
  unfold matrixEval
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  have hn (j : Fin 9) : (radius j:ℝ)*
      normalized (realVector center) (realVector radius) g j = g j-(center j:ℝ) := by
    have hne : (radius j:ℝ) ≠ 0 := by exact_mod_cast hr j
    dsimp [normalized,realVector]
    field_simp [hne]
  push_cast
  calc
    (M s r:ℝ)*(radius s:ℝ)*(radius r:ℝ)*
        (normalized (realVector center) (realVector radius) g s*
          normalized (realVector center) (realVector radius) g r) =
      (M s r:ℝ)*((radius s:ℝ)*normalized (realVector center) (realVector radius) g s)*
        ((radius r:ℝ)*normalized (realVector center) (realVector radius) g r) := by ring
    _ = _ := by rw [hn,hn]

theorem form_identity (anchor center radius : Fin 9 → ℚ) (F0 : ℚ)
    (gradient : Fin 9 → ℚ) (payment : ℚ) (M : Fin 9 → Fin 9 → ℚ)
    (target : ℚ) (g : Fin 9 → ℝ) (hr : ∀ r, radius r ≠ 0) :
    eval (form anchor center radius F0 gradient payment M target)
        (realVector center) (realVector radius) g-
      ((form anchor center radius F0 gradient payment M target).bound:ℝ) =
      quadratic anchor F0 gradient payment M g-(target:ℝ) := by
  have hconst :
      (constant anchor center F0 gradient payment M:ℝ) =
      (F0:ℝ)-(payment:ℝ)-dotQ gradient (realVector anchor)+
        matrixEval M (realVector (delta center anchor))-
        dotQ (cross M (delta center anchor)) (realVector center) := by
    unfold constant dotQ matrixEval realVector
    push_cast <;> rfl
  have hb : ((form anchor center radius F0 gradient payment M target).bound:ℝ) =
      (target:ℝ)-(constant anchor center F0 gradient payment M:ℝ) := by
    simp only [form,Rat.cast_sub]
  rw [eval_actual]
  change
    (dotQ (fun r => gradient r+cross M (delta center anchor) r) g+
      (dotQ (fun _ => (0:ℚ)) (u g)+
        (dotQ (collectH (fun s r => M s r*radius s*radius r))
          (fun e => normalized (realVector center) (realVector radius) g (hFirst e)*
            normalized (realVector center) (realVector radius) g (hSecond e))+
          ∑ s, dotQ (fun _ => (0:ℚ))
            (fun e => normalized (realVector center) (realVector radius) g s*u g e))))-
      ((form anchor center radius F0 gradient payment M target).bound:ℝ) = _
  simp only [dot_zero,Finset.sum_const_zero,zero_add,add_zero]
  rw [dot_add,moment_matrix M center radius g hr,hb,hconst]
  unfold quadratic
  rw [matrix_recenter M anchor center g]
  have hga : dotQ gradient (fun r => g r-(anchor r:ℝ)) =
      dotQ gradient g-dotQ gradient (realVector anchor) :=
    dot_vector_sub gradient g (realVector anchor)
  have hgc : dotQ (cross M (delta center anchor)) (fun r => g r-(center r:ℝ)) =
      dotQ (cross M (delta center anchor)) g-dotQ (cross M (delta center anchor)) (realVector center) :=
    dot_vector_sub (cross M (delta center anchor)) g (realVector center)
  rw [hga,hgc]
  ring

/- Rational ledger and packet coefficients: finite checks may compare
   supplied F0/gradient/payment/M with these definitions entirely in Rat. -/

def weightQ (e : Fin 41) : ℚ := WindowValueFlow.weightQ e
def pressureQ (r : Fin 9) : ℚ :=
  (WindowDirectionalFlow.pressureInt r:ℚ)/(WindowDirectionalFlow.D:ℚ)
def incidenceQ (e : Fin 41) (r : Fin 9) : ℚ :=
  (WindowDirectionalFlow.incidence e r:ℚ)
def valueQ (p : Packet) (e : Fin 41) : ℚ := (pointRow p e).lower
def slopeQ (p : Packet) (e : Fin 41) : ℚ := (pointRow p e).slope
def errorQ (p : Packet) (e : Fin 41) : ℚ := (pointRow p e).error

def F0Q (p : Packet) : ℚ :=
  (∑ r, pressureQ r*p.center r)+∑ e, weightQ e*valueQ p e
def gradientQ (p : Packet) (r : Fin 9) : ℚ :=
  pressureQ r+∑ e, weightQ e*slopeQ p e*incidenceQ e r
def errorGradientQ (p : Packet) (r : Fin 9) : ℚ :=
  ∑ e, weightQ e*errorQ p e*incidenceQ e r
def paymentQ (p : Packet) : ℚ := ∑ r, errorGradientQ p r*p.radius r
def matrixQ (p : Packet) (s r : Fin 9) : ℚ :=
  ∑ e, weightQ e*(p.secondLower e/2)*incidenceQ e s*incidenceQ e r

theorem weightQ_cast (e : Fin 41) : (weightQ e:ℝ) = weight e := by
  exact (WindowValueFlow.weight_cast e).symm

theorem pressureQ_cast (r : Fin 9) :
    (pressureQ r:ℝ) = StructuralW10Followup20261016.NewLedger.W.b r := by
  unfold pressureQ
  push_cast
  exact WindowDirectionalFlow.pressure_cast r

theorem incidenceQ_cast (e : Fin 41) (r : Fin 9) :
    (incidenceQ e r:ℝ) = incidence e r := by
  simpa only [incidenceQ,Rat.cast_intCast] using WindowDirectionalFlow.incidence_cast e r

theorem F0Q_cast (p : Packet) :
    (F0Q p:ℝ) = WindowGramDiagonal.constant (realVector p.center) (WindowMomentEnergyCertificate.V p) := by
  unfold F0Q WindowGramDiagonal.constant pressure realVector
  push_cast
  simp_rw [pressureQ_cast,weightQ_cast]
  rfl

theorem gradientQ_cast (p : Packet) (r : Fin 9) :
    (gradientQ p r:ℝ) = WindowGramDiagonal.linear (WindowMomentEnergyCertificate.S p) r := by
  unfold gradientQ WindowGramDiagonal.linear
  push_cast
  simp_rw [pressureQ_cast,weightQ_cast,incidenceQ_cast]
  rfl

theorem paymentQ_cast (p : Packet) :
    (paymentQ p:ℝ) = WindowMomentEnergy.payment (WindowMomentEnergyCertificate.E p) (realVector p.radius) := by
  unfold paymentQ errorGradientQ WindowMomentEnergy.payment WindowMomentEnergy.errorGradient realVector
  push_cast
  simp_rw [weightQ_cast,incidenceQ_cast]
  rfl

def realMatrix (L : Fin 41 → ℝ) (s r : Fin 9) : ℝ :=
  ∑ e, weight e*(L e/2)*incidence e s*incidence e r

theorem matrixQ_cast (p : Packet) (s r : Fin 9) :
    (matrixQ p s r:ℝ) =
      realMatrix (fun e => (p.secondLower e:ℝ)) s r := by
  unfold matrixQ realMatrix
  push_cast
  simp_rw [weightQ_cast,incidenceQ_cast]

theorem realMatrix_span (L : Fin 41 → ℝ) (p g : Fin 9 → ℝ) :
    (∑ s, ∑ r, realMatrix L s r*(g s-p s)*(g r-p r)) =
      ∑ e, weight e*(L e/2)*(span g e-span p e)^2 := by
  unfold realMatrix
  simp_rw [Finset.sum_mul]
  have hcomm :
      (∑ s : Fin 9, ∑ r : Fin 9, ∑ e : Fin 41,
        weight e*(L e/2)*incidence e s*incidence e r*(g s-p s)*(g r-p r)) =
      ∑ e : Fin 41, ∑ s : Fin 9, ∑ r : Fin 9,
        weight e*(L e/2)*incidence e s*incidence e r*(g s-p s)*(g r-p r) := by
    have hi (s : Fin 9) :
        (∑ r : Fin 9, ∑ e : Fin 41,
          weight e*(L e/2)*incidence e s*incidence e r*(g s-p s)*(g r-p r)) =
        ∑ e : Fin 41, ∑ r : Fin 9,
          weight e*(L e/2)*incidence e s*incidence e r*(g s-p s)*(g r-p r) := Finset.sum_comm
    simp_rw [hi]
    rw [Finset.sum_comm]
  rw [hcomm]
  apply Finset.sum_congr rfl
  intro e _
  rw [WindowGramDiagonal.span_sub,pow_two]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem quadratic_eq_certificate (p : Packet) (g : Fin 9 → ℝ) :
    quadratic p.center (F0Q p) (gradientQ p) (paymentQ p) (matrixQ p) g =
      WindowMomentEnergyCertificate.polynomial p g := by
  have hm : matrixEval (matrixQ p) (fun r => g r-(p.center r:ℝ)) =
      ∑ e, weight e*((p.secondLower e:ℝ)/2)*
        (span g e-span (realVector p.center) e)^2 := by
    unfold matrixEval
    simp_rw [matrixQ_cast]
    exact realMatrix_span _ _ _
  unfold quadratic WindowMomentEnergyCertificate.polynomial WindowMomentEnergy.polynomial
  rw [F0Q_cast,paymentQ_cast,hm]
  have hg : dotQ (gradientQ p) (fun r => g r-(p.center r:ℝ)) =
      ∑ r, WindowGramDiagonal.linear (WindowMomentEnergyCertificate.S p) r*
        (g r-(p.center r:ℝ)) := by
    unfold dotQ
    simp_rw [gradientQ_cast]
  rw [hg]
  rfl

def energyForm (p : Packet) (layoutCenter layoutRadius : Fin 9 → ℚ) (target : ℚ) : RatForm :=
  form p.center layoutCenter layoutRadius (F0Q p) (gradientQ p) (paymentQ p) (matrixQ p) target

theorem energyForm_identity (p : Packet) (layoutCenter layoutRadius : Fin 9 → ℚ)
    (target : ℚ) (g : Fin 9 → ℝ) (hr : ∀ r, layoutRadius r ≠ 0) :
    eval (energyForm p layoutCenter layoutRadius target)
        (realVector layoutCenter) (realVector layoutRadius) g-
      ((energyForm p layoutCenter layoutRadius target).bound:ℝ) =
      WindowMomentEnergyCertificate.polynomial p g-(target:ℝ) := by
  unfold energyForm
  rw [form_identity _ _ _ _ _ _ _ _ _ hr,quadratic_eq_certificate]

theorem energyForm_sublevel {cell : DifferenceCell.Cell 10} {p : Packet}
    (hc : WindowMomentEnergyCertificate.check cell p = true)
    (layoutCenter layoutRadius : Fin 9 → ℚ) (target : ℚ)
    (hr : ∀ r, layoutRadius r ≠ 0) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g)
    (hbelow : WindowGapEnergy.Fw24 g < (target:ℝ)) :
    eval (energyForm p layoutCenter layoutRadius target)
        (realVector layoutCenter) (realVector layoutRadius) g <
      ((energyForm p layoutCenter layoutRadius target).bound:ℝ) := by
  have hsub := WindowMomentEnergyCertificate.sublevel hc hg hbelow
  have he := energyForm_identity p layoutCenter layoutRadius target g hr
  linarith only [hsub,he]

set_option pp.fullNames true
#print axioms cross_dot
#print axioms matrix_recenter
#print axioms moment_matrix
#print axioms form_identity
#print axioms F0Q_cast
#print axioms gradientQ_cast
#print axioms paymentQ_cast
#print axioms matrixQ_cast
#print axioms realMatrix_span
#print axioms quadratic_eq_certificate
#print axioms energyForm_identity
#print axioms energyForm_sublevel
end StructuralGoal20261016.WindowMomentEnergyPolynomial
end

