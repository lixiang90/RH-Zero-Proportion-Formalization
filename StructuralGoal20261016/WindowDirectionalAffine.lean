/- SPDX-License-Identifier: Apache-2.0
Actual 41-edge directional derivatives and their affine enclosures. Scalar
oracle inequalities are aggregated before a flow bound, preserving their
common gap coordinates. Interior-support directions vanish at actual
orthant minima; active lower faces are treated in the original orthant.
-/
import StructuralGoal20261016.WindowGramExpansion
import StructuralGoal20261016.WindowMinimizerCover
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Finset
open scoped BigOperators
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowDirectionalAffine
open WindowGapEnergy WindowGramTransfer
open StructuralW10Followup20261016.NewLedger (W)

theorem span_line (g d : Fin 9 → ℝ) (t : ℝ) (e : Fin 41) :
 span (line (n := 10) g d t) e = span g e+t*span d e := by
 simp only [span,ptsN_line]
 ring

theorem directional_eq (g d : Fin 9 → ℝ) :
 directional W g d = pressure d+
   ∑ e : Fin 41, weight e*span d e*w1 (span g e) := by
 have hp (r : Fin 9) : HasDerivAt
     (fun t : ℝ => W.b r*(line (n := 10) g d t) r) (W.b r*d r) 0 := by
   have hh := (((hasDerivAt_id (0:ℝ)).mul_const (d r)).const_add (g r)).const_mul (W.b r)
   convert hh using 1 <;> first | rfl | simp only [line,mul_one,one_mul,id_eq]
 have he (e : Fin 41) : HasDerivAt
     (fun t : ℝ => weight e*WindowKernel.w 24 WindowKernel.d24
       (span (line (n := 10) g d t) e))
     (weight e*span d e*w1 (span g e)) 0 := by
   have hs : HasDerivAt (fun t : ℝ => span (line (n := 10) g d t) e)
       (span d e) 0 :=
     (ptsN_line_hasDerivAt (n := 10) g d (pairJ e)).sub
       (ptsN_line_hasDerivAt (n := 10) g d (pairI e))
   have hw := (w_hasDerivAt (span (line (n := 10) g d 0) e)).comp 0 hs
   rw [line_zero] at hw
   exact (hw.const_mul (weight e)).congr_deriv (by ring)
 have hp' := HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hp r)
 have he' := HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => he e)
 have hh : HasDerivAt (fun t => Fw24 (line (n := 10) g d t))
     (pressure d+∑ e : Fin 41, weight e*span d e*w1 (span g e)) 0 := by
   have hfun : (fun t => Fw24 (line (n := 10) g d t)) =
       (fun t => pressure (line (n := 10) g d t)+∑ e : Fin 41,
         weight e*WindowKernel.w 24 WindowKernel.d24 (span (line (n := 10) g d t) e)) := by
     funext t
     exact actual_energy_expansion _
   rw [hfun]
   exact hp'.add he'
 exact (directional_hasDerivAt W g d).unique hh

def incidence (e : Fin 41) (r : Fin 9) : ℝ :=
 (if (r:ℕ) < (pairJ e:ℕ) then 1 else 0)-
   (if (r:ℕ) < (pairI e:ℕ) then 1 else 0)

theorem span_eq_sum (g : Fin 9 → ℝ) (e : Fin 41) :
 span g e = ∑ r, g r*incidence e r := by
 unfold span ptsN incidence
 rw [← Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro r _
 split_ifs <;> ring

def model (g d : Fin 9 → ℝ) (a b : Fin 41 → ℝ) : ℝ :=
 pressure d+∑ e : Fin 41, weight e*span d e*(a e+b e*span g e)
def intercept (d : Fin 9 → ℝ) (a : Fin 41 → ℝ) : ℝ :=
 pressure d+∑ e : Fin 41, weight e*span d e*a e
def coefficient (d : Fin 9 → ℝ) (b : Fin 41 → ℝ) (r : Fin 9) : ℝ :=
 ∑ e : Fin 41, weight e*span d e*b e*incidence e r
def error (d : Fin 9 → ℝ) (epsilon : Fin 41 → ℝ) : ℝ :=
 ∑ e : Fin 41, |weight e*span d e| * epsilon e

theorem model_eq (g d : Fin 9 → ℝ) (a b : Fin 41 → ℝ) :
 model g d a b = intercept d a+∑ r, coefficient d b r*g r := by
 simp only [model,intercept,coefficient,mul_add,Finset.sum_add_distrib,add_assoc]
 congr 1
 congr 1
 simp_rw [span_eq_sum g,Finset.mul_sum,Finset.sum_mul]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro r _
 apply Finset.sum_congr rfl
 intro e _
 ring

theorem enclosure (g d : Fin 9 → ℝ) (a b epsilon : Fin 41 → ℝ)
 (hscalar : ∀ e, |w1 (span g e)-(a e+b e*span g e)| ≤ epsilon e) :
 |directional W g d-(intercept d a+∑ r, coefficient d b r*g r)| ≤ error d epsilon := by
 rw [← model_eq]
 have he : directional W g d-model g d a b =
     ∑ e : Fin 41, (weight e*span d e)*(w1 (span g e)-(a e+b e*span g e)) := by
   rw [directional_eq]
   unfold model
   rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
   apply Finset.sum_congr rfl
   intro e _
   ring
 rw [he]
 apply (Finset.abs_sum_le_sum_abs _ _).trans
 apply Finset.sum_le_sum
 intro e _
 rw [abs_mul]
 exact mul_le_mul_of_nonneg_left (hscalar e) (abs_nonneg _)

theorem span_neg (d : Fin 9 → ℝ) (e : Fin 41) :
 span (fun r => -d r) e = -span d e := by
 rw [span_eq_sum,span_eq_sum,← Finset.sum_neg_distrib]
 apply Finset.sum_congr rfl
 intro r _
 ring

theorem directional_neg (g d : Fin 9 → ℝ) :
 directional W g (fun r => -d r) = -directional W g d := by
 rw [directional_eq,directional_eq]
 simp only [span_neg,pressure,mul_neg,neg_mul,Finset.sum_neg_distrib]
 ring

theorem zero_at_relevant {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g) (d : Fin 9 → ℝ)
 (hsupport : ∀ r, d r ≠ 0 → sep < g r) : directional W g d = 0 := by
 have hactive : ∀ r, g r = sep → d r = 0 := by
   intro r hr
   by_contra hn
   have hs := hsupport r hn
   linarith
 have hp := WindowMinimizerCover.directional_nonneg hg d (by
   intro r hr
   simpa only [hactive r hr] using (le_refl (0:ℝ)))
 have hn := WindowMinimizerCover.directional_nonneg hg (fun r => -d r) (by
   intro r hr
   rw [hactive r hr]
   norm_num)
 rw [directional_neg] at hn
 linarith

theorem exclude_relevant {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g) (d : Fin 9 → ℝ)
 (hfeasible : ∀ r, g r = sep → 0 ≤ d r)
 (a b epsilon : Fin 41 → ℝ)
 (hscalar : ∀ e, |w1 (span g e)-(a e+b e*span g e)| ≤ epsilon e)
 (hnegative : (intercept d a+∑ r, coefficient d b r*g r)+error d epsilon < 0) : False := by
 have hp := WindowMinimizerCover.directional_nonneg hg d hfeasible
 have he := (abs_le.mp (enclosure g d a b epsilon hscalar)).2
 linarith

set_option pp.fullNames true
#print axioms directional_eq
#print axioms span_eq_sum
#print axioms model_eq
#print axioms enclosure
#print axioms zero_at_relevant
#print axioms exclude_relevant
end StructuralGoal20261016.WindowDirectionalAffine
end
