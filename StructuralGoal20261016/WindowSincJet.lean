/- SPDX-License-Identifier: Apache-2.0
Actual finite sinc-jet formula, including every removable pole.
The auxiliary sinc moments are integrals, with differentiation under the
integral and an exact integration-by-parts recurrence proved below.
-/
import StructuralGoal20261016.WindowTaylorBridge
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped BigOperators Topology
namespace StructuralGoal20261016.WindowSincJet
open WindowKernel WindowDerivative WindowTaylorBridge

def sincAtom (r : ℕ) (z t : ℝ) : ℝ :=
 t^r * Real.cos (z*t+r*π/2)

def sincMoment (r : ℕ) (z : ℝ) : ℝ := ∫ t in (0:ℝ)..1, sincAtom r z t

theorem sincAtom_continuous (r : ℕ) (z : ℝ) : Continuous (sincAtom r z) := by
 unfold sincAtom
 fun_prop

theorem sincAtom_hasDerivAt (r : ℕ) (z t : ℝ) :
 HasDerivAt (fun y => sincAtom r y t) (sincAtom (r+1) z t) z := by
 have hlin : HasDerivAt (fun y : ℝ => y*t+r*π/2) t z := by
   convert ((hasDerivAt_id z).mul_const t).add_const (r*π/2) using 1 <;>
     first | rfl | simp only [id_eq, one_mul] | ring
 have h := ((Real.hasDerivAt_cos _).comp z hlin).const_mul (t^r)
 refine h.congr_deriv ?_
 unfold sincAtom
 have he : z*t+((r+1 : ℕ):ℝ)*π/2 = (z*t+(r:ℝ)*π/2)+π/2 := by
   push_cast
   ring
 rw [he, Real.cos_add_pi_div_two, pow_succ]
 ring

theorem sincMoment_hasDerivAt (r : ℕ) (z : ℝ) :
 HasDerivAt (sincMoment r) (sincMoment (r+1) z) z := by
 let μ := volume.restrict (Ioc (0:ℝ) 1)
 have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (μ := μ) (s := Set.univ) (F := fun y t => sincAtom r y t)
   (F' := fun y t => sincAtom (r+1) y t) (bound := fun t => |t|^(r+1))
   (show Set.univ ∈ 𝓝 z from Filter.univ_mem)
   (Filter.Eventually.of_forall fun y => (sincAtom_continuous r y).aestronglyMeasurable)
   ((sincAtom_continuous r z).intervalIntegrable 0 1).1
   ((sincAtom_continuous (r+1) z).aestronglyMeasurable)
   (ae_of_all μ fun t y _ => by
     rw [Real.norm_eq_abs, sincAtom, abs_mul, abs_pow]
     exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
   ((by fun_prop : Continuous (fun t : ℝ => |t|^(r+1))).intervalIntegrable 0 1).1
   (ae_of_all μ fun t y _ => sincAtom_hasDerivAt r y t)
 have he (y : ℝ) (q : ℕ) : (∫ t, sincAtom q y t ∂μ) = sincMoment q y := by
   unfold sincMoment μ
   rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
 have hef : (fun y => ∫ t, sincAtom r y t ∂μ) = sincMoment r := funext fun y => he y r
 rw [hef, he z (r+1)] at h
 exact h.2

theorem sincMoment_zero_order (z : ℝ) : sincMoment 0 z = Real.sinc z := by
 unfold sincMoment sincAtom
 simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, zero_div, add_zero]
 by_cases hz : z = 0
 · subst z
   norm_num
 · rw [intervalIntegral.integral_comp_mul_left _ hz, integral_cos,
     Real.sinc_of_ne_zero hz]
   simp only [mul_one, mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
   ring

theorem sincMoment_recurrence (r : ℕ) (z : ℝ) :
 Real.cos (z+(r:ℝ)*π/2) = (r+1:ℕ)*sincMoment r z+z*sincMoment (r+1) z := by
 have hd (t : ℝ) : HasDerivAt
     (fun t : ℝ => t^(r+1)*Real.cos (z*t+r*π/2))
     ((r+1:ℕ)*sincAtom r z t+z*sincAtom (r+1) z t) t := by
   have hl : HasDerivAt (fun t : ℝ => z*t+r*π/2) z t := by
     convert ((hasDerivAt_id t).const_mul z).add_const (r*π/2) using 1 <;>
       first | rfl | simp only [id_eq, mul_one] | ring
   have h := (hasDerivAt_pow (r+1) t).mul ((Real.hasDerivAt_cos _).comp t hl)
   refine h.congr_deriv ?_
   unfold sincAtom
   have he : z*t+((r+1:ℕ):ℝ)*π/2 = (z*t+(r:ℝ)*π/2)+π/2 := by
     push_cast
     ring
   rw [he, Real.cos_add_pi_div_two]
   simp only [Nat.add_sub_cancel, Function.comp_apply]
   push_cast
   ring
 have hi : IntervalIntegrable
     (fun t : ℝ => (r+1:ℕ)*sincAtom r z t+z*sincAtom (r+1) z t) volume 0 1 :=
   ((continuous_const.mul (sincAtom_continuous r z)).add
     (continuous_const.mul (sincAtom_continuous (r+1) z))).intervalIntegrable _ _
 have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
   (a := (0:ℝ)) (b := 1) (fun t _ => hd t) hi
 have hi0 : IntervalIntegrable (fun t : ℝ => ((r+1:ℕ):ℝ)*sincAtom r z t) volume 0 1 :=
   (continuous_const.mul (sincAtom_continuous r z)).intervalIntegrable _ _
 have hi1 : IntervalIntegrable (fun t : ℝ => z*sincAtom (r+1) z t) volume 0 1 :=
   (continuous_const.mul (sincAtom_continuous (r+1) z)).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hi0 hi1,
   intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
 simpa only [sincMoment, one_pow, one_mul, mul_one, zero_pow (Nat.succ_ne_zero r),
   zero_mul, mul_zero, zero_add, sub_zero] using h.symm

theorem sincMoment_succ {z : ℝ} (hz : z ≠ 0) (r : ℕ) :
 sincMoment (r+1) z =
   (Real.cos (z+(r:ℝ)*π/2)-(r+1:ℕ)*sincMoment r z)/z := by
 apply (eq_div_iff hz).2
 nlinarith only [sincMoment_recurrence r z]

theorem sincMoment_at_zero (r : ℕ) :
 sincMoment r 0 = Real.cos ((r:ℝ)*π/2)/(r+1:ℕ) := by
 have h := sincMoment_recurrence r 0
 simp only [zero_add, zero_mul, add_zero] at h
 apply (eq_div_iff (by positivity : ((r+1:ℕ):ℝ) ≠ 0)).2
 nlinarith only [h]

def rawJet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
 (sincMoment r (π*x-Real.sqrt 2/2)+sincMoment r (π*x+Real.sqrt 2/2)+
   ∑ j ∈ Finset.range N, d j*(sincMoment r (π*x-π*((j:ℝ)+1))+
     sincMoment r (π*x+π*((j:ℝ)+1))))/2

def finiteJet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
 π^r*rawJet N d r x/AMW.K0AM

theorem rawJet_zero_order (N : ℕ) (d : ℕ → ℝ) (x : ℝ) :
 rawJet N d 0 x = K N d x := by
 rw [K_eq_sinc]
 unfold rawJet AMW.KMT
 simp_rw [sincMoment_zero_order]
 rw [show (Real.sqrt 2-2*π*x)/2 = -(π*x-Real.sqrt 2/2) by ring,
   show (Real.sqrt 2+2*π*x)/2 = π*x+Real.sqrt 2/2 by ring, Real.sinc_neg]
 have he : ∀ j : ℕ, d j*(Real.sinc (π*x-π*((j:ℝ)+1))+
     Real.sinc (π*x+π*((j:ℝ)+1))) =
   2*(d j*((Real.sinc (π*(x-((j:ℝ)+1)))+Real.sinc (π*(x+((j:ℝ)+1))))/2)) := by
   intro j
   rw [mul_sub, mul_add]
   ring
 simp_rw [he]
 rw [← Finset.mul_sum]
 ring

theorem rawJet_hasDerivAt (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 HasDerivAt (rawJet N d r) (π*rawJet N d (r+1) x) x := by
 have ha (a : ℝ) : HasDerivAt (fun y : ℝ => sincMoment r (π*y+a))
     (π*sincMoment (r+1) (π*x+a)) x := by
   have hl : HasDerivAt (fun y : ℝ => π*y+a) π x := by
     convert ((hasDerivAt_id x).const_mul π).add_const a using 1 <;>
       first | rfl | simp only [id_eq, mul_one]
   exact ((sincMoment_hasDerivAt r (π*x+a)).comp x hl).congr_deriv
     (show sincMoment (r+1) (π*x+a)*π = π*sincMoment (r+1) (π*x+a) by ring)
 have hs : ∀ j ∈ Finset.range N, HasDerivAt
     (fun y : ℝ => d j*(sincMoment r (π*y-π*((j:ℝ)+1))+
       sincMoment r (π*y+π*((j:ℝ)+1))))
     (d j*(π*sincMoment (r+1) (π*x-π*((j:ℝ)+1))+
       π*sincMoment (r+1) (π*x+π*((j:ℝ)+1)))) x := by
   intro j _
   simpa only [sub_eq_add_neg, neg_mul, Pi.add_apply] using
     ((ha (-π*((j:ℝ)+1))).add (ha (π*((j:ℝ)+1)))).const_mul (d j)
 have hb := ((ha (-Real.sqrt 2/2)).add (ha (Real.sqrt 2/2))).add
   (HasDerivAt.fun_sum hs)
 have hb' := hb.div_const 2
 have hsumeq : (∑ j ∈ Finset.range N, d j*
     (π*sincMoment (r+1) (π*x-π*((j:ℝ)+1))+
       π*sincMoment (r+1) (π*x+π*((j:ℝ)+1)))) =
   π*∑ j ∈ Finset.range N, d j*(sincMoment (r+1) (π*x-π*((j:ℝ)+1))+
     sincMoment (r+1) (π*x+π*((j:ℝ)+1))) := by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j _
   ring
 have he : (π*sincMoment (r+1) (π*x+-Real.sqrt 2/2)+
     π*sincMoment (r+1) (π*x+Real.sqrt 2/2)+
     ∑ j ∈ Finset.range N, d j*(π*sincMoment (r+1) (π*x-π*((j:ℝ)+1))+
       π*sincMoment (r+1) (π*x+π*((j:ℝ)+1))))/2 = π*rawJet N d (r+1) x := by
   rw [hsumeq]
   unfold rawJet
   simp only [neg_div, ← sub_eq_add_neg]
   ring
 have hp := hb'.congr_deriv he
 convert hp using 1 <;>
   first | rfl | (funext y; simp only [rawJet, Pi.add_apply, sub_eq_add_neg, neg_div])

theorem finiteJet_hasDerivAt (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 HasDerivAt (finiteJet N d r) (finiteJet N d (r+1) x) x := by
 have h := ((rawJet_hasDerivAt N d r x).const_mul (π^r)).div_const AMW.K0AM
 refine h.congr_deriv ?_
 unfold finiteJet
 rw [pow_succ]
 ring

theorem finiteJet_eq_jet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) :
 finiteJet N d r = jet N d r := by
 induction r with
 | zero =>
   funext x
   rw [finiteJet, pow_zero, one_mul, rawJet_zero_order]
   rw [jet_zero_eq]
   unfold k
   rw [K_zero]
   rfl
 | succ r ih =>
   funext x
   have h := finiteJet_hasDerivAt N d r x
   rw [ih] at h
   exact h.deriv.symm.trans (jet_hasDerivAt N d r x).deriv

theorem iterated_k_eq_finiteJet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) :
 iteratedDeriv r (k N d) = finiteJet N d r := by
 rw [iterated_k_eq_jet, finiteJet_eq_jet]

#print axioms sincMoment_recurrence
#print axioms sincMoment_at_zero
#print axioms iterated_k_eq_finiteJet
end StructuralGoal20261016.WindowSincJet
end
