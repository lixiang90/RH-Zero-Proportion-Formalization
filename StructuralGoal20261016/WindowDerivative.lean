/- SPDX-License-Identifier: Apache-2.0
Fourier moment derivatives for the actual finite cosine window.
Differentiation is justified under the integral by an integrable dominator;
the derivative chain and its bounds have no assumed differential identities.
-/
import StructuralGoal20261016.WindowKernel
import Mathlib.Analysis.Calculus.ParametricIntegral
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped BigOperators Topology
namespace StructuralGoal20261016.WindowDerivative
open WindowEnergy WindowKernel

def atom (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x t : ℝ) : ℝ :=
 v N d t * (2*π*t)^r * Real.cos (2*π*x*t + r*π/2)
def moment (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
 ∫ t in (-(1:ℝ)/2)..(1/2), atom N d r x t
def jet (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
 moment N d r x / AMW.K0AM

theorem atom_continuous (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 Continuous (atom N d r x) := by
 unfold atom
 exact ((v_continuous N d).mul (by fun_prop)).mul (by fun_prop)

theorem atom_hasDerivAt (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x t : ℝ) :
 HasDerivAt (fun y => atom N d r y t) (atom N d (r+1) x t) x := by
 have hlin : HasDerivAt (fun y : ℝ => 2*π*y*t + r*π/2) (2*π*t) x := by
   convert (((hasDerivAt_id x).const_mul (2*π)).mul_const t).add_const (r*π/2) using 1 <;>
     first | rfl | simp only [id_eq, mul_one] | ring
 have h := ((Real.hasDerivAt_cos _).comp x hlin).const_mul (v N d t * (2*π*t)^r)
 refine h.congr_deriv ?_
 unfold atom
 have he : 2*π*x*t + ((r+1 : ℕ) : ℝ)*π/2 =
   (2*π*x*t + (r : ℝ)*π/2) + π/2 := by push_cast; ring
 rw [he, Real.cos_add_pi_div_two, pow_succ]
 ring

theorem moment_hasDerivAt (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 HasDerivAt (moment N d r) (moment N d (r+1) x) x := by
 let μ := volume.restrict (Ioc (-(1:ℝ)/2) (1/2))
 have hcont (y : ℝ) := atom_continuous N d r y
 have hcont' (y : ℝ) := atom_continuous N d (r+1) y
 have hbcont : Continuous (fun t => |v N d t| * |2*π*t|^(r+1)) :=
   (v_continuous N d).abs.mul (by fun_prop)
 have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (μ := μ) (s := Set.univ) (F := fun y t => atom N d r y t)
   (F' := fun y t => atom N d (r+1) y t)
   (bound := fun t => |v N d t| * |2*π*t|^(r+1))
   (show Set.univ ∈ 𝓝 x from Filter.univ_mem)
   (Filter.Eventually.of_forall fun y => (hcont y).aestronglyMeasurable)
   ((hcont x).intervalIntegrable (-(1:ℝ)/2) (1/2)).1
   ((hcont' x).aestronglyMeasurable)
   (ae_of_all μ fun t y _ => by
     rw [Real.norm_eq_abs, atom, abs_mul, abs_mul, abs_pow]
     exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))
   (hbcont.intervalIntegrable (-(1:ℝ)/2) (1/2)).1
   (ae_of_all μ fun t y _ => atom_hasDerivAt N d r y t)
 have he (y : ℝ) (q : ℕ) :
     (∫ t, atom N d q y t ∂μ) = moment N d q y := by
   unfold moment μ
   rw [intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ 1/2)]
 have hef : (fun y => ∫ t, atom N d r y t ∂μ) = moment N d r := funext fun y => he y r
 rw [hef, he x (r+1)] at h
 exact h.2

theorem jet_hasDerivAt (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 HasDerivAt (jet N d r) (jet N d (r+1) x) x :=
 (moment_hasDerivAt N d r x).div_const AMW.K0AM

theorem moment_zero_eq (N : ℕ) (d : ℕ → ℝ) : moment N d 0 = K N d := by
 funext x
 simp only [moment, atom, K, pow_zero, mul_one, Nat.cast_zero, zero_mul,
   zero_div, add_zero]

theorem jet_zero_eq (N : ℕ) (d : ℕ → ℝ) : jet N d 0 = k N d := by
 funext x
 unfold jet k
 rw [moment_zero_eq, K_zero]
 rfl

theorem moment_abs_le (N : ℕ) (d : ℕ → ℝ)
 (hpos : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v N d t) (r : ℕ) (x : ℝ) :
 |moment N d r x| ≤ π^r * AMW.K0AM := by
 have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
 have hpt : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2),
     |atom N d r x t| ≤ π^r * v N d t := by
   intro t ht
   have hv := hpos t ht
   have htbound : |2*π*t| ≤ π := by
     have htab : |t| ≤ (1:ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
     rw [abs_mul, abs_of_pos (by positivity : 0 < 2*π)]
     nlinarith [pi_pos]
   rw [atom, abs_mul, abs_mul, abs_pow, abs_of_nonneg (hpos t ht)]
   calc
     _ ≤ v N d t * |2*π*t|^r * 1 :=
       mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
     _ ≤ π^r * v N d t := by
       rw [mul_one, mul_comm (π^r)]
       exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htbound r) (hpos t ht)
 unfold moment
 calc
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |atom N d r x t| :=
     intervalIntegral.abs_integral_le_integral_abs hab
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), π^r * v N d t :=
     intervalIntegral.integral_mono_on hab
       ((atom_continuous N d r x).abs.intervalIntegrable _ _)
       ((continuous_const.mul (v_continuous N d)).intervalIntegrable _ _) hpt
   _ = _ := by
     rw [intervalIntegral.integral_const_mul, WindowEnergy.integral_v]
     rfl

theorem jet_abs_le (N : ℕ) (d : ℕ → ℝ)
 (hpos : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v N d t) (r : ℕ) (x : ℝ) :
 |jet N d r x| ≤ π^r := by
 rw [jet, abs_div, abs_of_pos AMW.K0AM_pos,
   div_le_iff₀ AMW.K0AM_pos]
 exact moment_abs_le N d hpos r x

theorem jet24_abs_le (r : ℕ) (x : ℝ) : |jet 24 d24 r x| ≤ π^r :=
 jet_abs_le 24 d24 v24_nonneg r x

theorem k24_hasDerivAt (x : ℝ) :
 HasDerivAt (k 24 d24) (jet 24 d24 1 x) x := by
 rw [← jet_zero_eq 24 d24]
 exact jet_hasDerivAt 24 d24 0 x

theorem v24_le (t : ℝ) : v 24 d24 t ≤ 27/25 := by
 rw [v24_eq]
 have hp := StructuralW10Followup20261016.WindowProfileGeneral.abs_perturb_le _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 t
 have hc := Real.cos_le_one (Real.sqrt 2*t)
 unfold StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
 linarith only [(abs_le.mp hp).2, hc]

theorem moment24_two_abs_le (x : ℝ) :
 |moment 24 d24 2 x| ≤ (9/25)*π^2 := by
 have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
 have hpoly : (∫ t in (-(1:ℝ)/2)..(1/2), t^2) = (1:ℝ)/12 := by
   have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
     (a := (-(1:ℝ)/2)) (b := (1:ℝ)/2)
     (f := fun t : ℝ => t^3/3) (f' := fun t : ℝ => t^2)
     (fun t _ => ((hasDerivAt_pow 3 t).div_const 3).congr_deriv (by norm_num))
     ((by fun_prop : Continuous (fun t : ℝ => t^2)).intervalIntegrable _ _)
   norm_num at h ⊢
 have hpt : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2),
   |atom 24 d24 2 x t| ≤ ((27/25)*(2*π)^2) * t^2 := by
   intro t ht
   have hv := v24_nonneg t ht
   rw [atom, abs_mul, abs_mul, abs_pow, abs_of_nonneg (v24_nonneg t ht)]
   have hs : |2*π*t|^2 = (2*π)^2*t^2 := by rw [sq_abs, mul_pow]
   rw [hs]
   calc
     _ ≤ v 24 d24 t * ((2*π)^2*t^2) * 1 :=
       mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
     _ ≤ ((27/25)*(2*π)^2)*t^2 := by
       rw [mul_one]
       nlinarith [mul_le_mul_of_nonneg_right (v24_le t)
         (show 0 ≤ (2*π)^2*t^2 by positivity)]
 unfold moment
 calc
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |atom 24 d24 2 x t| :=
     intervalIntegral.abs_integral_le_integral_abs hab
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), ((27/25)*(2*π)^2)*t^2 :=
     intervalIntegral.integral_mono_on hab
       ((atom_continuous 24 d24 2 x).abs.intervalIntegrable _ _)
       ((by fun_prop : Continuous _).intervalIntegrable _ _) hpt
   _ = _ := by rw [intervalIntegral.integral_const_mul, hpoly]; ring

theorem jet24_two_abs_le (x : ℝ) : |jet 24 d24 2 x| ≤ 4 := by
 rw [jet, abs_div, abs_of_pos AMW.K0AM_pos, div_le_iff₀ AMW.K0AM_pos]
 have hrho := Opeth.AMMajorant.rho_le
 change 1 / AMW.K0AM ≤ (109/100 : ℝ) at hrho
 rw [div_le_iff₀ AMW.K0AM_pos] at hrho
 have hp := Real.pi_lt_d2
 have hp2 := pow_le_pow_left₀ Real.pi_pos.le hp.le 2
 exact (moment24_two_abs_le x).trans (by nlinarith)

#print axioms moment_hasDerivAt
#print axioms jet_hasDerivAt
#print axioms jet_zero_eq
#print axioms jet24_abs_le
#print axioms jet24_two_abs_le
end StructuralGoal20261016.WindowDerivative
end
