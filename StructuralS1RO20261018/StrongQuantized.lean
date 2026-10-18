/- SPDX-License-Identifier: Apache-2.0
Current s1R strong tangent remainder and the original quantized anchor line.
Curvature is assumed only on the explicitly stated anchor-to-span hull.
-/
import StructuralS1RO20261018.CellAQuantitative
import StructuralS1RM20261018.PhaseA1.QuantizedComponent
import Mathlib.Analysis.Convex.Deriv
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Set AMW.Cert AMW.Cert.PyrD AMW.Cert.PCell
open StructuralS1RM20261018.QuantizedComponent
namespace StructuralS1RO20261018.StrongQuantized

/-- The true first-order tangent dominates the original asymmetric
derivative quantization. In particular the original L0 is not changed. -/
theorem ell_le_true_tangent {f : ℕ → ℕ} {L0 L U p : ℕ}
    (ht : TVal f L U p) (hL0 : L0 ≤ L) (s : ℝ)
    (hs1 : (L : ℝ)/SC ≤ s) (hs2 : s ≤ (U : ℝ)/SC) :
    ell f L0 p s ≤ wfun ((p : ℝ)/SC) +
      w1 ((p : ℝ)/SC) * (s - (p : ℝ)/SC) := by
  obtain ⟨hLp, hpU, hlo, hhi, htan⟩ := ht
  have hqL : (L : ℝ)/SC ≤ (p : ℝ)/SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hLp) (by norm_num [SC])
  have hqU : (p : ℝ)/SC ≤ (U : ℝ)/SC :=
    div_le_div_of_nonneg_right (by exact_mod_cast hpU) (by norm_num [SC])
  have hv := htan ((p : ℝ)/SC) hqL hqU
  simp only [sub_self, mul_zero, add_zero] at hv
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  rw [hSC] at hs1 hlo hhi hv ⊢
  have hs : 0 ≤ s - (L0 : ℝ)/32768 := by
    have h : (L0 : ℝ)/32768 ≤ (L : ℝ)/32768 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hL0) (by norm_num)
    linarith
  have hp : 0 ≤ (p : ℝ)/32768 - (L0 : ℝ)/32768 := by
    have h : (L0 : ℝ) ≤ p := by exact_mod_cast hL0.trans hLp
    linarith
  have hl : 0 ≤ w1 ((p : ℝ)/32768) -
      ((lo32 (hi32 (f p)) : ℝ)-2000000000)/1000000000 := by linarith
  have hu : 0 ≤ (2000000000-(hi32 (hi32 (f p)) : ℝ))/1000000000 -
      w1 ((p : ℝ)/32768) := by linarith
  have h1 := mul_nonneg hl hs
  have h2 := mul_nonneg hu hp
  unfold ell
  nlinarith only [hv, h1, h2]

/-- Actual current w and w1 are globally differentiable. Convexity is
proved only for w(t)-m*(t-q)^2/2 on the given closed segment. -/
theorem strong_tangent (q s m : ℝ)
    (hsecond : ∀ y ∈ uIcc q s, m ≤ w2 y) :
    wfun q + w1 q*(s-q) + (m/2)*(s-q)^2 ≤ wfun s := by
  let H : ℝ → ℝ := fun y => wfun y - (m/2)*(y-q)^2
  let H1 : ℝ → ℝ := fun y => w1 y - m*(y-q)
  have hd (x : ℝ) : HasDerivAt H (H1 x) x := by
    change HasDerivAt (fun y : ℝ => wfun y-(m/2)*(y-q)^2)
      (w1 x-m*(x-q)) x
    have hw := hasDerivAt_wfun x (kD_neg x).ne
    have hquad := (((hasDerivAt_id x).sub_const q).pow 2).const_mul (m/2)
    convert hw.sub hquad using 1 <;> ring
  have hd1 (x : ℝ) : HasDerivAt H1 (w2 x-m) x := by
    change HasDerivAt (fun y : ℝ => w1 y-m*(y-q)) (w2 x-m) x
    have hw := hasDerivAt_w1 x (kD_neg x).ne
    have hlin := ((hasDerivAt_id x).sub_const q).const_mul m
    convert hw.sub hlin using 1 <;> ring
  have hc : ConvexOn ℝ (uIcc q s) H :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_uIcc q s)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x _ => (hd1 x).hasDerivWithinAt)
      (fun x hx => sub_nonneg.mpr (hsecond x (interior_subset hx)))
  rcases lt_trichotomy q s with hqs | heq | hsq
  · have h := hc.le_slope_of_hasDerivAt left_mem_uIcc right_mem_uIcc hqs (hd q)
    rw [slope_def_field] at h
    have ht := (le_div_iff₀ (sub_pos.mpr hqs)).mp h
    dsimp [H, H1] at ht
    nlinarith only [ht]
  · subst s
    simp
  · have h := hc.slope_le_of_hasDerivAt right_mem_uIcc left_mem_uIcc hsq (hd q)
    rw [slope_def_field] at h
    have ht := (div_le_iff₀ (sub_pos.mpr hsq)).mp h
    dsimp [H, H1] at ht
    nlinarith only [ht]

/-- A finite packet must cover hull(q,I), not just the feasible interval I.
The original tangent interval and the original L0 remain explicit. -/
theorem ell_strong_hull {f : ℕ → ℕ} {L0 L U p : ℕ} {a b m : ℝ}
    (ht : TVal f L U p) (hL0 : L0 ≤ L) (hm : 0 ≤ m)
    (hsecond : ∀ y ∈ Icc (min ((p : ℝ)/SC) a) (max ((p : ℝ)/SC) b), m ≤ w2 y)
    (s : ℝ) (hs : s ∈ Icc a b)
    (hs1 : (L : ℝ)/SC ≤ s) (hs2 : s ≤ (U : ℝ)/SC) :
    ell f L0 p s + (m/2)*(s-(p : ℝ)/SC)^2 ≤ wfun s := by
  have hsegment : ∀ y ∈ uIcc ((p : ℝ)/SC) s, m ≤ w2 y := by
    intro y hy
    apply hsecond y
    have hq1 := min_le_left ((p : ℝ)/SC) a
    have hq2 := le_max_left ((p : ℝ)/SC) b
    have hsL := (min_le_right ((p : ℝ)/SC) a).trans hs.1
    have hsU := hs.2.trans (le_max_right ((p : ℝ)/SC) b)
    rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith
  have htangent := strong_tangent ((p : ℝ)/SC) s m hsegment
  have hquant := ell_le_true_tangent ht hL0 s hs1 hs2
  linarith only [htangent, hquant]

theorem scaled_strong_hull {f : ℕ → ℕ} {L0 L U p : ℕ} {a b m : ℝ}
    (ht : TVal f L U p) (hL0 : L0 ≤ L) (hm : 0 ≤ m)
    (hsecond : ∀ y ∈ Icc (min ((p : ℝ)/SC) a) (max ((p : ℝ)/SC) b), m ≤ w2 y)
    (s : ℝ) (hs : s ∈ Icc a b)
    (hs1 : (L : ℝ)/SC ≤ s) (hs2 : s ≤ (U : ℝ)/SC) :
    (slope f p : ℝ)*(20*32768*s) + (intercept f L0 p : ℝ) +
      ((kappa : ℝ)*m/2)*(s-(p : ℝ)/SC)^2 ≤ (kappa : ℝ)*wfun s := by
  have h := mul_le_mul_of_nonneg_left (ell_strong_hull ht hL0 hm hsecond s hs hs1 hs2)
    (show (0 : ℝ) ≤ kappa by norm_num [kappa])
  have he : (slope f p : ℝ)*(20*32768*s)+(intercept f L0 p : ℝ) =
      (kappa : ℝ)*ell f L0 p s := by
    unfold slope intercept dLo dHi ell kappa
    push_cast
    ring
  calc
    _ = (kappa : ℝ)*(ell f L0 p s+(m/2)*(s-(p : ℝ)/SC)^2) := by rw [he]; ring
    _ ≤ (kappa : ℝ)*wfun s := h

set_option pp.fullNames true
#print axioms ell_le_true_tangent
#print axioms strong_tangent
#print axioms ell_strong_hull
#print axioms scaled_strong_hull
end StructuralS1RO20261018.StrongQuantized
end
