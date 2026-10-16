/- SPDX-License-Identifier: Apache-2.0
Actual second variation of the new 24-mode energy. A negative curvature
direction supported in the interior of the original orthant excludes a
genuine global minimizer, even when first-order KKT equations hold.
-/
import StructuralGoal20261016.WindowKKTInstance
import StructuralGoal20261016.WindowConvexityCertificate
import Mathlib.Analysis.Calculus.DerivativeTest
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Set Filter Finset
open scoped Topology BigOperators
open Zeta23Ext.Bridge
open Zeta23Ext.BridgeW (WCert)

namespace StructuralGoal20261016.WindowSecondVariation
open WindowGapEnergy WindowKernel WindowDerivative

theorem deriv2_nonneg_of_local_min {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra h
  have hn : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hx := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hx] with y hmy hxy
    exact le_antisymm hxy hmy
  have hz : deriv (deriv f) x = 0 := by
    simpa using he.deriv.deriv_eq
  exact (ne_of_lt hn) hz

def w2 (x : ℝ) : ℝ :=
  2 * (jet 24 d24 1 x)^2 + 2 * k 24 d24 x * jet 24 d24 2 x

theorem w1_hasDerivAt (x : ℝ) : HasDerivAt w1 (w2 x) x := by
  have h := ((k24_hasDerivAt x).const_mul 2).mul (jet_hasDerivAt 24 d24 1 x)
  convert h using 1 <;> first | rfl | simp only [w1, w2] <;> ring

theorem w2_eq_actual (x : ℝ) :
    w2 x = iteratedDeriv 2 (w 24 d24) x := by
  rw [WindowTaylorBridge.iterated_w_eq]
  norm_num [Finset.sum_range_succ, ← jet_zero_eq, w2]
  ring

variable {n : ℕ}

def curvature (W : WCert n) (g v : Fin (n-1) → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) then
      W.a i j * w2 (ptsN n g j - ptsN n g i) *
        (ptsN n v j - ptsN n v i)^2 else 0

theorem directional_hasDerivAt_at (W : WCert n) (g v : Fin (n-1) → ℝ) (t : ℝ) :
    HasDerivAt (fun u => Fw W (line g v u))
      (directional W (line g v t) v) t := by
  have ho : HasDerivAt (fun u => Fw W (line (line g v t) v u))
      (directional W (line g v t) v) (t-t) := by
    simpa only [sub_self] using directional_hasDerivAt W (line g v t) v
  have hi : HasDerivAt (fun u : ℝ => u-t) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const t
  have hh := ho.comp (h := fun u : ℝ => u-t) t hi
  have he : ((fun u => Fw W (line (line g v t) v u)) ∘ (fun u : ℝ => u-t)) =
      (fun u => Fw W (line g v u)) := by
    funext u
    simp only [Function.comp_apply]
    congr 1
    funext r
    unfold line
    ring
  rw [he] at hh
  convert hh using 1 <;> first | rfl | simp only [mul_one]

theorem curvature_hasDerivAt (W : WCert n) (g v : Fin (n-1) → ℝ) :
    HasDerivAt (fun t => directional W (line g v t) v) (curvature W g v) 0 := by
  classical
  have hp (i j : Fin n) : HasDerivAt
      (fun t => if (i : ℕ) < (j : ℕ) then
        W.a i j * w1 (ptsN n (line g v t) j - ptsN n (line g v t) i) *
          (ptsN n v j - ptsN n v i) else 0)
      (if (i : ℕ) < (j : ℕ) then
        W.a i j * w2 (ptsN n g j - ptsN n g i) *
          (ptsN n v j - ptsN n v i)^2 else 0) 0 := by
    by_cases hij : (i : ℕ) < (j : ℕ)
    · simp only [if_pos hij]
      have hs := (ptsN_line_hasDerivAt g v j).sub (ptsN_line_hasDerivAt g v i)
      have hw := (w1_hasDerivAt
        (ptsN n (line g v 0) j - ptsN n (line g v 0) i)).comp 0 hs
      rw [line_zero] at hw
      exact ((hw.const_mul (W.a i j)).mul_const
        (ptsN n v j - ptsN n v i)).congr_deriv (by ring)
    · simp only [if_neg hij]
      exact hasDerivAt_const 0 0
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hp i j))
  have h := hs.const_add (∑ r, W.b r * v r)
  convert h using 1 <;> first | rfl | simp only [directional, curvature]

theorem curvature_eq_second_deriv (W : WCert n) (g v : Fin (n-1) → ℝ) :
    curvature W g v = deriv (deriv (fun t => Fw W (line g v t))) 0 := by
  have he : deriv (fun t => Fw W (line g v t)) =
      (fun t => directional W (line g v t) v) :=
    funext fun t => (directional_hasDerivAt_at W g v t).deriv
  rw [he]
  exact (curvature_hasDerivAt W g v).deriv.symm

/-- Support must be strictly inside the original separated orthant. A cell's
artificial boundary is not a feasible-domain boundary. -/
theorem curvature_nonneg_at_min (W : WCert n) {sep : ℝ}
    (g v : Fin (n-1) → ℝ) (hg : CoverCoerciveKKT.Orthant sep g)
    (hmin : ∀ y, CoverCoerciveKKT.Orthant sep y → Fw W g ≤ Fw W y)
    (hsupport : ∀ r, v r ≠ 0 → sep < g r) : 0 ≤ curvature W g v := by
  have hcoord (r : Fin (n-1)) :
      ∀ᶠ t in 𝓝 (0 : ℝ), sep ≤ (line g v t) r := by
    by_cases hv : v r = 0
    · exact Filter.Eventually.of_forall (fun t => by simpa [line, hv] using hg r)
    · have hc : Continuous (fun t : ℝ => g r + t*v r) := by fun_prop
      have he : ∀ᶠ t in 𝓝 (0 : ℝ), sep < g r+t*v r :=
        (isOpen_Ioi.preimage hc).mem_nhds (by simpa using hsupport r hv)
      exact he.mono (fun t ht => ht.le)
  have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), CoverCoerciveKKT.Orthant sep (line g v t) :=
    Filter.eventually_all.mpr hcoord
  have hm : IsLocalMin (fun t => Fw W (line g v t)) 0 := by
    filter_upwards [hfeas] with t ht
    simpa only [line_zero] using hmin (line g v t) ht
  have hc : ContinuousAt (fun t => Fw W (line g v t)) 0 :=
    (directional_hasDerivAt W g v).continuousAt
  rw [curvature_eq_second_deriv]
  exact deriv2_nonneg_of_local_min hm hc

theorem curvature_nonneg_of_relevant {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant sep g) (v : Fin 9 → ℝ)
    (hsupport : ∀ r, v r ≠ 0 → sep < g r) :
    0 ≤ curvature StructuralW10Followup20261016.NewLedger.W g v :=
  curvature_nonneg_at_min (n := 10)
    StructuralW10Followup20261016.NewLedger.W g v hg.1 hg.2.2 hsupport

set_option pp.fullNames true
#print axioms deriv2_nonneg_of_local_min
#print axioms w2_eq_actual
#print axioms curvature_eq_second_deriv
#print axioms curvature_nonneg_at_min
#print axioms curvature_nonneg_of_relevant
end StructuralGoal20261016.WindowSecondVariation
end
