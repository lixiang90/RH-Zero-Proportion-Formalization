/- SPDX-License-Identifier: Apache-2.0
Global minimum and coordinate KKT reduction for a continuous energy bounded
below by strictly positive pressure on a lower orthant. No finite cover or
new zeta proportion is asserted by this generic reduction.
-/
import GramDefect20261015.Core
set_option Elab.async false

noncomputable section
open Set Filter Finset
open scoped Topology
namespace StructuralGoal20261016.CoverCoerciveKKT

def Orthant {n : ℕ} (sep : ℝ) (g : Fin n → ℝ) : Prop := ∀ i, sep ≤ g i

def coordinateLine {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update g i t

theorem coordinateLine_mem {n : ℕ} {sep : ℝ} {g : Fin n → ℝ}
    (hg : Orthant sep g) (i : Fin n) {t : ℝ} (ht : sep ≤ t) :
    Orthant sep (coordinateLine g i t) := by
  intro j
  by_cases h : j = i
  · subst j
    simpa [coordinateLine] using ht
  · simpa [coordinateLine, Function.update_of_ne h] using hg j

/-- Strictly positive linear pressure makes the relevant sublevel compact.
    The minimizer is proved to exist, and is not an extra hypothesis. -/
theorem exists_global_min {n : ℕ} {sep : ℝ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) (b : Fin n → ℝ) (hb : ∀ i, 0 < b i)
    (hpressure : ∀ g, Orthant sep g → (∑ i, b i * g i) ≤ F g) :
    ∃ g, Orthant sep g ∧ ∀ y, Orthant sep y → F g ≤ F y := by
  classical
  let z : Fin n → ℝ := fun _ => sep
  let p : ℝ := ∑ i, b i * sep
  let budget : ℝ := F z - p
  have hz : Orthant sep z := by intro i; exact le_rfl
  have hbudget : 0 ≤ budget := by
    have h := hpressure z hz
    change (∑ i, b i * sep) ≤ F z at h
    dsimp [budget, p]
    linarith
  let U : Fin n → ℝ := fun i => sep + budget / b i
  have hzU : z ≤ U := by
    intro i
    exact le_add_of_nonneg_right (div_nonneg hbudget (hb i).le)
  have hsublevel : ∀ y, Orthant sep y → F y ≤ F z → y ∈ Icc z U := by
    intro y hy hyF
    refine ⟨hy, ?_⟩
    intro i
    have hterms : ∀ j : Fin n, 0 ≤ b j * (y j - sep) := by
      intro j; exact mul_nonneg (hb j).le (sub_nonneg.mpr (hy j))
    have hone : b i * (y i - sep) ≤ ∑ j, b j * (y j - sep) :=
      Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ i)
    have hsum : (∑ j, b j * (y j - sep)) = (∑ j, b j * y j) - p := by
      simp [mul_sub, Finset.sum_sub_distrib, p]
    rw [hsum] at hone
    have hp := hpressure y hy
    have hmul : b i * (y i - sep) ≤ budget := by
      dsimp [budget]
      linarith
    have hdiv : y i - sep ≤ budget / b i := by
      apply (le_div_iff₀ (hb i)).mpr
      simpa [mul_comm] using hmul
    dsimp [U]
    linarith
  obtain ⟨g, hg, hmin⟩ := (isCompact_Icc : IsCompact (Icc z U)).exists_isMinOn
    ⟨z, le_rfl, hzU⟩ hF.continuousOn
  refine ⟨g, hg.1, ?_⟩
  intro y hy
  by_cases hyF : F y ≤ F z
  · exact hmin (hsublevel y hy hyF)
  · exact (hmin ⟨le_rfl, hzU⟩).trans (le_of_lt (lt_of_not_ge hyF))

/-- Every existing coordinate derivative at an orthant minimum is nonnegative.
    The direction of increase is feasible even on the boundary. -/
theorem gradient_nonneg {n : ℕ} {sep : ℝ} {F : (Fin n → ℝ) → ℝ}
    {g : Fin n → ℝ} (hg : Orthant sep g)
    (hmin : ∀ y, Orthant sep y → F g ≤ F y)
    (i : Fin n) {d : ℝ}
    (hd : HasDerivAt (fun t => F (coordinateLine g i t)) d (g i)) : 0 ≤ d := by
  let f : ℝ → ℝ := fun t => F (coordinateLine g i t)
  have hline : ∀ t ∈ Ici sep, f (g i) ≤ f t := by
    intro t ht
    have h := hmin (coordinateLine g i t) (coordinateLine_mem hg i ht)
    simpa [f, coordinateLine] using h
  have hlocal : IsLocalMinOn f (Ici sep) (g i) := by
    change ∀ᶠ t in 𝓝[Ici sep] (g i), f (g i) ≤ f t
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hline t ht
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Ici sep) (g i) := by
    rw [one_mem_posTangentConeAt_iff_frequently]
    have he : ∀ᶠ t in 𝓝[>] (g i), t ∈ Ici sep := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hg i).trans (le_of_lt ht)
    exact he.frequently
  have hd' : HasDerivAt f d (g i) := hd
  have h := hlocal.hasFDerivWithinAt_nonneg
    (hasDerivAt_iff_hasFDerivAt.1 hd').hasFDerivWithinAt hcone
  simpa using h

/-- Away from the lower face both coordinate directions are feasible. -/
theorem gradient_eq_zero {n : ℕ} {sep : ℝ} {F : (Fin n → ℝ) → ℝ}
    {g : Fin n → ℝ} (hg : Orthant sep g)
    (hmin : ∀ y, Orthant sep y → F g ≤ F y)
    (i : Fin n) (hi : sep < g i) {d : ℝ}
    (hd : HasDerivAt (fun t => F (coordinateLine g i t)) d (g i)) : d = 0 := by
  have hlocal : IsLocalMin (fun t => F (coordinateLine g i t)) (g i) := by
    change ∀ᶠ t in 𝓝 (g i), F (coordinateLine g i (g i)) ≤ F (coordinateLine g i t)
    filter_upwards [Ici_mem_nhds hi] with t ht
    simpa [coordinateLine] using hmin (coordinateLine g i t) (coordinateLine_mem hg i ht)
  exact hlocal.hasDerivAt_eq_zero hd

/-- A complete certificate covering only KKT-compatible minima suffices for
    a global floor. The cover remains an explicit, substantive proof input. -/
theorem floor_of_kkt_cover {n : ℕ} {sep c : ℝ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) (b : Fin n → ℝ) (hb : ∀ i, 0 < b i)
    (hpressure : ∀ g, Orthant sep g → (∑ i, b i * g i) ≤ F g)
    (d : (Fin n → ℝ) → Fin n → ℝ)
    (hd : ∀ g i, HasDerivAt (fun t => F (coordinateLine g i t)) (d g i) (g i))
    (hcover : ∀ g, Orthant sep g → (∀ i, 0 ≤ d g i) →
      (∀ i, sep < g i → d g i = 0) → c ≤ F g) :
    ∀ y, Orthant sep y → c ≤ F y := by
  obtain ⟨g, hg, hmin⟩ := exists_global_min hF b hb hpressure
  have hfloor : c ≤ F g := hcover g hg
    (fun i => gradient_nonneg hg hmin i (hd g i))
    (fun i hi => gradient_eq_zero hg hmin i hi (hd g i))
  intro y hy
  exact hfloor.trans (hmin y hy)

#print axioms exists_global_min
#print axioms gradient_nonneg
#print axioms gradient_eq_zero
#print axioms floor_of_kkt_cover
end StructuralGoal20261016.CoverCoerciveKKT
end
