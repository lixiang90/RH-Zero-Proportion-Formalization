/- SPDX-License-Identifier: Apache-2.0
Actual gap energy for the new 24-mode Fourier window. The function below is
shared by the counting and global KKT certificate interfaces. No global floor
or improved zeta proportion is assumed or asserted by this module. -/
import StructuralGoal20261016.WindowDerivative
import StructuralGoal20261016.CoverCoerciveKKT
import StructuralW10Followup20261016.NewLedger
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset Set Filter
open scoped BigOperators Topology
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowGapEnergy
open WindowKernel WindowDerivative
variable {n : ℕ}

def Fw (W : WCert n) (g : Fin (n-1) → ℝ) : ℝ :=
  ∑ r, W.b r * g r + ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) then
      W.a i j * WindowKernel.w 24 d24 (ptsN n g j - ptsN n g i) else 0

abbrev Fw24 := Fw StructuralW10Followup20261016.NewLedger.W

def w1 (x : ℝ) : ℝ := 2 * WindowKernel.k 24 d24 x * jet 24 d24 1 x

theorem w_hasDerivAt (x : ℝ) :
    HasDerivAt (WindowKernel.w 24 d24) (w1 x) x := by
  have h := (k24_hasDerivAt x).pow 2
  refine h.congr_deriv ?_
  simp only [w1]
  ring

theorem w_continuous : Continuous (WindowKernel.w 24 d24) :=
  continuous_iff_continuousAt.mpr (fun x => (w_hasDerivAt x).continuousAt)

theorem continuous_ptsN (i : Fin n) :
    Continuous (fun g : Fin (n-1) → ℝ => ptsN n g i) := by
  unfold ptsN
  apply continuous_finsetSum
  intro r _
  split_ifs
  · exact continuous_apply r
  · exact continuous_const

theorem continuous_Fw (W : WCert n) : Continuous (Fw W) := by
  unfold Fw
  apply Continuous.add
  · apply continuous_finsetSum
    intro r _
    exact continuous_const.mul (continuous_apply r)
  · apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    split_ifs
    · exact continuous_const.mul
        (w_continuous.comp ((continuous_ptsN j).sub (continuous_ptsN i)))
    · exact continuous_const

theorem pressure_le (W : WCert n) (ha : ∀ i j, 0 ≤ W.a i j)
    (g : Fin (n-1) → ℝ) : (∑ r, W.b r * g r) ≤ Fw W g := by
  unfold Fw
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (ha i j) (sq_nonneg _)
  · exact le_rfl

def line (g v : Fin (n-1) → ℝ) (t : ℝ) : Fin (n-1) → ℝ :=
  fun r => g r + t * v r

theorem line_zero (g v : Fin (n-1) → ℝ) : line g v 0 = g := by
  funext r
  simp [line]

theorem ptsN_line (g v : Fin (n-1) → ℝ) (t : ℝ) (i : Fin n) :
    ptsN n (line g v t) i = ptsN n g i + t * ptsN n v i := by
  classical
  unfold ptsN
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : (r : ℕ) < (i : ℕ)
  · simp only [h, if_true, line]
  · simp only [h, if_false, mul_zero, add_zero]

theorem ptsN_line_hasDerivAt (g v : Fin (n-1) → ℝ) (i : Fin n) :
    HasDerivAt (fun t => ptsN n (line g v t) i) (ptsN n v i) 0 := by
  have h : HasDerivAt (fun t : ℝ => ptsN n g i + t * ptsN n v i) (ptsN n v i) 0 := by
    simpa only [one_mul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (ptsN n v i)).const_add (ptsN n g i)
  simpa only [ptsN_line] using h

def directional (W : WCert n) (g v : Fin (n-1) → ℝ) : ℝ :=
  ∑ r, W.b r * v r + ∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) < (j : ℕ) then
      W.a i j * w1 (ptsN n g j - ptsN n g i) *
        (ptsN n v j - ptsN n v i) else 0

theorem directional_hasDerivAt (W : WCert n) (g v : Fin (n-1) → ℝ) :
    HasDerivAt (fun t => Fw W (line g v t)) (directional W g v) 0 := by
  classical
  have hp (r : Fin (n-1)) :
      HasDerivAt (fun t => W.b r * (line g v t) r) (W.b r * v r) 0 := by
    have h : HasDerivAt (fun t : ℝ => W.b r * (g r + t * v r)) (W.b r * v r) 0 := by
      simpa only [one_mul, id_eq] using
        (((hasDerivAt_id (0 : ℝ)).mul_const (v r)).const_add (g r)).const_mul (W.b r)
    convert h using 1
    funext t
    unfold line
    ring
  have hpair (i j : Fin n) : HasDerivAt
      (fun t => if (i : ℕ) < (j : ℕ) then
        W.a i j * WindowKernel.w 24 d24
          (ptsN n (line g v t) j - ptsN n (line g v t) i) else 0)
      (if (i : ℕ) < (j : ℕ) then
        W.a i j * w1 (ptsN n g j - ptsN n g i) *
          (ptsN n v j - ptsN n v i) else 0) 0 := by
    by_cases hij : (i : ℕ) < (j : ℕ)
    · simp only [if_pos hij]
      have hs := (ptsN_line_hasDerivAt g v j).sub (ptsN_line_hasDerivAt g v i)
      have hw := (w_hasDerivAt (ptsN n (line g v 0) j - ptsN n (line g v 0) i)).comp 0 hs
      rw [line_zero] at hw
      exact (hw.const_mul (W.a i j)).congr_deriv (by ring)
    · simp only [if_neg hij]
      exact hasDerivAt_const 0 0
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hpair i j))
  convert (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hp r)).add hs using 1 <;>
    first | rfl | simp only [Fw, directional, Pi.add_apply]

def basis (r : Fin (n-1)) : Fin (n-1) → ℝ := fun j => if j = r then 1 else 0
def gradient (W : WCert n) (g : Fin (n-1) → ℝ) (r : Fin (n-1)) : ℝ :=
  directional W g (basis r)

theorem line_basis (g : Fin (n-1) → ℝ) (r : Fin (n-1)) (t : ℝ) :
    line g (basis r) (t - g r) = CoverCoerciveKKT.coordinateLine g r t := by
  classical
  funext j
  by_cases hj : j = r
  · subst j
    simp [line, basis, CoverCoerciveKKT.coordinateLine]
  · simp [line, basis, hj, CoverCoerciveKKT.coordinateLine, Function.update_of_ne hj]

theorem coordinate_hasDerivAt (W : WCert n) (g : Fin (n-1) → ℝ) (r : Fin (n-1)) :
    HasDerivAt (fun t => Fw W (CoverCoerciveKKT.coordinateLine g r t))
      (gradient W g r) (g r) := by
  have ho : HasDerivAt (fun t => Fw W (line g (basis r) t))
      (gradient W g r) (g r - g r) := by
    simpa only [sub_self, gradient] using directional_hasDerivAt W g (basis r)
  have hi : HasDerivAt (fun t : ℝ => t - g r) 1 (g r) := by
    simpa only [id_eq] using (hasDerivAt_id (g r)).sub_const (g r)
  have h := ho.comp (h := fun t : ℝ => t - g r) (g r) hi
  have he : ((fun t => Fw W (line g (basis r) t)) ∘ fun t : ℝ => t - g r) =
      (fun t => Fw W (CoverCoerciveKKT.coordinateLine g r t)) := by
    funext t
    simp only [Function.comp_apply, line_basis]
  rw [he] at h
  convert h using 1 <;> first | rfl | simp only [mul_one]

/-- A direction may have negative components at strictly interior gaps. Only
its components on active lower faces must point into the feasible orthant. -/
theorem directional_nonneg_at_min (W : WCert n) {sep : ℝ}
    (g v : Fin (n-1) → ℝ) (hg : CoverCoerciveKKT.Orthant sep g)
    (hmin : ∀ y, CoverCoerciveKKT.Orthant sep y → Fw W g ≤ Fw W y)
    (hv : ∀ r, g r = sep → 0 ≤ v r) : 0 ≤ directional W g v := by
  classical
  have hcoord (r : Fin (n-1)) :
      ∀ᶠ t in 𝓝[>] (0 : ℝ), sep ≤ g r + t * v r := by
    by_cases hr : sep < g r
    · have hc : Continuous (fun t : ℝ => g r + t * v r) := by fun_prop
      have he : ∀ᶠ t in 𝓝 (0 : ℝ), sep < g r + t * v r :=
        (isOpen_Ioi.preimage hc).mem_nhds (by simpa using hr)
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
      exact ht.le
    · have heq : g r = sep := le_antisymm (le_of_not_gt hr) (hg r)
      have hv0 := hv r heq
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [heq]
      exact le_add_of_nonneg_right (mul_nonneg ht.le hv0)
  have hfeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), CoverCoerciveKKT.Orthant sep (line g v t) :=
    Filter.eventually_all.mpr hcoord
  have hm : IsLocalMinOn (fun t => Fw W (line g v t)) (Set.Ioi (0 : ℝ)) 0 := by
    change ∀ᶠ t in 𝓝[>] (0 : ℝ), Fw W (line g v 0) ≤ Fw W (line g v t)
    filter_upwards [hfeas] with t ht
    simpa only [line_zero] using hmin (line g v t) ht
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Set.Ioi (0 : ℝ)) 0 := by
    rw [one_mem_posTangentConeAt_iff_frequently]
    have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
    exact he.frequently
  have hd := directional_hasDerivAt W g v
  have h := hm.hasFDerivWithinAt_nonneg
    (hasDerivAt_iff_hasFDerivAt.1 hd).hasFDerivWithinAt hcone
  simpa using h

theorem ptsN_basis (r : Fin (n-1)) (i : Fin n) :
    ptsN n (basis r) i = if (r : ℕ) < (i : ℕ) then 1 else 0 := by
  classical
  unfold ptsN basis
  rw [Finset.sum_eq_single r]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem gradient_eq (W : WCert n) (g : Fin (n-1) → ℝ) (r : Fin (n-1)) :
    gradient W g r = W.b r + ∑ i : Fin n, ∑ j : Fin n,
      if (i : ℕ) < (j : ℕ) then
        W.a i j * w1 (ptsN n g j - ptsN n g i) *
          ((if (r : ℕ) < (j : ℕ) then 1 else 0) -
            (if (r : ℕ) < (i : ℕ) then 1 else 0)) else 0 := by
  classical
  simp [gradient, directional, ptsN_basis, basis]

theorem b24_pos (r : Fin 9) : 0 < StructuralW10Followup20261016.NewLedger.W.b r := by
  fin_cases r <;> norm_num [StructuralW10Followup20261016.NewLedger.W,
    StructuralW10Followup20261016.NewLedger.b, StructuralW10Followup20261016.NewLedger.bN]

/-- Explicit pressure root bound for every actual sublevel point. -/
theorem coordinate_upper_of_lt {sep c : ℝ} (g : Fin 9 → ℝ)
    (hg : CoverCoerciveKKT.Orthant sep g) (hf : Fw24 g < c) (r : Fin 9) :
    g r < sep +
      (c - sep * StructuralW10Followup20261016.NewLedger.W.B) /
        StructuralW10Followup20261016.NewLedger.W.b r := by
  let W := StructuralW10Followup20261016.NewLedger.W
  have hterms : ∀ j : Fin 9, 0 ≤ W.b j * (g j - sep) := by
    intro j
    exact mul_nonneg (b24_pos j).le (sub_nonneg.mpr (hg j))
  have hone : W.b r * (g r - sep) ≤ ∑ j, W.b j * (g j - sep) :=
    Finset.single_le_sum (fun j _ => hterms j) (Finset.mem_univ r)
  have hsum : (∑ j, W.b j * (g j - sep)) = (∑ j, W.b j * g j) - sep * W.B := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, WCert.B]
    ring
  have hp := pressure_le W StructuralW10Followup20261016.NewLedger.a_nonneg g
  have hmul : W.b r * (g r - sep) < c - sep * W.B := by
    rw [hsum] at hone
    change Fw W g < c at hf
    linarith
  have hdiv : g r - sep < (c - sep * W.B) / W.b r :=
    (lt_div_iff₀ (b24_pos r)).mpr (by simpa only [mul_comm] using hmul)
  change g r < sep + (c - sep * W.B) / W.b r
  linarith

theorem exists_global_min (sep : ℝ) : ∃ g : Fin 9 → ℝ,
    CoverCoerciveKKT.Orthant sep g ∧
      ∀ y, CoverCoerciveKKT.Orthant sep y → Fw24 g ≤ Fw24 y :=
  CoverCoerciveKKT.exists_global_min
    (continuous_Fw StructuralW10Followup20261016.NewLedger.W)
    StructuralW10Followup20261016.NewLedger.W.b b24_pos
    (fun g _ => pressure_le _ StructuralW10Followup20261016.NewLedger.a_nonneg g)

def reverse (g : Fin 9 → ℝ) : Fin 9 → ℝ := fun r => g r.rev

theorem Fw24_reverse (g : Fin 9 → ℝ) : Fw24 (reverse g) = Fw24 g := by
  simp [Fw24, Fw, StructuralW10Followup20261016.NewLedger.W,
    StructuralW10Followup20261016.NewLedger.a,
    StructuralW10Followup20261016.NewLedger.aN,
    StructuralW10Followup20261016.NewLedger.b,
    StructuralW10Followup20261016.NewLedger.bN,
    ptsN, reverse, Fin.sum_univ_succ, Fin.rev, Fin.succ]
  ring_nf

theorem exists_ordered_global_min (sep : ℝ) : ∃ g : Fin 9 → ℝ,
    CoverCoerciveKKT.Orthant sep g ∧ g 0 ≤ g 8 ∧
      ∀ y, CoverCoerciveKKT.Orthant sep y → Fw24 g ≤ Fw24 y := by
  obtain ⟨g, hg, hmin⟩ := exists_global_min sep
  by_cases ho : g 0 ≤ g 8
  · exact ⟨g, hg, ho, hmin⟩
  · refine ⟨reverse g, (fun r => hg r.rev), ?_, ?_⟩
    · change g 8 ≤ g 0
      exact le_of_lt (lt_of_not_ge ho)
    · intro y hy
      rw [Fw24_reverse]
      exact hmin y hy

/-- A counterexample to a floor yields an ordered actual global minimizer
below that same floor. This is the relevant domain for a KKT-only cover. -/
theorem exists_ordered_min_below {sep c : ℝ}
    (hcounter : ∃ y : Fin 9 → ℝ, CoverCoerciveKKT.Orthant sep y ∧ Fw24 y < c) :
    ∃ g : Fin 9 → ℝ, CoverCoerciveKKT.Orthant sep g ∧ g 0 ≤ g 8 ∧
      (∀ y, CoverCoerciveKKT.Orthant sep y → Fw24 g ≤ Fw24 y) ∧ Fw24 g < c := by
  obtain ⟨y, hy, hyc⟩ := hcounter
  obtain ⟨g, hg, ho, hmin⟩ := exists_ordered_global_min sep
  exact ⟨g, hg, ho, hmin, (hmin y hy).trans_lt hyc⟩

theorem floor_of_kkt_cover {sep c : ℝ}
    (hcover : ∀ g : Fin 9 → ℝ, CoverCoerciveKKT.Orthant sep g →
      (∀ r, 0 ≤ gradient StructuralW10Followup20261016.NewLedger.W g r) →
      (∀ r, sep < g r → gradient StructuralW10Followup20261016.NewLedger.W g r = 0) →
      c ≤ Fw24 g) :
    ∀ g : Fin 9 → ℝ, CoverCoerciveKKT.Orthant sep g → c ≤ Fw24 g :=
  CoverCoerciveKKT.floor_of_kkt_cover
    (continuous_Fw StructuralW10Followup20261016.NewLedger.W)
    StructuralW10Followup20261016.NewLedger.W.b b24_pos
    (fun g _ => pressure_le _ StructuralW10Followup20261016.NewLedger.a_nonneg g)
    (gradient StructuralW10Followup20261016.NewLedger.W)
    (coordinate_hasDerivAt StructuralW10Followup20261016.NewLedger.W) hcover

#print axioms continuous_Fw
#print axioms directional_hasDerivAt
#print axioms coordinate_hasDerivAt
#print axioms directional_nonneg_at_min
#print axioms exists_global_min
#print axioms coordinate_upper_of_lt
#print axioms Fw24_reverse
#print axioms exists_ordered_min_below
#print axioms floor_of_kkt_cover
end StructuralGoal20261016.WindowGapEnergy
end
