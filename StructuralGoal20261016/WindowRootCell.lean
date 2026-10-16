/- SPDX-License-Identifier: Apache-2.0
Actual root cell of the new-window cover: every coupled pressure bound.
The numeric comparisons are kernel-checked over rationals. No global floor
or complete coverage is claimed by this root-containment theorem.
-/
import StructuralGoal20261016.WindowPressureRoot
import StructuralGoal20261016.WindowDifferenceCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Finset Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowRootCell
open StructuralW10Followup20261016.NewLedger

def indices (i j : Fin 10) : Finset (Fin 9) :=
  Finset.univ.filter (fun r => (i:ℕ) ≤ (r:ℕ) ∧ (r:ℕ) < (j:ℕ))

def root : DifferenceCell.Cell 10 := ![![0, 765058, 796546, 828034, 859522, 891010, 922498, 953986, 985474, 1016962], ![-31488, 0, 403138, 434626, 466114, 497602, 529090, 560578, 592066, 985474], ![-62976, -31488, 0, 297460, 328948, 360436, 391924, 423412, 560578, 953986], ![-94464, -62976, -31488, 0, 255780, 287268, 318756, 391924, 529090, 922498], ![-125952, -94464, -62976, -31488, 0, 237464, 287268, 360436, 497602, 891010], ![-157440, -125952, -94464, -62976, -31488, 0, 255780, 328948, 466114, 859522], ![-188928, -157440, -125952, -94464, -62976, -31488, 0, 297460, 434626, 828034], ![-220416, -188928, -157440, -125952, -94464, -62976, -31488, 0, 403138, 796546], ![-251904, -220416, -188928, -157440, -125952, -94464, -62976, -31488, 0, 765058], ![-283392, -251904, -220416, -188928, -157440, -125952, -94464, -62976, -31488, 0]]
def minimum : Fin 10 → Fin 10 → ℕ := ![![1, 2050531, 2050531, 2050531, 2050531, 2050531, 2050531, 2050531, 2050531, 2050531], ![1, 1, 4047384, 4047384, 4047384, 4047384, 4047384, 4047384, 4047384, 2050531], ![1, 1, 1, 5655513, 5655513, 5655513, 5655513, 5655513, 4047384, 2050531], ![1, 1, 1, 1, 6706494, 6706494, 6706494, 5655513, 4047384, 2050531], ![1, 1, 1, 1, 1, 7302840, 6706494, 5655513, 4047384, 2050531], ![1, 1, 1, 1, 1, 1, 6706494, 5655513, 4047384, 2050531], ![1, 1, 1, 1, 1, 1, 1, 5655513, 4047384, 2050531], ![1, 1, 1, 1, 1, 1, 1, 1, 4047384, 2050531], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 2050531], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

theorem span_indices (g : Fin 9 → ℝ) (i j : Fin 10) (hij : (i:ℕ) ≤ (j:ℕ)) :
    ptsN 10 g j-ptsN 10 g i = ∑ r ∈ indices i j, g r := by
  simp only [ptsN,indices,← Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp_all <;> omega

def Numeric : Prop :=
  (∀ i : Fin 10, root i i = 0) ∧ ∀ i j : Fin 10, (i:ℕ) < (j:ℕ) →
    0 < minimum i j ∧
    (∀ r ∈ indices i j, minimum i j ≤ bN r) ∧
    ((indices i j).card:ℚ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℚ)/10000000000)
        ≤ (root i j:ℚ)/32768 ∧
    -(root j i:ℚ)/32768 ≤ ((indices i j).card:ℚ)*(123/128)

theorem numeric : Numeric := by
  unfold Numeric
  decide +kernel

theorem positive_span_upper (g : Fin 9 → ℝ)
    (hg : WindowPressureRoot.Region (123/128) (221/25000) g)
    (i j : Fin 10) (hij : (i:ℕ) < (j:ℕ)) :
    ptsN 10 g j-ptsN 10 g i ≤ (root i j:ℝ)/32768 := by
  have data := numeric.2 i j hij
  have hmN : (0:ℝ) < (minimum i j:ℝ) := by exact_mod_cast data.1
  have hm : (0:ℝ) < (minimum i j:ℝ)/10000000000 := by positivity
  have hmb : ∀ r ∈ indices i j, (minimum i j:ℝ)/10000000000 ≤ W.b r := by
    intro r hr
    change (minimum i j:ℝ)/10000000000 ≤ (bN r:ℝ)/10000000000
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast data.2.1 r hr
  have h := WindowPressureRoot.selected_span_upper (indices i j) W.b g
    (123/128) (221/25000) ((minimum i j:ℝ)/10000000000)
    b_nonneg hg.1 hm hmb hg.2
  have hB : (∑ r, W.b r) = (11055671:ℝ)/2500000000 := pressure_eq
  rw [hB] at h
  have hu : ((indices i j).card:ℝ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℝ)/10000000000)
        ≤ (root i j:ℝ)/32768 := by
    have hQ := data.2.2.1
    have hR : ((((indices i j).card:ℚ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℚ)/10000000000):ℚ):ℝ)
        ≤ (((root i j:ℚ)/32768:ℚ):ℝ) := Rat.cast_le.mpr hQ
    push_cast at hR
    exact hR
  rw [span_indices g i j hij.le]
  exact h.le.trans hu

theorem positive_span_lower (g : Fin 9 → ℝ)
    (hg : CoverCoerciveKKT.Orthant (123/128) g)
    (i j : Fin 10) (hij : (i:ℕ) < (j:ℕ)) :
    -(root j i:ℝ)/32768 ≤ ptsN 10 g j-ptsN 10 g i := by
  have hl : -(root j i:ℝ)/32768 ≤ ((indices i j).card:ℝ)*(123/128) := by
    have hQ := (numeric.2 i j hij).2.2.2
    have hR : ((-(root j i:ℚ)/32768:ℚ):ℝ) ≤
      ((((indices i j).card:ℚ)*(123/128):ℚ):ℝ) := Rat.cast_le.mpr hQ
    push_cast at hR
    exact hR
  rw [span_indices g i j hij.le]
  apply hl.trans
  calc
    ((indices i j).card:ℝ)*(123/128) = ∑ r ∈ indices i j, (123/128:ℝ) := by simp
    _ ≤ ∑ r ∈ indices i j, g r := Finset.sum_le_sum (fun r _ => hg r)

theorem contains (g : Fin 9 → ℝ)
    (hg : WindowPressureRoot.Region (123/128) (221/25000) g) :
    WindowDifferenceCell.Contains root g := by
  intro i j
  change 32768*ptsN 10 g j-32768*ptsN 10 g i ≤ (root i j:ℝ)
  rcases lt_trichotomy (i:ℕ) (j:ℕ) with hij | hij | hij
  · have h := positive_span_upper g hg i j hij
    linarith
  · have heq : i = j := Fin.ext hij
    subst j
    rw [numeric.1 i]
    simp
  · have h := positive_span_lower g hg.1 j i hij
    linarith

set_option pp.fullNames true
#print axioms numeric
#print axioms span_indices
#print axioms positive_span_upper
#print axioms positive_span_lower
#print axioms contains
end StructuralGoal20261016.WindowRootCell
end
