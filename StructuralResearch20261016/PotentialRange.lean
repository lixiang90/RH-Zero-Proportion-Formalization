import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/- Pure rational research lemma. The global local-energy inequality is not claimed.
   Fixed candidate SHA256: b8a684344d2fd2dc810ad0650fe4f5a49ed20cb84a43cc2c042242e21c49413a -/
noncomputable section
namespace OverlapPotential20261016
attribute [local instance] Classical.propDecidable
def classes (g : Fin 7 → ℝ) : Fin 7 → Fin 3 :=
  fun i => if g i ≤ 3 / 2 then 0 else if g i ≤ 5 / 2 then 1 else 2
def ternaryCode (w : Fin 7 → Fin 3) : ℕ := 1 * (w 0).val + 3 * (w 1).val + 9 * (w 2).val + 27 * (w 3).val + 81 * (w 4).val + 243 * (w 5).val + 729 * (w 6).val
def delta (s : ℕ) : ℝ :=
  if s = 91 then ((122089 : ℝ) / 1000000000000)
  else if s = 99 then ((-3878991 : ℝ) / 1000000000000)
  else if s = 165 then ((4745194 : ℝ) / 1000000000000)
  else if s = 171 then ((3878991 : ℝ) / 1000000000000)
  else if s = 253 then ((-122659 : ℝ) / 1000000000000)
  else if s = 261 then ((-4745194 : ℝ) / 1000000000000)
  else if s = 271 then ((-34532 : ℝ) / 1000000000000)
  else if s = 273 then ((85939 : ℝ) / 1000000000000)
  else if s = 276 then ((-4714932 : ℝ) / 1000000000000)
  else if s = 298 then ((860009 : ℝ) / 1000000000000)
  else if s = 496 then ((4417188 : ℝ) / 1000000000000)
  else if s = 516 then ((4714932 : ℝ) / 1000000000000)
  else if s = 759 then ((-68242 : ℝ) / 1000000000000)
  else if s = 786 then ((-860009 : ℝ) / 1000000000000)
  else if s = 813 then ((-52819 : ℝ) / 1000000000000)
  else if s = 816 then ((-4417188 : ℝ) / 1000000000000)
  else if s = 820 then ((75530 : ℝ) / 1000000000000)
  else 0
theorem delta_bounds (s : ℕ) :
    -(133 / 100000 : ℝ) ≤ delta s ∧ delta s ≤ (143 / 100000 : ℝ) := by
  by_cases h0 : s = 91
  · subst s; norm_num [delta]
  by_cases h1 : s = 99
  · subst s; norm_num [delta]
  by_cases h2 : s = 165
  · subst s; norm_num [delta]
  by_cases h3 : s = 171
  · subst s; norm_num [delta]
  by_cases h4 : s = 253
  · subst s; norm_num [delta]
  by_cases h5 : s = 261
  · subst s; norm_num [delta]
  by_cases h6 : s = 271
  · subst s; norm_num [delta]
  by_cases h7 : s = 273
  · subst s; norm_num [delta]
  by_cases h8 : s = 276
  · subst s; norm_num [delta]
  by_cases h9 : s = 298
  · subst s; norm_num [delta]
  by_cases h10 : s = 496
  · subst s; norm_num [delta]
  by_cases h11 : s = 516
  · subst s; norm_num [delta]
  by_cases h12 : s = 759
  · subst s; norm_num [delta]
  by_cases h13 : s = 786
  · subst s; norm_num [delta]
  by_cases h14 : s = 813
  · subst s; norm_num [delta]
  by_cases h15 : s = 816
  · subst s; norm_num [delta]
  by_cases h16 : s = 820
  · subst s; norm_num [delta]
  simp only [delta, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, if_false]
  norm_num
theorem zero_bounds {g : Fin 7 → ℝ} (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (i : Fin 7) (h : classes g i = 0) :
    (17 / 20 : ℝ) ≤ g i ∧ g i ≤ (3 / 2 : ℝ) := by
  by_cases h0 : g i ≤ (3 / 2 : ℝ)
  · exact ⟨hg i, h0⟩
  · dsimp only [classes] at h
    rw [if_neg h0] at h
    split_ifs at h with h1
    · have hh := congrArg Fin.val h; norm_num at hh
    · have hh := congrArg Fin.val h; norm_num at hh
theorem one_bounds {g : Fin 7 → ℝ} (i : Fin 7) (h : classes g i = 1) :
    (3 / 2 : ℝ) ≤ g i ∧ g i ≤ (5 / 2 : ℝ) := by
  by_cases h0 : g i ≤ (3 / 2 : ℝ)
  · simp [classes, h0] at h
  · by_cases h1 : g i ≤ (5 / 2 : ℝ)
    · exact ⟨(lt_of_not_ge h0).le, h1⟩
    · simp [classes, h0, h1] at h
def state21 : Fin 7 → Fin 3 := ![1, 0, 1, 0, 1, 0, 0]
def affine21 (g : Fin 7 → ℝ) : ℝ :=
  ((-2060881 : ℝ) / 1000000000000) +
    ((612766184 : ℝ) / 1000000000000) * (g 0 - (197 / 100 : ℝ)) +
    ((346100111 : ℝ) / 1000000000000) * (g 6 - (26 / 25 : ℝ))
theorem affine21_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state21) :
    -(133 / 100000 : ℝ) ≤ affine21 g ∧ affine21 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (1 : Fin 3) := by
    simpa [state21] using congrFun h (0 : Fin 7)
  have h0 := one_bounds (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state21] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (1 : Fin 3) := by
    simpa [state21] using congrFun h (2 : Fin 7)
  have h2 := one_bounds (2 : Fin 7) hc2
  have hc3 : classes g 3 = (0 : Fin 3) := by
    simpa [state21] using congrFun h (3 : Fin 7)
  have h3 := zero_bounds hg (3 : Fin 7) hc3
  have hc4 : classes g 4 = (1 : Fin 3) := by
    simpa [state21] using congrFun h (4 : Fin 7)
  have h4 := one_bounds (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state21] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (0 : Fin 3) := by
    simpa [state21] using congrFun h (6 : Fin 7)
  have h6 := zero_bounds hg (6 : Fin 7) hc6
  unfold affine21
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state37 : Fin 7 → Fin 3 := ![1, 0, 1, 0, 0, 1, 0]
def affine37 (g : Fin 7 → ℝ) : ℝ :=
  ((823975 : ℝ) / 1000000000000) +
    ((350082874 : ℝ) / 1000000000000) * (g 0 - (197 / 100 : ℝ)) +
    ((440102973 : ℝ) / 1000000000000) * (g 5 - (197 / 100 : ℝ)) +
    ((956226546 : ℝ) / 1000000000000) * (g 6 - (26 / 25 : ℝ))
theorem affine37_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state37) :
    -(133 / 100000 : ℝ) ≤ affine37 g ∧ affine37 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (1 : Fin 3) := by
    simpa [state37] using congrFun h (0 : Fin 7)
  have h0 := one_bounds (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state37] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (1 : Fin 3) := by
    simpa [state37] using congrFun h (2 : Fin 7)
  have h2 := one_bounds (2 : Fin 7) hc2
  have hc3 : classes g 3 = (0 : Fin 3) := by
    simpa [state37] using congrFun h (3 : Fin 7)
  have h3 := zero_bounds hg (3 : Fin 7) hc3
  have hc4 : classes g 4 = (0 : Fin 3) := by
    simpa [state37] using congrFun h (4 : Fin 7)
  have h4 := zero_bounds hg (4 : Fin 7) hc4
  have hc5 : classes g 5 = (1 : Fin 3) := by
    simpa [state37] using congrFun h (5 : Fin 7)
  have h5 := one_bounds (5 : Fin 7) hc5
  have hc6 : classes g 6 = (0 : Fin 3) := by
    simpa [state37] using congrFun h (6 : Fin 7)
  have h6 := zero_bounds hg (6 : Fin 7) hc6
  unfold affine37
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state41 : Fin 7 → Fin 3 := ![1, 0, 0, 1, 0, 1, 0]
def affine41 (g : Fin 7 → ℝ) : ℝ :=
  ((6925901 : ℝ) / 1000000000000) +
    ((240857535 : ℝ) / 1000000000000) * (g 0 - (197 / 100 : ℝ)) +
    ((545099343 : ℝ) / 1000000000000) * (g 3 - (197 / 100 : ℝ)) +
    ((762290651 : ℝ) / 1000000000000) * (g 6 - (26 / 25 : ℝ))
theorem affine41_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state41) :
    -(133 / 100000 : ℝ) ≤ affine41 g ∧ affine41 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (1 : Fin 3) := by
    simpa [state41] using congrFun h (0 : Fin 7)
  have h0 := one_bounds (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state41] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (0 : Fin 3) := by
    simpa [state41] using congrFun h (2 : Fin 7)
  have h2 := zero_bounds hg (2 : Fin 7) hc2
  have hc3 : classes g 3 = (1 : Fin 3) := by
    simpa [state41] using congrFun h (3 : Fin 7)
  have h3 := one_bounds (3 : Fin 7) hc3
  have hc4 : classes g 4 = (0 : Fin 3) := by
    simpa [state41] using congrFun h (4 : Fin 7)
  have h4 := zero_bounds hg (4 : Fin 7) hc4
  have hc5 : classes g 5 = (1 : Fin 3) := by
    simpa [state41] using congrFun h (5 : Fin 7)
  have h5 := one_bounds (5 : Fin 7) hc5
  have hc6 : classes g 6 = (0 : Fin 3) := by
    simpa [state41] using congrFun h (6 : Fin 7)
  have h6 := zero_bounds hg (6 : Fin 7) hc6
  unfold affine41
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state42 : Fin 7 → Fin 3 := ![0, 1, 0, 1, 0, 1, 0]
def affine42 (g : Fin 7 → ℝ) : ℝ :=
  ((-956858 : ℝ) / 1000000000000) +
    ((-819136184 : ℝ) / 1000000000000) * (g 0 - (26 / 25 : ℝ)) +
    ((631209351 : ℝ) / 1000000000000) * (g 1 - (197 / 100 : ℝ)) +
    ((-178763854 : ℝ) / 1000000000000) * (g 2 - (26 / 25 : ℝ)) +
    ((410194052 : ℝ) / 1000000000000) * (g 4 - (26 / 25 : ℝ)) +
    ((-569497694 : ℝ) / 1000000000000) * (g 5 - (197 / 100 : ℝ)) +
    ((977393305 : ℝ) / 1000000000000) * (g 6 - (26 / 25 : ℝ))
theorem affine42_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state42) :
    -(133 / 100000 : ℝ) ≤ affine42 g ∧ affine42 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (0 : Fin 3) := by
    simpa [state42] using congrFun h (0 : Fin 7)
  have h0 := zero_bounds hg (0 : Fin 7) hc0
  have hc1 : classes g 1 = (1 : Fin 3) := by
    simpa [state42] using congrFun h (1 : Fin 7)
  have h1 := one_bounds (1 : Fin 7) hc1
  have hc2 : classes g 2 = (0 : Fin 3) := by
    simpa [state42] using congrFun h (2 : Fin 7)
  have h2 := zero_bounds hg (2 : Fin 7) hc2
  have hc3 : classes g 3 = (1 : Fin 3) := by
    simpa [state42] using congrFun h (3 : Fin 7)
  have h3 := one_bounds (3 : Fin 7) hc3
  have hc4 : classes g 4 = (0 : Fin 3) := by
    simpa [state42] using congrFun h (4 : Fin 7)
  have h4 := zero_bounds hg (4 : Fin 7) hc4
  have hc5 : classes g 5 = (1 : Fin 3) := by
    simpa [state42] using congrFun h (5 : Fin 7)
  have h5 := one_bounds (5 : Fin 7) hc5
  have hc6 : classes g 6 = (0 : Fin 3) := by
    simpa [state42] using congrFun h (6 : Fin 7)
  have h6 := zero_bounds hg (6 : Fin 7) hc6
  unfold affine42
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state45 : Fin 7 → Fin 3 := ![1, 0, 1, 1, 0, 1, 0]
def affine45 (g : Fin 7 → ℝ) : ℝ :=
  ((-2213453 : ℝ) / 1000000000000)
theorem affine45_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state45) :
    -(133 / 100000 : ℝ) ≤ affine45 g ∧ affine45 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (1 : Fin 3) := by
    simpa [state45] using congrFun h (0 : Fin 7)
  have h0 := one_bounds (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state45] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (1 : Fin 3) := by
    simpa [state45] using congrFun h (2 : Fin 7)
  have h2 := one_bounds (2 : Fin 7) hc2
  have hc3 : classes g 3 = (1 : Fin 3) := by
    simpa [state45] using congrFun h (3 : Fin 7)
  have h3 := one_bounds (3 : Fin 7) hc3
  have hc4 : classes g 4 = (0 : Fin 3) := by
    simpa [state45] using congrFun h (4 : Fin 7)
  have h4 := zero_bounds hg (4 : Fin 7) hc4
  have hc5 : classes g 5 = (1 : Fin 3) := by
    simpa [state45] using congrFun h (5 : Fin 7)
  have h5 := one_bounds (5 : Fin 7) hc5
  have hc6 : classes g 6 = (0 : Fin 3) := by
    simpa [state45] using congrFun h (6 : Fin 7)
  have h6 := zero_bounds hg (6 : Fin 7) hc6
  unfold affine45
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state74 : Fin 7 → Fin 3 := ![0, 1, 0, 1, 0, 0, 1]
def affine74 (g : Fin 7 → ℝ) : ℝ :=
  ((-9943104 : ℝ) / 1000000000000) +
    ((-1033135558 : ℝ) / 1000000000000) * (g 0 - (26 / 25 : ℝ)) +
    ((-455659793 : ℝ) / 1000000000000) * (g 3 - (197 / 100 : ℝ)) +
    ((-421752578 : ℝ) / 1000000000000) * (g 6 - (197 / 100 : ℝ))
theorem affine74_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state74) :
    -(133 / 100000 : ℝ) ≤ affine74 g ∧ affine74 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (0 : Fin 3) := by
    simpa [state74] using congrFun h (0 : Fin 7)
  have h0 := zero_bounds hg (0 : Fin 7) hc0
  have hc1 : classes g 1 = (1 : Fin 3) := by
    simpa [state74] using congrFun h (1 : Fin 7)
  have h1 := one_bounds (1 : Fin 7) hc1
  have hc2 : classes g 2 = (0 : Fin 3) := by
    simpa [state74] using congrFun h (2 : Fin 7)
  have h2 := zero_bounds hg (2 : Fin 7) hc2
  have hc3 : classes g 3 = (1 : Fin 3) := by
    simpa [state74] using congrFun h (3 : Fin 7)
  have h3 := one_bounds (3 : Fin 7) hc3
  have hc4 : classes g 4 = (0 : Fin 3) := by
    simpa [state74] using congrFun h (4 : Fin 7)
  have h4 := zero_bounds hg (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state74] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (1 : Fin 3) := by
    simpa [state74] using congrFun h (6 : Fin 7)
  have h6 := one_bounds (6 : Fin 7) hc6
  unfold affine74
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state82 : Fin 7 → Fin 3 := ![0, 1, 0, 0, 1, 0, 1]
def affine82 (g : Fin 7 → ℝ) : ℝ :=
  ((-4332755 : ℝ) / 1000000000000) +
    ((-926632438 : ℝ) / 1000000000000) * (g 0 - (26 / 25 : ℝ)) +
    ((-624626025 : ℝ) / 1000000000000) * (g 1 - (197 / 100 : ℝ)) +
    ((-447280097 : ℝ) / 1000000000000) * (g 6 - (197 / 100 : ℝ))
theorem affine82_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state82) :
    -(133 / 100000 : ℝ) ≤ affine82 g ∧ affine82 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (0 : Fin 3) := by
    simpa [state82] using congrFun h (0 : Fin 7)
  have h0 := zero_bounds hg (0 : Fin 7) hc0
  have hc1 : classes g 1 = (1 : Fin 3) := by
    simpa [state82] using congrFun h (1 : Fin 7)
  have h1 := one_bounds (1 : Fin 7) hc1
  have hc2 : classes g 2 = (0 : Fin 3) := by
    simpa [state82] using congrFun h (2 : Fin 7)
  have h2 := zero_bounds hg (2 : Fin 7) hc2
  have hc3 : classes g 3 = (0 : Fin 3) := by
    simpa [state82] using congrFun h (3 : Fin 7)
  have h3 := zero_bounds hg (3 : Fin 7) hc3
  have hc4 : classes g 4 = (1 : Fin 3) := by
    simpa [state82] using congrFun h (4 : Fin 7)
  have h4 := one_bounds (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state82] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (1 : Fin 3) := by
    simpa [state82] using congrFun h (6 : Fin 7)
  have h6 := one_bounds (6 : Fin 7) hc6
  unfold affine82
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state84 : Fin 7 → Fin 3 := ![0, 0, 1, 0, 1, 0, 1]
def affine84 (g : Fin 7 → ℝ) : ℝ :=
  ((11431 : ℝ) / 1000000000000) +
    ((-306767379 : ℝ) / 1000000000000) * (g 0 - (26 / 25 : ℝ)) +
    ((-184983609 : ℝ) / 1000000000000) * (g 4 - (197 / 100 : ℝ)) +
    ((-698322057 : ℝ) / 1000000000000) * (g 6 - (197 / 100 : ℝ))
theorem affine84_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state84) :
    -(133 / 100000 : ℝ) ≤ affine84 g ∧ affine84 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (0 : Fin 3) := by
    simpa [state84] using congrFun h (0 : Fin 7)
  have h0 := zero_bounds hg (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state84] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (1 : Fin 3) := by
    simpa [state84] using congrFun h (2 : Fin 7)
  have h2 := one_bounds (2 : Fin 7) hc2
  have hc3 : classes g 3 = (0 : Fin 3) := by
    simpa [state84] using congrFun h (3 : Fin 7)
  have h3 := zero_bounds hg (3 : Fin 7) hc3
  have hc4 : classes g 4 = (1 : Fin 3) := by
    simpa [state84] using congrFun h (4 : Fin 7)
  have h4 := one_bounds (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state84] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (1 : Fin 3) := by
    simpa [state84] using congrFun h (6 : Fin 7)
  have h6 := one_bounds (6 : Fin 7) hc6
  unfold affine84
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state85 : Fin 7 → Fin 3 := ![1, 0, 1, 0, 1, 0, 1]
def affine85 (g : Fin 7 → ℝ) : ℝ :=
  ((-2262 : ℝ) / 1000000000000) +
    ((419109690 : ℝ) / 1000000000000) * (g 0 - (197 / 100 : ℝ)) +
    ((-663616995 : ℝ) / 1000000000000) * (g 1 - (26 / 25 : ℝ)) +
    ((245321503 : ℝ) / 1000000000000) * (g 2 - (197 / 100 : ℝ)) +
    ((-293327685 : ℝ) / 1000000000000) * (g 4 - (197 / 100 : ℝ)) +
    ((867402733 : ℝ) / 1000000000000) * (g 5 - (26 / 25 : ℝ)) +
    ((-514373417 : ℝ) / 1000000000000) * (g 6 - (197 / 100 : ℝ))
theorem affine85_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state85) :
    -(133 / 100000 : ℝ) ≤ affine85 g ∧ affine85 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (1 : Fin 3) := by
    simpa [state85] using congrFun h (0 : Fin 7)
  have h0 := one_bounds (0 : Fin 7) hc0
  have hc1 : classes g 1 = (0 : Fin 3) := by
    simpa [state85] using congrFun h (1 : Fin 7)
  have h1 := zero_bounds hg (1 : Fin 7) hc1
  have hc2 : classes g 2 = (1 : Fin 3) := by
    simpa [state85] using congrFun h (2 : Fin 7)
  have h2 := one_bounds (2 : Fin 7) hc2
  have hc3 : classes g 3 = (0 : Fin 3) := by
    simpa [state85] using congrFun h (3 : Fin 7)
  have h3 := zero_bounds hg (3 : Fin 7) hc3
  have hc4 : classes g 4 = (1 : Fin 3) := by
    simpa [state85] using congrFun h (4 : Fin 7)
  have h4 := one_bounds (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state85] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (1 : Fin 3) := by
    simpa [state85] using congrFun h (6 : Fin 7)
  have h6 := one_bounds (6 : Fin 7) hc6
  unfold affine85
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def state90 : Fin 7 → Fin 3 := ![0, 1, 0, 1, 1, 0, 1]
def affine90 (g : Fin 7 → ℝ) : ℝ :=
  ((2698829 : ℝ) / 1000000000000)
theorem affine90_bounds {g : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (h : classes g = state90) :
    -(133 / 100000 : ℝ) ≤ affine90 g ∧ affine90 g ≤ (143 / 100000 : ℝ) := by
  have hc0 : classes g 0 = (0 : Fin 3) := by
    simpa [state90] using congrFun h (0 : Fin 7)
  have h0 := zero_bounds hg (0 : Fin 7) hc0
  have hc1 : classes g 1 = (1 : Fin 3) := by
    simpa [state90] using congrFun h (1 : Fin 7)
  have h1 := one_bounds (1 : Fin 7) hc1
  have hc2 : classes g 2 = (0 : Fin 3) := by
    simpa [state90] using congrFun h (2 : Fin 7)
  have h2 := zero_bounds hg (2 : Fin 7) hc2
  have hc3 : classes g 3 = (1 : Fin 3) := by
    simpa [state90] using congrFun h (3 : Fin 7)
  have h3 := one_bounds (3 : Fin 7) hc3
  have hc4 : classes g 4 = (1 : Fin 3) := by
    simpa [state90] using congrFun h (4 : Fin 7)
  have h4 := one_bounds (4 : Fin 7) hc4
  have hc5 : classes g 5 = (0 : Fin 3) := by
    simpa [state90] using congrFun h (5 : Fin 7)
  have h5 := zero_bounds hg (5 : Fin 7) hc5
  have hc6 : classes g 6 = (1 : Fin 3) := by
    simpa [state90] using congrFun h (6 : Fin 7)
  have h6 := one_bounds (6 : Fin 7) hc6
  unfold affine90
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]
def V (g : Fin 7 → ℝ) : ℝ :=
  if classes g = state21 then affine21 g
  else if classes g = state37 then affine37 g
  else if classes g = state41 then affine41 g
  else if classes g = state42 then affine42 g
  else if classes g = state45 then affine45 g
  else if classes g = state74 then affine74 g
  else if classes g = state82 then affine82 g
  else if classes g = state84 then affine84 g
  else if classes g = state85 then affine85 g
  else if classes g = state90 then affine90 g
  else delta (ternaryCode (classes g))
theorem V_bounds (g : Fin 7 → ℝ) (hg : ∀ i, (17 / 20 : ℝ) ≤ g i) :
    -(133 / 100000 : ℝ) ≤ V g ∧ V g ≤ (143 / 100000 : ℝ) := by
  unfold V
  split_ifs with h21 h37 h41 h42 h45 h74 h82 h84 h85 h90
  · exact affine21_bounds hg h21
  · exact affine37_bounds hg h37
  · exact affine41_bounds hg h41
  · exact affine42_bounds hg h42
  · exact affine45_bounds hg h45
  · exact affine74_bounds hg h74
  · exact affine82_bounds hg h82
  · exact affine84_bounds hg h84
  · exact affine85_bounds hg h85
  · exact affine90_bounds hg h90
  · exact delta_bounds _
theorem V_oscillation {g h : Fin 7 → ℝ}
    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i) (hh : ∀ i, (17 / 20 : ℝ) ≤ h i) :
    V g - V h ≤ (69 / 25000 : ℝ) := by
  have a := V_bounds g hg
  have b := V_bounds h hh
  linarith
end OverlapPotential20261016
#print axioms OverlapPotential20261016.V_bounds
#print axioms OverlapPotential20261016.V_oscillation
