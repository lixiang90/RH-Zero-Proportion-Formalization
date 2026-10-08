import Mathlib.Tactic

/-!
Finite proof layer for the already fixed expanded nine-point certificate.

This file introduces no mathematical axiom, no placeholder, and no native
decision procedure. The data-instantiation and low-cover walk are separate
from the generic real soundness lemmas below.
-/

namespace RHWeil.RecordSubmission.FiniteCertificate

def boxTerm (r lo hi : ℝ) : ℝ :=
  if 0 ≤ r then r * lo else r * hi

theorem boxTerm_le_mul {r lo hi x : ℝ}
    (hxlo : lo ≤ x) (hxhi : x ≤ hi) :
    boxTerm r lo hi ≤ r * x := by
  by_cases hr : 0 ≤ r
  · simp only [boxTerm, if_pos hr]
    exact mul_le_mul_of_nonneg_left hxlo hr
  · simp only [boxTerm, if_neg hr]
    exact mul_le_mul_of_nonpos_left hxhi (le_of_lt (lt_of_not_ge hr))

def dot {n : ℕ} (a x : Fin n → ℝ) : ℝ :=
  ∑ i, a i * x i

def residual {n m : ℕ} (c : Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin n) : ℝ :=
  c i + ∑ j, lam j * A j i

def dualLower {n m : ℕ} (c : Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (b lam : Fin m → ℝ)
    (lo hi : Fin n → ℝ) : ℝ :=
  -(∑ j, lam j * b j) + ∑ i, boxTerm (residual c A lam i) (lo i) (hi i)

theorem residual_dot {n m : ℕ} (c x : Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (lam : Fin m → ℝ) :
    dot (residual c A lam) x =
      dot c x + ∑ j, lam j * dot (A j) x := by
  simp only [dot, residual, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Complete box residual correction. No optimality or zero-residual
assumption is used. -/
theorem dualLower_sound {n m : ℕ} (c x : Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (b lam : Fin m → ℝ)
    (lo hi : Fin n → ℝ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hrows : ∀ j, dot (A j) x ≤ b j)
    (hlo : ∀ i, lo i ≤ x i) (hhi : ∀ i, x i ≤ hi i) :
    dualLower c A b lam lo hi ≤ dot c x := by
  have hr :
      (∑ j, lam j * dot (A j) x) ≤ ∑ j, lam j * b j :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hrows j) (hlam j)
  have hb :
      (∑ i, boxTerm (residual c A lam i) (lo i) (hi i)) ≤
        dot (residual c A lam) x :=
    Finset.sum_le_sum fun i _ => boxTerm_le_mul (hlo i) (hhi i)
  rw [residual_dot] at hb
  unfold dualLower
  linarith

/-- A positive scale transports the exact objective lower bound to the
normalized local reward. -/
theorem scaled_certificate_sound {n m : ℕ} (c x : Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (b lam : Fin m → ℝ)
    (lo hi : Fin n → ℝ) (scale target : ℝ)
    (hscale : 0 < scale)
    (hlam : ∀ j, 0 ≤ lam j)
    (hrows : ∀ j, dot (A j) x ≤ b j)
    (hlo : ∀ i, lo i ≤ x i) (hhi : ∀ i, x i ≤ hi i)
    (hcheck : scale * target ≤ dualLower c A b lam lo hi) :
    target ≤ dot c x / scale := by
  apply (le_div_iff₀ hscale).2
  have h := hcheck.trans (dualLower_sound c x A b lam lo hi hlam hrows hlo hhi)
  simpa only [mul_comm] using h

/-- A genuine interval tangent and a certified derivative interval give
two simultaneously usable affine cuts on the entire closed interval. -/
theorem safe_anchor_cuts {w : ℝ → ℝ} {v d dm dp q l u x : ℝ}
    (hdm : dm ≤ d) (hdp : d ≤ dp)
    (hlq : l ≤ q) (hqu : q ≤ u) (hlx : l ≤ x) (hxu : x ≤ u)
    (htangent : v + d * (x - q) ≤ w x) :
    v + dp * (l - q) + dm * (x - l) ≤ w x ∧
      v + dm * (u - q) + dp * (x - u) ≤ w x := by
  have h1 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hlx)
  have h2 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hlq)
  have h3 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hxu)
  have h4 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hqu)
  constructor <;> nlinarith

/-- The exact stronger-frame branch of the global nine-point cover. -/
theorem outside_low_cover {F0 F1 w : ℝ}
    (h0 : (805003 : ℝ) / 100000000 ≤ F0)
    (h1 : (805003 : ℝ) / 100000000 ≤ F1)
    (hw : 0 ≤ w)
    (hout : (805803 : ℝ) / 100000000 ≤ F0 ∨
      (805803 : ℝ) / 100000000 ≤ F1) :
    (805260 : ℝ) / 100000000 ≤ (F0 + F1) / 2 + 2 * w := by
  rcases hout with h | h <;> norm_num at * <;> linarith

/-- Exact target and ratio arithmetic, checked through the Lean kernel. -/
theorem target_ratio :
    (((67216841 : ℚ) - 404350) / 100000000) /
      (1 - (805260 : ℚ) / 100000000) = 66812491 / 99194740 := by
  norm_num

/- The production checker uses integer-scaled variables:
   Y_i = 5*SC*g_i and Z_ij = 5*10^10*SC*w(distance).
   The sparse multipliers have denominator 10^9. Gap/span rows are
   rescaled by 10^10 relative to kernel rows before applying this layer. -/

def intBoxTerm (r lo hi : ℤ) : ℤ :=
  if 0 ≤ r then r * lo else r * hi

def intResidual {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (lam : Fin m → ℕ) (i : Fin n) : ℤ :=
  c i + ∑ j, (lam j : ℤ) * A j i

def intDualLower {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (lam : Fin m → ℕ) (lo hi : Fin n → ℤ) : ℤ :=
  -(∑ j, (lam j : ℤ) * b j) +
    ∑ i, intBoxTerm (intResidual c A lam i) (lo i) (hi i)

def integerCheck {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (lam : Fin m → ℕ) (lo hi : Fin n → ℤ) (target : ℤ) : Bool :=
  decide (target ≤ intDualLower c A b lam lo hi)

theorem intBoxTerm_cast (r lo hi : ℤ) :
    (intBoxTerm r lo hi : ℝ) = boxTerm (r : ℝ) (lo : ℝ) (hi : ℝ) := by
  by_cases h : 0 ≤ r
  · have hr : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
    simp only [intBoxTerm, boxTerm, if_pos h, if_pos hr, Int.cast_mul]
  · have hr : ¬ (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
    simp only [intBoxTerm, boxTerm, if_neg h, if_neg hr, Int.cast_mul]

theorem intResidual_cast {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (lam : Fin m → ℕ) (i : Fin n) :
    (intResidual c A lam i : ℝ) =
      residual (fun i => (c i : ℝ)) (fun j i => (A j i : ℝ))
        (fun j => (lam j : ℝ)) i := by
  simp only [intResidual, residual, Int.cast_add, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast]

theorem intDualLower_cast {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (lam : Fin m → ℕ) (lo hi : Fin n → ℤ) :
    (intDualLower c A b lam lo hi : ℝ) =
      dualLower (fun i => (c i : ℝ)) (fun j i => (A j i : ℝ))
        (fun j => (b j : ℝ)) (fun j => (lam j : ℝ))
        (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ)) := by
  simp only [intDualLower, dualLower, Int.cast_add, Int.cast_neg,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    intBoxTerm_cast, intResidual_cast]

/-- Kernel evaluation of a closed integer checker implies a genuine
real objective bound, once all actual rows and box bounds are proved. -/
theorem integerCheck_sound {n m : ℕ} (c : Fin n → ℤ)
    (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (lam : Fin m → ℕ) (lo hi : Fin n → ℤ) (target : ℤ)
    (x : Fin n → ℝ)
    (hcheck : integerCheck c A b lam lo hi target = true)
    (hrows : ∀ j, dot (fun i => (A j i : ℝ)) x ≤ (b j : ℝ))
    (hlo : ∀ i, (lo i : ℝ) ≤ x i)
    (hhi : ∀ i, x i ≤ (hi i : ℝ)) :
    (target : ℝ) ≤ dot (fun i => (c i : ℝ)) x := by
  have hz : target ≤ intDualLower c A b lam lo hi :=
    of_decide_eq_true hcheck
  have hr : (target : ℝ) ≤ (intDualLower c A b lam lo hi : ℝ) := by
    exact_mod_cast hz
  rw [intDualLower_cast] at hr
  exact hr.trans (dualLower_sound _ _ _ _ _ _ _
    (fun j => Nat.cast_nonneg _) hrows hlo hhi)

/-- The exact integer threshold after both objective and multiplier
rescalings. It is independent of any floating-point proposal. -/
def expandedIntegerTarget : ℤ :=
  2 * 805260 * (5 * 10000000000 * 32768) * 1000000000

theorem expandedIntegerTarget_positive : 0 < expandedIntegerTarget := by
  norm_num [expandedIntegerTarget]

end RHWeil.RecordSubmission.FiniteCertificate
