import Mathlib.Tactic
import RecordProportion.ImportedAM
import RecordProportion.FiniteCertificateData
import RecordProportion.FloydSoundness
import RecordProportion.RowEvaluation
import RecordProportion.SparseDualSoundness
import RecordProportion.PointSoundness
import RecordProportion.GeometryCoverage

open scoped BigOperators

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Finite proof layer for the already fixed expanded nine-point certificate.

This file introduces no mathematical axiom, no placeholder, and no native
decision procedure. The data-instantiation and low-cover walk are separate
from the generic real soundness lemmas below.
-/

namespace RHWeil.RecordSubmission.FiniteCertificate

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

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

theorem tangent_scaled_cuts {f : Nat → Nat} {L U p : Nat}
    (ht : TVal f L U p) (s : Real)
    (hsL : (L:Real)/SC ≤ s) (hsU : s ≤ (U:Real)/SC) :
    10*((lo32 (hi32 (f p)):Real)-2000000000)*SC*s-10000000000*SC*wfun s ≤
        -(lo32 (f p):Real)*SC + 10*(2000000000-(hi32 (hi32 (f p)):Real))*(p:Real) -
          10*((2000000000-(hi32 (hi32 (f p)):Real))-
            ((lo32 (hi32 (f p)):Real)-2000000000))*(L:Real) ∧
    10*(2000000000-(hi32 (hi32 (f p)):Real))*SC*s-10000000000*SC*wfun s ≤
        -(lo32 (f p):Real)*SC + 10*((lo32 (hi32 (f p)):Real)-2000000000)*(p:Real) -
          10*(((lo32 (hi32 (f p)):Real)-2000000000)-
            (2000000000-(hi32 (hi32 (f p)):Real)))*(U:Real) := by
  obtain ⟨hLp,hpU,hdm,hdp,hval⟩ := ht
  have h1 : ((lo32 (hi32 (f p)):Real)-2000000000)/1000000000 ≤ w1 ((p:Real)/SC) := by linarith
  have h2 : w1 ((p:Real)/SC) ≤ (2000000000-(hi32 (hi32 (f p)):Real))/1000000000 := by linarith
  have hL : (L:Real)/SC ≤ (p:Real)/SC := by exact div_le_div_of_nonneg_right (by exact_mod_cast hLp) (by norm_num [SC])
  have hU : (p:Real)/SC ≤ (U:Real)/SC := by exact div_le_div_of_nonneg_right (by exact_mod_cast hpU) (by norm_num [SC])
  have hc := safe_anchor_cuts h1 h2 hL hU hsL hsU (hval s hsL hsU)
  have hm1 := mul_le_mul_of_nonneg_left hc.1 (by norm_num : (0:Real) ≤ 327680000000000)
  have hm2 := mul_le_mul_of_nonneg_left hc.2 (by norm_num : (0:Real) ≤ 327680000000000)
  norm_num [SC] at hm1 hm2 ⊢
  constructor <;> nlinarith [hm1,hm2]

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

/- Reflection acts on the actual AM objective and the actual upstream
   InCell predicate. It is not merely a symmetry of certificate labels. -/

def scalarF9 (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : ℝ :=
  (AMW.Cert.PC8CL.G x0 x1 x2 x3 x4 x5 x6 +
    AMW.Cert.PC8CL.G x1 x2 x3 x4 x5 x6 x7) / 2 +
    2 * AMW.Cert.wfun (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7)

theorem scalarF9_reflection (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) :
    scalarF9 x7 x6 x5 x4 x3 x2 x1 x0 =
      scalarF9 x0 x1 x2 x3 x4 x5 x6 x7 := by
  unfold scalarF9
  rw [AMW.Cert.PC8CL_G_rev x1 x2 x3 x4 x5 x6 x7,
    AMW.Cert.PC8CL_G_rev x0 x1 x2 x3 x4 x5 x6]
  have hs : x7 + x6 + x5 + x4 + x3 + x2 + x1 + x0 =
      x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 := by ring
  rw [hs]
  ring

def reverseSeven (g : ℕ → ℝ) : ℕ → ℝ := fun i => g (6 - i)

theorem reverseSeven_involution (g : ℕ → ℝ) (i : ℕ) (hi : i < 7) :
    reverseSeven (reverseSeven g) i = g i := by
  simp only [reverseSeven]
  congr 1
  omega

def reflectionSpan : List ℕ :=
  [20, 19, 17, 14, 10, 5, 18, 16, 13, 9, 4, 15, 12, 8, 3, 11, 7, 2, 6, 1, 0]

def reflectedCell (c : AMW.Cert.PCell.Cl) : AMW.Cert.PCell.Cl :=
  ⟨(List.range 7).map (fun i => c.L.getD (6 - i) 0),
    (List.range 7).map (fun i => c.U.getD (6 - i) 0),
    reflectionSpan.map (fun k => c.A.getD k 0),
    reflectionSpan.map (fun k => c.B.getD k 0)⟩

theorem reflectedCell_lengths (c : AMW.Cert.PCell.Cl) :
    (reflectedCell c).L.length = 7 ∧ (reflectedCell c).U.length = 7 ∧
      (reflectedCell c).A.length = 21 ∧ (reflectedCell c).B.length = 21 := by
  simp [reflectedCell, reflectionSpan]

theorem InCell_reflection (c : AMW.Cert.PCell.Cl) (g : ℕ → ℝ)
    (hg : AMW.Cert.PCell.InCell 7 AMW.Cert.PC8CL.PR c g) :
    AMW.Cert.PCell.InCell 7 AMW.Cert.PC8CL.PR
      (reflectedCell c) (reverseSeven g) := by
  constructor
  · intro i hi
    change (((List.range 7).map (fun r => c.L.getD (6-r) 0)).getD i 0 : Real) / AMW.Cert.SC ≤ g (6-i) ∧
      g (6-i) ≤ (((List.range 7).map (fun r => c.U.getD (6-r) 0)).getD i 0 : Real) / AMW.Cert.SC
    rw [AMW.Cert.PCell.getD_map_range _ hi, AMW.Cert.PCell.getD_map_range _ hi]
    exact hg.1 (6-i) (by omega)
  · intro k hk
    have hk' : k < 21 := by simpa [AMW.Cert.PC8CL.PR] using hk
    interval_cases k
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 20 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 19 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 17 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 14 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 10 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 5 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 18 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 16 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 13 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 9 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 4 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 15 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 12 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 8 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 3 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 11 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 7 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 2 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 6 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 1 (by decide)
    · simpa [reflectedCell, reflectionSpan, reverseSeven,
        AMW.Cert.PC8CL.PR, AMW.Cert.PCell.pI, AMW.Cert.PCell.pJ,
        AMW.Cert.PCell.gsum_range, Finset.sum_range_succ,
        add_comm, add_left_comm, add_assoc] using hg.2 0 (by decide)

def W9aNumerators : List ℕ :=
  [0, 13630830, 0, 19565904, 20317441, 45030671, 100000000, 200000000, 400000000, 0, 0, 43628826, 30621878, 67332393, 99999999, 154969327, 200000000, 200000000, 0, 0, 0, 67354136, 99999999, 113101699, 159365116, 154969327, 100000000, 0, 0, 0, 0, 75386205, 138756242, 113101699, 99999999, 45030671, 0, 0, 0, 0, 0, 75386205, 99999999, 67332393, 20317441, 0, 0, 0, 0, 0, 0, 67354136, 30621878, 19565904, 0, 0, 0, 0, 0, 0, 0, 43628826, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13630830, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def W9bNumerators : List ℕ := [28898, 86170, 132798, 156484, 156484, 132798, 86170, 28898]

def W9 : Zeta23Ext.BridgeW.WCert 9 where
  a i j := (W9aNumerators.getD (9 * i.val + j.val) 0 : ℝ) / 200000000
  b r := (W9bNumerators.getD r.val 0 : ℝ) / 200000000

theorem W9_pressure : W9.B = (404350 : ℝ) / 100000000 := by
  norm_num [Zeta23Ext.BridgeW.WCert.B, W9, W9bNumerators, Fin.sum_univ_succ]

theorem W9_bmin (r : Fin 8) :
    (28898 : ℝ) / 200000000 ≤ W9.b r := by
  fin_cases r <;> norm_num [W9, W9bNumerators]

theorem W9_pairmass :
    (∑ i : Fin 9, ∑ j : Fin 9, W9.a i j) ≤ 16 := by
  norm_num [W9, W9aNumerators, Fin.sum_univ_succ]

theorem W9_upper_pairmass :
    (∑ i : Fin 9, ∑ j : Fin 9,
      if (i : Nat) < (j : Nat) then W9.a i j else 0) ≤ 16 := by
  apply le_trans _ W9_pairmass
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Nat.cast_nonneg _) (by norm_num)

def W9SpanNumerator (s : Nat) : Nat :=
  ∑ i : Fin 9, ∑ j : Fin 9,
    if i.val < j.val ∧ j.val-i.val=s then W9aNumerators.getD (9*i.val+j.val) 0 else 0

theorem spanmass_eq (s : Nat) :
    W9.spanMass s = (W9SpanNumerator s : Real)/200000000 := by
  unfold Zeta23Ext.BridgeW.WCert.spanMass W9SpanNumerator W9
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem spanNumerator_le (s : Nat) : W9SpanNumerator s ≤ 400000000 := by
  by_cases hs : s ≤ 8
  · interval_cases s <;> decide +kernel
  · have hz : W9SpanNumerator s = 0 := by
      unfold W9SpanNumerator
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro h
      have hj := j.isLt
      omega
    rw [hz]
    decide

theorem W9_adm : W9.Adm := by
  constructor
  · intro i j
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · intro r
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  · intro s
    rw [spanmass_eq]
    have h : (W9SpanNumerator s : Real) ≤ 400000000 := by
      exact_mod_cast spanNumerator_le s
    linarith


/- Complete low-cover routing. The captured low cells are actual closed
   upstream cells; a successful branch proves either the stronger frame
   inequality or membership in one of these cells. -/
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC8CL

open RHWeil.RecordSubmission.FiniteCertificateData

def ninePoints (g : Fin 8 → Real) (i : Fin 9) : Real :=
  [0,g 0,g 0+g 1,g 0+g 1+g 2,g 0+g 1+g 2+g 3,
   g 0+g 1+g 2+g 3+g 4,g 0+g 1+g 2+g 3+g 4+g 5,
   g 0+g 1+g 2+g 3+g 4+g 5+g 6,
   g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7].getD i.val 0

theorem ninePoints_eq (g : Fin 8 → Real) (i : Fin 9) :
    Zeta23Ext.Bridge.ptsN 9 g i = ninePoints g i := by
  fin_cases i <;>
    simp [Zeta23Ext.Bridge.ptsN,ninePoints,Fin.sum_univ_succ] <;> ring

theorem W9_scalar_identity (g : Fin 8 → Real) :
    Zeta23Ext.BridgeW.Fw W9 g = scalarF9 (g 0) (g 1) (g 2) (g 3)
      (g 4) (g 5) (g 6) (g 7) := by
  have he : g = (fun r : Fin 8 => [g 0,g 1,g 2,g 3,g 4,g 5,g 6,g 7].getD r.val 0) := by
    funext r
    fin_cases r <;> rfl
  conv_lhs => rw [he]
  unfold Zeta23Ext.BridgeW.Fw
  simp only [Fin.sum_univ_succ]
  norm_num [W9,W9aNumerators,W9bNumerators]
  simp_rw [ninePoints_eq]
  have hw : Zeta23Ext.Bridge.wfun = AMW.Cert.wfun := rfl
  rw [hw]
  simp only [ninePoints,scalarF9,AMW.Cert.PC8CL.G]
  norm_num [AMW.Cert.PC8CL.SA]
  norm_num [Fin.succ,Fin.castSucc]
  ring_nf


def lowCell (index : Nat) : Cl where
  L := (List.range 7).map fun r => cellLower index r (r+1)
  U := (List.range 7).map fun r => cellUpper index r (r+1)
  A := longSpans.map fun p => cellLower index p.1 p.2
  B := longSpans.map fun p => cellUpper index p.1 p.2


/-- Every actual gap or long-span bound is retained by the decoded cell. -/
theorem lowCell_spanbounds (index : Nat) (g : Nat → Real)
    (hg : InCell 7 PR (lowCell index) g) (i j : Nat)
    (hij : i < j) (hj : j ≤ 7) :
    (cellLower index i j : Real)/SC ≤ gsum g i j ∧
      gsum g i j ≤ (cellUpper index i j : Real)/SC := by
  have hi : i ≤ 6 := by omega
  interval_cases i <;> interval_cases j <;> first
    | omega
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 0 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 1 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 2 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 3 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 4 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 5 (by decide)
    | simpa [lowCell,gsum_range,Finset.sum_range_succ,getD_map_range] using hg.1 6 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 0 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 1 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 2 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 3 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 4 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 5 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 6 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 7 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 8 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 9 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 10 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 11 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 12 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 13 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 14 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 15 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 16 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 17 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 18 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 19 (by decide)
    | simpa [lowCell,longSpans,PR,pI,pJ] using hg.2 20 (by decide)

theorem gsum_shift (g : Nat → Real) (offset i j : Nat) :
    gsum (fun r => g (r+offset)) i j = gsum g (i+offset) (j+offset) := by
  simp only [gsum_range,Nat.add_sub_add_right]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  omega

theorem natList_sum_cast (xs : List Nat) :
    ((xs.sum:Nat):Real) = (xs.map fun (a : Nat) => (a:Real)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem lowCell_tightbounds (label i j : Nat) (g : Nat → Real)
    (hg : InCell 7 PR (lowCell label) g) (hij : i < j) (hj : j ≤ 7) :
    (tightLower label i j:Real)/SC ≤ gsum g i j ∧
      gsum g i j ≤ (tightUpper label i j:Real)/SC := by
  have hSC : (0:Real) < SC := by norm_num [SC]
  have hbase := lowCell_spanbounds label g hg i j hij hj
  have hLo : ((((List.range (j-i)).map fun k => cellLower label (i+k) (i+k+1)).sum:Nat):Real) ≤
      SC*gsum g i j := by
    rw [natList_sum_cast,List.map_map]
    change (((List.range (j-i)).map fun k => (cellLower label (i+k) (i+k+1):Real)).sum) ≤ _
    rw [RHWeilRecord.SparseDualSoundness.range_sum,gsum_range,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hb := (lowCell_spanbounds label g hg (i+k) (i+k+1) (by omega) (by omega)).1
    have hc := (div_le_iff₀ hSC).mp hb
    simp only [gsum_range, Nat.add_sub_cancel_left, Finset.sum_range_one, Nat.add_zero] at hc
    nlinarith
  have hHi : SC*gsum g i j ≤
      ((((List.range (j-i)).map fun k => cellUpper label (i+k) (i+k+1)).sum:Nat):Real) := by
    rw [natList_sum_cast,List.map_map]
    change _ ≤ (((List.range (j-i)).map fun k => (cellUpper label (i+k) (i+k+1):Real)).sum)
    rw [RHWeilRecord.SparseDualSoundness.range_sum,gsum_range,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hb := (lowCell_spanbounds label g hg (i+k) (i+k+1) (by omega) (by omega)).2
    have hc := (le_div_iff₀ hSC).mp hb
    simp only [gsum_range, Nat.add_sub_cancel_left, Finset.sum_range_one, Nat.add_zero] at hc
    nlinarith
  constructor
  · apply (div_le_iff₀ hSC).mpr
    simp only [tightLower,Nat.cast_max]
    apply max_le
    · have h := (div_le_iff₀ hSC).mp hbase.1; nlinarith
    · nlinarith
  · apply (le_div_iff₀ hSC).mpr
    simp only [tightUpper,Nat.cast_min]
    apply le_min
    · have h := (le_div_iff₀ hSC).mp hbase.2; nlinarith
    · nlinarith

def gapPotential (g : Nat → Real) (i : Nat) : Real :=
  5*SC*∑ r ∈ Finset.range i, g r

theorem gapPotential_difference (g : Nat → Real) (i j : Nat) (hij : i ≤ j) :
    gapPotential g j - gapPotential g i = 5*SC*gsum g i j := by
  rw [gsum,Finset.sum_Ico_eq_sub _ hij]
  unfold gapPotential
  ring

theorem cellUpper_le (label i j : Nat) : cellUpper label i j ≤ 4194303 := by
  unfold cellUpper cellBound bits
  exact Nat.and_le_right

theorem gsum_nonneg_of_theta {g : Nat → Real}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r) {i j : Nat} (hj : j ≤ 8) :
    0 ≤ gsum g i j := by
  rw [gsum_range]
  apply Finset.sum_nonneg
  intro r hr
  have h := htheta (i+r) (by have := Finset.mem_range.mp hr; omega)
  linarith

theorem gapPotential_mono {g : Nat → Real}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ 8) : gapPotential g i ≤ gapPotential g j := by
  have h := gsum_nonneg_of_theta htheta hj (i := i)
  have hd := gapPotential_difference g i j hij
  have hSC : (0 : Real) ≤ 5*SC := by norm_num [SC]
  have := mul_nonneg hSC h
  linarith

/-- The finite infinity sentinel is bounded using the actual two frames. -/
theorem pairPotential_infinity {g : Nat → Real} {left right : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1)))
    {i j : Nat} (hi : i < 9) (hj : j < 9) :
    gapPotential g j - gapPotential g i ≤ 1000000000000000000000000000000 := by
  have hleft := (lowCell_spanbounds left g hl 0 7 (by decide) (by decide)).2
  have hright := (lowCell_spanbounds right (fun r => g (r+1)) hr 6 7
    (by decide) (by decide)).2
  have huL : (cellUpper left 0 7 : Real) ≤ 4194303 := by
    exact_mod_cast cellUpper_le left 0 7
  have huR : (cellUpper right 6 7 : Real) ≤ 4194303 := by
    exact_mod_cast cellUpper_le right 6 7
  have hp7 := gapPotential_difference g 0 7 (by decide)
  have hp8 := gapPotential_difference g 7 8 (by decide)
  have h0 : gapPotential g 0 = 0 := by simp [gapPotential]
  have hnon := gapPotential_mono htheta (i := 0) (j := i) (by omega) (by omega)
  have hmax := gapPotential_mono htheta (i := j) (j := 8) (by omega) (by omega)
  simp only [gsum_range, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.add_zero] at hright hp8
  norm_num [SC] at hleft hright hp7 hp8
  rw [h0] at hp7 hnon
  nlinarith

theorem framePotential_upper {g : Nat → Real} {label i j : Nat}
    (hcell : InCell 7 PR (lowCell label) g) (hij : i < j) (hj : j ≤ 7) :
    gapPotential g j - gapPotential g i ≤ 5*(cellUpper label i j : Real) ∧
      gapPotential g i - gapPotential g j ≤ -5*(cellLower label i j : Real) := by
  have hs := lowCell_spanbounds label g hcell i j hij hj
  have hd := gapPotential_difference g i j (by omega)
  norm_num [SC] at hs hd
  constructor <;> nlinarith

/-- Actual continuous gaps satisfy every primitive edge of the 9-prefix graph. -/
theorem primitiveBound_sound {g : Nat → Real} {left right i j : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1)))
    (hi : i < 9) (hj : j < 9) :
    gapPotential g j - gapPotential g i ≤ (primitiveBound left right i j : Real) := by
  by_cases heq : i = j
  · subst j
    simp [primitiveBound]
  have hinf := pairPotential_infinity htheta hl hr hi hj
  have hfirst : gapPotential g j - gapPotential g i ≤
      (if i ≤ 7 ∧ j ≤ 7 then
        if i < j then 5*(cellUpper left i j : Int) else -5*(cellLower left j i : Int)
       else 1000000000000000000000000000000 : Int) := by
    by_cases hframe : i ≤ 7 ∧ j ≤ 7
    · rw [if_pos hframe]
      by_cases hij : i < j
      · rw [if_pos hij, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        exact (framePotential_upper hl hij hframe.2).1
      · rw [if_neg hij]
        push_cast
        norm_num
        have hrev := (framePotential_upper (i := j) (j := i) hl (by omega) hframe.1).2
        linarith
    · simpa only [if_neg hframe, Int.cast_ofNat] using hinf
  have hsecond : gapPotential g j - gapPotential g i ≤
      (if 1 ≤ i ∧ 1 ≤ j then
        if i < j then 5*(cellUpper right (i-1) (j-1) : Int)
        else -5*(cellLower right (j-1) (i-1) : Int)
       else 1000000000000000000000000000000 : Int) := by
    by_cases hframe : 1 ≤ i ∧ 1 ≤ j
    · rw [if_pos hframe]
      by_cases hij : i < j
      · rw [if_pos hij, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        have hs := (lowCell_spanbounds right (fun r => g (r+1)) hr
          (i-1) (j-1) (by omega) (by omega)).2
        rw [gsum_shift] at hs
        rw [show i-1+1=i by omega, show j-1+1=j by omega] at hs
        have hd := gapPotential_difference g i j (by omega)
        norm_num [SC] at hs hd
        nlinarith
      · rw [if_neg hij]
        push_cast
        norm_num
        have hs := (lowCell_spanbounds right (fun r => g (r+1)) hr
          (j-1) (i-1) (by omega) (by omega)).1
        rw [gsum_shift] at hs
        rw [show i-1+1=i by omega, show j-1+1=j by omega] at hs
        have hd := gapPotential_difference g j i (by omega)
        norm_num [SC] at hs hd
        nlinarith
    · simpa only [if_neg hframe, Int.cast_ofNat] using hinf
  unfold primitiveBound
  rw [if_neg heq]
  dsimp only
  by_cases hadj : i = j+1
  · rw [if_pos hadj, Int.cast_min, Int.cast_min]
    refine le_min (le_min hfirst hsecond) ?_
    rw [hadj]
    have ht := htheta j (by omega)
    have hd := gapPotential_difference g j i (by omega)
    rw [hadj] at hd
    simp only [gsum_range, Nat.add_sub_cancel, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.add_zero] at hd
    norm_num [SC] at hd ⊢
    nlinarith
  · rw [if_neg hadj, Int.cast_min]
    exact le_min hfirst hsecond

def initialPairBounds (left right : Nat) : Array Int :=
  ((List.range 81).map fun slot => primitiveBound left right (slot/9) (slot%9)).toArray

theorem initialPairBounds_entry (left right i j : Nat) (hi : i < 9) (hj : j < 9) :
    ((initialPairBounds left right)[9*i+j]?).getD 0 = primitiveBound left right i j := by
  have hs : 9*i+j < 81 := by omega
  have hd : (9*i+j)/9=i := by omega
  have hm : (9*i+j)%9=j := by omega
  simp [initialPairBounds,hs,hd,hm]

theorem initialPotentialBound {g : Nat → Real} {left right : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
      (initialPairBounds left right) := by
  intro i hi j hj
  rw [initialPairBounds_entry left right i j hi hj]
  exact primitiveBound_sound htheta hl hr hi hj

theorem closedPotentialBound {g : Nat → Real} {left right : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
      (pairClosure left right) := by
  change RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
    (RHWeilRecord.FloydSoundness.closure (initialPairBounds left right))
  exact RHWeilRecord.FloydSoundness.closure_real_preserves
    (initialPotentialBound htheta hl hr)

def kernelScale : Real := 5*10000000000*32768

def actualVector (g : Nat → Real) (column : Fin 42) : Real :=
  if column.val < 8 then 5*SC*g column.val else
    let p := squareSpans.getD (column.val-8) (0,0)
    kernelScale*wfun (gsum g p.1 p.2)

def integerBoxLo (left right : Nat) (column : Fin 42) : Int :=
  if column.val < 8 then max (4*32768)
    (-((pairClosure left right)[9*(column.val+1)+column.val]?).getD 0) else 0

def integerBoxHi (left right : Nat) (column : Fin 42) : Int :=
  if column.val < 8 then
    ((pairClosure left right)[9*column.val+column.val+1]?).getD 0
  else 5*10000000000*32768

/-- Both signs of every objective residual use the full Floyd box. -/
theorem actualVector_box {g : Nat → Real} {left right : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1))) (column : Fin 42) :
    (integerBoxLo left right column : Real) ≤ actualVector g column ∧
      actualVector g column ≤ (integerBoxHi left right column : Real) := by
  have hc := closedPotentialBound htheta hl hr
  by_cases hsmall : column.val < 8
  · have hd := gapPotential_difference g column.val (column.val+1) (by omega)
    simp only [gsum_range,Nat.add_sub_cancel,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,Nat.add_zero] at hd
    have hfor := hc column.val (by omega) (column.val+1) (by omega)
    have hrev := hc (column.val+1) (by omega) column.val (by omega)
    have ht := htheta column.val hsmall
    simp only [actualVector,integerBoxLo,integerBoxHi,if_pos hsmall,Int.cast_max,
      Int.cast_neg,Int.cast_mul,Int.cast_ofNat]
    rw [show 9*column.val+column.val+1 = 9*column.val+(column.val+1) by omega]
    norm_num [SC] at hd ⊢
    constructor
    · constructor <;> nlinarith
    · nlinarith
  · simp only [actualVector,integerBoxLo,integerBoxHi,if_neg hsmall]
    have hnon : 0 ≤ wfun (gsum g (squareSpans.getD (column.val-8) (0,0)).1
      (squareSpans.getD (column.val-8) (0,0)).2) := by
      exact sq_nonneg _
    have hup := AMW.wfunAM_le_one (gsum g (squareSpans.getD (column.val-8) (0,0)).1
      (squareSpans.getD (column.val-8) (0,0)).2)
    have hscale : 0 ≤ kernelScale := by norm_num [kernelScale]
    constructor
    · simpa only [Int.cast_zero] using mul_nonneg hscale hnon
    · calc kernelScale * _ ≤ kernelScale * 1 :=
          mul_le_mul_of_nonneg_left hup hscale
        _ = _ := by norm_num [kernelScale]

def actualValue (g : Nat → Real) (column : Nat) : Real :=
  RHWeilRecord.RowEvaluation.actualValue wfun g column

theorem actualValue_fin (g : Nat → Real) (column : Fin 42) :
    actualValue g column.val = actualVector g column := by
  simp only [actualValue,RHWeilRecord.RowEvaluation.actualValue,actualVector]
  split_ifs <;> simp [RHWeilRecord.RowEvaluation.kernelScale,kernelScale,
    RHWeilRecord.RowEvaluation.gsum,gsum_range,SC]

theorem actualValue_box {g : Nat → Real} {left right : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1)))
    (column : Nat) (hc : column < 42) :
    (integerBoxLo left right ⟨column,hc⟩ : Real) ≤ actualValue g column ∧
      actualValue g column ≤ (integerBoxHi left right ⟨column,hc⟩ : Real) := by
  rw [actualValue_fin g ⟨column,hc⟩]
  exact actualVector_box htheta hl hr ⟨column,hc⟩

theorem integerObjective_identity (g : Nat → Real) :
    (∑ i ∈ Finset.range 42, (objectiveCoeff i:Real)*actualValue g i) =
      200000000*kernelScale*scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  norm_num [objectiveCoeff,actualValue,RHWeilRecord.RowEvaluation.actualValue,squareSpans,terms,RHWeilRecord.RowEvaluation.gsum,
    scalarF9,AMW.Cert.PC8CL.G,kernelScale,RHWeilRecord.RowEvaluation.kernelScale,SA,Finset.sum_range_succ]
  ring_nf

theorem cell_ext {c d : Cl} (hL : c.L = d.L) (hU : c.U = d.U)
    (hA : c.A = d.A) (hB : c.B = d.B) : c = d := by
  cases c
  cases d
  cases hL
  cases hU
  cases hA
  cases hB
  rfl

theorem cellBound_reflection (label i j side : Nat) (hl : label < 241) :
    cellBound (label+241) i j side = cellBound label (7-j) (7-i) side := by
  have hn : ¬ label+241 < 241 := by omega
  simp only [cellBound,cellPacket,if_pos hl,if_neg hn,Nat.add_sub_cancel]

theorem list_ext_getD {L U : List Nat} (hl : L.length = U.length)
    (h : ∀ i, i < L.length → i < U.length → L.getD i 0 = U.getD i 0) : L = U := by
  apply List.ext_getElem hl
  intro i hi hj
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] using h i hi hj

theorem lowCell_reflected (label : Nat) (hl : label < 241) :
    lowCell (label+241) = reflectedCell (lowCell label) := by
  apply cell_ext
  · apply list_ext_getD
    · simp [lowCell,reflectedCell]
    · intro i hi hj
      simp only [lowCell,reflectedCell,List.length_map,List.length_range] at hi hj ⊢
      rw [getD_map_range _ hi,getD_map_range _ hj]
      rw [getD_map_range _ (show 6-i<7 by omega)]
      change cellBound (label+241) i (i+1) 0 = cellBound label (6-i) (6-i+1) 0
      rw [cellBound_reflection label i (i+1) 0 hl]
      have h1 : 7-(i+1)=6-i := by omega
      have h2 : 7-i=6-i+1 := by omega
      rw [h1,h2]
  · apply list_ext_getD
    · simp [lowCell,reflectedCell]
    · intro i hi hj
      simp only [lowCell,reflectedCell,List.length_map,List.length_range] at hi hj ⊢
      rw [getD_map_range _ hi,getD_map_range _ hj]
      rw [getD_map_range _ (show 6-i<7 by omega)]
      change cellBound (label+241) i (i+1) 1 = cellBound label (6-i) (6-i+1) 1
      rw [cellBound_reflection label i (i+1) 1 hl]
      have h1 : 7-(i+1)=6-i := by omega
      have h2 : 7-i=6-i+1 := by omega
      rw [h1,h2]
  · apply list_ext_getD
    · simp [lowCell,reflectedCell,longSpans,reflectionSpan]
    · intro i hi hj
      simp only [lowCell,reflectedCell,List.length_map,List.length_range] at hi hj
      have hi' : i < 21 := by simpa [longSpans] using hi
      interval_cases i <;>
        simp [lowCell,reflectedCell,longSpans,reflectionSpan,cellLower,cellBound_reflection label _ _ 0 hl]
  · apply list_ext_getD
    · simp [lowCell,reflectedCell,longSpans,reflectionSpan]
    · intro i hi hj
      simp only [lowCell,reflectedCell,List.length_map,List.length_range] at hi hj
      have hi' : i < 21 := by simpa [longSpans] using hi
      interval_cases i <;>
        simp [lowCell,reflectedCell,longSpans,reflectionSpan,cellUpper,cellBound_reflection label _ _ 1 hl]

def lowMatch (c : Cl) (index : Nat) : Bool :=
  decide (c.L = (lowCell index).L) && decide (c.U = (lowCell index).U) &&
    decide (c.A = (lowCell index).A) && decide (c.B = (lowCell index).B)

def lowCheck (c : Cl) : Bool := (List.range 241).any (lowMatch c)

def StrongOrLow (g : Nat → Real) : Prop :=
  Pg 805803 7 BS TS g ∨ ∃ index < 241, InCell 7 PR (lowCell index) g

theorem lowCheck_sound {c : Cl} (h : lowCheck c = true) :
    ∃ index < 241, c = lowCell index := by
  obtain ⟨index, hindex, hmatch⟩ := List.any_eq_true.mp h
  have hi : index < 241 := List.mem_range.mp hindex
  simp only [lowMatch, Bool.and_eq_true, decide_eq_true_eq] at hmatch
  obtain ⟨⟨⟨hL,hU⟩,hA⟩,hB⟩ := hmatch
  exact ⟨index,hi,cell_ext hL hU hA hB⟩

def strongLeaf (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
 forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
 forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
 forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
 forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
 forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
 forceR (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) fun L07 => forceR (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) fun U07 =>
 forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
 forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
 forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
 forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
 forceR (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) fun L17 => forceR (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) fun U17 =>
 forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
 forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
 forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
 forceR (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) fun L27 => forceR (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) fun U27 =>
 forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
 forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
 forceR (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) fun L37 => forceR (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) fun U37 =>
 forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
 forceR (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) fun L47 => forceR (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) fun U47 =>
 forceR (nmax s.A57 (Nat.add s.l5 s.l6)) fun L57 => forceR (nmin s.B57 (Nat.add s.u5 s.u6)) fun U57 =>
 forceR 0 fun o0 =>
 dec4F 8 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
 dec4F 8 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
 dec4F 8 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
 dec4F 8 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
 dec4F 8 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
 dec4F 8 w o5 L07 U07 fun k07 m07 p07 r07 o6 =>
 dec4F 8 w o6 s.l1 s.u1 fun k12 m12 p12 r12 o7 =>
 dec4F 8 w o7 L13 U13 fun k13 m13 p13 r13 o8 =>
 dec4F 8 w o8 L14 U14 fun k14 m14 p14 r14 o9 =>
 dec4F 8 w o9 L15 U15 fun k15 m15 p15 r15 o10 =>
 dec4F 8 w o10 L16 U16 fun k16 m16 p16 r16 o11 =>
 dec4F 8 w o11 L17 U17 fun k17 m17 p17 r17 o12 =>
 dec4F 8 w o12 s.l2 s.u2 fun k23 m23 p23 r23 o13 =>
 dec4F 8 w o13 L24 U24 fun k24 m24 p24 r24 o14 =>
 dec4F 8 w o14 L25 U25 fun k25 m25 p25 r25 o15 =>
 dec4F 8 w o15 L26 U26 fun k26 m26 p26 r26 o16 =>
 dec4F 8 w o16 L27 U27 fun k27 m27 p27 r27 o17 =>
 dec4F 8 w o17 s.l3 s.u3 fun k34 m34 p34 r34 o18 =>
 dec4F 8 w o18 L35 U35 fun k35 m35 p35 r35 o19 =>
 dec4F 8 w o19 L36 U36 fun k36 m36 p36 r36 o20 =>
 dec4F 8 w o20 L37 U37 fun k37 m37 p37 r37 o21 =>
 dec4F 8 w o21 s.l4 s.u4 fun k45 m45 p45 r45 o22 =>
 dec4F 8 w o22 L46 U46 fun k46 m46 p46 r46 o23 =>
 dec4F 8 w o23 L47 U47 fun k47 m47 p47 r47 o24 =>
 dec4F 8 w o24 s.l5 s.u5 fun k56 m56 p56 r56 o25 =>
 dec4F 8 w o25 s.l6 s.u6 fun k67 m67 p67 r67 o26 =>
 (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k56 m56 p56 r56 k67 m67 p67 r67 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.P6 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.S6 y.Cp y.Cm 805803))
 (ydec (toCl s).L (toCl s).A (toCl s).B 12 w 42 ⟨o26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
theorem strongLeaf_sound {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
   (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb) (hR : rgOk R = true) (w : ℕ) (s : St)
   (h : strongLeaf top bk tD bD pb R w s ≠ 0) : CovBy 7 PR (Pg 805803 7 BS TS) (toCl s) := by
 unfold strongLeaf at h
 simp only [dec4F, forceR_eq] at h
 exact mcheckGZ_sound (f := pb) hlb hD hpt hR (by decide : 0 < 8) hPR hTS (ydec_ok s 12 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 805803 (brec_ne h))
def chosenLeaf (top : Nat) (bk : Nat → Nat) (tD : Nat) (bD : Nat → Nat)
    (pb : Nat → Nat) (R : Nat × Nat × List (List Nat)) (w : Nat) (s : St) : Nat :=
  let strong := strongLeaf top bk tD bD pb R w s
  if strong = 0 then
    if lowCheck (toCl s) = true then mleafP top bk tD bD pb R w s else 0
  else strong

theorem chosenLeaf_sound {top : Nat} {bk : Nat → Nat} {tD : Nat}
    {bD : Nat → Nat} {pb : Nat → Nat} {R : Nat × Nat × List (List Nat)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb)
    (hR : rgOk R = true) (w : Nat) (s : St)
    (h : chosenLeaf top bk tD bD pb R w s ≠ 0) :
    CovBy 7 PR StrongOrLow (toCl s) := by
  by_cases hs : strongLeaf top bk tD bD pb R w s = 0
  · by_cases hl : lowCheck (toCl s) = true
    · obtain ⟨index,hi,he⟩ := lowCheck_sound hl
      intro g hg
      exact Or.inr ⟨index,hi,he ▸ hg⟩
    · simp [chosenLeaf,hs,hl] at h
  · intro g hg
    exact Or.inl (strongLeaf_sound hlb hD hpt hR w s hs g hg)

def lowCoverLeafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
 fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A24 B24 A25 B25 A26 B26 A27 B27 A35 B35 A36 B36 A37 B37 A46 B46 A47 B47 A57 B57 M => Bool.rec (motive := fun _ => ℕ)
   (forceR (Bool.rec (motive := fun _ => ℕ) (chosenLeaf top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A24, B24, A25, B25, A26, B26, A27, B27, A35, B35, A36, B36, A37, B37, A46, B46, A47, B47, A57, B57, M⟩)
       (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A24, B24, A25, B25, A26, B26, A27, B27, A35, B35, A36, B36, A37, B37, A46, B46, A47, B47, A57, B57, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
     Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
   (Nat.add pos 1) (Nat.blt u6 l0)
theorem lowCoverLeafStep_sound {top : Nat} {bk : Nat → Nat} {tD : Nat}
    {bD : Nat → Nat} {pb : Nat → Nat} {R : Nat × Nat × List (List Nat)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb)
    (hR : rgOk R = true) (pos w : Nat) :
    CovK (lowCoverLeafStep top bk tD bD pb R pos w) StrongOrLow := by
  intro s h
  have h' : Bool.rec (motive := fun _ => Nat)
      (forceR (Bool.rec (motive := fun _ => Nat)
        (chosenLeaf top bk tD bD pb R (Nat.shiftRight w 2) s)
        (fleaf (Nat.shiftRight w 2) s)
        (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
        Bool.rec (motive := fun _ => Nat) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
      (Nat.add pos 1) (Nat.blt s.u6 s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u6 s.l0
  · rw [hs,forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'
      exact chosenLeaf_sound hlb hD hpt hR _ s fun h0 => by
        rw [h0] at h'
        exact h' rfl
    · rw [hk] at h'
      exact farkas_cov (ydec_ok s 12 (Nat.shiftRight w 2) 42 _
        (MulOK_zero s 0)) (brec_ne (show fleaf (Nat.shiftRight w 2) s ≠ 0 from fun h0 => by
          rw [h0] at h'
          exact h' rfl))
  · intro g hg
    left
    right
    have h1 : g 6 ≤ (s.u6 : Real) / SC := (hg.1 6 (by norm_num)).2
    have h2 : (s.l0 : Real) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have hlt : (s.u6 : Real) / SC < (s.l0 : Real) / SC :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    linarith

def lowCoverNode (top : Nat) (bk : Nat → Nat) (tD : Nat) (bD : Nat → Nat)
    (pb : Nat → Nat) (R : Nat × Nat × List (List Nat))
    (bits : Nat) (ih : WF) (pos : Nat) : ST :=
  Bool.rec (motive := fun _ => ST)
    (lowCoverLeafStep top bk tD bD pb R pos (Nat.shiftRight bits pos))
    (splitAx ih (Nat.add pos 6) (Nat.land (Nat.shiftRight (Nat.shiftRight bits pos) 1) 31))
    (Nat.beq (Nat.land (Nat.shiftRight bits pos) 1) 1)

def lowCoverWalkC (top : Nat) (bk : Nat → Nat) (tD : Nat) (bD : Nat → Nat)
    (pb : Nat → Nat) (R : Nat × Nat × List (List Nat)) (bits fuel : Nat) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK)
    (fun _ ih pos => lowCoverNode top bk tD bD pb R bits ih pos) fuel

def lowCoverWalk (top : Nat) (bk : Nat → Nat) (tD : Nat) (bD : Nat → Nat)
    (pb : Nat → Nat) (R : Nat × Nat × List (List Nat)) (bits fuel : Nat) : WF :=
  fun pos => tm (lowCoverWalkC top bk tD bD pb R bits fuel pos)

theorem lowCoverWalkC_sound {top : Nat} {bk : Nat → Nat} {tD : Nat}
    {bD : Nat → Nat} {pb : Nat → Nat} {R : Nat × Nat × List (List Nat)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb)
    (hR : rgOk R = true) (bits : Nat) :
    ∀ fuel, WalkOK (lowCoverWalkC top bk tD bD pb R bits fuel) StrongOrLow
  | 0 => fun _ => zK_ok
  | n+1 => fun pos => show CovK
      (lowCoverNode top bk tD bD pb R bits
        (lowCoverWalkC top bk tD bD pb R bits n) pos) StrongOrLow from
      brec_dep (P := fun k => CovK k StrongOrLow)
        (fun _ => lowCoverLeafStep_sound hlb hD hpt hR pos _) fun _ =>
        splitAx_ok (lowCoverWalkC_sound hlb hD hpt hR bits n) _ _

theorem lowCoverWalk_sound {top : Nat} {bk : Nat → Nat} {tD : Nat}
    {bD : Nat → Nat} {pb : Nat → Nat} {R : Nat × Nat × List (List Nat)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF pb)
    (hR : rgOk R = true) (bits fuel : Nat) :
    WalkOK (lowCoverWalk top bk tD bD pb R bits fuel) StrongOrLow :=
  fun pos => tm_ok (lowCoverWalkC_sound hlb hD hpt hR bits fuel pos)


/-- The full positive pressure is retained together with a single
    certified kernel term. This is needed at original clear-cover nodes. -/
theorem separated_pressure_term {g : Nat → Real}
    (htheta : ∀ r < 7, (4 : Real)/5 ≤ g r) {n : Nat} (hn : n < TS.length) :
    (tA TS n : Real) * wfun (gsum g (tI TS n) (tJ TS n)) + 323480 ≤
      Fg 7 BS TS g := by
  have hp := Finset.sum_le_sum (s := Finset.range 7)
    (fun r hr => mul_le_mul_of_nonneg_left
      (htheta r (Finset.mem_range.mp hr)) (Nat.cast_nonneg (BS.getD r 0)))
  have he : (∑ r ∈ Finset.range 7, (BS.getD r 0 : Real) * ((4 : Real)/5)) =
      323480 := by norm_num [BS,Finset.sum_range_succ]
  rw [he] at hp
  have ht := Finset.single_le_sum
    (f := fun n => (tA TS n : Real) * wfun (gsum g (tI TS n) (tJ TS n)))
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _))
    (Finset.mem_range.mpr hn)
  unfold Fg
  linarith

/-- The original clear guards plus the actual separated-gap pressure
    prove the stronger-or-low conclusion. No clear guard is promoted
    merely by changing the walk target. -/
theorem lowCover_root (Smax : Nat → Nat)
    (hS : ∀ r < 7, 805803 * SC ≤ BS.getD r 0 * Smax r)
    (cov : List (List (Nat × Nat × Bool)))
    (hcov : ∀ r < 7, coverChk 805003 (tA TS (ADJ.getD r 0))
      (SC/2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 7, 805803*4 ≤ tA TS (ADJ.getD r 0))
    (W : Nat) (hW : 7*KB ≤ W)
    (hrun : ∀ idx : Nat → Nat,
      (∀ r < 7, idx r < (badOf (cov.getD r [])).length) →
      CovBy 7 PR StrongOrLow (rootCl 7 PR.length W cov idx))
    (g : Nat → Real) (htheta : ∀ r < 7, (4 : Real)/5 ≤ g r) : StrongOrLow g := by
 classical
 have hg : ∀ r < 7, 0 ≤ g r := fun r hr => (by norm_num : (0 : Real) ≤ 4/5).trans (htheta r hr)
 have hSC : (0:ℝ) < SC := by norm_num [SC]
 by_cases hgood : ∃ r < 7, (805803 : ℝ) ≤ Fg 7 BS TS g
 · obtain ⟨r, -, h⟩ := hgood; exact Or.inl (Or.inl h)
 push_neg at hgood
 have hbad : ∀ r < 7, ∃ i, i < (badOf (cov.getD r [])).length ∧
     (((badOf (cov.getD r [])).getD i (0, 0)).1 : ℝ) / SC ≤ g r ∧ g r ≤ (((badOf (cov.getD r [])).getD i (0, 0)).2 : ℝ) / SC ∧
     ((badOf (cov.getD r [])).getD i (0, 0)).2 < KB := by
   intro r hr
   obtain ⟨hn, hi, hj⟩ := hADJ r hr
   have hsr : gsum g (tI TS (ADJ.getD r 0)) (tJ TS (ADJ.getD r 0)) = g r := by rw [hi, hj, gsum]; simp
   have hterm := Fg_ge_term (bs := BS) hg hn
   rw [hsr] at hterm
   by_cases hcut : (Smax r : ℝ) / SC ≤ g r
   · exfalso
     have hq := (Nat.cast_le (α := ℝ)).mpr (hS r hr); push_cast at hq
     have h1 : (805803 : ℝ) ≤ (BS.getD r 0 : ℝ) * g r := by
       have : (805803 : ℝ) ≤ (BS.getD r 0 : ℝ) * ((Smax r : ℝ) / SC) := by
         rw [mul_div_assoc', le_div_iff₀ hSC]; linarith
       exact this.trans (mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _))
     exact absurd (h1.trans (Fg_ge_lin hg hr)) (not_le.mpr (hgood r hr))
   push_neg at hcut
   rcases le_total (g r) (((SC / 2 : ℕ) : ℝ) / SC) with hw | hw
   · exfalso
     have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1 / 2 := by norm_num [SC]
     have h19 := wfun_window (g r) (hg r hr) (by rw [hhalf] at hw; exact hw)
     have hq := (Nat.cast_le (α := ℝ)).mpr (hwin r hr); push_cast at hq
     have h1 : (805803 : ℝ) ≤ (tA TS (ADJ.getD r 0) : ℝ) * wfun (g r) := by
       nlinarith [mul_le_mul_of_nonneg_left h19 (Nat.cast_nonneg (tA TS (ADJ.getD r 0)) : (0:ℝ) ≤ (tA TS (ADJ.getD r 0) : ℝ))]
     exact absurd (h1.trans hterm) (not_le.mpr (hgood r hr))
   rcases coverChk_sound 805003 (tA TS (ADJ.getD r 0)) (cov.getD r []) (SC / 2) (Smax r) (hcov r hr) (g r) hw hcut with
     hclear | ⟨s, hs, he, h1, h2, h3⟩
   · have hp := separated_pressure_term htheta hn
     rw [hsr] at hp
     have hstrong : (805803 : Real) ≤ Fg 7 BS TS g := by
       norm_num at hclear
       change (805003 : Real) ≤ (tA TS (ADJ.getD r 0) : Real)*wfun (g r) at hclear
       linarith
     exact absurd hstrong (not_le.mpr (hgood r hr))
   obtain ⟨i, hi', hsi⟩ := List.mem_iff_getElem.mp (badOf_mem hs he)
   refine ⟨i, hi', ?_, ?_, ?_⟩
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h1
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h2
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h3
 choose! idx hidx using hbad
 apply hrun idx (fun r hr => (hidx r hr).1) g
 refine incell_root hPR (W := W) (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk])
   (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk]) ?_ (fun r hr => ?_)
 · have h1 : ((sumR (rootCl 7 PR.length W cov idx).U 0 7 : ℕ) : ℝ) ≤ ((7 * KB : ℕ) : ℝ) := by
     rw [sumR_eq, Nat.zero_add]; push_cast
     calc ∑ r ∈ Finset.Ico 0 7, (((rootCl 7 PR.length W cov idx).U.getD r 0 : ℕ) : ℝ)
         ≤ ∑ r ∈ Finset.Ico 0 7, (KB : ℝ) := by
           apply Finset.sum_le_sum; intro r hr
           have hr' : r < 7 := (Finset.mem_Ico.mp hr).2
           simp only [rootCl]; rw [getD_map_range _ hr']
           exact_mod_cast (hidx r hr').2.2.2.le
       _ = (7 : ℝ) * KB := by simp
   exact (by exact_mod_cast h1 : sumR _ 0 7 ≤ 7 * KB).trans hW
 · simp only [rootCl]; rw [getD_map_range _ hr, getD_map_range _ hr]
   exact ⟨(hidx r hr).2.1, (hidx r hr).2.2.1⟩


open AMW.Cert.PC8CLData

def rootIndices (index : Nat) : Nat → Nat :=
  fun r => [0,index/16%2,index/8%2,index/4%2,index/2%2,index%2,0].getD r 0

def lowRootCell (index : Nat) : Cl := rootCl 7 21 1099511627776 COV (rootIndices index)

def lowRootBits : List Nat :=
  [WB0, WB1, WB2, WB3, WB4, WB5, WB6, WB7, WB8, WB9, WB10, WB11, WB12, WB13, WB14, WB15, WB16, WB17, WB18, WB19, WB20, WB21, WB22, WB23, WB24, WB25, WB26, WB27, WB28, WB29, WB30, WB31]

def lowRootEnds : List Nat :=
  [8086, 17530, 39365, 31362, 84866, 98514, 53623, 25468, 46633, 51837, 79730, 34388, 53774, 40814, 59698, 9391, 17940, 47838, 59890, 27034, 76566, 63562, 42914, 63478, 29321, 27057, 37691, 18175, 33587, 68280, 9278, 3740]

def lowRootCheck (index : Nat) : Bool :=
  decide (U (lowCoverWalk TOP BK TOPD BKD PT REG (lowRootBits.getD index 0) 128 1)
    (ofCl (lowRootCell index) 0) = lowRootEnds.getD index 0)

theorem lowRoot_check_0 : lowRootCheck 0 = true := by decide +kernel
theorem lowRoot_check_1 : lowRootCheck 1 = true := by decide +kernel
theorem lowRoot_check_2 : lowRootCheck 2 = true := by decide +kernel
theorem lowRoot_check_3 : lowRootCheck 3 = true := by decide +kernel
theorem lowRoot_check_4 : lowRootCheck 4 = true := by decide +kernel
theorem lowRoot_check_5 : lowRootCheck 5 = true := by decide +kernel
theorem lowRoot_check_6 : lowRootCheck 6 = true := by decide +kernel
theorem lowRoot_check_7 : lowRootCheck 7 = true := by decide +kernel
theorem lowRoot_check_8 : lowRootCheck 8 = true := by decide +kernel
theorem lowRoot_check_9 : lowRootCheck 9 = true := by decide +kernel
theorem lowRoot_check_10 : lowRootCheck 10 = true := by decide +kernel
theorem lowRoot_check_11 : lowRootCheck 11 = true := by decide +kernel
theorem lowRoot_check_12 : lowRootCheck 12 = true := by decide +kernel
theorem lowRoot_check_13 : lowRootCheck 13 = true := by decide +kernel
theorem lowRoot_check_14 : lowRootCheck 14 = true := by decide +kernel
theorem lowRoot_check_15 : lowRootCheck 15 = true := by decide +kernel
theorem lowRoot_check_16 : lowRootCheck 16 = true := by decide +kernel
theorem lowRoot_check_17 : lowRootCheck 17 = true := by decide +kernel
theorem lowRoot_check_18 : lowRootCheck 18 = true := by decide +kernel
theorem lowRoot_check_19 : lowRootCheck 19 = true := by decide +kernel
theorem lowRoot_check_20 : lowRootCheck 20 = true := by decide +kernel
theorem lowRoot_check_21 : lowRootCheck 21 = true := by decide +kernel
theorem lowRoot_check_22 : lowRootCheck 22 = true := by decide +kernel
theorem lowRoot_check_23 : lowRootCheck 23 = true := by decide +kernel
theorem lowRoot_check_24 : lowRootCheck 24 = true := by decide +kernel
theorem lowRoot_check_25 : lowRootCheck 25 = true := by decide +kernel
theorem lowRoot_check_26 : lowRootCheck 26 = true := by decide +kernel
theorem lowRoot_check_27 : lowRootCheck 27 = true := by decide +kernel
theorem lowRoot_check_28 : lowRootCheck 28 = true := by decide +kernel
theorem lowRoot_check_29 : lowRootCheck 29 = true := by decide +kernel
theorem lowRoot_check_30 : lowRootCheck 30 = true := by decide +kernel
theorem lowRoot_check_31 : lowRootCheck 31 = true := by decide +kernel

theorem lowRoot_checked (index : Nat) (hi : index < 32) : lowRootCheck index = true := by
  match index with
  | 0 => exact lowRoot_check_0
  | 1 => exact lowRoot_check_1
  | 2 => exact lowRoot_check_2
  | 3 => exact lowRoot_check_3
  | 4 => exact lowRoot_check_4
  | 5 => exact lowRoot_check_5
  | 6 => exact lowRoot_check_6
  | 7 => exact lowRoot_check_7
  | 8 => exact lowRoot_check_8
  | 9 => exact lowRoot_check_9
  | 10 => exact lowRoot_check_10
  | 11 => exact lowRoot_check_11
  | 12 => exact lowRoot_check_12
  | 13 => exact lowRoot_check_13
  | 14 => exact lowRoot_check_14
  | 15 => exact lowRoot_check_15
  | 16 => exact lowRoot_check_16
  | 17 => exact lowRoot_check_17
  | 18 => exact lowRoot_check_18
  | 19 => exact lowRoot_check_19
  | 20 => exact lowRoot_check_20
  | 21 => exact lowRoot_check_21
  | 22 => exact lowRoot_check_22
  | 23 => exact lowRoot_check_23
  | 24 => exact lowRoot_check_24
  | 25 => exact lowRoot_check_25
  | 26 => exact lowRoot_check_26
  | 27 => exact lowRoot_check_27
  | 28 => exact lowRoot_check_28
  | 29 => exact lowRoot_check_29
  | 30 => exact lowRoot_check_30
  | 31 => exact lowRoot_check_31
  | n+32 => omega

theorem lowRoot_end_nonzero (index : Nat) (hi : index < 32) :
    lowRootEnds.getD index 0 ≠ 0 := by
  interval_cases index <;> decide

theorem lowRoot_covered (index : Nat) (hi : index < 32) :
    CovBy 7 PR StrongOrLow (lowRootCell index) := by
  have hk := lowCoverWalk_sound lbS lbD ptS hR (lowRootBits.getD index 0) 128 1
  apply ofCl_ok hk
    (by simp [lowRootCell,rootCl]) (by simp [lowRootCell,rootCl])
    (by simp [lowRootCell,rootCl]) (by simp [lowRootCell,rootCl])
  have he := of_decide_eq_true (lowRoot_checked index hi)
  exact he ▸ lowRoot_end_nonzero index hi

theorem lowRun (idx : Nat → Nat)
    (h : ∀ r < 7, idx r < (badOf (COV.getD r [])).length) :
    CovBy 7 PR StrongOrLow (rootCl 7 21 1099511627776 COV idx) := by
  have h0 : idx 0 = 0 := by
    have hh := h 0 (by decide)
    have hn : (badOf (COV.getD 0 [])).length = 1 := by decide
    rw [hn] at hh
    omega
  have h6 : idx 6 = 0 := by
    have hh := h 6 (by decide)
    have hn : (badOf (COV.getD 6 [])).length = 1 := by decide
    rw [hn] at hh
    omega
  have h1 : idx 1 < 2 := by simpa [COV,badOf] using h 1 (by decide)
  have h2 : idx 2 < 2 := by simpa [COV,badOf] using h 2 (by decide)
  have h3 : idx 3 < 2 := by simpa [COV,badOf] using h 3 (by decide)
  have h4 : idx 4 < 2 := by simpa [COV,badOf] using h 4 (by decide)
  have h5 : idx 5 < 2 := by simpa [COV,badOf] using h 5 (by decide)
  let index := 16*idx 1+8*idx 2+4*idx 3+2*idx 4+idx 5
  have hi : index < 32 := by dsimp [index]; omega
  rw [rootCl_congr (idx' := rootIndices index)]
  · exact lowRoot_covered index hi
  · intro r hr
    interval_cases r <;> norm_num [rootIndices,index] <;> omega

theorem strong_or_low_half (g : Nat → Real)
    (htheta : ∀ r < 7, (4 : Real)/5 ≤ g r) : StrongOrLow g :=
  lowCover_root SMAX (by decide) COV (by decide +kernel) (by decide)
    1099511627776 (by decide) lowRun g htheta

theorem Fg_scalar (g : Nat → Real) :
    Fg 7 BS TS g = (SA : Real)*AMW.Cert.PC8CL.G (g 0) (g 1) (g 2) (g 3)
      (g 4) (g 5) (g 6) := by
  simp [Fg,BS,TS,tA,tI,tJ,gsum_range,AMW.Cert.PC8CL.G,SA,Finset.sum_range_succ]
  ring

theorem Fg_reflection (g : Nat → Real) :
    Fg 7 BS TS (reverseSeven g) = Fg 7 BS TS g := by
  rw [Fg_scalar,Fg_scalar]
  simp only [reverseSeven]
  norm_num only
  rw [AMW.Cert.PC8CL_G_rev]

def FrameCovered (g : Nat → Real) : Prop :=
  (805803 : Real) ≤ Fg 7 BS TS g ∨ ∃ label < 482, InCell 7 PR (lowCell label) g

theorem InCell_congr_first_seven {c : Cl} {g f : Nat → Real}
    (h : InCell 7 PR c g) (he : ∀ r < 7, g r = f r) : InCell 7 PR c f := by
  constructor
  · intro r hr
    simpa only [he r hr] using h.1 r hr
  · intro k hk
    have heq : gsum g (pI PR k) (pJ PR k) = gsum f (pI PR k) (pJ PR k) := by
      unfold gsum
      apply Finset.sum_congr rfl
      intro r hr
      exact he r (lt_of_lt_of_le (Finset.mem_Ico.mp hr).2 (hPR k hk).2)
    simpa only [heq] using h.2 k hk

theorem strong_or_low_full (g : Nat → Real)
    (htheta : ∀ r < 7, (4 : Real)/5 ≤ g r) : FrameCovered g := by
  by_cases horient : g 6 < g 0
  · have ht : ∀ r < 7, (4 : Real)/5 ≤ reverseSeven g r := by
      intro r hr
      exact htheta (6-r) (by omega)
    rcases strong_or_low_half (reverseSeven g) ht with (hstrong|hdir)|hlow
    · left
      rw [Fg_reflection] at hstrong
      exact hstrong
    · simp only [reverseSeven] at hdir
      norm_num only at hdir
      linarith
    · obtain ⟨label,hl,hcell⟩ := hlow
      right
      refine ⟨label+241,by omega,?_⟩
      rw [lowCell_reflected label hl]
      have hrev := InCell_reflection (lowCell label) (reverseSeven g) hcell
      have he : ∀ r < 7, reverseSeven (reverseSeven g) r = g r :=
        fun r hr => reverseSeven_involution g r hr
      exact InCell_congr_first_seven hrev he
  · rcases strong_or_low_half g htheta with (hstrong|hdir)|hlow
    · exact Or.inl hstrong
    · exact False.elim (horient hdir)
    · obtain ⟨label,hl,hcell⟩ := hlow
      exact Or.inr ⟨label,by omega,hcell⟩


theorem row_gsum_eq (g : Nat → Real) (i j : Nat) :
    RHWeilRecord.RowEvaluation.gsum g i j = gsum g i j := by rw [gsum_range]; rfl

theorem anchorRows_sound {f : Nat → Nat} {g : Nat → Real}
    {offset i j point value L U : Nat}
    (hlast : j+offset ≤ 8) (hsquare : (i+offset,j+offset) ∈ squareSpans)
    (hvalue : value < 2^96) (hpack : value = f point)
    (ht : TVal f L U point)
    (hlo : (L:Real)/SC ≤ gsum g (i+offset) (j+offset))
    (hhi : gsum g (i+offset) (j+offset) ≤ (U:Real)/SC) :
    ∀ row ∈ anchorRows offset i j point value L U,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*
        RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ (row.bound:Real) := by
  have hb0 : bits value 0 32 = lo32 (f point) := by
    rw [RHWeil.RecordSubmission.PointSoundness.bits_zero_32,hpack]
  have hb1 : bits value 32 32 = lo32 (hi32 (f point)) := by
    rw [RHWeil.RecordSubmission.PointSoundness.bits_32_32,hpack]
  have hb2 : bits value 64 32 = hi32 (hi32 (f point)) := by
    rw [RHWeil.RecordSubmission.PointSoundness.bits_64_32 hvalue,hpack]
  have hc := tangent_scaled_cuts ht (gsum g (i+offset) (j+offset)) hlo hhi
  rw [←hb0,←hb1,←hb2] at hc
  have hm1 := mul_le_mul_of_nonneg_left hc.1 (by norm_num : (0:Real) ≤ 5)
  have hm2 := mul_le_mul_of_nonneg_left hc.2 (by norm_num : (0:Real) ≤ 5)
  have hsq := RHWeilRecord.RowEvaluation.squareColumn_eval wfun g (i+offset) (j+offset) hsquare
  intro row hr
  simp only [anchorRows,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  all_goals
    rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hlast (Or.inr ⟨hsq.1,hsq.2.1⟩)]
    rw [hsq.2.2]
    simp only [row_gsum_eq]
    norm_num [RHWeilRecord.RowEvaluation.kernelScale,SC] at hm1 hm2 ⊢
    nlinarith [hm1,hm2]


theorem term_span_info {i j weight : Nat} (ht : (i,j,weight) ∈ terms) :
    i < j ∧ j ≤ 7 := by
  have hc : terms.all (fun t => decide (t.1 < t.2.1 ∧ t.2.1 ≤ 7)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp hc) (i,j,weight) ht)

theorem term_square_info {i j weight offset : Nat} (ht : (i,j,weight) ∈ terms)
    (ho : offset < 2) : (i+offset,j+offset) ∈ squareSpans := by
  have hc : terms.all (fun t => decide
      ((t.1,t.2.1) ∈ squareSpans ∧ (t.1+1,t.2.1+1) ∈ squareSpans)) = true := by decide
  have hp := of_decide_eq_true ((List.all_eq_true.mp hc) (i,j,weight) ht)
  interval_cases offset <;> simpa using (by first | exact hp.1 | exact hp.2)

theorem cellSpan_info {i j : Nat} (ht : (i,j) ∈ cellSpans) : i < j ∧ j ≤ 7 := by
  have hc : cellSpans.all (fun t => decide (t.1 < t.2 ∧ t.2 ≤ 7)) = true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp hc) (i,j) ht)

theorem frameRows_sound {g : Nat → Real} {label offset : Nat}
    (hl : label < 482) (ho : offset < 2)
    (hg : InCell 7 PR (lowCell label) (fun r => g (r+offset))) :
    ∀ row ∈ frameRows label offset,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
  intro row hr
  simp only [frameRows,List.mem_append,List.mem_flatMap] at hr
  rcases hr with ⟨span,hm,hr⟩ | ⟨term,hm,hr⟩
  · rcases span with ⟨i,j⟩
    have hs := cellSpan_info hm
    have hb := lowCell_spanbounds label (fun r => g (r+offset)) hg i j hs.1 hs.2
    rw [gsum_shift] at hb
    have hlast : j+offset ≤ 8 := by omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      change (∑ c ∈ Finset.range 42, (_:IntegerRow).coeff c*RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hlast (Or.inl rfl)]
      rw [row_gsum_eq]
      norm_num [SC] at hb ⊢
      nlinarith [hb.1,hb.2]
  · rcases term with ⟨i,j,weight⟩
    have hs := term_span_info hm
    have hsqmem := term_square_info hm ho
    have hsq := RHWeilRecord.RowEvaluation.squareColumn_eval wfun g (i+offset) (j+offset) hsqmem
    have hb := lowCell_tightbounds label i j (fun r => g (r+offset)) hg hs.1 hs.2
    rw [gsum_shift] at hb
    have hlast : j+offset ≤ 8 := by omega
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · change (∑ c ∈ Finset.range 42, (_:IntegerRow).coeff c*RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hlast (Or.inr ⟨hsq.1,hsq.2.1⟩)]
      rw [hsq.2.2]
      have hw := RHWeil.RecordSubmission.PointSoundness.old_constant_bound hl hm hb.1 hb.2
      change (bits (termAtom label i j) 35 32 : Real)/10000000000 ≤ wfun (gsum g (i+offset) (j+offset)) at hw
      rw [row_gsum_eq]
      norm_num [RHWeilRecord.RowEvaluation.kernelScale] at hw ⊢
      nlinarith
    · rcases List.mem_flatMap.mp hr with ⟨point,hpoint,hrow⟩
      exact anchorRows_sound hlast hsqmem
        (RHWeil.RecordSubmission.PointSoundness.pointValue_lt point)
        (RHWeil.RecordSubmission.PointSoundness.old_point_value_eq hl hm hpoint)
        (RHWeil.RecordSubmission.PointSoundness.old_tangent_value hl hm hpoint)
        hb.1 hb.2 row hrow


theorem extraRows_sound {g : Nat → Real} {index : Nat}
    (hi : index < 1224)
    (hl : ((pairPacks[index]?).getD (0,0,0,0,0,0)).1 < 482)
    (hr : ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1 < 482)
    (hgl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hgr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1))) :
    let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
    ∀ row ∈ extraRows pair.1 pair.2.1 pair.2.2.2.2.1 pair.2.2.2.2.2,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  change ∀ row ∈ extraRows pair.1 pair.2.1 pair.2.2.2.2.1 pair.2.2.2.2.2, _
  intro row hrow
  simp only [extraRows,List.mem_flatMap] at hrow
  obtain ⟨k,hk,hrow⟩ := hrow
  have hk' := List.mem_range.mp hk
  let atom := bits pair.2.2.2.2.2 (15*k) 15
  let offset := bits atom 0 1
  let i := bits atom 1 3
  let j := bits atom 4 3
  let packet := (catalog[bits atom 7 8]?).getD 0
  let p := bits packet 0 20
  let value := bits packet 20 96
  let label := if offset = 0 then pair.1 else pair.2.1
  have ho : offset < 2 := RHWeil.RecordSubmission.PointSoundness.bits_lt_two_pow atom 0 1
  have hspan := RHWeil.RecordSubmission.PointSoundness.extra_span_valid hi hk'
  change ∃ weight, (i,j,weight) ∈ terms at hspan
  obtain ⟨weight,ht⟩ := hspan
  have hs := term_span_info ht
  have hsq := term_square_info ht ho
  have hlast : j+offset ≤ 8 := by omega
  have hlabel : label < 482 := by dsimp [label]; split_ifs <;> assumption
  have hg : InCell 7 PR (lowCell label) (fun r => g (r+offset)) := by
    by_cases hz : offset = 0
    · simpa [label,hz] using hgl
    · have hz' : offset = 1 := by omega
      simpa [label,hz,hz'] using hgr
  have hb := lowCell_tightbounds label i j (fun r => g (r+offset)) hg hs.1 hs.2
  rw [gsum_shift] at hb
  have hbL : ((min (tightLower label i j) p:Nat):Real)/SC ≤ gsum g (i+offset) (j+offset) := by
    exact (div_le_div_of_nonneg_right (by exact_mod_cast Nat.min_le_left (tightLower label i j) p)
      (by norm_num [SC])).trans hb.1
  have hbU : gsum g (i+offset) (j+offset) ≤ ((max (tightUpper label i j) p:Nat):Real)/SC := by
    exact hb.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_max_left (tightUpper label i j) p)
      (by norm_num [SC]))
  have hpv := RHWeil.RecordSubmission.PointSoundness.extra_point_value_eq hi hk'
  have hpt := RHWeil.RecordSubmission.PointSoundness.extra_tangent_value hi hk'
  change value = PT p at hpv
  change TVal PT (min (tightLower label i j) p) (max (tightUpper label i j) p) p at hpt
  exact anchorRows_sound hlast hsq
    (RHWeil.RecordSubmission.PointSoundness.catalog_value_lt packet)
    hpv hpt hbL hbU row hrow



theorem selectedRow_sound {g : Nat → Real} {rows : List IntegerRow}
    (hrows : ∀ row ∈ rows,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real))
    (index : Nat) :
      (∑ c ∈ Finset.range 42, ((rows.getD index default).coeff c:Real)*actualValue g c) ≤
        ((rows.getD index default).bound:Real) := by
  by_cases hi : index < rows.length
  · rw [List.getD_eq_getElem rows default hi]
    exact hrows _ (List.getElem_mem hi)
  · rw [List.getD_eq_default rows default (Nat.le_of_not_lt hi)]
    have hb : (default : IntegerRow).bound = 0 := rfl
    have hc : ∀ i, (default : IntegerRow).coeff i = 0 := by
      intro i
      change (if i < 8 then if 0 ≤ i ∧ i < 0 then (0:Int) else 0 else if i = 0 then 0 else 0) = 0
      simp
    simp [hb,hc]

theorem representative_real_bound {g : Nat → Real} {index : Nat}
    (hi : index < 1224)
    (hc : integerCertificateCheck index = true)
    (hl : ((pairPacks[index]?).getD (0,0,0,0,0,0)).1 < 482)
    (hr : ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1 < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hgr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1))) :
    (805260:Real)/100000000 ≤
      scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let rows := frameRows pair.1 0 ++ frameRows pair.2.1 1 ++
    extraRows pair.1 pair.2.1 pair.2.2.2.2.1 pair.2.2.2.2.2
  let multipliers := (decodeMultipliers pair.2.2.1 pair.2.2.2.1).map fun p =>
    let row := rows.getD p.1 default
    let lambda : Int := p.2 * (if row.geometric then 10000000000 else 1)
    (row,lambda)
  let lo := fun column =>
    if column < 8 then max (4*32768) (-((pairClosure pair.1 pair.2.1)[9*(column+1)+column]?).getD 0) else 0
  let up := fun column =>
    if column < 8 then ((pairClosure pair.1 pair.2.1)[9*column+column+1]?).getD 0 else 5*10000000000*32768
  have hrows : ∀ row ∈ rows,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
    intro row hm
    simp only [rows,List.mem_append] at hm
    rcases hm with (hm|hm)|hm
    · exact frameRows_sound hl (by decide) (by simpa only [Nat.add_zero] using hgl) row hm
    · exact frameRows_sound hr (by decide) hgr row hm
    · exact extraRows_sound hi hl hr hgl hgr row hm
  have hlam : ∀ r ∈ multipliers, 0 ≤ r.2 := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    dsimp only
    split_ifs <;> positivity
  have hselected : ∀ r ∈ multipliers,
      (∑ c ∈ Finset.range 42, (r.1.coeff c:Real)*actualValue g c) ≤ (r.1.bound:Real) := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact selectedRow_sound hrows p.1
  have hbox := actualValue_box htheta hgl hgr
  have hnumeric : 2*805260*(5*10000000000*32768)*1000000000 ≤ integerCertificateLower index :=
    of_decide_eq_true hc
  have heq : integerCertificateLower index = RHWeilRecord.SparseDualSoundness.checkerL 42 multipliers
      (fun c => 1000000000*objectiveCoeff c) (fun r c => r.1.coeff c)
      (fun r => r.1.bound) (fun r => r.2) lo up := rfl
  rw [heq] at hnumeric
  have hbound := RHWeilRecord.SparseDualSoundness.threshold_sound 42 multipliers
    (fun c => 1000000000*objectiveCoeff c) (actualValue g) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) lo up
    (2*805260*(5*10000000000*32768)*1000000000) hnumeric hlam hselected
    (fun c hc => (hbox c hc).1) (fun c hc => (hbox c hc).2)
  simp only [Int.cast_mul,Int.cast_ofNat] at hbound
  simp_rw [mul_assoc] at hbound
  rw [←Finset.mul_sum,integerObjective_identity] at hbound
  norm_num [kernelScale] at hbound ⊢
  nlinarith


theorem reflectedCell_involution {c : Cl}
    (hL : c.L.length = 7) (hU : c.U.length = 7)
    (hA : c.A.length = 21) (hB : c.B.length = 21) :
    reflectedCell (reflectedCell c) = c := by
  apply cell_ext
  · apply list_ext_getD
    · simp [reflectedCell,hL]
    · intro i hi hj
      have hi' : i < 7 := by simpa [reflectedCell,reflectionSpan] using hi
      simp only [reflectedCell]
      rw [getD_map_range _ hi',getD_map_range _ (show 6-i<7 by omega)]
      rw [show 6-(6-i)=i by omega]
  · apply list_ext_getD
    · simp [reflectedCell,hU]
    · intro i hi hj
      have hi' : i < 7 := by simpa [reflectedCell,reflectionSpan] using hi
      simp only [reflectedCell]
      rw [getD_map_range _ hi',getD_map_range _ (show 6-i<7 by omega)]
      rw [show 6-(6-i)=i by omega]
  · apply list_ext_getD
    · simp [reflectedCell,reflectionSpan,hA]
    · intro i hi hj
      have hi' : i < 21 := by simpa [reflectedCell,reflectionSpan] using hi
      interval_cases i <;> simp [reflectedCell,reflectionSpan]
  · apply list_ext_getD
    · simp [reflectedCell,reflectionSpan,hB]
    · intro i hi hj
      have hi' : i < 21 := by simpa [reflectedCell,reflectionSpan] using hi
      interval_cases i <;> simp [reflectedCell,reflectionSpan]

theorem lowCell_reflection_all {label : Nat} (hl : label < 482) :
    lowCell (reflectionLabel label) = reflectedCell (lowCell label) := by
  by_cases hsmall : label < 241
  · simpa [reflectionLabel,hsmall] using lowCell_reflected label hsmall
  · have hk : label-241 < 241 := by omega
    have he : label-241+241=label := by omega
    have href := lowCell_reflected (label-241) hk
    rw [he] at href
    rw [href]
    have hinv := reflectedCell_involution (c:=lowCell (label-241))
      (by simp [lowCell]) (by simp [lowCell])
      (by simp [lowCell,longSpans]) (by simp [lowCell,longSpans])
    rw [hinv]
    simp [reflectionLabel,hsmall]

def reverseEight (g : Nat → Real) (r : Nat) : Real := g (7-r)

theorem reverseEight_scalar (g : Nat → Real) :
    scalarF9 (reverseEight g 0) (reverseEight g 1) (reverseEight g 2) (reverseEight g 3)
      (reverseEight g 4) (reverseEight g 5) (reverseEight g 6) (reverseEight g 7) =
    scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  simp only [reverseEight]
  norm_num only
  exact scalarF9_reflection _ _ _ _ _ _ _ _

theorem reverseEight_cells {g : Nat → Real} {left right : Nat}
    (hl : left < 482) (hr : right < 482)
    (hgl : InCell 7 PR (lowCell left) g)
    (hgr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    InCell 7 PR (lowCell (reflectionLabel right)) (reverseEight g) ∧
      InCell 7 PR (lowCell (reflectionLabel left)) (fun r => reverseEight g (r+1)) := by
  constructor
  · rw [lowCell_reflection_all hr]
    apply InCell_congr_first_seven (InCell_reflection (lowCell right) (fun r => g (r+1)) hgr)
    intro r hr
    change g (6-r+1) = g (7-r)
    congr 1
    omega
  · rw [lowCell_reflection_all hl]
    apply InCell_congr_first_seven (InCell_reflection (lowCell left) g hgl)
    intro r hr
    change g (6-r) = g (7-(r+1))
    congr 1
    omega


theorem old_frame_lower (g : Nat → Real) (h : ∀ r < 7, 0 ≤ g r) :
    (805003:Real) ≤ Fg 7 BS TS g := by
  have hc := AMW.Cert.PC8CL_cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)
    (h 0 (by decide)) (h 1 (by decide)) (h 2 (by decide)) (h 3 (by decide))
    (h 4 (by decide)) (h 5 (by decide)) (h 6 (by decide))
  rw [Fg_scalar]
  norm_num [cN,SA] at hc ⊢
  nlinarith

theorem scalar_from_frames (g : Nat → Real) :
    scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) =
      (Fg 7 BS TS g+Fg 7 BS TS (fun r => g (r+1)))/(2*SA)+
        2*wfun (g 0+g 1+g 2+g 3+g 4+g 5+g 6+g 7) := by
  rw [Fg_scalar,Fg_scalar]
  simp [scalarF9,SA]
  ring

theorem local_from_low_pairs
    (hpair : ∀ (g : Nat → Real) (left right : Nat), left < 482 → right < 482 →
      (∀ r < 8, (4:Real)/5 ≤ g r) → InCell 7 PR (lowCell left) g →
      InCell 7 PR (lowCell right) (fun r => g (r+1)) →
      (805260:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7))
    (g : Fin 8 → Real) (hg : ∀ r, (4:Real)/5 ≤ g r) :
    (805260:Real)/100000000 ≤ Zeta23Ext.BridgeW.Fw W9 g := by
  let f := fun r : Nat => [g 0,g 1,g 2,g 3,g 4,g 5,g 6,g 7].getD r 0
  have hf : ∀ r < 8, (4:Real)/5 ≤ f r := by
    intro r hr
    have he : f r = g ⟨r,hr⟩ := by interval_cases r <;> rfl
    rw [he]
    exact hg ⟨r,hr⟩
  have hn0 : ∀ r < 7, 0 ≤ f r := by intro r hr; have := hf r (by omega); linarith
  have hn1 : ∀ r < 7, 0 ≤ f (r+1) := by intro r hr; have := hf (r+1) (by omega); linarith
  have ho0 := old_frame_lower f hn0
  have ho1 := old_frame_lower (fun r => f (r+1)) hn1
  have hnon : 0 ≤ wfun (f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7) := sq_nonneg _
  rw [W9_scalar_identity]
  change (805260:Real)/100000000 ≤
    scalarF9 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  rcases strong_or_low_full f (fun r hr => hf r (by omega)) with hstrong | hlow
  · rw [scalar_from_frames]
    norm_num [SA] at ho0 ho1 hstrong ⊢
    nlinarith
  · rcases strong_or_low_full (fun r => f (r+1)) (fun r hr => hf (r+1) (by omega)) with hstrong | hlow'
    · rw [scalar_from_frames]
      norm_num [SA] at ho0 ho1 hstrong ⊢
      nlinarith
    · obtain ⟨left,hl,hcell⟩ := hlow
      obtain ⟨right,hr,hcell'⟩ := hlow'
      exact hpair f left right hl hr hf hcell hcell'


theorem reflectionLabel_lt {label : Nat} (hl : label < 482) : reflectionLabel label < 482 := by
  unfold reflectionLabel
  split_ifs <;> omega

theorem low_pair_bound_from_verified_families
    (hgeometry : ∀ (g : Nat → Real) (left right : Nat), left < 482 → right < 482 →
      (∀ r < 8, (4:Real)/5 ≤ g r) → InCell 7 PR (lowCell left) g →
      InCell 7 PR (lowCell right) (fun r => g (r+1)) →
      ∃ index < 2399, pairLabelAt index = pairLabel left right)
    (horbit : ∀ index < 2399, orbitCheck index = true)
    (hshape : ∀ index < 1224,
      let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
      packet.1 < 482 ∧ packet.2.1 < 482 ∧ representativeLabel index = pairLabel packet.1 packet.2.1)
    (hnumeric : ∀ index < 1224, integerCertificateCheck index = true)
    (g : Nat → Real) (left right : Nat) (hl : left < 482) (hr : right < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell left) g)
    (hgr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    (805260:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  obtain ⟨index,hi,heindex⟩ := hgeometry g left right hl hr htheta hgl hgr
  have hoc := horbit index hi
  simp only [orbitCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hoc
  let rep := orbitIndexAt index / 2
  have hrep : rep < 1224 := hoc.1
  let packet := (pairPacks[rep]?).getD (0,0,0,0,0,0)
  have hs := hshape rep hrep
  change packet.1 < 482 ∧ packet.2.1 < 482 ∧ representativeLabel rep = pairLabel packet.1 packet.2.1 at hs
  have he := hoc.2
  rw [heindex] at he
  by_cases heven : orbitIndexAt index % 2 = 0
  · rw [if_pos heven,hs.2.2] at he
    have hlabels := RHWeilRecord.GeometryCoverage.pairLabel_injective hl hr hs.1 hs.2.1 he
    have hcells0 : InCell 7 PR (lowCell packet.1) g := by simpa only [hlabels.1] using hgl
    have hcells1 : InCell 7 PR (lowCell packet.2.1) (fun r => g (r+1)) := by simpa only [hlabels.2] using hgr
    exact representative_real_bound hrep (hnumeric rep hrep) hs.1 hs.2.1 htheta hcells0 hcells1
  · rw [if_neg heven,hs.2.2,RHWeilRecord.GeometryCoverage.reflectedPair_pairLabel hs.1 hs.2.1] at he
    have hlabels := RHWeilRecord.GeometryCoverage.pairLabel_injective hl hr
      (reflectionLabel_lt hs.2.1) (reflectionLabel_lt hs.1) he
    have hrevcells := reverseEight_cells hl hr hgl hgr
    have href0 : reflectionLabel right = packet.1 := by
      rw [hlabels.2,reflectionLabel_involution hs.1]
    have href1 : reflectionLabel left = packet.2.1 := by
      rw [hlabels.1,reflectionLabel_involution hs.2.1]
    have ht : ∀ r < 8, (4:Real)/5 ≤ reverseEight g r := by
      intro r hr
      exact htheta (7-r) (by omega)
    have hcells0 : InCell 7 PR (lowCell packet.1) (reverseEight g) := by
      simpa only [href0] using hrevcells.1
    have hcells1 : InCell 7 PR (lowCell packet.2.1) (fun r => reverseEight g (r+1)) := by
      simpa only [href1] using hrevcells.2
    have hb := representative_real_bound hrep (hnumeric rep hrep) hs.1 hs.2.1 ht hcells0 hcells1
    rw [reverseEight_scalar] at hb
    exact hb



/- The only inputs to the generic transport are discharged by the actual
   kernel-checked complete geometry, orbit, shape, and original numeric families. -/
theorem low_pair_bound (g : Nat → Real) (left right : Nat)
    (hl : left < 482) (hr : right < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell left) g)
    (hgr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    (805260:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  apply low_pair_bound_from_verified_families
    (horbit := orbit_coverage) (hshape := representative_packet_shape)
    (hnumeric := all_integer_representatives) _ g left right hl hr htheta hgl hgr
  intro f l r hl hr ht hfl hfr
  apply RHWeilRecord.GeometryCoverage.physical_pair_covered hl hr
  change RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential f) (initialPairBounds l r)
  exact initialPotentialBound ht hfl hfr

/-- Unconditional local c260 certificate for the actual fixed nine-point weights. -/
theorem W9_local_certificate (g : Fin 8 → Real) (hg : ∀ r, (4:Real)/5 ≤ g r) :
    (805260:Real)/100000000 ≤ Zeta23Ext.BridgeW.Fw W9 g :=
  local_from_low_pairs low_pair_bound g hg

end RHWeil.RecordSubmission.FiniteCertificate
