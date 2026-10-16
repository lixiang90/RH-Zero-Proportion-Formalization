/- SPDX-License-Identifier: Apache-2.0
Exact rational interval arithmetic for finite window certificates.
All scalar operations have ordinary real-number soundness proofs. The
checker may widen an interval after each operation to keep its data small.
-/
import StructuralGoal20261016.WindowSincJet
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowRationalInterval

abbrev QI := ℚ × ℚ
def Holds (I : QI) (x : ℝ) : Prop := (I.1:ℝ) ≤ x ∧ x ≤ (I.2:ℝ)
def point (q : ℚ) : QI := (q,q)
def add (I J : QI) : QI := (I.1+J.1,I.2+J.2)
def neg (I : QI) : QI := (-I.2,-I.1)
def sub (I J : QI) : QI := add I (neg J)
def mul (I J : QI) : QI :=
 (min (min (I.1*J.1) (I.1*J.2)) (min (I.2*J.1) (I.2*J.2)),
  max (max (I.1*J.1) (I.1*J.2)) (max (I.2*J.1) (I.2*J.2)))
def inv (I : QI) : QI := (1/I.2,1/I.1)
def div (I J : QI) : QI := mul I (inv J)
def scale : ℚ := 10^30
def floorQ (q : ℚ) : ℚ := ((⌊q*scale⌋:ℤ):ℚ)/scale
def ceilQ (q : ℚ) : ℚ := ((⌈q*scale⌉:ℤ):ℚ)/scale
def round (I : QI) : QI := (floorQ I.1,ceilQ I.2)
def radd (I J : QI) : QI := round (add I J)
def rneg (I : QI) : QI := round (neg I)
def rsub (I J : QI) : QI := round (sub I J)
def rmul (I J : QI) : QI := round (mul I J)
def rdiv (I J : QI) : QI := round (div I J)

theorem point_sound (q : ℚ) : Holds (point q) (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem widen {I J : QI} {x : ℝ} (h : Holds I x)
 (hl : J.1 ≤ I.1) (hu : I.2 ≤ J.2) : Holds J x := by
 have hl' : (J.1:ℝ) ≤ (I.1:ℝ) := by exact_mod_cast hl
 have hu' : (I.2:ℝ) ≤ (J.2:ℝ) := by exact_mod_cast hu
 exact ⟨hl'.trans h.1, h.2.trans hu'⟩

theorem floorQ_le (q : ℚ) : floorQ q ≤ q := by
 rw [floorQ, div_le_iff₀ (show 0 < scale by norm_num [scale])]
 exact Int.floor_le _

theorem le_ceilQ (q : ℚ) : q ≤ ceilQ q := by
 rw [ceilQ, le_div_iff₀ (show 0 < scale by norm_num [scale])]
 exact Int.le_ceil _

theorem round_sound {I : QI} {x : ℝ} (h : Holds I x) : Holds (round I) x :=
 widen h (floorQ_le _) (le_ceilQ _)

theorem add_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (add I J) (x+y) := by
 unfold Holds add at *
 push_cast
 exact ⟨add_le_add hx.1 hy.1,add_le_add hx.2 hy.2⟩

theorem neg_sound {I : QI} {x : ℝ} (hx : Holds I x) : Holds (neg I) (-x) := by
 unfold Holds neg at *
 push_cast
 exact ⟨neg_le_neg hx.2,neg_le_neg hx.1⟩

theorem sub_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (sub I J) (x-y) := by
 simpa only [sub, sub_eq_add_neg] using add_sound hx (neg_sound hy)

theorem mul_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
 min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
 x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
 have hlin (v : ℝ) : min (v*c) (v*d) ≤ v*y ∧ v*y ≤ max (v*c) (v*d) := by
   by_cases hv : 0 ≤ v
   · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hv),
       (mul_le_mul_of_nonneg_left hy.2 hv).trans (le_max_right _ _)⟩
   · have hv' : v ≤ 0 := le_of_not_ge hv
     exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hv'),
       (mul_le_mul_of_nonpos_left hy.1 hv').trans (le_max_left _ _)⟩
 have ha := hlin a
 have hb := hlin b
 by_cases hy0 : 0 ≤ y
 · exact ⟨((min_le_left _ _).trans ha.1).trans (mul_le_mul_of_nonneg_right hx.1 hy0),
     (mul_le_mul_of_nonneg_right hx.2 hy0).trans (hb.2.trans (le_max_right _ _))⟩
 · have hy0' : y ≤ 0 := le_of_not_ge hy0
   exact ⟨((min_le_right _ _).trans hb.1).trans (mul_le_mul_of_nonpos_right hx.2 hy0'),
     (mul_le_mul_of_nonpos_right hx.1 hy0').trans (ha.2.trans (le_max_left _ _))⟩

theorem mul_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (mul I J) (x*y) := by
 unfold Holds mul
 push_cast
 exact mul_bounds hx hy

theorem inv_sound {I : QI} {x : ℝ} (hx : Holds I x) (hnz : 0 < I.1 ∨ I.2 < 0) :
 Holds (inv I) (1/x) := by
 unfold Holds inv at *
 push_cast
 rcases hnz with hp | hn
 · have hp' : (0:ℝ) < I.1 := by exact_mod_cast hp
   exact ⟨one_div_le_one_div_of_le (hp'.trans_le hx.1) hx.2,
     one_div_le_one_div_of_le hp' hx.1⟩
 · have hn' : (I.2:ℝ) < 0 := by exact_mod_cast hn
   exact ⟨one_div_le_one_div_of_neg_of_le hn' hx.2,
     one_div_le_one_div_of_neg_of_le (hx.2.trans_lt hn') hx.1⟩

theorem div_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y)
 (hnz : 0 < J.1 ∨ J.2 < 0) : Holds (div I J) (x/y) := by
 simpa only [div, div_eq_mul_inv, one_div, one_mul] using mul_sound hx (inv_sound hy hnz)

theorem radd_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (radd I J) (x+y) := round_sound (add_sound hx hy)

theorem rneg_sound {I : QI} {x : ℝ} (hx : Holds I x) :
 Holds (rneg I) (-x) := round_sound (neg_sound hx)

theorem rsub_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (rsub I J) (x-y) := round_sound (sub_sound hx hy)

theorem rmul_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y) :
 Holds (rmul I J) (x*y) := round_sound (mul_sound hx hy)

theorem rdiv_sound {I J : QI} {x y : ℝ} (hx : Holds I x) (hy : Holds J y)
 (hnz : 0 < J.1 ∨ J.2 < 0) : Holds (rdiv I J) (x/y) := round_sound (div_sound hx hy hnz)

theorem nonzero {I : QI} {x : ℝ} (hx : Holds I x) (hnz : 0 < I.1 ∨ I.2 < 0) : x ≠ 0 := by
 rcases hnz with hp | hn
 · have hp' : (0:ℝ) < I.1 := by exact_mod_cast hp
   exact (hp'.trans_le hx.1).ne'
 · have hn' : (I.2:ℝ) < 0 := by exact_mod_cast hn
   exact (hx.2.trans_lt hn').ne

def pow (I : QI) : ℕ → QI
 | 0 => point 1
 | r+1 => mul (pow I r) I

theorem pow_sound {I : QI} {x : ℝ} (hx : Holds I x) (r : ℕ) : Holds (pow I r) (x^r) := by
 induction r with
 | zero => simpa only [pow, pow_zero, Rat.cast_one] using point_sound 1
 | succ r ih => simpa only [pow, pow_succ] using mul_sound ih hx

theorem sinc_zero_sound {Z S : QI} {z : ℝ} (hz : Holds Z z)
 (hs : Holds S (Real.sin z)) (hnz : 0 < Z.1 ∨ Z.2 < 0) :
 Holds (div S Z) (WindowSincJet.sincMoment 0 z) := by
 rw [WindowSincJet.sincMoment_zero_order, Real.sinc_of_ne_zero (nonzero hz hnz)]
 exact div_sound hs hz hnz

theorem sinc_succ_sound {Z C R : QI} {z : ℝ} {r : ℕ}
 (hz : Holds Z z) (hc : Holds C (Real.cos (z+(r:ℝ)*π/2)))
 (hr : Holds R (WindowSincJet.sincMoment r z)) (hnz : 0 < Z.1 ∨ Z.2 < 0) :
 Holds (div (sub C (mul (point (r+1)) R)) Z) (WindowSincJet.sincMoment (r+1) z) := by
 rw [WindowSincJet.sincMoment_succ (nonzero hz hnz)]
 exact div_sound (sub_sound hc (mul_sound (by exact_mod_cast point_sound (r+1:ℚ)) hr)) hz hnz

#print axioms mul_sound
#print axioms sinc_succ_sound
end StructuralGoal20261016.WindowRationalInterval
end
