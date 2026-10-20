/- PREPARATION ONLY: W9A2 quantitative finite-state walk.
Official source 241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7.
All original numerical payloads, kernel, guards, topology and cursors remain
unchanged. Each numerical leaf checks a state-dependent natural target.
No compiler or kernel has checked this generated variant yet.
-/
/-
R. Arun Chandru
arun.chandru@gmail.com
https://github.com/arun-chandru
https://x.com/arunchandru
https://researchgate.net/profile/R_Chandru
-/
/-
Copyright (c) 2026 R. Arun Chandru, for original contributions.
SPDX-License-Identifier: Apache-2.0
-/
import ChallengeDeps
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zeta23.PrimeSideA.EndsE1
import Zeta23.Taper.Norms
import Zeta23.ThmD.Concrete
import Zeta23.ThmD.Limit
import Zeta23.ThmD.Mult
import Zeta23.ThmD.Window
import Zeta23.ThmD.WindowCore
import Zeta23.ThmD.ZeroSideD
import Zeta23.ZeroSide.RankTraceMult
-- The zfNat64 block below is reproduced unmodified from critical-strip-exclusion-attempt-1 (Zero Forge / @zkvoxels, GitHub cafeai), Apache-2.0.
/-
Transparent source packing for finite-certificate numeral payloads.

The alphabet is A-Z, a-z, 0-9, +, _.  Its digits represent an unsigned
integer in radix 64, most significant digit first, without byte padding.
It contains no quote, escape, slash, hyphen, whitespace or comment marker.
The explicit bit length rejects truncation, excess leading digits and
noncanonical leading zeroes.  Each literal is bounded to 65536 bits.

This is ordinary elaborator syntax sugar.  The macro can return only the
decimal numeral token produced by Lean.Syntax.mkNumLit.  The kernel receives
the same ordinary Nat numeral as in the unpacked file; no decoding function,
new axiom, evaluation oracle or altered certificate evaluator occurs in its
proof terms.  Every inherited finite check and independent kernel replay is
still required.  The producer separately audits exact integer roundtrips.
-/
namespace ZeroForgePackedNat

/- Work with bytes so non-ASCII input is rejected rather than normalized.
   Every accepted branch yields exactly one of the 64 declared digits. -/
private def digit64 (byte : UInt8) : Except String Nat :=
  let code := byte.toNat
  if 65 ≤ code ∧ code ≤ 90 then
    .ok (code - 65)
  else if 97 ≤ code ∧ code ≤ 122 then
    .ok (code - 97 + 26)
  else if 48 ≤ code ∧ code ≤ 57 then
    .ok (code - 48 + 52)
  else if code = 43 then
    .ok 62
  else if code = 95 then
    .ok 63
  else
    .error "zfNat64: invalid ASCII digit"

/- This function is total and pure.  The source bit bound and exact encoded
   length are checked before iterating.  No back-references, allocation sizes
   supplied by the payload, or unchecked buffer indexes are involved. -/
def decode64 (bits : Nat) (text : String) : Except String Nat := do
  if bits > 65536 then
    throw "zfNat64: bit length exceeds the source-packing bound"
  if bits = 0 then
    if text = "A" then
      return 0
    else
      throw "zfNat64: zero must have the unique encoding A"
  let bytes := text.toByteArray
  if bytes.size != (bits + 5) / 6 then
    throw "zfNat64: encoded length does not match the declared bit length"
  let leadingBits := (bits - 1) % 6 + 1
  let lower := Nat.shiftLeft 1 (leadingBits - 1)
  let upper := Nat.shiftLeft 1 leadingBits
  let mut first := true
  let mut value := 0
  for byte in bytes do
    let digit ← digit64 byte
    if first then
      if digit < lower ∨ upper ≤ digit then
        throw "zfNat64: leading digit does not match the declared bit length"
      first := false
    value := Nat.add (Nat.shiftLeft value 6) digit
  return value

end ZeroForgePackedNat

/- MacroM is deliberately confined to constructing one ordinary numeral AST.
   A rejected payload raises an elaboration error at its string literal. -/
macro "zfNat64 " bits:num payload:str : term => do
  match ZeroForgePackedNat.decode64 bits.getNat payload.getString with
  | .ok value =>
    return ⟨(Lean.Syntax.mkNumLit (toString value)).raw⟩
  | .error message =>
    Lean.Macro.throwErrorAt payload message

set_option Elab.async false
section
set_option linter.all false
set_option Elab.async false
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace AMW
open Zeta23
def cAMn : ℕ → ℤ
 | 0 => 1000000000
 | 1 => 13686387
 | 2 => -15900768
 | 3 => 5481450
 | 4 => 6757377
 | 5 => -608034
 | 6 => 4418860
 | 7 => -6059090
 | 8 => 2213086
 | 9 => -6211618
 | 10 => 5410132
 | 11 => -2059537
 | 12 => -1000
 | _ => 0
def cAM (j : ℕ) : ℚ := (cAMn j : ℚ) / 10 ^ 9
def ωAM (j : ℕ) : ℝ := if j = 0 then Real.sqrt 2 else 2 * π * j
def vAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.cos (ωAM j * s)
def MAM : ℝ := 5 / 4
def phiW (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ :=
 Real.sqrt (vAM (u / L) / MAM) * Taper.phi ϱ L w u
def fW (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (vAM (u / L) / MAM)
theorem phiW_eq_mul (ϱ : ℝ → ℝ) (L w u : ℝ) : phiW ϱ L w u = fW L u * Taper.phi ϱ L w u := rfl
def localFunW (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
 AdmWindow.localFun (phiW P.ϱ (P.L T) P.w) (P.L T)
theorem MAM_pos : (0 : ℝ) < MAM := by norm_num [MAM]
theorem cAM_zero : (cAM 0 : ℝ) = 1 := by norm_num [cAM, cAMn]
theorem ωAM_zero : ωAM 0 = Real.sqrt 2 := by simp [ωAM]
theorem ωAM_succ (j : ℕ) : ωAM (j + 1) = 2 * π * ((j : ℝ) + 1) := by
 simp [ωAM]
def pAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 12, (cAM (j + 1) : ℝ) * Real.cos (ωAM (j + 1) * s)
theorem vAM_eq (s : ℝ) : vAM s = Real.cos (Real.sqrt 2 * s) + pAM s := by
 rw [vAM, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
 rfl
theorem sum_abs_cAM_succ :
   ∑ j ∈ Finset.range 12, |(cAM (j + 1) : ℝ)| ≤ 68807339 / 1000000000 := by
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num [abs_div]
theorem abs_pAM_le (s : ℝ) : |pAM s| ≤ 68807339 / 1000000000 := by
 unfold pAM
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 refine le_trans (Finset.sum_le_sum fun j _ => ?_) sum_abs_cAM_succ
 rw [abs_mul]
 exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
theorem vAM_even (s : ℝ) : vAM (-s) = vAM s := by
 unfold vAM
 refine Finset.sum_congr rfl fun j _ => ?_
 rw [mul_neg, Real.cos_neg]
theorem vAM_le (s : ℝ) : vAM s ≤ 5 / 4 := by
 rw [vAM_eq]
 have h1 := Real.cos_le_one (Real.sqrt 2 * s)
 have h2 := (abs_le.mp (abs_pAM_le s)).2
 linarith
theorem cos_sqrt2_ge {s : ℝ} : 1 - s ^ 2 ≤ Real.cos (Real.sqrt 2 * s) := by
 have h := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * s)
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have e : (Real.sqrt 2 * s) ^ 2 / 2 = s ^ 2 := by rw [mul_pow, hsq]; ring
 linarith
theorem vAM_ge_core {s : ℝ} (hs : |s| ≤ 1 / 2) : 681 / 1000 ≤ vAM s := by
 rw [vAM_eq]
 have h1 := cos_sqrt2_ge (s := s)
 have h2 := (abs_le.mp (abs_pAM_le s)).1
 have hs2 : s ^ 2 ≤ 1 / 4 := by
   have := abs_le.mp hs; nlinarith
 linarith
theorem vAM_pos_wide {s : ℝ} (hs : |s| ≤ 3 / 5) : 0 < vAM s := by
 rw [vAM_eq]
 have h1 := cos_sqrt2_ge (s := s)
 have h2 := (abs_le.mp (abs_pAM_le s)).1
 have hs2 : s ^ 2 ≤ 9 / 25 := by
   have := abs_le.mp hs; nlinarith
 linarith
theorem vAM_zero : vAM 0 = 1007127245 / 10 ^ 9 := by
 simp only [vAM, mul_zero, Real.cos_zero, mul_one, Finset.sum_range_succ, Finset.sum_range_zero,
   cAM, cAMn]
 norm_num
theorem vAM_continuous : Continuous vAM := by
 unfold vAM; fun_prop
theorem vAM_contDiff : ContDiff ℝ ⊤ vAM := by
 unfold vAM
 exact ContDiff.sum fun j _ => contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
def vAMd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))
def vAMdd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))
theorem hasDerivAt_vAM (s : ℝ) : HasDerivAt vAM (vAMd s) s := by
 unfold vAM vAMd
 have h : ∀ j ∈ Finset.range 13, HasDerivAt (fun s => (cAM j : ℝ) * Real.cos (ωAM j * s))
     (-((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))) s := by
   intro j _
   have h1 : HasDerivAt (fun s => ωAM j * s) (ωAM j) s := by
     simpa using (hasDerivAt_id s).const_mul (ωAM j)
   have h2 := ((Real.hasDerivAt_cos (ωAM j * s)).comp s h1).const_mul (cAM j : ℝ)
   exact h2.congr_deriv (by ring)
 have := HasDerivAt.fun_sum h
 simpa using this
theorem hasDerivAt_vAMd (s : ℝ) : HasDerivAt vAMd (vAMdd s) s := by
 unfold vAMd vAMdd
 have h : ∀ j ∈ Finset.range 13, HasDerivAt (fun s => -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s)))
     (-((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))) s := by
   intro j _
   have h1 : HasDerivAt (fun s => ωAM j * s) (ωAM j) s := by
     simpa using (hasDerivAt_id s).const_mul (ωAM j)
   have h2 := (((Real.hasDerivAt_sin (ωAM j * s)).comp s h1).const_mul
     ((cAM j : ℝ) * ωAM j)).neg
   exact h2.congr_deriv (by ring)
 have := HasDerivAt.fun_sum h
 simpa using this
theorem ωAM_nonneg (j : ℕ) : 0 ≤ ωAM j := by
 unfold ωAM; split_ifs <;> positivity
theorem ωAM_le (j : ℕ) : ωAM j ≤ if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ) := by
 by_cases h : j = 0
 · subst h
   rw [if_pos rfl, ωAM_zero, Real.sqrt_le_left (by norm_num)]; norm_num
 · rw [if_neg h]
   unfold ωAM
   rw [if_neg h]
   have := Real.pi_lt_d2
   have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
   nlinarith
theorem abs_vAMd_le (s : ℝ) : |vAMd s| ≤ 7 / 2 := by
 unfold vAMd
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have hb : ∀ j ∈ Finset.range 13, |-((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))|
     ≤ |(cAM j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
   intro j _
   rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (ωAM_nonneg j)]
   calc |(cAM j : ℝ)| * ωAM j * |Real.sin (ωAM j * s)| ≤ |(cAM j : ℝ)| * ωAM j * 1 :=
         mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity [ωAM_nonneg j])
     _ ≤ |(cAM j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
         rw [mul_one]; exact mul_le_mul_of_nonneg_left (ωAM_le j) (abs_nonneg _)
 refine (Finset.sum_le_sum hb).trans ?_
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num [abs_div]
theorem ωAM_sq_le (j : ℕ) :
   ωAM j ^ 2 ≤ if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2 := by
 by_cases h : j = 0
 · subst h
   rw [if_pos rfl, ωAM_zero, Real.sq_sqrt (by norm_num)]
 · rw [if_neg h]
   unfold ωAM
   rw [if_neg h]
   have h1 := Real.pi_lt_d2
   have h0 := Real.pi_pos
   have : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
   have hj2 : (0 : ℝ) ≤ (j : ℝ) ^ 2 := sq_nonneg _
   have e : (2 * π * (j : ℝ)) ^ 2 = 4 * π ^ 2 * (j : ℝ) ^ 2 := by ring
   rw [e]
   nlinarith
theorem abs_vAMdd_le (s : ℝ) : |vAMdd s| ≤ 87 := by
 unfold vAMdd
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have hb : ∀ j ∈ Finset.range 13, |-((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))|
     ≤ |(cAM j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
   intro j _
   rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (ωAM j))]
   calc |(cAM j : ℝ)| * ωAM j ^ 2 * |Real.cos (ωAM j * s)| ≤ |(cAM j : ℝ)| * ωAM j ^ 2 * 1 :=
         mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
     _ ≤ |(cAM j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
         rw [mul_one]; exact mul_le_mul_of_nonneg_left (ωAM_sq_le j) (abs_nonneg _)
 refine (Finset.sum_le_sum hb).trans ?_
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num [abs_div]
def hW (L : ℝ) (u : ℝ) : ℝ := vAM (u / L) / MAM
variable {L : ℝ}
theorem fW_eq_sqrt (u : ℝ) : fW L u = Real.sqrt (hW L u) := rfl
theorem fW_even (u : ℝ) : fW L (-u) = fW L u := by
 simp only [fW, neg_div, vAM_even]
theorem fW_nonneg (u : ℝ) : 0 ≤ fW L u := Real.sqrt_nonneg _
theorem hW_le_one (u : ℝ) : hW L u ≤ 1 := by
 unfold hW
 rw [div_le_one MAM_pos]
 exact vAM_le _
theorem fW_le_one (u : ℝ) : fW L u ≤ 1 := by
 rw [fW_eq_sqrt, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
 exact Real.sqrt_le_sqrt (hW_le_one u)
theorem abs_div_le_half (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
 rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith
theorem hW_core_ge (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L / 2) : 681 / 1250 ≤ hW L u := by
 have h := vAM_ge_core (abs_div_le_half hL hu)
 unfold hW MAM
 rw [le_div_iff₀ (by norm_num)]
 linarith
theorem hW_pos_of_mem (hL : 0 < L) {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :
   0 < hW L u := by
 unfold hW
 refine div_pos (vAM_pos_wide ?_) MAM_pos
 rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
 constructor <;> linarith [hu.1, hu.2]
theorem hW_contDiff : ContDiff ℝ ⊤ (hW L) := by
 unfold hW
 exact (vAM_contDiff.comp (contDiff_id.div_const L)).div_const MAM
theorem fW_contDiffOn (hL : 0 < L) :
   ContDiffOn ℝ 2 (fW L) (Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10)) :=
 (hW_contDiff.of_le le_top).contDiffOn.sqrt fun _ hu => (hW_pos_of_mem hL hu).ne'
variable {ϱ : ℝ → ℝ} {w : ℝ}
theorem phiW_even (u : ℝ) : phiW ϱ L w (-u) = phiW ϱ L w u := by
 rw [phiW_eq_mul, phiW_eq_mul, fW_even, Taper.phi_even]
theorem phiW_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiW ϱ L w u :=
 mul_nonneg (fW_nonneg u) (Taper.phi_nonneg hϱ u)
theorem phiW_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phiW ϱ L w u ≤ 1 := by
 rw [phiW_eq_mul]
 calc fW L u * Taper.phi ϱ L w u ≤ 1 * 1 :=
       mul_le_mul (fW_le_one u) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
   _ = 1 := one_mul 1
theorem phiW_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
   phiW ϱ L w u = 0 := by
 rw [phiW_eq_mul, Taper.phi_eq_zero hϱ hw hu, mul_zero]
theorem phiW_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ContDiff ℝ 2 (phiW ϱ L w) := by
 have hL : 0 < L := by linarith
 rw [contDiff_iff_contDiffAt]
 intro u
 rcases lt_or_ge |u| (L / 2 + L / 10) with hu | hu
 · have hmem : u ∈ Ioo (-(L / 2 + L / 10)) (L / 2 + L / 10) := by
     rw [mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
   have hf : ContDiffAt ℝ 2 (fW L) u := (fW_contDiffOn hL).contDiffAt (isOpen_Ioo.mem_nhds hmem)
   exact hf.mul (((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt)
 · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := by
     have : {v : ℝ | L / 2 < |v|} = (fun v : ℝ => |v|) ⁻¹' Set.Ioi (L / 2) := rfl
     rw [this]
     exact (continuous_abs).isOpen_preimage _ isOpen_Ioi
   have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
     show L / 2 < |u|; linarith
   apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0))
   filter_upwards [hopen.mem_nhds hmem] with v hv
   exact phiW_eq_zero hϱ hw (le_of_lt hv)
theorem phiW_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   Continuous (phiW ϱ L w) :=
 (phiW_contDiff hϱ hw hwL).continuous
theorem phiW_sq_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
   phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := by
 rw [phiW_eq_mul, fW_eq_sqrt, mul_pow]
 rcases le_or_gt (L / 2) |u| with hu | hu
 · rw [Taper.phi_eq_zero hϱ hw hu]; ring
 · rw [Real.sq_sqrt]
   refine (hW_pos_of_mem hL ?_).le
   rw [mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
end AMW
end
noncomputable section
open Real Set MeasureTheory
namespace AMW
def KfunAM (x : ℝ) : ℝ := ∫ t in (-(1:ℝ)/2)..(1/2), vAM t * Real.cos (2 * π * x * t)
def kfunAM (x : ℝ) : ℝ := KfunAM x / KfunAM 0
def wfunAM (x : ℝ) : ℝ := kfunAM x ^ 2
theorem KfunAM_neg (x : ℝ) : KfunAM (-x) = KfunAM x := by
 unfold KfunAM
 congr 1; funext t
 rw [show 2 * π * -x * t = -(2 * π * x * t) by ring, Real.cos_neg]
theorem wfunAM_nonneg (x : ℝ) : 0 ≤ wfunAM x := sq_nonneg _
theorem vAM_pos_on {t : ℝ} (ht : t ∈ Icc (-(1:ℝ)/2) (1/2)) : 0 < vAM t :=
 lt_of_lt_of_le (by norm_num) (vAM_ge_core (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩))
theorem KfunAM_zero : KfunAM 0 = ∫ t in (-(1:ℝ)/2)..(1/2), vAM t := by
 unfold KfunAM; simp
theorem KfunAM_zero_pos : 0 < KfunAM 0 := by
 rw [KfunAM_zero]
 apply intervalIntegral.intervalIntegral_pos_of_pos_on
 · exact vAM_continuous.intervalIntegrable _ _
 · intro t ht; exact vAM_pos_on ⟨ht.1.le, ht.2.le⟩
 · norm_num
theorem abs_KfunAM_le (x : ℝ) : |KfunAM x| ≤ KfunAM 0 := by
 rw [KfunAM_zero]
 unfold KfunAM
 have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
 calc |∫ t in (-(1:ℝ)/2)..(1/2), vAM t * Real.cos (2 * π * x * t)|
     ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |vAM t * Real.cos (2 * π * x * t)| :=
       intervalIntegral.abs_integral_le_integral_abs hab
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), vAM t := by
       apply intervalIntegral.integral_mono_on hab
       · exact ((vAM_continuous.mul (by fun_prop : Continuous fun t : ℝ =>
           Real.cos (2 * π * x * t))).abs).intervalIntegrable _ _
       · exact vAM_continuous.intervalIntegrable _ _
       · intro t ht
         rw [abs_mul, abs_of_pos (vAM_pos_on ht)]
         exact mul_le_of_le_one_right (vAM_pos_on ht).le (Real.abs_cos_le_one _)
theorem integral_cos_mul_sinc (c : ℝ) :
   (∫ t in (-(1 : ℝ) / 2)..(1 / 2), Real.cos (c * t)) = Real.sinc (c / 2) := by
 rcases eq_or_ne c 0 with hc | hc
 · subst hc; norm_num
 · have hc2 : c / 2 ≠ 0 := by simpa using hc
   rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos, Real.sinc_of_ne_zero hc2,
     show c * ((1:ℝ)/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring,
     Real.sin_neg, smul_eq_mul]
   field_simp
   ring
theorem KfunAM_eq_sinc (x : ℝ) :
   KfunAM x = ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
     ((Real.sinc ((ωAM j - 2 * π * x) / 2) + Real.sinc ((ωAM j + 2 * π * x) / 2)) / 2) := by
 unfold KfunAM vAM
 have hpt : ∀ t, (∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.cos (ωAM j * t)) * Real.cos (2 * π * x * t)
     = ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
         ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2) := by
   intro t
   rw [Finset.sum_mul]
   refine Finset.sum_congr rfl fun j _ => ?_
   rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
   ring
 simp_rw [hpt]
 have hI : ∀ j ∈ Finset.range 13, IntervalIntegrable (fun t => (cAM j : ℝ) *
     ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2))
     volume (-(1:ℝ)/2) (1/2) := fun j _ =>
   (by fun_prop : Continuous fun t => (cAM j : ℝ) *
     ((Real.cos ((ωAM j - 2 * π * x) * t) + Real.cos ((ωAM j + 2 * π * x) * t)) / 2)).intervalIntegrable _ _
 rw [intervalIntegral.integral_finsetSum hI]
 refine Finset.sum_congr rfl fun j _ => ?_
 have h1 : IntervalIntegrable (fun t => Real.cos ((ωAM j - 2 * π * x) * t)) volume (-(1:ℝ)/2) (1/2) :=
   (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
 have h2 : IntervalIntegrable (fun t => Real.cos ((ωAM j + 2 * π * x) * t)) volume (-(1:ℝ)/2) (1/2) :=
   (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
 rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
   intervalIntegral.integral_add h1 h2, integral_cos_mul_sinc, integral_cos_mul_sinc]
def KMT (x : ℝ) : ℝ :=
 (Real.sinc ((Real.sqrt 2 - 2 * π * x) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * x) / 2)) / 2
theorem term_sinc (n : ℕ) (x : ℝ) :
   (Real.sinc ((ωAM (n + 1) - 2 * π * x) / 2) + Real.sinc ((ωAM (n + 1) + 2 * π * x) / 2)) / 2
     = (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2 := by
 rw [ωAM_succ]
 have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
 have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
 rw [e1, e2, Real.sinc_neg]
theorem term_closed (n : ℕ) {x : ℝ} (hx : x ^ 2 ≠ ((n : ℝ) + 1) ^ 2) :
   (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2
     = (-1) ^ (n + 1) * x * Real.sin (π * x) / (π * (x ^ 2 - ((n : ℝ) + 1) ^ 2)) := by
 have hπ : π ≠ 0 := Real.pi_pos.ne'
 have h1 : x - ((n : ℝ) + 1) ≠ 0 := by
   intro h; apply hx; rw [show x = (n : ℝ) + 1 by linarith]
 have h2 : x + ((n : ℝ) + 1) ≠ 0 := by
   intro h; apply hx; rw [show x = -((n : ℝ) + 1) by linarith]; ring
 have hd : x ^ 2 - ((n : ℝ) + 1) ^ 2 ≠ 0 := sub_ne_zero.mpr hx
 rw [Real.sinc_of_ne_zero (mul_ne_zero hπ h1), Real.sinc_of_ne_zero (mul_ne_zero hπ h2)]
 have s1 : Real.sin (π * (x - ((n : ℝ) + 1))) = (-1) ^ (n + 1) * Real.sin (π * x) := by
   rw [show π * (x - ((n : ℝ) + 1)) = π * x - ((n + 1 : ℕ) : ℝ) * π by push_cast; ring,
     Real.sin_sub_nat_mul_pi]
 have s2 : Real.sin (π * (x + ((n : ℝ) + 1))) = (-1) ^ (n + 1) * Real.sin (π * x) := by
   rw [show π * (x + ((n : ℝ) + 1)) = π * x + ((n + 1 : ℕ) : ℝ) * π by push_cast; ring,
     Real.sin_add_nat_mul_pi]
 rw [s1, s2]
 have hprod : x ^ 2 - ((n : ℝ) + 1) ^ 2 = (x - ((n : ℝ) + 1)) * (x + ((n : ℝ) + 1)) := by ring
 rw [hprod]
 field_simp
 ring
def corrAM (x : ℝ) : ℝ :=
 x * Real.sin (π * x) / π *
   ∑ n ∈ Finset.range 12, (-1) ^ (n + 1) * (cAM (n + 1) : ℝ) / (x ^ 2 - ((n : ℝ) + 1) ^ 2)
theorem KfunAM_closed {x : ℝ} (hx : ∀ n : ℕ, n < 12 → x ^ 2 ≠ ((n : ℝ) + 1) ^ 2) :
   KfunAM x = KMT x + corrAM x := by
 rw [KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
 congr 1
 unfold corrAM
 rw [Finset.mul_sum]
 refine Finset.sum_congr rfl fun n hn => ?_
 rw [term_sinc, term_closed n (hx n (Finset.mem_range.mp hn))]
 have hπ : π ≠ 0 := Real.pi_pos.ne'
 have hd : x ^ 2 - ((n : ℝ) + 1) ^ 2 ≠ 0 := sub_ne_zero.mpr (hx n (Finset.mem_range.mp hn))
 field_simp
theorem KfunAM_zero_closed : KfunAM 0 = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
 have h0 : ∀ n : ℕ, n < 12 → (0:ℝ) ^ 2 ≠ ((n : ℝ) + 1) ^ 2 := by
   intro n _; have := Nat.cast_nonneg (α := ℝ) n; nlinarith
 rw [KfunAM_closed h0]
 unfold KMT corrAM
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 simp only [mul_zero, sub_zero, add_zero, zero_mul, zero_div]
 rw [Real.sinc_of_ne_zero (by positivity)]
 field_simp
 rw [hsq]
 ring
theorem KMT_eq_gamma {x : ℝ} (h : 1 - 2 * (π * x) ^ 2 ≠ 0) :
   KMT x = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)
     * ((Real.cos (π * x) - 2 * ((Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2))
         * (π * x) * Real.sin (π * x)) / (1 - 2 * (π * x) ^ 2)) := by
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hs0 : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsa : Real.sin (Real.sqrt 2 / 2) ≠ 0 := by
   apply ne_of_gt
   apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
   have : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
   linarith [Real.pi_gt_three]
 generalize hb : π * x = b at h ⊢
 have hx2 : 2 * π * x = 2 * b := by rw [← hb]; ring
 have h1 : Real.sqrt 2 / 2 - b ≠ 0 := by
   intro hz; apply h
   have : b = Real.sqrt 2 / 2 := by linarith
   rw [this, div_pow, hsq]; norm_num
 have h2 : Real.sqrt 2 / 2 + b ≠ 0 := by
   intro hz; apply h
   have : b = -(Real.sqrt 2 / 2) := by linarith
   rw [this, neg_sq, div_pow, hsq]; norm_num
 unfold KMT
 rw [hx2, show (Real.sqrt 2 - 2 * b) / 2 = Real.sqrt 2 / 2 - b by ring,
   show (Real.sqrt 2 + 2 * b) / 2 = Real.sqrt 2 / 2 + b by ring,
   Real.sinc_of_ne_zero h1, Real.sinc_of_ne_zero h2, Real.sin_sub, Real.sin_add]
 generalize Real.sin (Real.sqrt 2 / 2) = S at hsa ⊢
 generalize Real.cos (Real.sqrt 2 / 2) = C
 have hprod : (Real.sqrt 2 / 2 - b) * (Real.sqrt 2 / 2 + b) = (1 - 2 * b ^ 2) / 2 := by
   have : (Real.sqrt 2 / 2 - b) * (Real.sqrt 2 / 2 + b) = Real.sqrt 2 ^ 2 / 4 - b ^ 2 := by ring
   rw [this, hsq]; ring
 rw [div_add_div _ _ h1 h2, hprod]
 field_simp
 linear_combination (2 * C * Real.sin b * b) * hsq
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace AMW
open Zeta23
def vConvAM (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2 - r), vAM s * vAM (s + r)
def aInf : ℝ := (∫ s in (-(1:ℝ)/2)..(1/2), vAM s) / MAM
def bInf : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s / MAM) ^ 2
def JInf : ℝ := 2 * (∫ r in (0:ℝ)..1, vConvAM r * r) / MAM ^ 2
theorem edge_est {h p : ℝ → ℝ} {L w : ℝ} (hw0 : 0 < w)
   (hwL : 2 * w ≤ L) (hh : ∀ u, |h u| ≤ 1) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
   (hpl : ∀ u : ℝ, |u| ≤ L/2 - w → p u = 1) (hsupp : ∀ u : ℝ, L/2 ≤ |u| → p u = 0)
   (hpc : Continuous p) (hhc : Continuous h) :
   |(∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u| ≤ 2 * w := by
 have hrestr : ∫ u, h u * p u = ∫ u in Set.Icc (-(L/2)) (L/2), h u * p u := by
   rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
   intro x hx
   rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
   have : L / 2 ≤ |x| := by
     rcases hx with hc | hc
     · rw [abs_of_neg (by linarith : x < 0)]; linarith
     · rw [abs_of_pos (by linarith : 0 < x)]; linarith
   rw [hsupp x this, mul_zero]
 have hIhp : MeasureTheory.IntegrableOn (fun u => h u * p u) (Set.Icc (-(L/2)) (L/2)) :=
   ((hhc.mul hpc).continuousOn).integrableOn_compact isCompact_Icc
 have hIh : MeasureTheory.IntegrableOn h (Set.Icc (-(L/2)) (L/2)) :=
   (hhc.continuousOn).integrableOn_compact isCompact_Icc
 have hsub : (∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u
     = ∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u) := by
   rw [hrestr, ← MeasureTheory.integral_sub hIhp hIh]
 rw [hsub]
 set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
     + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
 have hImaj : Integrable maj := by
   apply Integrable.add
   · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
       (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
   · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
       (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
 have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
   Set.indicator_nonneg (fun _ _ => zero_le_one) u
 have hptw : ∀ u ∈ Set.Icc (-(L/2)) (L/2), |h u * p u - h u| ≤ maj u := by
   intro u hu
   have hmaj0 : 0 ≤ maj u := by
     rw [hmaj]
     exact add_nonneg (hind0 _ u) (hind0 _ u)
   rcases le_or_gt |u| (L/2 - w) with hpl' | hedge
   · rw [hpl u hpl', mul_one, sub_self, abs_zero]
     exact hmaj0
   · have hbound : |h u * p u - h u| ≤ 1 := by
       have e : h u * p u - h u = h u * (p u - 1) := by ring
       rw [e, abs_mul]
       calc |h u| * |p u - 1| ≤ 1 * 1 := by
             apply mul_le_mul (hh u) ?_ (abs_nonneg _) zero_le_one
             rw [abs_le]
             exact ⟨by linarith [hp0 u], by linarith [hp1 u]⟩
         _ = 1 := mul_one 1
     have hone : (1:ℝ) ≤ maj u := by
       rw [hmaj]
       show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
         + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
       rcases le_or_gt u 0 with hneg | hpos
       · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
           refine ⟨hu.1, ?_⟩
           have habs : |u| = -u := abs_of_nonpos hneg
           rw [habs] at hedge
           linarith
         have := hind0 (Set.Icc (L/2 - w) (L/2)) u
         rw [Set.indicator_of_mem hu1, Pi.one_apply]
         linarith
       · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
           refine ⟨?_, hu.2⟩
           have habs : |u| = u := abs_of_pos hpos
           rw [habs] at hedge
           linarith
         have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
         rw [Set.indicator_of_mem hu1, Pi.one_apply]
         linarith
     linarith
 calc |∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u)|
     ≤ ∫ u in Set.Icc (-(L/2)) (L/2), |h u * p u - h u| :=
       MeasureTheory.abs_integral_le_integral_abs
   _ ≤ ∫ u in Set.Icc (-(L/2)) (L/2), maj u := by
       apply MeasureTheory.setIntegral_mono_on
         (((hhc.mul hpc).sub hhc).abs.continuousOn.integrableOn_compact isCompact_Icc)
         hImaj.integrableOn measurableSet_Icc hptw
   _ ≤ ∫ u, maj u :=
       MeasureTheory.setIntegral_le_integral hImaj
         (MeasureTheory.ae_of_all _ fun u => by
           rw [hmaj]
           apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => zero_le_one) u)
   _ = 2 * w := by
       rw [hmaj]
       rw [MeasureTheory.integral_add
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))]
       rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
         Real.volume_Icc, Real.volume_Icc,
         ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
       ring
theorem integral_scale {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L) :
   ∫ u in (-(L/2))..(L/2), v (u / L) = L * ∫ s in (-(1:ℝ)/2)..(1/2), v s := by
 rw [intervalIntegral.integral_comp_div (f := v) hL.ne', smul_eq_mul,
   show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
   show L/2 / L = (1:ℝ)/2 by rw [div_div]; rw [div_eq_div_iff (by positivity) (by norm_num)]; ring]
theorem abs_vAM_le (s : ℝ) : |vAM s| ≤ 5 / 4 := by
 rw [vAM_eq]
 have h1 := Real.abs_cos_le_one (Real.sqrt 2 * s)
 have h2 := abs_pAM_le s
 calc |Real.cos (Real.sqrt 2 * s) + pAM s| ≤ |Real.cos (Real.sqrt 2 * s)| + |pAM s| := abs_add_le _ _
   _ ≤ 5 / 4 := by linarith
theorem abs_hW_le (L u : ℝ) : |hW L u| ≤ 1 := by
 unfold hW
 rw [abs_div, abs_of_pos MAM_pos, div_le_one MAM_pos]
 exact abs_vAM_le _
theorem hW_continuous (L : ℝ) : Continuous (hW L) :=
 (vAM_continuous.comp (continuous_id.div_const L)).div_const MAM
variable {ϱ : ℝ → ℝ} {L w : ℝ}
theorem integral_hW (hL : 0 < L) :
   ∫ u in Set.Icc (-(L/2)) (L/2), hW L u = L * aInf := by
 rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
 unfold hW aInf
 rw [integral_scale (v := fun s => vAM s / MAM) hL, intervalIntegral.integral_div]
theorem integral_hW_sq (hL : 0 < L) :
   ∫ u in Set.Icc (-(L/2)) (L/2), hW L u ^ 2 = L * bInf := by
 rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
 unfold hW bInf
 exact integral_scale (v := fun s => (vAM s / MAM) ^ 2) hL
theorem aW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |L⁻¹ * (∫ u, phiW ϱ L w u ^ 2) - aInf| ≤ 2 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 have hwin : ∫ u, phiW ϱ L w u ^ 2 = ∫ u, hW L u * Taper.phi ϱ L w u ^ 2 := by
   congr 1; funext u; exact phiW_sq_eq hϱ hw0 hL u
 have hcore := edge_est (h := hW L) (p := fun u => Taper.phi ϱ L w u ^ 2) hw0 hwL'
   (abs_hW_le L) (fun u => sq_nonneg _)
   (fun u => by
     calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
           pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
       _ = 1 := one_pow 2)
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 2 = 1
     rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 2 = 0
     rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
   ((Taper.phi_continuous hϱ hw0 hwL').pow 2) (hW_continuous L)
 rw [integral_hW hL] at hcore
 rw [hwin]
 have e : L⁻¹ * (∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - aInf
     = L⁻¹ * ((∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf) := by
   field_simp
 rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
 calc L⁻¹ * |(∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf| ≤ L⁻¹ * (2 * w) :=
       mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
   _ = 2 * w / L := by field_simp
theorem bW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |L⁻¹ * (∫ u, phiW ϱ L w u ^ 4) - bInf| ≤ 2 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 have hwin : ∫ u, phiW ϱ L w u ^ 4 = ∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
   congr 1; funext u
   have := phiW_sq_eq hϱ hw0 hL u (ϱ := ϱ) (w := w)
   calc phiW ϱ L w u ^ 4 = (phiW ϱ L w u ^ 2) ^ 2 := by ring
     _ = (hW L u * Taper.phi ϱ L w u ^ 2) ^ 2 := by rw [this]
     _ = hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by ring
 have hcore := edge_est (h := fun u => hW L u ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hw0 hwL'
   (fun u => by
     rw [abs_pow]
     calc |hW L u| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_hW_le L u) 2
       _ = 1 := one_pow 2)
   (fun u => by positivity)
   (fun u => by
     calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 :=
           pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
       _ = 1 := one_pow 4)
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 4 = 1
     rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 4 = 0
     rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow (by norm_num : (4:ℕ) ≠ 0)])
   ((Taper.phi_continuous hϱ hw0 hwL').pow 4) ((hW_continuous L).pow 2)
 rw [integral_hW_sq hL] at hcore
 rw [hwin]
 have e : L⁻¹ * (∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - bInf
     = L⁻¹ * ((∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf) := by
   field_simp
 rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
 calc L⁻¹ * |(∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf| ≤ L⁻¹ * (2 * w) :=
       mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
   _ = 2 * w / L := by field_simp
def sW (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (hW L) u
theorem sW_nonneg (hL : 0 < L) (u : ℝ) : 0 ≤ sW L u := by
 unfold sW
 apply Set.indicator_nonneg
 intro x hx
 have := hW_core_ge hL (abs_le.mpr ⟨hx.1, hx.2⟩)
 linarith
theorem abs_sW_le (L u : ℝ) : |sW L u| ≤ 1 := by
 unfold sW
 by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
 · rw [Set.indicator_of_mem hm]; exact abs_hW_le L u
 · rw [Set.indicator_of_notMem hm, abs_zero]; exact zero_le_one
theorem sW_measurable (L : ℝ) : Measurable (sW L) :=
 Measurable.indicator (hW_continuous L).measurable measurableSet_Icc
theorem sW_integrable (L : ℝ) : Integrable (sW L) :=
 (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
   ((hW_continuous L).continuousOn.integrableOn_compact isCompact_Icc)
theorem integral_abs_phiWsq_sub_sharp (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ∫ u, |phiW ϱ L w u ^ 2 - sW L u| ≤ 2 * w := by
 have hL : 0 < L := by linarith
 set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
     + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
 have hImaj : Integrable maj := by
   apply Integrable.add <;>
     exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
       (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
 have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
   Set.indicator_nonneg (fun _ _ => zero_le_one) u
 have hpt : ∀ u : ℝ, |phiW ϱ L w u ^ 2 - sW L u| ≤ maj u := by
   intro u
   have hmaj0 : 0 ≤ maj u := by
     rw [hmaj]
     exact add_nonneg (hind0 _ u) (hind0 _ u)
   have hval : phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := phiW_sq_eq hϱ hw hL u
   rcases le_or_gt |u| (L/2 - w) with hpl | hedge
   · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
       rw [abs_le] at hpl
       constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
     rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one]
     unfold sW
     rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
     exact hmaj0
   · rcases le_or_gt |u| (L/2) with hin | hout
     · have hbound : |phiW ϱ L w u ^ 2 - sW L u| ≤ 1 := by
         have h1' : 0 ≤ phiW ϱ L w u ^ 2 := sq_nonneg _
         have h2' : phiW ϱ L w u ^ 2 ≤ 1 := by
           calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 :=
                 pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
             _ = 1 := one_pow 2
         have h3' : 0 ≤ sW L u := sW_nonneg hL u
         have h4' : sW L u ≤ 1 := (abs_le.mp (abs_sW_le L u)).2
         rw [abs_le]
         constructor <;> linarith
       have hone : (1:ℝ) ≤ maj u := by
         rw [hmaj]
         show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
           + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
         rcases le_or_gt u 0 with hneg | hpos
         · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
             have : |u| = -u := abs_of_nonpos hneg
             rw [this] at hin hedge
             exact ⟨by linarith, by linarith⟩
           have := hind0 (Set.Icc (L/2 - w) (L/2)) u
           rw [Set.indicator_of_mem hu1, Pi.one_apply]
           linarith
         · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
             have : |u| = u := abs_of_pos hpos
             rw [this] at hin hedge
             exact ⟨by linarith, by linarith⟩
           have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
           rw [Set.indicator_of_mem hu1, Pi.one_apply]
           linarith
       linarith
     · have h1' : phiW ϱ L w u = 0 := phiW_eq_zero hϱ hw (le_of_lt hout)
       have h2' : sW L u = 0 := by
         unfold sW
         apply Set.indicator_of_notMem
         intro hm
         have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
         linarith
       rw [h1', h2']
       norm_num
       exact hmaj0
 calc ∫ u, |phiW ϱ L w u ^ 2 - sW L u|
     ≤ ∫ u, maj u := by
       apply MeasureTheory.integral_mono_of_nonneg
         (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
         (MeasureTheory.ae_of_all _ hpt)
   _ = 2 * w := by
       rw [hmaj]
       rw [MeasureTheory.integral_add
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
         MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
         Real.volume_Icc, Real.volume_Icc,
         ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
       ring
theorem phiW_sq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) :
   HasCompactSupport (fun u => phiW ϱ L w u ^ 2) := by
 apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L/2)) (b := L/2))
 intro x hx
 rw [Function.mem_support] at hx
 by_contra hmem
 apply hx
 show phiW ϱ L w x ^ 2 = 0
 rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
 have : L / 2 ≤ |x| := by
   rcases hmem with hc | hc
   · rw [abs_of_neg (by linarith : x < 0)]; linarith
   · rw [abs_of_pos (by linarith : 0 < x)]; linarith
 rw [phiW_eq_zero hϱ hw this, zero_pow two_ne_zero]
theorem autocorr_phiWsq_close (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
   |Params.autocorr (fun u => phiW ϱ L w u ^ 2) y - ∫ u, sW L u * sW L (u + y)| ≤ 4 * w := by
 set h : ℝ → ℝ := fun u => phiW ϱ L w u ^ 2 with hhdef
 set k : ℝ → ℝ := sW L with hkdef
 have hh_cont : Continuous h := (phiW_continuous hϱ hw hwL).pow 2
 have hh1 : ∀ u, |h u| ≤ 1 := by
   intro u
   rw [hhdef]
   simp only
   rw [abs_of_nonneg (sq_nonneg _)]
   calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
     _ = 1 := one_pow 2
 have hk_meas : Measurable k := sW_measurable L
 have hk1 : ∀ u, |k u| ≤ 1 := abs_sW_le L
 have hint_h : Integrable h :=
   hh_cont.integrable_of_hasCompactSupport (phiW_sq_hasCompactSupport hϱ hw (by linarith))
 have hint_k : Integrable k := sW_integrable L
 have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
 have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
 have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
 have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
 have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
   hint_hy.aestronglyMeasurable
 have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
   have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hh1 (u + y))
   exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
 have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
   exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hk1 u)
 have hint_hh : Integrable (fun u => h u * h (u + y)) := by
   have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hh1 (u + y))
   exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
 have hint_kk : Integrable (fun u => k u * k (u + y)) := by
   exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hk1 u)
 have hdecomp : Params.autocorr h y - ∫ u, k u * k (u + y)
     = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
   have e1 : Params.autocorr h y - ∫ u, k u * k (u + y)
       = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
     rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl,
       MeasureTheory.integral_sub hint_hh hint_kk]
   rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
   apply MeasureTheory.integral_congr_ae
   apply MeasureTheory.ae_of_all
   intro u
   ring
 have hd2w := integral_abs_phiWsq_sub_sharp hϱ hw hwL
 have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
 have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
   calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
         MeasureTheory.abs_integral_le_integral_abs
     _ ≤ ∫ u, |h u - k u| := by
         apply MeasureTheory.integral_mono_of_nonneg
           (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
           (MeasureTheory.ae_of_all _ fun u => ?_)
         show |(h u - k u) * h (u + y)| ≤ |h u - k u|
         rw [abs_mul]
         calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
               mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
           _ = |h u - k u| := mul_one _
     _ ≤ 2 * w := hd2w
 have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
   have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
     MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
   calc |∫ u, k u * (h (u + y) - k (u + y))|
       ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
     _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
         apply MeasureTheory.integral_mono_of_nonneg
           (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
           (MeasureTheory.ae_of_all _ fun u => ?_)
         show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
         rw [abs_mul]
         calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
               mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
           _ = _ := one_mul _
     _ = ∫ u, |h u - k u| := htrans
     _ ≤ 2 * w := hd2w
 calc |Params.autocorr h y - ∫ u, k u * k (u + y)|
     = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by
       rw [hdecomp]
   _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
   _ ≤ 4 * w := by linarith
theorem sharp_overlap (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
   ∫ u, sW L u * sW L (u + y) = L * vConvAM (y / L) / MAM ^ 2 := by
 have hind : ∀ u : ℝ, sW L u * sW L (u + y)
     = (Set.Icc (-(L/2)) (L/2 - y)).indicator (fun u => hW L u * hW L (u + y)) u := by
   intro u
   unfold sW
   by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
   · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
     have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
     rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
   · rw [Set.indicator_of_notMem hu]
     rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
     rcases hu with hu | hu
     · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
     · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
 rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
   MeasureTheory.integral_indicator measurableSet_Icc,
   MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
 have hF : ∀ u, hW L u * hW L (u + y) = (fun s => vAM s * vAM (s + y / L) / MAM ^ 2) (u / L) := by
   intro u
   simp only [hW]
   rw [show (u + y) / L = u / L + y / L by ring]
   ring
 simp_rw [hF]
 rw [intervalIntegral.integral_comp_div (f := fun s => vAM s * vAM (s + y / L) / MAM ^ 2) hL.ne',
   smul_eq_mul, intervalIntegral.integral_div,
   show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
   show (L/2 - y) / L = 1/2 - y / L by field_simp]
 unfold vConvAM
 ring
theorem continuous_vConvAM : Continuous vConvAM := by
 unfold vConvAM
 have h : Continuous (Function.uncurry fun (r s : ℝ) => vAM s * vAM (s + r)) :=
   (vAM_continuous.comp continuous_snd).mul (vAM_continuous.comp (continuous_snd.add continuous_fst))
 exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous h
   (continuous_const.sub continuous_id)
theorem JW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |2 / L ^ 3 * (∫ y in (0:ℝ)..L, Params.autocorr (fun u => phiW ϱ L w u ^ 2) y * y) - JInf|
     ≤ 8 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 set A : ℝ → ℝ := Params.autocorr (fun u => phiW ϱ L w u ^ 2) with hAdef
 set C : ℝ → ℝ := fun y => L * vConvAM (y / L) / MAM ^ 2 with hCdef
 have hAcont : Continuous A := by
   rw [hAdef]
   refine Taper.autocorr_continuous_of_support _ (M := L/2) ((phiW_continuous hϱ hw0 hwL').pow 2) ?_
   intro u hu
   show phiW ϱ L w u ^ 2 = 0
   rw [phiW_eq_zero hϱ hw0 hu, zero_pow two_ne_zero]
 have hCcont : Continuous C := by
   rw [hCdef]
   exact ((continuous_const.mul (continuous_vConvAM.comp (continuous_id.div_const L))).div_const _)
 have hIA : IntervalIntegrable (fun y => A y * y) MeasureTheory.volume 0 L :=
   (hAcont.mul continuous_id).intervalIntegrable 0 L
 have hIC : IntervalIntegrable (fun y => C y * y) MeasureTheory.volume 0 L :=
   (hCcont.mul continuous_id).intervalIntegrable 0 L
 have hsplit : ∫ y in (0:ℝ)..L, A y * y
     = (∫ y in (0:ℝ)..L, (A y - C y) * y) + ∫ y in (0:ℝ)..L, C y * y := by
   have e1 : ∫ y in (0:ℝ)..L, (A y - C y) * y = ∫ y in (0:ℝ)..L, (A y * y - C y * y) :=
     intervalIntegral.integral_congr (fun y _ => by ring)
   rw [e1, intervalIntegral.integral_sub hIA hIC]
   ring
 have hcmp : |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * L := by
   have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * w * L)
     (f := fun y => (A y - C y) * y) (a := 0) (b := L) ?_
   · rw [Real.norm_eq_abs] at hb
     calc |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * |L - 0| := hb
       _ = 4 * w * L * L := by rw [sub_zero, abs_of_pos hL]
   · intro y hy
     rw [Set.uIoc_of_le hL.le] at hy
     rw [Real.norm_eq_abs]
     show |(A y - C y) * y| ≤ 4 * w * L
     rw [abs_mul]
     have hAC : |A y - C y| ≤ 4 * w := by
       have h1 := autocorr_phiWsq_close hϱ hw0 hwL' y (L := L)
       rw [sharp_overlap hL hy.1.le hy.2] at h1
       exact h1
     calc |A y - C y| * |y| ≤ (4 * w) * L := by
           apply mul_le_mul hAC ?_ (abs_nonneg _) (by positivity)
           rw [abs_of_pos hy.1]
           exact hy.2
       _ = 4 * w * L := rfl
 have hmain : 2 / L ^ 3 * ∫ y in (0:ℝ)..L, C y * y = JInf := by
   have hG : ∀ y, C y * y = (L ^ 2 / MAM ^ 2) * ((fun r => vConvAM r * r) (y / L)) := by
     intro y
     simp only [hCdef]
     field_simp
   simp_rw [hG]
   rw [intervalIntegral.integral_const_mul,
     intervalIntegral.integral_comp_div (f := fun r => vConvAM r * r) hL.ne', smul_eq_mul,
     zero_div, div_self hL.ne']
   unfold JInf
   field_simp
 have e : 2 / L ^ 3 * (∫ y in (0:ℝ)..L, A y * y) - JInf
     = 2 / L ^ 3 * (∫ y in (0:ℝ)..L, (A y - C y) * y) := by
   rw [hsplit, mul_add, hmain]; ring
 rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / L ^ 3)]
 calc 2 / L ^ 3 * |∫ y in (0:ℝ)..L, (A y - C y) * y|
     ≤ 2 / L ^ 3 * (4 * w * L * L) := mul_le_mul_of_nonneg_left hcmp (by positivity)
   _ = 8 * w / L := by field_simp; ring
theorem vAM_pos_core {s : ℝ} (hs : s ∈ Set.Icc (-(1:ℝ)/2) (1/2)) : 0 < vAM s :=
 lt_of_lt_of_le (by norm_num) (vAM_ge_core (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩))
theorem vConvAM_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ vConvAM r := by
 unfold vConvAM
 apply intervalIntegral.integral_nonneg (by linarith)
 intro s hs
 exact mul_nonneg (vAM_pos_core ⟨hs.1, by linarith [hs.2]⟩).le
   (vAM_pos_core ⟨by linarith [hs.1], by linarith [hs.2]⟩).le
theorem JInf_nonneg : 0 ≤ JInf := by
 unfold JInf
 apply div_nonneg _ (sq_nonneg _)
 apply mul_nonneg (by norm_num)
 apply intervalIntegral.integral_nonneg zero_le_one
 intro r hr
 exact mul_nonneg (vConvAM_nonneg hr.1 hr.2) hr.1
theorem bInf_pos : 0 < bInf := by
 unfold bInf
 apply intervalIntegral.intervalIntegral_pos_of_pos_on
 · exact ((vAM_continuous.div_const _).pow 2).intervalIntegrable _ _
 · intro s hs
   have h1 := vAM_pos_core ⟨hs.1.le, hs.2.le⟩
   have h2 := MAM_pos
   positivity
 · norm_num
theorem aInf_pos : 0 < aInf := by
 unfold aInf
 apply div_pos _ MAM_pos
 apply intervalIntegral.intervalIntegral_pos_of_pos_on
 · exact vAM_continuous.intervalIntegrable _ _
 · intro s hs
   exact vAM_pos_core ⟨hs.1.le, hs.2.le⟩
 · norm_num
theorem tendsto_aW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => (localFunW P T).a) atTop (𝓝 aInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact aW_close hP.taper hP.one_le_w hT
theorem tendsto_bW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => (localFunW P T).b) atTop (𝓝 bInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact bW_close hP.taper hP.one_le_w hT
theorem tendsto_JW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y) atTop
     (𝓝 JInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 8)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact JW_close hP.taper hP.one_le_w hT
theorem tendsto_cRatio_W {P : Params} (hP : P.Valid) :
   Tendsto (fun T => ThmD.cRatio (P.lam1 T) (localFunW P T).a (localFunW P T).b
     (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y)) atTop
     (𝓝 (ThmD.cRatio P.lam aInf bInf JInf)) := by
 have hden : 0 < bInf + P.lam ^ 2 * JInf := by
   have h1 := JInf_nonneg
   have h2 := bInf_pos
   positivity
 have hl1 := ThmD.tendsto_lam1 hP.lam_pos
 have hnum := hl1.mul ((tendsto_aW hP).pow 2)
 have hdenT := (tendsto_bW hP).add ((hl1.pow 2).mul (tendsto_JW hP))
 exact hnum.div hdenT hden.ne'
theorem cRatio_W_pos {lam : ℝ} (hlam : 0 < lam) : 0 < ThmD.cRatio lam aInf bInf JInf := by
 unfold ThmD.cRatio
 have h1 := JInf_nonneg
 have h2 := bInf_pos
 have h3 := aInf_pos
 positivity
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter
namespace AMW
section Swap
variable {q : ℝ → ℝ} {B : ℝ}
def ext0 (q : ℝ → ℝ) : ℝ → ℝ := (Icc (-(1:ℝ)/2) (1/2)).indicator q
theorem ext0_measurable (hq : Continuous q) : Measurable (ext0 q) :=
 hq.measurable.indicator measurableSet_Icc
theorem abs_ext0_le (hB : ∀ s, |q s| ≤ B) (s : ℝ) : |ext0 q s| ≤ B := by
 unfold ext0
 by_cases h : s ∈ Icc (-(1:ℝ)/2) (1/2)
 · rw [Set.indicator_of_mem h]; exact hB s
 · rw [Set.indicator_of_notMem h, abs_zero]; exact (abs_nonneg _).trans (hB s)
theorem intervalIntegral_eq_indicator (f : ℝ → ℝ) :
   ∫ s in (-(1:ℝ)/2)..(1/2), f s = ∫ s, (Icc (-(1:ℝ)/2) (1/2)).indicator f s := by
 rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
   intervalIntegral.integral_of_le (by norm_num)]
def acor (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s, ext0 q s * ext0 q (s + r)
theorem acor_neg (r : ℝ) : acor q (-r) = acor q r := by
 unfold acor
 have h := MeasureTheory.integral_sub_right_eq_self (μ := volume)
   (fun x => ext0 q (x + r) * ext0 q x) r
 simp only [sub_add_cancel] at h
 calc ∫ s, ext0 q s * ext0 q (s + -r) = ∫ x, ext0 q x * ext0 q (x - r) := by
       simp only [sub_eq_add_neg]
   _ = ∫ x, ext0 q (x + r) * ext0 q x := h
   _ = ∫ s, ext0 q s * ext0 q (s + r) := by
       congr 1; funext s; ring
theorem acor_eq_zero {r : ℝ} (hr : 1 < r) : acor q r = 0 := by
 unfold acor
 have : ∀ s, ext0 q s * ext0 q (s + r) = 0 := by
   intro s
   unfold ext0
   by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2)
   · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r), mul_zero]
     intro h; linarith [hs.1, h.2]
   · rw [Set.indicator_of_notMem hs, zero_mul]
 simp only [this, integral_zero]
theorem acor_eq_overlap {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
   acor q r = ∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r) := by
 unfold acor
 have hind : ∀ s : ℝ, ext0 q s * ext0 q (s + r)
     = (Icc (-(1:ℝ)/2) (1/2 - r)).indicator (fun s => q s * q (s + r)) s := by
   intro s
   unfold ext0
   by_cases hs : s ∈ Icc (-(1:ℝ)/2) (1/2 - r)
   · have hs1 : s ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨hs.1, by linarith [hs.2]⟩
     have hs2 : s + r ∈ Icc (-(1:ℝ)/2) (1/2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
     rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs1, Set.indicator_of_mem hs2]
   · rw [Set.indicator_of_notMem hs]
     rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
     rcases hs with hs | hs
     · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
     · rw [Set.indicator_of_notMem (s := Icc (-(1:ℝ)/2) (1/2)) (a := s + r)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
 rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
   integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(1:ℝ)/2 ≤ 1/2 - r)]
theorem integrable_swap (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
   Integrable (fun p : ℝ × ℝ => ext0 q p.1 * (|p.2| * ext0 q (p.1 + p.2)))
     (volume.prod volume) := by
 have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
 set K : Set (ℝ × ℝ) := Icc (-(1:ℝ)/2) (1/2) ×ˢ Icc (-1:ℝ) 1 with hK
 have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
 have hKf : (volume.prod volume) K ≠ ⊤ := by
   rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
   exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
 have hg : Integrable (K.indicator (fun _ => B ^ 2)) (volume.prod volume) :=
   (integrable_indicator_iff hKm).mpr (integrableOn_const hKf)
 refine hg.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
 · exact ((ext0_measurable hq).comp measurable_fst).mul
     ((continuous_abs.measurable.comp measurable_snd).mul
       ((ext0_measurable hq).comp (measurable_fst.add measurable_snd))) |>.aestronglyMeasurable
 · rw [Real.norm_eq_abs]
   by_cases h1 : p.1 ∈ Icc (-(1:ℝ)/2) (1/2)
   · by_cases h2 : p.1 + p.2 ∈ Icc (-(1:ℝ)/2) (1/2)
     · have hpK : p ∈ K := ⟨h1, by constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]⟩
       rw [Set.indicator_of_mem hpK, abs_mul, abs_mul, abs_abs]
       have hr : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
         by linarith [h1.1, h1.2, h2.1, h2.2]⟩
       have e1 := abs_ext0_le hB p.1 (q := q)
       have e2 := abs_ext0_le hB (p.1 + p.2) (q := q)
       calc |ext0 q p.1| * (|p.2| * |ext0 q (p.1 + p.2)|) ≤ B * (1 * B) := by
             apply mul_le_mul e1 (mul_le_mul hr e2 (abs_nonneg _) zero_le_one)
               (by positivity) hB0
         _ = B ^ 2 := by ring
     · have : ext0 q (p.1 + p.2) = 0 := Set.indicator_of_notMem h2 _
       rw [this, mul_zero, mul_zero, abs_zero]
       exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p
   · have : ext0 q p.1 = 0 := Set.indicator_of_notMem h1 _
     rw [this, zero_mul, abs_zero]
     exact Set.indicator_nonneg (fun _ _ => sq_nonneg B) p
theorem swap_identity (hq : Continuous q) (hB : ∀ s, |q s| ≤ B) :
   2 * ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
     = ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t := by
 have hR1 : ∀ s, ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t = ∫ t, |s - t| * ext0 q t := by
   intro s
   rw [intervalIntegral_eq_indicator]
   congr 1; funext t
   unfold ext0
   exact Set.indicator_mul_right _ (fun t => |s - t|) q
 have hR2 : ∫ s in (-(1:ℝ)/2)..(1/2), q s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * q t
     = ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r)) := by
   simp_rw [hR1]
   rw [intervalIntegral_eq_indicator]
   congr 1; funext s
   have e1 : (Icc (-(1:ℝ)/2) (1/2)).indicator (fun s => q s * ∫ t, |s - t| * ext0 q t) s
       = ext0 q s * ∫ t, |s - t| * ext0 q t := by
     unfold ext0
     exact Set.indicator_mul_left _ q (fun s => ∫ t, |s - t| * ext0 q t)
   rw [e1, ← integral_const_mul]
   have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
     (fun t => ext0 q s * (|s - t| * ext0 q t)) s
   rw [← h]
   congr 1; funext r
   rw [show s - (s + r) = -r by ring, abs_neg]
 have hS : ∫ s, ∫ r, ext0 q s * (|r| * ext0 q (s + r))
     = ∫ r, |r| * acor q r := by
   rw [MeasureTheory.integral_integral_swap (integrable_swap hq hB)]
   congr 1; funext r
   unfold acor
   rw [← integral_const_mul]
   congr 1; funext s
   ring
 have hE : ∫ r, |r| * acor q r = 2 * ∫ r in Ioi 0, r * acor q r := by
   have e : (fun r => |r| * acor q r) = fun r => (fun x => x * acor q x) |r| := by
     funext r
     simp only
     rcases le_or_gt 0 r with h | h
     · rw [abs_of_nonneg h]
     · rw [abs_of_neg h, acor_neg]
   rw [e]
   exact integral_comp_abs (f := fun x => x * acor q x)
 have hI : ∫ r in Ioi 0, r * acor q r = ∫ r in (0:ℝ)..1, r * acor q r := by
   rw [intervalIntegral.integral_of_le zero_le_one]
   refine (MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
     (f := fun r => r * acor q r) measurableSet_Ioi
     (Ioc_subset_Ioi_self : Ioc (0:ℝ) 1 ⊆ Ioi 0) ?_)
   intro x hx
   have hx1 : 1 < x := by
     rcases hx with ⟨hx0, hx1⟩
     simp only [mem_Ioc, not_and_or, not_le] at hx1
     rcases hx1 with h | h
     · exact absurd (mem_Ioi.mp hx0) h
     · exact h
   rw [acor_eq_zero hx1, mul_zero]
 have hO : ∫ r in (0:ℝ)..1, r * acor q r
     = ∫ r in (0:ℝ)..1, (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r := by
   apply intervalIntegral.integral_congr
   intro r hr
   rw [Set.uIcc_of_le zero_le_one] at hr
   show r * acor q r = (∫ s in (-(1:ℝ)/2)..(1/2 - r), q s * q (s + r)) * r
   rw [acor_eq_overlap hr.1 hr.2, mul_comm]
 rw [hR2, hS, hE, hI, hO]
end Swap
theorem JInf_eq_energy :
   JInf * MAM ^ 2
     = ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t := by
 rw [← swap_identity vAM_continuous abs_vAM_le]
 unfold JInf vConvAM
 have h := MAM_pos
 field_simp
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter
namespace AMW
open Zeta23
theorem integral_cos_half {c : ℝ} (hc : c ≠ 0) :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (c * t) = 2 * Real.sin (c / 2) / c := by
 rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos, smul_eq_mul,
   show c * (1/2) = c/2 by ring, show c * (-(1:ℝ)/2) = -(c/2) by ring, Real.sin_neg]
 field_simp
 ring
theorem cos_mul_cos_eq (a b t : ℝ) :
   Real.cos (a * t) * Real.cos (b * t) = (Real.cos ((a - b) * t) + Real.cos ((a + b) * t)) / 2 := by
 rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]; ring
theorem cos_lin_intervalIntegrable (c : ℝ) :
   IntervalIntegrable (fun t => Real.cos (c * t)) volume (-(1:ℝ)/2) (1/2) :=
 (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
theorem integral_cos_cos {a b : ℝ} (h1 : a - b ≠ 0) (h2 : a + b ≠ 0) :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (a * t) * Real.cos (b * t)
     = Real.sin ((a - b) / 2) / (a - b) + Real.sin ((a + b) / 2) / (a + b) := by
 simp_rw [cos_mul_cos_eq]
 rw [intervalIntegral.integral_div, intervalIntegral.integral_add (cos_lin_intervalIntegrable _)
   (cos_lin_intervalIntegrable _), integral_cos_half h1, integral_cos_half h2]
 field_simp
theorem two_pi_k_pos (n : ℕ) : 0 < 2 * π * ((n : ℝ) + 1) := by positivity
theorem integral_cos_k (n : ℕ) :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * ((n : ℝ) + 1) * t) = 0 := by
 rw [integral_cos_half (two_pi_k_pos n).ne']
 have : 2 * π * ((n : ℝ) + 1) / 2 = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
 rw [this, Real.sin_nat_mul_pi]; simp
theorem integral_cos_sqrt2 :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (Real.sqrt 2 * t) = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 rw [integral_cos_half hs.ne']
 field_simp
 rw [hsq]
theorem integral_cos_k_cos_k (m n : ℕ) :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (2 * π * ((m : ℝ) + 1) * t) * Real.cos (2 * π * ((n : ℝ) + 1) * t)
     = if m = n then 1 / 2 else 0 := by
 split_ifs with h
 · subst h
   simp_rw [cos_mul_cos_eq, sub_self, zero_mul, Real.cos_zero]
   rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
     (cos_lin_intervalIntegrable _), intervalIntegral.integral_const]
   have hc : 2 * π * ((m : ℝ) + 1) + 2 * π * ((m : ℝ) + 1) ≠ 0 := by
     have := two_pi_k_pos m; linarith
   rw [integral_cos_half hc]
   have : (2 * π * ((m : ℝ) + 1) + 2 * π * ((m : ℝ) + 1)) / 2 = ((2 * m + 2 : ℕ) : ℝ) * π := by
     push_cast; ring
   rw [this, Real.sin_nat_mul_pi]
   norm_num
 · have h1 : 2 * π * ((m : ℝ) + 1) - 2 * π * ((n : ℝ) + 1) ≠ 0 := by
     have hmn : (m : ℝ) ≠ n := by exact_mod_cast h
     intro h0
     apply hmn
     have hπ := Real.pi_pos
     have : 2 * π * ((m : ℝ) - n) = 0 := by linarith
     rcases mul_eq_zero.mp this with h' | h'
     · linarith
     · linarith
   have h2 : 2 * π * ((m : ℝ) + 1) + 2 * π * ((n : ℝ) + 1) ≠ 0 := by
     have := two_pi_k_pos m; have := two_pi_k_pos n; linarith
   rw [integral_cos_cos h1 h2]
   have e1 : (2 * π * ((m : ℝ) + 1) - 2 * π * ((n : ℝ) + 1)) / 2 = (((m : ℤ) - n : ℤ) : ℝ) * π := by
     push_cast; ring
   have e2 : (2 * π * ((m : ℝ) + 1) + 2 * π * ((n : ℝ) + 1)) / 2 = ((m + n + 2 : ℕ) : ℝ) * π := by
     push_cast; ring
   rw [e1, e2, Real.sin_int_mul_pi, Real.sin_nat_mul_pi]
   simp
def Xk (n : ℕ) : ℝ :=
 (-1) ^ (n + 1) * Real.sin (Real.sqrt 2 / 2) * (2 * Real.sqrt 2) / (2 - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)
theorem two_sub_ne (n : ℕ) : (2 : ℝ) - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 ≠ 0 := by
 have hπ := Real.pi_gt_three
 have hn : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
   have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
   nlinarith
 have : (9:ℝ) ≤ π ^ 2 := by nlinarith
 nlinarith
theorem integral_cos_sqrt2_cos_k (n : ℕ) :
   ∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (Real.sqrt 2 * t) * Real.cos (2 * π * ((n : ℝ) + 1) * t) = Xk n := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hk := two_pi_k_pos n
 have hπ := Real.pi_gt_three
 have h2 : Real.sqrt 2 + 2 * π * ((n : ℝ) + 1) ≠ 0 := by linarith
 have h1 : Real.sqrt 2 - 2 * π * ((n : ℝ) + 1) ≠ 0 := by
   have hs2 : Real.sqrt 2 < 2 := by
     rw [Real.sqrt_lt' (by norm_num)]; norm_num
   have : (2:ℝ) * π * 1 ≤ 2 * π * ((n : ℝ) + 1) := by
     have := Nat.cast_nonneg (α := ℝ) n
     nlinarith
   linarith
 rw [integral_cos_cos h1 h2]
 have e1 : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) / 2 = Real.sqrt 2 / 2 - ((n + 1 : ℕ) : ℝ) * π := by
   push_cast; ring
 have e2 : (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1)) / 2 = Real.sqrt 2 / 2 + ((n + 1 : ℕ) : ℝ) * π := by
   push_cast; ring
 rw [e1, e2, Real.sin_sub_nat_mul_pi, Real.sin_add_nat_mul_pi]
 unfold Xk
 have hd := two_sub_ne n
 have hprod : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) * (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1))
     = 2 - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by
   have e : (Real.sqrt 2 - 2 * π * ((n : ℝ) + 1)) * (Real.sqrt 2 + 2 * π * ((n : ℝ) + 1))
       = Real.sqrt 2 ^ 2 - (2 * π * ((n : ℝ) + 1)) ^ 2 := by ring
   rw [e, hsq]; ring
 rw [div_add_div _ _ h1 h2, hprod]
 congr 1
 ring
private theorem hasDerivAt_left' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
   HasDerivAt (fun x => (s - x) * Real.sin (ω * x) / ω - Real.cos (ω * x) / ω ^ 2)
     ((s - x) * Real.cos (ω * x)) x := by
 have h1 : HasDerivAt (fun x : ℝ => s - x) (-1) x := by
   simpa using (hasDerivAt_id x).const_sub s
 have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
 have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
   (Real.hasDerivAt_sin (ω * x)).comp x hlin
 have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
   (Real.hasDerivAt_cos (ω * x)).comp x hlin
 have h4 := ((h1.mul h2).div_const ω).sub (h3.div_const (ω ^ 2))
 exact h4.congr_deriv (by field_simp; ring)
private theorem hasDerivAt_right' (ω s : ℝ) (hω : ω ≠ 0) (x : ℝ) :
   HasDerivAt (fun x => (x - s) * Real.sin (ω * x) / ω + Real.cos (ω * x) / ω ^ 2)
     ((x - s) * Real.cos (ω * x)) x := by
 have h1 : HasDerivAt (fun x : ℝ => x - s) 1 x := by
   simpa using (hasDerivAt_id x).sub_const s
 have hlin : HasDerivAt (fun x : ℝ => ω * x) (ω * 1) x := (hasDerivAt_id x).const_mul ω
 have h2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * x) * (ω * 1)) x :=
   (Real.hasDerivAt_sin (ω * x)).comp x hlin
 have h3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * x) * (ω * 1)) x :=
   (Real.hasDerivAt_cos (ω * x)).comp x hlin
 have h4 := ((h1.mul h2).div_const ω).add (h3.div_const (ω ^ 2))
 exact h4.congr_deriv (by field_simp; ring)
theorem kernel_cos {ω s : ℝ} (hω : ω ≠ 0) (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
   ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * Real.cos (ω * t)
     = Real.sin (ω / 2) / ω + 2 * Real.cos (ω / 2) / ω ^ 2 - 2 * Real.cos (ω * s) / ω ^ 2 := by
 have hcont : ∀ a b : ℝ, IntervalIntegrable
     (fun t => |s - t| * Real.cos (ω * t)) MeasureTheory.volume a b := fun a b =>
   (Continuous.intervalIntegrable (by fun_prop) a b)
 have hsplit : ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * Real.cos (ω * t)
     = (∫ t in (-(1:ℝ)/2)..s, |s - t| * Real.cos (ω * t))
       + ∫ t in s..(1/2), |s - t| * Real.cos (ω * t) :=
   (intervalIntegral.integral_add_adjacent_intervals (hcont _ _) (hcont _ _)).symm
 have hleft : ∫ t in (-(1:ℝ)/2)..s, |s - t| * Real.cos (ω * t)
     = ∫ t in (-(1:ℝ)/2)..s, (s - t) * Real.cos (ω * t) := by
   apply intervalIntegral.integral_congr
   intro x hx
   rw [Set.uIcc_of_le hs1] at hx
   show |s - x| * Real.cos (ω * x) = (s - x) * Real.cos (ω * x)
   rw [abs_of_nonneg (by linarith [hx.2] : (0:ℝ) ≤ s - x)]
 have hleft2 : ∫ t in (-(1:ℝ)/2)..s, (s - t) * Real.cos (ω * t)
     = ((s - s) * Real.sin (ω * s) / ω - Real.cos (ω * s) / ω ^ 2)
       - ((s - (-(1:ℝ)/2)) * Real.sin (ω * (-(1:ℝ)/2)) / ω - Real.cos (ω * (-(1:ℝ)/2)) / ω ^ 2) :=
   intervalIntegral.integral_eq_sub_of_hasDerivAt
     (fun x _ => hasDerivAt_left' ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
 have hright : ∫ t in s..(1/2), |s - t| * Real.cos (ω * t)
     = ∫ t in s..(1/2), (t - s) * Real.cos (ω * t) := by
   apply intervalIntegral.integral_congr
   intro x hx
   rw [Set.uIcc_of_le hs2] at hx
   show |s - x| * Real.cos (ω * x) = (x - s) * Real.cos (ω * x)
   rw [abs_of_nonpos (by linarith [hx.1] : s - x ≤ 0), neg_sub]
 have hright2 : ∫ t in s..(1/2), (t - s) * Real.cos (ω * t)
     = (((1:ℝ)/2 - s) * Real.sin (ω * (1/2)) / ω + Real.cos (ω * (1/2)) / ω ^ 2)
       - ((s - s) * Real.sin (ω * s) / ω + Real.cos (ω * s) / ω ^ 2) :=
   intervalIntegral.integral_eq_sub_of_hasDerivAt
     (fun x _ => hasDerivAt_right' ω s hω x) (Continuous.intervalIntegrable (by fun_prop) _ _)
 rw [hsplit, hleft, hleft2, hright, hright2,
   show ω * (1/2) = ω / 2 by ring, show ω * (-(1:ℝ)/2) = -(ω / 2) by ring, Real.sin_neg, Real.cos_neg]
 field_simp
 ring
def dAM (n : ℕ) : ℝ := (cAM (n + 1) : ℝ)
def ek (n : ℕ) (t : ℝ) : ℝ := Real.cos (2 * π * ((n : ℝ) + 1) * t)
theorem ek_continuous (n : ℕ) : Continuous (ek n) := by unfold ek; fun_prop
theorem vAM_eq' (t : ℝ) :
   vAM t = Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range 12, dAM n * ek n t := by
 rw [vAM_eq]
 unfold pAM dAM ek
 congr 1
 refine Finset.sum_congr rfl fun n _ => ?_
 rw [ωAM_succ]
theorem kernel_vAM {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
   ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t
     = (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2) - Real.cos (Real.sqrt 2 * s))
       + ∑ n ∈ Finset.range 12,
           dAM n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hpt : ∀ t, |s - t| * vAM t
     = |s - t| * Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range 12, dAM n * (|s - t| * ek n t) := by
   intro t
   rw [vAM_eq', mul_add, Finset.mul_sum]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hI0 : IntervalIntegrable (fun t => |s - t| * Real.cos (Real.sqrt 2 * t)) volume (-(1:ℝ)/2) (1/2) :=
   (by fun_prop : Continuous fun t => |s - t| * Real.cos (Real.sqrt 2 * t)).intervalIntegrable _ _
 have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * (|s - t| * ek n t))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   ((continuous_const.mul ((continuous_const.sub continuous_id).abs.mul (ek_continuous n)))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * (|s - t| * ek n t))
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     ((continuous_const.sub continuous_id).abs.mul (ek_continuous n))).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hI0 hS,
   intervalIntegral.integral_finsetSum hIn, kernel_cos hs.ne' hs1 hs2, hsq]
 congr 1
 · field_simp
 · refine Finset.sum_congr rfl fun n _ => ?_
   rw [intervalIntegral.integral_const_mul]
   congr 1
   unfold ek
   rw [kernel_cos (two_pi_k_pos n).ne' hs1 hs2]
   have e1 : 2 * π * ((n : ℝ) + 1) / 2 = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
   rw [e1, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
   have hk := two_pi_k_pos n
   have hπ := Real.pi_pos
   field_simp
   ring
def betaV : ℝ :=
 Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2)
   + ∑ n ∈ Finset.range 12, dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
def rV (s : ℝ) : ℝ :=
 ∑ n ∈ Finset.range 12, dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s
theorem rV_continuous : Continuous rV := by
 unfold rV
 exact continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)
theorem vAM_add_kernel {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
   vAM s + ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t = betaV + rV s := by
 rw [kernel_vAM hs1 hs2, vAM_eq']
 unfold betaV rV
 have e : ∀ n ∈ Finset.range 12, dAM n * ek n s
     + dAM n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
     = dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
       + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s := by
   intro n _
   have hk := two_pi_k_pos n
   have hπ := Real.pi_pos
   field_simp
   ring
 have hsum := Finset.sum_congr rfl e
 rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
 linarith
theorem integral_vAM :
   ∫ t in (-(1:ℝ)/2)..(1/2), vAM t = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
 simp_rw [vAM_eq']
 have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * ek n t)
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * ek n t)
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
 rw [intervalIntegral.integral_add (cos_lin_intervalIntegrable _) hS,
   intervalIntegral.integral_finsetSum hIn, integral_cos_sqrt2]
 have h0 : ∀ n ∈ Finset.range 12, ∫ t in (-(1:ℝ)/2)..(1/2), dAM n * ek n t = 0 := by
   intro n _
   rw [intervalIntegral.integral_const_mul]
   unfold ek
   rw [integral_cos_k, mul_zero]
 rw [Finset.sum_eq_zero h0, add_zero]
theorem integral_vAM_ek {m : ℕ} (hm : m ∈ Finset.range 12) :
   ∫ t in (-(1:ℝ)/2)..(1/2), vAM t * ek m t = Xk m + dAM m / 2 := by
 have hpt : ∀ t, vAM t * ek m t
     = Real.cos (Real.sqrt 2 * t) * ek m t + ∑ n ∈ Finset.range 12, dAM n * (ek n t * ek m t) := by
   intro t
   rw [vAM_eq', add_mul, Finset.sum_mul]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hI0 : IntervalIntegrable (fun t => Real.cos (Real.sqrt 2 * t) * ek m t) volume (-(1:ℝ)/2) (1/2) :=
   ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul (ek_continuous m)).intervalIntegrable _ _
 have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable (fun t => dAM n * (ek n t * ek m t))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range 12, dAM n * (ek n t * ek m t))
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hI0 hS, intervalIntegral.integral_finsetSum hIn]
 unfold ek
 rw [integral_cos_sqrt2_cos_k]
 congr 1
 have h : ∀ n ∈ Finset.range 12, ∫ t in (-(1:ℝ)/2)..(1/2),
     dAM n * (Real.cos (2 * π * ((n : ℝ) + 1) * t) * Real.cos (2 * π * ((m : ℝ) + 1) * t))
     = if n = m then dAM n / 2 else 0 := by
   intro n _
   rw [intervalIntegral.integral_const_mul, integral_cos_k_cos_k]
   split_ifs <;> ring
 rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range 12) m (fun n => dAM n / 2), if_pos hm]
theorem euler_lagrange (n : ℕ) :
   (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * Xk n
     + (-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) = 0 := by
 unfold Xk
 have hd := two_sub_ne n
 have hD : (2:ℝ) - 4 * π ^ 2 * ((n : ℝ) + 1) ^ 2 = 2 * (1 - 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) := by ring
 rw [hD] at hd ⊢
 set E : ℝ := 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 with hEdef
 have hE : 0 < E := by rw [hEdef]; positivity
 have h1E : 1 - E ≠ 0 := fun h => hd (by rw [h]; ring)
 field_simp
 ring
def PAM : ℝ := ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
theorem energy_total :
   (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2)
     + (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t)
     = Real.sin (Real.sqrt 2 / 2) ^ 2
       + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) + PAM := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hK : ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t
     = ∫ s in (-(1:ℝ)/2)..(1/2), vAM s * (betaV + rV s - vAM s) := by
   apply intervalIntegral.integral_congr
   intro s hs'
   rw [Set.uIcc_of_le (by norm_num)] at hs'
   have := vAM_add_kernel hs'.1 hs'.2
   show vAM s * _ = vAM s * (betaV + rV s - vAM s)
   congr 1
   linarith
 have hA : IntervalIntegrable (fun t => vAM t ^ 2) volume (-(1:ℝ)/2) (1/2) :=
   (vAM_continuous.pow 2).intervalIntegrable _ _
 have hB : IntervalIntegrable (fun s => vAM s * (betaV + rV s - vAM s)) volume (-(1:ℝ)/2) (1/2) :=
   (vAM_continuous.mul ((continuous_const.add rV_continuous).sub vAM_continuous)).intervalIntegrable _ _
 rw [hK, ← intervalIntegral.integral_add hA hB]
 have hpt : ∀ s, vAM s ^ 2 + vAM s * (betaV + rV s - vAM s)
     = betaV * vAM s + ∑ n ∈ Finset.range 12,
         dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s) := by
   intro s
   have alg : ∀ a b S : ℝ, a ^ 2 + a * (b + S - a) = b * a + a * S := fun a b S => by ring
   rw [alg, rV, Finset.mul_sum]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hIn : ∀ n ∈ Finset.range 12, IntervalIntegrable
     (fun s => dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul (vAM_continuous.mul (ek_continuous n))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun s => ∑ n ∈ Finset.range 12,
     dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s)) volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     (vAM_continuous.mul (ek_continuous n))).intervalIntegrable _ _
 have hC : IntervalIntegrable (fun s => betaV * vAM s) volume (-(1:ℝ)/2) (1/2) :=
   (continuous_const.mul vAM_continuous).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hC hS,
   intervalIntegral.integral_finsetSum hIn, intervalIntegral.integral_const_mul, integral_vAM]
 have hterm : ∀ n ∈ Finset.range 12,
     ∫ s in (-(1:ℝ)/2)..(1/2), dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (vAM s * ek n s)
       = dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2) := by
   intro n hn
   rw [intervalIntegral.integral_const_mul, integral_vAM_ek hn]
 rw [Finset.sum_congr rfl hterm]
 unfold betaV PAM
 have hEL : ∀ n ∈ Finset.range 12,
     dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
       + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2)
     = dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
   intro n _
   have h := euler_lagrange n
   have hk2 : (0:ℝ) < 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
   have e : dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
       + dAM n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + dAM n / 2)
       = dAM n * ((1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * Xk n
           + (-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)))
         + dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
     field_simp
     ring
   rw [e, h, mul_zero, zero_add]
 have hsum := Finset.sum_congr rfl hEL
 rw [Finset.sum_add_distrib] at hsum
 rw [add_mul, Finset.sum_mul]
 have e2 : (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2))
       * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
     = Real.sin (Real.sqrt 2 / 2) ^ 2 + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) := by
   field_simp
 rw [e2]
 linarith
def HW : ℝ := 2 - (ThmD.cRatio 1 aInf bInf JInf)⁻¹
theorem sin_theta0_pos : 0 < Real.sin (Real.sqrt 2 / 2) := by
 apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
 have hs2 : Real.sqrt 2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
 linarith [Real.pi_gt_three]
theorem HW_eq :
   HW = 3 / 2 - Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
     - PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hsin := sin_theta0_pos
 have hM := MAM_pos
 have hJ := JInf_eq_energy
 have hE := energy_total
 have hb : bInf = (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2) / MAM ^ 2 := by
   unfold bInf
   rw [← intervalIntegral.integral_div]
   congr 1; funext t; ring
 have ha : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
   unfold aInf; rw [integral_vAM]
 have hJ' : JInf = (∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t) / MAM ^ 2 := by
   rw [← hJ]; field_simp
 unfold HW ThmD.cRatio
 rw [hb, ha, hJ']
 have hden : (∫ t in (-(1:ℝ)/2)..(1/2), vAM t ^ 2) / MAM ^ 2 + 1 ^ 2
     * ((∫ s in (-(1:ℝ)/2)..(1/2), vAM s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * vAM t) / MAM ^ 2)
     = (Real.sin (Real.sqrt 2 / 2) ^ 2
       + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) + PAM) / MAM ^ 2 := by
   rw [← hE]; ring
 rw [hden]
 generalize Real.sin (Real.sqrt 2 / 2) = S at hsin ⊢
 generalize Real.cos (Real.sqrt 2 / 2) = C
 have key : (1 * (Real.sqrt 2 * S / MAM) ^ 2 / ((S ^ 2 + Real.sqrt 2 * S * C + PAM) / MAM ^ 2))⁻¹
     = (S ^ 2 + Real.sqrt 2 * S * C + PAM) / (2 * S ^ 2) := by
   rw [div_pow, mul_pow, hsq, inv_div]
   field_simp
 have hcs : C / (Real.sqrt 2 * S) = Real.sqrt 2 * C / (2 * S) := by
   rw [div_eq_div_iff (by positivity) (by positivity)]
   linear_combination (-(C * S)) * hsq
 rw [key, hcs]
 field_simp
 ring
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace AMW
open Zeta23
/-
Modified by R. Arun Chandru, 2026-10-12: merge the order-20 window enclosure
from master-of-puppets3 and propagate the sharpened rational HW floor.
Terminal HW-floor refinement adapted from Yuhang Shi.
Copyright (c) 2026 Yuhang Shi.
SPDX-License-Identifier: Apache-2.0
-/
theorem taylor20_F (θ : ℝ) (hθ : |θ| ≤ 1) :
   |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000)|
       ≤ |θ|^20 * (1/2317049531596800000) ∧
   |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000)|
       ≤ |θ|^20 * (1/2317049531596800000) := by
 have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
   simpa using hθ
 have hb := Complex.exp_bound hx (n := 20) (by norm_num)
 have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
 have hsum : ∑ m ∈ Finset.range 20, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
     = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I := by
   simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
   apply Complex.ext <;> · simp [pow_succ]; ring
 rw [hsum, hnx] at hb
 have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I)‖ ≤ |θ|^20 * (1/2317049531596800000) := by
   refine hb.trans (le_of_eq ?_)
   norm_num
 constructor
 · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
 · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]
theorem sqrt2_half_bounds :
   (707106781186547524400844362104/10^30 : ℝ) ≤ Real.sqrt 2 / 2 ∧
     Real.sqrt 2 / 2 ≤ 707106781186547524400844362105/10^30 := by
 have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 constructor <;> nlinarith [h2, hnn]
theorem cos_theta0_le : Real.cos (Real.sqrt 2 / 2) ≤ 760244597075630151253567702555 / 10 ^ 30 := by
 have hb := sqrt2_half_bounds
 set r : ℝ := 707106781186547524400844362104/10^30 with hr
 have hr0 : 0 ≤ r := by rw [hr]; norm_num
 have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
 have hmono : Real.cos (Real.sqrt 2 / 2) ≤ Real.cos r :=
   Real.cos_le_cos_of_nonneg_of_le_pi hr0 (by linarith [hb.2, Real.pi_gt_three]) hb.1
 have ht := (abs_le.mp (taylor20_F r hr1).1).2
 rw [abs_of_nonneg hr0] at ht
 have hv : (1 - r^2/2 + r^4/24 - r^6/720 + r^8/40320 - r^10/3628800 + r^12/479001600 - r^14/87178291200 + r^16/20922789888000 - r^18/6402373705728000) + r ^ 20 * (1/2317049531596800000)
     ≤ 760244597075630151253567702555 / 10 ^ 30 := by
   rw [hr]; norm_num
 linarith
theorem sin_theta0_ge : 649636939080062444129454621098 / 10 ^ 30 ≤ Real.sin (Real.sqrt 2 / 2) := by
 have hb := sqrt2_half_bounds
 have hc := cos_theta0_le
 have hc0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
   Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
 have hcsq : Real.cos (Real.sqrt 2 / 2) ^ 2 ≤ (760244597075630151253567702555 / 10 ^ 30 : ℝ) ^ 2 :=
   pow_le_pow_left₀ hc0 hc 2
 have hcircle := Real.sin_sq_add_cos_sq (Real.sqrt 2 / 2)
 have hs0 := sin_theta0_pos
 have hsq : (649636939080062444129454621098 / 10 ^ 30 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 := by
   nlinarith only [hcsq, hcircle]
 nlinarith only [hsq, hs0]
def PAMhi : ℝ :=
 ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * (314159265358979323847 / 10 ^ 20) ^ 2 * ((n : ℝ) + 1) ^ 2))
theorem PAM_le : PAM ≤ PAMhi := by
 unfold PAM PAMhi
 apply Finset.sum_le_sum
 intro n _
 apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
 apply sub_le_sub_left
 have hπ := Real.pi_lt_d20
 have hπ0 := Real.pi_pos
 have hk : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
 apply one_div_le_one_div_of_le (by positivity)
 have : π ^ 2 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 := by
   apply pow_le_pow_left₀ hπ0.le; linarith
 have := mul_le_mul_of_nonneg_right this hk.le
 nlinarith
theorem PAMhi_nonneg : 0 ≤ PAMhi := by
 unfold PAMhi
 apply Finset.sum_nonneg
 intro n _
 apply mul_nonneg (sq_nonneg _)
 have hk : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
   have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
   nlinarith
 have : 1 / (4 * (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ 1 / 2 := by
   rw [div_le_div_iff₀ (by positivity) (by norm_num)]
   nlinarith
 linarith
theorem floor_numeric :
   (6721237468782417141365717707344332375586 / 10 ^ 40 : ℝ) ≤ 3 / 2 - (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30))
     - PAMhi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) := by
 unfold PAMhi dAM
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num
theorem HW_ge : (6721237468782417141365717707344332375586 / 10 ^ 40 : ℝ) ≤ HW := by
 rw [HW_eq]
 have hc := cos_theta0_le
 have hs := sin_theta0_ge
 have hb := sqrt2_half_bounds
 have hP := PAM_le
 have hP0 := PAMhi_nonneg
 have hs0 : (0:ℝ) < 649636939080062444129454621098 / 10 ^ 30 := by norm_num
 have hr0 : (0:ℝ) < 707106781186547524400844362104/10^30 := by norm_num
 have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
   Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
 have hden : 2 * (707106781186547524400844362104/10^30 : ℝ) * (649636939080062444129454621098 / 10 ^ 30)
     ≤ Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
   have h2 : 2 * (707106781186547524400844362104/10^30 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
   exact mul_le_mul h2 hs hs0.le (Real.sqrt_nonneg 2)
 have h1 : Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
     ≤ (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30)) :=
   div_le_div₀ (by norm_num) hc (by positivity) hden
 have hsq : (649636939080062444129454621098 / 10 ^ 30 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 :=
   pow_le_pow_left₀ hs0.le hs 2
 have h2 : PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤ PAMhi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) :=
   div_le_div₀ hP0 hP (by positivity) (by linarith)
 have := floor_numeric
 linarith
theorem aInf_eq : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
 unfold aInf; rw [integral_vAM]
theorem aInf_gt_half : 1 / 2 < aInf := by
 rw [aInf_eq]
 have hb := sqrt2_half_bounds
 have hs := sin_theta0_ge
 unfold MAM
 rw [lt_div_iff₀ (by norm_num)]
 have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
 nlinarith
theorem aInf_sq_le_bInf : aInf ^ 2 ≤ bInf := by
 set q : ℝ → ℝ := fun s => vAM s / MAM with hq
 have hqc : Continuous q := vAM_continuous.div_const _
 have ha : aInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s := by
   unfold aInf; rw [hq, intervalIntegral.integral_div]
 have hb : bInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s ^ 2 := rfl
 have h0 : 0 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 :=
   intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
 have hexp : ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 = bInf - aInf ^ 2 := by
   have e : (fun s => (q s - aInf) ^ 2) = fun s => q s ^ 2 - 2 * aInf * q s + aInf ^ 2 := by
     funext s; ring
   have i1 : IntervalIntegrable (fun s => q s ^ 2 - 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
     ((hqc.pow 2).sub (continuous_const.mul hqc)).intervalIntegrable _ _
   have i2 : IntervalIntegrable (fun s => q s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
     (hqc.pow 2).intervalIntegrable _ _
   have i3 : IntervalIntegrable (fun s => 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
     (continuous_const.mul hqc).intervalIntegrable _ _
   rw [e, intervalIntegral.integral_add i1 intervalIntegrable_const,
     intervalIntegral.integral_sub i2 i3,
     intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← ha, ← hb]
   simp only [smul_eq_mul]
   ring
 linarith
theorem bInf_gt_half : 1 / 2 < bInf := by
 have h1 := aInf_gt_half
 have h2 := aInf_sq_le_bInf
 have hb := sqrt2_half_bounds
 have hs := sin_theta0_ge
 have ha : (734 / 1000 : ℝ) < aInf := by
   rw [aInf_eq]
   unfold MAM
   rw [lt_div_iff₀ (by norm_num)]
   have h2' : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
   nlinarith
 nlinarith
theorem eventually_bW_ge_half {P : Params} (hP : P.Valid) :
   ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).b := by
 filter_upwards [(tendsto_bW hP).eventually (lt_mem_nhds bInf_gt_half)] with T h
 exact h.le
end AMW
end
noncomputable section
open Real
namespace AMW
open Zeta23
def atW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : Params := ⟨fun x => W T (P.L T / 2 - P.w * x), P.lam, P.w⟩
section rfl
variable (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ)
@[simp] theorem atW_L : (atW P W T).L = P.L := rfl
theorem atW_tau_eq (k : ℤ) : (atW P W T).tau T k = T + k * (2 * π / P.L T) := rfl
end rfl
variable {P : Params} {W : ℝ → ℝ → ℝ}
theorem atW_phi (T : ℝ) (hw : P.w ≠ 0) (hev : ∀ u, W T (-u) = W T u) : (atW P W T).phi T = W T := by
 funext u
 show W T (P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w)) = W T u
 have e : P.L T / 2 - P.w * ((P.lam * l T / 2 - |u|) / P.w) = |u| := by
   simp only [Params.L]; field_simp; ring
 rw [e]
 rcases le_or_gt 0 u with hu | hu
 · rw [abs_of_nonneg hu]
 · rw [abs_of_neg hu]; exact hev u
theorem atW_phi_valid (T : ℝ) (hP : P.Valid) (hev : ∀ u, W T (-u) = W T u) : (atW P W T).phi T = W T :=
 atW_phi T (by linarith [hP.one_le_w]) hev
section
variable (T : ℝ) (hP : P.Valid) (hev : ∀ u, W T (-u) = W T u)
include hP hev
theorem atW_localFun : (atW P W T).localFun T = AdmWindow.localFun (W T) (P.L T) := by
 rw [Params.localFun_eq_admWindow, atW_phi_valid T hP hev]; rfl
theorem atW_a : (atW P W T).a T = AdmWindow.av (W T) (P.L T) := by
 rw [show (atW P W T).a T = ((atW P W T).localFun T).a from rfl, atW_localFun T hP hev]; rfl
theorem atW_phiHat : (atW P W T).phiHat T = AdmWindow.vHat (W T) := by
 show AdmWindow.vHat ((atW P W T).phi T) = _
 rw [atW_phi_valid T hP hev]
theorem atW_phiHatR : (atW P W T).phiHatR T = AdmWindow.vHatR (W T) := by
 show AdmWindow.vHatR ((atW P W T).phi T) = _
 rw [atW_phi_valid T hP hev]
theorem atW_trGtilde :
   (atW P W T).trGtilde T = PrimeSide.trGtA (P.toSetting T) (AdmWindow.localFun (W T) (P.L T)) := by
 rw [← PrimeSide.trGtA_concrete (atW P W T) T, atW_localFun T hP hev]; rfl
theorem atW_trGtildeSq :
   (atW P W T).trGtildeSq T = PrimeSide.trGt2A (P.toSetting T) (AdmWindow.localFun (W T) (P.L T)) := by
 rw [← PrimeSide.trGt2A_concrete (atW P W T) T, atW_localFun T hP hev]; rfl
end
end AMW
end
noncomputable section
open Real
namespace AMW
theorem cos_sin_taylor12 (θ : ℝ) (hθ : |θ| ≤ 1) :
   |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800)|
       ≤ |θ|^12 * (13/5748019200) ∧
   |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800)|
       ≤ |θ|^12 * (13/5748019200) := by
 have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by simpa using hθ
 have hb := Complex.exp_bound hx (n := 12) (by norm_num)
 have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
 have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
     = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
         * Complex.I := by
   simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
   apply Complex.ext <;> · simp [pow_succ]; ring
 rw [hsum, hnx] at hb
 have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
         * Complex.I)‖ ≤ |θ|^12 * (13/5748019200) := by
   refine hb.trans (le_of_eq ?_)
   norm_num
 constructor
 · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
 · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]
def tCosQ (t : ℚ) : ℚ :=
 let s := t * t
 1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
def tSinQ (t : ℚ) : ℚ :=
 let s := t * t
 t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
def errQ : ℚ := 13/5748019200
def fl (x : ℚ) : ℚ := ((⌊x * 10000000000⌋ : ℤ) : ℚ) / 10000000000
def cl (x : ℚ) : ℚ := ((⌈x * 10000000000⌉ : ℤ) : ℚ) / 10000000000
theorem fl_le (x : ℚ) : ((fl x : ℚ) : ℝ) ≤ (x : ℝ) := by
 refine Rat.cast_le.mpr ?_
 unfold fl; rw [div_le_iff₀ (by norm_num)]; exact Int.floor_le _
theorem le_cl (x : ℚ) : (x : ℝ) ≤ ((cl x : ℚ) : ℝ) := by
 refine Rat.cast_le.mpr ?_
 unfold cl; rw [le_div_iff₀ (by norm_num)]; exact Int.le_ceil _
theorem tCosQ_cast (q : ℚ) : ((tCosQ q : ℚ) : ℝ)
   = 1 - (q:ℝ)^2/2 + (q:ℝ)^4/24 - (q:ℝ)^6/720 + (q:ℝ)^8/40320 - (q:ℝ)^10/3628800 := by
 simp only [tCosQ]; push_cast; ring
theorem tSinQ_cast (q : ℚ) : ((tSinQ q : ℚ) : ℝ)
   = (q:ℝ) - (q:ℝ)^3/6 + (q:ℝ)^5/120 - (q:ℝ)^7/5040 + (q:ℝ)^9/362880 - (q:ℝ)^11/39916800 := by
 simp only [tSinQ]; push_cast; ring
theorem errQ_cast : ((errQ : ℚ) : ℝ) = 13/5748019200 := by simp only [errQ]; push_cast; ring
private lemma err_scale {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
   |t| ^ 12 * (13 / 5748019200) ≤ 13/5748019200 := by
 rw [abs_of_nonneg h0]
 have : t ^ 12 ≤ 1 := pow_le_one₀ h0 h1
 nlinarith
private lemma one_le_pi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
theorem cos_ge_of {θ : ℝ} {u : ℚ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : (u : ℝ) ≤ 1) :
   ((tCosQ u - errQ : ℚ) : ℝ) ≤ Real.cos θ := by
 have h0u : (0:ℝ) ≤ u := h0.trans hu
 have hmono : Real.cos u ≤ Real.cos θ :=
   Real.cos_le_cos_of_nonneg_of_le_pi h0 (hu1.trans one_le_pi) hu
 have ht := abs_le.mp (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).1
 have he := err_scale h0u hu1
 push_cast; rw [tCosQ_cast, errQ_cast]
 linarith [ht.1, ht.2]
theorem cos_le_of {θ : ℝ} {l : ℚ} (h0 : (0:ℝ) ≤ l) (hl : (l:ℝ) ≤ θ) (hθ1 : θ ≤ 1) :
   Real.cos θ ≤ ((tCosQ l + errQ : ℚ) : ℝ) := by
 have hl1 : (l:ℝ) ≤ 1 := hl.trans hθ1
 have hmono : Real.cos θ ≤ Real.cos l :=
   Real.cos_le_cos_of_nonneg_of_le_pi h0 (hθ1.trans one_le_pi) hl
 have ht := abs_le.mp (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).1
 have he := err_scale h0 hl1
 push_cast; rw [tCosQ_cast, errQ_cast]
 linarith [ht.1, ht.2]
theorem sin_ge_of {θ : ℝ} {l : ℚ} (h0 : (0:ℝ) ≤ l) (hl : (l:ℝ) ≤ θ) (hθ1 : θ ≤ 1) :
   ((tSinQ l - errQ : ℚ) : ℝ) ≤ Real.sin θ := by
 have hl1 : (l:ℝ) ≤ 1 := hl.trans hθ1
 have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
 have hmono : Real.sin l ≤ Real.sin θ :=
   Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hθ1.trans hpi2) hl
 have ht := abs_le.mp (cos_sin_taylor12 l (by rw [abs_of_nonneg h0]; exact hl1)).2
 have he := err_scale h0 hl1
 push_cast; rw [tSinQ_cast, errQ_cast]
 linarith [ht.1, ht.2]
theorem sin_le_of {θ : ℝ} {u : ℚ} (h0 : 0 ≤ θ) (hu : θ ≤ u) (hu1 : (u:ℝ) ≤ 1) :
   Real.sin θ ≤ ((tSinQ u + errQ : ℚ) : ℝ) := by
 have h0u : (0:ℝ) ≤ u := h0.trans hu
 have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
 have hmono : Real.sin θ ≤ Real.sin u :=
   Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (hu1.trans hpi2) hu
 have ht := abs_le.mp (cos_sin_taylor12 u (by rw [abs_of_nonneg h0u]; exact hu1)).2
 have he := err_scale h0u hu1
 push_cast; rw [tSinQ_cast, errQ_cast]
 linarith [ht.1, ht.2]
def piLoQ : ℚ := 3141592 / 10 ^ 6
def piHiQ : ℚ := 3141593 / 10 ^ 6
def s2LoQ : ℚ := 14142135 / 10 ^ 7
def s2HiQ : ℚ := 14142136 / 10 ^ 7
theorem piLoQ_le : ((piLoQ : ℚ) : ℝ) ≤ Real.pi := by
 have h := Real.pi_gt_d6; simp only [piLoQ]; push_cast; norm_num at h ⊢; linarith
theorem piHiQ_ge : Real.pi ≤ ((piHiQ : ℚ) : ℝ) := by
 have h := Real.pi_lt_d6; simp only [piHiQ]; push_cast; norm_num at h ⊢; linarith
theorem s2LoQ_le : ((s2LoQ : ℚ) : ℝ) ≤ Real.sqrt 2 := by
 have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 simp only [s2LoQ]; push_cast; nlinarith
theorem s2HiQ_ge : Real.sqrt 2 ≤ ((s2HiQ : ℚ) : ℝ) := by
 have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 simp only [s2HiQ]; push_cast; nlinarith
def imulZ (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
 if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
def isub (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)
def InI (I : ℚ × ℚ) (x : ℝ) : Prop := ((I.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((I.2 : ℚ) : ℝ)
theorem imulZ_sound (e : ℤ) {I : ℚ × ℚ} {f : ℝ} (h : InI I f) : InI (imulZ e I) ((e:ℝ) * f) := by
 obtain ⟨h1, h2⟩ := h
 unfold imulZ InI
 split_ifs with he
 · have he' : (0:ℝ) ≤ e := by exact_mod_cast he
   simp only; push_cast
   exact ⟨mul_le_mul_of_nonneg_left h1 he', mul_le_mul_of_nonneg_left h2 he'⟩
 · have he' : (e:ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
   simp only; push_cast
   exact ⟨mul_le_mul_of_nonpos_left h2 he', mul_le_mul_of_nonpos_left h1 he'⟩
theorem iadd_sound {I J : ℚ × ℚ} {f g : ℝ} (hI : InI I f) (hJ : InI J g) : InI (iadd I J) (f + g) := by
 unfold iadd InI at *; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem isub_sound {I J : ℚ × ℚ} {f g : ℝ} (hI : InI I f) (hJ : InI J g) : InI (isub I J) (f - g) := by
 unfold isub InI at *; simp only; push_cast; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
def piMul (S : ℚ × ℚ) : ℚ × ℚ := (min (piLoQ * S.1) (piHiQ * S.1), max (piLoQ * S.2) (piHiQ * S.2))
theorem piMul_sound {S : ℚ × ℚ} {x : ℝ} (h : InI S x) : InI (piMul S) (Real.pi * x) := by
 obtain ⟨h1, h2⟩ := h
 have hlo := piLoQ_le; have hhi := piHiQ_ge
 have hp0 : (0:ℝ) ≤ Real.pi := Real.pi_pos.le
 unfold piMul InI
 simp only; push_cast
 constructor
 · rcases le_or_gt 0 (S.1 : ℝ) with hs | hs
   · refine (min_le_left _ _).trans ?_
     calc (piLoQ : ℝ) * S.1 ≤ Real.pi * S.1 := mul_le_mul_of_nonneg_right hlo hs
       _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left h1 hp0
   · refine (min_le_right _ _).trans ?_
     calc (piHiQ : ℝ) * S.1 ≤ Real.pi * S.1 := mul_le_mul_of_nonpos_right hhi hs.le
       _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left h1 hp0
 · rcases le_or_gt 0 (S.2 : ℝ) with hs | hs
   · refine le_trans ?_ (le_max_right _ _)
     calc Real.pi * x ≤ Real.pi * S.2 := mul_le_mul_of_nonneg_left h2 hp0
       _ ≤ (piHiQ : ℝ) * S.2 := mul_le_mul_of_nonneg_right hhi hs
   · refine le_trans ?_ (le_max_left _ _)
     calc Real.pi * x ≤ Real.pi * S.2 := mul_le_mul_of_nonneg_left h2 hp0
       _ ≤ (piLoQ : ℝ) * S.2 := mul_le_mul_of_nonpos_right hlo hs.le
def TLo (a : ℚ) : ℚ := fl (piLoQ * a)
def THi (a : ℚ) : ℚ := cl (piHiQ * a)
def cosI (a : ℚ) : ℚ × ℚ := (fl (tCosQ (THi a) - errQ), cl (tCosQ (TLo a) + errQ))
def sinI (a : ℚ) : ℚ × ℚ := (fl (tSinQ (TLo a) - errQ), cl (tSinQ (THi a) + errQ))
theorem TLo_le {a : ℚ} (ha : 0 ≤ a) : ((TLo a : ℚ) : ℝ) ≤ Real.pi * a :=
 (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right piLoQ_le (by exact_mod_cast ha))
theorem le_THi {a : ℚ} (ha : 0 ≤ a) : Real.pi * a ≤ ((THi a : ℚ) : ℝ) :=
 le_trans (by push_cast; exact mul_le_mul_of_nonneg_right piHiQ_ge (by exact_mod_cast ha)) (le_cl _)
theorem cosI_sound {a : ℚ} (ha : 0 ≤ a) (h0 : 0 ≤ TLo a) (h1 : THi a ≤ 1) :
   InI (cosI a) (Real.cos (Real.pi * a)) := by
 have hθ0 : 0 ≤ Real.pi * a := mul_nonneg Real.pi_pos.le (by exact_mod_cast ha)
 have h1' : ((THi a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
 have h0' : (0:ℝ) ≤ ((TLo a : ℚ) : ℝ) := by exact_mod_cast h0
 exact ⟨(fl_le _).trans (cos_ge_of hθ0 (le_THi ha) h1'),
   (cos_le_of h0' (TLo_le ha) ((le_THi ha).trans h1')).trans (le_cl _)⟩
theorem sinI_sound {a : ℚ} (ha : 0 ≤ a) (h0 : 0 ≤ TLo a) (h1 : THi a ≤ 1) :
   InI (sinI a) (Real.sin (Real.pi * a)) := by
 have hθ0 : 0 ≤ Real.pi * a := mul_nonneg Real.pi_pos.le (by exact_mod_cast ha)
 have h1' : ((THi a : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
 have h0' : (0:ℝ) ≤ ((TLo a : ℚ) : ℝ) := by exact_mod_cast h0
 exact ⟨(fl_le _).trans (sin_ge_of h0' (TLo_le ha) ((le_THi ha).trans h1')),
   (sin_le_of hθ0 (le_THi ha) h1').trans (le_cl _)⟩
def csA : ℕ → ℤ × ℤ
 | 0 => (1, 0)
 | k+1 => (-(csA k).2, (csA k).1)
theorem cos_sin_half (k : ℕ) :
   Real.cos (Real.pi * ((k:ℝ) / 2)) = ((csA k).1 : ℝ) ∧
     Real.sin (Real.pi * ((k:ℝ) / 2)) = ((csA k).2 : ℝ) := by
 induction k with
 | zero => simp [csA]
 | succ k ih =>
   have e : Real.pi * (((k + 1 : ℕ) : ℝ) / 2) = Real.pi * ((k:ℝ) / 2) + Real.pi / 2 := by
     push_cast; ring
   rw [e, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, ih.1, ih.2]
   simp [csA]
def kOf (t : ℚ) : ℕ := (⌊2 * t + 1 / 2⌋).toNat
def rOf (t : ℚ) : ℚ := t - (kOf t : ℚ) / 2
def sinPiI (t : ℚ) : ℚ × ℚ :=
 if 0 ≤ rOf t then iadd (imulZ (csA (kOf t)).2 (cosI (rOf t))) (imulZ (csA (kOf t)).1 (sinI (rOf t)))
 else isub (imulZ (csA (kOf t)).2 (cosI (-rOf t))) (imulZ (csA (kOf t)).1 (sinI (-rOf t)))
def sinPiOk (t : ℚ) : Bool := decide (0 ≤ TLo |rOf t|) && decide (THi |rOf t| ≤ 1)
theorem sinPiI_sound (t : ℚ) (h : sinPiOk t = true) : InI (sinPiI t) (Real.sin (Real.pi * t)) := by
 simp only [sinPiOk, Bool.and_eq_true, decide_eq_true_eq] at h
 obtain ⟨h0, h1⟩ := h
 have hcs := cos_sin_half (kOf t)
 have ht : (t : ℝ) = (kOf t : ℝ) / 2 + (rOf t : ℚ) := by
   simp only [rOf]; push_cast; ring
 unfold sinPiI
 split_ifs with hr
 · rw [abs_of_nonneg hr] at h0 h1
   have e : Real.sin (Real.pi * t) = ((csA (kOf t)).2 : ℝ) * Real.cos (Real.pi * (rOf t : ℚ))
       + ((csA (kOf t)).1 : ℝ) * Real.sin (Real.pi * (rOf t : ℚ)) := by
     rw [ht, mul_add, Real.sin_add, hcs.1, hcs.2]
   rw [e]
   exact iadd_sound (imulZ_sound _ (cosI_sound hr h0 h1)) (imulZ_sound _ (sinI_sound hr h0 h1))
 · push_neg at hr
   rw [abs_of_neg hr] at h0 h1
   have hr' : 0 ≤ -rOf t := by linarith
   have e : Real.sin (Real.pi * t) = ((csA (kOf t)).2 : ℝ) * Real.cos (Real.pi * ((-rOf t : ℚ) : ℝ))
       - ((csA (kOf t)).1 : ℝ) * Real.sin (Real.pi * ((-rOf t : ℚ) : ℝ)) := by
     have e2 : Real.pi * ((-rOf t : ℚ) : ℝ) = -(Real.pi * (rOf t : ℚ)) := by push_cast; ring
     rw [e2, Real.cos_neg, Real.sin_neg, ht, mul_add, Real.sin_add, hcs.1, hcs.2]; ring
   rw [e]
   exact isub_sound (imulZ_sound _ (cosI_sound hr' h0 h1)) (imulZ_sound _ (sinI_sound hr' h0 h1))
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace AMW
open Zeta23
structure PVFactor (f : ℝ → ℝ) (L A B ρ : ℝ) : Prop where
 A_nonneg : 0 ≤ A
 B_nonneg : 0 ≤ B
 even : ∀ u, f (-u) = f u
 nonneg : ∀ u, 0 ≤ f u
 le_one : ∀ u, |u| ≤ L / 2 → f u ≤ 1
 smooth : ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ 2 f (Ioo (-(L / 2 + δ)) (L / 2 + δ))
 deriv_le : ∀ u, |u| ≤ L / 2 → |deriv f u| ≤ A / L
 deriv2_le : ∀ u, |u| ≤ L / 2 → |deriv (deriv f) u| ≤ B / L ^ 2
 posVar : ∫ u in (0:ℝ)..(L / 2), max (deriv f u) 0 ≤ ρ
 budget : f 0 + 2 * ρ ≤ 1
 budget_sq : f 0 ^ 2 + 4 * ρ ≤ 1
def phiM (f : ℝ → ℝ) (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := f u * Taper.phi ϱ L w u
def cMod (ϱ : ℝ → ℝ) (A B : ℝ) : ℝ := Taper.cRho ϱ + A + A ^ 2 + B
variable {f : ℝ → ℝ} {ϱ : ℝ → ℝ} {L w A B ρ : ℝ}
theorem phiM_even (hf : PVFactor f L A B ρ) (u : ℝ) : phiM f ϱ L w (-u) = phiM f ϱ L w u := by
 simp only [phiM, hf.even, Taper.phi_even]
theorem phiM_nonneg (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phiM f ϱ L w u :=
 mul_nonneg (hf.nonneg u) (Taper.phi_nonneg hϱ u)
theorem phiM_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
   phiM f ϱ L w u = 0 := by
 simp only [phiM, Taper.phi_eq_zero hϱ hw hu, mul_zero]
theorem phiM_le_one (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) :
   phiM f ϱ L w u ≤ 1 := by
 rcases le_or_gt (L / 2) |u| with hu | hu
 · rw [phiM_eq_zero hϱ hw hu]; exact zero_le_one
 · calc phiM f ϱ L w u ≤ 1 * 1 :=
         mul_le_mul (hf.le_one u hu.le) (Taper.phi_le_one hϱ u) (Taper.phi_nonneg hϱ u) zero_le_one
     _ = 1 := mul_one 1
theorem phiM_zero_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) : phiM f ϱ L w 0 ≤ f 0 :=
 mul_le_of_le_one_right (hf.nonneg 0) (Taper.phi_le_one hϱ 0)
theorem phiM_contDiff (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ContDiff ℝ 2 (phiM f ϱ L w) := by
 obtain ⟨δ, hδ, hsm⟩ := hf.smooth
 rw [contDiff_iff_contDiffAt]
 intro u
 rcases lt_or_ge |u| (L / 2 + δ) with hu | hu
 · have hmem : u ∈ Ioo (-(L / 2 + δ)) (L / 2 + δ) := by
     constructor <;> linarith [neg_abs_le u, le_abs_self u]
   have hfu : ContDiffAt ℝ 2 f u := hsm.contDiffAt (isOpen_Ioo.mem_nhds hmem)
   exact hfu.mul ((Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)).contDiffAt
 · have hopen : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
   have hmem : u ∈ {v : ℝ | L / 2 < |v|} := by
     simp only [mem_setOf_eq]; linarith
   refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := 0)) ?_
   filter_upwards [hopen.mem_nhds hmem] with v hv
   exact phiM_eq_zero hϱ hw hv.le
theorem phi_antitoneOn (hϱ : TaperProfile ϱ) (hw : 0 < w) :
   AntitoneOn (Taper.phi ϱ L w) (Ici 0) := by
 intro x hx y hy hxy
 simp only [mem_Ici] at hx hy
 unfold Taper.phi
 apply hϱ.monotone
 rw [abs_of_nonneg hx, abs_of_nonneg hy]
 gcongr
theorem deriv_phi_nonpos (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : 0 < u) :
   deriv (Taper.phi ϱ L w) u ≤ 0 := by
 rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hu)]
 exact (phi_antitoneOn hϱ hw).derivWithin_nonpos
theorem integral_abs_deriv_le_two_of_posVar {g : ℝ → ℝ} {M ρ : ℝ} (hM : 0 < M)
   (hg : ContDiff ℝ 1 g) (heven : ∀ x, g (-x) = g x)
   (hsupp : ∀ x, M ≤ |x| → g x = 0)
   (hpos : ∫ u in (0:ℝ)..M, max (deriv g u) 0 ≤ ρ) (hbud : g 0 + 2 * ρ ≤ 1) :
   ∫ u, |deriv g u| ≤ 2 := by
 have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
 have hd' : Continuous (deriv g) := hg.continuous_deriv le_rfl
 have hderiv0 : ∀ x : ℝ, M < |x| → deriv g x = 0 := by
   intro x hx
   have hopen : IsOpen {v : ℝ | M < |v|} := (continuous_abs).isOpen_preimage _ isOpen_Ioi
   have hEq : g =ᶠ[nhds x] (fun _ => (0:ℝ)) := by
     filter_upwards [hopen.mem_nhds hx] with v hv
     exact hsupp v (le_of_lt hv)
   rw [hEq.deriv_eq, deriv_const]
 have hodd : ∀ x : ℝ, |deriv g (-x)| = |deriv g x| := by
   intro x
   have hfe : (fun y : ℝ => g (-y)) = g := funext heven
   have h := deriv_comp_neg (f := g) (x := x)
   rw [hfe] at h
   have h' : deriv g (-x) = -deriv g x := by linarith
   rw [h', abs_neg]
 have habs : (fun u : ℝ => |deriv g u|) = fun u => (fun t => |deriv g t|) |u| := by
   funext u
   show |deriv g u| = |deriv g (|u|)|
   rcases le_or_gt 0 u with h | h
   · rw [abs_of_nonneg h]
   · rw [abs_of_neg h, hodd]
 have hhalf : ∫ u, |deriv g u| = 2 * ∫ u in Set.Ioi 0, |deriv g u| := by
   conv_lhs => rw [habs]
   exact integral_comp_abs (f := fun t => |deriv g t|)
 have hcs : HasCompactSupport (deriv g) := by
   apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M))
   intro x hx
   rw [Function.mem_support] at hx
   by_contra hmem
   apply hx
   apply hderiv0
   rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
   rcases hmem with h | h
   · rw [abs_of_neg (by linarith)]; linarith
   · rw [abs_of_pos (by linarith)]; linarith
 have hint : Integrable (fun u => |deriv g u|) := (hd'.integrable_of_hasCompactSupport hcs).abs
 have hsplit : ∫ u in Set.Ioi 0, |deriv g u|
     = (∫ u in Set.Ioc 0 M, |deriv g u|) + ∫ u in Set.Ioi M, |deriv g u| := by
   rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
     hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hM.le]
 have hfar : ∫ u in Set.Ioi M, |deriv g u| = 0 := by
   apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
   intro x hx
   rw [hderiv0 x (by rw [abs_of_pos (lt_trans hM hx)]; exact hx), abs_zero]
 have hpt : ∀ x : ℝ, |deriv g x| = 2 * max (deriv g x) 0 - deriv g x := by
   intro x
   rcases le_or_gt 0 (deriv g x) with h | h
   · rw [abs_of_nonneg h, max_eq_left h]; ring
   · rw [abs_of_neg h, max_eq_right h.le]; ring
 have hmaxc : Continuous fun x => max (deriv g x) 0 := hd'.max continuous_const
 have hFTC : ∫ u in (0:ℝ)..M, deriv g u = g M - g 0 :=
   intervalIntegral.integral_deriv_eq_sub (fun x _ => hd x) ((hd'.intervalIntegrable) 0 M)
 have hnear : ∫ u in Set.Ioc 0 M, |deriv g u|
     = 2 * (∫ u in (0:ℝ)..M, max (deriv g u) 0) - (g M - g 0) := by
   rw [← intervalIntegral.integral_of_le hM.le]
   simp_rw [hpt]
   rw [intervalIntegral.integral_sub ((hmaxc.intervalIntegrable 0 M).const_mul 2)
       (hd'.intervalIntegrable 0 M), intervalIntegral.integral_const_mul, hFTC]
 have hgM : g M = 0 := hsupp M (by rw [abs_of_pos hM])
 rw [hhalf, hsplit, hfar, hnear, hgM]
 linarith
theorem max_deriv_mul_le {f τ : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
   (hτ : DifferentiableAt ℝ τ x) (hf0 : 0 ≤ f x) (hτ0 : 0 ≤ τ x) (hτ1 : τ x ≤ 1)
   (hτ' : deriv τ x ≤ 0) :
   max (deriv (fun u => f u * τ u) x) 0 ≤ max (deriv f x) 0 := by
 rw [deriv_fun_mul hf hτ]
 refine max_le ?_ (le_max_right _ _)
 have h1 : f x * deriv τ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0 hτ'
 have h2 : deriv f x * τ x ≤ max (deriv f x) 0 := by
   rcases le_or_gt 0 (deriv f x) with h | h
   · rw [max_eq_left h]; nlinarith
   · rw [max_eq_right h.le]; nlinarith
 linarith
theorem posVar_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ∫ u in (0:ℝ)..(L / 2), max (deriv (phiM f ϱ L w) u) 0 ≤ ρ := by
 have hL : 0 < L := by linarith
 obtain ⟨δ, hδ, hsm⟩ := hf.smooth
 have hU : IsOpen (Ioo (-(L / 2 + δ)) (L / 2 + δ)) := isOpen_Ioo
 have hφ := phiM_contDiff hf hϱ hw hwL
 have hτ : ContDiff ℝ 2 (Taper.phi ϱ L w) := (Taper.phi_contDiff hϱ hw hwL).of_le (by norm_num)
 have hcore : Icc (0:ℝ) (L / 2) ⊆ Ioo (-(L / 2 + δ)) (L / 2 + δ) := fun u hu => by
   constructor <;> linarith [hu.1, hu.2]
 have hf'c : ContinuousOn (deriv f) (Icc (0:ℝ) (L / 2)) :=
   ((hsm.continuousOn_deriv_of_isOpen hU (by norm_num))).mono hcore
 refine le_trans ?_ hf.posVar
 refine intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) ?_ ?_ ?_
 · exact ((hφ.continuous_deriv (by norm_num)).max continuous_const).intervalIntegrable _ _
 · exact (ContinuousOn.sup hf'c continuousOn_const).intervalIntegrable_of_Icc (by linarith)
 · intro u hu
   have huU : u ∈ Ioo (-(L / 2 + δ)) (L / 2 + δ) := hcore (Ioo_subset_Icc_self hu)
   have hfd : DifferentiableAt ℝ f u :=
     (hsm.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds huU)
   exact max_deriv_mul_le hfd (hτ.differentiable (by norm_num) u) (hf.nonneg u)
     (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) (deriv_phi_nonpos hϱ hw hu.1)
theorem integral_abs_deriv_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w)
   (hwL : 2 * w ≤ L) : ∫ u, |deriv (phiM f ϱ L w) u| ≤ 2 := by
 have hL : 0 < L := by linarith
 refine integral_abs_deriv_le_two_of_posVar (by positivity : (0:ℝ) < L / 2)
   ((phiM_contDiff hf hϱ hw hwL).of_le (by norm_num)) (phiM_even hf)
   (fun x hx => phiM_eq_zero hϱ hw hx) (posVar_phiM_le hf hϱ hw hwL) ?_
 linarith [phiM_zero_le (w := w) hf hϱ, hf.budget]
theorem integral_abs_deriv_phiM_sq_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 0 < w)
   (hwL : 2 * w ≤ L) : ∫ u, |deriv (fun u => phiM f ϱ L w u ^ 2) u| ≤ 2 := by
 have hL : 0 < L := by linarith
 have hφ := phiM_contDiff hf hϱ hw hwL
 have hφd : Differentiable ℝ (phiM f ϱ L w) := hφ.differentiable (by norm_num)
 have hφ'c : Continuous (deriv (phiM f ϱ L w)) := hφ.continuous_deriv (by norm_num)
 have hdsq : ∀ u, deriv (fun u => phiM f ϱ L w u ^ 2) u = 2 * phiM f ϱ L w u * deriv (phiM f ϱ L w) u :=
   fun u => by
     rw [((hφd u).hasDerivAt.fun_pow 2).deriv]; push_cast; ring
 have hpos : ∫ u in (0:ℝ)..(L / 2), max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0 ≤ 2 * ρ := by
   have hpt : ∀ u, max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0
       ≤ 2 * max (deriv (phiM f ϱ L w) u) 0 := fun u => by
     rw [hdsq]
     have h0 := phiM_nonneg (w := w) hf hϱ u
     have h1 := phiM_le_one hf hϱ hw u
     refine max_le ?_ (by positivity)
     rcases le_or_gt 0 (deriv (phiM f ϱ L w) u) with h | h
     · rw [max_eq_left h]; nlinarith
     · rw [max_eq_right h.le]; nlinarith
   have hc1 : Continuous fun u => max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0 := by
     simp_rw [hdsq]
     exact ((continuous_const.mul hφ.continuous).mul hφ'c).max continuous_const
   have hc2 : Continuous fun u => 2 * max (deriv (phiM f ϱ L w) u) 0 :=
     continuous_const.mul (hφ'c.max continuous_const)
   calc ∫ u in (0:ℝ)..(L / 2), max (deriv (fun u => phiM f ϱ L w u ^ 2) u) 0
       ≤ ∫ u in (0:ℝ)..(L / 2), 2 * max (deriv (phiM f ϱ L w) u) 0 :=
         intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
           (hc2.intervalIntegrable _ _) fun u _ => hpt u
     _ = 2 * ∫ u in (0:ℝ)..(L / 2), max (deriv (phiM f ϱ L w) u) 0 :=
         intervalIntegral.integral_const_mul _ _
     _ ≤ 2 * ρ := by linarith [posVar_phiM_le hf hϱ hw hwL]
 refine integral_abs_deriv_le_two_of_posVar (by positivity : (0:ℝ) < L / 2)
   ((hφ.pow 2).of_le (by norm_num)) (fun x => by rw [phiM_even hf])
   (fun x hx => by rw [phiM_eq_zero hϱ hw hx, zero_pow two_ne_zero]) hpos ?_
 have h0 := phiM_zero_le (w := w) hf hϱ
 have h00 := phiM_nonneg (w := w) hf hϱ 0
 have : phiM f ϱ L w 0 ^ 2 ≤ f 0 ^ 2 := pow_le_pow_left₀ h00 h0 2
 linarith [hf.budget_sq]
theorem deriv2_mul_eq {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
   (hG : ContDiffOn ℝ 2 G U) {u : ℝ} (hu : u ∈ U) :
   deriv (deriv (fun v => F v * G v)) u
     = deriv (deriv F) u * G u + 2 * (deriv F u * deriv G u) + F u * deriv (deriv G) u := by
 have hFd : ∀ v ∈ U, DifferentiableAt ℝ F v := fun v hv =>
   (hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hv)
 have hGd : ∀ v ∈ U, DifferentiableAt ℝ G v := fun v hv =>
   (hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hv)
 have hF' : ContDiffOn ℝ 1 (deriv F) U := hF.deriv_of_isOpen hU (by norm_num)
 have hG' : ContDiffOn ℝ 1 (deriv G) U := hG.deriv_of_isOpen hU (by norm_num)
 have hF'd : DifferentiableAt ℝ (deriv F) u :=
   (hF'.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
 have hG'd : DifferentiableAt ℝ (deriv G) u :=
   (hG'.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu)
 have h1 : deriv (fun v => F v * G v) =ᶠ[nhds u] fun v => deriv F v * G v + F v * deriv G v := by
   filter_upwards [hU.mem_nhds hu] with v hv
   exact deriv_mul (hFd v hv) (hGd v hv)
 rw [h1.deriv_eq]
 have hA : HasDerivAt (fun v => deriv F v * G v) (deriv (deriv F) u * G u + deriv F u * deriv G u) u :=
   hF'd.hasDerivAt.mul (hGd u hu).hasDerivAt
 have hB : HasDerivAt (fun v => F v * deriv G v) (deriv F u * deriv G u + F u * deriv (deriv G) u) u :=
   (hFd u hu).hasDerivAt.mul hG'd.hasDerivAt
 have hAB : HasDerivAt (fun v => deriv F v * G v + F v * deriv G v)
     ((deriv (deriv F) u * G u + deriv F u * deriv G u)
       + (deriv F u * deriv G u + F u * deriv (deriv G) u)) u := hA.add hB
 rw [hAB.deriv]; ring
theorem deriv_mul_eq {F G : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U)
   (hG : ContDiffOn ℝ 2 G U) {u : ℝ} (hu : u ∈ U) :
   deriv (fun v => F v * G v) u = deriv F u * G u + F u * deriv G u :=
 deriv_mul ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))
   ((hG.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hu))
theorem deriv2_eq_zero_of_eqOn {H : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) (hz : ∀ v ∈ V, H v = 0)
   {u : ℝ} (hu : u ∈ V) : deriv H u = 0 ∧ deriv (deriv H) u = 0 := by
 have hd : ∀ v ∈ V, deriv H v = 0 := by
   intro v hv
   have : H =ᶠ[nhds v] fun _ => (0:ℝ) := by
     filter_upwards [hV.mem_nhds hv] with x hx using hz x hx
   rw [this.deriv_eq, deriv_const]
 refine ⟨hd u hu, ?_⟩
 have : deriv H =ᶠ[nhds u] fun _ => (0:ℝ) := by
   filter_upwards [hV.mem_nhds hu] with x hx using hd x hx
 rw [this.deriv_eq, deriv_const]
theorem integrable_abs_of_cs {h : ℝ → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) :
   Integrable (fun u => |h u|) :=
 (hc.abs).integrable_of_hasCompactSupport (hcs.comp_left (g := fun t => |t|) abs_zero)
theorem integral_abs_deriv2_mul_le {F G : ℝ → ℝ} {L δ A' B' : ℝ} (hδ : 0 < δ)
   (hA' : 0 ≤ A') (hB' : 0 ≤ B')
   (hF : ContDiffOn ℝ 2 F (Ioo (-(L / 2 + δ)) (L / 2 + δ)))
   (hF0 : ∀ u, |u| ≤ L / 2 → |F u| ≤ 1) (hF1 : ∀ u, |u| ≤ L / 2 → |deriv F u| ≤ A')
   (hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv F) u| ≤ B')
   (hG : ContDiff ℝ 2 G) (hGcs : HasCompactSupport G) (hGzero : ∀ u, L / 2 < |u| → G u = 0)
   (hH : ContDiff ℝ 2 (fun u => F u * G u)) (hHcs : HasCompactSupport (fun u => F u * G u)) :
   ∫ u, |deriv (deriv (fun u => F u * G u)) u|
     ≤ B' * (∫ u, |G u|) + 2 * A' * (∫ u, |deriv G u|) + ∫ u, |deriv (deriv G) u| := by
 set U : Set ℝ := Ioo (-(L / 2 + δ)) (L / 2 + δ) with hUdef
 have hU : IsOpen U := isOpen_Ioo
 set H : ℝ → ℝ := fun u => F u * G u with hHdef
 have hpt : ∀ u, |deriv (deriv H) u| ≤ B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u| := by
   intro u
   rcases le_or_gt |u| (L / 2) with hu | hu
   · have huU : u ∈ U := by
       simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
     rw [deriv2_mul_eq hU hF hG.contDiffOn huU]
     have h0 := hF0 u hu; have h1 := hF1 u hu; have h2 := hF2 u hu
     calc |deriv (deriv F) u * G u + 2 * (deriv F u * deriv G u) + F u * deriv (deriv G) u|
         ≤ |deriv (deriv F) u * G u| + |2 * (deriv F u * deriv G u)| + |F u * deriv (deriv G) u| :=
           abs_add_three _ _ _
       _ ≤ B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u| := by
           rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]
           have hg0 := abs_nonneg (G u); have hg1 := abs_nonneg (deriv G u)
           have hg2 := abs_nonneg (deriv (deriv G) u)
           have e1 : |deriv (deriv F) u| * |G u| ≤ B' * |G u| := mul_le_mul_of_nonneg_right h2 hg0
           have e2 : 2 * (|deriv F u| * |deriv G u|) ≤ 2 * A' * |deriv G u| := by
             nlinarith [mul_le_mul_of_nonneg_right h1 hg1]
           have e3 : |F u| * |deriv (deriv G) u| ≤ |deriv (deriv G) u| := by
             nlinarith [mul_le_mul_of_nonneg_right h0 hg2]
           linarith
   · have hV : IsOpen {v : ℝ | L / 2 < |v|} := continuous_abs.isOpen_preimage _ isOpen_Ioi
     have hz : ∀ v ∈ {v : ℝ | L / 2 < |v|}, H v = 0 := fun v hv => by
       simp only [hHdef, hGzero v hv, mul_zero]
     rw [(deriv2_eq_zero_of_eqOn hV hz hu).2, abs_zero]
     positivity
 have hH2c : Continuous (deriv (deriv H)) := (hH.deriv' (n := 1)).continuous_deriv le_rfl
 have hG1c : Continuous (deriv G) := (hG.deriv' (n := 1)).continuous
 have hG2c : Continuous (deriv (deriv G)) := (hG.deriv' (n := 1)).continuous_deriv le_rfl
 have iH : Integrable (fun u => |deriv (deriv H) u|) := integrable_abs_of_cs hH2c hHcs.deriv.deriv
 have iG : Integrable (fun u => |G u|) := integrable_abs_of_cs hG.continuous hGcs
 have iG1 : Integrable (fun u => |deriv G u|) := integrable_abs_of_cs hG1c hGcs.deriv
 have iG2 : Integrable (fun u => |deriv (deriv G) u|) := integrable_abs_of_cs hG2c hGcs.deriv.deriv
 have iR : Integrable (fun u => B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|) :=
   ((iG.const_mul B').add (iG1.const_mul (2 * A'))).add iG2
 calc ∫ u, |deriv (deriv H) u|
     ≤ ∫ u, (B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|) := integral_mono iH iR hpt
   _ = B' * (∫ u, |G u|) + 2 * A' * (∫ u, |deriv G u|) + ∫ u, |deriv (deriv G) u| := by
       have s1 : ∫ u, (B' * |G u| + 2 * A' * |deriv G u| + |deriv (deriv G) u|)
           = (∫ u, (B' * |G u| + 2 * A' * |deriv G u|)) + ∫ u, |deriv (deriv G) u| :=
         integral_add ((iG.const_mul B').add (iG1.const_mul (2 * A'))) iG2
       have s2 : ∫ u, (B' * |G u| + 2 * A' * |deriv G u|)
           = (∫ u, B' * |G u|) + ∫ u, 2 * A' * |deriv G u| :=
         integral_add (iG.const_mul B') (iG1.const_mul (2 * A'))
       rw [s1, s2, integral_const_mul, integral_const_mul]
theorem integral_abs_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ∫ u, |Taper.phi ϱ L w u| ≤ L := by
 have hL : 0 < L := by linarith
 have heq : ∫ u, |Taper.phi ϱ L w u| = ∫ u in Icc (-(L / 2)) (L / 2), |Taper.phi ϱ L w u| := by
   refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
   rw [mem_Icc, not_and_or, not_le, not_le] at hu
   have habs : L / 2 ≤ |u| := by
     rcases hu with h | h
     · linarith [neg_le_abs u]
     · linarith [le_abs_self u]
   rw [Taper.phi_eq_zero hϱ hw habs, abs_zero]
 rw [heq]
 calc ∫ u in Icc (-(L / 2)) (L / 2), |Taper.phi ϱ L w u|
     ≤ ∫ u in Icc (-(L / 2)) (L / 2), (1:ℝ) := by
       refine setIntegral_mono_on ?_ (by simp) measurableSet_Icc fun u _ => ?_
       · exact ((Taper.phi_continuous hϱ hw hwL).abs.integrableOn_Icc)
       · rw [abs_of_nonneg (Taper.phi_nonneg hϱ u)]; exact Taper.phi_le_one hϱ u
   _ = L := by
       rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
         ENNReal.toReal_ofReal (by linarith)]
       ring
theorem integral_abs_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ L := by
 have hL : 0 < L := by linarith
 have ha := Taper.aConst_le_one hϱ hw hwL
 unfold Taper.aConst at ha
 have habs : (fun u => |Taper.phi ϱ L w u ^ 2|) = fun u => Taper.phi ϱ L w u ^ 2 :=
   funext fun u => abs_of_nonneg (sq_nonneg _)
 rw [habs]
 rwa [inv_mul_le_iff₀ hL, mul_one] at ha
theorem l1Deriv2_nonneg' (ϱ : ℝ → ℝ) : 0 ≤ Taper.l1Deriv2 ϱ := integral_nonneg fun _ => abs_nonneg _
theorem phiM_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) : HasCompactSupport (phiM f ϱ L w) :=
 (Taper.phi_hasCompactSupport hϱ (L := L) hw).mul_left
theorem PVFactor.abs_le_one (hf : PVFactor f L A B ρ) (u : ℝ) (hu : |u| ≤ L / 2) : |f u| ≤ 1 := by
 rw [abs_of_nonneg (hf.nonneg u)]; exact hf.le_one u hu
theorem integral_abs_deriv2_phiM_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
   (hwL : 8 * w ≤ L) : ∫ u, |deriv (deriv (phiM f ϱ L w)) u| ≤ cMod ϱ A B / w := by
 have hw0 : 0 < w := by linarith
 have h2wL : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 obtain ⟨δ, hδ, hsm⟩ := hf.smooth
 have hmain := integral_abs_deriv2_mul_le (F := f) (G := Taper.phi ϱ L w) (L := L) hδ
   (div_nonneg hf.A_nonneg hL.le) (div_nonneg hf.B_nonneg (sq_nonneg L)) hsm hf.abs_le_one hf.deriv_le
   hf.deriv2_le ((Taper.phi_contDiff hϱ hw0 h2wL).of_le (by norm_num)) (Taper.phi_hasCompactSupport hϱ hw0)
   (fun u hu => Taper.phi_eq_zero hϱ hw0 hu.le) (phiM_contDiff hf hϱ hw0 h2wL)
   (phiM_hasCompactSupport hϱ hw0)
 have hI0 := integral_abs_phi_le hϱ hw0 h2wL
 have hI1 : ∫ u, |deriv (Taper.phi ϱ L w) u| = 2 := Taper.integral_abs_deriv_phi hϱ hw0 h2wL
 have hI2 : ∫ u, |deriv (deriv (Taper.phi ϱ L w)) u| = 2 * Taper.l1Deriv2 ϱ / w :=
   Taper.integral_abs_deriv2_phi hϱ hw0 h2wL
 rw [hI1, hI2] at hmain
 have hc := Taper.two_mul_l1Deriv2_le_cRho hϱ
 have hl1 := l1Deriv2_nonneg' ϱ
 have hA := hf.A_nonneg; have hB := hf.B_nonneg
 refine hmain.trans ?_
 have e1 : B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / w := by
   calc B / L ^ 2 * ∫ u, |Taper.phi ϱ L w u| ≤ B / L ^ 2 * L := by gcongr
     _ = B / L := by field_simp
     _ ≤ B / w := div_le_div_of_nonneg_left hB hw0 (by linarith)
 have e2 : 2 * (A / L) * 2 ≤ A / w := by
   rw [show 2 * (A / L) * 2 = 4 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
 have e3 : 2 * Taper.l1Deriv2 ϱ / w ≤ Taper.cRho ϱ / w := div_le_div_of_nonneg_right hc hw0.le
 have e4 : 0 ≤ A ^ 2 / w := by positivity
 calc B / L ^ 2 * (∫ u, |Taper.phi ϱ L w u|) + 2 * (A / L) * 2 + 2 * Taper.l1Deriv2 ϱ / w
     ≤ B / w + A / w + Taper.cRho ϱ / w + A ^ 2 / w := by linarith
   _ = cMod ϱ A B / w := by simp only [cMod]; ring
theorem phiM_sq_eq : (fun u => phiM f ϱ L w u ^ 2) = fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2) := by
 funext u; simp only [phiM]; ring
theorem integral_abs_deriv2_phiM_sq_le (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
   (hwL : 8 * w ≤ L) : ∫ u, |deriv (deriv (fun u => phiM f ϱ L w u ^ 2)) u| ≤ cMod ϱ A B / w := by
 have hw0 : 0 < w := by linarith
 have h2wL : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 obtain ⟨δ, hδ, hsm⟩ := hf.smooth
 set U : Set ℝ := Ioo (-(L / 2 + δ)) (L / 2 + δ) with hUdef
 have hU : IsOpen U := isOpen_Ioo
 have hcore : ∀ u, |u| ≤ L / 2 → u ∈ U := fun u hu => by
   simp only [hUdef, mem_Ioo]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
 have hsm2 : ContDiffOn ℝ 2 (fun u => f u * f u) U := hsm.mul hsm
 have hA := hf.A_nonneg; have hB := hf.B_nonneg
 have hF0 : ∀ u, |u| ≤ L / 2 → |f u * f u| ≤ 1 := fun u hu => by
   rw [abs_mul]; have := hf.abs_le_one u hu; nlinarith [abs_nonneg (f u)]
 have hF1 : ∀ u, |u| ≤ L / 2 → |deriv (fun u => f u * f u) u| ≤ 2 * A / L := fun u hu => by
   rw [deriv_mul_eq hU hsm hsm (hcore u hu)]
   have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu
   calc |deriv f u * f u + f u * deriv f u| = 2 * (|f u| * |deriv f u|) := by
         rw [show deriv f u * f u + f u * deriv f u = 2 * (f u * deriv f u) by ring, abs_mul, abs_mul,
           abs_two]
     _ ≤ 2 * (1 * (A / L)) := by gcongr
     _ = 2 * A / L := by ring
 have hF2 : ∀ u, |u| ≤ L / 2 → |deriv (deriv (fun u => f u * f u)) u| ≤ (2 * B + 2 * A ^ 2) / L ^ 2 :=
   fun u hu => by
   rw [deriv2_mul_eq hU hsm hsm (hcore u hu)]
   have h0 := hf.abs_le_one u hu; have h1 := hf.deriv_le u hu; have h2 := hf.deriv2_le u hu
   have hd0 := abs_nonneg (deriv f u)
   calc |deriv (deriv f) u * f u + 2 * (deriv f u * deriv f u) + f u * deriv (deriv f) u|
       ≤ |deriv (deriv f) u * f u| + |2 * (deriv f u * deriv f u)| + |f u * deriv (deriv f) u| :=
         abs_add_three _ _ _
     _ = 2 * (|deriv (deriv f) u| * |f u|) + 2 * (|deriv f u| * |deriv f u|) := by
         rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
     _ ≤ 2 * (B / L ^ 2 * 1) + 2 * (A / L * (A / L)) := by gcongr
     _ = (2 * B + 2 * A ^ 2) / L ^ 2 := by field_simp
 have hφ := Taper.phi_contDiff hϱ hw0 h2wL
 have hG : ContDiff ℝ 2 (fun u => Taper.phi ϱ L w u ^ 2) := (hφ.pow 2).of_le (by norm_num)
 have hGcs : HasCompactSupport (fun u => Taper.phi ϱ L w u ^ 2) :=
   (Taper.phi_hasCompactSupport hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
 have hGzero : ∀ u, L / 2 < |u| → Taper.phi ϱ L w u ^ 2 = 0 := fun u hu => by
   rw [Taper.phi_eq_zero hϱ hw0 hu.le, zero_pow two_ne_zero]
 have hH : ContDiff ℝ 2 (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
   rw [← phiM_sq_eq]; exact (phiM_contDiff hf hϱ hw0 h2wL).pow 2
 have hHcs : HasCompactSupport (fun u => (f u * f u) * (Taper.phi ϱ L w u ^ 2)) := by
   rw [← phiM_sq_eq]; exact (phiM_hasCompactSupport hϱ hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
 have hmain := integral_abs_deriv2_mul_le (F := fun u => f u * f u) (G := fun u => Taper.phi ϱ L w u ^ 2)
   (L := L) hδ (by positivity : (0:ℝ) ≤ 2 * A / L) (by positivity : (0:ℝ) ≤ (2 * B + 2 * A ^ 2) / L ^ 2)
   hsm2 hF0 hF1 hF2 hG hGcs hGzero hH hHcs
 rw [phiM_sq_eq]
 have hI0 := integral_abs_phi_sq_le hϱ hw0 h2wL
 have hI1 : ∫ u, |deriv (fun u => Taper.phi ϱ L w u ^ 2) u| = 2 := Taper.integral_abs_deriv_phi_sq hϱ hw0 h2wL
 have hI2 : ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u| ≤ Taper.cRho ϱ / w :=
   Taper.integral_abs_deriv2_phi_sq_le hϱ hw h2wL
 rw [hI1] at hmain
 refine hmain.trans ?_
 have e1 : (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2| ≤ (B + A ^ 2) / w := by
   calc (2 * B + 2 * A ^ 2) / L ^ 2 * ∫ u, |Taper.phi ϱ L w u ^ 2|
       ≤ (2 * B + 2 * A ^ 2) / L ^ 2 * L := by gcongr
     _ = (2 * B + 2 * A ^ 2) / L := by field_simp
     _ ≤ (B + A ^ 2) / w := by rw [div_le_div_iff₀ hL hw0]; nlinarith
 have e2 : 2 * (2 * A / L) * 2 ≤ A / w := by
   rw [show 2 * (2 * A / L) * 2 = 8 * A / L by ring, div_le_div_iff₀ hL hw0]; nlinarith
 calc (2 * B + 2 * A ^ 2) / L ^ 2 * (∫ u, |Taper.phi ϱ L w u ^ 2|) + 2 * (2 * A / L) * 2
       + ∫ u, |deriv (deriv (fun u => Taper.phi ϱ L w u ^ 2)) u|
     ≤ (B + A ^ 2) / w + A / w + Taper.cRho ϱ / w := by linarith
   _ = cMod ϱ A B / w := by simp only [cMod]; ring
theorem four_le_cMod (hϱ : TaperProfile ϱ) (hA : 0 ≤ A) (hB : 0 ≤ B) : 4 ≤ cMod ϱ A B := by
 have := Taper.four_le_cRho hϱ
 simp only [cMod]; nlinarith [sq_nonneg A]
theorem admWindow_phiM (hf : PVFactor f L A B ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   AdmWindow (phiM f ϱ L w) L w (cMod ϱ A B) where
 one_le_w := hw
 w8 := hwL
 four_le_c := four_le_cMod hϱ hf.A_nonneg hf.B_nonneg
 even := phiM_even hf
 nonneg := phiM_nonneg hf hϱ
 le_one := phiM_le_one hf hϱ (by linarith)
 contDiff := phiM_contDiff hf hϱ (by linarith) (by linarith)
 support := fun _ hu => phiM_eq_zero hϱ (by linarith) hu
 l1_deriv := integral_abs_deriv_phiM_le hf hϱ (by linarith) (by linarith)
 l1_deriv_sq := integral_abs_deriv_phiM_sq_le hf hϱ (by linarith) (by linarith)
 l1_deriv2 := integral_abs_deriv2_phiM_le hf hϱ hw hwL
 l1_deriv2_sq := integral_abs_deriv2_phiM_sq_le hf hϱ hw hwL
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter Topology
namespace AMW
open Zeta23
structure Profile (p : ℝ → ℝ) (δ A₁ A₂ ρ : ℝ) : Prop where
 δ_pos : 0 < δ
 A₁_nonneg : 0 ≤ A₁
 A₂_nonneg : 0 ≤ A₂
 even : ∀ s, p (-s) = p s
 contDiff : ContDiff ℝ 2 p
 pos : ∀ s, |s| ≤ 1 / 2 + δ → 0 < p s
 ge_quarter : ∀ s, |s| ≤ 1 / 2 → 1 / 4 ≤ p s
 le_one : ∀ s, |s| ≤ 1 / 2 → p s ≤ 1
 deriv_le : ∀ s, |s| ≤ 1 / 2 → |deriv p s| ≤ A₁
 deriv2_le : ∀ s, |s| ≤ 1 / 2 → |deriv (deriv p) s| ≤ A₂
 posVar : ∫ s in (0:ℝ)..(1 / 2), max (deriv p s) 0 ≤ ρ
 budget : Real.sqrt (p 0) + 2 * ρ ≤ 1
 budget_sq : p 0 + 4 * ρ ≤ 1
def fP (p : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (p (u / L))
variable {p : ℝ → ℝ} {δ A₁ A₂ ρ L : ℝ}
section
variable (hp : Profile p δ A₁ A₂ ρ) (hL : 0 < L)
include hp hL
lemma pos_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) : 0 < p (u / L) := by
 apply hp.pos
 rw [abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
 constructor <;> nlinarith [hu.1, hu.2]
lemma fP_eq_sqrt_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
   fP p L u = Real.sqrt (p (u / L)) := by
 rfl
lemma hasDerivAt_comp_div (u : ℝ) : HasDerivAt (fun u => p (u / L)) (deriv p (u / L) / L) u := by
 have h1 : HasDerivAt (fun x : ℝ => x / L) (1 / L) u := by
   simpa using (hasDerivAt_id u).div_const L
 exact (((hp.contDiff.differentiable (by norm_num)) (u / L)).hasDerivAt.comp u h1).congr_deriv (by ring)
lemma deriv_comp_div : deriv (fun u => p (u / L)) = fun u => deriv p (u / L) / L :=
 funext fun u => (hasDerivAt_comp_div hp hL u).deriv
lemma deriv2_comp_div (u : ℝ) :
   deriv (deriv (fun u => p (u / L))) u = deriv (deriv p) (u / L) / L ^ 2 := by
 rw [deriv_comp_div hp hL]
 have hd : Differentiable ℝ (deriv p) := (hp.contDiff.deriv' (n := 1)).differentiable (by norm_num)
 have h1 : HasDerivAt (fun x : ℝ => x / L) (1 / L) u := by
   simpa using (hasDerivAt_id u).div_const L
 have h2 : HasDerivAt (fun u => deriv p (u / L) / L) (deriv (deriv p) (u / L) / L ^ 2) u := by
   exact (((hd (u / L)).hasDerivAt.comp u h1).div_const L).congr_deriv
     (show deriv (deriv p) (u / L) * (1 / L) / L = deriv (deriv p) (u / L) / L ^ 2 by ring)
 exact h2.deriv
lemma fP_contDiffOn : ContDiffOn ℝ 2 (fP p L) (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := by
 have hc : ContDiff ℝ 2 (fun u => p (u / L)) := hp.contDiff.comp (contDiff_id.div_const L)
 have h1 : ContDiffOn ℝ 2 (fun u => Real.sqrt (p (u / L))) (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :=
   hc.contDiffOn.sqrt fun u hu => (pos_of_mem hp hL hu).ne'
 exact h1.congr fun u hu => fP_eq_sqrt_of_mem hp hL hu
lemma fP_mul_self_of_mem {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
   fP p L u * fP p L u = p (u / L) := by
 rw [fP_eq_sqrt_of_mem hp hL hu, ← sq, Real.sq_sqrt (pos_of_mem hp hL hu).le]
lemma core_abs {u : ℝ} (hu : |u| ≤ L / 2) : |u / L| ≤ 1 / 2 := by
 rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]; linarith
lemma core_mem {u : ℝ} (hu : |u| ≤ L / 2) : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) := by
 have := hp.δ_pos
 have hδL : 0 < δ * L := mul_pos this hL
 constructor <;> linarith [neg_abs_le u, le_abs_self u]
lemma fP_core_ge {u : ℝ} (hu : |u| ≤ L / 2) : 1 / 2 ≤ fP p L u := by
 have h := hp.ge_quarter _ (core_abs hp hL hu)
 rw [fP]
 refine Real.le_sqrt_of_sq_le ?_
 linarith
lemma fP_le_one {u : ℝ} (hu : |u| ≤ L / 2) : fP p L u ≤ 1 := by
 rw [fP, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
 exact Real.sqrt_le_sqrt (hp.le_one _ (core_abs hp hL hu))
lemma deriv_fP_eq {u : ℝ} (hu : u ∈ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) :
   deriv (fP p L) u * (2 * fP p L u) = deriv p (u / L) / L := by
 have hU : IsOpen (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := isOpen_Ioo
 have hsm := fP_contDiffOn hp hL
 have hev : (fun v => fP p L v * fP p L v) =ᶠ[nhds u] fun v => p (v / L) := by
   filter_upwards [hU.mem_nhds hu] with v hv using fP_mul_self_of_mem hp hL hv
 have hd := deriv_mul_eq hU hsm hsm hu
 rw [hev.deriv_eq, (hasDerivAt_comp_div hp hL u).deriv] at hd
 rw [hd]; ring
lemma abs_deriv_fP_le {u : ℝ} (hu : |u| ≤ L / 2) : |deriv (fP p L) u| ≤ A₁ / L := by
 have hf := fP_core_ge hp hL hu
 have e := deriv_fP_eq hp hL (core_mem hp hL hu)
 have hd := hp.deriv_le _ (core_abs hp hL hu)
 have e' : deriv (fP p L) u = deriv p (u / L) / L / (2 * fP p L u) := by
   rw [← e]; field_simp
 rw [e', abs_div, abs_div, abs_of_pos hL, abs_of_pos (by linarith : 0 < 2 * fP p L u)]
 calc |deriv p (u / L)| / L / (2 * fP p L u) ≤ |deriv p (u / L)| / L / 1 := by
       gcongr; linarith
   _ ≤ A₁ / L := by rw [div_one]; gcongr
lemma abs_deriv2_fP_le {u : ℝ} (hu : |u| ≤ L / 2) :
   |deriv (deriv (fP p L)) u| ≤ (A₂ + 2 * A₁ ^ 2) / L ^ 2 := by
 set U : Set ℝ := Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) with hUdef
 have hU : IsOpen U := isOpen_Ioo
 have huU : u ∈ U := core_mem hp hL hu
 have hsm := fP_contDiffOn hp hL
 have hd1 : ∀ v ∈ U, deriv (fun x => fP p L x * fP p L x) v = deriv (fun x => p (x / L)) v := by
   intro v hv
   have hev : (fun x => fP p L x * fP p L x) =ᶠ[nhds v] fun x => p (x / L) := by
     filter_upwards [hU.mem_nhds hv] with x hx using fP_mul_self_of_mem hp hL hx
   exact hev.deriv_eq
 have hev2 : deriv (fun x => fP p L x * fP p L x) =ᶠ[nhds u] deriv (fun x => p (x / L)) := by
   filter_upwards [hU.mem_nhds huU] with v hv using hd1 v hv
 have hd2 : deriv (deriv (fun x => p (x / L))) u
     = deriv (deriv (fP p L)) u * fP p L u + 2 * (deriv (fP p L) u * deriv (fP p L) u)
       + fP p L u * deriv (deriv (fP p L)) u := by
   rw [← hev2.deriv_eq]; exact deriv2_mul_eq hU hsm hsm huU
 rw [deriv2_comp_div hp hL] at hd2
 have hf := fP_core_ge hp hL hu
 have h1 := abs_deriv_fP_le hp hL hu
 have h2 := hp.deriv2_le _ (core_abs hp hL hu)
 have e : deriv (deriv (fP p L)) u
     = (deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)) / (2 * fP p L u) := by
   rw [hd2]; field_simp; ring
 rw [e, abs_div, abs_of_pos (by linarith : 0 < 2 * fP p L u),
   div_le_div_iff₀ (by linarith) (by positivity)]
 have hsq : |deriv (fP p L) u| ^ 2 ≤ (A₁ / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
 have hL2 : 0 < L ^ 2 := by positivity
 have hA := hp.A₁_nonneg; have hB := hp.A₂_nonneg
 calc |deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)| * L ^ 2
     ≤ (|deriv (deriv p) (u / L)| / L ^ 2 + 2 * |deriv (fP p L) u| ^ 2) * L ^ 2 := by
       gcongr
       calc |deriv (deriv p) (u / L) / L ^ 2 - 2 * (deriv (fP p L) u * deriv (fP p L) u)|
           ≤ |deriv (deriv p) (u / L) / L ^ 2| + |2 * (deriv (fP p L) u * deriv (fP p L) u)| :=
             abs_sub _ _
         _ = |deriv (deriv p) (u / L)| / L ^ 2 + 2 * |deriv (fP p L) u| ^ 2 := by
             rw [abs_div, abs_of_pos hL2, abs_mul, abs_two, abs_mul]; ring
   _ ≤ (A₂ / L ^ 2 + 2 * (A₁ / L) ^ 2) * L ^ 2 := by gcongr
   _ = (A₂ + 2 * A₁ ^ 2) * 1 := by field_simp
   _ ≤ (A₂ + 2 * A₁ ^ 2) * (2 * fP p L u) := by
       gcongr; linarith
lemma posVar_fP_le : ∫ u in (0:ℝ)..(L / 2), max (deriv (fP p L) u) 0 ≤ ρ := by
 have hU : IsOpen (Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L)) := isOpen_Ioo
 have hsm := fP_contDiffOn hp hL
 have hcore : Icc (0:ℝ) (L / 2) ⊆ Ioo (-(L / 2 + δ * L)) (L / 2 + δ * L) := fun u hu =>
   core_mem hp hL (by rw [abs_of_nonneg hu.1]; exact hu.2)
 have hf'c : ContinuousOn (deriv (fP p L)) (Icc (0:ℝ) (L / 2)) :=
   (hsm.continuousOn_deriv_of_isOpen hU (by norm_num)).mono hcore
 have hp'c : Continuous (deriv p) := hp.contDiff.continuous_deriv (by norm_num)
 have hg : Continuous fun u => max (deriv p (u / L)) 0 / L :=
   ((hp'c.comp (continuous_id.div_const L)).max continuous_const).div_const L
 have hpt : ∀ u ∈ Icc (0:ℝ) (L / 2), max (deriv (fP p L) u) 0 ≤ max (deriv p (u / L)) 0 / L := by
   intro u hu
   have hu' : |u| ≤ L / 2 := by rw [abs_of_nonneg hu.1]; exact hu.2
   have hf := fP_core_ge hp hL hu'
   have e := deriv_fP_eq hp hL (hcore hu)
   refine max_le ?_ (by positivity)
   rcases le_or_gt (deriv (fP p L) u) 0 with h | h
   · exact h.trans (by positivity)
   · have : deriv (fP p L) u ≤ deriv p (u / L) / L := by nlinarith
     exact this.trans (div_le_div_of_nonneg_right (le_max_left _ _) hL.le)
 calc ∫ u in (0:ℝ)..(L / 2), max (deriv (fP p L) u) 0
     ≤ ∫ u in (0:ℝ)..(L / 2), max (deriv p (u / L)) 0 / L :=
       intervalIntegral.integral_mono_on (by linarith)
         ((ContinuousOn.sup hf'c continuousOn_const).intervalIntegrable_of_Icc (by linarith))
         (hg.intervalIntegrable _ _) hpt
   _ = ∫ s in (0:ℝ)..(1 / 2), max (deriv p s) 0 := by
       rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div (fun s => max (deriv p s) 0)
         hL.ne', smul_eq_mul, zero_div, show L / 2 / L = 1 / 2 by field_simp]
       field_simp
   _ ≤ ρ := hp.posVar
theorem pvFactor_fP : PVFactor (fP p L) L A₁ (A₂ + 2 * A₁ ^ 2) ρ where
 A_nonneg := hp.A₁_nonneg
 B_nonneg := by have := hp.A₂_nonneg; positivity
 even := fun u => by simp only [fP, neg_div, hp.even]
 nonneg := fun u => Real.sqrt_nonneg _
 le_one := fun u hu => fP_le_one hp hL hu
 smooth := ⟨δ * L, mul_pos hp.δ_pos hL, fP_contDiffOn hp hL⟩
 deriv_le := fun u hu => abs_deriv_fP_le hp hL hu
 deriv2_le := fun u hu => abs_deriv2_fP_le hp hL hu
 posVar := posVar_fP_le hp hL
 budget := by
   have h0 : 0 < p 0 := hp.pos 0 (by rw [abs_zero]; linarith [hp.δ_pos])
   rw [fP, zero_div]; exact hp.budget
 budget_sq := by
   have h0 : 0 < p 0 := hp.pos 0 (by rw [abs_zero]; linarith [hp.δ_pos])
   rw [fP, zero_div, Real.sq_sqrt h0.le]; exact hp.budget_sq
end
theorem admWindow_fP {ϱ : ℝ → ℝ} {w : ℝ} (hp : Profile p δ A₁ A₂ ρ) (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
   (hwL : 8 * w ≤ L) : AdmWindow (phiM (fP p L) ϱ L w) L w (cMod ϱ A₁ (A₂ + 2 * A₁ ^ 2)) :=
 admWindow_phiM (pvFactor_fP hp (by linarith)) hϱ hw hwL
end AMW
end
noncomputable section
open Real Set MeasureTheory
namespace AMW
open Zeta23
def sumQ (f : ℕ → ℚ) : ℕ → ℚ
 | 0 => 0
 | n + 1 => sumQ f n + f n
def allQ (f : ℕ → Bool) : ℕ → Bool
 | 0 => true
 | n + 1 => allQ f n && f n
theorem sumQ_eq (f : ℕ → ℚ) (n : ℕ) : sumQ f n = ∑ j ∈ Finset.range n, f j := by
 induction n with
 | zero => rfl
 | succ n ih => rw [sumQ, ih, Finset.sum_range_succ]
theorem allQ_iff (f : ℕ → Bool) (n : ℕ) : allQ f n = true ↔ ∀ j < n, f j = true := by
 induction n with
 | zero => simp [allQ]
 | succ n ih =>
   rw [allQ, Bool.and_eq_true, ih]
   constructor
   · rintro ⟨h1, h2⟩ j hj
     rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
     · exact h1 j h
     · exact h ▸ h2
   · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
def sinTabZ : List (ℤ × ℤ) := [(-23, 23), (122715334, 122715420), (245412211, 245412336), (368072129, 368072293), (490676618, 490676821), (613207212, 613207454), (735645460, 735645741), (857972922, 857973241), (980171177, 980171535), (1102221821, 1102222218), (1224106475, 1224106910), (1345806783, 1345807256), (1467304418, 1467304929), (1588581082, 1588581631), (1709618512, 1709619097), (1830398479, 1830399103), (1950902796, 1950903456), (2071113314, 2071114011), (2191011930, 2191012663), (2310580587, 2310581356), (2429801281, 2429802085), (2548656054, 2548656894), (2667127010, 2667127885), (2785196306, 2785197216), (2902846163, 2902847107), (3020058861, 3020059840), (3136816751, 3136817762), (3253102246, 3253103291), (3368897838, 3368898914), (3484186085, 3484187194), (3598949628, 3598950767), (3713171181, 3713172353), (3826833546, 3826834747), (3939919603, 3939920835), (4052412323, 4052413585), (4164294765, 4164296055), (4275550080, 4275551398), (4386161513, 4386162859), (4496112407, 4496113780), (4605386202, 4605387601), (4713966444, 4713967869), (4821836780, 4821838231), (4928980966, 4928982440), (5035382865, 5035384364), (5141026455, 5141027976), (5245895825, 5245897369), (5349975184, 5349976748), (5453248855, 5453250441), (5555701288, 5555702893), (5657317053, 5657318678), (5758080847, 5758082491), (5857977496, 5857979157), (5956991955, 5956993634), (6055109314, 6055111008), (6152314796, 6152316505), (6248593762, 6248595486), (6343931713, 6343933451), (6438314292, 6438316043), (6531727285, 6531729047), (6624156624, 6624158398), (6715588390, 6715590173), (6806008813, 6806010606), (6895404278, 6895406078), (6983761319, 6983763128), (7071067175, 7071068989), (7157307633, 7157309399), (7242470227, 7242471943), (7326542131, 7326543799), (7409510684, 7409512305), (7491363392, 7491364966), (7572087929, 7572089455), (7651672136, 7651673616), (7730104029, 7730105464), (7807371797, 7807373186), (7883463803, 7883465147), (7958368588, 7958369889), (8032074872, 8032076129), (8104571555, 8104572769), (8175847718, 8175848890), (8245892629, 8245893759), (8314695739, 8314696827), (8382246685, 8382247733), (8448535296, 8448536304), (8513551588, 8513552557), (8577285771, 8577286701), (8639728245, 8639729137), (8700869608, 8700870463), (8760700651, 8760701470), (8819212365, 8819213148), (8876395938, 8876396686), (8932242757, 8932243471), (8986744414, 8986745095), (9039892700, 9039893347), (9091679610, 9091680226), (9142097347, 9142097932), (9191138318, 9191138872), (9238795136, 9238795661), (9285060626, 9285061122), (9329927819, 9329928287), (9373389959, 9373390400), (9415440501, 9415440916), (9456073112, 9456073501), (9495281672, 9495282037), (9533060278, 9533060620), (9569403240, 9569403558), (9604305084, 9604305381), (9637760555, 9637760831), (9669764615, 9669764870), (9700312443, 9700312679), (9729399439, 9729399657), (9757021224, 9757021424), (9783173636, 9783173820), (9807852739, 9807852907), (9831054814, 9831054968), (9852776368, 9852776508), (9873014130, 9873014257), (9891765053, 9891765168), (9909026311, 9909026415), (9924795306, 9924795400), (9939069663, 9939069749), (9951847233, 9951847310), (9963126091, 9963126160), (9972904538, 9972904601), (9981181102, 9981181160), (9987954536, 9987954590), (9993223821, 9993223872), (9996988163, 9996988211), (9999246995, 9999247042), (9999999977, 10000000023)]
def tabI (q : ℕ) : ℚ × ℚ :=
 (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)
def tabOk : Bool :=
 allQ (fun q => sinPiOk ((q : ℚ) / 256) && decide ((tabI q).1 ≤ (sinPiI ((q : ℚ) / 256)).1)
   && decide ((sinPiI ((q : ℚ) / 256)).2 ≤ (tabI q).2)) 129
def ineg (I : ℚ × ℚ) : ℚ × ℚ := (-I.2, -I.1)
def sinLook (r : ℕ) : ℚ × ℚ :=
 if r % 512 ≤ 128 then tabI (r % 512)
 else if r % 512 ≤ 256 then tabI (256 - r % 512)
 else if r % 512 ≤ 384 then ineg (tabI (r % 512 - 256))
 else ineg (tabI (512 - r % 512))
def midQ (i : ℕ) : ℚ := (2 * i + 1) / 512
def termU (i j : ℕ) : ℚ :=
 if j = 0 then -(s2LoQ * max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)))
 else if 0 ≤ -(2 * j * cAM j) then -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).2
 else -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).1
def termOk (i : ℕ) : Bool := decide (0 ≤ fl (s2LoQ * midQ i)) && decide (s2HiQ * midQ i ≤ 1)
def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + 87 / 512
def pvCheck (ρ : ℚ) : Bool :=
 tabOk && allQ termOk 128 && decide (sumQ (fun i => max (cellU i) 0) 128 / 320 ≤ ρ)
theorem tabI_sound (h : tabOk = true) {q : ℕ} (hq : q < 129) :
   InI (tabI q) (Real.sin (Real.pi * ((q : ℝ) / 256))) := by
 rw [tabOk, allQ_iff] at h
 have hq' := h q hq
 simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
 obtain ⟨⟨hok, h1⟩, h2⟩ := hq'
 have hs := sinPiI_sound _ hok
 push_cast at hs
 exact ⟨(Rat.cast_le.mpr h1).trans hs.1, hs.2.trans (Rat.cast_le.mpr h2)⟩
theorem ineg_sound {I : ℚ × ℚ} {x : ℝ} (h : InI I x) : InI (ineg I) (-x) := by
 obtain ⟨h1, h2⟩ := h
 unfold ineg InI; push_cast; exact ⟨neg_le_neg h2, neg_le_neg h1⟩
theorem sinLook_sound (h : tabOk = true) (r : ℕ) :
   InI (sinLook r) (Real.sin (Real.pi * ((r : ℝ) / 256))) := by
 have hper : Real.sin (Real.pi * ((r : ℝ) / 256)) = Real.sin (Real.pi * (((r % 512 : ℕ) : ℝ) / 256)) := by
   have hr : (r : ℝ) = ((r % 512 : ℕ) : ℝ) + ((r / 512 : ℕ) : ℝ) * 512 := by
     exact_mod_cast (by omega : r = r % 512 + r / 512 * 512)
   rw [hr, show Real.pi * ((((r % 512 : ℕ) : ℝ) + ((r / 512 : ℕ) : ℝ) * 512) / 256)
     = Real.pi * (((r % 512 : ℕ) : ℝ) / 256) + ((r / 512 : ℕ) : ℝ) * (2 * Real.pi) by ring]
   exact Real.sin_add_nat_mul_two_pi _ _
 rw [hper]
 unfold sinLook
 have hq256 : r % 512 < 512 := Nat.mod_lt _ (by norm_num)
 generalize r % 512 = q at hq256 ⊢
 split_ifs with h1 h2 h3
 · exact tabI_sound h (by omega)
 · have e : Real.sin (Real.pi * ((q : ℝ) / 256)) = Real.sin (Real.pi * (((256 - q : ℕ) : ℝ) / 256)) := by
     rw [Nat.cast_sub h2, show Real.pi * ((((256 : ℕ) : ℝ) - (q : ℝ)) / 256)
       = Real.pi - Real.pi * ((q : ℝ) / 256) by push_cast; ring, Real.sin_pi_sub]
   rw [e]; exact tabI_sound h (by omega)
 · have e : Real.sin (Real.pi * ((q : ℝ) / 256)) = -Real.sin (Real.pi * (((q - 256 : ℕ) : ℝ) / 256)) := by
     rw [Nat.cast_sub (by omega : 256 ≤ q), show Real.pi * (((q : ℝ) - ((256 : ℕ) : ℝ)) / 256)
       = Real.pi * ((q : ℝ) / 256) - Real.pi by push_cast; ring, Real.sin_sub_pi]; ring
   rw [e]; exact ineg_sound (tabI_sound h (by omega))
 · have e : Real.sin (Real.pi * ((q : ℝ) / 256)) = -Real.sin (Real.pi * (((512 - q : ℕ) : ℝ) / 256)) := by
     rw [Nat.cast_sub (by omega : q ≤ 512), show Real.pi * ((((512 : ℕ) : ℝ) - (q : ℝ)) / 256)
       = 2 * Real.pi - Real.pi * ((q : ℝ) / 256) by push_cast; ring, Real.sin_two_pi_sub]; ring
   rw [e]; exact ineg_sound (tabI_sound h (by omega))
theorem termU_sound (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) (j : ℕ) :
   -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ))) ≤ ((termU i j : ℚ) : ℝ) := by
 unfold termU
 have hm0 : (0:ℚ) ≤ midQ i := by unfold midQ; positivity
 by_cases hj : j = 0
 · subst hj
   simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
   simp only [if_true]
   obtain ⟨h0, h1⟩ := hok
   rw [cAM_zero, ωAM_zero, one_mul]
   have hm' : (0:ℝ) ≤ midQ i := by exact_mod_cast hm0
   have hs2 := s2LoQ_le
   have hθ0 : 0 ≤ Real.sqrt 2 * midQ i := mul_nonneg (Real.sqrt_nonneg 2) hm'
   have hθ1 : Real.sqrt 2 * midQ i ≤ 1 := by
     have : ((s2HiQ * midQ i : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
     push_cast at this
     nlinarith [s2HiQ_ge]
   have hl0 : (0:ℝ) ≤ ((fl (s2LoQ * midQ i) : ℚ) : ℝ) := by exact_mod_cast h0
   have hlθ : ((fl (s2LoQ * midQ i) : ℚ) : ℝ) ≤ Real.sqrt 2 * midQ i :=
     (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right hs2 hm')
   have hsin := sin_ge_of hl0 hlθ hθ1
   have hsin0 : 0 ≤ Real.sin (Real.sqrt 2 * midQ i) :=
     Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (hθ1.trans (by linarith [Real.pi_gt_three]))
   have hlb : ((max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)) : ℚ) : ℝ)
       ≤ Real.sin (Real.sqrt 2 * midQ i) := by
     push_cast
     exact max_le hsin0 ((fl_le _).trans (by exact_mod_cast hsin))
   have hs2lo0 : (0:ℝ) ≤ ((s2LoQ : ℚ) : ℝ) := by simp only [s2LoQ]; push_cast; norm_num
   push_cast at hlb ⊢
   nlinarith
 · simp only [hj, if_false]
   have hω : ωAM j = 2 * Real.pi * j := by simp [ωAM, hj]
   have hS := piMul_sound (sinLook_sound htab (j * (2 * i + 1)))
   have e : -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * (midQ i : ℝ)))
       = ((-(2 * j * cAM j) : ℚ) : ℝ)
         * (Real.pi * Real.sin (Real.pi * (((j * (2 * i + 1) : ℕ) : ℝ) / 256))) := by
     rw [hω]; simp only [midQ]; push_cast; ring_nf
   rw [e]
   obtain ⟨h1, h2⟩ := hS
   split_ifs with he
   · have he' : (0:ℝ) ≤ ((-(2 * j * cAM j) : ℚ) : ℝ) := by exact_mod_cast he
     push_cast at he' h2 ⊢
     exact mul_le_mul_of_nonneg_left h2 he'
   · have he' : ((-(2 * j * cAM j) : ℚ) : ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
     push_cast at he' h1 ⊢
     exact mul_le_mul_of_nonpos_left h1 he'
theorem vAMd_mid_le (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) :
   vAMd (midQ i) ≤ ((sumQ (termU i) 13 : ℚ) : ℝ) := by
 rw [sumQ_eq, Rat.cast_sum, vAMd]
 exact Finset.sum_le_sum fun j _ => termU_sound htab hok j
theorem vAMd_lipschitz (x y : ℝ) : vAMd y ≤ vAMd x + 87 * |y - x| := by
 have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := vAMd) (s := Set.univ) (C := 87)
   (fun x _ => (hasDerivAt_vAMd x).differentiableAt)
   (fun x _ => by rw [Real.norm_eq_abs, (hasDerivAt_vAMd x).deriv]; exact abs_vAMdd_le x)
   convex_univ (Set.mem_univ x) (Set.mem_univ y)
 rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
 linarith [le_abs_self (vAMd y - vAMd x)]
theorem deriv_vAM_div : deriv (fun s => vAM s / MAM) = fun s => vAMd s / MAM :=
 funext fun s => ((hasDerivAt_vAM s).div_const MAM).deriv
theorem posVar_of_check {ρ : ℚ} (h : pvCheck ρ = true) :
   ∫ s in (0:ℝ)..(1 / 2), max (deriv (fun s => vAM s / MAM) s) 0 ≤ (ρ : ℝ) := by
 simp only [pvCheck, Bool.and_eq_true, decide_eq_true_eq] at h
 obtain ⟨⟨htab, hcells⟩, hsum⟩ := h
 rw [allQ_iff] at hcells
 rw [deriv_vAM_div]
 have hM : (0:ℝ) < MAM := MAM_pos
 set a : ℕ → ℝ := fun k => (k : ℝ) / 256 with ha
 have hcont : Continuous fun s => max (vAMd s / MAM) 0 :=
   (((continuous_iff_continuousAt.mpr fun x => (hasDerivAt_vAMd x).continuousAt)).div_const MAM).max
     continuous_const
 have hcell : ∀ i < 128, ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
     ≤ 1 / 256 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
   intro i hi
   have hab : a i ≤ a (i + 1) := by simp only [ha]; gcongr; push_cast; linarith
   have hmid : ((midQ i : ℚ) : ℝ) = (2 * i + 1) / 512 := by simp only [midQ]; push_cast; ring
   have hvm := vAMd_mid_le htab (hcells i hi)
   have hpt : ∀ s ∈ Set.Icc (a i) (a (i + 1)), max (vAMd s / MAM) 0
       ≤ ((max (cellU i) 0 : ℚ) : ℝ) / MAM := by
     intro s hs
     have hd : |s - (midQ i : ℝ)| ≤ 1 / 512 := by
       rw [hmid, abs_le]
       simp only [ha, Set.mem_Icc] at hs
       push_cast at hs
       obtain ⟨hs1, hs2⟩ := hs
       constructor <;> linarith
     have hlip := vAMd_lipschitz (midQ i : ℝ) s
     have hU : vAMd s ≤ ((cellU i : ℚ) : ℝ) := by
       simp only [cellU]; push_cast
       linarith
     push_cast
     exact max_le ((div_le_div_of_nonneg_right hU hM.le).trans
       (div_le_div_of_nonneg_right (le_max_left _ _) hM.le)) (div_nonneg (le_max_right _ _) hM.le)
   calc ∫ s in a i..a (i + 1), max (vAMd s / MAM) 0
       ≤ ∫ s in a i..a (i + 1), ((max (cellU i) 0 : ℚ) : ℝ) / MAM :=
         intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
           (continuous_const.intervalIntegrable _ _) hpt
     _ = 1 / 256 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
         rw [intervalIntegral.integral_const, smul_eq_mul]
         simp only [ha]; push_cast; ring
 have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
   (f := fun s => max (vAMd s / MAM) 0) (a := a) (n := 128) (fun k _ => hcont.intervalIntegrable _ _)
 have ha0 : a 0 = 0 := by simp [ha]
 have haN : a 128 = 1 / 2 := by simp only [ha]; norm_num
 rw [ha0, haN] at hsplit
 rw [← hsplit]
 refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
 have hq : ((sumQ (fun i => max (cellU i) 0) 128 / 320 : ℚ) : ℝ) ≤ (ρ : ℝ) := by
   exact_mod_cast hsum
 refine le_of_eq_of_le ?_ hq
 rw [sumQ_eq, ← Finset.mul_sum, ← Finset.sum_div]
 push_cast
 simp only [MAM]
 ring
set_option maxRecDepth 100000 in
theorem pvCheck_AM : pvCheck (9 / 200) = true := by decide +kernel
theorem deriv2_vAM_div : deriv (deriv (fun s => vAM s / MAM)) = fun s => vAMdd s / MAM := by
 rw [deriv_vAM_div]
 exact funext fun s => ((hasDerivAt_vAMd s).div_const MAM).deriv
theorem vAM_zero_div_le : vAM 0 / MAM ≤ 81 / 100 := by
 rw [vAM_zero, MAM]; norm_num
theorem profile_AM : Profile (fun s => vAM s / MAM) (1 / 10) (14 / 5) (348 / 5) (9 / 200) where
 δ_pos := by norm_num
 A₁_nonneg := by norm_num
 A₂_nonneg := by norm_num
 even := fun s => by simp only [vAM_even]
 contDiff := (vAM_contDiff.of_le le_top).div_const MAM
 pos := fun s hs => div_pos (vAM_pos_wide (by linarith)) MAM_pos
 ge_quarter := fun s hs => by
   have := vAM_ge_core hs
   rw [MAM, le_div_iff₀ (by norm_num)]; linarith
 le_one := fun s _ => by rw [div_le_one MAM_pos]; exact vAM_le s
 deriv_le := fun s _ => by
   rw [deriv_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_vAMd_le s]
 deriv2_le := fun s _ => by
   rw [deriv2_vAM_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_vAMdd_le s]
 posVar := by
   have h := posVar_of_check pvCheck_AM
   push_cast at h
   exact h
 budget := by
   have h0 : Real.sqrt (vAM 0 / MAM) ≤ 9 / 10 := by
     rw [show (9 / 10 : ℝ) = Real.sqrt (81 / 100) by
       rw [show (81 / 100 : ℝ) = (9 / 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
     exact Real.sqrt_le_sqrt vAM_zero_div_le
   linarith
 budget_sq := by linarith [vAM_zero_div_le]
def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (14 / 5) (348 / 5 + 2 * (14 / 5) ^ 2)
theorem admWindow_phiW {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   AdmWindow (phiW ϱ L w) L w (cAMW ϱ) :=
 admWindow_fP profile_AM hϱ hw hwL
end AMW
end
noncomputable section
open Filter Complex Real Set MeasureTheory
namespace AMW
open Zeta23
section generic
variable {P : Params} {W : ℝ → ℝ → ℝ} {cW : ℝ} (hP : P.Valid) (hev : ∀ T u, W T (-u) = W T u)
 (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w cW)
include hP hev hW
theorem poissonSqW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ZeroSide.PoissonSq T (atW P W T) := by
 intro γ
 have h := (hW T h8).hasSum_vHatR_mul T γ γ
 rw [sub_self, (hW T h8).VPhiR_zero] at h
 simp only [atW_phiHatR T hP (hev T), atW_a T hP (hev T), atW_tau_eq, atW_L, sq]
 convert h using 1
 ring
theorem GzGpW (Z : ZeroConfig) (H : PaperInputs Z) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
   Z.Gz (atW P W T) T = (atW P W T).Gp T := by
 have hL : 0 < P.L T := by linarith [hP.one_le_w]
 refine Z.Gz_eq_Gp (atW P W T) T H.EF hL ?_ ?_
 · rw [atW_phi_valid T hP (hev T)]; exact (hW T h8).vC_contDiff
 · rw [atW_phi_valid T hP (hev T)]; exact closure_minimal (hW T h8).support_subset isClosed_Icc
omit hP hev hW in
lemma C1W_nonneg (W : ℝ → ℝ → ℝ) (T : ℝ) : 0 ≤ ∫ u, |deriv (deriv (W T)) u| :=
 integral_nonneg fun _ => abs_nonneg _
omit hev in
lemma C1W_le {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ∫ u, |deriv (deriv (W T)) u| ≤ cW :=
 (hW T h8).l1_deriv2.trans (div_le_self (hW T h8).c_nonneg hP.one_le_w)
theorem hdecayW {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
   ‖(atW P W T).phiHat T (r - I * y)‖
     ≤ Real.exp ((atW P W T).L T / 4) * (∫ u, |deriv (deriv (W T)) u|) / ‖(r : ℂ) - I * y‖ ^ 2 := by
 have hL : 0 ≤ P.L T := (hW T h8).L_pos.le
 rw [atW_phiHat T hP (hev T), atW_L, le_div_iff₀ (by positivity)]
 refine le_trans ((hW T h8).norm_vHat_mul_sq_le _) ?_
 gcongr
 have him : ((r : ℂ) - I * y).im = -y := by simp
 rw [him, abs_neg]
 nlinarith
theorem eventually_tailPackageW (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (atW P W T).a T) (Z : ZeroConfig)
   (H : PaperInputs Z) :
   ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atW P W T) T (θ₀ T)) ∧
     ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * ∫ u, |deriv (deriv (W T)) u|) T, ?_, ?_⟩
 · have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (ThmD.tendsto_L hP).eventually_ge_atTop 2
   filter_upwards [eventually_ge_atTop Tail.T₀, hL2, ThmD.eventually_w8 hP, ha] with T hT hL h8 haT
   have HT : Tail.TailHyp Z (atW P W T) T A₀ (∫ u, |deriv (deriv (W T)) u|) :=
     { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := C1W_nonneg W T,
       hdecay := fun r y hy hz => hdecayW hP hev hW h8 r y hy hz }
   exact HT.tailInputs (by linarith) (fun z => GzGp.phiHat_conj _ T z)
 · exact Tail.eventually_theta0_le P hP hA₀ (fun T => ∫ u, |deriv (deriv (W T)) u|)
     (C1W_nonneg W) (R := cW / 2) ((ThmD.eventually_w8 hP).mono fun T h8 => by linarith [C1W_le hP hW h8])
theorem eventually_GzGpW (Z : ZeroConfig) (H : PaperInputs Z) :
   ∀ᶠ T in atTop, Z.Gz (atW P W T) T = (atW P W T).Gp T := by
 filter_upwards [ThmD.eventually_w8 hP] with T h8
 exact GzGpW hP hev hW Z H h8
end generic
def WAM (P : Params) (T : ℝ) : ℝ → ℝ := phiW P.ϱ (P.L T) P.w
def atAM (P : Params) (T : ℝ) : Params := atW P (WAM P) T
variable {P : Params}
theorem WAM_even (P : Params) (T u : ℝ) : WAM P T (-u) = WAM P T u := phiW_even u
theorem admWindow_WAM (hP : P.Valid) (T : ℝ) (h8 : 8 * P.w ≤ P.L T) :
   AdmWindow (WAM P T) (P.L T) P.w (cAMW P.ϱ) :=
 admWindow_phiW hP.taper hP.one_le_w h8
theorem atAM_a (hP : P.Valid) (T : ℝ) : (atAM P T).a T = AdmWindow.av (WAM P T) (P.L T) :=
 atW_a T hP (WAM_even P T)
lemma phiW_sq_ge (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
   681 / 1250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ WAM P T u ^ 2 := by
 have hw0 : 0 < P.w := by linarith [hP.one_le_w]
 have hL : 0 < P.L T := by linarith [hP.one_le_w]
 rw [WAM, phiW_sq_eq hP.taper hw0 hL]
 rcases le_or_gt (P.L T / 2) |u| with hu | hu
 · rw [Taper.phi_eq_zero hP.taper hw0 hu]; simp
 · exact mul_le_mul_of_nonneg_right (hW_core_ge hL hu.le) (sq_nonneg _)
theorem aAM_range_of (hP : P.Valid) {T : ℝ} (h32 : 32 * P.w ≤ P.L T) :
   1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
 have h8 : 8 * P.w ≤ P.L T := by linarith [hP.one_le_w]
 have hW := admWindow_WAM hP T h8
 rw [atAM_a hP]
 refine ⟨?_, hW.av_le_one⟩
 have hw0 : 0 < P.w := by linarith [hP.one_le_w]
 have h2 : 2 * P.w ≤ P.L T := by linarith
 have hL : 0 < P.L T := by linarith [hP.one_le_w]
 have hb : 1 - 2 * P.w / P.L T ≤ Taper.aConst P.ϱ (P.L T) P.w :=
   (Taper.one_sub_le_bConst hP.taper hw0 h2).trans (Taper.bConst_le_aConst hP.taper hw0 h2)
 have hwL : 2 * P.w / P.L T ≤ 1 / 16 := by rw [div_le_iff₀ hL]; linarith
 have hint : Integrable (fun u => WAM P T u ^ 2) := hW.integrable_pow two_pos
 have hint' : Integrable (fun u => 681 / 1250 * Taper.phi P.ϱ (P.L T) P.w u ^ 2) :=
   (((Taper.phi_continuous hP.taper hw0 h2).fun_pow 2).integrable_of_hasCompactSupport
     ((Taper.phi_hasCompactSupport hP.taper hw0).comp_left (g := fun t => t ^ 2) (by norm_num))).const_mul _
 have hcmp : 681 / 1250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ ∫ u, WAM P T u ^ 2 := by
   rw [← integral_const_mul]
   exact integral_mono hint' hint (phiW_sq_ge hP h8)
 unfold AdmWindow.av
 unfold Taper.aConst at hb
 have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
 calc (1:ℝ) / 2 ≤ 681 / 1250 * (1 - 2 * P.w / P.L T) := by nlinarith
   _ ≤ 681 / 1250 * ((P.L T)⁻¹ * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by gcongr
   _ = (P.L T)⁻¹ * (681 / 1250 * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by ring
   _ ≤ (P.L T)⁻¹ * ∫ u, WAM P T u ^ 2 := mul_le_mul_of_nonneg_left hcmp hLi.le
theorem eventually_w32 (hP : P.Valid) : ∀ᶠ T in atTop, 32 * P.w ≤ P.L T :=
 (ThmD.tendsto_L hP).eventually_ge_atTop _
theorem eventually_aAM_range (hP : P.Valid) :
   ∀ᶠ T in atTop, 1 / 2 ≤ (atAM P T).a T ∧ (atAM P T).a T ≤ 1 := by
 filter_upwards [eventually_w32 hP] with T h32
 exact aAM_range_of hP h32
theorem eventually_GzGpAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
   ∀ᶠ T in atTop, Z.Gz (atAM P T) T = (atAM P T).Gp T :=
 eventually_GzGpW hP (WAM_even P) (admWindow_WAM hP) Z H
theorem eventually_tailPackageAM (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) :
   ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (atAM P T) T (θ₀ T)) ∧
     ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) :=
 eventually_tailPackageW hP (WAM_even P) (admWindow_WAM hP)
   ((eventually_aAM_range hP).mono fun _ h => h.1) Z H
end AMW
end
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
namespace AMW
open Zeta23 ThmD PrimeSide PaperParams
def lfW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : PrimeSide.LocalFun := AdmWindow.localFun (W T) (P.L T)
variable (P : Params) (W : ℝ → ℝ → ℝ)
def concreteDataW (Z : ZeroConfig) : DataD P where
 aT := fun T => (lfW P W T).a
 bT := fun T => (lfW P W T).b
 trG := fun T => trGtA (P.toSetting T) (lfW P W T)
 trG2 := fun T => trGt2A (P.toSetting T) (lfW P W T)
 Ncnt := fun T => (Z.N T (2 * T) : ℝ)
 Mtot := fun T => MtotalA (P.toSetting T) (lfW P W T)
 Mmumu := fun T => Mform (lfW P W T).Phi T Zeta23.mu Zeta23.mu
 MPP := fun T => Mform (lfW P W T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PX (P.X T))
 MmuP := fun T => Mform (lfW P W T).Phi T Zeta23.mu (Zeta23.PX (P.X T))
 MmuPi := fun T => Mform (lfW P W T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
 MPPi := fun T => Mform (lfW P W T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PiX (P.X T))
 MPiPi := fun T => Mform (lfW P W T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
 intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
 sumL2g := fun T => sumA2g (P.X T) (lfW P W T).g
 JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y
def LocalHypsCoreWEventually (c : ℝ) : Prop :=
 ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → PrimeSide.LocalHypsCore c (P.toSetting T) (lfW P W T)
variable {P W}
theorem localHypsCoreW_eventually {c : ℝ} (hP : P.Valid)
   (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
   (hb : ∀ᶠ T in atTop, 1 / 2 ≤ AdmWindow.bv (W T) (P.L T)) : LocalHypsCoreWEventually P W c := by
 have hl : Tendsto l atTop atTop :=
   Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
 have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
 have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
   filter_upwards [hL.eventually_ge_atTop 0] with T h
   simpa [Params.X] using Real.one_le_exp h
 obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
   ((hL.eventually_ge_atTop (8 * P.w)).and (hb.and hX)))
 refine ⟨T₀, fun T hT => ?_⟩
 obtain ⟨h1, h8, hbT, hX1⟩ := hT₀ T hT
 exact AdmWindow.localHypsCore (P.toSetting T) (hW T h8) hP.lam_pos hP.lam_le_one h1 hX1 hbT
lemma evBound_of_eventuallyAtCoreW {c : ℝ} (hLoc : LocalHypsCoreWEventually P W c)
   {f g : Setting → LocalFun → ℝ}
   (h : ∃ C : ℝ, EventuallyAtCore c P.lam (fun p F => |f p F| ≤ C * g p F))
   (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (lfW P W T)) :
   EvBound (fun T => f (P.toSetting T) (lfW P W T)) (fun T => g (P.toSetting T) (lfW P W T)) := by
 obtain ⟨T₀, hT₀⟩ := hLoc
 obtain ⟨C, T₁, hT₁⟩ := h
 obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
 refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
 have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
 have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
 have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
 have := hT₁ (P.toSetting T) (lfW P W T) rfl h1 (hT₀ T h0)
 calc |f (P.toSetting T) (lfW P W T)| ≤ C * g (P.toSetting T) (lfW P W T) := this
   _ ≤ max C 1 * g (P.toSetting T) (lfW P W T) :=
     mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)
theorem gW_deriv_facts {c L w : ℝ} {v : ℝ → ℝ} (hW : AdmWindow v L w c) :
   Differentiable ℝ (Params.autocorr (fun u => v u ^ 2))
     ∧ Continuous (deriv (Params.autocorr (fun u => v u ^ 2)))
     ∧ ∀ y : ℝ, |deriv (Params.autocorr (fun u => v u ^ 2)) y| ≤ 2 := by
 apply ThmD.autocorr_deriv_facts
 · exact (hW.contDiff.pow 2).of_le (by norm_num)
 · exact hW.sq_hasCompactSupport
 · intro x; exact hW.sq_even x
 · intro u
   rw [abs_of_nonneg (sq_nonneg _)]
   calc v u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (hW.nonneg u) (hW.le_one u) 2
     _ = 1 := one_pow 2
 · exact hW.l1_deriv_sq
theorem concreteFactsW {Z : ZeroConfig} {c : ℝ} (hP : P.Valid) (inp : PaperInputs Z)
   (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
   (hLoc : LocalHypsCoreWEventually P W c) : FactsD (concreteDataW P W Z) := by
 have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
 have hΓ := inp.Gamma
 have hcheb := inp.cheb
 have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
   filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
     eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
   exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
 obtain ⟨T₀, hT₀⟩ := id hLoc
 have e_ends := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.lem_ends c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
 have e_mumu := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_mumu c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
   exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
 have e_PP := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_PP (cϱ := c) (lam := P.lam) hcheb inp.MV hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact mul_nonneg (sq_nonneg _) hX)
 have e_muP := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_cross_muP c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact mul_nonneg hl (Real.sqrt_nonneg _))
 have e_muPi := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_cross_muPi c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
 have e_PPi := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_cross_PPi c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact mul_nonneg hL hX)
 have e_PiPi := evBound_of_eventuallyAtCoreW hLoc
   (PrimeSide.prop_cross_PiPi c P.lam hΓ hcheb hlam) (by
   filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
   exact div_nonneg (mul_nonneg hL hX) hT)
 refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?ab_range, rvm_evBound inp.RvM, ?muints2,
   ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP, e_muPi, e_PPi, e_PiPi⟩
 case ab_range =>
   filter_upwards [eventually_ge_atTop T₀, ThmD.eventually_w8 hP] with T hT h8
   have hF := hT₀ T hT
   have hL0 : 0 < P.L T := by linarith [hP.one_le_w]
   refine ⟨hF.b_ge_half, hF.b_le_a, hF.a_le_one, ?_, ?_⟩
   · apply mul_nonneg (by positivity)
     apply intervalIntegral.integral_nonneg (by linarith : (0:ℝ) ≤ P.L T)
     intro y hy
     exact mul_nonneg (hF.g_nonneg y) hy.1
   · have hgcont : Continuous (lfW P W T).g := (gW_deriv_facts (hW T h8)).1.continuous
     have hgle : ∀ y ∈ Set.Icc (0:ℝ) (P.L T), (lfW P W T).g y * y ≤ P.L T * y := by
       intro y hy
       apply mul_le_mul_of_nonneg_right _ hy.1
       calc (lfW P W T).g y ≤ (lfW P W T).Aphi y := hF.g_le_Aphi y
         _ ≤ max ((P.toSetting T).L - |y|) 0 := hF.Aphi_le y
         _ ≤ P.L T := by
             apply max_le _ hL0.le
             have := abs_nonneg y
             show (P.toSetting T).L - |y| ≤ P.L T
             have e : (P.toSetting T).L = P.L T := rfl
             rw [e]
             linarith
     have hIle : ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y
         ≤ ∫ y in (0:ℝ)..(P.L T), P.L T * y := by
       apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ P.L T) ?_ ?_ hgle
       · exact (hgcont.mul continuous_id).intervalIntegrable 0 (P.L T)
       · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (P.L T)
     have hIval : ∫ y in (0:ℝ)..(P.L T), P.L T * y = P.L T ^ 3 / 2 := by
       rw [intervalIntegral.integral_const_mul, integral_id]
       ring
     calc 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y
         ≤ 2 / P.L T ^ 3 * (P.L T ^ 3 / 2) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           rw [← hIval]
           exact hIle
       _ = 1 := by field_simp
 case muints2 =>
   obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
   refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
     (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
   have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
   rw [mul_div_assoc]
   refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
   exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
 case prop_trace =>
   obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
   obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace c P.lam hΓ hcheb hlam A
   refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
   have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
   have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
   have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
   have hF := hT₀ T h0
   have := hC (P.toSetting T) (lfW P W T) rfl h2 hF (Z.N T (2 * T) : ℝ) (hN T h1)
   refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
   exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
 case Msplit =>
   filter_upwards [eventually_ge_atTop T₀] with T hT
   exact eq_Msplit c hΓ (P.toSetting T) (lfW P W T) (hT₀ T hT)
 case sumJ =>
   obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close hcheb
   refine ⟨C, hC0, ?_⟩
   obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos 8)
   obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (ThmD.eventually_w8 hP)
   refine ⟨max T₀ (max T₁ T₂), fun T hT => ?_⟩
   have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
   have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
   have hL8 : 8 ≤ P.L T := hT₁ T h1
   have h8 : 8 * P.w ≤ P.L T := hT₂ T h2
   have hg := gW_deriv_facts (hW T h8)
   have hgsupp : ∀ y : ℝ, P.L T ≤ y → (lfW P W T).g y = 0 := by
     intro y hy
     exact (hW T h8).gv_eq_zero (by rw [abs_of_nonneg (by linarith)]; exact hy)
   have key := hC (P.L T) (P.X T) (lfW P W T).g hL8 (by
       show P.X T = Real.exp (P.L T)
       rfl) hg.1 hg.2.1 hg.2.2 hgsupp
   have e : P.L T ^ 3 / 2 * ((concreteDataW P W Z).JT T)
       = ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y := by
     show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (lfW P W T).g y * y) = _
     have hL0 : 0 < P.L T := by linarith
     field_simp
   show |sumA2g (P.X T) (lfW P W T).g - P.L T ^ 3 / 2 * ((concreteDataW P W Z).JT T)|
     ≤ C * P.L T ^ 2
   rw [e]
   exact key
theorem tracesBoundsW_concrete {Z : ZeroConfig} {c : ℝ} (hP : P.Valid) (inp : PaperInputs Z)
   (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (W T) (P.L T) P.w c)
   (hLoc : LocalHypsCoreWEventually P W c) :
   TracesBoundsD P (concreteDataW P W Z).aT (concreteDataW P W Z).bT (concreteDataW P W Z).JT
     (concreteDataW P W Z).trG (concreteDataW P W Z).trG2 (concreteDataW P W Z).Ncnt :=
 tracesBoundsD_of_factsD _ (concreteFactsW hP inp hW hLoc)
theorem atW_ident (Z : ZeroConfig) (hP : P.Valid) (hev : ∀ T u, W T (-u) = W T u) (T : ℝ) :
   (atW P W T).trGtilde T = (concreteDataW P W Z).trG T ∧
     (atW P W T).trGtildeSq T = (concreteDataW P W Z).trG2 T ∧
     (atW P W T).a T = (concreteDataW P W Z).aT T :=
 ⟨atW_trGtilde T hP (hev T), atW_trGtildeSq T hP (hev T), atW_a T hP (hev T)⟩
end AMW
end
noncomputable section
open Real Set MeasureTheory Filter
namespace AMW
open Zeta23
variable {P : Params}
theorem eventually_bAM_ge_half (hP : P.Valid) :
   ∀ᶠ T in atTop, 1 / 2 ≤ AdmWindow.bv (WAM P T) (P.L T) :=
 eventually_bW_ge_half hP
theorem localHypsCoreAM_eventually (hP : P.Valid) : LocalHypsCoreWEventually P (WAM P) (cAMW P.ϱ) :=
 localHypsCoreW_eventually hP (admWindow_WAM hP) (eventually_bAM_ge_half hP)
theorem tracesBoundsAM_concrete {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z) :
   ThmD.TracesBoundsD P (concreteDataW P (WAM P) Z).aT (concreteDataW P (WAM P) Z).bT
     (concreteDataW P (WAM P) Z).JT (concreteDataW P (WAM P) Z).trG (concreteDataW P (WAM P) Z).trG2
     (concreteDataW P (WAM P) Z).Ncnt :=
 tracesBoundsW_concrete hP inp (admWindow_WAM hP) (localHypsCoreAM_eventually hP)
end AMW
end
set_option linter.all false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder
namespace Zeta23Ext.StableRankTrace
def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3
lemma Psi_eq_gc_two_add_one (t : ℝ) : Psi t = gc 2 t + 1 := by
 unfold Psi
 split_ifs with h
 · rw [gc_of_le h]; ring
 · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring
lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
 unfold Psi
 split_ifs with h
 · positivity
 · have : (2 : ℝ) < t := not_le.mp h
   linarith
section Eigen
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
 fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j
lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
   Wmat hP.1.eigenvalues (eigCols hP)
     = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
       * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
 ext a j
 simp only [Wmat, eigCols, Matrix.mul_diagonal]
 ring
lemma pmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
   Pmat hP.1.eigenvalues (eigCols hP) = P := by
 have hdd : (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)
       * ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜))
     = RCLike.ofReal ∘ hP.1.eigenvalues := by
   funext j
   simp only [Function.comp_apply, ← RCLike.ofReal_mul]
   rw [Real.mul_self_sqrt (hP.eigenvalues_nonneg j)]
 have hstar : (diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)))ᴴ
     = diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
   rw [diagonal_conjTranspose]
   simp [RCLike.star_def]
 unfold Pmat
 rw [wmat_eigCols hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
   Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
 conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
 rfl
lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
   xsq (eigCols hP) j = 1 := by
 have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
 rw [mem_doublyStochastic_iff_sum] at hDS
 simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j
end Eigen
section Main
variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
 [Fintype r] [DecidableEq r]
lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
   rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
 unfold rtrace
 rw [trace_mul_comm, Matrix.trace, map_sum]
 refine Finset.sum_congr rfl fun j _ => ?_
 rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
 simp
lemma rtrace_specMap_Psi (V : Matrix n r 𝕜) :
   rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
     = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
       + (Fintype.card r : ℝ) := by
 rw [rtrace_specMap]
 have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := Psi_eq_gc_two_add_one
 simp only [hshift]
 rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
 congr 1
 exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm
theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
   {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
   2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
       + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
     ≤ frobSq (V * Vᴴ + Q) := by
 classical
 have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
 have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
 have hR := rank_trace_mult hm (eigCols hP) hQ hb (c := 2) (by norm_num)
 rw [pmat_eigCols hP] at hR
 have hx : ∀ j, hP.1.eigenvalues j * xsq (eigCols hP) j = hP.1.eigenvalues j := by
   intro j; rw [xsq_eigCols hP j, mul_one]
 simp only [hx] at hR
 rw [rtrace_specMap_Psi V]
 have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
 linarith [hR]
theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
   {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
   4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
       + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
     ≤ frobSq (V * Vᴴ + Q) := by
 have hsharp := stable_rank_trace_sharp V hQ hb
 have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
   rw [rtrace_self_mul_conjTranspose V]
   calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
     _ = (Fintype.card r : ℝ) := by simp
 rw [rtrace_add]
 linarith
end Main
end Zeta23Ext.StableRankTrace
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.StableRankTrace
namespace Zeta23Ext.Bridge
def Kfun (x : ℝ) : ℝ := AMW.KfunAM x
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0
def wfun (x : ℝ) : ℝ := kfun x ^ 2
def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
 ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0
section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
 ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2
def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
 if h : B.Nonempty then B.sup' h x - B.inf' h x else 0
lemma abs_sub_le_spanOf (x : ι → ℝ) {B : Finset ι} {i j : ι} (hi : i ∈ B) (hj : j ∈ B) :
   |x i - x j| ≤ spanOf x B := by
 have hne : B.Nonempty := ⟨i, hi⟩
 unfold spanOf
 rw [dif_pos hne, abs_le]
 constructor
 · linarith [Finset.le_sup' x hj, Finset.inf'_le x hi]
 · linarith [Finset.le_sup' x hi, Finset.inf'_le x hj]
lemma spanOf_nonneg (x : ι → ℝ) (B : Finset ι) : 0 ≤ spanOf x B := by
 unfold spanOf
 split_ifs with h
 · obtain ⟨i, hi⟩ := h
   linarith [Finset.le_sup' x hi, Finset.inf'_le x hi]
 · exact le_rfl
def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)
lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
 unfold defect
 rw [rtrace_specMap]
 exact Finset.sum_nonneg fun _ _ => Psi_nonneg _
def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
 defect (hM.submatrix (Subtype.val : B → ι))
lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
   0 ≤ blockDefect hM B :=
 defect_nonneg _
end Blocks
section BlockLevel
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)
def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ
def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c
def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c
lemma P₁_posSemidef (c : ℝ) : (P₁ D c).PosSemidef := posSemidef_self_mul_conjTranspose _
lemma gramS₁_isHermitian (c : ℝ) : (gramS₁ D c).IsHermitian :=
 isHermitian_conjTranspose_mul_self _
lemma blockP_isHermitian (c : ℝ) : (D.blockP c).IsHermitian :=
 ZeroBlockData.isHermitian_real_smul D.onPart_posSemidef.isHermitian _
lemma Q'_isHermitian (c : ℝ) : (Q' D c).IsHermitian :=
 ((blockP_isHermitian D c).add (D.blockQ_isHermitian c)).sub (P₁_posSemidef D c).1
lemma P₁_add_Q' (c : ℝ) : P₁ D c + Q' D c = D.blockP c + D.blockQ c := by
 unfold Q'; abel
end BlockLevel
section Concrete
open Classical
def mtParams (T : ℝ) : Params := AMW.atAM (paramsOf stdProfile 1) T
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)
def aL2 : ℝ := P.a T * P.L T ^ 2
def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj
def retained : Finset (ZI Z T) :=
 (bdata Z P T).S₁.filter fun z =>
   P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
 (Finset.mem_filter.mp hz).1
def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
 fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩
lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
 fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)
def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
 (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)
lemma gram_isHermitian : (gram Z P T).IsHermitian :=
 (gramS₁_isHermitian _ _).submatrix _
def Dcirc : ℝ := defect (gram_isHermitian Z P T)
def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)
lemma re_eq_half_of_mem_S₁ {z : ZI Z T} (hz : z ∈ (bdata Z P T).S₁) : (z : ℂ).re = 1 / 2 := by
 have h : (bdata Z P T).σ z = z := by
   simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hz
   exact hz.1
 exact (mkData_σ_eq_iff Z T _ _ z).mp h
lemma xret_injective (hL : 0 < P.L T) : Function.Injective (xret Z P T) := by
 intro z z' h
 have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
 have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
 unfold xret xnorm at h
 have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
 have him : (z.1 : ℂ).im = (z'.1 : ℂ).im := by
   have h1 := (div_left_inj' hpi.ne').mp h
   have h2 := mul_left_cancel₀ hL.ne' h1
   linarith
 apply Subtype.ext; apply Subtype.ext
 exact Complex.ext (by rw [hz, hz']) him
end Concrete
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace Zeta23Ext.Bridge
lemma Kfun_neg (x : ℝ) : Kfun (-x) = Kfun x := AMW.KfunAM_neg x
lemma kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
 unfold kfun; rw [Kfun_neg]
lemma wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
 unfold wfun; rw [kfun_neg]
lemma wfun_sub_comm (a b : ℝ) : wfun (a - b) = wfun (b - a) := by
 rw [← wfun_neg, neg_sub]
lemma wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _
lemma abs_Kfun_le_Kfun_zero (x : ℝ) : |Kfun x| ≤ Kfun 0 := AMW.abs_KfunAM_le x
lemma abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := by
 unfold kfun
 rw [abs_div]
 rcases eq_or_ne (Kfun 0) 0 with h | h
 · rw [h, abs_zero, div_zero]; exact zero_le_one
 · rw [div_le_one (abs_pos.mpr h)]
   exact (abs_Kfun_le_Kfun_zero x).trans (le_abs_self _)
section Sorted
variable {m : ℕ}
def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0
lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
 unfold sortedExt; rw [dif_pos h]
lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
   sortedExt y a ≤ sortedExt y b := by
 rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
 exact hy.monotone (Fin.mk_le_mk.mpr hab)
def windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
 fun j => Y (i + ((j : ℕ) + 1)) - Y (i + j)
lemma range_filter_lt {N k : ℕ} (hk : k ≤ N) : ((range N).filter fun j => j < k) = range k := by
 ext j
 simp only [mem_filter, mem_range]
 omega
lemma ptsN_windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) (k : Fin n) :
   ptsN n (windowGaps n Y i) k = Y (i + k) - Y i := by
 have hk : (k : ℕ) ≤ n - 1 := by have := k.2; omega
 unfold ptsN windowGaps
 rw [Fin.sum_univ_eq_sum_range
   (fun j => if j < (k : ℕ) then Y (i + (j + 1)) - Y (i + j) else 0) (n - 1),
   ← sum_filter, range_filter_lt hk]
 have := Finset.sum_range_sub (fun j => Y (i + j)) (k : ℕ)
 simpa using this
end Sorted
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Zeta23Ext.Bridge
section PsiConvex
open Zeta23Ext.StableRankTrace
lemma affine_le_Psi {s x : ℝ} (hs : s ≤ 2) : 2 * (s - 1) * x - (s ^ 2 - 1) ≤ Psi x := by
 unfold Psi
 split_ifs with h
 · nlinarith [sq_nonneg (x - s)]
 · have hx : 2 < x := not_le.mp h
   nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : (0 : ℝ) ≤ 2 * x - 2 - s)]
lemma affine_eq_Psi (x : ℝ) : 2 * (min x 2 - 1) * x - ((min x 2) ^ 2 - 1) = Psi x := by
 unfold Psi
 rcases le_or_gt x 2 with h | h
 · rw [min_eq_left h, if_pos h]; ring
 · rw [min_eq_right h.le, if_neg (not_le.mpr h)]; ring
theorem Psi_convexOn : ConvexOn ℝ Set.univ Psi := by
 refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
 simp only [smul_eq_mul]
 set z := a * x + b * y with hz
 set t := min z 2 with ht
 have ht2 : t ≤ 2 := min_le_right _ _
 have hx := affine_le_Psi (x := x) ht2
 have hy := affine_le_Psi (x := y) ht2
 have hsplit : 2 * (t - 1) * z - (t ^ 2 - 1)
     = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := by
   rw [hz]; linear_combination (t ^ 2 - 1) * hab
 calc Psi z = 2 * (t - 1) * z - (t ^ 2 - 1) := (affine_eq_Psi z).symm
   _ = a * (2 * (t - 1) * x - (t ^ 2 - 1)) + b * (2 * (t - 1) * y - (t ^ 2 - 1)) := hsplit
   _ ≤ a * Psi x + b * Psi y :=
       add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
end PsiConvex
section Entries
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma re_mul_conjTranspose_apply_self (Y : Matrix κ ι 𝕜) (j : κ) :
   RCLike.re ((Y * Yᴴ) j j) = ∑ i, ‖Y j i‖ ^ 2 := by
 rw [Matrix.mul_apply, map_sum]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj]
 simp
lemma re_conjTranspose_mul_apply_self (Y : Matrix κ ι 𝕜) (i : ι) :
   RCLike.re ((Yᴴ * Y) i i) = ∑ j, ‖Y j i‖ ^ 2 := by
 rw [Matrix.mul_apply, map_sum]
 refine Finset.sum_congr rfl fun j _ => ?_
 rw [conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
 simp
lemma re_mul_diagonal_mul_conjTranspose_apply (Y : Matrix κ ι 𝕜) (d : ι → ℝ) (j : κ) :
   RCLike.re ((Y * (diagonal (RCLike.ofReal ∘ d) : Matrix ι ι 𝕜) * Yᴴ : Matrix κ κ 𝕜) j j)
     = ∑ i, ‖Y j i‖ ^ 2 * d i := by
 rw [Matrix.mul_apply, map_sum]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [mul_diagonal, conjTranspose_apply, Function.comp_apply, RCLike.star_def,
   show Y j i * (d i : 𝕜) * starRingEnd 𝕜 (Y j i) = (d i : 𝕜) * (Y j i * starRingEnd 𝕜 (Y j i))
     by ring,
   RCLike.mul_conj,
   show ((d i : 𝕜) * ((‖Y j i‖ : 𝕜) ^ 2) : 𝕜) = ((‖Y j i‖ ^ 2 * d i : ℝ) : 𝕜) by push_cast; ring,
   RCLike.ofReal_re]
lemma sum_normSq_col_eigenvectorUnitary {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (i : ι) :
   ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 = 1 := by
 have h := re_conjTranspose_mul_apply_self (hM.eigenvectorUnitary : Matrix ι ι 𝕜) i
 rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2] at h
 simpa using h.symm
end Entries
section Mix
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def compressWeight {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
 ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
lemma compressWeight_le_one {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
   (hg : Function.Injective g) (i : ι) : compressWeight hM g i ≤ 1 := by
 unfold compressWeight
 calc ∑ j, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (g j) i‖ ^ 2
     = ∑ k ∈ univ.image g, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
       (Finset.sum_image (f := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2)
         (s := univ) (g := g) hg.injOn).symm
   _ ≤ ∑ k, ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) k i‖ ^ 2 :=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
   _ = 1 := sum_normSq_col_eigenvectorUnitary hM i
lemma sum_compressWeight_fiberwise {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (β : ι → κ) (i : ι) :
   ∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i = 1 := by
 unfold compressWeight
 have h : ∀ b : κ, ∑ j : (univ.filter fun i => β i = b),
     ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) (j : ι) i‖ ^ 2
       = ∑ j ∈ univ.filter (fun i => β i = b), ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2 :=
   fun b => Finset.sum_coe_sort (univ.filter fun i => β i = b)
     (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)
 simp only [h]
 rw [Finset.sum_fiberwise univ β (fun j => ‖(hM.eigenvectorUnitary : Matrix ι ι 𝕜) j i‖ ^ 2)]
 exact sum_normSq_col_eigenvectorUnitary hM i
theorem eigenvalues_submatrix_eq_mix {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
   (hg : Function.Injective g) :
   ∃ S : κ → ι → ℝ, (∀ j i, 0 ≤ S j i) ∧ (∀ j, ∑ i, S j i = 1)
     ∧ (∀ i, ∑ j, S j i = compressWeight hM g i)
     ∧ ∀ j, (hM.submatrix g).eigenvalues j = ∑ i, S j i * hM.eigenvalues i := by
 set U : Matrix ι ι 𝕜 := (hM.eigenvectorUnitary : Matrix ι ι 𝕜) with hUdef
 have hP : (M.submatrix g g).IsHermitian := hM.submatrix g
 set V : Matrix κ κ 𝕜 := (hP.eigenvectorUnitary : Matrix κ κ 𝕜) with hVdef
 set Ug : Matrix κ ι 𝕜 := U.submatrix g id with hUgdef
 set Y : Matrix κ ι 𝕜 := star V * Ug with hYdef
 have hUU : U * star U = 1 := Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
 have hVsV : star V * V = 1 := Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
 have hVVs : V * star V = 1 := Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2
 have hM' : M = U * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * star U := by
   conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
 have hUgUg : Ug * Ugᴴ = 1 := by
   rw [hUgdef, conjTranspose_submatrix, ← star_eq_conjTranspose,
     ← Matrix.submatrix_mul _ _ g id g Function.bijective_id, hUU, submatrix_one _ hg]
 have hPsub : M.submatrix g g = Ug * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Ugᴴ := by
   conv_lhs => rw [hM']
   rw [Matrix.submatrix_mul _ _ g id g Function.bijective_id,
     Matrix.submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id, hUgdef,
     conjTranspose_submatrix, star_eq_conjTranspose]
 have hdiag0 : diagonal (RCLike.ofReal ∘ hP.eigenvalues) = star V * M.submatrix g g * V := by
   rw [← hP.conjStarAlgAut_star_eigenvectorUnitary, Unitary.conjStarAlgAut_star_apply]
 have hdiag : diagonal (RCLike.ofReal ∘ hP.eigenvalues)
     = Y * (diagonal (RCLike.ofReal ∘ hM.eigenvalues) : Matrix ι ι 𝕜) * Yᴴ := by
   rw [hdiag0, hPsub, hYdef, conjTranspose_mul, star_eq_conjTranspose V,
     conjTranspose_conjTranspose]
   simp only [Matrix.mul_assoc]
 have hYY : Y * Yᴴ = 1 := by
   rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
     Matrix.mul_assoc, ← Matrix.mul_assoc Ug, hUgUg, Matrix.one_mul, ← star_eq_conjTranspose,
     hVsV]
 have hYtY : Yᴴ * Y = Ugᴴ * Ug := by
   rw [hYdef, conjTranspose_mul, star_eq_conjTranspose V, conjTranspose_conjTranspose,
     Matrix.mul_assoc, ← Matrix.mul_assoc V, ← star_eq_conjTranspose V, hVVs, Matrix.one_mul]
 refine ⟨fun j i => ‖Y j i‖ ^ 2, fun j i => by positivity, ?_, ?_, ?_⟩
 · intro j
   show ∑ i, ‖Y j i‖ ^ 2 = 1
   have h := re_mul_conjTranspose_apply_self Y j
   rw [hYY] at h
   simpa using h.symm
 · intro i
   show ∑ j, ‖Y j i‖ ^ 2 = compressWeight hM g i
   have h1 := re_conjTranspose_mul_apply_self Y i
   have h2 := re_conjTranspose_mul_apply_self Ug i
   rw [hYtY] at h1
   rw [← h1, h2]
   rfl
 · intro j
   show hP.eigenvalues j = ∑ i, ‖Y j i‖ ^ 2 * hM.eigenvalues i
   have h := re_mul_diagonal_mul_conjTranspose_apply Y hM.eigenvalues j
   rw [← hdiag, diagonal_apply_eq, Function.comp_apply, RCLike.ofReal_re] at h
   exact h
end Mix
section Pinching
variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
theorem sum_eigenvalues_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
   (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) :
   ∑ j, f ((hM.submatrix g).eigenvalues j)
     ≤ ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by
 obtain ⟨S, hS0, hSrow, hScol, hSeig⟩ := eigenvalues_submatrix_eq_mix hM hg
 calc ∑ j, f ((hM.submatrix g).eigenvalues j)
     = ∑ j, f (∑ i, S j i * hM.eigenvalues i) := by simp only [hSeig]
   _ ≤ ∑ j, ∑ i, S j i * f (hM.eigenvalues i) := by
       refine Finset.sum_le_sum fun j _ => ?_
       have h := hf.map_sum_le (t := Finset.univ) (w := S j) (p := hM.eigenvalues)
         (fun i _ => hS0 j i) (hSrow j) (fun i _ => Set.mem_univ _)
       simpa only [smul_eq_mul] using h
   _ = ∑ i, (∑ j, S j i) * f (hM.eigenvalues i) := by
       rw [Finset.sum_comm]; simp only [Finset.sum_mul]
   _ = ∑ i, compressWeight hM g i * f (hM.eigenvalues i) := by simp only [hScol]
theorem sum_eigenvalues_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
   (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
   ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
     ≤ ∑ i, f (hM.eigenvalues i) := by
 calc ∑ b, ∑ j, f ((hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)).eigenvalues j)
     ≤ ∑ b, ∑ i, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i
           * f (hM.eigenvalues i) :=
       Finset.sum_le_sum fun b _ => sum_eigenvalues_submatrix_le hM Subtype.val_injective hf
   _ = ∑ i, (∑ b, compressWeight hM (Subtype.val : (univ.filter fun i => β i = b) → ι) i)
           * f (hM.eigenvalues i) := by
       rw [Finset.sum_comm]; simp only [Finset.sum_mul]
   _ = ∑ i, f (hM.eigenvalues i) := by simp only [sum_compressWeight_fiberwise, one_mul]
theorem sum_eigenvalues_submatrix_le_of_nonneg {M : Matrix ι ι 𝕜} (hM : M.IsHermitian)
   {g : κ → ι} (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
   (hf0 : ∀ t, 0 ≤ f t) :
   ∑ j, f ((hM.submatrix g).eigenvalues j) ≤ ∑ i, f (hM.eigenvalues i) :=
 (sum_eigenvalues_submatrix_le hM hg hf).trans <| Finset.sum_le_sum fun i _ => by
   calc compressWeight hM g i * f (hM.eigenvalues i) ≤ 1 * f (hM.eigenvalues i) :=
         mul_le_mul_of_nonneg_right (compressWeight_le_one hM hg i) (hf0 _)
     _ = f (hM.eigenvalues i) := one_mul _
theorem rtrace_specMap_pinching_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {f : ℝ → ℝ}
   (hf : ConvexOn ℝ Set.univ f) (β : ι → κ) :
   ∑ b, rtrace (specMap (hM.submatrix (Subtype.val : (univ.filter fun i => β i = b) → ι)) f)
     ≤ rtrace (specMap hM f) := by
 simp only [rtrace_specMap]
 exact sum_eigenvalues_pinching_le hM hf β
theorem rtrace_specMap_submatrix_le {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) {g : κ → ι}
   (hg : Function.Injective g) {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : ∀ t, 0 ≤ f t) :
   rtrace (specMap (hM.submatrix g) f) ≤ rtrace (specMap hM f) := by
 rw [rtrace_specMap, rtrace_specMap]
 exact sum_eigenvalues_submatrix_le_of_nonneg hM hg hf hf0
end Pinching
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Filter Asymptotics Topology Real RHLinalg
open Zeta23 Zeta23.ThmD Zeta23.Assembly
namespace Zeta23Ext.Bridge
theorem seamA_mult2_defect {Z : ZeroConfig} {P : Params} {T : ℝ} (hT : 0 ≤ T)
   {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T)
   {D : ℝ}
   (hcore : 4 * rtrace (P.hat T (Z.Az P T)) - frobSq (P.hat T (Z.Az P T))
     - 2 * (Z.NIprime T : ℝ) + D ≤ (Z.s1 T : ℝ)) :
   4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
     - 3 * (NII Z T : ℝ)
     - θ₀ / (P.a T * P.L T)
         * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
     + D ≤ Z.N0s T (2 * T) := by
 obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
 have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
   rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
 have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
 have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
   (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
 have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
   exact_mod_cast s1_le Z hT
 have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
   exact_mod_cast NIprime_eq Z hT
 rw [hNI] at hcore
 linarith [hcore, hpert, hs1]
theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
   (aT bT JT trG trG2 : ℝ → ℝ)
   (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
   {c : ℝ} (hc0 : 0 < c)
   (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
   (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
   (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (AMW.atAM P T) T (θ₀ T))
   (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
   (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
   (hGzGp : ∀ᶠ T in atTop, Z.Gz (AMW.atAM P T) T = (AMW.atAM P T).Gp T)
   (hId : ∀ᶠ T in atTop, (AMW.atAM P T).trGtilde T = trG T ∧ (AMW.atAM P T).trGtildeSq T = trG2 T ∧
     (AMW.atAM P T).a T = aT T)
   (hcalE : Tendsto P.calE atTop (𝓝 0))
   (D : ℝ → ℝ)
   (hcore : ∀ᶠ T in atTop,
     4 * rtrace ((AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T))
       - frobSq ((AMW.atAM P T).hat T (Z.Az (AMW.atAM P T) T))
       - 2 * (Z.NIprime T : ℝ) + D T ≤ (Z.s1 T : ℝ)) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) + D T ≤ (Z.N0s T (2 * T) : ℝ) := by
 have hlam0 := hP.lam_pos
 have hlam1 : P.lam ≤ 1 := hP.lam_le_one
 obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
 obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
 obtain ⟨Cθ, hθ⟩ := hθ₀
 obtain ⟨CII, hII⟩ := hNII
 set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
 set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
 set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
 set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
 set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
 set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
     + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
 have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
 have hmain : ∀ᶠ T in atTop,
     (2 - c⁻¹) * N T - err T ≤ (Z.N0s T (2 * T) : ℝ) - D T := by
   filter_upwards [hcore, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
     eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
     eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
     with T hcoreT hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
   obtain ⟨hidtr, hidfr, hida⟩ := hid
   have hapos' : 0 < aT T := by linarith [ha2.1]
   have haposD : 0 < (AMW.atAM P T).a T := by rw [hida]; exact hapos'
   have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
   have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT
   have hrt : rtrace ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T)) = (aT T * P.L T)⁻¹ * trG T := by
     rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
   have hfr : frobSq ((AMW.atAM P T).hat T (Z.Gz (AMW.atAM P T) T))
       = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
     rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
   have haL : (AMW.atAM P T).a T * (AMW.atAM P T).L T = aT T * P.L T := by rw [hida]; rfl
   rw [hrt, hfr, haL] at hA
   have hA' : 4 * ((aT T * P.L T)⁻¹ * trG T) - ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
       - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
       - θ₀ T / (aT T * P.L T)
           * (4 + 2 * Real.sqrt (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + θ₀ T / (aT T * P.L T))
       ≤ (Z.N0s T (2 * T) : ℝ) - D T := by linarith [hA]
   have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
     trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
   have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
     have h := hfr2 T hT₂
     simp only at h
     have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
       rw [← mul_assoc] at h
       exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
     have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
       rw [inv_pow, div_eq_inv_mul]
     rw [e]; simp only [hR₂]; linarith
   have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
   have h := N0star_lower_c hB₀ hA' htr hfrb
   have hN0 : 0 ≤ N T := Nat.cast_nonneg _
   have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
     have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
     linarith [h1]
   simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
   linarith
 have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
 have o1 : R₁ =o[atTop] N := by
   have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
     refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
     filter_upwards [ha] with T ha2
     rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
     rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
   have := isLittleO_of_bdd_mul hbd
     (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
   exact this.congr_left fun T => by simp only [hR₁]; ring
 have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
   have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
   filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
     hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
   exact ⟨h1, h2⟩
 have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
   refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
   filter_upwards [hcinv_bd] with T h
   rw [abs_of_nonneg h.1]; exact h.2
 have o2 : R₂ =o[atTop] N := by
   have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
     simpa using hcalE.const_mul C₂
   have i1 : (fun T => cinv T * N T) =O[atTop] N := by
     have := hcinvO.mul (isBigO_refl N atTop)
     simpa using this
   have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
   refine (this.congr_left fun T => ?_).congr_right fun T => by simp
   simp only [hR₂]
 have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
   have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
     refine IsBigO.of_bound CII ?_
     filter_upwards [hII, eventually_l_pos] with T h hl
     rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
       abs_of_nonneg (by positivity)]
     simpa [mul_assoc] using h
   exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
 have o4 : Tendsto B atTop (𝓝 0) := by
   have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
     simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
   refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
   · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
     have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
     exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
   · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
       with T hTl ha2 hl hθT hT0
     have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
     have hapos' : 0 < aT T := by linarith [ha2.1]
     have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
     simp only [hBdef]
     rw [div_le_iff₀ (mul_pos hapos' hLpos)]
     calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
       _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
       _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
       _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
         have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
             = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
         rw [this]; gcongr; exact ha2.1
 have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
   (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
 have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
   refine isLittleO_of_tendsto_zero_mul ?_
   have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
     simpa using hcinv_to.sub_const c⁻¹
   simpa using this.abs
 have herr_o : err =o[atTop] N := o5.add o6
 have hfin := eps_form_of_isLittleO (lower := fun T => (Z.N0s T (2 * T) : ℝ) - D T) hmain
   (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
 intro ε hε
 obtain ⟨T₀, hT₀⟩ := hfin ε hε
 filter_upwards [eventually_ge_atTop T₀] with T hT
 have := hT₀ T hT
 simp only [hNdef] at this
 linarith
end Zeta23Ext.Bridge
end
set_option linter.all false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace Zeta23Ext.Bridge
open Classical
section GramEntry
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
lemma bdata_v_eq (hreal : PhiHatReal T P) {y : ZI Z T} (hy : (y : ℂ).re = 1 / 2) (k : Fin (P.d T)) :
   (bdata Z P T).v y k = (P.phiHatR T ((y : ℂ).im - P.tau T k) : ℂ) := by
 simp only [bdata, blockData, mkData_v, evalVec]
 rw [gammaOf_of_re_eq_half hy, ← Complex.ofReal_sub, hreal]
lemma gram_apply (hreal : PhiHatReal T P) (hc : 0 ≤ aL2 P T) (z z' : retained Z P T) :
   gram Z P T z z' =
     (((aL2 P T)⁻¹ * ∑ k : Fin (P.d T),
       P.phiHatR T ((z.1 : ℂ).im - P.tau T k) * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℝ) : ℂ) := by
 have hz := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z.2)
 have hz' := re_eq_half_of_mem_S₁ Z P T (mem_S₁_of_mem_retained Z P T z'.2)
 have hsq : (Real.sqrt (aL2 P T) : ℂ) * (Real.sqrt (aL2 P T) : ℂ) = (aL2 P T : ℂ) := by
   rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc]
 have hentry : ∀ a b : (bdata Z P T).S₁, gramS₁ (bdata Z P T) (aL2 P T) a b
     = ∑ k, star (Vsimple (bdata Z P T) (aL2 P T) k a) * Vsimple (bdata Z P T) (aL2 P T) k b := by
   intro a b
   simp only [gramS₁, Matrix.mul_apply, Matrix.conjTranspose_apply]
 unfold gram
 rw [Matrix.submatrix_apply, hentry]
 have e : ∀ k : Fin (P.d T),
     star (Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z))
       * Vsimple (bdata Z P T) (aL2 P T) k (toS₁ Z P T z')
     = (((aL2 P T)⁻¹ * (P.phiHatR T ((z.1 : ℂ).im - P.tau T k)
         * P.phiHatR T ((z'.1 : ℂ).im - P.tau T k)) : ℝ) : ℂ) := by
   intro k
   have h1 : (bdata Z P T).v (toS₁ Z P T z) k = (P.phiHatR T ((z.1 : ℂ).im - P.tau T k) : ℂ) :=
     bdata_v_eq Z P T hreal hz k
   have h2 : (bdata Z P T).v (toS₁ Z P T z') k = (P.phiHatR T ((z'.1 : ℂ).im - P.tau T k) : ℂ) :=
     bdata_v_eq Z P T hreal hz' k
   simp only [Vsimple]
   rw [h1, h2]
   simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
   rw [div_mul_div_comm, hsq]
   push_cast
   ring
 simp_rw [e]
 rw [← Complex.ofReal_sum, Finset.mul_sum]
end GramEntry
section Window
@[simp] lemma atAM_L (P : Params) (T : ℝ) : (AMW.atAM P T).L = P.L := rfl
variable {P : Params} (hP : P.Valid) (T : ℝ)
include hP
lemma atAM_phiHatR_eq : (AMW.atAM P T).phiHatR T = AdmWindow.vHatR (AMW.WAM P T) :=
 AMW.atW_phiHatR T hP (AMW.WAM_even P T)
lemma phiHatReal_atAM : PhiHatReal T (AMW.atAM P T) := fun r => GzGp.phiHat_ofReal _ T r
end Window
section Tail
lemma Wfun_le_of_L_le {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
   (hF : PrimeSide.LocalHypsCoreW c p F) {Δ : ℝ} (hΔ : p.L ≤ Δ) :
   PrimeSide.Wfun c p Δ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 := by
 have h8 := hF.eight_le_L
 have hL : 0 < p.L := hF.L_pos
 have hΔ0 : 0 < Δ := lt_of_lt_of_le hL hΔ
 have hw : 0 < p.w := by linarith [hF.one_le_w]
 have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
 set K : ℝ := (c / p.w) ^ 2 with hK
 have hK0 : 0 ≤ K := sq_nonneg _
 have hπ := Real.pi_pos
 have hψ : PrimeSide.psiA c p Δ ^ 2 ≤ K / Δ ^ 4 := by
   have h1 : PrimeSide.psiA c p Δ ≤ c / (p.w * Δ ^ 2) := PrimeSide.psiA_le_div_sq hΔ0.ne'
   calc PrimeSide.psiA c p Δ ^ 2 ≤ (c / (p.w * Δ ^ 2)) ^ 2 :=
         pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF Δ) h1 2
     _ = K / Δ ^ 4 := by rw [hK]; field_simp
 have hint : ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2 ≤ K / (3 * Δ ^ 3) :=
   PrimeSide.setIntegral_psiA_sq_Ioi_le_div hF hΔ0
 have hh : (p.h)⁻¹ = p.L / (2 * Real.pi) := by
   unfold PrimeSide.Setting.h; rw [inv_div]
 have hhpos : 0 ≤ (p.h)⁻¹ := by rw [hh]; positivity
 have hΔ4 : p.L ^ 2 ≤ Δ ^ 4 := by
   have : p.L ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hL.le hΔ 2
   have h2 : (1 : ℝ) ≤ Δ ^ 2 := by nlinarith
   calc p.L ^ 2 ≤ Δ ^ 2 := this
     _ = Δ ^ 2 * 1 := (mul_one _).symm
     _ ≤ Δ ^ 2 * Δ ^ 2 := by gcongr
     _ = Δ ^ 4 := by ring
 have hA : K / Δ ^ 4 ≤ K / p.L ^ 2 :=
   div_le_div_of_nonneg_left hK0 (by positivity) hΔ4
 have hB : (p.h)⁻¹ * (K / (3 * Δ ^ 3)) ≤ K / p.L ^ 2 := by
   rw [hh]
   have e : p.L / (2 * Real.pi) * (K / (3 * Δ ^ 3)) = K * (p.L / (6 * Real.pi * Δ ^ 3)) := by
     field_simp; ring
   rw [e]
   have hΔ3 : p.L ^ 3 ≤ Δ ^ 3 := pow_le_pow_left₀ hL.le hΔ 3
   have h3 : p.L / (6 * Real.pi * Δ ^ 3) ≤ 1 / p.L ^ 2 := by
     rw [div_le_div_iff₀ (by positivity) (by positivity)]
     have : p.L * p.L ^ 2 = p.L ^ 3 := by ring
     rw [this]
     nlinarith [Real.pi_gt_three, pow_pos hΔ0 3]
   calc K * (p.L / (6 * Real.pi * Δ ^ 3)) ≤ K * (1 / p.L ^ 2) :=
         mul_le_mul_of_nonneg_left h3 hK0
     _ = K / p.L ^ 2 := by ring
 unfold PrimeSide.Wfun
 calc PrimeSide.psiA c p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, PrimeSide.psiA c p r ^ 2
     ≤ K / Δ ^ 4 + (p.h)⁻¹ * (K / (3 * Δ ^ 3)) := by
       gcongr
   _ ≤ K / p.L ^ 2 + K / p.L ^ 2 := add_le_add hA hB
   _ = 2 * K / p.L ^ 2 := by ring
lemma rho_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
   (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ : ℝ}
   (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ) :
   PrimeSide.rho p F τ ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
 have hL : 0 < p.L := hF.L_pos
 have hτ : τ ∈ Set.Icc p.T (2 * p.T) := ⟨by linarith, by linarith⟩
 have hmaj := PrimeSide.rho_le_majorant hF hT hτ
 have hW1 := Wfun_le_of_L_le hF h1
 have hW2 := Wfun_le_of_L_le hF h2
 have hψ : PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / p.w) ^ 2 / p.L ^ 2 := by
   have hΔ0 : 0 < p.tau p.d - τ := lt_of_lt_of_le hL h3
   have hw : 0 < p.w := by linarith [hF.one_le_w]
   have hc : 0 ≤ c := by linarith [hF.four_le_cϱ]
   have hb : PrimeSide.psiA c p (p.tau p.d - τ) ≤ c / (p.w * (p.tau p.d - τ) ^ 2) :=
     PrimeSide.psiA_le_div_sq hΔ0.ne'
   have hΔ4 : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 4 := by
     have h8 := hF.eight_le_L
     have : p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := pow_le_pow_left₀ hL.le h3 2
     have h2' : (1 : ℝ) ≤ (p.tau p.d - τ) ^ 2 := by nlinarith
     calc p.L ^ 2 ≤ (p.tau p.d - τ) ^ 2 := this
       _ = (p.tau p.d - τ) ^ 2 * 1 := (mul_one _).symm
       _ ≤ (p.tau p.d - τ) ^ 2 * (p.tau p.d - τ) ^ 2 := by gcongr
       _ = (p.tau p.d - τ) ^ 4 := by ring
   calc PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 ≤ (c / (p.w * (p.tau p.d - τ) ^ 2)) ^ 2 :=
         pow_le_pow_left₀ (PrimeSide.psiA_nonneg_of hF _) hb 2
     _ = (c / p.w) ^ 2 / (p.tau p.d - τ) ^ 4 := by field_simp
     _ ≤ (c / p.w) ^ 2 / p.L ^ 2 :=
         div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hΔ4
 calc PrimeSide.rho p F τ
     ≤ PrimeSide.Wfun c p (τ - p.T) + PrimeSide.Wfun c p (2 * p.T - τ)
         + PrimeSide.psiA c p (p.tau p.d - τ) ^ 2 := hmaj
   _ ≤ 2 * (c / p.w) ^ 2 / p.L ^ 2 + 2 * (c / p.w) ^ 2 / p.L ^ 2 + (c / p.w) ^ 2 / p.L ^ 2 :=
       add_le_add (add_le_add hW1 hW2) hψ
   _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring
lemma abs_Kinf_sub_Kfun_le_of_far {c : ℝ} {p : PrimeSide.Setting} {F : PrimeSide.LocalFun}
   (hF : PrimeSide.LocalHypsCoreW c p F) (hT : 0 < p.T) {τ τ' : ℝ}
   (h1 : p.L ≤ τ - p.T) (h2 : p.L ≤ 2 * p.T - τ) (h3 : p.L ≤ p.tau p.d - τ)
   (h1' : p.L ≤ τ' - p.T) (h2' : p.L ≤ 2 * p.T - τ') (h3' : p.L ≤ p.tau p.d - τ') :
   |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'| ≤ 5 * (c / p.w) ^ 2 / p.L ^ 2 := by
 have h := PrimeSide.abs_Kinf_sub_Kfun_le hF τ τ' one_pos
 have hρ := rho_le_of_far hF hT h1 h2 h3
 have hρ' := rho_le_of_far hF hT h1' h2' h3'
 calc |PrimeSide.Kinf p F τ τ' - PrimeSide.Kfun p F τ τ'|
     ≤ (1 * PrimeSide.rho p F τ + PrimeSide.rho p F τ' / 1) / 2 := h
   _ ≤ (1 * (5 * (c / p.w) ^ 2 / p.L ^ 2) + 5 * (c / p.w) ^ 2 / p.L ^ 2 / 1) / 2 := by
       gcongr
   _ = 5 * (c / p.w) ^ 2 / p.L ^ 2 := by ring
end Tail
section Limit
lemma Kfun_zero_pos : 0 < Kfun 0 := AMW.KfunAM_zero_pos
lemma abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 := AMW.abs_KfunAM_le x
lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ) :
   (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
 unfold paperFT
 have hexp : Continuous fun u : ℝ => Complex.exp (Complex.I * (r : ℂ) * (u : ℂ)) := by fun_prop
 have hint : Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
   refine hg.ofReal.mul_bdd (c := 1) hexp.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
   rw [Complex.norm_exp]
   simp
 rw [← integral_re_C hint]
 congr 1 with u
 have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
 rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
lemma integral_sW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
   ∫ u, AMW.sW L u * Real.cos (2 * Real.pi * x / L * u) = L / AMW.MAM * Kfun x := by
 set f : ℝ → ℝ := fun s => AMW.vAM s / AMW.MAM * Real.cos (2 * Real.pi * x * s) with hf
 have hind : ∀ u, AMW.sW L u * Real.cos (2 * Real.pi * x / L * u)
     = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
   intro u
   unfold AMW.sW
   by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
   · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
     simp only [AMW.hW]
     rw [show 2 * Real.pi * x / L * u = 2 * Real.pi * x * (u / L) by ring]
   · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
 simp_rw [hind]
 rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith), AMW.integral_scale (v := f) hL]
 have e : (fun s => f s) = fun s => AMW.vAM s * Real.cos (2 * Real.pi * x * s) / AMW.MAM := by
   funext s; simp only [hf]; ring
 rw [e, intervalIntegral.integral_div]
 unfold Kfun AMW.KfunAM
 ring
lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
   |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
 have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
 have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
   rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
 have hfi : Integrable fun u => f u * Real.cos (r * u) :=
   hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
 have hgi : Integrable fun u => g u * Real.cos (r * u) :=
   hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
 rw [← integral_sub hfi hgi]
 calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
     ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
   _ ≤ ∫ u, |f u - g u| := by
       refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
       rw [← sub_mul, abs_mul]
       exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
variable {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP h8
lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
   |AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) - P.L T / AMW.MAM * Kfun x| ≤ 2 * P.w := by
 have hW := AMW.admWindow_WAM hP T h8
 have hL := hW.L_pos
 have hw : 0 < P.w := hW.w_pos
 set r := 2 * Real.pi * x / P.L T with hr
 have hV : AdmWindow.VPhiR (AMW.WAM P T) r = ∫ u, AMW.WAM P T u ^ 2 * Real.cos (r * u) :=
   re_paperFT_ofReal (hW.integrable_pow two_pos) r
 have hS : ∫ u, AMW.sW (P.L T) u * Real.cos (r * u) = P.L T / AMW.MAM * Kfun x :=
   integral_sW_mul_cos hL x
 have hL1 : ∫ u, |AMW.WAM P T u ^ 2 - AMW.sW (P.L T) u| ≤ 2 * P.w :=
   AMW.integral_abs_phiWsq_sub_sharp hP.taper hw (by linarith)
 rw [hV, ← hS]
 exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) (AMW.sW_integrable _) r).trans hL1
lemma abs_aL_sub_L_mul_Kfun_zero_le :
   |(AMW.atAM P T).a T * P.L T - P.L T / AMW.MAM * Kfun 0| ≤ 2 * P.w := by
 have hW := AMW.admWindow_WAM hP T h8
 have h := abs_VPhiR_sub_L_mul_Kfun_le hP h8 0
 rw [mul_zero, zero_div, hW.VPhiR_zero] at h
 rw [AMW.atAM_a hP T]
 exact h
lemma abs_VPhiR_div_sub_kfun_le (h32 : 32 * P.w ≤ P.L T) (x : ℝ) :
   |AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) / ((AMW.atAM P T).a T * P.L T) - kfun x|
     ≤ 12 * P.w / P.L T := by
 have hW := AMW.admWindow_WAM hP T h8
 have hL := hW.L_pos
 have hw : 0 < P.w := hW.w_pos
 have hM := AMW.MAM_pos
 have ha : 1 / 2 ≤ (AMW.atAM P T).a T := (AMW.aAM_range_of hP h32).1
 have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP h8 x
 have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP h8
 have hK0 : 0 < Kfun 0 := Kfun_zero_pos
 have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
 set V := AdmWindow.VPhiR (AMW.WAM P T) (2 * Real.pi * x / P.L T) with hV
 set A := (AMW.atAM P T).a T * P.L T with hA
 set K := Kfun x with hK'
 set K0 := Kfun 0 with hK0'
 set c := P.L T / AMW.MAM with hc
 have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
 have hApos : 0 < A := by linarith
 have e : V / A - K / K0 = (V - c * K) / A + K * (c * K0 - A) / (A * K0) := by
   field_simp
   ring
 unfold kfun
 rw [e]
 have h2' : |c * K0 - A| ≤ 2 * P.w := by rw [abs_sub_comm]; exact h2
 calc |(V - c * K) / A + K * (c * K0 - A) / (A * K0)|
     ≤ |(V - c * K) / A| + |K * (c * K0 - A) / (A * K0)| := abs_add_le _ _
   _ = |V - c * K| / A + |K| * |c * K0 - A| / (A * K0) := by
       rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
   _ ≤ 2 * P.w / A + K0 * (2 * P.w) / (A * K0) := by gcongr
   _ = 4 * P.w / A := by field_simp; ring
   _ ≤ 12 * P.w / P.L T := by
       rw [div_le_div_iff₀ hApos hL]
       nlinarith
end Limit
section Assembly
lemma retained_far {Z : ZeroConfig} {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 ≤ T)
   {z : ZI Z T} (hz : z ∈ retained Z P T) :
   P.L T ≤ (z : ℂ).im - T ∧ P.L T ≤ 2 * T - (z : ℂ).im ∧ P.L T ≤ P.tau T (P.d T) - (z : ℂ).im := by
 obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hz
 unfold xnorm at h1 h2
 have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
 have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
 have hd : ((P.d T : ℕ) : ℝ) ≤ P.L T * T / (2 * Real.pi) := Nat.floor_le (by positivity)
 have h1' : 2 * Real.pi * P.L T ^ 2 ≤ P.L T * ((z : ℂ).im - T) := by
   have := (le_div_iff₀ hπ).mp h1; linarith
 have h2' : P.L T * ((z : ℂ).im - T) ≤ 2 * Real.pi * ((P.d T : ℝ) - P.L T ^ 2) := by
   have := (div_le_iff₀ hπ).mp h2; linarith
 have hd' : 2 * Real.pi * (P.d T : ℝ) ≤ P.L T * T := by
   have := (le_div_iff₀ hπ).mp hd; linarith
 have g1 : 2 * Real.pi * P.L T ≤ (z : ℂ).im - T := by
   have : P.L T * (2 * Real.pi * P.L T) ≤ P.L T * ((z : ℂ).im - T) := by nlinarith
   exact le_of_mul_le_mul_left this hL
 have g2 : 2 * Real.pi * P.L T ≤ 2 * T - (z : ℂ).im := by
   have : P.L T * ((z : ℂ).im - T) ≤ P.L T * (T - 2 * Real.pi * P.L T) := by nlinarith
   have := le_of_mul_le_mul_left this hL
   linarith
 have hL2 : P.L T ≤ 2 * Real.pi * P.L T := by nlinarith
 refine ⟨by linarith, by linarith, ?_⟩
 have htau : P.tau T (P.d T) = T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
   simp only [Params.tau, Params.hgrid, Int.cast_natCast]
 rw [htau]
 have e : T + (P.d T : ℝ) * (2 * Real.pi / P.L T) - (z : ℂ).im
     = (2 * Real.pi * (P.d T : ℝ) - P.L T * ((z : ℂ).im - T)) / P.L T := by
   field_simp
   ring
 rw [e, le_div_iff₀ hL]
 nlinarith
lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
   PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
     = ∑ k : Fin ((AMW.atAM P T).d T), (AMW.atAM P T).phiHatR T (γ - (AMW.atAM P T).tau T k)
         * (AMW.atAM P T).phiHatR T (γ' - (AMW.atAM P T).tau T k) := by
 rw [atAM_phiHatR_eq hP T]; rfl
lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
   PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
     = P.L T * AdmWindow.VPhiR (AMW.WAM P T) (γ - γ') := rfl
theorem gram_close_of {P : Params} (hP : P.Valid) {T : ℝ} (hT : 0 < T)
   (h8 : 8 * P.w ≤ P.L T) (h32 : 32 * P.w ≤ P.L T)
   (hF : PrimeSide.LocalHypsCoreW (AMW.cAMW P.ϱ) (P.toSetting T) (AMW.lfW P (AMW.WAM P) T))
   (Z : ZeroConfig) (z z' : retained Z (AMW.atAM P T) T) :
   ‖gram Z (AMW.atAM P T) T z z'
       - (kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z') : ℂ)‖
     ≤ 10 * (AMW.cAMW P.ϱ / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
 have hW := AMW.admWindow_WAM hP T h8
 have hL := hW.L_pos
 have ha : 1 / 2 ≤ (AMW.atAM P T).a T := (AMW.aAM_range_of hP h32).1
 have hc : 0 < aL2 (AMW.atAM P T) T := by
   unfold aL2; rw [atAM_L]; exact mul_pos (by linarith) (pow_pos hL 2)
 set K : ℝ := (AMW.cAMW P.ϱ / P.w) ^ 2 with hK
 have hK0 : 0 ≤ K := sq_nonneg _
 rw [gram_apply Z (AMW.atAM P T) T (phiHatReal_atAM hP T) hc.le z z', ← Complex.ofReal_sub,
   Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
 set γ : ℝ := (z.1 : ℂ).im with hγ
 set γ' : ℝ := (z'.1 : ℂ).im with hγ'
 obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := AMW.atAM P T) hL hT.le z.2
 obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := AMW.atAM P T) hL hT.le z'.2
 have htail : |PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'
     - PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
   abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'
 have hx : 2 * Real.pi * (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z') / P.L T
     = γ - γ' := by
   unfold xret xnorm
   rw [atAM_L]
   field_simp
   ring
 have hlim := abs_VPhiR_div_sub_kfun_le hP h8 h32
   (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')
 rw [hx] at hlim
 set A : ℝ := (AMW.atAM P T).a T with hA
 set V : ℝ := AdmWindow.VPhiR (AMW.WAM P T) (γ - γ') with hV
 set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' with hKf
 have hKinf : PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (AMW.WAM P) T) γ γ' = P.L T * V :=
   Kinf_eq T γ γ'
 rw [hKinf] at htail
 have haL2 : aL2 (AMW.atAM P T) T = A * P.L T ^ 2 := by unfold aL2; rw [atAM_L]
 rw [haL2]
 have hApos : 0 < A := by linarith
 have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')
     = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
       + (V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')) := by
   field_simp
   ring
 rw [hsplit]
 have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
   rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
   nlinarith [pow_pos hL 2]
 calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
       + (V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z'))|
     ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
       + |V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')| :=
         abs_add_le _ _
   _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
       + |V / (A * P.L T) - kfun (xret Z (AMW.atAM P T) T z - xret Z (AMW.atAM P T) T z')| := by
       rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
   _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
       gcongr
   _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
       field_simp
       ring
end Assembly
section Strips
variable (Z : ZeroConfig)
lemma window_union {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) :
   Z.window a c = Z.window a b ∪ Z.window b c := by
 ext ρ
 simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
 constructor
 · rintro ⟨hρ, ha, hc⟩
   rcases le_or_gt ρ.im b with hle | hgt
   · exact Or.inl ⟨hρ, ha, hle⟩
   · exact Or.inr ⟨hρ, hgt, hc⟩
 · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
   · exact ⟨hρ, ha, le_trans hb h2⟩
   · exact ⟨hρ, lt_of_le_of_lt h1 hb, hc⟩
lemma N_add {a b c : ℝ} (h1 : a ≤ b) (h2 : b ≤ c) : Z.N a c = Z.N a b + Z.N b c := by
 unfold ZeroConfig.N
 rw [window_union Z h1 h2]
 refine finsum_mem_union ?_ (Z.finite_window a b) (Z.finite_window b c)
 rw [Set.disjoint_left]
 rintro ρ ⟨_, _, hb⟩ ⟨_, hb', _⟩
 exact absurd hb (not_le.2 hb')
lemma N_mono {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) : Z.N a b ≤ Z.N c d := by
 unfold ZeroConfig.N
 have hsub : Z.window a b ⊆ Z.window c d := by
   rintro ρ ⟨hρ, h1, h2⟩
   exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩
 have hfab : (Z.window a b).Finite := Z.finite_window a b
 have hfcd : (Z.window c d).Finite := Z.finite_window c d
 rw [finsum_mem_eq_finite_toFinset_sum _ hfab, finsum_mem_eq_finite_toFinset_sum _ hfcd]
 apply Finset.sum_le_sum_of_subset
 intro ρ hρ
 rw [Set.Finite.mem_toFinset] at hρ ⊢
 exact hsub hρ
lemma ncard_window_le_N (a b : ℝ) : (Z.window a b).ncard ≤ Z.N a b := by
 unfold ZeroConfig.N
 have hfin : (Z.window a b).Finite := Z.finite_window a b
 rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Set.ncard_eq_toFinset_card _ hfin,
   Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro ρ hρ
 rw [Set.Finite.mem_toFinset] at hρ
 exact Z.one_le_mult ρ hρ.1
lemma N_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
   (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) (n : ℕ) :
   (Z.N a (a + n) : ℝ) ≤ n * A₀ * Real.log (|a| + n + 3) := by
 induction n with
 | zero =>
   simp only [Nat.cast_zero, add_zero, zero_mul]
   have : Z.N a a = 0 := by
     unfold ZeroConfig.N
     have : Z.window a a = ∅ := by
       ext ρ
       simp only [ZeroConfig.window, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
         iff_false]
       rintro ⟨_, h1, h2⟩; linarith
     rw [this, finsum_mem_empty]
   rw [this]; simp
 | succ n ih =>
   have hsplit : Z.N a (a + (n + 1 : ℕ)) = Z.N a (a + n) + Z.N (a + n) (a + n + 1) := by
     push_cast
     rw [← add_assoc]
     exact N_add Z (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]) (by linarith)
   rw [hsplit]
   push_cast
   have h1 := hloc (a + n)
   have hlogmono : Real.log (|a| + n + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
     Real.log_le_log (by positivity) (by linarith)
   have hlogmono' : Real.log (|a + n| + 3) ≤ Real.log (|a| + (n + 1) + 3) :=
     Real.log_le_log (by positivity) (by linarith [abs_add_le a (n : ℝ), abs_of_nonneg (n.cast_nonneg : (0:ℝ) ≤ n)])
   have hA : 0 ≤ A₀ := by linarith
   have hn : (0 : ℝ) ≤ n := n.cast_nonneg
   calc ((Z.N a (a + n) : ℕ) : ℝ) + ((Z.N (a + n) (a + n + 1) : ℕ) : ℝ)
       ≤ n * A₀ * Real.log (|a| + n + 3) + A₀ * Real.log (|a + n| + 3) := add_le_add ih h1
     _ ≤ n * A₀ * Real.log (|a| + (n + 1) + 3) + A₀ * Real.log (|a| + (n + 1) + 3) := by
         gcongr
     _ = (n + 1) * A₀ * Real.log (|a| + (n + 1) + 3) := by ring
lemma N_le_of_local_count_real {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
   (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (a : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
   (Z.N a (a + ℓ) : ℝ) ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by
 set n : ℕ := ⌈ℓ⌉₊ with hn
 have hn1 : ℓ ≤ n := Nat.le_ceil ℓ
 have hn2 : (n : ℝ) < ℓ + 1 := Nat.ceil_lt_add_one hℓ
 have hA : 0 ≤ A₀ := by linarith
 have hmono : (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := by
   exact_mod_cast N_mono Z le_rfl (by linarith)
 have hlog : Real.log (|a| + n + 3) ≤ Real.log (|a| + ℓ + 4) :=
   Real.log_le_log (by positivity) (by linarith)
 have hlog0 : 0 ≤ Real.log (|a| + n + 3) := Real.log_nonneg (by linarith [abs_nonneg a, (n.cast_nonneg : (0:ℝ) ≤ n)])
 calc (Z.N a (a + ℓ) : ℝ) ≤ Z.N a (a + n) := hmono
   _ ≤ n * A₀ * Real.log (|a| + n + 3) := N_le_of_local_count Z hA₀ hloc a n
   _ ≤ (ℓ + 1) * A₀ * Real.log (|a| + ℓ + 4) := by gcongr
end Strips
section StripInclusion
lemma N0s_le_card_retained_add (Z : ZeroConfig) (P : Params) (T : ℝ) (hL : 0 < P.L T) :
   (Z.N0s T (2 * T) : ℝ) ≤ (retained Z P T).card
     + Z.N T (T + 2 * Real.pi * P.L T)
     + Z.N (2 * T - (2 * Real.pi * P.L T + 2 * Real.pi / P.L T)) (2 * T) := by
 classical
 set ℓ : ℝ := 2 * Real.pi * P.L T with hℓ
 set ℓ' : ℝ := 2 * Real.pi * P.L T + 2 * Real.pi / P.L T with hℓ'
 set A : Set ℂ := Z.window T (2 * T) ∩ ZeroConfig.onLine ∩ Z.simple with hA
 set R : Finset ℂ := (retained Z P T).map (Function.Embedding.subtype _) with hR
 have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
 have hD0 : 0 ≤ D0 T := Real.sqrt_nonneg T
 have hsub : A ⊆ (↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T) := by
   rintro ρ ⟨⟨⟨hρc, hT1, hT2⟩, hre⟩, hm⟩
   have hre' : ρ.re = 1 / 2 := hre
   have hm' : Z.mult ρ = 1 := hm
   have hρZ : ρ ∈ ZI Z T := by
     rw [mem_ZI, mem_ZIprime_iff]
     exact ⟨hρc, by linarith, by linarith⟩
   set z : ZI Z T := ⟨ρ, hρZ⟩ with hz
   have hzS : z ∈ (bdata Z P T).S₁ := by
     simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and]
     exact ⟨(mkData_σ_eq_iff Z T _ _ z).mpr hre', hm'⟩
   by_cases hx : P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
   · left; left
     rw [Finset.mem_coe, hR, Finset.mem_map]
     exact ⟨z, Finset.mem_filter.mpr ⟨hzS, hx⟩, rfl⟩
   · rw [not_and_or] at hx
     rcases hx with hx | hx
     · left; right
       refine ⟨hρc, hT1, ?_⟩
       push Not at hx
       unfold xnorm at hx
       have h1 := (div_lt_iff₀ hπ).mp hx
       have : P.L T * (ρ.im - T) < P.L T * ℓ := by rw [hℓ]; nlinarith
       have := lt_of_mul_lt_mul_left this hL.le
       show ρ.im ≤ T + ℓ
       linarith
     · right
       refine ⟨hρc, ?_, hT2⟩
       push Not at hx
       unfold xnorm at hx
       have h1 := (lt_div_iff₀ hπ).mp hx
       have hd : P.L T * T / (2 * Real.pi) < (P.d T : ℝ) + 1 := Nat.lt_floor_add_one _
       have hd' := (div_lt_iff₀ hπ).mp hd
       have hLℓ' : P.L T * ℓ' = 2 * Real.pi * P.L T ^ 2 + 2 * Real.pi := by
         rw [hℓ']; field_simp
       have : P.L T * (2 * T - ℓ') < P.L T * ρ.im := by nlinarith
       exact lt_of_mul_lt_mul_left this hL.le
 have hfin : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).Finite :=
   ((R.finite_toSet).union (Z.finite_window _ _)).union (Z.finite_window _ _)
 have hN0s : Z.N0s T (2 * T) = A.ncard := rfl
 have hcard : ((↑R : Set ℂ).ncard : ℝ) = (retained Z P T).card := by
   rw [Set.ncard_coe_finset, hR, Finset.card_map]
 have hlo := ncard_window_le_N Z T (T + ℓ)
 have hhi := ncard_window_le_N Z (2 * T - ℓ') (2 * T)
 have hu : ((↑R : Set ℂ) ∪ Z.window T (T + ℓ) ∪ Z.window (2 * T - ℓ') (2 * T)).ncard
     ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
   (Set.ncard_union_le _ _).trans (by gcongr; exact Set.ncard_union_le _ _)
 have hle : A.ncard ≤ (↑R : Set ℂ).ncard + (Z.window T (T + ℓ)).ncard
     + (Z.window (2 * T - ℓ') (2 * T)).ncard :=
   (Set.ncard_le_ncard hsub hfin).trans hu
 rw [hN0s]
 calc (A.ncard : ℝ) ≤ ((↑R : Set ℂ).ncard : ℝ) + (Z.window T (T + ℓ)).ncard
       + (Z.window (2 * T - ℓ') (2 * T)).ncard := by exact_mod_cast hle
   _ ≤ (retained Z P T).card + Z.N T (T + ℓ) + Z.N (2 * T - ℓ') (2 * T) := by
       rw [hcard]
       have hlo' : ((Z.window T (T + ℓ)).ncard : ℝ) ≤ Z.N T (T + ℓ) := by exact_mod_cast hlo
       have hhi' : ((Z.window (2 * T - ℓ') (2 * T)).ncard : ℝ) ≤ Z.N (2 * T - ℓ') (2 * T) := by
         exact_mod_cast hhi
       linarith
end StripInclusion
section StripCount
lemma strips_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
   (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {T L : ℝ} (hT : 1 ≤ T)
   (hL1 : 1 ≤ L) (hLT : L ≤ T) (hlogT : Real.log T ≤ L + 2 * Real.pi) :
   (Z.N T (T + 2 * Real.pi * L) : ℝ) + Z.N (2 * T - (2 * Real.pi * L + 2 * Real.pi / L)) (2 * T)
     ≤ 1600 * A₀ * L ^ 2 := by
 have hπ := Real.pi_pos
 have hπ4 := Real.pi_lt_four
 have hπ3 := Real.pi_gt_three
 have hA : 0 ≤ A₀ := by linarith
 set ℓ : ℝ := 2 * Real.pi * L with hℓ
 set ℓ' : ℝ := 2 * Real.pi * L + 2 * Real.pi / L with hℓ'
 have hLpos : 0 < L := by linarith
 have hℓ0 : 0 ≤ ℓ := by positivity
 have h2πL : 2 * Real.pi / L ≤ 2 * Real.pi * L := by
   rw [div_le_iff₀ hLpos]; nlinarith
 have hℓ'0 : 0 ≤ ℓ' := by positivity
 have hℓ'le : ℓ' ≤ 4 * Real.pi * L := by rw [hℓ']; linarith
 have hℓle : ℓ ≤ ℓ' := by
   have : 0 ≤ 2 * Real.pi / L := by positivity
   rw [hℓ, hℓ']; linarith
 have h1 := N_le_of_local_count_real Z hA₀ hloc T hℓ0
 have h2 := N_le_of_local_count_real Z hA₀ hloc (2 * T - ℓ') hℓ'0
 rw [sub_add_cancel] at h2
 set M : ℝ := (6 + 8 * Real.pi) * T with hM
 have hM1 : |T| + ℓ + 4 ≤ M := by
   rw [abs_of_pos (by linarith), hM]; nlinarith
 have hM2 : |2 * T - ℓ'| + ℓ' + 4 ≤ M := by
   have : |2 * T - ℓ'| ≤ 2 * T + ℓ' := by
     rw [abs_le]; constructor <;> linarith
   rw [hM]; nlinarith
 have hlogM : Real.log M ≤ (6 + 10 * Real.pi) * L := by
   have hT0 : 0 < T := by linarith
   rw [hM, Real.log_mul (by positivity) hT0.ne']
   have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 6 + 8 * Real.pi)
   nlinarith
 have hlog1 : Real.log (|T| + ℓ + 4) ≤ (6 + 10 * Real.pi) * L :=
   (Real.log_le_log (by positivity) hM1).trans hlogM
 have hlog2 : Real.log (|2 * T - ℓ'| + ℓ' + 4) ≤ (6 + 10 * Real.pi) * L :=
   (Real.log_le_log (by positivity) hM2).trans hlogM
 have hcoef : ℓ' + 1 ≤ (4 * Real.pi + 1) * L := by nlinarith
 have hcoef' : ℓ + 1 ≤ (4 * Real.pi + 1) * L := by linarith
 have hb1 : (Z.N T (T + ℓ) : ℝ) ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
   refine h1.trans ?_
   have h0 : 0 ≤ Real.log (|T| + ℓ + 4) := Real.log_nonneg (by linarith [abs_nonneg T])
   gcongr
 have hb2 : (Z.N (2 * T - ℓ') (2 * T) : ℝ)
     ≤ (4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L) := by
   refine h2.trans ?_
   have h0 : 0 ≤ Real.log (|2 * T - ℓ'| + ℓ' + 4) :=
     Real.log_nonneg (by linarith [abs_nonneg (2 * T - ℓ')])
   gcongr
 have hL2 : 0 ≤ A₀ * L ^ 2 := by positivity
 have hconst : 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) ≤ 1600 := by nlinarith
 calc (Z.N T (T + ℓ) : ℝ) + Z.N (2 * T - ℓ') (2 * T)
     ≤ 2 * ((4 * Real.pi + 1) * L * A₀ * ((6 + 10 * Real.pi) * L)) := by linarith
   _ = 2 * ((4 * Real.pi + 1) * (6 + 10 * Real.pi)) * (A₀ * L ^ 2) := by ring
   _ ≤ 1600 * (A₀ * L ^ 2) := by
       gcongr
   _ = 1600 * A₀ * L ^ 2 := by ring
end StripCount
end Zeta23Ext.Bridge
end
set_option linter.all false
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide
namespace Zeta23Ext.Bridge
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
def multPart (c : ℝ) : Matrix d d ℂ :=
 ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)
lemma mem_S₂_σ {z : ι} (hz : z ∈ D.S₂) : D.σ z = z := by
 simp only [ZeroBlockData.S₂, mem_filter, mem_univ, true_and] at hz
 exact hz.1
lemma mem_S₁_σ {z : ι} (hz : z ∈ D.S₁) : D.σ z = z := by
 simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
 exact hz.1
lemma mem_S₁_m {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
 simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
 exact hz.2
lemma multPart_posSemidef {c : ℝ} (hc : 0 < c) : (multPart D c).PosSemidef := by
 unfold multPart
 refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
 have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
 simpa using this
lemma rank_multPart_le {c : ℝ} (hc : 0 < c) : (multPart D c).rank ≤ D.s₂ := by
 unfold multPart
 rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
 refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
 simp [ZeroBlockData.s₂]
lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
   P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
 ext k l
 simp only [P₁, Vsimple, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
   vecMulVec_apply, smul_eq_mul]
 rw [← Finset.sum_coe_sort D.S₁, mul_sum]
 refine sum_congr rfl fun z _ => ?_
 have hσ := mem_S₁_σ D z.2
 have hm := mem_S₁_m D z.2
 have hstar : star (D.v z l) = D.v z l := congrFun (D.star_v_of_onLine hσ) l
 rw [hm, star_div₀, hstar, Nat.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal]
 have hsq : ((Real.sqrt c : ℂ)) * (Real.sqrt c : ℂ) = (c : ℂ) := by
   rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
 rw [div_mul_div_comm, hsq, Complex.ofReal_inv, inv_mul_eq_div]
lemma Q'_eq_multPart_add_blockQ {c : ℝ} (hc : 0 < c) :
   Q' D c = multPart D c + D.blockQ c := by
 unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart multPart
 rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
 abel
theorem regroup_posIndex (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
   posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
 have hR := multPart_posSemidef D hc
 have hH : (multPart D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
 rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
 calc posIndex hH
     ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
   _ ≤ D.s₂ + Pr.p := by
       rw [posIndex_eq_rank_of_posSemidef hR]
       exact Nat.add_le_add (rank_multPart_le D hc) (D.posIndex_blockQ_le Pr hc)
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23Ext.StableRankTrace
namespace Zeta23Ext.Bridge
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
lemma Vsimple_col_le_one {c : ℝ} (hc : 0 < c)
   (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (z : D.S₁) :
   ∑ k, ‖Vsimple D c k z‖ ^ 2 ≤ 1 := by
 have hz : (z : ι) ∈ D.onLine := by
   have := z.2
   simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at this
   exact (D.mem_onLine).mpr this.1
 have hs : ∀ k, ‖Vsimple D c k z‖ ^ 2 = ‖D.v z k‖ ^ 2 / c := by
   intro k
   simp only [Vsimple]
   rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc), div_pow,
     Real.sq_sqrt hc.le]
 simp_rw [hs]
 rw [← Finset.sum_div, div_le_one hc]
 exact hPois z hz
theorem count_defect (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
   (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
   4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) - 2 * (D.Ncount : ℝ)
     + defect (gramS₁_isHermitian D c) ≤ (D.s₁ : ℝ) := by
 classical
 have hb := regroup_posIndex D Pr hc
 have h := stable_rank_trace (Vsimple D c) (Vsimple_col_le_one D hc hPois) (Q'_isHermitian D c) hb
 have e : Vsimple D c * (Vsimple D c)ᴴ + Q' D c = D.blockP c + D.blockQ c := P₁_add_Q' D c
 rw [e] at h
 have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
   exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
 have hcard : (Fintype.card D.S₁ : ℝ) = D.s₁ := by rw [Fintype.card_coe]; rfl
 have hdef : defect (gramS₁_isHermitian D c)
     = rtrace (specMap (isHermitian_conjTranspose_mul_self (Vsimple D c)) Psi) := rfl
 rw [hcard] at h
 push_cast at h
 linarith
end Zeta23Ext.Bridge
end
noncomputable section
open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace Zeta23Ext.Bridge
theorem tail_passage (Z : ZeroConfig) (H : PaperInputs Z)
   (h7 : ∀ᶠ T in atTop,
     4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
       - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
       - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ)) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     (AMW.HW - ε) * (Z.N T (2 * T) : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.N0s T (2 * T) : ℝ) := by
 set P : Params := paramsOf stdProfile 1 with hPdef
 have hP : P.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
 have hlam : P.lam = 1 := rfl
 have hLoc := AMW.localHypsCoreAM_eventually hP
 have hTr := AMW.tracesBoundsAM_concrete (Z := Z) hP H
 have hc : Tendsto (fun T => cRatio (P.lam1 T) ((AMW.concreteDataW P (AMW.WAM P) Z).aT T)
     ((AMW.concreteDataW P (AMW.WAM P) Z).bT T) ((AMW.concreteDataW P (AMW.WAM P) Z).JT T)) atTop
     (𝓝 (cRatio P.lam AMW.aInf AMW.bInf AMW.JInf)) := AMW.tendsto_cRatio_W hP
 have hc0 := AMW.cRatio_W_pos hP.lam_pos
 have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (AMW.concreteDataW P (AMW.WAM P) Z).aT T
     ∧ (AMW.concreteDataW P (AMW.WAM P) Z).aT T ≤ 1 :=
   (AMW.concreteFactsW hP H (AMW.admWindow_WAM hP) hLoc).ab_range.mono
     fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
 obtain ⟨θ₀, hTail, hθ₀⟩ := AMW.eventually_tailPackageAM Z H hP
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 have hNII := Tail.eventually_NII_le Z hA₀ hloc
 have hGzGp := AMW.eventually_GzGpAM Z H hP
 have hId : ∀ᶠ T in atTop,
     (AMW.atAM P T).trGtilde T = (AMW.concreteDataW P (AMW.WAM P) Z).trG T ∧
     (AMW.atAM P T).trGtildeSq T = (AMW.concreteDataW P (AMW.WAM P) Z).trG2 T ∧
     (AMW.atAM P T).a T = (AMW.concreteDataW P (AMW.WAM P) Z).aT T :=
   Eventually.of_forall fun T => AMW.atW_ident Z hP (AMW.WAM_even P) T
 have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
   (zero_le_one.trans hP.one_le_w)
 have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀ hTail hθ₀ hNII hGzGp hId hcalE
   (fun T => Dcirc Z (mtParams T) T) h7
 intro ε hε
 exact h ε hε
end Zeta23Ext.Bridge
end
noncomputable section
open Matrix RHLinalg Filter
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace Zeta23Ext.Bridge
open Classical
theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
       ≤ ((retained Z (mtParams T) T).card : ℝ) := by
 intro ε hε
 have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
 have hA0 : 0 < A₀ := by linarith
 have hπ := Real.pi_pos
 set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
 have hcpos : 0 < c := by positivity
 have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
   Real.isLittleO_log_id_atTop.def hcpos
 filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
   (tendsto_L hP).eventually_ge_atTop 1, hlittle,
   eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
 have hT0 : 0 < T := by linarith
 set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
 have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
   rw [hLdef]
   show 1 * Real.log (T / (2 * Real.pi)) = _
   rw [one_mul, Real.log_div hT0.ne' (by positivity)]
 have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
 have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
 have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
 have hLlogT : L ≤ Real.log T := by linarith
 have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
 have hLT : L ≤ T := by linarith
 have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
 have hlogc : Real.log T ≤ c * T := by
   have h := hlog
   simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
   exact h
 have hLpos : 0 < (mtParams T).L T := by show 0 < L; linarith
 have hincl := N0s_le_card_retained_add Z (mtParams T) T hLpos
 have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
 have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
   have e1 : (mtParams T).L T = L := rfl
   rw [e1] at hincl
   linarith
 have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
   have h := hRvM T hTT₀
   have hℓ₁ : L ≤ ell1 T := by
     show 1 * l T ≤ l T + 2 * Real.log 2 - 1
     have := Real.log_two_gt_d9
     linarith
   have h1 := (abs_le.mp h).1
   have h2 : C * Real.log T ≤ |C| * Real.log T :=
     mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
   have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
     rw [mul_div_right_comm]
     exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
   linarith
 have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
   have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
     have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
       have : L * L ≤ L * (c * T) := by
         have : L ≤ c * T := hLlogT.trans hlogc
         exact mul_le_mul_of_nonneg_left this (by linarith)
       nlinarith
     have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
       rw [hc]; field_simp
     linarith
   have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
     have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
       apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
       nlinarith
     have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
     have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
       rw [le_div_iff₀ (by positivity)]
       have hL0 : 0 ≤ L := by linarith
       nlinarith
     calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
       _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
       _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
       _ = ε * T * L / (4 * Real.pi) := by ring
   have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
     field_simp
     ring
   linarith
 have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
   have := mul_le_mul_of_nonneg_left hN hε.le
   nlinarith [hkey]
 linarith
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace
namespace Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma specMap_const_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
   specMap hA (fun _ => 1) = 1 := by
 unfold specMap
 simp
lemma specMap_sub_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
   specMap hA (fun t => t - 1) = A - 1 := by
 have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
 rw [h, specMap_sub, specMap_id, specMap_const_one]
lemma offDiagSqOn_le_frobSq_sub_one (A : Matrix ι ι ℂ) :
   offDiagSqOn A univ ≤ frobSq (A - 1) := by
 rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
 unfold offDiagSqOn
 refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
 split_ifs with h
 · positivity
 · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]
theorem block_defect_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
   min 1 (offDiagSqOn A univ) ≤ defect hA := by
 unfold defect
 rw [rtrace_specMap]
 by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
 ·
   have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
     sum_congr rfl fun i _ => by simp [Psi, hall i]
   have hfrob := frobSq_specMap hA (fun t => t - 1)
   rw [specMap_sub_one] at hfrob
   rw [hsum, ← hfrob]
   exact (min_le_right _ _).trans (offDiagSqOn_le_frobSq_sub_one A)
 ·
   push Not at hall
   obtain ⟨i, hi⟩ := hall
   refine (min_le_left _ _).trans ?_
   calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
         unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
     _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
         single_le_sum (fun j _ => Psi_nonneg (hA.eigenvalues j)) (mem_univ i)
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma sq_sub_two_mul_le_sq {a b δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b)
   (h : |b - a| ≤ δ) : a ^ 2 - 2 * δ ≤ b ^ 2 := by
 rw [abs_le] at h
 obtain ⟨h1, h2⟩ := h
 rcases le_or_gt a b with hab | hab
 · nlinarith
 · rcases le_or_gt δ a with hδa | hδa
   · nlinarith
   · nlinarith
lemma wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ} (h : ‖g - (kfun t : ℂ)‖ ≤ δ) :
   wfun t - 2 * δ ≤ ‖g‖ ^ 2 := by
 have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
 have htri : abs (‖g‖ - |kfun t|) ≤ δ := by
   rw [← hk]; exact (abs_norm_sub_norm_le g _).trans h
 have := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
 rw [sq_abs] at this
 exact this
lemma offDiagSqOn_submatrix (G : Matrix ι ι ℂ) (B : Finset ι) :
   offDiagSqOn (G.submatrix (Subtype.val : B → ι) Subtype.val) univ = offDiagSqOn G B := by
 unfold offDiagSqOn
 rw [← Finset.sum_coe_sort B]
 refine sum_congr rfl fun i _ => ?_
 rw [← Finset.sum_coe_sort B]
 refine sum_congr rfl fun j _ => ?_
 simp only [submatrix_apply, Subtype.ext_iff]
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem pinching_partition {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
   (κ : Type) [Fintype κ] [DecidableEq κ] (β : ι → κ) :
   ∑ b, blockDefect hM (univ.filter fun i => β i = b) ≤ defect hM := by
 unfold blockDefect defect
 exact rtrace_specMap_pinching_le hM Psi_convexOn β
theorem pinching_submatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
   {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (f : κ → ι) (hf : Function.Injective f) :
   defect (hM.submatrix f) ≤ defect hM := by
 unfold defect
 exact rtrace_specMap_submatrix_le hM hf Psi_convexOn Zeta23Ext.StableRankTrace.Psi_nonneg
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace Zeta23Ext.Bridge
section Abstract
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Abstract
section Analytic
open Classical
lemma spanOf_xret_le_d (Z : ZeroConfig) (P : Params) (T : ℝ) :
   spanOf (xret Z P T) univ ≤ (P.d T : ℝ) := by
 have hb : ∀ z : retained Z P T,
     P.L T ^ 2 ≤ xret Z P T z ∧ xret Z P T z ≤ (P.d T : ℝ) - P.L T ^ 2 :=
   fun z => (Finset.mem_filter.mp z.2).2
 unfold spanOf
 split_ifs with h
 · have h1 : (univ : Finset (retained Z P T)).sup' h (xret Z P T) ≤ (P.d T : ℝ) - P.L T ^ 2 :=
     sup'_le _ _ fun z _ => (hb z).2
   have h2 : P.L T ^ 2 ≤ (univ : Finset (retained Z P T)).inf' h (xret Z P T) :=
     le_inf' _ _ fun z _ => (hb z).1
   have : 0 ≤ P.L T ^ 2 := sq_nonneg _
   linarith
 · exact Nat.cast_nonneg _
theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     spanOf (xret Z (mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
 intro ε hε
 obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
 have hV : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
 have hLpos : ∀ᶠ T in atTop, 0 < (mtParams T).L T := (tendsto_L hV).eventually_gt_atTop 0
 set K : ℝ := max ((1 + ε) * C / ε) 0 with hK
 have hK0 : 0 ≤ K := le_max_right _ _
 have hc : (0 : ℝ) < 1 / (2 * Real.pi * (K + 1)) := by positivity
 have hlogT : ∀ᶠ T in atTop, ‖Real.log T‖ ≤ (1 / (2 * Real.pi * (K + 1))) * ‖id T‖ :=
   Real.isLittleO_log_id_atTop.def hc
 have hell : ∀ᶠ T in atTop, 1 ≤ ell1 T := by
   have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
     Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
   have h' : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1))
       atTop atTop := h.atTop_add tendsto_const_nhds
   exact (h'.eventually_ge_atTop 1).mono fun T hT => by unfold ell1 l; linarith
 filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * Real.pi), hLpos, hlogT, hell]
   with T hT₀ h2π hL hlog hel
 have hpi : 0 < 2 * Real.pi := by positivity
 have hT0 : 0 < T := lt_of_lt_of_le hpi h2π
 have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
 have hLg0 : 0 ≤ Real.log T := Real.log_nonneg hT1
 have hl0 : 0 ≤ l T := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
 have hN := abs_le.mp (hRvM T hT₀)
 have hLle : (mtParams T).L T ≤ l T := by
   show (paramsOf stdProfile 1).lam * l T ≤ l T
   exact mul_le_of_le_one_left hl0 hV.lam_le_one
 have hl_ell : l T ≤ ell1 T := by
   unfold ell1; linarith [Real.log_two_gt_d9]
 have hd : ((mtParams T).d T : ℝ) ≤ T / (2 * Real.pi) * ell1 T := by
   have h0 : 0 ≤ (mtParams T).L T * T / (2 * Real.pi) := by positivity
   calc ((mtParams T).d T : ℝ) ≤ (mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le h0
     _ = T / (2 * Real.pi) * (mtParams T).L T := by ring
     _ ≤ T / (2 * Real.pi) * ell1 T := by gcongr; exact hLle.trans hl_ell
 have hKA : K * Real.log T ≤ T / (2 * Real.pi) * ell1 T := by
   simp only [Real.norm_eq_abs, id, abs_of_nonneg hLg0, abs_of_pos hT0] at hlog
   have h1 : K * Real.log T ≤ K * (1 / (2 * Real.pi * (K + 1)) * T) :=
     mul_le_mul_of_nonneg_left hlog hK0
   have h2 : K * (1 / (2 * Real.pi * (K + 1)) * T) ≤ T / (2 * Real.pi) := by
     rw [show K * (1 / (2 * Real.pi * (K + 1)) * T) = T / (2 * Real.pi) * (K / (K + 1)) by
       field_simp]
     have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
     exact mul_le_of_le_one_right (by positivity) this
   have h3 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T :=
     le_mul_of_one_le_right (by positivity) hel
   linarith
 have h1 : (1 + ε) * C / ε * Real.log T ≤ T / (2 * Real.pi) * ell1 T :=
   (mul_le_mul_of_nonneg_right (le_max_left _ _) hLg0).trans hKA
 have h2 : (1 + ε) * C * Real.log T ≤ ε * (T / (2 * Real.pi) * ell1 T) := by
   have e : (1 + ε) * C * Real.log T = ε * ((1 + ε) * C / ε * Real.log T) := by
     field_simp
   rw [e]
   exact mul_le_mul_of_nonneg_left h1 hε.le
 calc spanOf (xret Z (mtParams T) T) univ ≤ ((mtParams T).d T : ℝ) := spanOf_xret_le_d Z _ T
   _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]
end Analytic
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
namespace Zeta23Ext.Bridge
open Classical
def P₀ : Params := paramsOf stdProfile 1
lemma P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
lemma eventually_L_pos : ∀ᶠ T in atTop, 0 < (mtParams T).L T :=
 (tendsto_L P₀_valid).eventually_gt_atTop 0
theorem eventually_h7 (Z : ZeroConfig) :
   ∀ᶠ T in atTop,
     4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
       - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
       - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
 filter_upwards [eventually_w8 P₀_valid, AMW.eventually_w32 P₀_valid] with T h8 h32
 set P := mtParams T with hP
 have hconj : PhiHatConj T P := phiHatConj
 have hL : 0 < P.L T := by
   change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
 have ha : 1 / 2 ≤ P.a T := (AMW.aAM_range_of P₀_valid h32).1
 have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
 have hPois : PoissonSq T P := AMW.poissonSqW P₀_valid (AMW.WAM_even P₀) (AMW.admWindow_WAM P₀_valid) h8
 have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
   (sum_normSq_v_le Z T P hconj phiHatReal hPois)
 have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
   pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
     (toS₁_injective Z P T)
 have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
   hat_Az_eq_hatP_add_hatQ Z T P hconj
 have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
   rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
 have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
   rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
 rw [hA, hN, hs]
 linarith [h7, hD]
end Zeta23Ext.Bridge
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace Zeta23Ext.BridgeW
open Zeta23Ext.Bridge
structure WCert (n : ℕ) where
 a : Fin n → Fin n → ℝ
 b : Fin (n - 1) → ℝ
variable {n : ℕ}
def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
 ∑ r, W.b r * g r
   + ∑ i : Fin n, ∑ j : Fin n,
       if (i : ℕ) < (j : ℕ) then W.a i j * wfun (ptsN n g j - ptsN n g i) else 0
def WCert.B (W : WCert n) : ℝ := ∑ r, W.b r
def WCert.spanMass (W : WCert n) (s : ℕ) : ℝ :=
 ∑ i : Fin n, ∑ j : Fin n,
   if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then W.a i j else 0
structure WCert.Adm (W : WCert n) : Prop where
 a_nonneg : ∀ i j, 0 ≤ W.a i j
 b_nonneg : ∀ r, 0 ≤ W.b r
 capacity : ∀ s : ℕ, W.spanMass s ≤ 2
lemma WCert.B_nonneg {W : WCert n} (hW : W.Adm) : 0 ≤ W.B :=
 sum_nonneg fun r _ => hW.b_nonneg r
lemma Fw_windowGaps (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
   Fw W (windowGaps n Y i)
     = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
       + ∑ a : Fin n, ∑ b : Fin n,
           if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
 unfold Fw
 have hq : (∑ a : Fin n, ∑ b : Fin n,
       if (a : ℕ) < (b : ℕ) then
         W.a a b * wfun (ptsN n (windowGaps n Y i) b - ptsN n (windowGaps n Y i) a) else 0)
     = ∑ a : Fin n, ∑ b : Fin n,
         if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
   refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
   rw [ptsN_windowGaps, ptsN_windowGaps,
     show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
 rw [hq]
 rfl
section BlockPressure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def sortedOn (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
 sortedExt (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))
def blkPress (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
 ∑ r : Fin (n - 1), b r * (sortedOn x B ((B.image x).card - (n - 1) + r) - sortedOn x B r)
end BlockPressure
end Zeta23Ext.BridgeW
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators
namespace Zeta23Ext.BridgeW
open Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma sum_gap_shift (Y : ℕ → ℝ) (r N : ℕ) :
   ∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r)) = Y (N + r) - Y r := by
 have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
 simp_rw [h]
 have := Finset.sum_range_sub (fun i => Y (i + r)) N
 simpa using this
lemma sortedOn_eq {x : ι → ℝ} {B : Finset ι} {m : ℕ} (hS : (B.image x).card = m) (k : ℕ) :
   sortedOn x B k = sortedExt (⇑((B.image x).orderEmbOfFin hS)) k := by
 unfold sortedOn sortedExt
 by_cases hk : k < (B.image x).card
 · have hk' : k < m := hS ▸ hk
   rw [dif_pos hk, dif_pos hk']
   set f : Fin (B.image x).card → ℝ := fun j => (B.image x).orderEmbOfFin hS ⟨j, hS ▸ j.2⟩
     with hf
   have hfs : ∀ j, f j ∈ B.image x := fun j => Finset.orderEmbOfFin_mem _ hS _
   have hmono : StrictMono f := by
     intro j j' hj
     exact ((B.image x).orderEmbOfFin hS).strictMono (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hj))
   have := Finset.orderEmbOfFin_unique rfl hfs hmono
   have h2 := congrFun this ⟨k, hk⟩
   simp only [hf] at h2
   rw [← h2]
 · have hk' : ¬ k < m := hS ▸ hk
   rw [dif_neg hk, dif_neg hk']
end Zeta23Ext.BridgeW
end
noncomputable section
set_option linter.unusedSectionVars false
open Finset Filter
open scoped BigOperators
open Zeta23 Zeta23.ThmD
namespace Zeta23Ext.BridgeW
open Zeta23Ext.Bridge
end Zeta23Ext.BridgeW
end
noncomputable section
open Filter
namespace AMW
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW
theorem N0simple_le_N0star' (T₁ T₂ : ℝ) : Zeta23.N0simple T₁ T₂ ≤ Zeta23.N0star T₁ T₂ := by
 refine Set.ncard_le_ncard Set.inter_subset_left ?_
 refine (Zeta23.zetaSeam.finite_window T₁ T₂).subset ?_
 rintro ρ ⟨⟨h1, h2, h3⟩, _⟩
 exact ⟨h1, h2, h3⟩
end AMW
end
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Zeta23Ext.BridgeW
open Zeta23Ext.Bridge
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma window_pairs_le_band {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
   (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
   ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
       (if (a : ℕ) < (b : ℕ) then
         W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
               - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
       else 0)
     ≤ ∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
         then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0) := by
 classical
 set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
 set Y := sortedExt y with hYdef
 have hm0 : 0 < m := by omega
 set T : Finset (ℕ × (Fin n × Fin n)) :=
   (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
   with hTdef
 set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
   W.a t.2.1 t.2.2 * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
 have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
     (if (a : ℕ) < (b : ℕ) then
       W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)
     = ∑ t ∈ T, f t := by
   rw [hTdef, sum_filter, sum_product]
   refine sum_congr rfl fun i _ => ?_
   exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
     W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)).symm
 rw [hLHS]
 set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
 set I := T.image φ with hIdef
 have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
   intro t ht
   simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
   exact ht
 have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
   intro q hq
   obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
   obtain ⟨h1, h2⟩ := hmem t ht
   have hb := t.2.2.2
   simp only [hφdef]
   omega
 rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]
 have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   set r := q.2 - q.1 with hrdef
   have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
       f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
     intro t ht
     rw [mem_filter] at ht
     obtain ⟨ht, hφt⟩ := ht
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
     have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
     simp only [hfdef]
     rw [e1, e2]
   rw [sum_congr rfl hconst, ← sum_mul]
   set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
   have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
     intro t ht t' ht' hee
     rw [mem_coe, mem_filter] at ht ht'
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
     have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
     simp only [hψdef] at hee
     have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
     have hi : t.1 = t'.1 := by omega
     exact Prod.ext hi hee
   have hsub : (T.filter (fun t => φ t = q)).image ψ
       ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
           (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
     intro p hp
     obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
     rw [mem_filter] at ht
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
     have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
     obtain ⟨-, hlt⟩ := hmem t ht.1
     rw [mem_filter, mem_product]
     refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
     simp only [hψdef]
     omega
   have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
     have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
         = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
       rw [sum_image hψinj]
     have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
         ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
             (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
       sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
     have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
             (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
         = W.spanMass r := by
       unfold WCert.spanMass
       rw [sum_filter, sum_product]
     rw [h1]
     exact h2.trans (h3 ▸ hW.capacity r)
   exact mul_le_mul_of_nonneg_right hmass (wfun_nonneg _)
 refine (sum_le_sum hfib).trans ?_
 set G : Fin m × Fin m → ℝ := fun r => if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
   then wfun (y r.1 - y r.2) else 0 with hGdef
 set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
 have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
   intro n h; simp only [htoFin, dif_pos h]
 set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
 set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
 have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   have hq1m : q.1 < m := by omega
   simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
     sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
   rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne, by omega, by omega⟩,
     wfun_sub_comm]
 have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   have hq1m : q.1 < m := by omega
   simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
     sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
   rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne', by omega, by omega⟩]
 have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
   rw [← sum_add_distrib]
   refine sum_congr rfl fun q hq => ?_
   rw [hG1 q hq, hG2 q hq]; ring
 have hinj₁ : Set.InjOn ψ₁ I := by
   intro q hq q' hq' h
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
   exact Prod.ext h.1 h.2
 have hinj₂ : Set.InjOn ψ₂ I := by
   intro q hq q' hq' h
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
   exact Prod.ext h.2 h.1
 have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
   rw [disjoint_left]
   intro r hr1 hr2
   obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
   obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
   omega
 have hGnn : ∀ r, 0 ≤ G r := by
   intro r; simp only [hGdef]; split_ifs
   · exact wfun_nonneg _
   · exact le_rfl
 rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
 exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r
theorem block_energy_band {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
   (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
   {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
   c * ((m : ℝ) - ((n : ℝ) - 1)) ≤ (∑ r : Fin m × Fin m,
       (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
         then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0))
     + blkPress W.b x univ := by
 classical
 set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
 have hymono : StrictMono y := ((univ.image x).orderEmbOfFin hS).strictMono
 set Y := sortedExt y with hYdef
 have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
 have hcastn : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
   rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
 have hwin : ∀ i ∈ range (m - (n - 1)), c ≤ Fw W (windowGaps n Y i) := by
   intro i hi
   rw [mem_range] at hi
   apply hCert
   intro j
   have hj := j.2
   have hlt : i + ((j : ℕ) + 1) < m := by omega
   exact sub_nonneg.mpr (sortedExt_mono hymono (by omega) hlt)
 have hsum : c * ((m : ℝ) - ((n : ℝ) - 1))
     ≤ ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n Y i) := by
   have h := sum_le_sum hwin
   rw [sum_const, card_range, nsmul_eq_mul] at h
   have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n : ℝ) - 1) := by
     rw [Nat.cast_sub (by omega : n - 1 ≤ m), hcastn]
   rw [hcast] at h
   linarith
 simp_rw [Fw_windowGaps] at hsum
 rw [sum_add_distrib] at hsum
 have hlin : ∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
     = blkPress W.b x univ := by
   rw [sum_comm]
   unfold blkPress
   rw [hS]
   refine sum_congr rfl fun r _ => ?_
   rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
 have hquad := window_pairs_le_band hn hm W hW x hx hS
 rw [← hydef, ← hYdef] at hquad
 linarith
def sRank (x : ι → ℝ) {m : ℕ} (hS : (univ.image x).card = m) (i : ι) : Fin m :=
 ((univ.image x).orderIsoOfFin hS).symm ⟨x i, mem_image_of_mem x (mem_univ i)⟩
lemma sRank_val (x : ι → ℝ) {m : ℕ} (hS : (univ.image x).card = m) (i : ι) :
   (univ.image x).orderEmbOfFin hS (sRank x hS i) = x i := by
 unfold sRank
 rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
lemma sRank_injective {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ} (hS : (univ.image x).card = m) :
   Function.Injective (sRank x hS) := by
 intro i j h
 apply hx
 rw [← sRank_val x hS i, ← sRank_val x hS j, h]
lemma sRank_bijective {x : ι → ℝ} (hx : Function.Injective x) {m : ℕ} (hS : (univ.image x).card = m)
   (hcard : Fintype.card ι = m) : Function.Bijective (sRank x hS) :=
 (Fintype.bijective_iff_injective_and_card _).mpr ⟨sRank_injective hx hS, by simp [hcard]⟩
end Zeta23Ext.BridgeW
end
noncomputable section
namespace AMW
open Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW
end AMW
end
namespace AMW.G
def DZ : ℕ := 1000000000000000
def ndivc (a b : ℕ) : ℕ := Nat.div (Nat.sub (Nat.add a b) 1) b
theorem DZ_pos : (0 : ℝ) < DZ := by norm_num [DZ]
theorem ndiv_le (a b : ℕ) (hb : 0 < b) : ((Nat.div a b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
 rw [le_div_iff₀ (by exact_mod_cast hb)]
 exact_mod_cast Nat.div_mul_le_self a b
theorem le_ndivc (a b : ℕ) (hb : 0 < b) : (a : ℝ) / b ≤ ((ndivc a b : ℕ) : ℝ) := by
 rw [div_le_iff₀ (by exact_mod_cast hb)]
 unfold ndivc
 have h1 : a + b - 1 = a + (b - 1) := by omega
 have h2 : a ≤ (a + (b - 1)) / b * b := by
   have := Nat.lt_div_mul_add (a := a + (b - 1)) hb
   have h3 : a + (b - 1) < (a + (b - 1)) / b * b + b := by
     have := Nat.lt_div_mul_add (a := a + (b - 1)) hb; linarith
   omega
 show (a : ℝ) ≤ ((Nat.div (Nat.sub (Nat.add a b) 1) b : ℕ) : ℝ) * b
 have e : Nat.div (Nat.sub (Nat.add a b) 1) b = (a + (b - 1)) / b := by
   rw [← h1]; rfl
 rw [e]; exact_mod_cast h2
structure SZ where
 (p n : ℕ)
namespace SZ
def v (a : SZ) : ℝ := (a.p : ℝ) - a.n
def ofN (m : ℕ) : SZ := ⟨m, 0⟩
def add (a b : SZ) : SZ := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
def sub (a b : SZ) : SZ := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
def neg (a : SZ) : SZ := ⟨a.n, a.p⟩
def mul (a b : SZ) : SZ := ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
def muln (m : ℕ) (a : SZ) : SZ := ⟨Nat.mul m a.p, Nat.mul m a.n⟩
def le (a b : SZ) : Bool := Nat.ble (Nat.add a.p b.n) (Nat.add b.p a.n)
def nonneg (a : SZ) : Bool := Nat.ble a.n a.p
def min (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) b a (a.le b)
def max (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) a b (a.le b)
def fl (a : SZ) (d : ℕ) : SZ :=
 Bool.rec (motive := fun _ => SZ) ⟨0, ndivc (Nat.sub a.n a.p) d⟩ ⟨Nat.div (Nat.sub a.p a.n) d, 0⟩ (Nat.ble a.n a.p)
def ce (a : SZ) (d : ℕ) : SZ :=
 Bool.rec (motive := fun _ => SZ) ⟨0, Nat.div (Nat.sub a.n a.p) d⟩ ⟨ndivc (Nat.sub a.p a.n) d, 0⟩ (Nat.ble a.n a.p)
@[simp] theorem v_ofN (m : ℕ) : (ofN m).v = m := by simp [v, ofN]
@[simp] theorem v_add (a b : SZ) : (a.add b).v = a.v + b.v := by
 simp only [v, add, Nat.add_eq]; push_cast; ring
@[simp] theorem v_sub (a b : SZ) : (a.sub b).v = a.v - b.v := by
 simp only [v, sub, Nat.add_eq]; push_cast; ring
@[simp] theorem v_neg (a : SZ) : a.neg.v = -a.v := by simp only [v, neg]; ring
@[simp] theorem v_mul (a b : SZ) : (a.mul b).v = a.v * b.v := by
 simp only [v, mul, Nat.add_eq, Nat.mul_eq]; push_cast; ring
@[simp] theorem v_muln (m : ℕ) (a : SZ) : (a.muln m).v = m * a.v := by
 simp only [v, muln, Nat.mul_eq]; push_cast; ring
theorem le_iff (a b : SZ) : a.le b = true ↔ a.v ≤ b.v := by
 simp only [le, Nat.ble_eq, Nat.add_eq, v]
 constructor
 · intro h; have : ((a.p + b.n : ℕ) : ℝ) ≤ ((b.p + a.n : ℕ) : ℝ) := by exact_mod_cast h
   push_cast at this; linarith
 · intro h; have : ((a.p + b.n : ℕ) : ℝ) ≤ ((b.p + a.n : ℕ) : ℝ) := by push_cast; linarith
   exact_mod_cast this
theorem nonneg_iff (a : SZ) : a.nonneg = true ↔ 0 ≤ a.v := by
 simp only [nonneg, Nat.ble_eq, v, sub_nonneg]; exact_mod_cast Iff.rfl
theorem v_min_le_left (a b : SZ) : (a.min b).v ≤ a.v := by
 unfold min; cases h : a.le b <;> simp only
 · have := (le_iff a b).not.mp (by simp [h]); linarith
 · exact le_rfl
theorem v_min_le_right (a b : SZ) : (a.min b).v ≤ b.v := by
 unfold min; cases h : a.le b <;> simp only
 · exact le_rfl
 · exact (le_iff a b).mp h
theorem le_v_max_left (a b : SZ) : a.v ≤ (a.max b).v := by
 unfold max; cases h : a.le b <;> simp only
 · exact le_rfl
 · exact (le_iff a b).mp h
theorem le_v_max_right (a b : SZ) : b.v ≤ (a.max b).v := by
 unfold max; cases h : a.le b <;> simp only
 · have := (le_iff a b).not.mp (by simp [h]); linarith
 · exact le_rfl
theorem v_fl_le (a : SZ) {d : ℕ} (hd : 0 < d) : (a.fl d).v ≤ a.v / d := by
 have hd' : (0 : ℝ) < d := by exact_mod_cast hd
 unfold fl
 cases h : Nat.ble a.n a.p <;> simp only [v]
 · have h : a.p < a.n := not_le.mp fun hle => by simp [Nat.ble_eq.mpr hle] at h
   have h1 := le_ndivc (Nat.sub a.n a.p) d hd
   have e : ((Nat.sub a.n a.p : ℕ) : ℝ) = (a.n : ℝ) - a.p := by
     rw [show Nat.sub a.n a.p = a.n - a.p from rfl, Nat.cast_sub h.le]
   rw [e] at h1
   have : (a.n : ℝ) / d - a.p / d ≤ ((ndivc (Nat.sub a.n a.p) d : ℕ) : ℝ) := by rw [← sub_div]; exact h1
   rw [sub_div]; push_cast; linarith
 · rw [Nat.ble_eq] at h
   have h1 := ndiv_le (Nat.sub a.p a.n) d hd
   have e : ((Nat.sub a.p a.n : ℕ) : ℝ) = (a.p : ℝ) - a.n := by
     rw [show Nat.sub a.p a.n = a.p - a.n from rfl, Nat.cast_sub h]
   rw [e] at h1
   push_cast; linarith
theorem le_v_ce (a : SZ) {d : ℕ} (hd : 0 < d) : a.v / d ≤ (a.ce d).v := by
 have hd' : (0 : ℝ) < d := by exact_mod_cast hd
 unfold ce
 cases h : Nat.ble a.n a.p <;> simp only [v]
 · have h : a.p < a.n := not_le.mp fun hle => by simp [Nat.ble_eq.mpr hle] at h
   have h1 := ndiv_le (Nat.sub a.n a.p) d hd
   have e : ((Nat.sub a.n a.p : ℕ) : ℝ) = (a.n : ℝ) - a.p := by
     rw [show Nat.sub a.n a.p = a.n - a.p from rfl, Nat.cast_sub h.le]
   rw [e] at h1
   have : ((Nat.div (Nat.sub a.n a.p) d : ℕ) : ℝ) ≤ (a.n : ℝ) / d - a.p / d := by rw [← sub_div]; exact h1
   rw [sub_div]; push_cast; linarith
 · rw [Nat.ble_eq] at h
   have h1 := le_ndivc (Nat.sub a.p a.n) d hd
   have e : ((Nat.sub a.p a.n : ℕ) : ℝ) = (a.p : ℝ) - a.n := by
     rw [show Nat.sub a.p a.n = a.p - a.n from rfl, Nat.cast_sub h]
   rw [e] at h1
   push_cast; linarith
end SZ
structure IV where
 (lo hi : SZ)
namespace IV
def Enc (I : IV) (a : ℝ) : Prop := I.lo.v / DZ ≤ a ∧ a ≤ I.hi.v / DZ
def ofN (a b : ℕ) : IV := ⟨⟨a, 0⟩, ⟨b, 0⟩⟩
def zero : IV := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
def add (I J : IV) : IV := ⟨I.lo.add J.lo, I.hi.add J.hi⟩
def sub (I J : IV) : IV := ⟨I.lo.sub J.hi, I.hi.sub J.lo⟩
def neg (I : IV) : IV := ⟨I.hi.neg, I.lo.neg⟩
def muln (m : ℕ) (I : IV) : IV := ⟨I.lo.muln m, I.hi.muln m⟩
def mul (I J : IV) : IV :=
 ⟨SZ.fl (SZ.min (SZ.min (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.min (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ,
  SZ.ce (SZ.max (SZ.max (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.max (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ⟩
def mulc (C I : IV) : IV :=
 ⟨SZ.fl (Bool.rec (motive := fun _ => SZ) (C.hi.mul I.lo) (C.lo.mul I.lo) I.lo.nonneg) DZ,
  SZ.ce (Bool.rec (motive := fun _ => SZ) (C.lo.mul I.hi) (C.hi.mul I.hi) I.hi.nonneg) DZ⟩
def divn (I : IV) (d : ℕ) : IV := ⟨I.lo.fl d, I.hi.ce d⟩
def divp (I : IV) (e0 e1 : ℕ) : IV :=
 ⟨Bool.rec (motive := fun _ => SZ) ((I.lo.muln DZ).fl e0) ((I.lo.muln DZ).fl e1) I.lo.nonneg,
  Bool.rec (motive := fun _ => SZ) ((I.hi.muln DZ).ce e1) ((I.hi.muln DZ).ce e0) I.hi.nonneg⟩
def scl (ng : Bool) (m : ℕ) (I : IV) : IV := Bool.rec (motive := fun _ => IV) (I.muln m) (I.muln m).neg ng
theorem enc_zero : zero.Enc 0 := by simp [Enc, zero, SZ.v]
theorem enc_add {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.add J).Enc (a + b) := by
 simp only [Enc, add, SZ.v_add, add_div] at *
 constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem enc_sub {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.sub J).Enc (a - b) := by
 simp only [Enc, sub, SZ.v_sub, sub_div] at *
 constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
theorem enc_neg {I : IV} {a : ℝ} (hI : I.Enc a) : I.neg.Enc (-a) := by
 simp only [Enc, neg, SZ.v_neg, neg_div] at *
 constructor <;> linarith [hI.1, hI.2]
theorem enc_muln {I : IV} {a : ℝ} (m : ℕ) (hI : I.Enc a) : (I.muln m).Enc (m * a) := by
 have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
 simp only [Enc, muln, SZ.v_muln] at *
 constructor
 · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hI.1 hm
 · rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hI.2 hm
theorem enc_scl {I : IV} {a : ℝ} (ng : Bool) (m : ℕ) (hI : I.Enc a) :
   (I.scl ng m).Enc ((if ng then -1 else 1) * m * a) := by
 cases ng
 · simp only [scl, Bool.false_eq_true, if_false, one_mul]; exact enc_muln m hI
 · simp only [scl, if_true]
   have := enc_neg (enc_muln m hI); rwa [show (-1 : ℝ) * m * a = -(m * a) by ring]
theorem mul_mem_corners {p P q Q x y : ℝ} (hx : p ≤ x ∧ x ≤ P) (hy : q ≤ y ∧ y ≤ Q) :
   min (min (p * q) (p * Q)) (min (P * q) (P * Q)) ≤ x * y ∧
     x * y ≤ max (max (p * q) (p * Q)) (max (P * q) (P * Q)) := by
 obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
 constructor
 · rcases le_total 0 y with hy0 | hy0
   · have h1 : p * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy0
     rcases le_total 0 p with hp | hp
     · have : p * q ≤ p * y := mul_le_mul_of_nonneg_left hy1 hp
       exact (min_le_left _ _).trans ((min_le_left _ _).trans (this.trans h1))
     · have : p * Q ≤ p * y := mul_le_mul_of_nonpos_left hy2 hp
       exact (min_le_left _ _).trans ((min_le_right _ _).trans (this.trans h1))
   · have h1 : P * y ≤ x * y := mul_le_mul_of_nonpos_right hx2 hy0
     rcases le_total 0 P with hP | hP
     · have : P * q ≤ P * y := mul_le_mul_of_nonneg_left hy1 hP
       exact (min_le_right _ _).trans ((min_le_left _ _).trans (this.trans h1))
     · have : P * Q ≤ P * y := mul_le_mul_of_nonpos_left hy2 hP
       exact (min_le_right _ _).trans ((min_le_right _ _).trans (this.trans h1))
 · rcases le_total 0 y with hy0 | hy0
   · have h1 : x * y ≤ P * y := mul_le_mul_of_nonneg_right hx2 hy0
     rcases le_total 0 P with hP | hP
     · have : P * y ≤ P * Q := mul_le_mul_of_nonneg_left hy2 hP
       exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_right _ _))
     · have : P * y ≤ P * q := mul_le_mul_of_nonpos_left hy1 hP
       exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_right _ _))
   · have h1 : x * y ≤ p * y := mul_le_mul_of_nonpos_right hx1 hy0
     rcases le_total 0 p with hp | hp
     · have : p * y ≤ p * Q := mul_le_mul_of_nonneg_left hy2 hp
       exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_left _ _))
     · have : p * y ≤ p * q := mul_le_mul_of_nonpos_left hy1 hp
       exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_left _ _))
theorem enc_mul {I J : IV} {a b : ℝ} (hI : I.Enc a) (hJ : J.Enc b) : (I.mul J).Enc (a * b) := by
 have hD := DZ_pos
 have hD0 : 0 < DZ := by norm_num [DZ]
 have hc := mul_mem_corners (x := a * DZ) (y := b * DZ)
   ⟨(div_le_iff₀ hD).mp hI.1, (le_div_iff₀ hD).mp hI.2⟩ ⟨(div_le_iff₀ hD).mp hJ.1, (le_div_iff₀ hD).mp hJ.2⟩
 unfold Enc mul
 constructor
 · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hD0) hD.le).trans ?_
   rw [div_div, div_le_iff₀ (by positivity)]
   have hm : (SZ.min (SZ.min (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.min (I.hi.mul J.lo) (I.hi.mul J.hi))).v
       ≤ min (min (I.lo.v * J.lo.v) (I.lo.v * J.hi.v)) (min (I.hi.v * J.lo.v) (I.hi.v * J.hi.v)) := by
     refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
     · rw [← SZ.v_mul]; exact (SZ.v_min_le_left _ _).trans (SZ.v_min_le_left _ _)
     · rw [← SZ.v_mul]; exact (SZ.v_min_le_left _ _).trans (SZ.v_min_le_right _ _)
     · rw [← SZ.v_mul]; exact (SZ.v_min_le_right _ _).trans (SZ.v_min_le_left _ _)
     · rw [← SZ.v_mul]; exact (SZ.v_min_le_right _ _).trans (SZ.v_min_le_right _ _)
   calc _ ≤ _ := hm
     _ ≤ a * DZ * (b * DZ) := hc.1
     _ = a * b * (DZ * DZ) := by ring
 · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hD0) hD.le)
   rw [div_div, le_div_iff₀ (by positivity)]
   have hm : max (max (I.lo.v * J.lo.v) (I.lo.v * J.hi.v)) (max (I.hi.v * J.lo.v) (I.hi.v * J.hi.v))
       ≤ (SZ.max (SZ.max (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.max (I.hi.mul J.lo) (I.hi.mul J.hi))).v := by
     refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
     · rw [← SZ.v_mul]; exact (SZ.le_v_max_left _ _).trans (SZ.le_v_max_left _ _)
     · rw [← SZ.v_mul]; exact (SZ.le_v_max_right _ _).trans (SZ.le_v_max_left _ _)
     · rw [← SZ.v_mul]; exact (SZ.le_v_max_left _ _).trans (SZ.le_v_max_right _ _)
     · rw [← SZ.v_mul]; exact (SZ.le_v_max_right _ _).trans (SZ.le_v_max_right _ _)
   calc a * b * (DZ * DZ) = a * DZ * (b * DZ) := by ring
     _ ≤ _ := hc.2
     _ ≤ _ := hm
theorem enc_mulc {C I : IV} {c a : ℝ} (hC : C.Enc c) (hC0 : 0 ≤ C.lo.v) (hI : I.Enc a) : (C.mulc I).Enc (c * a) := by
 have hD := DZ_pos
 have hD0 : 0 < DZ := by norm_num [DZ]
 have hc0 : 0 ≤ c := (div_nonneg hC0 hD.le).trans hC.1
 obtain ⟨hc1, hc2⟩ := hC; obtain ⟨ha1, ha2⟩ := hI
 have hc1' := (div_le_iff₀ hD).mp hc1; have hc2' := (le_div_iff₀ hD).mp hc2
 have ha1' := (div_le_iff₀ hD).mp ha1; have ha2' := (le_div_iff₀ hD).mp ha2
 unfold Enc mulc
 constructor
 · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hD0) hD.le).trans ?_
   rw [div_div, div_le_iff₀ (by positivity)]
   cases h : I.lo.nonneg <;> simp only [SZ.v_mul]
   · have hn : I.lo.v < 0 := by have := (SZ.nonneg_iff I.lo).not.mp (by simp [h]); linarith
     rcases le_total 0 a with ha | ha
     · nlinarith
     · nlinarith
   · have hn := (SZ.nonneg_iff I.lo).mp h
     nlinarith
 · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hD0) hD.le)
   rw [div_div, le_div_iff₀ (by positivity)]
   cases h : I.hi.nonneg <;> simp only [SZ.v_mul]
   · have hn : I.hi.v < 0 := by have := (SZ.nonneg_iff I.hi).not.mp (by simp [h]); linarith
     nlinarith
   · have hn := (SZ.nonneg_iff I.hi).mp h
     rcases le_total 0 a with ha | ha
     · nlinarith
     · nlinarith
theorem enc_divn {I : IV} {a : ℝ} {d : ℕ} (hd : 0 < d) (hI : I.Enc a) : (I.divn d).Enc (a / d) := by
 have hD := DZ_pos
 have hd' : (0 : ℝ) < d := by exact_mod_cast hd
 unfold Enc divn
 constructor
 · refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ hd) hD.le).trans ?_
   rw [div_div, mul_comm, ← div_div]
   exact div_le_div_of_nonneg_right hI.1 hd'.le
 · refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ hd) hD.le)
   rw [div_div, mul_comm, ← div_div]
   exact div_le_div_of_nonneg_right hI.2 hd'.le
theorem enc_divp {I : IV} {a e : ℝ} {e0 e1 : ℕ} (he0 : 0 < e0) (h0 : (e0 : ℝ) / DZ ≤ e) (h1 : e ≤ (e1 : ℝ) / DZ)
   (hI : I.Enc a) : (I.divp e0 e1).Enc (a / e) := by
 have hD := DZ_pos
 have hD0 : 0 < DZ := by norm_num [DZ]
 have he0' : (0 : ℝ) < e0 := by exact_mod_cast he0
 have he1 : 0 < e1 := by
   have : (e0 : ℝ) ≤ e1 := by
     have := h0.trans h1; rwa [div_le_div_iff_of_pos_right hD] at this
   exact_mod_cast he0'.trans_le this
 have he1' : (0 : ℝ) < e1 := by exact_mod_cast he1
 have hepos : 0 < e := (div_pos he0' hD).trans_le h0
 have h0' : (e0 : ℝ) ≤ e * DZ := (div_le_iff₀ hD).mp h0
 have h1' : e * DZ ≤ e1 := (le_div_iff₀ hD).mp h1
 obtain ⟨ha1, ha2⟩ := hI
 unfold Enc divp
 constructor
 · cases h : I.lo.nonneg <;> simp only
   · have hn : I.lo.v < 0 := by have := (SZ.nonneg_iff I.lo).not.mp (by simp [h]); linarith
     refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ he0) hD.le).trans ?_
     rw [SZ.v_muln, div_div, div_le_div_iff₀ (by positivity) hepos]
     have := (div_le_iff₀ hD).mp ha1
     nlinarith
   · have hn := (SZ.nonneg_iff I.lo).mp h
     refine (div_le_div_of_nonneg_right (SZ.v_fl_le _ he1) hD.le).trans ?_
     rw [SZ.v_muln, div_div, div_le_div_iff₀ (by positivity) hepos]
     have := (div_le_iff₀ hD).mp ha1
     nlinarith
 · cases h : I.hi.nonneg <;> simp only
   · have hn : I.hi.v < 0 := by have := (SZ.nonneg_iff I.hi).not.mp (by simp [h]); linarith
     refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ he1) hD.le)
     rw [SZ.v_muln, div_div, div_le_div_iff₀ hepos (by positivity)]
     have := (le_div_iff₀ hD).mp ha2
     nlinarith
   · have hn := (SZ.nonneg_iff I.hi).mp h
     refine le_trans ?_ (div_le_div_of_nonneg_right (SZ.le_v_ce _ he0) hD.le)
     rw [SZ.v_muln, div_div, div_le_div_iff₀ hepos (by positivity)]
     have := (le_div_iff₀ hD).mp ha2
     nlinarith
end IV
end AMW.G
namespace AMW.G
def SC : ℕ := 32768
def DZ2 : ℕ := 500000000000000
def PLN : ℕ := 314159265358979323846
def PUN : ℕ := 314159265358979323847
def E20 : ℕ := 100000000000000000000
def ERRD : ℕ := 2262000
def E9 : ℕ := 1000000000
def CDEN : ℕ := Nat.mul 3628800 (Nat.pow DZ 9)
def SDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 10)
def SCDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)
def S1DEN : ℕ := Nat.mul 3991680 (Nat.pow DZ 8)
def S2DEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)
def DZp (k : ℕ) : ℕ := Nat.pow DZ k
def cosP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 3628800 (DZp 10)) (Nat.mul (Nat.mul 151200 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))
def cosN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1814400 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 5040 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def sinP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 39916800 T) (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 5)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 9)) (DZp 2))
def sinN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 3)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 7)) (DZp 4))) (Nat.pow T 11)
def scP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 39916800 (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 8)) (DZp 2))
def scN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def s1P (T : ℕ) : ℕ := Nat.add (Nat.mul (Nat.mul 133056 (Nat.pow T 3)) (DZp 6)) (Nat.mul (Nat.mul 88 (Nat.pow T 7)) (DZp 2))
def s1N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1330560 T) (DZp 8)) (Nat.mul (Nat.mul 4752 (Nat.pow T 5)) (DZp 4))) (Nat.pow T 9)
def s2P (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 3991680 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 6160 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
def s2N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 13305600 (DZp 10)) (Nat.mul (Nat.mul 237600 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))
def PIC : IV := IV.ofN 3141592653589793 3141592653589794
def PI2C : IV := IV.ofN 9869604401089357 9869604401089364
def GAM0 : ℕ := 1654998581400000
def GAM1 : ℕ := 1654998603600000
def G1C : IV := IV.ofN 2654998581400000 2654998603600000
def G2C : IV := IV.ofN 4309997162800000 4309997207200000
def RHOC : IV := IV.ofN 1088464550157349 1088464557864635
def SIGC : IV := IV.ofN 346469027075676 346469029528983
def TAUC : IV := IV.ofN 3419512234467246 3419512258680401
def CE : List (ℕ × ℕ × Bool) :=
 [(1, 13686387, true), (2, 15900768, true), (3, 5481450, true), (4, 6757377, false), (5, 608034, false),
  (6, 4418860, false), (7, 6059090, false), (8, 2213086, false), (9, 6211618, false), (10, 5410132, false),
  (11, 2059537, false), (12, 1000, true)]
def CJ (j : ℕ) : ℕ × Bool :=
 match j with
 | 1 => (13686387, false) | 2 => (15900768, true) | 3 => (5481450, false) | 4 => (6757377, false)
 | 5 => (608034, true) | 6 => (4418860, false) | 7 => (6059090, true) | 8 => (2213086, false)
 | 9 => (6211618, true) | 10 => (5410132, false) | 11 => (2059537, true) | 12 => (1000, true) | _ => (0, false)
structure Acc where
 (pl ph nl nh : ℕ)
def Acc.put (a : Acc) (ng : Bool) (e m0 m1 : ℕ) : Acc :=
 Bool.rec (motive := fun _ => Acc) ⟨Nat.add a.pl (Nat.mul e m0), Nat.add a.ph (Nat.mul e m1), a.nl, a.nh⟩
   ⟨a.pl, a.ph, Nat.add a.nl (Nat.mul e m0), Nat.add a.nh (Nat.mul e m1)⟩ ng
def mnum (n X X2 J2 : ℕ) : ℕ :=
 Nat.rec (motive := fun _ => ℕ) (Nat.mul X (DZp 2))
   (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul (Nat.add X2 J2) (DZp 3))
     (fun _ _ => Nat.mul (Nat.mul (Nat.mul 2 X) (Nat.add X2 (Nat.mul 3 J2))) (DZp 4)) m) n
def hden (n Y : ℕ) : ℕ :=
 Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 Y)
   (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 (Nat.mul Y Y)) (fun _ _ => Nat.pow Y 3) m) n
def mneg (n : ℕ) (ab : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (!ab) true (Nat.beq n 1)
def hneg (n : ℕ) : Bool := Nat.beq n 1
def farJ (n k XL XU XL2 XU2 : ℕ) (a : Acc) (j e : ℕ) (sg : Bool) : Acc :=
 let J := Nat.mul j DZ
 let J2 := Nat.mul J J
 Bool.rec (motive := fun _ => Acc)
   (Bool.rec (motive := fun _ => Acc)
     (a.put (xor sg (mneg n false)) e (Nat.div (mnum n XL XL2 J2) (Nat.pow (Nat.sub J2 XL2) (Nat.succ n)))
       (ndivc (mnum n XU XU2 J2) (Nat.pow (Nat.sub J2 XU2) (Nat.succ n))))
     (a.put (xor sg (mneg n true)) e (Nat.div (mnum n XU XU2 J2) (Nat.pow (Nat.sub XU2 J2) (Nat.succ n)))
       (ndivc (mnum n XL XL2 J2) (Nat.pow (Nat.sub XL2 J2) (Nat.succ n))))
     (Nat.blt (Nat.mul 2 j) k))
   (a.put (xor sg (hneg n)) e (Nat.div (DZp (Nat.add n 2)) (hden n (Nat.add XU J)))
     (ndivc (DZp (Nat.add n 2)) (hden n (Nat.add XL J))))
   (Nat.beq (Nat.mul 2 j) k)
def farAcc (n k XL XU XL2 XU2 : ℕ) : List (ℕ × ℕ × Bool) → Acc → Acc
 | [], a => a
 | (j, e, sg) :: rest, a => farAcc n k XL XU XL2 XU2 rest (farJ n k XL XU XL2 XU2 a j e sg)
structure CellA where
 (LN UN : ℕ)
namespace CellA
def k (c : CellA) : ℕ := Nat.div (Nat.add (Nat.mul 2 (Nat.add c.LN c.UN)) SC) (Nat.mul 2 SC)
def side (c : CellA) : Bool := Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)
def LLO (c : CellA) : ℕ := Nat.div (Nat.mul c.LN DZ) SC
def UHI (c : CellA) : ℕ := ndivc (Nat.mul c.UN DZ) SC
def AD (c : CellA) : ℕ := Nat.mul c.k DZ2
def RLO (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.UHI) (Nat.sub c.LLO c.AD) c.side
def RHI (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.LLO) (Nat.sub c.UHI c.AD) c.side
def TLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.RLO) E20
def TUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.RHI) E20
def CI (c : CellA) : IV :=
 ⟨⟨Nat.div (Nat.sub (cosP c.TUZ) (cosN c.TUZ)) CDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (cosP c.TLZ) (cosN c.TLZ)) CDEN) ERRD, 0⟩⟩
def SI (c : CellA) : IV :=
 ⟨⟨Nat.div (Nat.sub (sinP c.TLZ) (sinN c.TLZ)) SDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (sinP c.TUZ) (sinN c.TUZ)) SDEN) ERRD, 0⟩⟩
def km4 (c : CellA) : ℕ := Nat.mod c.k 4
def CX (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV)
   (Bool.rec (motive := fun _ => IV)
     (Bool.rec (motive := fun _ => IV) (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) c.CI.neg (Nat.beq c.km4 2))
     (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 1))
   c.CI (Nat.beq c.km4 0)
def SX (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV)
   (Bool.rec (motive := fun _ => IV)
     (Bool.rec (motive := fun _ => IV) c.CI.neg (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 2))
     c.CI (Nat.beq c.km4 1))
   (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) (Nat.beq c.km4 0)
def BLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.LLO) E20
def BUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.UHI) E20
def BI (c : CellA) : IV := IV.ofN c.BLZ c.BUZ
def PG (c : CellA) : IV := IV.ofN (Nat.div (Nat.mul GAM0 c.BLZ) DZ) (ndivc (Nat.mul GAM1 c.BUZ) DZ)
def NI (c : CellA) : IV := c.CX.sub (IV.mulc c.PG c.SX)
def E0 (c : CellA) : ℕ := Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ
def E1 (c : CellA) : ℕ := Nat.sub (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ
def EI (c : CellA) : IV := IV.ofN c.E0 c.E1
def ok (c : CellA) : Bool :=
 Nat.ble c.LN c.UN && Nat.ble c.TUZ DZ
   && Bool.rec (motive := fun _ => Bool) (Nat.ble (Nat.mul 2 c.UN) (Nat.mul c.k SC)) (Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)) c.side
   && Nat.blt 0 c.E0
def FA (c : CellA) (n : ℕ) : IV :=
 let k := c.k
 let XL := c.LLO
 let XU := c.UHI
 let XL2 := Nat.mul XL XL
 let XU2 := Nat.mul XU XU
 let a := (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 ⟨0, 0, 0, 0⟩ 1 13686387 true) 2 15900768 true) 3 5481450 true) 4 6757377 false) 5 608034 false) 6 4418860 false) 7 6059090 false) 8 2213086 false) 9 6211618 false) 10 5410132 false) 11 2059537 false) 12 1000 true)
 IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9
def nearOn (c : CellA) : Bool := Nat.beq (Nat.mod c.k 2) 0 && Nat.ble 2 c.k && Nat.ble c.k 24
def S0 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨scP c.TLZ, scN c.TUZ⟩ SCDEN).sub (SZ.ofN ERRD), (SZ.ce ⟨scP c.TUZ, scN c.TLZ⟩ SCDEN).add (SZ.ofN ERRD)⟩
def G1 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨s1P c.TLZ, s1N c.TUZ⟩ S1DEN).sub (SZ.ofN (Nat.mul 2 ERRD)), (SZ.ce ⟨s1P c.TUZ, s1N c.TLZ⟩ S1DEN).add (SZ.ofN (Nat.mul 2 ERRD))⟩
def G2 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨s2P c.TLZ, s2N c.TUZ⟩ S2DEN).sub (SZ.ofN (Nat.mul 5 ERRD)), (SZ.ce ⟨s2P c.TUZ, s2N c.TLZ⟩ S2DEN).add (SZ.ofN (Nat.mul 5 ERRD))⟩
def j0 (c : CellA) : ℕ := Nat.div c.k 2
def B0 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 c.S0).divn (Nat.mul 2 E9)) c.nearOn
def B1 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero
   ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PIC (Bool.rec (motive := fun _ => IV) c.G1.neg c.G1 c.side))).divn (Nat.mul 2 E9))
   c.nearOn
def B2 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PI2C c.G2)).divn (Nat.mul 2 E9)) c.nearOn
def SF0 (c : CellA) : IV := c.SX.mul (c.FA 0)
def K0 (c : CellA) : IV := (c.NI.neg.divp c.E0 c.E1).add ((IV.mulc SIGC c.SF0).add (IV.mulc RHOC c.B0))
def MI (c : CellA) : IV :=
 (IV.mulc c.EI ((IV.mulc G1C c.SX).add (IV.mulc c.PG c.CX))).add (IV.mulc (c.BI.muln 4) c.NI)
def E2L (c : CellA) : ℕ := Nat.div (Nat.mul c.E0 c.E0) DZ
def E2U (c : CellA) : ℕ := ndivc (Nat.mul c.E1 c.E1) DZ
def K1 (c : CellA) : IV :=
 (IV.mulc PIC (c.MI.divp c.E2L c.E2U)).add
   (((IV.mulc RHOC (c.CX.mul (c.FA 0))).add (IV.mulc SIGC (c.SX.mul (c.FA 1)))).add (IV.mulc RHOC c.B1))
def N2 (c : CellA) : IV := (IV.mulc c.PG c.SX).sub (IV.mulc G2C c.CX)
def E3L (c : CellA) : ℕ := Nat.div (Nat.mul c.E2L c.E0) DZ
def E3U (c : CellA) : ℕ := ndivc (Nat.mul c.E2U c.E1) DZ
def PP (c : CellA) : IV :=
 ((IV.mulc (IV.ofN c.E2L c.E2U) c.N2).sub ((IV.mulc c.EI c.NI).muln 4)).add ((IV.mulc c.BI c.MI).muln 8)
def K2 (c : CellA) : IV :=
 (IV.mulc PI2C (c.PP.divp c.E3L c.E3U)).neg.add
   ((((IV.mulc RHOC (c.CX.mul (c.FA 1))).muln 2).sub (IV.mulc TAUC c.SF0)).add
     ((IV.mulc SIGC (c.SX.mul (c.FA 2))).add (IV.mulc RHOC c.B2)))
def KA (c : CellA) : SZ := SZ.max (SZ.ofN 0) (SZ.max c.K0.lo c.K0.hi.neg)
def W1 (c : CellA) : IV := (c.K0.mul c.K1).muln 2
def W2L (c : CellA) : SZ :=
 SZ.add (SZ.mul (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)) (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)))
   ((c.K0.mul c.K2).lo.muln DZ)
end CellA
end AMW.G
noncomputable section
open Real Filter Topology Asymptotics
namespace AMW
def sc1 (θ : ℝ) : ℝ := if θ = 0 then 0 else (θ * Real.cos θ - Real.sin θ) / θ ^ 2
def sc2 (θ : ℝ) : ℝ := if θ = 0 then -1 / 3 else (-θ ^ 2 * Real.sin θ - 2 * θ * Real.cos θ + 2 * Real.sin θ) / θ ^ 3
theorem hasDerivAt_sinc_of_ne {θ : ℝ} (h : θ ≠ 0) : HasDerivAt Real.sinc (sc1 θ) θ := by
 have hev : Real.sinc =ᶠ[𝓝 θ] fun t => Real.sin t / t := by
   filter_upwards [isOpen_ne.mem_nhds h] with t ht
   rw [Real.sinc_of_ne_zero ht]
 have hd := (Real.hasDerivAt_sin θ).div (hasDerivAt_id θ) h
 rw [sc1, if_neg h]
 refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
 simp only [id]
 ring
theorem abs_sin_sub_self_le {h : ℝ} (hh : |h| ≤ 1) : |Real.sin h - h| ≤ |h| ^ 3 := by
 have hb := Real.sin_bound hh
 have h0 := abs_nonneg h
 have e : Real.sin h - h = (Real.sin h - (h - h ^ 3 / 6)) - h ^ 3 / 6 := by ring
 rw [e]
 have h3 : |h ^ 3 / 6| = |h| ^ 3 / 6 := by rw [abs_div, abs_pow]; norm_num
 have h5 : |h| ^ 5 ≤ |h| ^ 3 := by
   calc |h| ^ 5 = |h| ^ 3 * (|h| * |h|) := by ring
     _ ≤ |h| ^ 3 * (1 * 1) := by gcongr
     _ = |h| ^ 3 := by ring
 calc |Real.sin h - (h - h ^ 3 / 6) - h ^ 3 / 6| ≤ |Real.sin h - (h - h ^ 3 / 6)| + |h ^ 3 / 6| := abs_sub _ _
   _ ≤ |h| ^ 5 / 100 + |h| ^ 3 / 6 := by rw [h3]; linarith
   _ ≤ |h| ^ 3 := by nlinarith [pow_nonneg h0 3]
theorem abs_sinc_sub_one_le {h : ℝ} (hh : |h| ≤ 1) : |Real.sinc h - 1| ≤ h ^ 2 := by
 rcases eq_or_ne h 0 with rfl | h0
 · simp
 rw [Real.sinc_of_ne_zero h0]
 have hp : 0 < |h| := abs_pos.mpr h0
 have e : Real.sin h / h - 1 = (Real.sin h - h) / h := by field_simp
 rw [e, abs_div, div_le_iff₀ hp]
 have := abs_sin_sub_self_le hh
 calc |Real.sin h - h| ≤ |h| ^ 3 := this
   _ = h ^ 2 * |h| := by rw [← sq_abs h]; ring
theorem hasDerivAt_sinc_zero : HasDerivAt Real.sinc 0 0 := by
 rw [hasDerivAt_iff_isLittleO_nhds_zero]
 have h1 : (fun h : ℝ => Real.sinc (0 + h) - Real.sinc 0 - h • (0 : ℝ)) =O[𝓝 0] fun h => h ^ 2 := by
   refine Asymptotics.IsBigO.of_bound 1 ?_
   filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
   rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
   simp only [zero_add, Real.sinc_zero, smul_zero, sub_zero, Real.norm_eq_abs, one_mul]
   rw [abs_of_nonneg (sq_nonneg h)]
   exact abs_sinc_sub_one_le hh.le
 exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
theorem hasDerivAt_sinc (θ : ℝ) : HasDerivAt Real.sinc (sc1 θ) θ := by
 rcases eq_or_ne θ 0 with rfl | h
 · have : sc1 0 = 0 := by simp [sc1]
   rw [this]; exact hasDerivAt_sinc_zero
 · exact hasDerivAt_sinc_of_ne h
theorem hasDerivAt_sc1_of_ne {θ : ℝ} (h : θ ≠ 0) : HasDerivAt sc1 (sc2 θ) θ := by
 have hev : sc1 =ᶠ[𝓝 θ] fun t => (t * Real.cos t - Real.sin t) / t ^ 2 := by
   filter_upwards [isOpen_ne.mem_nhds h] with t ht
   rw [sc1, if_neg ht]
 have hn : HasDerivAt (fun t => t * Real.cos t - Real.sin t) (1 * Real.cos θ + θ * (-Real.sin θ) - Real.cos θ) θ :=
   ((hasDerivAt_id θ).mul (Real.hasDerivAt_cos θ)).sub (Real.hasDerivAt_sin θ)
 have hd : HasDerivAt (fun t : ℝ => t ^ 2) (((2 : ℕ) : ℝ) * θ ^ (2 - 1)) θ := hasDerivAt_pow 2 θ
 have hq := hn.div hd (pow_ne_zero 2 h)
 rw [sc2, if_neg h]
 refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
 field_simp
 ring
theorem abs_sc1_num_le {h : ℝ} (hh : |h| ≤ 1) : |h * Real.cos h - Real.sin h + h ^ 3 / 3| ≤ |h| ^ 4 / 8 := by
 have hc := Real.cos_bound hh
 have hs := Real.sin_bound hh
 have h0 := abs_nonneg h
 have e : h * Real.cos h - Real.sin h + h ^ 3 / 3
     = h * (Real.cos h - (1 - h ^ 2 / 2)) - (Real.sin h - (h - h ^ 3 / 6)) := by ring
 rw [e]
 have h5 : |h| ^ 5 ≤ |h| ^ 4 := by
   calc |h| ^ 5 = |h| ^ 4 * |h| := by ring
     _ ≤ |h| ^ 4 * 1 := by gcongr
     _ = |h| ^ 4 := by ring
 calc |h * (Real.cos h - (1 - h ^ 2 / 2)) - (Real.sin h - (h - h ^ 3 / 6))|
     ≤ |h * (Real.cos h - (1 - h ^ 2 / 2))| + |Real.sin h - (h - h ^ 3 / 6)| := abs_sub _ _
   _ = |h| * |Real.cos h - (1 - h ^ 2 / 2)| + |Real.sin h - (h - h ^ 3 / 6)| := by rw [abs_mul]
   _ ≤ |h| * (|h| ^ 4 * (5 / 96)) + |h| ^ 5 / 100 := by gcongr
   _ ≤ |h| ^ 4 / 8 := by nlinarith [pow_nonneg h0 4]
theorem hasDerivAt_sc1_zero : HasDerivAt sc1 (-1 / 3) 0 := by
 rw [hasDerivAt_iff_isLittleO_nhds_zero]
 have h1 : (fun h : ℝ => sc1 (0 + h) - sc1 0 - h • (-1 / 3 : ℝ)) =O[𝓝 0] fun h => h ^ 2 := by
   refine Asymptotics.IsBigO.of_bound 1 ?_
   filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
   rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
   simp only [zero_add, smul_eq_mul, Real.norm_eq_abs, one_mul]
   rw [abs_of_nonneg (sq_nonneg h)]
   have hs0 : sc1 0 = 0 := by simp [sc1]
   rw [hs0]
   rcases eq_or_ne h 0 with rfl | h0
   · simp [sc1]
   rw [sc1, if_neg h0]
   have hp : 0 < h ^ 2 := by positivity
   have e : (h * Real.cos h - Real.sin h) / h ^ 2 - 0 - h * (-1 / 3)
       = (h * Real.cos h - Real.sin h + h ^ 3 / 3) / h ^ 2 := by field_simp; ring
   rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
   have := abs_sc1_num_le hh.le
   have hq : |h| ^ 4 = h ^ 2 * h ^ 2 := by rw [← sq_abs h]; ring
   have hh2 : h ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg h]
   nlinarith [sq_nonneg h]
 exact h1.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
theorem hasDerivAt_sc1 (θ : ℝ) : HasDerivAt sc1 (sc2 θ) θ := by
 rcases eq_or_ne θ 0 with rfl | h
 · have : sc2 0 = -1 / 3 := by simp [sc2]
   rw [this]; exact hasDerivAt_sc1_zero
 · exact hasDerivAt_sc1_of_ne h
def K1AM (x : ℝ) : ℝ :=
 ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
   ((-(π * sc1 ((ωAM j - 2 * π * x) / 2)) + π * sc1 ((ωAM j + 2 * π * x) / 2)) / 2)
def K2AM (x : ℝ) : ℝ :=
 ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
   ((π ^ 2 * sc2 ((ωAM j - 2 * π * x) / 2) + π ^ 2 * sc2 ((ωAM j + 2 * π * x) / 2)) / 2)
theorem hasDerivAt_lin_m (w x : ℝ) : HasDerivAt (fun y : ℝ => (w - 2 * π * y) / 2) (-π) x := by
 have := ((hasDerivAt_id x).const_mul (2 * π)).const_sub w |>.div_const 2
 simpa using this.congr_deriv (by ring)
theorem hasDerivAt_lin_p (w x : ℝ) : HasDerivAt (fun y : ℝ => (w + 2 * π * y) / 2) π x := by
 have := ((hasDerivAt_id x).const_mul (2 * π)).const_add w |>.div_const 2
 simpa using this.congr_deriv (by ring)
theorem hasDerivAt_KfunAM (x : ℝ) : HasDerivAt KfunAM (K1AM x) x := by
 have hK : KfunAM = fun y => ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
     ((Real.sinc ((ωAM j - 2 * π * y) / 2) + Real.sinc ((ωAM j + 2 * π * y) / 2)) / 2) :=
   funext KfunAM_eq_sinc
 rw [hK, K1AM]
 apply HasDerivAt.fun_sum
 intro j _
 have h1 := (hasDerivAt_sinc ((ωAM j - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (ωAM j) x)
 have h2 := (hasDerivAt_sinc ((ωAM j + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (ωAM j) x)
 exact ((h1.add h2).div_const 2).const_mul _ |>.congr_deriv (by ring)
theorem hasDerivAt_K1AM (x : ℝ) : HasDerivAt K1AM (K2AM x) x := by
 rw [show K1AM = fun y => ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
     ((-(π * sc1 ((ωAM j - 2 * π * y) / 2)) + π * sc1 ((ωAM j + 2 * π * y) / 2)) / 2) from rfl, K2AM]
 apply HasDerivAt.fun_sum
 intro j _
 have h1 := (hasDerivAt_sc1 ((ωAM j - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (ωAM j) x)
 have h2 := (hasDerivAt_sc1 ((ωAM j + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (ωAM j) x)
 exact ((((h1.const_mul π).neg).add (h2.const_mul π)).div_const 2).const_mul _ |>.congr_deriv (by ring)
def k1AM (x : ℝ) : ℝ := K1AM x / KfunAM 0
def k2AM (x : ℝ) : ℝ := K2AM x / KfunAM 0
def w1AM (x : ℝ) : ℝ := 2 * kfunAM x * k1AM x
def w2AM (x : ℝ) : ℝ := 2 * (k1AM x ^ 2 + kfunAM x * k2AM x)
theorem hasDerivAt_kfunAM (x : ℝ) : HasDerivAt kfunAM (k1AM x) x :=
 (hasDerivAt_KfunAM x).div_const _
theorem hasDerivAt_k1AM (x : ℝ) : HasDerivAt k1AM (k2AM x) x :=
 (hasDerivAt_K1AM x).div_const _
theorem hasDerivAt_wfunAM (x : ℝ) : HasDerivAt wfunAM (w1AM x) x := by
 have h := (hasDerivAt_kfunAM x).pow 2
 refine h.congr_deriv ?_
 simp only [w1AM]; push_cast; ring
theorem hasDerivAt_w1AM (x : ℝ) : HasDerivAt w1AM (w2AM x) x := by
 have h := ((hasDerivAt_kfunAM x).const_mul 2).mul (hasDerivAt_k1AM x)
 refine (h.congr_deriv ?_ : HasDerivAt (fun y => 2 * kfunAM y * k1AM y) _ x)
 simp only [w2AM]; ring
end AMW
end
noncomputable section
open Real Filter Topology
namespace AMW
def gamAM : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
def mN (x : ℝ) : ℝ := Real.cos (π * x) - 2 * gamAM * (π * x) * Real.sin (π * x)
def mD (x : ℝ) : ℝ := 1 - 2 * (π * x) ^ 2
def mNb (x : ℝ) : ℝ := -(1 + 2 * gamAM) * Real.sin (π * x) - 2 * gamAM * (π * x) * Real.cos (π * x)
def mM (x : ℝ) : ℝ := mNb x * mD x + 4 * (π * x) * mN x
def mN2 (x : ℝ) : ℝ := -(1 + 4 * gamAM) * Real.cos (π * x) + 2 * gamAM * (π * x) * Real.sin (π * x)
def mP (x : ℝ) : ℝ := mN2 x * mD x ^ 2 + 4 * mN x * mD x + 8 * (π * x) * mM x
def K0AM : ℝ := Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)
theorem K0AM_eq : KfunAM 0 = K0AM := KfunAM_zero_closed
theorem K0AM_pos : 0 < K0AM := by rw [← K0AM_eq]; exact KfunAM_zero_pos
theorem hasDerivAt_pix (x : ℝ) : HasDerivAt (fun y : ℝ => π * y) π x := by
 simpa using (hasDerivAt_id x).const_mul π
theorem hasDerivAt_mN (x : ℝ) : HasDerivAt mN (π * mNb x) x := by
 have hc := (Real.hasDerivAt_cos (π * x)).comp x (hasDerivAt_pix x)
 have hs := (Real.hasDerivAt_sin (π * x)).comp x (hasDerivAt_pix x)
 have h := hc.sub (((hasDerivAt_pix x).const_mul (2 * gamAM)).mul hs)
 have e : mN = fun y => Real.cos (π * y) - 2 * gamAM * (π * y) * Real.sin (π * y) := rfl
 rw [e]; refine h.congr_deriv ?_
 simp only [Function.comp, mNb]; ring
theorem hasDerivAt_mD (x : ℝ) : HasDerivAt mD (-(4 * π * (π * x))) x := by
 have h := ((hasDerivAt_pix x).pow 2).const_mul 2 |>.const_sub 1
 have e : mD = fun y => 1 - 2 * (π * y) ^ 2 := rfl
 rw [e]; refine h.congr_deriv ?_
 push_cast; ring
theorem hasDerivAt_mNb (x : ℝ) : HasDerivAt mNb (π * mN2 x) x := by
 have hc := (Real.hasDerivAt_cos (π * x)).comp x (hasDerivAt_pix x)
 have hs := (Real.hasDerivAt_sin (π * x)).comp x (hasDerivAt_pix x)
 have h := (hs.const_mul (-(1 + 2 * gamAM))).sub (((hasDerivAt_pix x).const_mul (2 * gamAM)).mul hc)
 have e : mNb = fun y => -(1 + 2 * gamAM) * Real.sin (π * y) - 2 * gamAM * (π * y) * Real.cos (π * y) := rfl
 rw [e]; refine h.congr_deriv ?_
 simp only [Function.comp, mN2]; ring
theorem hasDerivAt_mM (x : ℝ) : HasDerivAt mM (π * (mN2 x * mD x + 4 * mN x)) x := by
 have h := ((hasDerivAt_mNb x).mul (hasDerivAt_mD x)).add (((hasDerivAt_pix x).const_mul 4).mul (hasDerivAt_mN x))
 have e : mM = fun y => mNb y * mD y + 4 * (π * y) * mN y := rfl
 rw [e]; refine h.congr_deriv ?_
 ring
theorem continuous_mD : Continuous mD := by unfold mD; fun_prop
theorem hasDerivAt_mND {x : ℝ} (hx : mD x ≠ 0) : HasDerivAt (fun y => mN y / mD y) (π * mM x / mD x ^ 2) x := by
 refine ((hasDerivAt_mN x).div (hasDerivAt_mD x) hx).congr_deriv ?_
 simp only [mM]; field_simp; ring
theorem hasDerivAt_mMD {x : ℝ} (hx : mD x ≠ 0) :
   HasDerivAt (fun y => π * mM y / mD y ^ 2) (π ^ 2 * mP x / mD x ^ 3) x := by
 have h := ((hasDerivAt_mM x).const_mul π).div ((hasDerivAt_mD x).pow 2) (pow_ne_zero 2 hx)
 refine h.congr_deriv ?_
 simp only [Pi.pow_apply, mP, mM]; push_cast; field_simp; ring
def KMT1 (x : ℝ) : ℝ :=
 (-(π * sc1 ((Real.sqrt 2 - 2 * π * x) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2
def KMT2 (x : ℝ) : ℝ :=
 (π ^ 2 * sc2 ((Real.sqrt 2 - 2 * π * x) / 2) + π ^ 2 * sc2 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2
theorem hasDerivAt_KMT (x : ℝ) : HasDerivAt KMT (KMT1 x) x := by
 have h1 := (hasDerivAt_sinc ((Real.sqrt 2 - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (Real.sqrt 2) x)
 have h2 := (hasDerivAt_sinc ((Real.sqrt 2 + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (Real.sqrt 2) x)
 have e : KMT = fun y => (Real.sinc ((Real.sqrt 2 - 2 * π * y) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * y) / 2)) / 2 := rfl
 rw [e]; exact ((h1.add h2).div_const 2).congr_deriv (by simp only [KMT1]; ring)
theorem hasDerivAt_KMT1 (x : ℝ) : HasDerivAt KMT1 (KMT2 x) x := by
 have h1 := (hasDerivAt_sc1 ((Real.sqrt 2 - 2 * π * x) / 2)).comp x (hasDerivAt_lin_m (Real.sqrt 2) x)
 have h2 := (hasDerivAt_sc1 ((Real.sqrt 2 + 2 * π * x) / 2)).comp x (hasDerivAt_lin_p (Real.sqrt 2) x)
 have e : KMT1 = fun y => (-(π * sc1 ((Real.sqrt 2 - 2 * π * y) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * y) / 2)) / 2 := rfl
 rw [e]; exact ((((h1.const_mul π).neg).add (h2.const_mul π)).div_const 2).congr_deriv (by simp only [KMT2]; ring)
theorem KMT_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT x = K0AM * (mN x / mD x) := by
 have h := KMT_eq_gamma (x := x) hx
 rw [h]; rfl
theorem isOpen_mD_ne : IsOpen {y : ℝ | mD y ≠ 0} := isOpen_ne_fun continuous_mD continuous_const
theorem KMT1_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT1 x = K0AM * (π * mM x / mD x ^ 2) := by
 have hev : KMT =ᶠ[𝓝 x] fun y => K0AM * (mN y / mD y) := by
   filter_upwards [isOpen_mD_ne.mem_nhds hx] with y hy using KMT_eq_ND hy
 have h2 := ((hasDerivAt_mND hx).const_mul K0AM).congr_of_eventuallyEq hev
 exact (hasDerivAt_KMT x).unique h2
theorem KMT2_eq_ND {x : ℝ} (hx : mD x ≠ 0) : KMT2 x = K0AM * (π ^ 2 * mP x / mD x ^ 3) := by
 have hev : KMT1 =ᶠ[𝓝 x] fun y => K0AM * (π * mM y / mD y ^ 2) := by
   filter_upwards [isOpen_mD_ne.mem_nhds hx] with y hy using KMT1_eq_ND hy
 have h2 := ((hasDerivAt_mMD hx).const_mul K0AM).congr_of_eventuallyEq hev
 exact (hasDerivAt_KMT1 x).unique h2
theorem sc1_neg (θ : ℝ) : sc1 (-θ) = -sc1 θ := by
 unfold sc1
 rcases eq_or_ne θ 0 with rfl | h
 · simp
 · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.cos_neg, Real.sin_neg]; ring
theorem sc2_neg (θ : ℝ) : sc2 (-θ) = sc2 θ := by
 unfold sc2
 rcases eq_or_ne θ 0 with rfl | h
 · simp
 · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Real.cos_neg, Real.sin_neg]; ring
def Tj (n : ℕ) (x : ℝ) : ℝ := (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2
def T1j (n : ℕ) (x : ℝ) : ℝ := (sc1 (π * (x - ((n : ℝ) + 1))) + sc1 (π * (x + ((n : ℝ) + 1)))) / 2
def T2j (n : ℕ) (x : ℝ) : ℝ := (sc2 (π * (x - ((n : ℝ) + 1))) + sc2 (π * (x + ((n : ℝ) + 1)))) / 2
def rhoAM : ℝ := 1 / K0AM
theorem kfunAM_eq {x : ℝ} (hx : mD x ≠ 0) :
   kfunAM x = mN x / mD x + rhoAM * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * Tj n x := by
 have h0 := K0AM_pos.ne'
 unfold kfunAM
 rw [K0AM_eq, KfunAM_eq_sinc, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
 have hk : (Real.sinc ((Real.sqrt 2 - 2 * π * x) / 2) + Real.sinc ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT x := rfl
 rw [hk, KMT_eq_ND hx]
 have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
     ((Real.sinc ((ωAM (n + 1) - 2 * π * x) / 2) + Real.sinc ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
     = (cAM (n + 1) : ℝ) * Tj n x := by
   intro n _; rw [term_sinc]; rfl
 rw [Finset.sum_congr rfl hs, rhoAM]
 field_simp
 ring
theorem k1AM_eq {x : ℝ} (hx : mD x ≠ 0) :
   k1AM x = π * mM x / mD x ^ 2 + rhoAM * π * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T1j n x := by
 have h0 := K0AM_pos.ne'
 unfold k1AM K1AM
 rw [K0AM_eq, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
 have hk : (-(π * sc1 ((Real.sqrt 2 - 2 * π * x) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT1 x := rfl
 rw [hk, KMT1_eq_ND hx]
 have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
     ((-(π * sc1 ((ωAM (n + 1) - 2 * π * x) / 2)) + π * sc1 ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
     = π * ((cAM (n + 1) : ℝ) * T1j n x) := by
   intro n _
   rw [ωAM_succ]
   have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
   have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
   rw [e1, e2, sc1_neg, T1j]; ring
 rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, rhoAM]
 field_simp
 ring
theorem k2AM_eq {x : ℝ} (hx : mD x ≠ 0) :
   k2AM x = π ^ 2 * mP x / mD x ^ 3 + rhoAM * π ^ 2 * ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T2j n x := by
 have h0 := K0AM_pos.ne'
 unfold k2AM K2AM
 rw [K0AM_eq, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul]
 have hk : (π ^ 2 * sc2 ((Real.sqrt 2 - 2 * π * x) / 2) + π ^ 2 * sc2 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2 = KMT2 x := rfl
 rw [hk, KMT2_eq_ND hx]
 have hs : ∀ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) *
     ((π ^ 2 * sc2 ((ωAM (n + 1) - 2 * π * x) / 2) + π ^ 2 * sc2 ((ωAM (n + 1) + 2 * π * x) / 2)) / 2)
     = π ^ 2 * ((cAM (n + 1) : ℝ) * T2j n x) := by
   intro n _
   rw [ωAM_succ]
   have e1 : (2 * π * ((n : ℝ) + 1) - 2 * π * x) / 2 = -(π * (x - ((n : ℝ) + 1))) := by ring
   have e2 : (2 * π * ((n : ℝ) + 1) + 2 * π * x) / 2 = π * (x + ((n : ℝ) + 1)) := by ring
   rw [e1, e2, sc2_neg, T2j]; ring
 rw [Finset.sum_congr rfl hs, ← Finset.mul_sum, rhoAM]
 field_simp
 ring
end AMW
end
noncomputable section
open Real
namespace AMW
def tcos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800
def tsin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800
def tsinc (t : ℝ) : ℝ := 1 - t^2/6 + t^4/120 - t^6/5040 + t^8/362880 - t^10/39916800
def tsc1 (t : ℝ) : ℝ := -t/3 + t^3/30 - t^5/840 + t^7/45360 - t^9/3991680
def tsc2 (t : ℝ) : ℝ := -1/3 + t^2/10 - t^4/168 + t^6/6480 - t^8/443520 + t^10/39916800
def terr : ℝ := 13 / 5748019200
theorem cos_sin_taylor12' (θ : ℝ) (hθ : |θ| ≤ 1) :
   |Real.cos θ - tcos θ| ≤ |θ| ^ 12 * terr ∧ |Real.sin θ - tsin θ| ≤ |θ| ^ 12 * terr := by
 have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by simpa using hθ
 have hb := Complex.exp_bound hx (n := 12) (by norm_num)
 have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
 have hsum : ∑ m ∈ Finset.range 12, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
     = ((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I := by
   simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, tcos, tsin]
   apply Complex.ext <;> · simp [pow_succ]; ring
 rw [hsum, hnx] at hb
 have hE : ‖Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I)‖
     ≤ |θ| ^ 12 * terr := by
   refine hb.trans (le_of_eq ?_); unfold terr; norm_num
 constructor
 · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_re]
 · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I) - (((tcos θ : ℝ) : ℂ) + ((tsin θ : ℝ) : ℂ) * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_im]
theorem terr_pos : 0 < terr := by unfold terr; norm_num
theorem abs_sinc_sub_tsinc_le {t : ℝ} (ht : |t| ≤ 1) : |Real.sinc t - tsinc t| ≤ terr := by
 rcases eq_or_ne t 0 with rfl | h0
 · simp [tsinc, terr_pos.le]
 have hs := (cos_sin_taylor12' t ht).2
 have hp : 0 < |t| := abs_pos.mpr h0
 have e : Real.sinc t - tsinc t = (Real.sin t - tsin t) / t := by
   rw [Real.sinc_of_ne_zero h0]; unfold tsinc tsin; field_simp
 rw [e, abs_div, div_le_iff₀ hp]
 have hte := terr_pos.le
 have h11 : |t| ^ 11 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
 calc |Real.sin t - tsin t| ≤ |t| ^ 12 * terr := hs
   _ = (|t| ^ 11 * terr) * |t| := by ring
   _ ≤ (1 * terr) * |t| := by gcongr
   _ = terr * |t| := by ring
theorem abs_sc1_sub_tsc1_le {t : ℝ} (ht : |t| ≤ 1) : |sc1 t - tsc1 t| ≤ 2 * terr := by
 rcases eq_or_ne t 0 with rfl | h0
 · simp [sc1, tsc1, terr_pos.le]
 have hc := (cos_sin_taylor12' t ht).1
 have hs := (cos_sin_taylor12' t ht).2
 have hp : 0 < |t| := abs_pos.mpr h0
 have hp2 : 0 < t ^ 2 := by positivity
 have e : sc1 t - tsc1 t = (t * (Real.cos t - tcos t) - (Real.sin t - tsin t)) / t ^ 2 := by
   rw [sc1, if_neg h0]; unfold tsc1 tcos tsin; field_simp; ring
 rw [e, abs_div, abs_of_pos hp2, div_le_iff₀ hp2]
 have h10 : |t| ^ 10 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
 have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
 have hte := terr_pos.le
 have h12 : 0 ≤ |t| ^ 12 * terr := by positivity
 calc |t * (Real.cos t - tcos t) - (Real.sin t - tsin t)|
     ≤ |t| * |Real.cos t - tcos t| + |Real.sin t - tsin t| := by
       rw [← abs_mul]; exact abs_sub _ _
   _ ≤ |t| * (|t| ^ 12 * terr) + |t| ^ 12 * terr := by gcongr
   _ ≤ 1 * (|t| ^ 12 * terr) + |t| ^ 12 * terr := by gcongr
   _ = (|t| ^ 10 * (2 * terr)) * |t| ^ 2 := by ring
   _ ≤ (1 * (2 * terr)) * |t| ^ 2 := by gcongr
   _ = 2 * terr * t ^ 2 := by rw [ht2]; ring
theorem abs_sc2_sub_tsc2_le {t : ℝ} (ht : |t| ≤ 1) : |sc2 t - tsc2 t| ≤ 5 * terr := by
 rcases eq_or_ne t 0 with rfl | h0
 · simp [sc2, tsc2, terr_pos.le]
 have hc := (cos_sin_taylor12' t ht).1
 have hs := (cos_sin_taylor12' t ht).2
 have hp : 0 < |t| := abs_pos.mpr h0
 have hp3 : 0 < |t ^ 3| := by positivity
 have e : sc2 t - tsc2 t
     = (-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t) + 2 * (Real.sin t - tsin t)) / t ^ 3 := by
   rw [sc2, if_neg h0]; unfold tsc2 tcos tsin; field_simp; ring
 rw [e, abs_div, div_le_iff₀ hp3, abs_pow]
 have h9 : |t| ^ 9 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
 have hsq : |t| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht
 have h0' := abs_nonneg t
 have hte := terr_pos.le
 have h12 : 0 ≤ |t| ^ 12 * terr := by positivity
 calc |-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t) + 2 * (Real.sin t - tsin t)|
     ≤ |t| ^ 2 * |Real.sin t - tsin t| + 2 * |t| * |Real.cos t - tcos t| + 2 * |Real.sin t - tsin t| := by
       have := abs_add_le (-t ^ 2 * (Real.sin t - tsin t) - 2 * t * (Real.cos t - tcos t)) (2 * (Real.sin t - tsin t))
       have h2 := abs_sub (-t ^ 2 * (Real.sin t - tsin t)) (2 * t * (Real.cos t - tcos t))
       rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_pow, abs_two] at *
       linarith
   _ ≤ 1 * (|t| ^ 12 * terr) + 2 * 1 * (|t| ^ 12 * terr) + 2 * (|t| ^ 12 * terr) := by gcongr
   _ = (|t| ^ 9 * (5 * terr)) * |t| ^ 3 := by ring
   _ ≤ (1 * (5 * terr)) * |t| ^ 3 := by gcongr
   _ = 5 * terr * |t| ^ 3 := by ring
end AMW
end
noncomputable section
open Real
namespace AMW.G
theorem DZ_eq : DZ = SC * 30517578125 := by norm_num [DZ, SC]
theorem pi_lo20 : ((PLN : ℕ) : ℝ) / E20 ≤ π := by
 have h := Real.pi_gt_d20; norm_num [PLN, E20] at h ⊢; linarith
theorem pi_hi20 : π ≤ ((PUN : ℕ) : ℝ) / E20 := by
 have h := Real.pi_lt_d20; norm_num [PUN, E20] at h ⊢; linarith
theorem ERRD_ge : terr ≤ (ERRD : ℝ) / DZ := by norm_num [terr, ERRD, DZ]
namespace CellA
variable (c : CellA)
theorem div_cancel_aux (u s q : ℕ) (hs : 0 < s) : u * (s * q) / s = u * q := by
 rw [show u * (s * q) = u * q * s by ring]; exact Nat.mul_div_cancel _ hs
theorem divc_cancel_aux (u s q : ℕ) (hs : 0 < s) : (u * (s * q) + s - 1) / s = u * q := by
 have h1 : u * (s * q) + s - 1 = (s - 1) + u * q * s := by
   have : 1 ≤ s := hs
   rw [show u * (s * q) = u * q * s by ring]; omega
 rw [h1, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt (by omega), Nat.zero_add]
theorem LLO_eq : c.LLO = c.LN * 30517578125 := by
 unfold LLO; rw [show Nat.mul c.LN DZ = c.LN * DZ from rfl, DZ_eq]
 exact div_cancel_aux _ _ _ (by norm_num [SC])
theorem UHI_eq : c.UHI = c.UN * 30517578125 := by
 unfold UHI ndivc; rw [show Nat.mul c.UN DZ = c.UN * DZ from rfl, DZ_eq]
 exact divc_cancel_aux _ _ _ (by norm_num [SC])
theorem LLO_div : (c.LLO : ℝ) / DZ = (c.LN : ℝ) / SC := by
 rw [LLO_eq]; push_cast; rw [DZ_eq]; push_cast; field_simp
theorem UHI_div : (c.UHI : ℝ) / DZ = (c.UN : ℝ) / SC := by
 rw [UHI_eq]; push_cast; rw [DZ_eq]; push_cast; field_simp
theorem AD_div : (c.AD : ℝ) / DZ = (c.k : ℝ) / 2 := by
 unfold AD; simp only [Nat.mul_eq]; push_cast; norm_num [DZ2, DZ]; ring
def roff (x : ℝ) : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x
theorem cosP_sub_cosN {T : ℕ} (hT : T ≤ DZ) : cosN T ≤ cosP T := by
 unfold cosP cosN DZp
 simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
 have h2 : T ^ 2 ≤ DZ ^ 2 := Nat.pow_le_pow_left hT 2
 have h6 : T ^ 6 ≤ DZ ^ 6 := Nat.pow_le_pow_left hT 6
 have h10 : T ^ 10 ≤ DZ ^ 10 := Nat.pow_le_pow_left hT 10
 have a1 : 1814400 * T ^ 2 * DZ ^ 8 ≤ 1814400 * DZ ^ 10 := by
   calc 1814400 * T ^ 2 * DZ ^ 8 ≤ 1814400 * DZ ^ 2 * DZ ^ 8 := by gcongr
     _ = 1814400 * DZ ^ 10 := by ring
 have a2 : 5040 * T ^ 6 * DZ ^ 4 ≤ 5040 * DZ ^ 10 := by
   calc 5040 * T ^ 6 * DZ ^ 4 ≤ 5040 * DZ ^ 6 * DZ ^ 4 := by gcongr
     _ = 5040 * DZ ^ 10 := by ring
 have : 0 ≤ 151200 * T ^ 4 * DZ ^ 6 + 90 * T ^ 8 * DZ ^ 2 := Nat.zero_le _
 omega
theorem sinP_sub_sinN {T : ℕ} (hT : T ≤ DZ) : sinN T ≤ sinP T := by
 unfold sinP sinN DZp
 simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
 have a1 : 6652800 * T ^ 3 * DZ ^ 8 ≤ 6652800 * T * DZ ^ 10 := by
   calc 6652800 * T ^ 3 * DZ ^ 8 = 6652800 * T * (T ^ 2 * DZ ^ 8) := by ring
     _ ≤ 6652800 * T * (DZ ^ 2 * DZ ^ 8) := by gcongr
     _ = 6652800 * T * DZ ^ 10 := by ring
 have a2 : 7920 * T ^ 7 * DZ ^ 4 ≤ 7920 * T * DZ ^ 10 := by
   calc 7920 * T ^ 7 * DZ ^ 4 = 7920 * T * (T ^ 6 * DZ ^ 4) := by ring
     _ ≤ 7920 * T * (DZ ^ 6 * DZ ^ 4) := by gcongr
     _ = 7920 * T * DZ ^ 10 := by ring
 have a3 : T ^ 11 ≤ T * DZ ^ 10 := by
   calc T ^ 11 = T * T ^ 10 := by ring
     _ ≤ T * DZ ^ 10 := by gcongr
 have : 0 ≤ 332640 * T ^ 5 * DZ ^ 6 + 110 * T ^ 9 * DZ ^ 2 := Nat.zero_le _
 nlinarith
theorem tcos_eq (T : ℕ) (h : cosN T ≤ cosP T) :
   tcos ((T : ℝ) / DZ) = ((Nat.sub (cosP T) (cosN T) : ℕ) : ℝ) / CDEN / DZ := by
 rw [show Nat.sub (cosP T) (cosN T) = cosP T - cosN T from rfl, Nat.cast_sub h]
 unfold tcos cosP cosN CDEN DZp
 simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
 push_cast
 have hD : (DZ : ℝ) ≠ 0 := by norm_num [DZ]
 field_simp
 ring
theorem tsin_eq (T : ℕ) (h : sinN T ≤ sinP T) :
   tsin ((T : ℝ) / DZ) = ((Nat.sub (sinP T) (sinN T) : ℕ) : ℝ) / SDEN / DZ := by
 rw [show Nat.sub (sinP T) (sinN T) = sinP T - sinN T from rfl, Nat.cast_sub h]
 unfold tsin sinP sinN SDEN DZp
 simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]
 push_cast
 have hD : (DZ : ℝ) ≠ 0 := by norm_num [DZ]
 field_simp
 ring
theorem cos_le_cos01 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : Real.cos b ≤ Real.cos a :=
 Real.cos_le_cos_of_nonneg_of_le_pi ha (hb.trans (by linarith [Real.pi_gt_three])) hab
theorem sin_le_sin01 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : Real.sin a ≤ Real.sin b :=
 Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (hb.trans (by linarith [Real.pi_gt_three])) hab
theorem abs_le_one_of {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : |t| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
structure Base (x : ℝ) : Prop where
 xlo : (c.LLO : ℝ) / DZ ≤ x
 xhi : x ≤ (c.UHI : ℝ) / DZ
 cx : c.CX.Enc (Real.cos (π * x))
 sx : c.SX.Enc (Real.sin (π * x))
 blo : (c.BLZ : ℝ) / DZ ≤ π * x
 bhi : π * x ≤ (c.BUZ : ℝ) / DZ
 e0 : 0 < c.E0
 elo : (c.E0 : ℝ) / DZ ≤ 2 * (π * x) ^ 2 - 1
 ehi : 2 * (π * x) ^ 2 - 1 ≤ (c.E1 : ℝ) / DZ
 r0 : 0 ≤ c.roff x
 tlo : (c.TLZ : ℝ) / DZ ≤ π * c.roff x
 thi : π * c.roff x ≤ (c.TUZ : ℝ) / DZ
 t1 : (c.TUZ : ℝ) / DZ ≤ 1
end CellA
theorem cos_sin_half (k : ℕ) :
   (Real.cos (π * ((k : ℝ) / 2)) = if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0) ∧
   (Real.sin (π * ((k : ℝ) / 2)) = if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0) := by
 have hk : (k : ℝ) = 4 * ((k / 4 : ℕ) : ℝ) + ((k % 4 : ℕ) : ℝ) := by
   have := Nat.div_add_mod k 4; exact_mod_cast this.symm
 have e : π * ((k : ℝ) / 2) = π * (((k % 4 : ℕ) : ℝ) / 2) + ((k / 4 : ℕ) : ℝ) * (2 * π) := by rw [hk]; ring
 rw [e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
 have hm : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
 interval_cases (k % 4) <;> simp <;> norm_num
 all_goals first
   | (rw [show π * (3 / 2) = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp)
   | (rw [show π * (3 / 2) = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two])
   | (rw [show π * (1 / 2) = π / 2 by ring]; simp)
   | skip
namespace CellA
variable (c : CellA)
theorem beq_val (m n : ℕ) : Nat.beq m n = decide (m = n) := by
 cases h : Nat.beq m n
 · have := Nat.ne_of_beq_eq_false h; simp [this]
 · have := Nat.eq_of_beq_eq_true h; simp [this]
theorem CX_val : c.CX = if c.km4 = 0 then c.CI else if c.km4 = 1 then (if c.side then c.SI.neg else c.SI)
   else if c.km4 = 2 then c.CI.neg else (if c.side then c.SI else c.SI.neg) := by
 unfold CX; simp only [beq_val]
 by_cases h0 : c.km4 = 0 <;> by_cases h1 : c.km4 = 1 <;> by_cases h2 : c.km4 = 2 <;> simp_all <;> cases c.side <;> rfl
theorem SX_val : c.SX = if c.km4 = 0 then (if c.side then c.SI else c.SI.neg) else if c.km4 = 1 then c.CI
   else if c.km4 = 2 then (if c.side then c.SI.neg else c.SI) else c.CI.neg := by
 unfold SX; simp only [beq_val]
 by_cases h0 : c.km4 = 0 <;> by_cases h1 : c.km4 = 1 <;> by_cases h2 : c.km4 = 2 <;> simp_all <;> cases c.side <;> rfl
theorem cx_sx_enc {x t : ℝ} (hx : π * x = π * ((c.k : ℝ) / 2) + (if c.side then t else -t))
   (hci : c.CI.Enc (Real.cos t)) (hsi : c.SI.Enc (Real.sin t)) :
   c.CX.Enc (Real.cos (π * x)) ∧ c.SX.Enc (Real.sin (π * x)) := by
 have hcs := cos_sin_half c.k
 have hkm : c.km4 = c.k % 4 := rfl
 rw [CX_val, SX_val, hx, Real.cos_add, Real.sin_add, hcs.1, hcs.2, hkm]
 have hm : c.k % 4 < 4 := Nat.mod_lt _ (by norm_num)
 have hsn := IV.enc_neg hsi
 have hcn := IV.enc_neg hci
 cases hs : c.side <;>
 · simp only [Bool.false_eq_true, if_true, if_false, Real.cos_neg, Real.sin_neg]
   interval_cases h4 : (c.k % 4)
   all_goals
     simp only [one_ne_zero, if_true, if_false,
       show ¬ ((1:ℕ) = 0) by norm_num, show ¬ ((2:ℕ) = 0) by norm_num, show ¬ ((3:ℕ) = 0) by norm_num,
       show ¬ ((2:ℕ) = 1) by norm_num, show ¬ ((3:ℕ) = 1) by norm_num, show ¬ ((3:ℕ) = 2) by norm_num,
       show ¬ ((0:ℕ) = 1) by norm_num, show ¬ ((0:ℕ) = 3) by norm_num, show ¬ ((1:ℕ) = 3) by norm_num,
       show ¬ ((2:ℕ) = 3) by norm_num, show ¬ ((0:ℕ) = 2) by norm_num, show ¬ ((1:ℕ) = 2) by norm_num]
     constructor
   all_goals first
     | (convert hci using 1; ring)
     | (convert hsi using 1; ring)
     | (convert hcn using 1; ring)
     | (convert hsn using 1; ring)
end CellA
namespace CellA
variable (c : CellA)
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
 rcases le_total b a with h | h
 · rw [Nat.cast_sub h]
 · rw [Nat.sub_eq_zero_of_le h]; have : (a : ℝ) ≤ b := by exact_mod_cast h
   simp only [Nat.cast_zero]; linarith
theorem nd_nonneg (a : ℕ) : (0 : ℝ) ≤ (a : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) DZ_pos.le
theorem err12 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |u| ^ 12 * terr ≤ terr :=
 mul_le_of_le_one_left terr_pos.le (pow_le_one₀ (abs_nonneg _) (abs_le_one_of h0 h1))
set_option maxHeartbeats 4000000 in
theorem base_sound (h : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.Base x := by
 unfold ok at h
 simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
 obtain ⟨⟨⟨hLU, hTU⟩, hside⟩, hE0⟩ := h
 have hD := DZ_pos
 have hSC : (0:ℝ) < SC := by norm_num [SC]
 have xlo : (c.LLO : ℝ) / DZ ≤ x := by rw [LLO_div]; exact hx1
 have xhi : x ≤ (c.UHI : ℝ) / DZ := by rw [UHI_div]; exact hx2
 have hL0 := nd_nonneg c.LLO
 have hx0 : 0 ≤ x := hL0.trans xlo
 have hAD := c.AD_div
 have hrlo : (c.RLO : ℝ) / DZ ≤ c.roff x ∧ c.roff x ≤ (c.RHI : ℝ) / DZ ∧ 0 ≤ c.roff x := by
   cases hs : c.side
   · rw [hs] at hside; simp only [Nat.ble_eq] at hside
     have hk : (c.UN : ℝ) / SC ≤ (c.k : ℝ) / 2 := by
       have : ((2 * c.UN : ℕ) : ℝ) ≤ ((c.k * SC : ℕ) : ℝ) := by exact_mod_cast hside
       push_cast at this; rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
     have h1 : c.UHI ≤ c.AD := by
       have : (c.UHI : ℝ) / DZ ≤ (c.AD : ℝ) / DZ := by rw [UHI_div, hAD]; exact hk
       exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
     have h2 : c.LLO ≤ c.AD := le_trans (by
       have : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := xlo.trans xhi
       exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this) h1
     have er : c.roff x = (c.k : ℝ) / 2 - x := by simp [roff, hs]
     refine ⟨?_, ?_, ?_⟩
     · simp only [RLO, hs]; rw [show Nat.sub c.AD c.UHI = c.AD - c.UHI from rfl, Nat.cast_sub h1, sub_div, hAD, er]
       linarith
     · simp only [RHI, hs]; rw [show Nat.sub c.AD c.LLO = c.AD - c.LLO from rfl, Nat.cast_sub h2, sub_div, hAD, er]
       linarith
     · rw [er]; linarith
   · rw [hs] at hside; simp only [Nat.ble_eq] at hside
     have hk : (c.k : ℝ) / 2 ≤ (c.LN : ℝ) / SC := by
       have : ((c.k * SC : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by exact_mod_cast hside
       push_cast at this; rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
     have h1 : c.AD ≤ c.LLO := by
       have : (c.AD : ℝ) / DZ ≤ (c.LLO : ℝ) / DZ := by rw [LLO_div, hAD]; exact hk
       exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
     have h2 : c.AD ≤ c.UHI := le_trans h1 (by
       have : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := xlo.trans xhi
       exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this)
     have er : c.roff x = x - (c.k : ℝ) / 2 := by simp [roff, hs]
     refine ⟨?_, ?_, ?_⟩
     · simp only [RLO, hs]; rw [show Nat.sub c.LLO c.AD = c.LLO - c.AD from rfl, Nat.cast_sub h1, sub_div, hAD, er]
       linarith
     · simp only [RHI, hs]; rw [show Nat.sub c.UHI c.AD = c.UHI - c.AD from rfl, Nat.cast_sub h2, sub_div, hAD, er]
       linarith
     · rw [er]; rw [LLO_div] at xlo; linarith
 obtain ⟨hr1, hr2, hr0⟩ := hrlo
 have tlo : (c.TLZ : ℝ) / DZ ≤ π * c.roff x := by
   unfold TLZ
   have h1 := ndiv_le (Nat.mul PLN c.RLO) E20 (by norm_num [E20])
   have e : ((Nat.mul PLN c.RLO : ℕ) : ℝ) = (PLN : ℝ) * c.RLO := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   calc ((Nat.div (Nat.mul PLN c.RLO) E20 : ℕ) : ℝ) / DZ ≤ ((PLN : ℝ) * c.RLO / E20) / DZ :=
         div_le_div_of_nonneg_right h1 hD.le
     _ = ((PLN : ℝ) / E20) * ((c.RLO : ℝ) / DZ) := by ring
     _ ≤ π * c.roff x := mul_le_mul pi_lo20 hr1 (nd_nonneg _) Real.pi_pos.le
 have thi : π * c.roff x ≤ (c.TUZ : ℝ) / DZ := by
   unfold TUZ
   have h1 := le_ndivc (Nat.mul PUN c.RHI) E20 (by norm_num [E20])
   have e : ((Nat.mul PUN c.RHI : ℕ) : ℝ) = (PUN : ℝ) * c.RHI := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   have hP0 : (0 : ℝ) ≤ (PUN : ℝ) / E20 := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   calc π * c.roff x ≤ ((PUN : ℝ) / E20) * ((c.RHI : ℝ) / DZ) := mul_le_mul pi_hi20 hr2 hr0 hP0
     _ = ((PUN : ℝ) * c.RHI / E20) / DZ := by ring
     _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
 have t1 : (c.TUZ : ℝ) / DZ ≤ 1 := by
   rw [div_le_one hD]; exact_mod_cast hTU
 have hTL1 : c.TLZ ≤ DZ := by
   have : (c.TLZ : ℝ) / DZ ≤ 1 := tlo.trans (thi.trans t1)
   rw [div_le_one hD] at this; exact_mod_cast this
 have hTL0 := nd_nonneg c.TLZ
 have ht0 : 0 ≤ π * c.roff x := mul_nonneg Real.pi_pos.le hr0
 have ht1 : π * c.roff x ≤ 1 := thi.trans t1
 have hTU0 : 0 ≤ (c.TUZ : ℝ) / DZ := ht0.trans thi
 have hTL1' : (c.TLZ : ℝ) / DZ ≤ 1 := tlo.trans ht1
 have hu' := err12 hTU0 t1
 have hl' := err12 hTL0 hTL1'
 have hcu := (cos_sin_taylor12' _ (abs_le_one_of hTU0 t1))
 have hcl := (cos_sin_taylor12' _ (abs_le_one_of hTL0 hTL1'))
 have hERR := ERRD_ge
 have hci : c.CI.Enc (Real.cos (π * c.roff x)) := by
   have hm1 := cos_le_cos01 ht0 thi t1
   have hm2 := cos_le_cos01 hTL0 tlo ht1
   have e1 := tcos_eq c.TUZ (cosP_sub_cosN hTU)
   have e2 := tcos_eq c.TLZ (cosP_sub_cosN hTL1)
   have f1 := div_le_div_of_nonneg_right (ndiv_le (Nat.sub (cosP c.TUZ) (cosN c.TUZ)) CDEN (by norm_num [CDEN, DZ])) hD.le
   have f2 := div_le_div_of_nonneg_right (le_ndivc (Nat.sub (cosP c.TLZ) (cosN c.TLZ)) CDEN (by norm_num [CDEN, DZ])) hD.le
   have a1 := (abs_le.mp hcu.1).1
   have a2 := (abs_le.mp hcl.1).2
   constructor
   · simp only [CI, SZ.v]; rw [sub_div]; linarith
   · simp only [CI, SZ.v, Nat.add_eq]; push_cast; rw [sub_zero, add_div]; linarith
 have hsi : c.SI.Enc (Real.sin (π * c.roff x)) := by
   have hm1 := sin_le_sin01 ht0 thi t1
   have hm2 := sin_le_sin01 hTL0 tlo ht1
   have e1 := tsin_eq c.TUZ (sinP_sub_sinN hTU)
   have e2 := tsin_eq c.TLZ (sinP_sub_sinN hTL1)
   have f1 := div_le_div_of_nonneg_right (ndiv_le (Nat.sub (sinP c.TLZ) (sinN c.TLZ)) SDEN (by norm_num [SDEN, DZ])) hD.le
   have f2 := div_le_div_of_nonneg_right (le_ndivc (Nat.sub (sinP c.TUZ) (sinN c.TUZ)) SDEN (by norm_num [SDEN, DZ])) hD.le
   have a1 := (abs_le.mp hcl.2).1
   have a2 := (abs_le.mp hcu.2).2
   constructor
   · simp only [SI, SZ.v]; rw [sub_div]; linarith
   · simp only [SI, SZ.v, Nat.add_eq]; push_cast; rw [sub_zero, add_div]; linarith
 have hx_eq : π * x = π * ((c.k : ℝ) / 2) + (if c.side then π * c.roff x else -(π * c.roff x)) := by
   cases hs : c.side <;> simp [roff, hs] <;> ring
 have hcxsx := c.cx_sx_enc hx_eq hci hsi
 have blo : (c.BLZ : ℝ) / DZ ≤ π * x := by
   unfold BLZ
   have h1 := ndiv_le (Nat.mul PLN c.LLO) E20 (by norm_num [E20])
   have e : ((Nat.mul PLN c.LLO : ℕ) : ℝ) = (PLN : ℝ) * c.LLO := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   calc ((Nat.div (Nat.mul PLN c.LLO) E20 : ℕ) : ℝ) / DZ ≤ ((PLN : ℝ) * c.LLO / E20) / DZ :=
         div_le_div_of_nonneg_right h1 hD.le
     _ = ((PLN : ℝ) / E20) * ((c.LLO : ℝ) / DZ) := by ring
     _ ≤ π * x := mul_le_mul pi_lo20 xlo hL0 Real.pi_pos.le
 have bhi : π * x ≤ (c.BUZ : ℝ) / DZ := by
   unfold BUZ
   have h1 := le_ndivc (Nat.mul PUN c.UHI) E20 (by norm_num [E20])
   have e : ((Nat.mul PUN c.UHI : ℕ) : ℝ) = (PUN : ℝ) * c.UHI := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   have hP0 : (0 : ℝ) ≤ (PUN : ℝ) / E20 := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   calc π * x ≤ ((PUN : ℝ) / E20) * ((c.UHI : ℝ) / DZ) := mul_le_mul pi_hi20 xhi hx0 hP0
     _ = ((PUN : ℝ) * c.UHI / E20) / DZ := by ring
     _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
 have hB0 := nd_nonneg c.BLZ
 have hpx0 : 0 ≤ π * x := hB0.trans blo
 have elo : (c.E0 : ℝ) / DZ ≤ 2 * (π * x) ^ 2 - 1 := by
   unfold E0 at hE0 ⊢
   have hle : DZ ≤ Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ := by
     by_contra hc; push_neg at hc
     rw [show Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ = Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ - DZ
       from rfl, Nat.sub_eq_zero_of_le hc.le] at hE0
     exact absurd hE0 (lt_irrefl 0)
   rw [show Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ = Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ - DZ
     from rfl, Nat.cast_sub hle, sub_div, div_self hD.ne']
   have h1 := ndiv_le (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ (by norm_num [DZ])
   have e : ((Nat.mul 2 (Nat.mul c.BLZ c.BLZ) : ℕ) : ℝ) = 2 * (c.BLZ : ℝ) * c.BLZ := by
     rw [Nat.mul_eq, Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   have hsq : ((c.BLZ : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ) ≤ (π * x) * (π * x) := mul_le_mul blo blo hB0 hpx0
   have : ((Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ : ℕ) : ℝ) / DZ ≤ 2 * (((c.BLZ : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ)) := by
     calc _ ≤ (2 * (c.BLZ : ℝ) * c.BLZ / DZ) / DZ := div_le_div_of_nonneg_right h1 hD.le
       _ = _ := by ring
   have hpq : (π * x) ^ 2 = (π * x) * (π * x) := sq _
   linarith
 have hE0r : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast hE0) hD
 have ehi : 2 * (π * x) ^ 2 - 1 ≤ (c.E1 : ℝ) / DZ := by
   unfold E1
   have h1 := le_ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ (by norm_num [DZ])
   have e : ((Nat.mul 2 (Nat.mul c.BUZ c.BUZ) : ℕ) : ℝ) = 2 * (c.BUZ : ℝ) * c.BUZ := by
     rw [Nat.mul_eq, Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   have hsq : (π * x) * (π * x) ≤ ((c.BUZ : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ) := mul_le_mul bhi bhi hpx0 (hpx0.trans bhi)
   have h2 : 2 * (((c.BUZ : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ)) ≤ ((ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ : ℕ) : ℝ) / DZ := by
     calc _ = (2 * (c.BUZ : ℝ) * c.BUZ / DZ) / DZ := by ring
       _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
   have hcast := natsub_ge (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ
   have h3 := div_le_div_of_nonneg_right hcast hD.le
   rw [sub_div, div_self hD.ne'] at h3
   have hpq : (π * x) ^ 2 = (π * x) * (π * x) := sq _
   have e3 : ((ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ - DZ : ℕ) : ℝ) = ((Nat.sub (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ : ℕ) : ℝ) := rfl
   rw [e3] at h3
   linarith
 exact ⟨xlo, xhi, hcxsx.1, hcxsx.2, blo, bhi, hE0, elo, ehi, hr0, tlo, thi, t1⟩
end CellA
end AMW.G
end
noncomputable section
open Real
namespace AMW.G
theorem sqrt2_half_bounds' :
   (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 / 2 ∧ Real.sqrt 2 / 2 ≤ 7071067811865475245/10^19 := by
 have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 constructor <;> nlinarith [h2, hnn]
theorem cos_sqrt2_half_bounds' :
   (7602445947/10^10 : ℝ) ≤ Real.cos (Real.sqrt 2 / 2) ∧ Real.cos (Real.sqrt 2 / 2) ≤ 7602445994/10^10 := by
 have hb := sqrt2_half_bounds'
 have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
 have hu : Real.sqrt 2 / 2 ≤ 1 := by linarith [hb.2]
 have hlo := CellA.cos_le_cos01 h0 hb.2 (by norm_num)
 have hhi := CellA.cos_le_cos01 (by norm_num) hb.1 hu
 have t1 := (cos_sin_taylor12' (7071067811865475245/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).1
 have t2 := (cos_sin_taylor12' (7071067811865475244/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).1
 have e1 : tcos (7071067811865475245/10^19 : ℝ) - terr ≥ 7602445947/10^10 := by unfold tcos terr; norm_num
 have e2 : tcos (7071067811865475244/10^19 : ℝ) + terr ≤ 7602445994/10^10 := by unfold tcos terr; norm_num
 have q1 : |(7071067811865475245/10^19 : ℝ)| ^ 12 * terr ≤ terr :=
   CellA.err12 (by norm_num) (by norm_num)
 have q2 : |(7071067811865475244/10^19 : ℝ)| ^ 12 * terr ≤ terr :=
   CellA.err12 (by norm_num) (by norm_num)
 constructor
 · linarith [(abs_le.mp t1).1]
 · linarith [(abs_le.mp t2).2]
theorem sin_sqrt2_half_bounds' :
   (6496369368/10^10 : ℝ) ≤ Real.sin (Real.sqrt 2 / 2) ∧ Real.sin (Real.sqrt 2 / 2) ≤ 6496369414/10^10 := by
 have hb := sqrt2_half_bounds'
 have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
 have hu : Real.sqrt 2 / 2 ≤ 1 := by linarith [hb.2]
 have hlo := CellA.sin_le_sin01 (by norm_num) hb.1 hu
 have hhi := CellA.sin_le_sin01 h0 hb.2 (by norm_num)
 have t1 := (cos_sin_taylor12' (7071067811865475244/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).2
 have t2 := (cos_sin_taylor12' (7071067811865475245/10^19 : ℝ) (by rw [abs_of_nonneg (by norm_num)]; norm_num)).2
 have e1 : tsin (7071067811865475244/10^19 : ℝ) - terr ≥ 6496369368/10^10 := by unfold tsin terr; norm_num
 have e2 : tsin (7071067811865475245/10^19 : ℝ) + terr ≤ 6496369414/10^10 := by unfold tsin terr; norm_num
 have q1 : |(7071067811865475244/10^19 : ℝ)| ^ 12 * terr ≤ terr := CellA.err12 (by norm_num) (by norm_num)
 have q2 : |(7071067811865475245/10^19 : ℝ)| ^ 12 * terr ≤ terr := CellA.err12 (by norm_num) (by norm_num)
 constructor
 · linarith [(abs_le.mp t1).1]
 · linarith [(abs_le.mp t2).2]
theorem gamAM_bounds : (8274992907/10^10 : ℝ) ≤ gamAM ∧ gamAM ≤ 8274993018/10^10 := by
 have hb := sqrt2_half_bounds'
 have hc := cos_sqrt2_half_bounds'
 have hs := sin_sqrt2_half_bounds'
 have h0 : (0:ℝ) ≤ Real.sqrt 2 / 2 := by linarith [hb.1]
 have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
 have hprodl : (7071067811865475244/10^19 : ℝ) * (7602445947/10^10) ≤ (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) :=
   mul_le_mul hb.1 hc.1 (by norm_num) h0
 have hprodu : (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) ≤ (7071067811865475245/10^19 : ℝ) * (7602445994/10^10) :=
   mul_le_mul hb.2 hc.2 (by linarith [hc.1]) (by norm_num)
 constructor
 · rw [gamAM, le_div_iff₀ hspos]; nlinarith [hprodl, hs.2]
 · rw [gamAM, div_le_iff₀ hspos]; nlinarith [hprodu, hs.1]
theorem rhoAM_eq : rhoAM = (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2) := by
 have hs : Real.sin (Real.sqrt 2 / 2) ≠ 0 := by linarith [sin_sqrt2_half_bounds'.1]
 have h2 : Real.sqrt 2 ≠ 0 := by positivity
 have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
 unfold rhoAM K0AM
 field_simp
 linarith [hsq]
theorem rhoAM_bounds : (1088464550157349/10^15 : ℝ) ≤ rhoAM ∧ rhoAM ≤ 1088464557864635/10^15 := by
 rw [rhoAM_eq]
 have hb := sqrt2_half_bounds'
 have hs := sin_sqrt2_half_bounds'
 have hspos : (0:ℝ) < Real.sin (Real.sqrt 2 / 2) := by linarith [hs.1]
 constructor
 · rw [le_div_iff₀ hspos]; nlinarith [hb.1, hs.2]
 · rw [div_le_iff₀ hspos]; nlinarith [hb.2, hs.1]
theorem pi_bounds15 : (3141592653589793/10^15 : ℝ) ≤ π ∧ π ≤ 3141592653589794/10^15 := by
 have h1 := Real.pi_gt_d20; have h2 := Real.pi_lt_d20
 constructor <;> norm_num at h1 h2 ⊢ <;> linarith
theorem enc_ofN {a b : ℕ} {v : ℝ} (h1 : (a : ℝ) / DZ ≤ v) (h2 : v ≤ (b : ℝ) / DZ) : (IV.ofN a b).Enc v := by
 simp only [IV.Enc, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact ⟨h1, h2⟩
theorem PIC_enc : PIC.Enc π := by
 have h := pi_bounds15
 refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]
theorem PI2C_enc : PI2C.Enc (π ^ 2) := by
 have h := pi_bounds15
 have h0 : (0:ℝ) ≤ 3141592653589793/10^15 := by norm_num
 refine enc_ofN ?_ ?_ <;> norm_num [DZ]
 · nlinarith [mul_le_mul h.1 h.1 h0 (h0.trans h.1)]
 · nlinarith [mul_le_mul h.2 h.2 (h0.trans h.1) (by norm_num : (0:ℝ) ≤ 3141592653589794/10^15)]
theorem G1C_enc : G1C.Enc (1 + 2 * gamAM) := by
 have h := gamAM_bounds
 refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]
theorem G2C_enc : G2C.Enc (1 + 4 * gamAM) := by
 have h := gamAM_bounds
 refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]
theorem GAM_bounds : (GAM0 : ℝ) / DZ ≤ 2 * gamAM ∧ 2 * gamAM ≤ (GAM1 : ℝ) / DZ := by
 have h := gamAM_bounds
 constructor <;> norm_num [GAM0, GAM1, DZ] <;> linarith [h.1, h.2]
theorem RHOC_enc : RHOC.Enc rhoAM := by
 have h := rhoAM_bounds
 refine enc_ofN ?_ ?_ <;> norm_num [DZ] <;> linarith [h.1, h.2]
theorem rhoAM_pos : 0 < rhoAM := by linarith [rhoAM_bounds.1]
theorem SIGC_enc : SIGC.Enc (rhoAM / π) := by
 have h := rhoAM_bounds
 have hp := pi_bounds15
 have hpp : 0 < π := Real.pi_pos
 refine enc_ofN ?_ ?_ <;> norm_num [DZ]
 · rw [le_div_iff₀ hpp]; nlinarith [h.1, hp.2]
 · rw [div_le_iff₀ hpp]; nlinarith [h.2, hp.1]
theorem TAUC_enc : TAUC.Enc (rhoAM * π) := by
 have h := rhoAM_bounds
 have hp := pi_bounds15
 refine enc_ofN ?_ ?_ <;> norm_num [DZ]
 · nlinarith [mul_le_mul h.1 hp.1 (by norm_num) rhoAM_pos.le]
 · nlinarith [mul_le_mul h.2 hp.2 Real.pi_pos.le (by norm_num)]
end AMW.G
end
end
section
/- Mechanical extraction of attempt016 at commit 296f7bb9c4e01b0c97554cf76af91ed99a410e8d,
   original physical lines 9511-20405; mathematical body retained byte-for-byte.
   Full original attribution retained above. Imports/global options and, where
   necessary, balanced closing ends are the only added commands. Source-only;
   no new compilation or acceptance claim. Original SHA256 5000dfb504e4cba831b3a7976974849f7574e2d7384a14f974b4a8bb02de2945.
-/
set_option linter.all false
set_option Elab.async false
noncomputable section
open Real
namespace AMW.G
def mf (n : ℕ) (j x : ℝ) : ℝ :=
 if n = 0 then x / (x ^ 2 - j ^ 2) else if n = 1 then -(x ^ 2 + j ^ 2) / (x ^ 2 - j ^ 2) ^ 2
 else 2 * x * (x ^ 2 + 3 * j ^ 2) / (x ^ 2 - j ^ 2) ^ 3
def hf (n : ℕ) (j x : ℝ) : ℝ :=
 if n = 0 then 1 / (2 * (x + j)) else if n = 1 then -1 / (2 * (x + j) ^ 2) else 1 / (x + j) ^ 3
def fv (n k j : ℕ) (x : ℝ) : ℝ := if 2 * j = k then hf n j x else mf n j x
def mmag (n : ℕ) (j x d : ℝ) : ℝ :=
 if n = 0 then x / d else if n = 1 then (x ^ 2 + j ^ 2) / d ^ 2 else 2 * x * (x ^ 2 + 3 * j ^ 2) / d ^ 3
def hmag (n : ℕ) (j x : ℝ) : ℝ :=
 if n = 0 then 1 / (2 * (x + j)) else if n = 1 then 1 / (2 * (x + j) ^ 2) else 1 / (x + j) ^ 3
theorem mf_above {n : ℕ} {j x : ℝ} : mf n j x = (if n = 1 then -1 else 1) * mmag n j x (x ^ 2 - j ^ 2) := by
 unfold mf mmag
 by_cases h0 : n = 0
 · subst h0; simp
 · by_cases h1 : n = 1
   · subst h1; simp; ring
   · simp [h0, h1]
theorem mf_below {n : ℕ} (hn : n < 3) {j x : ℝ} : mf n j x = -mmag n j x (j ^ 2 - x ^ 2) := by
 unfold mf mmag
 have e : x ^ 2 - j ^ 2 = -(j ^ 2 - x ^ 2) := by ring
 generalize j ^ 2 - x ^ 2 = d at e ⊢
 rw [e]
 interval_cases n
 · simp only [if_true]; rw [div_neg]
 · simp only [one_ne_zero, if_true, if_false]; rw [neg_sq, neg_div]
 · simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false]
   rw [show (-d) ^ 3 = -(d ^ 3) by ring, div_neg]
theorem hf_eq {n : ℕ} {j x : ℝ} : hf n j x = (if n = 1 then -1 else 1) * hmag n j x := by
 unfold hf hmag
 by_cases h0 : n = 0
 · subst h0; simp
 · by_cases h1 : n = 1
   · subst h1; simp only [one_ne_zero, if_true, if_false]; ring
   · simp [h0, h1]
theorem mmag_above_anti {n : ℕ} (hn : n < 3) {j a b : ℝ} (hj : 0 ≤ j) (ha : j < a) (hab : a ≤ b) :
   mmag n j b (b ^ 2 - j ^ 2) ≤ mmag n j a (a ^ 2 - j ^ 2) := by
 have ha' : 0 < a - j := by linarith
 have hb' : 0 < b - j := by linarith
 have hapj : 0 < a + j := by linarith
 have hbpj : 0 < b + j := by linarith
 have pf : ∀ x : ℝ, j < x → mmag n j x (x ^ 2 - j ^ 2) =
     if n = 0 then (1 / (x - j) + 1 / (x + j)) / 2 else if n = 1 then (1 / (x - j) ^ 2 + 1 / (x + j) ^ 2) / 2
     else 1 / (x - j) ^ 3 + 1 / (x + j) ^ 3 := by
   intro x hx
   have h1 : x - j ≠ 0 := by linarith
   have h2 : x + j ≠ 0 := by linarith
   have h3 : x ^ 2 - j ^ 2 = (x - j) * (x + j) := by ring
   unfold mmag; rw [h3]; split_ifs <;> field_simp <;> ring
 rw [pf b (by linarith), pf a ha]
 have m1 : ∀ p : ℕ, 1 / (b - j) ^ p ≤ 1 / (a - j) ^ p := fun p =>
   one_div_le_one_div_of_le (pow_pos ha' p) (pow_le_pow_left₀ ha'.le (by linarith) p)
 have m2 : ∀ p : ℕ, 1 / (b + j) ^ p ≤ 1 / (a + j) ^ p := fun p =>
   one_div_le_one_div_of_le (pow_pos hapj p) (pow_le_pow_left₀ hapj.le (by linarith) p)
 have m1' := m1 1; have m2' := m2 1; simp only [pow_one] at m1' m2'
 split_ifs
 · linarith
 · linarith [m1 2, m2 2]
 · linarith [m1 3, m2 3]
theorem mmag_below_mono {n : ℕ} (hn : n < 3) {j a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < j) :
   mmag n j a (j ^ 2 - a ^ 2) ≤ mmag n j b (j ^ 2 - b ^ 2) := by
 have hda : 0 < j ^ 2 - a ^ 2 := by nlinarith
 have hdb : 0 < j ^ 2 - b ^ 2 := by nlinarith
 have hd : j ^ 2 - b ^ 2 ≤ j ^ 2 - a ^ 2 := by nlinarith
 have hsq : a ^ 2 ≤ b ^ 2 := by nlinarith
 unfold mmag
 interval_cases n <;> simp only [show (1:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 0 by norm_num,
   show (2:ℕ) ≠ 1 by norm_num, if_true, if_false]
 · rw [div_le_div_iff₀ hda hdb]; nlinarith
 · rw [div_le_div_iff₀ (pow_pos hda 2) (pow_pos hdb 2)]
   have e1 : (j ^ 2 - b ^ 2) ^ 2 ≤ (j ^ 2 - a ^ 2) ^ 2 := pow_le_pow_left₀ hdb.le hd 2
   have e2 : a ^ 2 + j ^ 2 ≤ b ^ 2 + j ^ 2 := by linarith
   exact mul_le_mul e2 e1 (by positivity) (by positivity)
 · rw [div_le_div_iff₀ (pow_pos hda 3) (pow_pos hdb 3)]
   have e1 : (j ^ 2 - b ^ 2) ^ 3 ≤ (j ^ 2 - a ^ 2) ^ 3 := pow_le_pow_left₀ hdb.le hd 3
   have e2 : 2 * a * (a ^ 2 + 3 * j ^ 2) ≤ 2 * b * (b ^ 2 + 3 * j ^ 2) := by nlinarith
   have hb0 : 0 ≤ b := ha.trans hab
   exact mul_le_mul e2 e1 (pow_pos hdb 3).le (by positivity)
theorem hmag_anti {n : ℕ} {j a b : ℝ} (ha : 0 < a + j) (hab : a ≤ b) : hmag n j b ≤ hmag n j a := by
 have hb : 0 < b + j := by linarith
 have hle : a + j ≤ b + j := by linarith
 unfold hmag
 split_ifs
 · exact one_div_le_one_div_of_le (by linarith) (by linarith)
 · exact one_div_le_one_div_of_le (by have := pow_pos ha 2; linarith) (by nlinarith [pow_le_pow_left₀ ha.le hle 2])
 · exact one_div_le_one_div_of_le (pow_pos ha 3) (pow_le_pow_left₀ ha.le hle 3)
def AccEnc (a : Acc) (S : ℝ) : Prop := (a.pl : ℝ) - a.nh ≤ S ∧ S ≤ (a.ph : ℝ) - a.nl
theorem put_enc {a : Acc} {S : ℝ} (h : AccEnc a S) (ng : Bool) (e a0 a1 : ℕ) {m : ℝ}
   (h0 : (a0 : ℝ) ≤ m) (h1 : m ≤ a1) :
   AccEnc (a.put ng e a0 a1) (S + (if ng then -1 else 1) * e * m) := by
 have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
 have p0 := mul_le_mul_of_nonneg_left h0 he
 have p1 := mul_le_mul_of_nonneg_left h1 he
 unfold AccEnc at *; obtain ⟨hl, hh⟩ := h
 cases ng <;> simp only [Acc.put, Nat.add_eq, Nat.mul_eq, Bool.false_eq_true, if_true, if_false] <;> push_cast <;>
   constructor <;> nlinarith
theorem mnum_eq0 (X X2 J2 : ℕ) : mnum 0 X X2 J2 = X * DZ ^ 2 := rfl
theorem mnum_eq1 (X X2 J2 : ℕ) : mnum 1 X X2 J2 = (X2 + J2) * DZ ^ 3 := rfl
theorem mnum_eq2 (X X2 J2 : ℕ) : mnum 2 X X2 J2 = 2 * X * (X2 + 3 * J2) * DZ ^ 4 := rfl
theorem hden_eq0 (Y : ℕ) : hden 0 Y = 2 * Y := rfl
theorem hden_eq1 (Y : ℕ) : hden 1 Y = 2 * (Y * Y) := rfl
theorem hden_eq2 (Y : ℕ) : hden 2 Y = Y ^ 3 := rfl
theorem DZr_ne : (DZ : ℝ) ≠ 0 := DZ_pos.ne'
theorem mnum_div {n : ℕ} (hn : n < 3) (X : ℕ) (j : ℕ) (d : ℝ) (hd : d = (X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2 ∨
   d = ((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) (hd0 : d ≠ 0) :
   ((mnum n X (X * X) ((j * DZ) * (j * DZ)) : ℕ) : ℝ) / d ^ (n + 1)
     = DZ * mmag n j ((X : ℝ) / DZ) (d / DZ ^ 2) := by
 have hD := DZr_ne
 unfold mmag
 interval_cases n
 · rw [mnum_eq0]; simp only [if_true]; push_cast; field_simp
 · rw [mnum_eq1]; simp only [one_ne_zero, if_true, if_false]; push_cast
   rcases hd with hd | hd <;> (subst hd; push_cast at hd0; field_simp)
 · rw [mnum_eq2]; simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false]; push_cast
   rcases hd with hd | hd <;> (subst hd; push_cast at hd0; field_simp)
theorem hden_div {n : ℕ} (hn : n < 3) (X j : ℕ) (hY : 0 < X + j * DZ) :
   ((DZp (n + 2) : ℕ) : ℝ) / (hden n (X + j * DZ) : ℕ) = DZ * hmag n j ((X : ℝ) / DZ) := by
 have hD := DZr_ne
 have hY' : (0 : ℝ) < ((X + j * DZ : ℕ) : ℝ) := by exact_mod_cast hY
 push_cast at hY'
 unfold hmag DZp
 interval_cases n
 · rw [hden_eq0]; simp only [if_true, Nat.pow_eq]; push_cast; field_simp
 · rw [hden_eq1]; simp only [one_ne_zero, if_true, if_false, Nat.pow_eq]; push_cast; field_simp
 · rw [hden_eq2]; simp only [show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num, if_false, Nat.pow_eq]
   push_cast; field_simp
theorem sgn_xor (sg b : Bool) : (if xor sg b then (-1 : ℝ) else 1) = (if sg then -1 else 1) * (if b then -1 else 1) := by
 cases sg <;> cases b <;> simp
theorem hneg_eq (n : ℕ) : (if hneg n then (-1 : ℝ) else 1) = (if n = 1 then -1 else 1) := by
 unfold hneg; by_cases h : n = 1
 · subst h; simp
 · have : Nat.beq n 1 = false := by cases hb : Nat.beq n 1; rfl; exact absurd (Nat.eq_of_beq_eq_true hb) h
   simp [this, h]
theorem mneg_true (n : ℕ) : mneg n true = hneg n := by
 unfold mneg hneg; cases Nat.beq n 1 <;> rfl
theorem mneg_false (n : ℕ) : mneg n false = true := by
 unfold mneg; cases Nat.beq n 1 <;> rfl
theorem hden_pos {n : ℕ} (hn : n < 3) {Y : ℕ} (hY : 0 < Y) : 0 < hden n Y := by
 interval_cases n
 · rw [hden_eq0]; omega
 · rw [hden_eq1]; positivity
 · rw [hden_eq2]; positivity
set_option maxHeartbeats 2000000 in
theorem farJ_enc {n k XL XU : ℕ} (hn : n < 3) {x : ℝ} (hxl : (XL : ℝ) / DZ ≤ x) (hxu : x ≤ (XU : ℝ) / DZ)
   {a : Acc} {S : ℝ} (hS : AccEnc a S) (j e : ℕ) (sg : Bool) (hj : 1 ≤ j)
   (hab : 2 * j < k → (j : ℝ) < (XL : ℝ) / DZ) (hbe : k < 2 * j → (XU : ℝ) / DZ < j) :
   AccEnc (farJ n k XL XU (Nat.mul XL XL) (Nat.mul XU XU) a j e sg)
     (S + (if sg then -1 else 1) * e * (DZ * fv n k j x)) := by
 have hD := DZ_pos
 have hD0 : 0 < DZ := by norm_num [DZ]
 have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
 have hXL0 : (0 : ℝ) ≤ (XL : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 have hx0 : 0 ≤ x := hXL0.trans hxl
 unfold farJ fv
 simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq, Nat.pow_eq]
 by_cases hk : 2 * j = k
 · -- the near pole: the half term `h_j`
   have hb : Nat.beq (2 * j) k = true := by rw [hk]; exact Nat.beq_refl k
   simp only [hb, if_pos hk]
   have hY : ∀ X : ℕ, 0 < X + j * DZ := fun X => by have : 0 < j * DZ := Nat.mul_pos hj hD0; omega
   have h0 : ((Nat.div (DZp (n + 2)) (hden n (XU + j * DZ)) : ℕ) : ℝ) ≤ DZ * hmag n j x := by
     refine (ndiv_le _ _ (hden_pos hn (hY XU))).trans ?_
     rw [hden_div hn XU j (hY XU)]
     exact mul_le_mul_of_nonneg_left (hmag_anti (by linarith) hxu) hD.le
   have h1 : DZ * hmag n j x ≤ ((ndivc (DZp (n + 2)) (hden n (XL + j * DZ)) : ℕ) : ℝ) := by
     refine le_trans ?_ (le_ndivc _ _ (hden_pos hn (hY XL)))
     rw [hden_div hn XL j (hY XL)]
     exact mul_le_mul_of_nonneg_left (hmag_anti (by linarith) hxl) hD.le
   have := put_enc hS (xor sg (hneg n)) e _ _ h0 h1
   have key : (if sg then (-1:ℝ) else 1) * e * (DZ * hf n j x)
       = (if xor sg (hneg n) then -1 else 1) * e * (DZ * hmag n j x) := by rw [sgn_xor, hneg_eq, hf_eq]; ring
   rw [key]; exact this
 · have hb : Nat.beq (2 * j) k = false := by
     cases h : Nat.beq (2 * j) k; rfl; exact absurd (Nat.eq_of_beq_eq_true h) hk
   simp only [hb, if_neg hk]
   by_cases hlt : 2 * j < k
   · -- above the pole
     have hb2 : Nat.blt (2 * j) k = true := Nat.blt_eq.mpr hlt
     simp only [hb2]
     have hjx := hab hlt
     have hJ : (((j * DZ : ℕ) : ℝ) / DZ) = j := by push_cast; field_simp
     have hXLJ : j * DZ * (j * DZ) ≤ XL * XL := by
       have : (j : ℝ) * DZ < XL := by rwa [lt_div_iff₀ hD] at hjx
       have h2 : j * DZ ≤ XL := by exact_mod_cast this.le
       exact Nat.mul_le_mul h2 h2
     have hXUJ : j * DZ * (j * DZ) ≤ XU * XU := by
       have : (j : ℝ) * DZ < XU := by
         have := hjx.trans_le (hxl.trans hxu); rwa [lt_div_iff₀ hD] at this
       have h2 : j * DZ ≤ XU := by exact_mod_cast this.le
       exact Nat.mul_le_mul h2 h2
     have dpos : ∀ X : ℕ, (j : ℝ) < (X : ℝ) / DZ → (0 : ℝ) < (X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2 := by
       intro X hX
       have : (j : ℝ) * DZ < X := by rwa [lt_div_iff₀ hD] at hX
       have h1 : (0 : ℝ) < (X : ℝ) - j * DZ := by linarith
       have h2 : (0 : ℝ) < (X : ℝ) + j * DZ := by have := mul_pos (show (0:ℝ) < j by linarith) hD; linarith
       push_cast; nlinarith [mul_pos h1 h2]
     have dsc : ∀ X : ℕ, ((X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2) / DZ ^ 2 = ((X : ℝ) / DZ) ^ 2 - (j : ℝ) ^ 2 := by
       intro X; push_cast; field_simp
     have castd : ∀ X : ℕ, j * DZ * (j * DZ) ≤ X * X →
         (((X * X - j * DZ * (j * DZ)) ^ (n + 1) : ℕ) : ℝ) = ((X : ℝ) ^ 2 - ((j * DZ : ℕ) : ℝ) ^ 2) ^ (n + 1) := by
       intro X hX; push_cast [Nat.cast_sub hX]; ring
     have hxU : (j : ℝ) < (XU : ℝ) / DZ := hjx.trans_le (hxl.trans hxu)
     have h0 : ((Nat.div (mnum n XU (XU * XU) (j * DZ * (j * DZ))) ((XU * XU - j * DZ * (j * DZ)) ^ Nat.succ n) : ℕ) : ℝ)
         ≤ DZ * mmag n j x (x ^ 2 - j ^ 2) := by
       refine (ndiv_le _ _ (pow_pos (by have := dpos XU hxU; push_cast at this; exact_mod_cast (show (0:ℝ) < ((XU * XU - j * DZ * (j * DZ) : ℕ) : ℝ) by push_cast [Nat.cast_sub hXUJ]; nlinarith)) _)).trans ?_
       rw [castd XU hXUJ, mnum_div hn XU j _ (Or.inl rfl) (dpos XU hxU).ne', dsc]
       exact mul_le_mul_of_nonneg_left (mmag_above_anti hn (by positivity) (hjx.trans_le hxl) hxu) hD.le
     have h1 : DZ * mmag n j x (x ^ 2 - j ^ 2)
         ≤ ((ndivc (mnum n XL (XL * XL) (j * DZ * (j * DZ))) ((XL * XL - j * DZ * (j * DZ)) ^ Nat.succ n) : ℕ) : ℝ) := by
       refine le_trans ?_ (le_ndivc _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((XL * XL - j * DZ * (j * DZ) : ℕ) : ℝ) by push_cast [Nat.cast_sub hXLJ]; have := dpos XL hjx; push_cast at this; nlinarith)) _))
       rw [castd XL hXLJ, mnum_div hn XL j _ (Or.inl rfl) (dpos XL hjx).ne', dsc]
       exact mul_le_mul_of_nonneg_left (mmag_above_anti hn (by positivity) hjx hxl) hD.le
     have := put_enc hS (xor sg (mneg n true)) e _ _ h0 h1
     have key : (if sg then (-1:ℝ) else 1) * e * (DZ * mf n j x)
         = (if xor sg (mneg n true) then -1 else 1) * e * (DZ * mmag n j x (x ^ 2 - j ^ 2)) := by
       rw [sgn_xor, mneg_true, hneg_eq, mf_above]; ring
     rw [key]; exact this
   · -- below the pole
     have hgt : k < 2 * j := by omega
     have hb2 : Nat.blt (2 * j) k = false := by
       cases h : Nat.blt (2 * j) k; rfl; exact absurd (Nat.blt_eq.mp h) hlt
     simp only [hb2]
     have hxj := hbe hgt
     have hXUJ : XU * XU ≤ j * DZ * (j * DZ) := by
       have : (XU : ℝ) < j * DZ := by rwa [div_lt_iff₀ hD] at hxj
       have h2 : XU ≤ j * DZ := by exact_mod_cast this.le
       exact Nat.mul_le_mul h2 h2
     have hXLJ : XL * XL ≤ j * DZ * (j * DZ) := le_trans (Nat.mul_le_mul (by
       have : (XL : ℝ) ≤ XU := by have := hxl.trans hxu; rwa [div_le_div_iff_of_pos_right hD] at this
       exact_mod_cast this) (by
       have : (XL : ℝ) ≤ XU := by have := hxl.trans hxu; rwa [div_le_div_iff_of_pos_right hD] at this
       exact_mod_cast this)) hXUJ
     have dpos : ∀ X : ℕ, (X : ℝ) / DZ < j → (0 : ℝ) < ((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2 := by
       intro X hX
       have : (X : ℝ) < j * DZ := by rwa [div_lt_iff₀ hD] at hX
       have h0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
       have h1 : (0 : ℝ) < (j : ℝ) * DZ - X := by linarith
       have h2 : (0 : ℝ) < (j : ℝ) * DZ + X := by linarith
       push_cast; nlinarith [mul_pos h1 h2]
     have dsc : ∀ X : ℕ, (((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) / DZ ^ 2 = (j : ℝ) ^ 2 - ((X : ℝ) / DZ) ^ 2 := by
       intro X; push_cast; field_simp
     have castd : ∀ X : ℕ, X * X ≤ j * DZ * (j * DZ) →
         (((j * DZ * (j * DZ) - X * X) ^ (n + 1) : ℕ) : ℝ) = (((j * DZ : ℕ) : ℝ) ^ 2 - (X : ℝ) ^ 2) ^ (n + 1) := by
       intro X hX; push_cast [Nat.cast_sub hX]; ring
     have hxL : (XL : ℝ) / DZ < j := (hxl.trans hxu).trans_lt hxj
     have h0 : ((Nat.div (mnum n XL (XL * XL) (j * DZ * (j * DZ))) ((j * DZ * (j * DZ) - XL * XL) ^ Nat.succ n) : ℕ) : ℝ)
         ≤ DZ * mmag n j x (j ^ 2 - x ^ 2) := by
       refine (ndiv_le _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((j * DZ * (j * DZ) - XL * XL : ℕ) : ℝ) by push_cast [Nat.cast_sub hXLJ]; have := dpos XL hxL; push_cast at this; nlinarith)) _)).trans ?_
       rw [castd XL hXLJ, mnum_div hn XL j _ (Or.inr rfl) (dpos XL hxL).ne', dsc]
       exact mul_le_mul_of_nonneg_left (mmag_below_mono hn hXL0 hxl (hxu.trans_lt hxj)) hD.le
     have h1 : DZ * mmag n j x (j ^ 2 - x ^ 2)
         ≤ ((ndivc (mnum n XU (XU * XU) (j * DZ * (j * DZ))) ((j * DZ * (j * DZ) - XU * XU) ^ Nat.succ n) : ℕ) : ℝ) := by
       refine le_trans ?_ (le_ndivc _ _ (pow_pos (by exact_mod_cast (show (0:ℝ) < ((j * DZ * (j * DZ) - XU * XU : ℕ) : ℝ) by push_cast [Nat.cast_sub hXUJ]; have := dpos XU hxj; push_cast at this; nlinarith)) _))
       rw [castd XU hXUJ, mnum_div hn XU j _ (Or.inr rfl) (dpos XU hxj).ne', dsc]
       exact mul_le_mul_of_nonneg_left (mmag_below_mono hn hx0 hxu hxj) hD.le
     have := put_enc hS (xor sg (mneg n false)) e _ _ h0 h1
     have key : (if sg then (-1:ℝ) else 1) * e * (DZ * mf n j x)
         = (if xor sg (mneg n false) then -1 else 1) * e * (DZ * mmag n j x (j ^ 2 - x ^ 2)) := by
       rw [sgn_xor, mneg_false, mf_below hn]; simp
     rw [key]; exact this
def fsum (n k : ℕ) (x : ℝ) : List (ℕ × ℕ × Bool) → ℝ
 | [] => 0
 | (j, e, sg) :: rest => (if sg then -1 else 1) * e * fv n k j x + fsum n k x rest
theorem farAcc_enc {n k XL XU : ℕ} (hn : n < 3) {x : ℝ} (hxl : (XL : ℝ) / DZ ≤ x) (hxu : x ≤ (XU : ℝ) / DZ)
   (hsep : ∀ j : ℕ, 1 ≤ j → (2 * j < k → (j : ℝ) < (XL : ℝ) / DZ) ∧ (k < 2 * j → (XU : ℝ) / DZ < j)) :
   ∀ (L : List (ℕ × ℕ × Bool)), (∀ t ∈ L, 1 ≤ t.1) → ∀ (a : Acc) (S : ℝ), AccEnc a S →
     AccEnc (farAcc n k XL XU (Nat.mul XL XL) (Nat.mul XU XU) L a) (S + DZ * fsum n k x L) := by
 intro L
 induction L with
 | nil => intro _ a S h; simpa [farAcc, fsum] using h
 | cons t rest ih =>
   intro hL a S h
   obtain ⟨j, e, sg⟩ := t
   have hj : 1 ≤ j := hL _ (List.mem_cons_self ..)
   have h1 := farJ_enc hn hxl hxu h j e sg hj (hsep j hj).1 (hsep j hj).2
   have h2 := ih (fun t ht => hL t (List.mem_cons_of_mem _ ht)) _ _ h1
   simp only [farAcc, fsum]
   convert h2 using 1
   ring
theorem CE_pos : ∀ t ∈ CE, 1 ≤ t.1 := by decide
namespace CellA
variable (c : CellA)
theorem RHI_small (h : c.ok = true) : (c.RHI : ℝ) / DZ < 1 / 2 := by
 unfold ok at h
 simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
 have hTU := h.1.1.2
 have hD := DZ_pos
 have h1 := le_ndivc (Nat.mul PUN c.RHI) E20 (by norm_num [E20])
 have e : ((Nat.mul PUN c.RHI : ℕ) : ℝ) = (PUN : ℝ) * c.RHI := by rw [Nat.mul_eq]; push_cast; ring
 rw [e] at h1
 have h2 : ((ndivc (Nat.mul PUN c.RHI) E20 : ℕ) : ℝ) ≤ DZ := by exact_mod_cast hTU
 have h3 : (PUN : ℝ) * c.RHI ≤ E20 * DZ := by
   have := h1.trans h2; rw [div_le_iff₀ (by norm_num [E20])] at this; linarith
 have hP : (2 : ℝ) * E20 < PUN := by unfold PUN E20; norm_num
 have hE : (0 : ℝ) < E20 := by unfold E20; norm_num
 have hR0 : (0 : ℝ) ≤ c.RHI := Nat.cast_nonneg _
 rw [div_lt_iff₀ hD]
 by_contra hc; push_neg at hc
 have h4 : (PUN : ℝ) * (DZ / 2) ≤ PUN * c.RHI := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
 have h5 : 0 < ((PUN : ℝ) / 2 - E20) * DZ := mul_pos (by linarith) hD
 clear h hTU h1 h2 e
 linarith
theorem sep (h : c.ok = true) (j : ℕ) :
   (2 * j < c.k → (j : ℝ) < (c.LLO : ℝ) / DZ) ∧ (c.k < 2 * j → (c.UHI : ℝ) / DZ < j) := by
 have hR := c.RHI_small h
 unfold ok at h
 simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
 obtain ⟨⟨⟨hLU, hTU⟩, hside⟩, hE0⟩ := h
 have hD := DZ_pos
 have hSC : (0:ℝ) < SC := by norm_num [SC]
 have hAD := c.AD_div
 have hLU' : (c.LLO : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := by
   rw [LLO_div, UHI_div]; exact div_le_div_of_nonneg_right (by exact_mod_cast hLU) hSC.le
 cases hs : c.side
 · rw [hs] at hside; simp only [Nat.ble_eq] at hside
   have hk : (c.UHI : ℝ) / DZ ≤ (c.k : ℝ) / 2 := by
     rw [UHI_div]
     have : ((2 * c.UN : ℕ) : ℝ) ≤ ((c.k * SC : ℕ) : ℝ) := by exact_mod_cast hside
     push_cast at this; rw [div_le_div_iff₀ hSC (by norm_num)]; linarith
   have hLA : c.LLO ≤ c.AD := by
     have : (c.LLO : ℝ) / DZ ≤ (c.AD : ℝ) / DZ := by rw [hAD]; linarith
     exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
   have hRe : (c.RHI : ℝ) / DZ = (c.k : ℝ) / 2 - (c.LLO : ℝ) / DZ := by
     simp only [RHI, hs]; rw [show Nat.sub c.AD c.LLO = c.AD - c.LLO from rfl, Nat.cast_sub hLA, sub_div, hAD]
   constructor
   · intro hj
     have : (2 * j + 1 : ℝ) ≤ c.k := by exact_mod_cast hj
     linarith
   · intro hj
     have : (c.k + 1 : ℝ) ≤ 2 * j := by exact_mod_cast hj
     linarith
 · rw [hs] at hside; simp only [Nat.ble_eq] at hside
   have hk : (c.k : ℝ) / 2 ≤ (c.LLO : ℝ) / DZ := by
     rw [LLO_div]
     have : ((c.k * SC : ℕ) : ℝ) ≤ ((2 * c.LN : ℕ) : ℝ) := by exact_mod_cast hside
     push_cast at this; rw [div_le_div_iff₀ (by norm_num) hSC]; linarith
   have hAU : c.AD ≤ c.UHI := by
     have : (c.AD : ℝ) / DZ ≤ (c.UHI : ℝ) / DZ := by rw [hAD]; linarith
     exact_mod_cast (div_le_div_iff_of_pos_right hD).mp this
   have hRe : (c.RHI : ℝ) / DZ = (c.UHI : ℝ) / DZ - (c.k : ℝ) / 2 := by
     simp only [RHI, hs]; rw [show Nat.sub c.UHI c.AD = c.UHI - c.AD from rfl, Nat.cast_sub hAU, sub_div, hAD]
   constructor
   · intro hj
     have : (2 * j + 1 : ℝ) ≤ c.k := by exact_mod_cast hj
     linarith
   · intro hj
     have : (c.k + 1 : ℝ) ≤ 2 * j := by exact_mod_cast hj
     linarith
theorem FA_eq (n : ℕ) : c.FA n =
   (let a := farAcc n c.k c.LLO c.UHI (Nat.mul c.LLO c.LLO) (Nat.mul c.UHI c.UHI) CE ⟨0, 0, 0, 0⟩
    IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9) := rfl
theorem FA_enc (h : c.ok = true) {n : ℕ} (hn : n < 3) {x : ℝ} (hxl : (c.LLO : ℝ) / DZ ≤ x) (hxu : x ≤ (c.UHI : ℝ) / DZ) :
   (c.FA n).Enc (fsum n c.k x CE / E9) := by
 have hD := DZ_pos
 have hA := farAcc_enc hn hxl hxu (fun j _ => c.sep h j) CE CE_pos ⟨0, 0, 0, 0⟩ 0 (by simp [AccEnc])
 rw [zero_add] at hA
 rw [FA_eq]
 refine IV.enc_divn (by norm_num [E9]) ?_
 obtain ⟨h1, h2⟩ := hA
 constructor
 · simp only [SZ.v]; rw [div_le_iff₀ hD]; linarith
 · simp only [SZ.v]; rw [le_div_iff₀ hD]; linarith
end CellA
end AMW.G
end
noncomputable section
open Real
namespace AMW.G
theorem near_enc {P N : ℕ → ℕ} {Pr Nr f : ℝ → ℝ} {DEN E : ℕ} (hDEN : 0 < DEN)
   (hP : ∀ T : ℕ, (P T : ℝ) / DEN = DZ * Pr ((T : ℝ) / DZ)) (hN : ∀ T : ℕ, (N T : ℝ) / DEN = DZ * Nr ((T : ℝ) / DZ))
   (hPm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Pr u ≤ Pr v) (hNm : ∀ u v : ℝ, 0 ≤ u → u ≤ v → Nr u ≤ Nr v)
   {ε : ℝ} (hε : ε ≤ (E : ℝ) / DZ) (herr : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → |f u - (Pr u - Nr u)| ≤ ε)
   {TL TU : ℕ} {t : ℝ} (h0 : (TL : ℝ) / DZ ≤ t) (h1 : t ≤ (TU : ℝ) / DZ) (h2 : (TU : ℝ) / DZ ≤ 1) :
   (IV.mk ((SZ.fl ⟨P TL, N TU⟩ DEN).sub (SZ.ofN E)) ((SZ.ce ⟨P TU, N TL⟩ DEN).add (SZ.ofN E))).Enc (f t) := by
 have hD := DZ_pos
 have hTL0 : (0 : ℝ) ≤ (TL : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 have ht0 : 0 ≤ t := hTL0.trans h0
 have hE := (abs_le.mp (herr t ht0 (h1.trans h2)))
 constructor
 · simp only [SZ.v_sub, SZ.v_ofN, sub_div]
   have f1 := SZ.v_fl_le ⟨P TL, N TU⟩ hDEN
   have e : (SZ.v ⟨P TL, N TU⟩) / DEN = DZ * Pr ((TL : ℝ) / DZ) - DZ * Nr ((TU : ℝ) / DZ) := by
     simp only [SZ.v]; rw [sub_div, hP, hN]
   rw [e] at f1
   have m1 := hPm _ _ hTL0 h0
   have m2 := hNm _ _ ht0 h1
   have : (SZ.fl ⟨P TL, N TU⟩ DEN).v / DZ ≤ Pr ((TL : ℝ) / DZ) - Nr ((TU : ℝ) / DZ) := by
     rw [div_le_iff₀ hD]; linarith
   linarith
 · simp only [SZ.v_add, SZ.v_ofN, add_div]
   have f1 := SZ.le_v_ce ⟨P TU, N TL⟩ hDEN
   have e : (SZ.v ⟨P TU, N TL⟩) / DEN = DZ * Pr ((TU : ℝ) / DZ) - DZ * Nr ((TL : ℝ) / DZ) := by
     simp only [SZ.v]; rw [sub_div, hP, hN]
   rw [e] at f1
   have m1 := hPm _ _ ht0 h1
   have m2 := hNm _ _ hTL0 h0
   have : Pr ((TU : ℝ) / DZ) - Nr ((TL : ℝ) / DZ) ≤ (SZ.ce ⟨P TU, N TL⟩ DEN).v / DZ := by
     rw [le_div_iff₀ hD]; linarith
   linarith
def Ps0 (u : ℝ) : ℝ := 1 + u ^ 4 / 120 + u ^ 8 / 362880
def Ns0 (u : ℝ) : ℝ := u ^ 2 / 6 + u ^ 6 / 5040 + u ^ 10 / 39916800
def Ps1 (u : ℝ) : ℝ := u ^ 3 / 30 + u ^ 7 / 45360
def Ns1 (u : ℝ) : ℝ := u / 3 + u ^ 5 / 840 + u ^ 9 / 3991680
def Ps2 (u : ℝ) : ℝ := u ^ 2 / 10 + u ^ 6 / 6480 + u ^ 10 / 39916800
def Ns2 (u : ℝ) : ℝ := 1 / 3 + u ^ 4 / 168 + u ^ 8 / 443520
theorem DZr : (DZ : ℝ) = 10 ^ 15 := by norm_num [DZ]
theorem scP_eq (T : ℕ) : (scP T : ℝ) / SCDEN = DZ * Ps0 ((T : ℝ) / DZ) := by
 unfold scP Ps0 SCDEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem scN_eq (T : ℕ) : (scN T : ℝ) / SCDEN = DZ * Ns0 ((T : ℝ) / DZ) := by
 unfold scN Ns0 SCDEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem s1P_eq (T : ℕ) : (s1P T : ℝ) / S1DEN = DZ * Ps1 ((T : ℝ) / DZ) := by
 unfold s1P Ps1 S1DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem s1N_eq (T : ℕ) : (s1N T : ℝ) / S1DEN = DZ * Ns1 ((T : ℝ) / DZ) := by
 unfold s1N Ns1 S1DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem s2P_eq (T : ℕ) : (s2P T : ℝ) / S2DEN = DZ * Ps2 ((T : ℝ) / DZ) := by
 unfold s2P Ps2 S2DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem s2N_eq (T : ℕ) : (s2N T : ℝ) / S2DEN = DZ * Ns2 ((T : ℝ) / DZ) := by
 unfold s2N Ns2 S2DEN DZp; simp only [Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; push_cast
 rw [DZr]; field_simp; ring
theorem tsinc_split (u : ℝ) : tsinc u = Ps0 u - Ns0 u := by unfold tsinc Ps0 Ns0; ring
theorem tsc1_split (u : ℝ) : tsc1 u = Ps1 u - Ns1 u := by unfold tsc1 Ps1 Ns1; ring
theorem tsc2_split (u : ℝ) : tsc2 u = Ps2 u - Ns2 u := by unfold tsc2 Ps2 Ns2; ring
namespace CellA
variable (c : CellA)
theorem near_t (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   (c.TLZ : ℝ) / DZ ≤ π * c.roff x ∧ π * c.roff x ≤ (c.TUZ : ℝ) / DZ ∧ (c.TUZ : ℝ) / DZ ≤ 1 :=
 let b := c.base_sound hc hx1 hx2; ⟨b.tlo, b.thi, b.t1⟩
theorem S0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.S0.Enc (Real.sinc (π * c.roff x)) := by
 obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
 unfold S0
 refine near_enc (by norm_num [SCDEN, DZ]) scP_eq scN_eq ?_ ?_ ERRD_ge ?_ h0 h1 h2
 · intro u v hu huv; unfold Ps0; gcongr
 · intro u v hu huv; unfold Ns0; gcongr
 · intro u hu0 hu1; rw [← tsinc_split]; exact abs_sinc_sub_tsinc_le (CellA.abs_le_one_of hu0 hu1)
theorem G1_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.G1.Enc (sc1 (π * c.roff x)) := by
 obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
 unfold G1
 have he : 2 * terr ≤ ((Nat.mul 2 ERRD : ℕ) : ℝ) / DZ := by rw [Nat.mul_eq]; push_cast; norm_num [terr, ERRD, DZ]
 refine near_enc (by norm_num [S1DEN, DZ]) s1P_eq s1N_eq ?_ ?_ he ?_ h0 h1 h2
 · intro u v hu huv; unfold Ps1; gcongr
 · intro u v hu huv; unfold Ns1; gcongr
 · intro u hu0 hu1; rw [← tsc1_split]; exact abs_sc1_sub_tsc1_le (CellA.abs_le_one_of hu0 hu1)
theorem G2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.G2.Enc (sc2 (π * c.roff x)) := by
 obtain ⟨h0, h1, h2⟩ := c.near_t hc hx1 hx2
 unfold G2
 have he : 5 * terr ≤ ((Nat.mul 5 ERRD : ℕ) : ℝ) / DZ := by rw [Nat.mul_eq]; push_cast; norm_num [terr, ERRD, DZ]
 refine near_enc (by norm_num [S2DEN, DZ]) s2P_eq s2N_eq ?_ ?_ he ?_ h0 h1 h2
 · intro u v hu huv; unfold Ps2; gcongr
 · intro u v hu huv; unfold Ns2; gcongr
 · intro u hu0 hu1; rw [← tsc2_split]; exact abs_sc2_sub_tsc2_le (CellA.abs_le_one_of hu0 hu1)
end CellA
end AMW.G
end
noncomputable section
open Real
namespace AMW.G
theorem sin_pi_shift (x : ℝ) (j : ℕ) :
   Real.sin (π * (x - j)) = (-1) ^ j * Real.sin (π * x) ∧ Real.sin (π * (x + j)) = (-1) ^ j * Real.sin (π * x) := by
 constructor
 · rw [show π * (x - j) = π * x - j * π by ring, Real.sin_sub_nat_mul_pi]
 · rw [show π * (x + j) = π * x + j * π by ring, Real.sin_add_nat_mul_pi]
theorem cos_pi_shift (x : ℝ) (j : ℕ) :
   Real.cos (π * (x - j)) = (-1) ^ j * Real.cos (π * x) ∧ Real.cos (π * (x + j)) = (-1) ^ j * Real.cos (π * x) := by
 constructor
 · rw [show π * (x - j) = π * x - j * π by ring, Real.cos_sub_nat_mul_pi]
 · rw [show π * (x + j) = π * x + j * π by ring, Real.cos_add_nat_mul_pi]
theorem sinc_q {y : ℝ} (hy : y ≠ 0) : Real.sinc (π * y) = Real.sin (π * y) / (π * y) :=
 Real.sinc_of_ne_zero (mul_ne_zero Real.pi_pos.ne' hy)
theorem sc1_q {y : ℝ} (hy : y ≠ 0) :
   sc1 (π * y) = (π * y * Real.cos (π * y) - Real.sin (π * y)) / (π * y) ^ 2 := by
 rw [sc1, if_neg (mul_ne_zero Real.pi_pos.ne' hy)]
theorem sc2_q {y : ℝ} (hy : y ≠ 0) :
   sc2 (π * y) = (-(π * y) ^ 2 * Real.sin (π * y) - 2 * (π * y) * Real.cos (π * y) + 2 * Real.sin (π * y)) / (π * y) ^ 3 := by
 rw [sc2, if_neg (mul_ne_zero Real.pi_pos.ne' hy)]
variable {x : ℝ} {j : ℕ}
theorem T0_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
   (Real.sinc (π * (x - j)) + Real.sinc (π * (x + j))) / 2 = (-1) ^ j * (Real.sin (π * x) / π) * mf 0 j x := by
 have hπ := Real.pi_pos.ne'
 have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
   rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
 rw [sinc_q h1, sinc_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, mf, if_pos rfl]
 field_simp; ring
theorem T1_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
   (sc1 (π * (x - j)) + sc1 (π * (x + j))) / 2
     = (-1) ^ j * ((Real.cos (π * x) / π) * mf 0 j x + (Real.sin (π * x) / π ^ 2) * mf 1 j x) := by
 have hπ := Real.pi_pos.ne'
 have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
   rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
 rw [sc1_q h1, sc1_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, (cos_pi_shift x j).1, (cos_pi_shift x j).2]
 unfold mf; simp only [if_pos rfl, one_ne_zero, if_false, if_true]
 field_simp; ring
theorem T2_far (h1 : x - j ≠ 0) (h2 : x + j ≠ 0) :
   (sc2 (π * (x - j)) + sc2 (π * (x + j))) / 2
     = (-1) ^ j * (-(Real.sin (π * x) / π) * mf 0 j x + 2 * (Real.cos (π * x) / π ^ 2) * mf 1 j x
         + (Real.sin (π * x) / π ^ 3) * mf 2 j x) := by
 have hπ := Real.pi_pos.ne'
 have hd : x ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
   rw [show x ^ 2 - (j : ℝ) ^ 2 = (x - j) * (x + j) by ring]; exact mul_ne_zero h1 h2
 rw [sc2_q h1, sc2_q h2, (sin_pi_shift x j).1, (sin_pi_shift x j).2, (cos_pi_shift x j).1, (cos_pi_shift x j).2]
 unfold mf; simp only [if_pos rfl, one_ne_zero, if_false, if_true, show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num]
 field_simp; ring
theorem T0_near (h2 : x + j ≠ 0) :
   (Real.sinc (π * (x - j)) + Real.sinc (π * (x + j))) / 2
     = Real.sinc (π * (x - j)) / 2 + (-1) ^ j * (Real.sin (π * x) / π) * hf 0 j x := by
 have hπ := Real.pi_pos.ne'
 rw [sinc_q h2, (sin_pi_shift x j).2, hf, if_pos rfl]
 field_simp
theorem T1_near (h2 : x + j ≠ 0) :
   (sc1 (π * (x - j)) + sc1 (π * (x + j))) / 2
     = sc1 (π * (x - j)) / 2 + (-1) ^ j * ((Real.cos (π * x) / π) * hf 0 j x + (Real.sin (π * x) / π ^ 2) * hf 1 j x) := by
 have hπ := Real.pi_pos.ne'
 rw [sc1_q h2, (sin_pi_shift x j).2, (cos_pi_shift x j).2]
 unfold hf; simp only [if_pos rfl, one_ne_zero, if_false, if_true]
 field_simp; ring
theorem T2_near (h2 : x + j ≠ 0) :
   (sc2 (π * (x - j)) + sc2 (π * (x + j))) / 2
     = sc2 (π * (x - j)) / 2 + (-1) ^ j * (-(Real.sin (π * x) / π) * hf 0 j x
         + 2 * (Real.cos (π * x) / π ^ 2) * hf 1 j x + (Real.sin (π * x) / π ^ 3) * hf 2 j x) := by
 have hπ := Real.pi_pos.ne'
 rw [sc2_q h2, (sin_pi_shift x j).2, (cos_pi_shift x j).2]
 unfold hf; simp only [if_pos rfl, one_ne_zero, if_false, if_true, show (2:ℕ) ≠ 0 by norm_num, show (2:ℕ) ≠ 1 by norm_num]
 field_simp; ring
end AMW.G
end
noncomputable section
open Real
namespace AMW.G
theorem fsum_CE (n k : ℕ) (x : ℝ) :
   fsum n k x CE = E9 * ∑ m ∈ Finset.range 12, (-1) ^ (m + 1) * (cAM (m + 1) : ℝ) * fv n k (m + 1) x := by
 simp only [fsum, CE, Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn, E9]
 push_cast
 ring
theorem CJ_val {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ 12) :
   (if (CJ j).2 then (-1 : ℝ) else 1) * ((CJ j).1 : ℝ) / E9 = (cAM j : ℝ) := by
 interval_cases j <;> norm_num [CJ, cAM, cAMn, E9]
def nsel (k : ℕ) (f : ℕ → ℝ) : ℝ :=
 ∑ m ∈ Finset.range 12, if 2 * (m + 1) = k then (cAM (m + 1) : ℝ) * f (m + 1) / 2 else 0
theorem nsel_eq (k : ℕ) (f : ℕ → ℝ) :
   nsel k f = if (k % 2 = 0 ∧ 2 ≤ k ∧ k ≤ 24) then (cAM (k / 2) : ℝ) * f (k / 2) / 2 else 0 := by
 unfold nsel
 split_ifs with h
 · obtain ⟨h0, h1, h2⟩ := h
   rw [Finset.sum_eq_single (k / 2 - 1)]
   · rw [if_pos (by omega), show k / 2 - 1 + 1 = k / 2 by omega]
   · intro m _ hm; rw [if_neg]; omega
   · intro hm; exfalso; apply hm; rw [Finset.mem_range]; omega
 · apply Finset.sum_eq_zero; intro m hm; rw [Finset.mem_range] at hm; rw [if_neg]; omega
section sums
variable {k : ℕ} {x : ℝ} (hx : 0 < x) (hsep : ∀ j : ℕ, 1 ≤ j → 2 * j ≠ k → x ≠ j)
include hx hsep
theorem per_j_sep (m : ℕ) (hm : 2 * (m + 1) ≠ k) : x - ((m + 1 : ℕ) : ℝ) ≠ 0 :=
 sub_ne_zero.mpr (hsep (m + 1) (by omega) hm)
theorem per_j_pos (m : ℕ) : x + ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
theorem sum_T0 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * Tj n x
   = (Real.sin (π * x) / π) * (fsum 0 k x CE / E9) + nsel k (fun j => Real.sinc (π * (x - j))) := by
 rw [fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), Finset.mul_sum, nsel, ← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun m _ => ?_
 have e : Tj m x = (Real.sinc (π * (x - ((m + 1 : ℕ) : ℝ))) + Real.sinc (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
   unfold Tj; push_cast; ring_nf
 rw [e]
 by_cases hm : 2 * (m + 1) = k
 · rw [T0_near (per_j_pos hx hsep m), fv, if_pos hm, if_pos hm]; push_cast; ring
 · rw [T0_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, if_neg hm, if_neg hm]; push_cast; ring
theorem sum_T1 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T1j n x
   = (Real.cos (π * x) / π) * (fsum 0 k x CE / E9) + (Real.sin (π * x) / π ^ 2) * (fsum 1 k x CE / E9)
     + nsel k (fun j => sc1 (π * (x - j))) := by
 rw [fsum_CE, fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
   mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), Finset.mul_sum, Finset.mul_sum, nsel,
   ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun m _ => ?_
 have e : T1j m x = (sc1 (π * (x - ((m + 1 : ℕ) : ℝ))) + sc1 (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
   unfold T1j; push_cast; ring_nf
 rw [e]
 by_cases hm : 2 * (m + 1) = k
 · rw [T1_near (per_j_pos hx hsep m), fv, fv, if_pos hm, if_pos hm, if_pos hm]; push_cast; ring
 · rw [T1_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, fv, if_neg hm, if_neg hm, if_neg hm]; push_cast; ring
theorem sum_T2 : ∑ n ∈ Finset.range 12, (cAM (n + 1) : ℝ) * T2j n x
   = -(Real.sin (π * x) / π) * (fsum 0 k x CE / E9) + 2 * (Real.cos (π * x) / π ^ 2) * (fsum 1 k x CE / E9)
     + (Real.sin (π * x) / π ^ 3) * (fsum 2 k x CE / E9) + nsel k (fun j => sc2 (π * (x - j))) := by
 rw [fsum_CE, fsum_CE, fsum_CE, mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
   mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0), mul_div_cancel_left₀ _ (by norm_num [E9] : (E9 : ℝ) ≠ 0),
   Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, nsel,
   ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
 refine Finset.sum_congr rfl fun m _ => ?_
 have e : T2j m x = (sc2 (π * (x - ((m + 1 : ℕ) : ℝ))) + sc2 (π * (x + ((m + 1 : ℕ) : ℝ)))) / 2 := by
   unfold T2j; push_cast; ring_nf
 rw [e]
 by_cases hm : 2 * (m + 1) = k
 · rw [T2_near (per_j_pos hx hsep m), fv, fv, fv, if_pos hm, if_pos hm, if_pos hm, if_pos hm]; push_cast; ring
 · rw [T2_far (per_j_sep hx hsep m hm) (per_j_pos hx hsep m), fv, fv, fv, if_neg hm, if_neg hm, if_neg hm, if_neg hm]
   push_cast; ring
end sums
end AMW.G
end
noncomputable section
open Real
namespace AMW.G
namespace CellA
variable (c : CellA)
theorem x_pos (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : 0 < x := by
 have b := c.base_sound hc hx1 hx2
 have hE0 : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast b.e0) DZ_pos
 have hB0 : (0 : ℝ) ≤ (c.BLZ : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) DZ_pos.le
 have h1 := b.elo; have h2 := b.blo
 have hpx : 0 < π * x := by nlinarith
 exact pos_of_mul_pos_right hpx Real.pi_pos.le
theorem sepx (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   ∀ j : ℕ, 1 ≤ j → 2 * j ≠ c.k → x ≠ j := by
 have b := c.base_sound hc hx1 hx2
 intro j _ hj
 rcases Nat.lt_or_gt_of_ne hj with h | h
 · have := (c.sep hc j).1 h; linarith [b.xlo]
 · have := (c.sep hc j).2 h; linarith [b.xhi]
theorem PG_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.PG.Enc (2 * gamAM * (π * x)) := by
 have b := c.base_sound hc hx1 hx2
 have hD := DZ_pos
 have hg := GAM_bounds
 have hB0 : (0 : ℝ) ≤ (c.BLZ : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 have hG0 : (0 : ℝ) ≤ (GAM0 : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 refine enc_ofN ?_ ?_
 · have h1 := ndiv_le (Nat.mul GAM0 c.BLZ) DZ (by norm_num [DZ])
   have e : ((Nat.mul GAM0 c.BLZ : ℕ) : ℝ) = (GAM0 : ℝ) * c.BLZ := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   calc ((Nat.div (Nat.mul GAM0 c.BLZ) DZ : ℕ) : ℝ) / DZ ≤ ((GAM0 : ℝ) * c.BLZ / DZ) / DZ :=
         div_le_div_of_nonneg_right h1 hD.le
     _ = ((GAM0 : ℝ) / DZ) * ((c.BLZ : ℝ) / DZ) := by ring
     _ ≤ 2 * gamAM * (π * x) := mul_le_mul hg.1 b.blo hB0 (hG0.trans hg.1)
 · have h1 := le_ndivc (Nat.mul GAM1 c.BUZ) DZ (by norm_num [DZ])
   have e : ((Nat.mul GAM1 c.BUZ : ℕ) : ℝ) = (GAM1 : ℝ) * c.BUZ := by rw [Nat.mul_eq]; push_cast; ring
   rw [e] at h1
   have hpx : 0 ≤ π * x := hB0.trans b.blo
   calc 2 * gamAM * (π * x) ≤ ((GAM1 : ℝ) / DZ) * ((c.BUZ : ℝ) / DZ) :=
         mul_le_mul hg.2 b.bhi hpx (hG0.trans (hg.1.trans hg.2))
     _ = ((GAM1 : ℝ) * c.BUZ / DZ) / DZ := by ring
     _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
theorem NI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.NI.Enc (mN x) := by
 have b := c.base_sound hc hx1 hx2
 have h := IV.enc_sub b.cx (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.sx)
 unfold mN; exact h
theorem EI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.EI.Enc (-mD x) := by
 have b := c.base_sound hc hx1 hx2
 refine enc_ofN ?_ ?_ <;> unfold mD
 · linarith [b.elo]
 · linarith [b.ehi]
theorem BI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.BI.Enc (π * x) := by
 have b := c.base_sound hc hx1 hx2
 exact enc_ofN b.blo b.bhi
theorem mD_neg (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : mD x < 0 := by
 have b := c.base_sound hc hx1 hx2
 have hE0 : (0 : ℝ) < (c.E0 : ℝ) / DZ := div_pos (by exact_mod_cast b.e0) DZ_pos
 unfold mD; linarith [b.elo]
theorem nearOn_iff : c.nearOn = true ↔ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := by
 unfold nearOn; simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq]
 exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
theorem roff_near (hk : c.k % 2 = 0) (x : ℝ) :
   π * (x - ((c.k / 2 : ℕ) : ℝ)) = if c.side then π * c.roff x else -(π * c.roff x) := by
 have e : ((c.k / 2 : ℕ) : ℝ) = (c.k : ℝ) / 2 := by
   have := Nat.div_add_mod c.k 2; rw [hk] at this
   have h2 : ((2 * (c.k / 2) : ℕ) : ℝ) = (c.k : ℝ) := by exact_mod_cast (by omega : 2 * (c.k / 2) = c.k)
   push_cast at h2; linarith
 rw [e]; unfold roff; split_ifs <;> ring
theorem B0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.B0.Enc (nsel c.k (fun j => Real.sinc (π * (x - j)))) := by
 rw [nsel_eq]
 unfold B0
 cases hn : c.nearOn
 · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
   rw [if_neg this]; exact IV.enc_zero
 · have h := (c.nearOn_iff).mp hn
   rw [if_pos h]
   simp only
   have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9]) (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (c.S0_enc hc hx1 hx2))
   have hj0' : c.j0 = c.k / 2 := rfl
   have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
   have hr := c.roff_near h.1 x
   have hs : Real.sinc (π * (x - ((c.k / 2 : ℕ) : ℝ))) = Real.sinc (π * c.roff x) := by
     rw [hr]; split_ifs
     · rfl
     · exact Real.sinc_neg _
   rw [hj0'] at hv
   convert hS using 1
   rw [hs, hj0', ← hv, Nat.mul_eq]; push_cast; ring
theorem B1_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.B1.Enc (π * nsel c.k (fun j => sc1 (π * (x - j)))) := by
 rw [nsel_eq]
 unfold B1
 cases hn : c.nearOn
 · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
   rw [if_neg this, mul_zero]; exact IV.enc_zero
 · have h := (c.nearOn_iff).mp hn
   rw [if_pos h]
   simp only
   have hG : (Bool.rec (motive := fun _ => IV) c.G1.neg c.G1 c.side).Enc (sc1 (π * (x - ((c.k / 2 : ℕ) : ℝ)))) := by
     rw [c.roff_near h.1 x]
     cases hs : c.side
     · simp only [Bool.false_eq_true, if_false, sc1_neg]; exact IV.enc_neg (c.G1_enc hc hx1 hx2)
     · simp only [if_true]; exact c.G1_enc hc hx1 hx2
   have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9])
     (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (IV.enc_mulc PIC_enc (by simp [PIC, IV.ofN, SZ.v]) hG))
   have hj0' : c.j0 = c.k / 2 := rfl
   have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
   rw [hj0'] at hv
   convert hS using 1
   rw [hj0', ← hv, Nat.mul_eq]; push_cast; ring
theorem B2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.B2.Enc (π ^ 2 * nsel c.k (fun j => sc2 (π * (x - j)))) := by
 rw [nsel_eq]
 unfold B2
 cases hn : c.nearOn
 · have : ¬ (c.k % 2 = 0 ∧ 2 ≤ c.k ∧ c.k ≤ 24) := fun h => by rw [(c.nearOn_iff).mpr h] at hn; exact absurd hn (by simp)
   rw [if_neg this, mul_zero]; exact IV.enc_zero
 · have h := (c.nearOn_iff).mp hn
   rw [if_pos h]
   simp only
   have hG : c.G2.Enc (sc2 (π * (x - ((c.k / 2 : ℕ) : ℝ)))) := by
     rw [c.roff_near h.1 x]
     split_ifs
     · exact c.G2_enc hc hx1 hx2
     · rw [sc2_neg]; exact c.G2_enc hc hx1 hx2
   have hS := IV.enc_divn (d := Nat.mul 2 E9) (by norm_num [E9])
     (IV.enc_scl (CJ c.j0).2 (CJ c.j0).1 (IV.enc_mulc PI2C_enc (by simp [PI2C, IV.ofN, SZ.v]) hG))
   have hj0' : c.j0 = c.k / 2 := rfl
   have hv := CJ_val (j := c.j0) (by rw [hj0']; omega) (by rw [hj0']; omega)
   rw [hj0'] at hv
   convert hS using 1
   rw [hj0', ← hv, Nat.mul_eq]; push_cast; ring
theorem K0_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.K0.Enc (kfunAM x) := by
 have b := c.base_sound hc hx1 hx2
 have hD := c.mD_neg hc hx1 hx2
 have hx0 := c.x_pos hc hx1 hx2
 have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
 have h1 := IV.enc_divp (I := c.NI.neg) b.e0 b.elo b.ehi (IV.enc_neg (c.NI_enc hc hx1 hx2))
 have h2 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF0)
 have h3 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B0_enc hc hx1 hx2)
 have h := IV.enc_add h1 (IV.enc_add h2 h3)
 unfold K0 SF0
 convert h using 1
 rw [kfunAM_eq hD.ne, sum_T0 hx0 (c.sepx hc hx1 hx2)]
 have hE : 2 * (π * x) ^ 2 - 1 = -mD x := by unfold mD; ring
 rw [hE]
 have hπ := Real.pi_pos.ne'
 field_simp
end CellA
theorem prod_lo_nat (a b : ℕ) {A B : ℝ} (hA : (a : ℝ) / DZ ≤ A) (hB : (b : ℝ) / DZ ≤ B) :
   ((Nat.div (Nat.mul a b) DZ : ℕ) : ℝ) / DZ ≤ A * B := by
 have hD := DZ_pos
 have h1 := ndiv_le (Nat.mul a b) DZ (by norm_num [DZ])
 have e : ((Nat.mul a b : ℕ) : ℝ) = (a : ℝ) * b := by rw [Nat.mul_eq]; push_cast; ring
 rw [e] at h1
 have ha : (0 : ℝ) ≤ (a : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 have hb : (0 : ℝ) ≤ (b : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 calc ((Nat.div (Nat.mul a b) DZ : ℕ) : ℝ) / DZ ≤ ((a : ℝ) * b / DZ) / DZ := div_le_div_of_nonneg_right h1 hD.le
   _ = ((a : ℝ) / DZ) * ((b : ℝ) / DZ) := by ring
   _ ≤ A * B := mul_le_mul hA hB hb (ha.trans hA)
theorem prod_hi_nat (a b : ℕ) {A B : ℝ} (hA : A ≤ (a : ℝ) / DZ) (hB : B ≤ (b : ℝ) / DZ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
   A * B ≤ ((ndivc (Nat.mul a b) DZ : ℕ) : ℝ) / DZ := by
 have hD := DZ_pos
 have h1 := le_ndivc (Nat.mul a b) DZ (by norm_num [DZ])
 have e : ((Nat.mul a b : ℕ) : ℝ) = (a : ℝ) * b := by rw [Nat.mul_eq]; push_cast; ring
 rw [e] at h1
 calc A * B ≤ ((a : ℝ) / DZ) * ((b : ℝ) / DZ) := mul_le_mul hA hB hB0 (hA0.trans hA)
   _ = ((a : ℝ) * b / DZ) / DZ := by ring
   _ ≤ _ := div_le_div_of_nonneg_right h1 hD.le
namespace CellA
variable (c : CellA)
theorem E_bounds (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   (c.E2L : ℝ) / DZ ≤ mD x ^ 2 ∧ mD x ^ 2 ≤ (c.E2U : ℝ) / DZ ∧
     (c.E3L : ℝ) / DZ ≤ (-mD x) ^ 3 ∧ (-mD x) ^ 3 ≤ (c.E3U : ℝ) / DZ := by
 have hEI := c.EI_enc hc hx1 hx2
 have b := c.base_sound hc hx1 hx2
 have hD := DZ_pos
 have e0 : (c.E0 : ℝ) / DZ ≤ -mD x := by unfold mD; linarith [b.elo]
 have e1 : -mD x ≤ (c.E1 : ℝ) / DZ := by unfold mD; linarith [b.ehi]
 have hE0 : (0 : ℝ) ≤ (c.E0 : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 have hm : 0 ≤ -mD x := hE0.trans e0
 have s2 : mD x ^ 2 = (-mD x) * (-mD x) := by ring
 have l2 : (c.E2L : ℝ) / DZ ≤ mD x ^ 2 := by rw [s2]; exact prod_lo_nat c.E0 c.E0 e0 e0
 have u2 : mD x ^ 2 ≤ (c.E2U : ℝ) / DZ := by rw [s2]; exact prod_hi_nat c.E1 c.E1 e1 e1 hm hm
 have s3 : (-mD x) ^ 3 = mD x ^ 2 * (-mD x) := by ring
 refine ⟨l2, u2, ?_, ?_⟩
 · rw [s3]; exact prod_lo_nat c.E2L c.E0 l2 e0
 · rw [s3]; exact prod_hi_nat c.E2U c.E1 u2 e1 (sq_nonneg _) hm
theorem MI_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.MI.Enc (mM x) := by
 have b := c.base_sound hc hx1 hx2
 have hX := IV.enc_add (IV.enc_mulc G1C_enc (by simp [G1C, IV.ofN, SZ.v]) b.sx)
   (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.cx)
 have h1 := IV.enc_mulc (c.EI_enc hc hx1 hx2) (by simp only [EI, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact Nat.cast_nonneg _) hX
 have h2 := IV.enc_mulc (IV.enc_muln 4 (c.BI_enc hc hx1 hx2)) (by simp [BI, IV.muln, IV.ofN, SZ.muln, SZ.v])
   (c.NI_enc hc hx1 hx2)
 have h := IV.enc_add h1 h2
 unfold MI; convert h using 1; unfold mM mNb; push_cast; ring
theorem K1_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.K1.Enc (k1AM x) := by
 have b := c.base_sound hc hx1 hx2
 have hD := c.mD_neg hc hx1 hx2
 have hx0 := c.x_pos hc hx1 hx2
 have hEb := c.E_bounds hc hx1 hx2
 have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
 have hF1 := c.FA_enc hc (n := 1) (by norm_num) b.xlo b.xhi
 have h1 := IV.enc_mulc PIC_enc (by simp [PIC, IV.ofN, SZ.v]) (IV.enc_divp (I := c.MI) hE2 hEb.1 hEb.2.1 (c.MI_enc hc hx1 hx2))
 have h2 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (IV.enc_mul b.cx hF0)
 have h3 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF1)
 have h4 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B1_enc hc hx1 hx2)
 have h := IV.enc_add h1 (IV.enc_add (IV.enc_add h2 h3) h4)
 unfold K1
 convert h using 1
 rw [k1AM_eq hD.ne, sum_T1 hx0 (c.sepx hc hx1 hx2)]
 have hπ := Real.pi_pos.ne'
 have hmD := hD.ne
 field_simp
theorem N2_enc (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.N2.Enc (mN2 x) := by
 have b := c.base_sound hc hx1 hx2
 have h := IV.enc_sub (IV.enc_mulc (c.PG_enc hc hx1 hx2) (by simp [PG, IV.ofN, SZ.v]) b.sx)
   (IV.enc_mulc G2C_enc (by simp [G2C, IV.ofN, SZ.v]) b.cx)
 unfold N2; convert h using 1; unfold mN2; ring
theorem K2_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x)
   (hx2 : x ≤ (c.UN : ℝ) / SC) : c.K2.Enc (k2AM x) := by
 have b := c.base_sound hc hx1 hx2
 have hD := c.mD_neg hc hx1 hx2
 have hx0 := c.x_pos hc hx1 hx2
 have hEb := c.E_bounds hc hx1 hx2
 have hF0 := c.FA_enc hc (n := 0) (by norm_num) b.xlo b.xhi
 have hF1 := c.FA_enc hc (n := 1) (by norm_num) b.xlo b.xhi
 have hF2 := c.FA_enc hc (n := 2) (by norm_num) b.xlo b.xhi
 have hE2enc : (IV.ofN c.E2L c.E2U).Enc (mD x ^ 2) := enc_ofN hEb.1 hEb.2.1
 have hP : c.PP.Enc (mP x) := by
   have h1 := IV.enc_mulc hE2enc (by simp [IV.ofN, SZ.v]) (c.N2_enc hc hx1 hx2)
   have h2 := IV.enc_muln 4 (IV.enc_mulc (c.EI_enc hc hx1 hx2) (by simp only [EI, IV.ofN, SZ.v, Nat.cast_zero, sub_zero]; exact Nat.cast_nonneg _) (c.NI_enc hc hx1 hx2))
   have h3 := IV.enc_muln 8 (IV.enc_mulc (c.BI_enc hc hx1 hx2) (by simp [BI, IV.ofN, SZ.v]) (c.MI_enc hc hx1 hx2))
   have h := IV.enc_add (IV.enc_sub h1 h2) h3
   unfold PP; convert h using 1; unfold mP; push_cast; ring
 have h1 := IV.enc_neg (IV.enc_mulc PI2C_enc (by simp [PI2C, IV.ofN, SZ.v])
   (IV.enc_divp (I := c.PP) hE3 hEb.2.2.1 hEb.2.2.2 hP))
 have h2 := IV.enc_muln 2 (IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (IV.enc_mul b.cx hF1))
 have h3 := IV.enc_mulc TAUC_enc (by simp [TAUC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF0)
 have h4 := IV.enc_mulc SIGC_enc (by simp [SIGC, IV.ofN, SZ.v]) (IV.enc_mul b.sx hF2)
 have h5 := IV.enc_mulc RHOC_enc (by simp [RHOC, IV.ofN, SZ.v]) (c.B2_enc hc hx1 hx2)
 have h := IV.enc_add h1 (IV.enc_add (IV.enc_sub h2 h3) (IV.enc_add h4 h5))
 unfold K2 SF0
 convert h using 1
 rw [k2AM_eq hD.ne, sum_T2 hx0 (c.sepx hc hx1 hx2)]
 have hπ := Real.pi_pos.ne'
 have hmD := hD.ne
 push_cast
 field_simp
 ring
end CellA
theorem SZ.max_le {a b : SZ} {c : ℝ} (ha : a.v ≤ c) (hb : b.v ≤ c) : (SZ.max a b).v ≤ c := by
 unfold SZ.max; cases a.le b
 · exact ha
 · exact hb
def mabs (I : IV) : SZ := SZ.max (SZ.ofN 0) (SZ.max I.lo I.hi.neg)
theorem mabs_nonneg (I : IV) : 0 ≤ (mabs I).v :=
 (SZ.le_v_max_left _ _).trans' (by simp [SZ.ofN, SZ.v])
theorem mabs_le {I : IV} {a : ℝ} (h : I.Enc a) : (mabs I).v ≤ |a| * DZ := by
 have hD := DZ_pos
 unfold mabs
 refine SZ.max_le (by simp [SZ.ofN, SZ.v]; positivity) (SZ.max_le ?_ ?_)
 · have := (div_le_iff₀ hD).mp h.1; nlinarith [le_abs_self a]
 · rw [SZ.v_neg]; have := (le_div_iff₀ hD).mp h.2; nlinarith [neg_abs_le a]
namespace CellA
variable (c : CellA)
theorem KA_eq : c.KA = mabs c.K0 := rfl
def KAn (c : CellA) : ℕ := Nat.sub c.KA.p c.KA.n
theorem KAn_eq : (c.KAn : ℝ) = c.KA.v := by
 have h := c.KA_eq ▸ mabs_nonneg c.K0
 unfold KAn SZ.v at *
 have hle : c.KA.n ≤ c.KA.p := by exact_mod_cast (sub_nonneg.mp h)
 rw [show Nat.sub c.KA.p c.KA.n = c.KA.p - c.KA.n from rfl, Nat.cast_sub hle]
theorem w_lower (hc : c.ok = true) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   ((c.KAn : ℝ) / DZ) ^ 2 ≤ wfunAM x := by
 have hD := DZ_pos
 have hA : (c.KAn : ℝ) / DZ ≤ |kfunAM x| := by
   rw [KAn_eq, KA_eq, div_le_iff₀ hD]; exact mabs_le (c.K0_enc hc hx1 hx2)
 have hA0 : (0 : ℝ) ≤ (c.KAn : ℝ) / DZ := div_nonneg (Nat.cast_nonneg _) hD.le
 unfold wfunAM
 calc ((c.KAn : ℝ) / DZ) ^ 2 ≤ |kfunAM x| ^ 2 := pow_le_pow_left₀ hA0 hA 2
   _ = kfunAM x ^ 2 := sq_abs _
theorem w1_enc (hc : c.ok = true) (hE2 : 0 < c.E2L) {x : ℝ} (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   c.W1.Enc (w1AM x) := by
 have h := IV.enc_muln 2 (IV.enc_mul (c.K0_enc hc hx1 hx2) (c.K1_enc hc hE2 hx1 hx2))
 unfold W1 w1AM; convert h using 1; push_cast; ring
theorem W2L_eq : c.W2L = SZ.add (SZ.mul (mabs c.K1) (mabs c.K1)) ((c.K0.mul c.K2).lo.muln DZ) := rfl
theorem w2_nonneg (hc : c.ok = true) (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L) (hW : c.W2L.nonneg = true) {x : ℝ}
   (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : 0 ≤ w2AM x := by
 have hD := DZ_pos
 have hK1 := c.K1_enc hc hE2 hx1 hx2
 have hKK := IV.enc_mul (c.K0_enc hc hx1 hx2) (c.K2_enc hc hE2 hE3 hx1 hx2)
 have hW' := (SZ.nonneg_iff _).mp hW
 rw [W2L_eq, SZ.v_add, SZ.v_mul, SZ.v_muln] at hW'
 have hs0 := mabs_nonneg c.K1
 have hsk := mabs_le hK1
 have hsq : (mabs c.K1).v * (mabs c.K1).v ≤ (k1AM x) ^ 2 * DZ ^ 2 := by
   have := mul_le_mul hsk hsk hs0 (hs0.trans hsk)
   rw [show |k1AM x| * DZ * (|k1AM x| * DZ) = |k1AM x| ^ 2 * DZ ^ 2 by ring, sq_abs] at this; exact this
 have hq := hKK.1
 have hD2 : (0 : ℝ) < DZ ^ 2 := by positivity
 unfold w2AM
 generalize (c.K0.mul c.K2).lo.v = q at hq hW'
 generalize (mabs c.K1).v = sv at hsq hW'
 generalize kfunAM x * k2AM x = kk at hq ⊢
 generalize k1AM x = a at hsq ⊢
 have hq' : q ≤ kk * DZ := (div_le_iff₀ hD).mp hq
 have hkk : q * DZ ≤ kk * DZ ^ 2 := by
   have := mul_le_mul_of_nonneg_right hq' hD.le; linarith [show kk * DZ * DZ = kk * DZ ^ 2 by ring]
 have h3 : 0 ≤ (a ^ 2 + kk) * DZ ^ 2 := by linarith
 have := nonneg_of_mul_nonneg_left h3 hD2
 linarith
end CellA
end AMW.G
end
noncomputable section
namespace AMW.Cert
def SC : ℕ := 32768
def KB : ℕ := 1048576
def SW : ℕ := 10000000000000
def U1 : ℕ := 1000000000
def KU1 : ℕ := 2000000000
def wfun (x : ℝ) : ℝ := AMW.wfunAM x
def w1 (x : ℝ) : ℝ := AMW.w1AM x
def w2 (x : ℝ) : ℝ := AMW.w2AM x
def kD (_ : ℝ) : ℝ := -1
theorem kD_neg (x : ℝ) : kD x < 0 := by norm_num [kD]
theorem wfun_nonneg (x : ℝ) : 0 ≤ wfun x := AMW.wfunAM_nonneg x
theorem hasDerivAt_wfun (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt wfun (w1 x) x := AMW.hasDerivAt_wfunAM x
theorem hasDerivAt_w1 (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt w1 (w2 x) x := AMW.hasDerivAt_w1AM x
structure CellN where
 (key : ℕ) (WN : ℕ)
namespace CellN
def LN (c : CellN) : ℕ := c.key / KB
def UN (c : CellN) : ℕ := c.key % KB
def A (c : CellN) : AMW.G.CellA := ⟨c.LN, c.UN⟩
def okC (c : CellN) : Bool := c.A.ok
def NLOZ (c : CellN) : ℤ := (c.A.KAn : ℤ)
def DHIZ (c : CellN) : ℤ := (AMW.G.DZ : ℤ)
def WZ (c : CellN) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) 0 (Nat.div (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)) c.okC
def okD (c : CellN) : Bool := c.A.ok && Nat.blt 0 c.A.E2L
def W1LO (c : CellN) : ℤ := ((c.A.W1.lo.fl 1000000).p : ℤ) - ((c.A.W1.lo.fl 1000000).n : ℤ)
def W1HI (c : CellN) : ℤ := ((c.A.W1.hi.ce 1000000).p : ℤ) - ((c.A.W1.hi.ce 1000000).n : ℤ)
def convOk (c : CellN) : Bool := c.okD && Nat.blt 0 c.A.E3L && c.A.W2L.nonneg
end CellN
theorem cellN_soundZ' (c : CellN) (w : ℕ) (hc : c.okC = true)
   (hW : (w : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW) (x : ℝ)
   (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : (w : ℝ) / SW ≤ wfun x := by
 have hl := c.A.w_lower hc (x := x) hx1 hx2
 have hD := AMW.G.DZ_pos
 have hSW : (0 : ℝ) < SW := by norm_num [SW]
 have hWr : (w : ℝ) * AMW.G.DZ * AMW.G.DZ ≤ (c.A.KAn : ℝ) * c.A.KAn * SW := by
   have := (Int.cast_le (R := ℝ)).mpr hW
   simp only [CellN.DHIZ, CellN.NLOZ, Int.cast_mul, Int.cast_natCast] at this; exact this
 unfold wfun
 refine le_trans ?_ hl
 generalize (AMW.G.DZ : ℝ) = D at hD hWr ⊢
 generalize (c.A.KAn : ℝ) = K at hWr ⊢
 generalize (SW : ℝ) = S at hSW hWr ⊢
 rw [div_pow, div_le_div_iff₀ hSW (by positivity)]
 linarith
theorem cellN_soundWZ (c : CellN) (x : ℝ) (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   (c.WZ : ℝ) / SW ≤ wfun x := by
 unfold CellN.WZ
 cases hc : c.okC
 · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
 · simp only
   apply cellN_soundZ' c _ hc _ x hx1 hx2
   simp only [CellN.DHIZ, CellN.NLOZ]
   have h := Nat.div_mul_le_self (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)
   rw [show Nat.div (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)
     = Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW / Nat.mul AMW.G.DZ AMW.G.DZ from rfl]
   generalize Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW / Nat.mul AMW.G.DZ AMW.G.DZ = q at h ⊢
   simp only [Nat.mul_eq] at h
   have h' : ((q * (AMW.G.DZ * AMW.G.DZ) : ℕ) : ℤ) ≤ ((c.A.KAn * c.A.KAn * SW : ℕ) : ℤ) := by exact_mod_cast h
   push_cast at h'
   linarith
theorem cellD_sound (c : CellN) (hc : c.okD = true) (x : ℝ)
   (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
   kD x < 0 ∧ (c.W1LO : ℝ) / U1 ≤ w1 x ∧ w1 x ≤ (c.W1HI : ℝ) / U1 := by
 simp only [CellN.okD, Bool.and_eq_true, Nat.blt_eq] at hc
 have hW := c.A.w1_enc hc.1 hc.2 (x := x) hx1 hx2
 have hD := AMW.G.DZ_pos
 have hU : (0 : ℝ) < U1 := by norm_num [U1]
 have hm : (0 : ℕ) < 1000000 := by norm_num
 refine ⟨kD_neg x, ?_, ?_⟩
 · have h1 := AMW.G.SZ.v_fl_le c.A.W1.lo hm
   have e : ((c.W1LO : ℤ) : ℝ) = (c.A.W1.lo.fl 1000000).v := by
     simp only [CellN.W1LO, AMW.G.SZ.v]; push_cast; ring
   rw [e]; unfold w1
   have h2 := hW.1
   rw [div_le_iff₀ hU]
   have : c.A.W1.lo.v / ((1000000 : ℕ) : ℝ) = (c.A.W1.lo.v / AMW.G.DZ) * U1 := by norm_num [AMW.G.DZ, U1]; ring
   rw [this] at h1
   nlinarith
 · have h1 := AMW.G.SZ.le_v_ce c.A.W1.hi hm
   have e : ((c.W1HI : ℤ) : ℝ) = (c.A.W1.hi.ce 1000000).v := by
     simp only [CellN.W1HI, AMW.G.SZ.v]; push_cast; ring
   rw [e]; unfold w1
   have h2 := hW.2
   rw [le_div_iff₀ hU]
   have : c.A.W1.hi.v / ((1000000 : ℕ) : ℝ) = (c.A.W1.hi.v / AMW.G.DZ) * U1 := by norm_num [AMW.G.DZ, U1]; ring
   rw [this] at h1
   nlinarith
theorem cellConv_sound (c : CellN) (hc : c.convOk = true) (x : ℝ)
   (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) : kD x < 0 ∧ 0 ≤ w2 x := by
 simp only [CellN.convOk, CellN.okD, Bool.and_eq_true, Nat.blt_eq] at hc
 obtain ⟨⟨⟨hok, hE2⟩, hE3⟩, hW⟩ := hc
 exact ⟨kD_neg x, c.A.w2_nonneg hok hE2 hE3 hW hx1 hx2⟩
attribute [irreducible] CellN.okC CellN.NLOZ CellN.DHIZ CellN.WZ CellN.okD CellN.W1LO CellN.W1HI CellN.convOk
end AMW.Cert
end
noncomputable section
namespace AMW.Cert.Pyr
open AMW.Cert
def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a
def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295
def entB (X l i j : ℕ) : ℕ :=
 let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
 let d := Nat.sub 10 kk
 fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))
def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
   (Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
   (Nat.ble 11 l)
def nmin (a b : ℕ) : ℕ := Nat.sub a (Nat.sub a b)
def dstep (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
 let d := Nat.sub E g
 let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
 let h := Nat.shiftRight g t
 let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
 Bool.rec (motive := fun _ => ℕ) (nmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))
def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
 let E := Nat.add ib 1
 dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (fun _ => 0))))))))))))))
def BL8 : ℕ := 0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888877777777777777777777777777777777777777777777777777777777777777776666666666666666666666666666666655555555555555554444444433332210
def blen (x : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15)
   (Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)) (Nat.ble 256 x)
def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (let k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
      dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) (Nat.shiftRight lo k))
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
 Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f k) ih) n
def allFrom (a n : ℕ) (f : ℕ → Bool) : Bool :=
 Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f (Nat.add a k)) ih) n
def cellAt (l i : ℕ) : CellN := ⟨Nat.add (Nat.mul (Nat.shiftLeft i l) KB) (Nat.shiftLeft (Nat.add i 1) l), 0⟩
def cellOkCore (c : CellN) (v : ℕ) : Bool :=
 c.okC && decide (((Nat.mul v 1000 : ℕ) : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
def cellOk (l i v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false (cellOkCore (cellAt l i) v) (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
   true (Nat.beq v 0)
def blockOkX (X j : ℕ) : Bool :=
 let r := Nat.land X 31
 let D := Nat.sub 10 r
 let Y := Nat.shiftRight X 5
 Nat.ble r 10
   && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk r (Nat.add (Nat.shiftLeft j D) t) (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
   && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
        Nat.ble (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
          (nmin (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))
def blockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOkX X j) true (Nat.beq X 0)
def topv (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)
def topOk (top : ℕ) (bk : ℕ → ℕ) : Bool :=
 allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
   Nat.ble (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
     (nmin (topv top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))
theorem forceR_eq (a : ℕ) (k : ℕ → ℕ) : forceR a k = k a := by cases a <;> rfl
theorem nmin_eq (a b : ℕ) : nmin a b = min a b := by
 unfold nmin
 simp only [Nat.sub_eq]
 rcases le_total a b with h | h
 · rw [min_eq_left h, Nat.sub_eq_zero_of_le h, Nat.sub_zero]
 · rw [min_eq_right h, Nat.sub_sub_self h]
theorem allBelow_spec {n : ℕ} {f : ℕ → Bool} (h : allBelow n f = true) : ∀ i < n, f i = true := by
 induction n with
 | zero => intro i hi; omega
 | succ n ih =>
   have h' : Bool.rec (motive := fun _ => Bool) false (f n) (allBelow n f) = true := h
   cases hb : allBelow n f
   · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
   · rw [hb] at h'
     intro i hi
     rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
     · exact ih hb i hi
     · subst hi; exact h'
theorem allFrom_spec {a n : ℕ} {f : ℕ → Bool} (h : allFrom a n f = true) : ∀ i < n, f (a + i) = true := by
 induction n with
 | zero => intro i hi; omega
 | succ n ih =>
   have h' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add a n)) (allFrom a n f) = true := h
   cases hb : allFrom a n f
   · rw [hb] at h'; exact absurd (show (false : Bool) = true from h') (by decide)
   · rw [hb] at h'
     intro i hi
     rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
     · exact ih hb i hi
     · subst hi; exact h'
theorem allFrom_add {a n m : ℕ} {f : ℕ → Bool} (h1 : allFrom a n f = true) (h2 : allFrom (a + n) m f = true) :
   allFrom a (n + m) f = true := by
 induction m with
 | zero => exact h1
 | succ m ih =>
   have h2' : Bool.rec (motive := fun _ => Bool) false (f (Nat.add (a + n) m)) (allFrom (a + n) m f) = true := h2
   cases hb : allFrom (a + n) m f
   · rw [hb] at h2'; exact absurd (show (false : Bool) = true from h2') (by decide)
   · rw [hb] at h2'
     have h3 := ih hb
     show Bool.rec (motive := fun _ => Bool) false (f (Nat.add a (n + m))) (allFrom a (n + m) f) = true
     rw [h3]
     have e : Nat.add a (n + m) = Nat.add (a + n) m := by simp only [Nat.add_eq]; omega
     rw [e]; exact h2'
theorem blocks_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk (bk j) j) = true) :
   ∀ j < 512, blockOk (bk j) j = true := by
 intro j hj
 have := allFrom_spec h j hj
 simpa using this
def CS (l i v : ℕ) : Prop :=
 ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → (v : ℝ) / 10000000000 ≤ wfun x
theorem CS_zero (l i : ℕ) : CS l i 0 := by
 intro x _ _; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
theorem CS_mono {l i v v' : ℕ} (hv : v' ≤ v) (h : CS l i v) : CS l i v' := by
 intro x h1 h2
 exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hv) (by norm_num)) (h x h1 h2)
theorem SC_posR : (0:ℝ) < SC := by norm_num [SC]
theorem castdiv_le {a b : ℕ} (h : a ≤ b) : (a : ℝ) / SC ≤ (b : ℝ) / SC :=
 div_le_div_of_nonneg_right (by exact_mod_cast h) SC_posR.le
theorem CS_min {l i a b : ℕ} (ha : CS l (2 * i) a) (hb : CS l (2 * i + 1) b) : CS (l + 1) i (min a b) := by
 intro x h1 h2
 have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
 have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
 rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
 · have := ha x (by rw [e1]; exact h1) hx
   exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left a b) (by norm_num)) this
 · have := hb x hx (by rw [e2]; exact h2)
   exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right a b) (by norm_num)) this
theorem CS_anc {l m i v : ℕ} (h : CS (l + m) (i / 2 ^ m) v) : CS l i v := by
 intro x h1 h2
 have hp : 0 < 2 ^ m := by positivity
 apply h x
 · refine le_trans (castdiv_le ?_) h1
   calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
     _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
 · refine le_trans h2 (castdiv_le ?_)
   have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
     have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
   calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
     _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring
theorem cellOk_sound {l i v : ℕ} (h : cellOk l i v = true) : CS l i v := by
 unfold cellOk at h
 cases hv : Nat.beq v 0
 · rw [hv] at h
   cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
   · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
   · rw [hK] at h
     have h' : cellOkCore (cellAt l i) v = true := h
     simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
     obtain ⟨hc, hW⟩ := h'
     have hK' : (i + 1) * 2 ^ l < KB := by
       rw [Nat.ble_eq] at hK
       simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
     have hLN : (cellAt l i).LN = i * 2 ^ l := by
       simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
       rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
     have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
       simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
       rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
     intro x h1 h2
     have := cellN_soundZ' (cellAt l i) (Nat.mul v 1000) hc hW x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
     have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
       simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
     rw [e] at this; exact this
 · have : v = 0 := by rw [← Nat.beq_eq, hv]
   subst this; exact CS_zero l i
theorem fld_zero (i : ℕ) : fld 0 i = 0 := by
 simp [fld]
def BlockSound (X j : ℕ) : Prop :=
 X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS (10 - d) (j * 2 ^ d + t) (fld (X / 32) (2 ^ d - 1 + t))
theorem blockOkX_sound {X j : ℕ} (h : blockOkX X j = true) : BlockSound X j := by
 have hr : Nat.land X 31 = X % 32 := by
   rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
 have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
 unfold blockOkX at h
 simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
 obtain ⟨⟨h10, hfin⟩, hint⟩ := h
 refine ⟨h10, ?_⟩
 set D := Nat.sub 10 (X % 32) with hD
 have hD' : D = 10 - X % 32 := rfl
 have hfin' := allBelow_spec hfin
 have hint' := allBelow_spec hint
 suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld (X / 32) (2 ^ (D - e) - 1 + t)) by
   intro d hd t ht
   have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
   rwa [Nat.sub_sub_self (by omega)] at this
 intro e
 induction e with
 | zero =>
   intro _ t ht
   have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
   simp only [Nat.sub_zero]
   have hc := cellOk_sound this
   simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
   have e10 : 10 - D = X % 32 := by omega
   rw [e10]; exact hc
 | succ e ih =>
   intro he t ht
   set d := D - (e + 1) with hd
   have hdD : d < D := by omega
   have hde : D - e = d + 1 := by omega
   have hc := hint' d hdD
   have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
   simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
   have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
   have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
   rw [hde] at h0 h1
   have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
   have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
   rw [e0] at h0; rw [e1] at h1
   have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
   have hm := CS_min h0 h1
   rw [hlev] at hm
   refine CS_mono ?_ hm
   have a0 : 2 ^ (d + 1) - 1 + 2 * t = 2 ^ (d + 1) - 1 + 2 * t := rfl
   exact hct
theorem blockOk_sound {X j : ℕ} (h : blockOk X j = true) : BlockSound X j := by
 unfold blockOk at h
 cases hX : Nat.beq X 0
 · rw [hX] at h
   exact blockOkX_sound h
 · have : X = 0 := by rw [← Nat.beq_eq, hX]
   subst this
   refine ⟨by norm_num, fun d _ t _ => ?_⟩
   simp only [Nat.zero_div, fld_zero]; exact CS_zero _ _
theorem topv_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv top bk 10 i = fld (bk i / 32) 0 := by
 unfold topv
 rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
theorem topv_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
   topv top bk l i = fld top (2 ^ (19 - l) + i) := by
 unfold topv
 have : Nat.beq l 10 = false := by
   cases h : Nat.beq l 10
   · rfl
   · exact absurd (by rw [← Nat.beq_eq, h]) hl
 rw [this]
 simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
theorem top_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
   ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS (10 + e) i (topv top bk (10 + e) i) := by
 have ht' := allFrom_spec ht
 intro e
 induction e with
 | zero =>
   intro _ i hi
   rw [Nat.add_zero, topv_ten]
   have hB := blockOk_sound (hb i (by simpa using hi))
   have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
   simpa using this
 | succ e ih =>
   intro he i hi
   have hl := ht' e (by omega) |> allBelow_spec
   have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
   simp only [Nat.ble_eq, nmin_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
   have e1 : 11 + e - 1 = 10 + e := by omega
   rw [e1] at hle
   have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
   have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
   have hm := CS_min h0 h1
   rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
   rw [topv_top top bk (by omega)]
   refine CS_mono ?_ hm
   rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
   exact hle
theorem entry_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
   (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS l i (entry top bk l i) := by
 unfold entry
 cases h11 : Nat.ble 11 l
 · -- a block level
   have hl : l ≤ 10 := by
     have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
     omega
   show CS l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
   rw [forceR_eq]
   set j := Nat.shiftRight i (Nat.sub 10 l) with hj
   have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
   have hj512 : j < 512 := by
     rw [hj']
     have hi' := hi (by omega)
     rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
     rwa [show 9 + (10 - l) = 19 - l by omega]
   have hB := blockOk_sound (hb j hj512)
   set X := bk j
   unfold entB
   have hr : Nat.land X 31 = X % 32 := by
     rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
   simp only [hr]
   set r := X % 32
   have hr10 : r ≤ 10 := hB.1
   have hkk : Nat.add l (Nat.sub r l) = max l r := by
     simp only [Nat.add_eq, Nat.sub_eq, max_def]; split_ifs <;> omega
   simp only [hkk]
   set kk := max l r with hkkdef
   have hkk10 : kk ≤ 10 := by omega
   have hlkk : l ≤ kk := le_max_left _ _
   set d := Nat.sub 10 kk with hd
   have hd' : d = 10 - kk := rfl
   set q := i / 2 ^ (kk - l) with hq
   have hqj : q / 2 ^ d = j := by
     rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
     congr 2; omega
   have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
   have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
       = 2 ^ d - 1 + q % 2 ^ d := by
     simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
       Nat.shiftRight_eq_div_pow]
     rw [← hq]
     have := Nat.div_add_mod' q (2 ^ d)
     rw [hqj] at this
     congr 1; omega
   have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
   rw [hidx, hY]
   have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
   have e1 : j * 2 ^ d + q % 2 ^ d = q := by
     have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
   rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
   exact CS_anc hcs
 · cases h20 : Nat.ble 20 l
   · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
     have hl' : l ≤ 19 := by
       have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
       omega
     show CS l i (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
     have := top_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
     rw [show 10 + (l - 10) = l by omega, topv_top top bk (by omega)] at this
     simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
   · exact CS_zero l i
def DSound (k E : ℕ) (f : ℕ → ℕ) : Prop :=
 ∀ g, g < E → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC →
   (f g : ℝ) / 10000000000 ≤ wfun x
theorem DSound_zero (k E : ℕ) : DSound k E (fun _ => 0) := by
 intro g _ x _ _
 simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
theorem entry_ge20 (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (i : ℕ) (hl : 20 ≤ l) : entry top bk l i = 0 := by
 have h11 : Nat.ble 11 l = true := by rw [Nat.ble_eq]; omega
 have h20 : Nat.ble 20 l = true := by rw [Nat.ble_eq]; omega
 unfold entry
 rw [h11, h20]
theorem pack_hi (l h : ℕ) (hh : h < 2 ^ 40) : Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40 = l := by
 simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
 rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hh, Nat.zero_add]
theorem pack_lo (l h : ℕ) (hh : h < 2 ^ 40) : Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775 = h := by
 rw [Nat.land_eq, show (1099511627775 : ℕ) = 2 ^ 40 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
 simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
 rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hh]
theorem pack_ge (l h : ℕ) : l ≤ Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40 := by
 simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
 rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity)]
 omega
theorem entry_pack_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
   (l h : ℕ) (hi : l ≤ 19 → h < 2 ^ (19 - l)) :
   CS l h (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40) (Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775)) := by
 by_cases hl : l ≤ 19
 · have hh : h < 2 ^ 40 := lt_of_lt_of_le (hi hl) (Nat.pow_le_pow_right (by norm_num) (by omega))
   rw [pack_hi l h hh, pack_lo l h hh]
   exact entry_sound hb ht l h hi
 · rw [entry_ge20 top bk _ (le_trans (by omega) (pack_ge l h))]
   exact CS_zero l h
theorem dcore_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
   (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound k E ih)
   (g : ℕ) (hg : g < E) (x : ℝ) (h1 : ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x) (h2 : x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC) (t : ℕ) :
   ((Bool.rec (motive := fun _ => ℕ)
     (nmin (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
       (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
       (ih (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)))
     (entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
       (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
     (Nat.ble E (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)) : ℕ) : ℝ) / 10000000000 ≤ wfun x := by
 set h := Nat.shiftRight g t with hh
 have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
 set v := entry top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 40)
   (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 1099511627775) with hv
 set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
 have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
 have hcell : CS (Nat.add k t) h v := by
   rw [hv]
   apply entry_pack_sound hb ht
   intro hkt
   have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
   have hgib : g * 2 ^ k < 2 ^ 19 := by
     have := hk hk'
     calc g * 2 ^ k < E * 2 ^ k := Nat.mul_lt_mul_of_pos_right hg (by positivity)
       _ ≤ 2 ^ 19 := this
   rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
   have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
     rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
   by_contra hcon
   push_neg at hcon
   have := Nat.mul_le_mul_right (2 ^ k) hcon
   rw [e] at this; omega
 have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC →
     (v : ℝ) / 10000000000 ≤ wfun y := by
   intro y hy1 hy2
   apply hcell y
   · refine le_trans (castdiv_le ?_) hy1
     rw [hh', Nat.add_eq, pow_add]
     calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
       _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
   · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
     rw [hg'', Nat.add_eq, pow_add]; ring
 cases hc : Nat.ble E g'
 · have hle : g' < E := by
     have : ¬ E ≤ g' := by rw [← Nat.ble_eq, hc]; decide
     omega
   show ((nmin _ _ : ℕ) : ℝ) / 10000000000 ≤ wfun x
   rw [nmin_eq]
   rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
   · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) (by norm_num)) (hcellx x h1 hx)
   · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) (by norm_num)) (hih g' hle x hx h2)
 · have hgt : E ≤ g' := by rw [← Nat.ble_eq, hc]
   exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
theorem dstep_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
   (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound k E ih) :
   DSound k E (dstep top bk k E ih) := by
 intro g hg x h1 h2
 unfold dstep
 simp only [forceR_eq]
 exact dcore_sound hb ht k E hk hih g hg x h1 h2 _
theorem dcov_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true)
   (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
   ∀ g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
     (dcov top bk k ib g : ℝ) / 10000000000 ≤ wfun x := by
 intro g hg x h1 h2
 have hs : ∀ {f : ℕ → ℕ}, DSound k (Nat.add ib 1) f → DSound k (Nat.add ib 1) (dstep top bk k (Nat.add ib 1) f) :=
   fun hf => dstep_sound hb ht k (Nat.add ib 1) hk hf
 exact hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (DSound_zero k _)))))))))))))) g (by simp only [Nat.add_eq]; omega) x h1 h2
def LBSound (top : ℕ) (bk : ℕ → ℕ) : Prop :=
 ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → (lb top bk lo hi : ℝ) / 10000000000 ≤ wfun x
theorem lb_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk (bk j) j = true) (ht : topOk top bk = true) :
   LBSound top bk := by
 intro lo hi x h1 h2
 unfold lb
 cases hlo : Nat.ble hi lo
 · cases hhi : Nat.ble 524289 hi
   · have hlh : lo < hi := by
       have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
       omega
     have hhi' : hi ≤ 524288 := by
       have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
       omega
     show ((dcov top bk (blen (Nat.shiftRight (Nat.sub hi lo) 5)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 5)))
       (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 5))) : ℕ) : ℝ) / 10000000000 ≤ wfun x
     set k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
     simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
     have hp : 0 < 2 ^ k := by positivity
     apply dcov_sound hb ht k ((hi - 1) / 2 ^ k)
     · intro hk
       have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
         rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
       calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
         _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
     · exact Nat.div_le_div_right (by omega)
     · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
     · refine le_trans h2 (castdiv_le ?_)
       have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
       have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
       rw [e]
       generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
       generalize 2 ^ k = P at h5 ⊢
       omega
   · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
 · simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg x
end AMW.Cert.Pyr
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def forceB (a : ℕ) (k : ℕ → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) a
def cellOkD (sgn : Bool) (l i v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false
     ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
       (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn)
     (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
   true (Nat.beq v 0)
def ptOk (x v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false (cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v) (Nat.ble (Nat.add x 1) KB))
   true (Nat.beq v 0)
end AMW.Cert.PyrD
end
section MvtPairDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def fld2 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 64 i)) 18446744073709551615
def lo32 (v : ℕ) : ℕ := Nat.land v 4294967295
def hi32 (v : ℕ) : ℕ := Nat.shiftRight v 32
def pmin (a b : ℕ) : ℕ :=
 Nat.add (Nat.sub (Nat.land a 4294967295) (Nat.sub (Nat.land a 4294967295) (Nat.land b 4294967295)))
   (Nat.shiftLeft (Nat.sub (Nat.shiftRight a 32) (Nat.sub (Nat.shiftRight a 32) (Nat.shiftRight b 32))) 32)
def ple (a b : ℕ) : Bool := Nat.ble (lo32 a) (lo32 b) && Nat.ble (hi32 a) (hi32 b)
def entB2 (X l i j : ℕ) : ℕ :=
 let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
 let d := Nat.sub 10 kk
 fld2 (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))
def entry2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
   (Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
   (Nat.ble 11 l)
def dstep2 (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
 let d := Nat.sub E g
 let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
 let h := Nat.shiftRight g t
 let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry2 top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
 Bool.rec (motive := fun _ => ℕ) (pmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))
def dcov2 (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
 let E := Nat.add ib 1
 dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (fun _ => 0))))))))))))))
def cellOk2 (l i v : ℕ) : Bool := cellOkD true l i (lo32 v) && cellOkD false l i (hi32 v)
def blockOk2X (X j : ℕ) : Bool :=
 let r := Nat.land X 31
 let D := Nat.sub 10 r
 let Y := Nat.shiftRight X 5
 Nat.ble r 10
   && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk2 r (Nat.add (Nat.shiftLeft j D) t) (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
   && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
        ple (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
          (pmin (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))
def blockOk2 (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOk2X X j) true (Nat.beq X 0)
def topv2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld2 (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)
def topOk2 (top : ℕ) (bk : ℕ → ℕ) : Bool :=
 allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
   ple (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
     (pmin (topv2 top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv2 top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))
end AMW.Cert.PyrD
end MvtPairDefs
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def fD (sgn : Bool) (x : ℝ) : ℝ := if sgn then w1 x + 2 else 2 - w1 x
def CSD (sgn : Bool) (l i v : ℕ) : Prop :=
 v ≠ 0 → ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC →
   kD x < 0 ∧ (v : ℝ) / U1 ≤ fD sgn x
theorem forceB_eq (a : ℕ) (k : ℕ → Bool) : forceB a k = k a := by cases a <;> rfl
theorem CSD_zero (sgn : Bool) (l i : ℕ) : CSD sgn l i 0 := fun h => absurd rfl h
theorem U1_posR : (0:ℝ) < U1 := by norm_num [U1]
theorem cellOkD_sound {sgn : Bool} {l i v : ℕ} (h : cellOkD sgn l i v = true) : CSD sgn l i v := by
 unfold cellOkD at h
 cases hv : Nat.beq v 0
 · rw [hv] at h
   cases hK : Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB
   · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
   · rw [hK] at h
     have h' : ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
         (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn) = true := h
     rw [Bool.and_eq_true] at h'
     obtain ⟨hok, hvb⟩ := h'
     have hK' : (i + 1) * 2 ^ l < KB := by
       rw [Nat.ble_eq] at hK
       simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq] at hK; omega
     have hLN : (cellAt l i).LN = i * 2 ^ l := by
       simp only [cellAt, CellN.LN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
       rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
     have hUN : (cellAt l i).UN = (i + 1) * 2 ^ l := by
       simp only [cellAt, CellN.UN, Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
       rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
     intro _ x h1 h2
     obtain ⟨hk, hlo, hhi⟩ := cellD_sound (cellAt l i) hok x (by rw [hLN]; exact h1) (by rw [hUN]; exact h2)
     refine ⟨hk, ?_⟩
     have hU1 := U1_posR
     have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
     cases sgn
     · have hv' : (v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI := of_decide_eq_true hvb
       have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((cellAt l i).W1HI : ℝ) := by exact_mod_cast hv'
       simp only [fD, ↓reduceIte, Bool.false_eq_true]
       rw [div_le_iff₀ hU1]
       have := (le_div_iff₀ hU1).mp hhi
       rw [eK] at hvr
       nlinarith
     · have hv' : (v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO := of_decide_eq_true hvb
       have hvr : (v : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((cellAt l i).W1LO : ℝ) := by exact_mod_cast hv'
       simp only [fD, ↓reduceIte]
       rw [div_le_iff₀ hU1]
       have := (div_le_iff₀ hU1).mp hlo
       rw [eK] at hvr
       nlinarith
 · have : v = 0 := by rw [← Nat.beq_eq, hv]
   subst this; exact CSD_zero sgn l i
theorem ptOk_sound {x v : ℕ} (h : ptOk x v = true) : (v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) := by
 unfold ptOk at h
 cases hv : Nat.beq v 0
 · rw [hv] at h
   cases hK : Nat.ble (Nat.add x 1) KB
   · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
   · rw [hK] at h
     have h' : cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v = true := h
     simp only [cellOkCore, Bool.and_eq_true, decide_eq_true_eq] at h'
     obtain ⟨hc, hW⟩ := h'
     have hK' : x < KB := by
       rw [Nat.ble_eq] at hK
       simp only [Nat.add_eq] at hK; omega
     have hLN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).LN = x := by
       simp only [CellN.LN, Nat.add_eq, Nat.mul_eq]
       rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
     have hUN : (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).UN = x := by
       simp only [CellN.UN, Nat.add_eq, Nat.mul_eq]
       rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
     have := cellN_soundZ' ⟨Nat.add (Nat.mul x KB) x, 0⟩ (Nat.mul v 1000) hc hW ((x : ℝ) / SC)
       (by rw [hLN]) (by rw [hUN])
     have e : ((Nat.mul v 1000 : ℕ) : ℝ) / SW = (v : ℝ) / 10000000000 := by
       simp only [Nat.mul_eq]; push_cast; norm_num [SW]; ring
     rw [e] at this; exact this
 · have : v = 0 := by rw [← Nat.beq_eq, hv]
   subst this; simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _
end AMW.Cert.PyrD
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def PS (v : ℕ) (x : ℝ) : Prop :=
 (lo32 v ≠ 0 → kD x < 0 ∧ (lo32 v : ℝ) / U1 ≤ fD true x) ∧
   (hi32 v ≠ 0 → kD x < 0 ∧ (hi32 v : ℝ) / U1 ≤ fD false x)
theorem lo32_eq (v : ℕ) : lo32 v = v % 2 ^ 32 := by
 unfold lo32
 rw [Nat.land_eq, show (4294967295 : ℕ) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
theorem hi32_eq (v : ℕ) : hi32 v = v / 2 ^ 32 := by
 unfold hi32
 rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
theorem pmin_def (a b : ℕ) :
   pmin a b = Nat.add (nmin (lo32 a) (lo32 b)) (Nat.shiftLeft (nmin (hi32 a) (hi32 b)) 32) := rfl
theorem pmin_lo (a b : ℕ) : lo32 (pmin a b) = min (lo32 a) (lo32 b) := by
 have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
 rw [pmin_def, nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, lo32_eq (min _ _ + _),
   Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha)]
theorem pmin_hi (a b : ℕ) : hi32 (pmin a b) = min (hi32 a) (hi32 b) := by
 have ha : lo32 a < 2 ^ 32 := by rw [lo32_eq]; exact Nat.mod_lt _ (by norm_num)
 rw [pmin_def, nmin_eq, nmin_eq, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, hi32_eq (min _ _ + _),
   Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt (lt_of_le_of_lt (min_le_left _ _) ha), Nat.zero_add]
theorem PS_zero (x : ℝ) : PS 0 x := ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩
theorem PS_mono {v v' : ℕ} {x : ℝ} (h : ple v' v = true) (hv : PS v x) : PS v' x := by
 unfold ple at h
 rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
 obtain ⟨h1, h2⟩ := h
 refine ⟨fun h0 => ?_, fun h0 => ?_⟩
 · obtain ⟨hk, hb⟩ := hv.1 (by omega)
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h1) U1_posR.le) hb⟩
 · obtain ⟨hk, hb⟩ := hv.2 (by omega)
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) U1_posR.le) hb⟩
theorem PS_pmin_left {a b : ℕ} {x : ℝ} (h : PS a x) : PS (pmin a b) x := by
 unfold PS
 rw [pmin_lo, pmin_hi]
 refine ⟨fun h0 => ?_, fun h0 => ?_⟩
 · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩
 · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.zero_min _))
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left _ _) U1_posR.le) hb⟩
theorem PS_pmin_right {a b : ℕ} {x : ℝ} (h : PS b x) : PS (pmin a b) x := by
 unfold PS
 rw [pmin_lo, pmin_hi]
 refine ⟨fun h0 => ?_, fun h0 => ?_⟩
 · obtain ⟨hk, hb⟩ := h.1 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩
 · obtain ⟨hk, hb⟩ := h.2 (fun h1 => h0 (by rw [h1]; exact Nat.min_zero _))
   exact ⟨hk, le_trans (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right _ _) U1_posR.le) hb⟩
def CS2 (l i v : ℕ) : Prop :=
 ∀ x : ℝ, ((i * 2 ^ l : ℕ) : ℝ) / SC ≤ x → x ≤ (((i + 1) * 2 ^ l : ℕ) : ℝ) / SC → PS v x
theorem CS2_zero (l i : ℕ) : CS2 l i 0 := fun x _ _ => PS_zero x
theorem CS2_mono {l i v v' : ℕ} (hv : ple v' v = true) (h : CS2 l i v) : CS2 l i v' :=
 fun x h1 h2 => PS_mono hv (h x h1 h2)
theorem CS2_min {l i a b : ℕ} (ha : CS2 l (2 * i) a) (hb : CS2 l (2 * i + 1) b) : CS2 (l + 1) i (pmin a b) := by
 intro x h1 h2
 have e1 : (2 * i) * 2 ^ l = i * 2 ^ (l + 1) := by rw [pow_succ]; ring
 have e2 : (2 * i + 1 + 1) * 2 ^ l = (i + 1) * 2 ^ (l + 1) := by rw [pow_succ]; ring
 rcases le_total x ((((2 * i + 1) * 2 ^ l : ℕ) : ℝ) / SC) with hx | hx
 · exact PS_pmin_left (ha x (by rw [e1]; exact h1) hx)
 · exact PS_pmin_right (hb x hx (by rw [e2]; exact h2))
theorem CS2_anc {l m i v : ℕ} (h : CS2 (l + m) (i / 2 ^ m) v) : CS2 l i v := by
 intro x h1 h2
 have hp : 0 < 2 ^ m := by positivity
 apply h x
 · refine le_trans (castdiv_le ?_) h1
   calc (i / 2 ^ m) * 2 ^ (l + m) = ((i / 2 ^ m) * 2 ^ m) * 2 ^ l := by rw [pow_add]; ring
     _ ≤ i * 2 ^ l := Nat.mul_le_mul_right _ (Nat.div_mul_le_self i (2 ^ m))
 · refine le_trans h2 (castdiv_le ?_)
   have hq : i + 1 ≤ (i / 2 ^ m + 1) * 2 ^ m := by
     have h3 := Nat.div_add_mod i (2 ^ m); have h4 := Nat.mod_lt i hp; nlinarith
   calc (i + 1) * 2 ^ l ≤ ((i / 2 ^ m + 1) * 2 ^ m) * 2 ^ l := Nat.mul_le_mul_right _ hq
     _ = (i / 2 ^ m + 1) * 2 ^ (l + m) := by rw [pow_add]; ring
theorem cellOk2_sound {l i v : ℕ} (h : cellOk2 l i v = true) : CS2 l i v := by
 unfold cellOk2 at h
 rw [Bool.and_eq_true] at h
 have hP := cellOkD_sound h.1
 have hM := cellOkD_sound h.2
 intro x h1 h2
 exact ⟨fun h0 => hP h0 x h1 h2, fun h0 => hM h0 x h1 h2⟩
theorem fld2_zero (i : ℕ) : fld2 0 i = 0 := by
 simp [fld2]
def BlockSound2 (X j : ℕ) : Prop :=
 X % 32 ≤ 10 ∧ ∀ d, d ≤ 10 - X % 32 → ∀ t < 2 ^ d, CS2 (10 - d) (j * 2 ^ d + t) (fld2 (X / 32) (2 ^ d - 1 + t))
theorem blockOk2X_sound {X j : ℕ} (h : blockOk2X X j = true) : BlockSound2 X j := by
 have hr : Nat.land X 31 = X % 32 := by
   rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
 have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
 unfold blockOk2X at h
 simp only [hr, hY, Bool.and_eq_true, Nat.ble_eq] at h
 obtain ⟨⟨h10, hfin⟩, hint⟩ := h
 refine ⟨h10, ?_⟩
 set D := Nat.sub 10 (X % 32) with hD
 have hD' : D = 10 - X % 32 := rfl
 have hfin' := allBelow_spec hfin
 have hint' := allBelow_spec hint
 suffices key : ∀ e, e ≤ D → ∀ t < 2 ^ (D - e), CS2 (10 - (D - e)) (j * 2 ^ (D - e) + t) (fld2 (X / 32) (2 ^ (D - e) - 1 + t)) by
   intro d hd t ht
   have := key (D - d) (Nat.sub_le _ _) t (by rw [Nat.sub_sub_self (by omega)]; exact ht)
   rwa [Nat.sub_sub_self (by omega)] at this
 intro e
 induction e with
 | zero =>
   intro _ t ht
   have := hfin' t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; simpa using ht)
   simp only [Nat.sub_zero]
   have hc := cellOk2_sound this
   simp only [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq] at hc
   have e10 : 10 - D = X % 32 := by omega
   rw [e10]; exact hc
 | succ e ih =>
   intro he t ht
   set d := D - (e + 1) with hd
   have hdD : d < D := by omega
   have hde : D - e = d + 1 := by omega
   have hc := hint' d hdD
   have hct := allBelow_spec hc t (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]; exact ht)
   simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hct
   have h0 := ih (by omega) (2 * t) (by rw [hde, pow_succ]; omega)
   have h1 := ih (by omega) (2 * t + 1) (by rw [hde, pow_succ]; omega)
   rw [hde] at h0 h1
   have e0 : j * 2 ^ (d + 1) + 2 * t = 2 * (j * 2 ^ d + t) := by rw [pow_succ]; ring
   have e1 : j * 2 ^ (d + 1) + (2 * t + 1) = 2 * (j * 2 ^ d + t) + 1 := by rw [pow_succ]; ring
   rw [e0] at h0; rw [e1] at h1
   have hlev : 10 - (d + 1) + 1 = 10 - d := by omega
   have hm := CS2_min h0 h1
   rw [hlev] at hm
   exact CS2_mono hct hm
theorem blockOk2_sound {X j : ℕ} (h : blockOk2 X j = true) : BlockSound2 X j := by
 unfold blockOk2 at h
 cases hX : Nat.beq X 0
 · rw [hX] at h
   exact blockOk2X_sound h
 · have : X = 0 := by rw [← Nat.beq_eq, hX]
   subst this
   refine ⟨by norm_num, fun d _ t _ => ?_⟩
   simp only [Nat.zero_div, fld2_zero]; exact CS2_zero _ _
theorem topv2_ten (top : ℕ) (bk : ℕ → ℕ) (i : ℕ) : topv2 top bk 10 i = fld2 (bk i / 32) 0 := by
 unfold topv2
 rw [show Nat.beq 10 10 = true from rfl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
theorem topv2_top (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (hl : l ≠ 10) (i : ℕ) :
   topv2 top bk l i = fld2 top (2 ^ (19 - l) + i) := by
 unfold topv2
 have : Nat.beq l 10 = false := by
   cases h : Nat.beq l 10
   · rfl
   · exact absurd (by rw [← Nat.beq_eq, h]) hl
 rw [this]
 simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul]
theorem top2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
   ∀ e, e ≤ 9 → ∀ i < 2 ^ (9 - e), CS2 (10 + e) i (topv2 top bk (10 + e) i) := by
 have ht' := allFrom_spec ht
 intro e
 induction e with
 | zero =>
   intro _ i hi
   rw [Nat.add_zero, topv2_ten]
   have hB := blockOk2_sound (hb i (by simpa using hi))
   have := hB.2 0 (Nat.zero_le _) 0 (by norm_num)
   simpa using this
 | succ e ih =>
   intro he i hi
   have hl := ht' e (by omega) |> allBelow_spec
   have hle := hl i (by simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.sub_eq, Nat.add_eq]; convert hi using 2; omega)
   simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] at hle
   have e1 : 11 + e - 1 = 10 + e := by omega
   rw [e1] at hle
   have h0 := ih (by omega) (2 * i) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
   have h1 := ih (by omega) (2 * i + 1) (by rw [show 9 - e = 9 - (e + 1) + 1 by omega, pow_succ]; omega)
   have hm := CS2_min h0 h1
   rw [show 10 + e + 1 = 10 + (e + 1) by omega] at hm
   rw [topv2_top top bk (by omega)]
   rw [show 19 - (10 + (e + 1)) = 19 - (11 + e) by omega]
   exact CS2_mono hle hm
theorem entry2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
   (l i : ℕ) (hi : l ≤ 19 → i < 2 ^ (19 - l)) : CS2 l i (entry2 top bk l i) := by
 unfold entry2
 cases h11 : Nat.ble 11 l
 · -- a block level
   have hl : l ≤ 10 := by
     have : ¬ 11 ≤ l := by rw [← Nat.ble_eq, h11]; decide
     omega
   show CS2 l i (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
   rw [forceR_eq]
   set j := Nat.shiftRight i (Nat.sub 10 l) with hj
   have hj' : j = i / 2 ^ (10 - l) := by rw [hj, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]; rfl
   have hj512 : j < 512 := by
     rw [hj']
     have hi' := hi (by omega)
     rw [Nat.div_lt_iff_lt_mul (by positivity), show (512:ℕ) = 2 ^ 9 by norm_num, ← pow_add]
     rwa [show 9 + (10 - l) = 19 - l by omega]
   have hB := blockOk2_sound (hb j hj512)
   set X := bk j
   unfold entB2
   have hr : Nat.land X 31 = X % 32 := by
     rw [Nat.land_eq, show (31:ℕ) = 2 ^ 5 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
   simp only [hr]
   set r := X % 32
   have hr10 : r ≤ 10 := hB.1
   have hkk : Nat.add l (Nat.sub r l) = max l r := by
     simp only [Nat.add_eq, Nat.sub_eq, max_def]; split_ifs <;> omega
   simp only [hkk]
   set kk := max l r with hkkdef
   have hkk10 : kk ≤ 10 := by omega
   have hlkk : l ≤ kk := le_max_left _ _
   set d := Nat.sub 10 kk with hd
   have hd' : d = 10 - kk := rfl
   set q := i / 2 ^ (kk - l) with hq
   have hqj : q / 2 ^ d = j := by
     rw [hq, hj', Nat.div_div_eq_div_mul, ← pow_add]
     congr 2; omega
   have ht' : q % 2 ^ d < 2 ^ d := Nat.mod_lt _ (by positivity)
   have hidx : Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d))
       = 2 ^ d - 1 + q % 2 ^ d := by
     simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq',
       Nat.shiftRight_eq_div_pow]
     rw [← hq]
     have := Nat.div_add_mod' q (2 ^ d)
     rw [hqj] at this
     congr 1; omega
   have hY : Nat.shiftRight X 5 = X / 32 := by rw [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
   rw [hidx, hY]
   have hcs := hB.2 d (by omega) (q % 2 ^ d) ht'
   have e1 : j * 2 ^ d + q % 2 ^ d = q := by
     have := Nat.div_add_mod' q (2 ^ d); rw [hqj] at this; omega
   rw [e1, show 10 - d = l + (kk - l) by omega] at hcs
   exact CS2_anc hcs
 · cases h20 : Nat.ble 20 l
   · have hl : 11 ≤ l := by rw [← Nat.ble_eq, h11]
     have hl' : l ≤ 19 := by
       have : ¬ 20 ≤ l := by rw [← Nat.ble_eq, h20]; decide
       omega
     show CS2 l i (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
     have := top2_sound hb ht (l - 10) (by omega) i (by rw [show 9 - (l - 10) = 19 - l by omega]; exact hi hl')
     rw [show 10 + (l - 10) = l by omega, topv2_top top bk (by omega)] at this
     simpa only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, one_mul] using this
   · exact CS2_zero l i
def DSound2 (k E : ℕ) (f : ℕ → ℕ) : Prop :=
 ∀ g, g < E → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC → PS (f g) x
theorem DSound2_zero (k E : ℕ) : DSound2 k E (fun _ => 0) := fun _ _ x _ _ => PS_zero x
theorem entry2_ge20 (top : ℕ) (bk : ℕ → ℕ) {l : ℕ} (i : ℕ) (hl : 20 ≤ l) : entry2 top bk l i = 0 := by
 have h11 : Nat.ble 11 l = true := by rw [Nat.ble_eq]; omega
 have h20 : Nat.ble 20 l = true := by rw [Nat.ble_eq]; omega
 unfold entry2
 rw [h11, h20]
theorem entry2_pack_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
   (l h : ℕ) (hi : l ≤ 19 → h < 2 ^ (19 - l)) :
   CS2 l h (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft l 40) h) 40) (Nat.land (Nat.add (Nat.shiftLeft l 40) h) 1099511627775)) := by
 by_cases hl : l ≤ 19
 · have hh : h < 2 ^ 40 := lt_of_lt_of_le (hi hl) (Nat.pow_le_pow_right (by norm_num) (by omega))
   rw [pack_hi l h hh, pack_lo l h hh]
   exact entry2_sound hb ht l h hi
 · rw [entry2_ge20 top bk _ (le_trans (by omega) (pack_ge l h))]
   exact CS2_zero l h
theorem dcore2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
   (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound2 k E ih)
   (g : ℕ) (hg : g < E) (x : ℝ) (h1 : ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x) (h2 : x ≤ ((E * 2 ^ k : ℕ) : ℝ) / SC) (t : ℕ) :
   PS (Bool.rec (motive := fun _ => ℕ)
     (pmin (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
       (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
       (ih (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t)))
     (entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 40)
       (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) (Nat.shiftRight g t)) 1099511627775))
     (Nat.ble E (Nat.shiftLeft (Nat.add (Nat.shiftRight g t) 1) t))) x := by
 set h := Nat.shiftRight g t with hh
 have hh' : h = g / 2 ^ t := by rw [hh, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
 set v := entry2 top bk (Nat.shiftRight (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 40)
   (Nat.land (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) 1099511627775) with hv
 set g' := Nat.shiftLeft (Nat.add h 1) t with hg'
 have hg'' : g' = (h + 1) * 2 ^ t := by rw [hg', Nat.shiftLeft_eq', Nat.shiftLeft_eq]
 have hcell : CS2 (Nat.add k t) h v := by
   rw [hv]
   apply entry2_pack_sound hb ht
   intro hkt
   have hk' : k ≤ 19 := by simp only [Nat.add_eq] at hkt; omega
   have hgib : g * 2 ^ k < 2 ^ 19 := by
     have := hk hk'
     calc g * 2 ^ k < E * 2 ^ k := Nat.mul_lt_mul_of_pos_right hg (by positivity)
       _ ≤ 2 ^ 19 := this
   rw [hh', Nat.div_lt_iff_lt_mul (by positivity)]
   have e : 2 ^ (19 - Nat.add k t) * 2 ^ t * 2 ^ k = 2 ^ 19 := by
     rw [← pow_add, ← pow_add]; congr 1; simp only [Nat.add_eq] at hkt ⊢; omega
   by_contra hcon
   push_neg at hcon
   have := Nat.mul_le_mul_right (2 ^ k) hcon
   rw [e] at this; omega
 have hcellx : ∀ y : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ y → y ≤ ((g' * 2 ^ k : ℕ) : ℝ) / SC → PS v y := by
   intro y hy1 hy2
   apply hcell y
   · refine le_trans (castdiv_le ?_) hy1
     rw [hh', Nat.add_eq, pow_add]
     calc g / 2 ^ t * (2 ^ k * 2 ^ t) = (g / 2 ^ t * 2 ^ t) * 2 ^ k := by ring
       _ ≤ g * 2 ^ k := Nat.mul_le_mul_right _ (Nat.div_mul_le_self g _)
   · refine le_trans hy2 (castdiv_le (le_of_eq ?_))
     rw [hg'', Nat.add_eq, pow_add]; ring
 cases hc : Nat.ble E g'
 · have hle : g' < E := by
     have : ¬ E ≤ g' := by rw [← Nat.ble_eq, hc]; decide
     omega
   show PS (pmin _ _) x
   rcases le_total x ((((g' * 2 ^ k : ℕ) : ℝ)) / SC) with hx | hx
   · exact PS_pmin_left (hcellx x h1 hx)
   · exact PS_pmin_right (hih g' hle x hx h2)
 · have hgt : E ≤ g' := by rw [← Nat.ble_eq, hc]
   exact hcellx x h1 (le_trans h2 (castdiv_le (Nat.mul_le_mul_right _ hgt)))
theorem dstep2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
   (k E : ℕ) (hk : k ≤ 19 → E * 2 ^ k ≤ 2 ^ 19) {ih : ℕ → ℕ} (hih : DSound2 k E ih) :
   DSound2 k E (dstep2 top bk k E ih) := by
 intro g hg x h1 h2
 unfold dstep2
 simp only [forceR_eq]
 exact dcore2_sound hb ht k E hk hih g hg x h1 h2 _
theorem dcov2_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true)
   (k ib : ℕ) (hk : k ≤ 19 → (ib + 1) * 2 ^ k ≤ 2 ^ 19) :
   ∀ g, g ≤ ib → ∀ x : ℝ, ((g * 2 ^ k : ℕ) : ℝ) / SC ≤ x → x ≤ (((ib + 1) * 2 ^ k : ℕ) : ℝ) / SC →
     PS (dcov2 top bk k ib g) x := by
 intro g hg x h1 h2
 have hs : ∀ {f : ℕ → ℕ}, DSound2 k (Nat.add ib 1) f → DSound2 k (Nat.add ib 1) (dstep2 top bk k (Nat.add ib 1) f) :=
   fun hf => dstep2_sound hb ht k (Nat.add ib 1) hk hf
 exact hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (hs (DSound2_zero k _)))))))))))))) g (by simp only [Nat.add_eq]; omega) x h1 h2
theorem blocks2_of {bk : ℕ → ℕ} (h : allFrom 0 512 (fun j => blockOk2 (bk j) j) = true) :
   ∀ j < 512, blockOk2 (bk j) j = true := by
 intro j hj
 have := allFrom_spec h j hj
 simpa using this
end AMW.Cert.PyrD
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
 rcases le_total b a with h | h
 · rw [Nat.cast_sub h]
 · rw [Nat.sub_eq_zero_of_le h]
   have := (Nat.cast_le (α := ℝ)).mpr h
   simp only [Nat.cast_zero]; linarith
theorem natsub_nonneg (a b : ℕ) : (0 : ℝ) ≤ ((a - b : ℕ) : ℝ) := Nat.cast_nonneg _
end AMW.Cert.PyrD
end
section SlopeDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def dcell (x : ℕ) : CellN := ⟨Nat.add (Nat.mul x KB) x, 0⟩
def ptdOk (x p m : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool) false
   ((Nat.beq p 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1LO)))
     && (Nat.beq m 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1HI))))
   (Nat.ble (Nat.add x 1) KB)
def lbDr (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (let k := blen (Nat.shiftRight (Nat.sub hi lo) 6)
      dcov2 top bk k (Nat.shiftRight (Nat.sub hi 1) k) (Nat.shiftRight lo k))
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
end AMW.Cert.PyrD
end SlopeDefs
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def LBSoundD (top : ℕ) (bk : ℕ → ℕ) : Prop :=
 ∀ lo hi : ℕ, ∀ x : ℝ, (lo : ℝ) / SC ≤ x → x ≤ (hi : ℝ) / SC → PS (lbDr top bk lo hi) x
theorem lbDr_sound {top : ℕ} {bk : ℕ → ℕ} (hb : ∀ j < 512, blockOk2 (bk j) j = true) (ht : topOk2 top bk = true) :
   LBSoundD top bk := by
 intro lo hi x h1 h2
 unfold lbDr
 cases hlo : Nat.ble hi lo
 · cases hhi : Nat.ble 524289 hi
   · have hlh : lo < hi := by
       have : ¬ hi ≤ lo := by rw [← Nat.ble_eq, hlo]; decide
       omega
     have hhi' : hi ≤ 524288 := by
       have : ¬ 524289 ≤ hi := by rw [← Nat.ble_eq, hhi]; decide
       omega
     show PS (dcov2 top bk (blen (Nat.shiftRight (Nat.sub hi lo) 6)) (Nat.shiftRight (Nat.sub hi 1) (blen (Nat.shiftRight (Nat.sub hi lo) 6)))
       (Nat.shiftRight lo (blen (Nat.shiftRight (Nat.sub hi lo) 6)))) x
     set k := blen (Nat.shiftRight (Nat.sub hi lo) 6)
     simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.sub_eq]
     have hp : 0 < 2 ^ k := by positivity
     apply dcov2_sound hb ht k ((hi - 1) / 2 ^ k)
     · intro hk
       have : (hi - 1) / 2 ^ k < 2 ^ (19 - k) := by
         rw [Nat.div_lt_iff_lt_mul hp, ← pow_add, show 19 - k + k = 19 by omega]; norm_num; omega
       calc ((hi - 1) / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ (19 - k) * 2 ^ k := Nat.mul_le_mul_right _ this
         _ = 2 ^ 19 := by rw [← pow_add]; congr 1; omega
     · exact Nat.div_le_div_right (by omega)
     · exact le_trans (castdiv_le (Nat.div_mul_le_self lo _)) h1
     · refine le_trans h2 (castdiv_le ?_)
       have h5 := Nat.lt_div_mul_add (a := hi - 1) hp
       have e : ((hi - 1) / 2 ^ k + 1) * 2 ^ k = (hi - 1) / 2 ^ k * 2 ^ k + 2 ^ k := by ring
       rw [e]
       generalize (hi - 1) / 2 ^ k * 2 ^ k = A at h5 ⊢
       generalize 2 ^ k = P at h5 ⊢
       omega
   · exact PS_zero x
 · exact PS_zero x
theorem ptdOk_sound {x p m : ℕ} (h : ptdOk x p m = true) :
   (p ≠ 0 → kD ((x : ℝ) / SC) < 0 ∧ (p : ℝ) / U1 ≤ fD true ((x : ℝ) / SC)) ∧
     (m ≠ 0 → kD ((x : ℝ) / SC) < 0 ∧ (m : ℝ) / U1 ≤ fD false ((x : ℝ) / SC)) := by
 unfold ptdOk at h
 cases hK : Nat.ble (Nat.add x 1) KB
 · rw [hK] at h; exact absurd (show (false : Bool) = true from h) (by decide)
 · rw [hK] at h
   have h' : ((Nat.beq p 0 || ((dcell x).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (dcell x).W1LO)))
     && (Nat.beq m 0 || ((dcell x).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (dcell x).W1HI)))) = true := h
   simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h'
   obtain ⟨hp, hm⟩ := h'
   have hK' : x < KB := by
     rw [Nat.ble_eq] at hK
     simp only [Nat.add_eq] at hK; omega
   have hLN : (dcell x).LN = x := by
     simp only [dcell, CellN.LN, Nat.add_eq, Nat.mul_eq]
     rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hK', Nat.zero_add]
   have hUN : (dcell x).UN = x := by
     simp only [dcell, CellN.UN, Nat.add_eq, Nat.mul_eq]
     rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hK']
   have hU1 := U1_posR
   have eK : ((KU1 : ℤ) : ℝ) = 2 * (U1 : ℝ) := by norm_num [KU1, U1]
   refine ⟨fun hp0 => ?_, fun hm0 => ?_⟩
   · rcases hp with hp | ⟨hok, hv⟩
     · exact absurd (by rw [← Nat.beq_eq]; exact hp) hp0
     obtain ⟨hk, hlo, -⟩ := cellD_sound (dcell x) hok ((x : ℝ) / SC) (by rw [hLN]) (by rw [hUN])
     refine ⟨hk, ?_⟩
     have hvr : (p : ℝ) ≤ ((KU1 : ℤ) : ℝ) + ((dcell x).W1LO : ℝ) := by exact_mod_cast hv
     simp only [fD, ↓reduceIte]
     rw [div_le_iff₀ hU1]
     have := (div_le_iff₀ hU1).mp hlo
     rw [eK] at hvr
     nlinarith
   · rcases hm with hm | ⟨hok, hv⟩
     · exact absurd (by rw [← Nat.beq_eq]; exact hm) hm0
     obtain ⟨hk, -, hhi⟩ := cellD_sound (dcell x) hok ((x : ℝ) / SC) (by rw [hLN]) (by rw [hUN])
     refine ⟨hk, ?_⟩
     have hvr : (m : ℝ) ≤ ((KU1 : ℤ) : ℝ) - ((dcell x).W1HI : ℝ) := by exact_mod_cast hv
     simp only [fD, ↓reduceIte, Bool.false_eq_true]
     rw [div_le_iff₀ hU1]
     have := (le_div_iff₀ hU1).mp hhi
     rw [eK] at hvr
     nlinarith
theorem PS_of_ptdOk {x v : ℕ} (h : ptdOk x (lo32 v) (hi32 v) = true) : PS v ((x : ℝ) / SC) := by
 have h' := ptdOk_sound h
 exact ⟨h'.1, h'.2⟩
theorem lo32_zero : lo32 0 = 0 := rfl
theorem hi32_zero : hi32 0 = 0 := rfl
end AMW.Cert.PyrD
end
section ConvDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def ccell (a b : ℕ) : CellN := ⟨Nat.add (Nat.mul a KB) b, 0⟩
def chainOk (a : ℕ) (l : List ℕ) : Bool :=
 List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
   (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && ih b) l a
def chainLast (a : ℕ) (l : List ℕ) : ℕ :=
 List.rec (motive := fun _ => ℕ → ℕ) (fun a => a) (fun b _ ih _ => ih b) l a
def dsel (j m a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) a b (Nat.ble m j)
def dpk (j k v : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 v (Nat.beq j k)
def pt3e (x v : ℕ) : Bool := ptOk x (lo32 v) && ptdOk x (lo32 (hi32 v)) (hi32 (hi32 v))
def rgA (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.1 (Nat.mul 20 k)) 1048575
def rgB (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.2.1 (Nat.mul 20 k)) 1048575
def rgOk (R : ℕ × ℕ × List (List ℕ)) : Bool :=
 allBelow 16 fun k => Nat.blt (rgB R k) (rgA R k)
   || (Nat.ble 1 (R.2.2.getD k []).length && chainOk (rgA R k) (R.2.2.getD k [])
     && Nat.beq (chainLast (rgA R k) (R.2.2.getD k [])) (rgB R k))
end AMW.Cert.PyrD
end ConvDefs
noncomputable section
namespace AMW.Cert
end AMW.Cert
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
theorem ccell_LN {a b : ℕ} (hb : b < KB) : (ccell a b).LN = a := by
 simp only [ccell, CellN.LN, Nat.add_eq, Nat.mul_eq]
 rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hb, Nat.zero_add]
theorem ccell_UN {a b : ℕ} (hb : b < KB) : (ccell a b).UN = b := by
 simp only [ccell, CellN.UN, Nat.add_eq, Nat.mul_eq]
 rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
theorem chainOk_sound : ∀ (l : List ℕ) (a : ℕ), chainOk a l = true → l ≠ [] →
   ∀ x : ℝ, (a : ℝ) / SC ≤ x → x ≤ (chainLast a l : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
 intro l
 induction l with
 | nil => intro a _ h; exact absurd rfl h
 | cons b r ih =>
   intro a h _ x hx1 hx2
   have h' : (Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && chainOk b r) = true := h
   simp only [Bool.and_eq_true, Nat.ble_eq] at h'
   obtain ⟨⟨⟨hab, hbK⟩, hcv⟩, hr⟩ := h'
   have hbK' : b < KB := by simp only [Nat.add_eq] at hbK; omega
   rcases le_or_gt x ((b : ℝ) / SC) with hxb | hxb
   · exact cellConv_sound (ccell a b) hcv x (by rw [ccell_LN hbK']; exact hx1) (by rw [ccell_UN hbK']; exact hxb)
   · cases r with
     | nil =>
       have e : chainLast a [b] = b := rfl
       rw [e] at hx2; linarith
     | cons c r' =>
       have e : chainLast a (b :: c :: r') = chainLast b (c :: r') := rfl
       rw [e] at hx2
       exact ih b hr (List.cons_ne_nil c r') x hxb.le hx2
def PTF (f : ℕ → ℕ) : Prop :=
 ∀ x : ℕ, (lo32 (f x) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 (f x)) ((x : ℝ) / SC)
end AMW.Cert.PyrD
end
section MinDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
def treadU (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDr tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
def treadD (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDr tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)
def mwc (κ lam : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 1024 0 (Nat.beq κ 3)) (Nat.sub 1024 lam) (Nat.beq κ 2))
   0 (Nat.beq κ 1)
def mw1 (κ lam : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.sub 1024 lam) (Nat.beq κ 3)) lam (Nat.beq κ 2))
   1024 (Nat.beq κ 1)
def mw2 (κ lam : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 lam (Nat.beq κ 3)
def mval (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U c l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul c (lb top bk L U)) (Nat.add (Nat.mul l1 (lo32 (f p1))) (Nat.mul l2 (lo32 (f p2))))
def mcp (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul (Nat.mul l1 (Nat.sub (hi32 (hi32 (f p1))) 2000000000)) (Nat.sub p1 L))
   (Nat.mul (Nat.mul l2 (Nat.sub (hi32 (hi32 (f p2))) 2000000000)) (Nat.sub p2 L))
def mcn (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul (Nat.mul l1 (Nat.sub 2000000000 (hi32 (hi32 (f p1))))) (Nat.sub p1 L))
   (Nat.mul (Nat.mul l2 (Nat.sub 2000000000 (hi32 (hi32 (f p2))))) (Nat.sub p2 L))
def msl (f : ℕ → ℕ) (l1 l2 p1 p2 : ℕ) : ℕ := Nat.add (Nat.mul l1 (lo32 (hi32 (f p1)))) (Nat.mul l2 (lo32 (hi32 (f p2))))
end AMW.Cert.PyrD
end MinDefs
noncomputable section
namespace AMW.Cert
theorem w1_mono_of_conv {za zb : ℝ} (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) {x y : ℝ}
   (hx : za ≤ x) (hxy : x ≤ y) (hy : y ≤ zb) : w1 x ≤ w1 y := by
 rcases eq_or_lt_of_le hxy with heq | hlt
 · rw [heq]
 obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
   (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
   (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
 have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
 have hpos : 0 < y - x := by linarith
 have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
 nlinarith
theorem ext_tangent {za zb L U p : ℝ}
   (hc : ∀ x : ℝ, za ≤ x → x ≤ zb → kD x < 0 ∧ 0 ≤ w2 x) (hp1 : za ≤ p) (hp2 : p ≤ zb)
   (hR : ∀ x : ℝ, zb ≤ x → x ≤ U → kD x < 0 ∧ w1 p ≤ w1 x)
   (hL : ∀ x : ℝ, L ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 p)
   (hLp : L ≤ p) (hpU : p ≤ U) {s : ℝ} (hs1 : L ≤ s) (hs2 : s ≤ U) :
   wfun p + w1 p * (s - p) ≤ wfun s := by
 have hk : ∀ x, L ≤ x → x ≤ U → kD x < 0 := by
   intro x h1 h2
   rcases le_total x za with h | h
   · exact (hL x h1 h).1
   · rcases le_total x zb with h' | h'
     · exact (hc x h h').1
     · exact (hR x h' h2).1
 have hW : ∀ ξ, L ≤ ξ → ξ ≤ U → HasDerivAt wfun (w1 ξ) ξ := fun ξ h1 h2 => hasDerivAt_wfun ξ (hk ξ h1 h2).ne
 have hmono : ∀ x y, za ≤ x → x ≤ y → y ≤ zb → w1 x ≤ w1 y := by
   intro x y hx hxy hy
   rcases eq_or_lt_of_le hxy with heq | hlt
   · rw [heq]
   obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope w1 w2 hlt
     (fun z hz => (hasDerivAt_w1 z (hc z (hx.trans hz.1) (hz.2.trans hy)).1.ne).continuousAt.continuousWithinAt)
     (fun z hz => hasDerivAt_w1 z (hc z (hx.trans hz.1.le) (hz.2.le.trans hy)).1.ne)
   have h2 := (hc η (hx.trans hη.1.le) (hη.2.le.trans hy)).2
   have hpos : 0 < y - x := by linarith
   have : w1 y - w1 x = w2 η * (y - x) := by rw [hηe]; field_simp
   nlinarith
 have hge : ∀ ξ, p ≤ ξ → ξ ≤ U → w1 p ≤ w1 ξ := by
   intro ξ h1 h2
   rcases le_total ξ zb with h | h
   · exact hmono p ξ hp1 h1 h
   · exact (hR ξ h h2).2
 have hle : ∀ ξ, L ≤ ξ → ξ ≤ p → w1 ξ ≤ w1 p := by
   intro ξ h1 h2
   rcases le_total ξ za with h | h
   · exact (hL ξ h1 h).2
   · exact hmono ξ p h h2 hp2
 rcases lt_trichotomy p s with hps | hps | hps
 · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
     (fun y hy => (hW y (hLp.trans hy.1) (hy.2.trans hs2)).continuousAt.continuousWithinAt)
     (fun y hy => hW y (hLp.trans hy.1.le) (hy.2.le.trans hs2))
   have h := hge ξ hξ.1.le (hξ.2.le.trans hs2)
   have hne : s - p ≠ 0 := by linarith
   have e : wfun s - wfun p = w1 ξ * (s - p) := by rw [hξe]; field_simp
   have hsp : 0 ≤ s - p := by linarith
   nlinarith
 · rw [hps]; simp
 · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope wfun w1 hps
     (fun y hy => (hW y (hs1.trans hy.1) (hy.2.trans hpU)).continuousAt.continuousWithinAt)
     (fun y hy => hW y (hs1.trans hy.1.le) (hy.2.le.trans hpU))
   have h := hle ξ (hs1.trans hξ.1.le) hξ.2.le
   have hne : p - s ≠ 0 := by linarith
   have e : wfun p - wfun s = w1 ξ * (p - s) := by rw [hξe]; field_simp
   have hsp : 0 ≤ p - s := by linarith
   nlinarith
end AMW.Cert
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
theorem rg_conv {R : ℕ × ℕ × List (List ℕ)} (hR : rgOk R = true) {k : ℕ} (hk : k < 16) (hab : rgA R k ≤ rgB R k) :
   ∀ x : ℝ, ((rgA R k : ℕ) : ℝ) / SC ≤ x → x ≤ ((rgB R k : ℕ) : ℝ) / SC → kD x < 0 ∧ 0 ≤ w2 x := by
 intro x hx1 hx2
 have hk' := allBelow_spec hR _ hk
 simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hk'
 rcases hk' with hempty | ⟨⟨⟨hlen, hch⟩, hlast⟩⟩
 · omega
 · set c := R.2.2.getD k [] with hc
   have hne : c ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
   exact chainOk_sound c _ hch hne x hx1 (by rw [hlast]; exact hx2)
theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
 cases e : Nat.beq a b
 · rfl
 · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem mw_sum (κ lam : ℕ) (hl : lam ≤ 1024) : mwc κ lam + mw1 κ lam + mw2 κ lam = 1024 := by
 unfold mwc mw1 mw2
 by_cases h1 : κ = 1
 · subst h1; simp only [show Nat.beq 1 1 = true from rfl, show Nat.beq 1 2 = false from rfl, show Nat.beq 1 3 = false from rfl]
 · rw [beq_false h1]
   by_cases h2 : κ = 2
   · subst h2
     simp only [show Nat.beq 2 2 = true from rfl, show Nat.beq 2 3 = false from rfl, Nat.sub_eq]; omega
   · rw [beq_false h2]
     by_cases h3 : κ = 3
     · subst h3; simp only [show Nat.beq 3 3 = true from rfl, Nat.sub_eq]; omega
     · rw [beq_false h3]; rfl
theorem natsub_pair (M : ℕ) : ((M - 2000000000 : ℕ) : ℝ) - ((2000000000 - M : ℕ) : ℝ) = (M : ℝ) - 2000000000 := by
 rcases le_total M 2000000000 with h | h
 · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
 · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
theorem gap_lo {E e H N : ℝ} (hN : 0 ≤ N) (hE : -N ≤ 1000000000 * E) (he0 : 0 ≤ e) (he1 : e ≤ H / 32768) :
   -(10 * (N * H)) ≤ 327680000000000 * (E * e) := by
 have hH : 0 ≤ H := by linarith
 rcases le_total 0 E with h | h
 · have : 0 ≤ E * e := mul_nonneg h he0
   nlinarith
 · have h1 : E * e ≥ E * (H / 32768) := by nlinarith
   nlinarith
theorem brec_ne {b : Bool} {x : ℕ} (h : Bool.rec (motive := fun _ => ℕ) 0 x b ≠ 0) : b = true := by
 cases b
 · exact absurd rfl h
 · rfl
end AMW.Cert.PyrD
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
end AMW.Cert.PyrD
end
noncomputable section
open Real
namespace AMW.Cert
theorem kfunAM_ge_cos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.cos (π * x) ≤ AMW.kfunAM x := by
 have hK0 := AMW.KfunAM_zero_pos
 unfold AMW.kfunAM
 rw [le_div_iff₀ hK0, AMW.KfunAM_zero]
 unfold AMW.KfunAM
 have hab : (-(1 : ℝ) / 2) ≤ 1 / 2 := by norm_num
 rw [← intervalIntegral.integral_const_mul]
 apply intervalIntegral.integral_mono_on hab
 · exact (continuous_const.mul AMW.vAM_continuous).intervalIntegrable _ _
 · exact (AMW.vAM_continuous.mul (by fun_prop : Continuous fun t : ℝ => Real.cos (2 * π * x * t))).intervalIntegrable _ _
 · intro t ht
   have hv := AMW.vAM_pos_on ht
   have habs : |2 * π * x * t| ≤ π * x := by
     rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * π * x)]
     have : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
     have hpx : 0 ≤ π * x := mul_nonneg Real.pi_pos.le h0
     have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 2 * π * x)
     linarith
   have hcos : Real.cos (π * x) ≤ Real.cos (2 * π * x * t) := by
     rw [← Real.cos_abs (2 * π * x * t)]
     exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by nlinarith [Real.pi_pos]) habs
   calc Real.cos (π * x) * AMW.vAM t ≤ Real.cos (2 * π * x * t) * AMW.vAM t := mul_le_mul_of_nonneg_right hcos hv.le
     _ = AMW.vAM t * Real.cos (2 * π * x * t) := mul_comm _ _
theorem wfun_quarter_low {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) : (1 / 4 : ℝ) ≤ wfun x := by
 have hk := kfunAM_ge_cos h0 (by linarith)
 have hc : Real.sqrt 2 / 2 ≤ Real.cos (π * x) := by
   rw [← Real.cos_pi_div_four]
   exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
 have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 have hk' : Real.sqrt 2 / 2 ≤ AMW.kfunAM x := hc.trans hk
 unfold wfun AMW.wfunAM
 nlinarith
def winCell (i : ℕ) : AMW.G.CellA := ⟨8192 + 512 * i, 8704 + 512 * i⟩
def winOk (i : ℕ) : Bool := (winCell i).ok && Nat.ble (Nat.mul AMW.G.DZ AMW.G.DZ) (Nat.mul 4 (Nat.mul (winCell i).KAn (winCell i).KAn))
theorem winOk_all : Pyr.allBelow 16 winOk = true := by decide +kernel
theorem wfun_quarter_high {x : ℝ} (h0 : 1 / 4 ≤ x) (h1 : x ≤ 1 / 2) : (1 / 4 : ℝ) ≤ wfun x := by
 have hall := Pyr.allBelow_spec winOk_all
 obtain ⟨i, hi, hx1, hx2⟩ : ∃ i < 16, ((8192 + 512 * i : ℕ) : ℝ) / AMW.G.SC ≤ x ∧ x ≤ ((8704 + 512 * i : ℕ) : ℝ) / AMW.G.SC := by
   have hSC : (AMW.G.SC : ℝ) = 32768 := by norm_num [AMW.G.SC]
   by_cases hx : x = 1 / 2
   · exact ⟨15, by norm_num, by rw [hSC, hx]; norm_num, by rw [hSC, hx]; norm_num⟩
   · have hlt : x < 1 / 2 := lt_of_le_of_ne h1 hx
     set n := ⌊(x - 1 / 4) * 64⌋₊ with hn
     have hn0 : (0 : ℝ) ≤ (x - 1 / 4) * 64 := by linarith
     have hnle := Nat.floor_le hn0
     have hnlt := Nat.lt_floor_add_one ((x - 1 / 4) * 64)
     have hn16 : n < 16 := by
       have : (n : ℝ) < 16 := by linarith
       exact_mod_cast this
     refine ⟨n, hn16, ?_, ?_⟩ <;> rw [hSC] <;> push_cast <;> linarith
 have hc := hall i hi
 unfold winOk at hc
 simp only [Bool.and_eq_true, Nat.ble_eq] at hc
 obtain ⟨hok, hK⟩ := hc
 have hw := (winCell i).w_lower hok (x := x) hx1 hx2
 have hD := AMW.G.DZ_pos
 generalize (winCell i).KAn = K at hK hw
 have hK' : (AMW.G.DZ : ℝ) * AMW.G.DZ ≤ 4 * ((K : ℝ) * K) := by
   have := (Nat.cast_le (α := ℝ)).mpr hK; simp only [Nat.mul_eq] at this; push_cast at this; exact this
 unfold wfun
 refine le_trans ?_ hw
 generalize (AMW.G.DZ : ℝ) = D at hD hK' ⊢
 rw [div_pow, le_div_iff₀ (by positivity)]
 nlinarith
theorem wfun_window (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : (1 / 4 : ℝ) ≤ wfun x := by
 rcases le_total x (1 / 4) with h | h
 · exact wfun_quarter_low h0 h
 · exact wfun_quarter_high h h1
end AMW.Cert
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def nmax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)
theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
 unfold nmax
 simp only [Nat.add_eq, Nat.sub_eq]
 omega
theorem le_nmax_right (a b : ℕ) : b ≤ nmax a b := by rw [nmax_eq]; exact le_max_right _ _
theorem le_nmax_left (a b : ℕ) : a ≤ nmax a b := by rw [nmax_eq]; exact le_max_left _ _
theorem natsub_diff (a b : ℕ) : ((a - b : ℕ) : ℝ) - ((b - a : ℕ) : ℝ) = (a : ℝ) - b := by
 rcases le_total a b with h | h
 · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
 · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; push_cast; ring
theorem SC_pos : (0 : ℝ) < SC := by norm_num [SC]
theorem lo_nmax {A L0 : ℕ} {s : ℝ} (h1 : (A : ℝ) / SC ≤ s) (h2 : (L0 : ℝ) / SC ≤ s) :
   ((nmax A L0 : ℕ) : ℝ) / SC ≤ s := by
 rw [nmax_eq]
 rcases le_total A L0 with h | h
 · rw [max_eq_right h]; exact h2
 · rw [max_eq_left h]; exact h1
theorem hi_nmin {B U0 : ℕ} {s : ℝ} (h1 : s ≤ (B : ℝ) / SC) (h2 : s ≤ (U0 : ℝ) / SC) :
   s ≤ ((nmin B U0 : ℕ) : ℝ) / SC := by
 rw [nmin_eq]
 rcases le_total B U0 with h | h
 · rw [min_eq_left h]; exact h1
 · rw [min_eq_right h]; exact h2
end AMW.Cert.PCell
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
end AMW.Cert.PyrD
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
structure Cl where
 (L U A B : List ℕ)
def gsum (g : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ r ∈ Finset.Ico i j, g r
def pI (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).1
def pJ (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).2
def InCell (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (g : ℕ → ℝ) : Prop :=
 (∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC) ∧
 ∀ k < PR.length, ((c.A.getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
   gsum g (pI PR k) (pJ PR k) ≤ ((c.B.getD k 0 : ℕ) : ℝ) / SC
def CovBy (Q : ℕ) (PR : List (ℕ × ℕ)) (P : (ℕ → ℝ) → Prop) (c : Cl) : Prop := ∀ g, InCell Q PR c g → P g
def PRok (Q : ℕ) (PR : List (ℕ × ℕ)) : Prop := ∀ k < PR.length, pI PR k + 2 ≤ pJ PR k ∧ pJ PR k ≤ Q
instance (Q : ℕ) (PR : List (ℕ × ℕ)) : Decidable (PRok Q PR) := by unfold PRok; infer_instance
def sumR (L : List ℕ) (i : ℕ) : ℕ → ℕ
 | 0 => 0
 | 1 => L.getD i 0
 | n + 2 => Nat.add (sumR L i (n + 1)) (L.getD (i + n + 1) 0)
theorem sumR_eq (L : List ℕ) (i : ℕ) : ∀ n, ((sumR L i n : ℕ) : ℝ) = ∑ r ∈ Finset.Ico i (i + n), ((L.getD r 0 : ℕ) : ℝ)
 | 0 => by simp [sumR]
 | 1 => by simp [sumR]
 | n + 2 => by
   have ih := sumR_eq L i (n + 1)
   rw [show i + (n + 2) = (i + (n + 1)) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ← ih]
   simp only [sumR, Nat.add_eq]; push_cast; rw [Nat.add_assoc i n 1]
def imap (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → List ℕ
 | _, [] => []
 | s, x :: xs => f s x :: imap f (s + 1) xs
theorem imap_length (f : ℕ → ℕ → ℕ) : ∀ (s : ℕ) (L : List ℕ), (imap f s L).length = L.length
 | _, [] => rfl
 | s, _ :: xs => by simp [imap, imap_length f (s + 1) xs]
theorem imap_getD (f : ℕ → ℕ → ℕ) : ∀ (s : ℕ) (L : List ℕ) (r : ℕ), r < L.length →
   (imap f s L).getD r 0 = f (s + r) (L.getD r 0)
 | _, [], r, h => absurd h (Nat.not_lt_zero _)
 | s, x :: xs, 0, _ => by simp [imap]
 | s, x :: xs, r + 1, h => by
   simp only [imap, List.getD_cons_succ]
   rw [imap_getD f (s + 1) xs r (by simpa using h)]
   congr 1; omega
def InBox (Q : ℕ) (c : Cl) (g : ℕ → ℝ) : Prop :=
 ∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC
theorem sum_lo {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
   ((sumR c.L i n : ℕ) : ℝ) / SC ≤ gsum g i (i + n) := by
 rw [sumR_eq, gsum, Finset.sum_div]
 exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).1
theorem sum_hi {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
   gsum g i (i + n) ≤ ((sumR c.U i n : ℕ) : ℝ) / SC := by
 rw [sumR_eq, gsum, Finset.sum_div]
 exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).2
def fLe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmax (c.A.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k))
def fUe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmin (c.B.getD k 0) (sumR c.U (pI PR k) (pJ PR k - pI PR k))
def femp (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : Bool := Nat.blt (fUe PR c k) (fLe PR c k)
def ind (b : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 1 b
def inr (r i j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) false (Nat.blt r j) (Nat.ble i r)
theorem ind_inr (r i j : ℕ) : ((ind (inr r i j) : ℕ) : ℝ) = if i ≤ r ∧ r < j then 1 else 0 := by
 unfold ind inr
 by_cases h1 : i ≤ r
 · rw [Nat.ble_eq_true_of_le h1]
   by_cases h2 : r < j
   · rw [show Nat.blt r j = true from Nat.blt_eq.mpr h2]; simp [h1, h2]
   · rw [show Nat.blt r j = false from Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)]; simp [h2]
 · rw [show Nat.ble i r = false from Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)]; simp [h1]
def MulOKg (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (P S : List ℕ) (Cp Cm : ℕ) : Prop :=
 ∀ g, InCell Q PR c g → 0 ≤ ((Cp : ℝ) - Cm) +
   ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
theorem mul_step {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} {P S : List ℕ} {Cp Cm : ℕ}
   (hP : P.length = Q) (hS : S.length = Q) (h : MulOKg Q PR c P S Cp Cm) {k : ℕ} (hk : k < PR.length) (Ylo Yhi : ℕ) :
   MulOKg Q PR c (imap (fun r x => Nat.add x (Nat.mul Ylo (ind (inr r (pI PR k) (pJ PR k))))) 0 P)
     (imap (fun r x => Nat.add x (Nat.mul Yhi (ind (inr r (pI PR k) (pJ PR k))))) 0 S)
     (Nat.add (Nat.add Cp (Nat.mul Ylo (Nat.sub (sumR c.L (pI PR k) (pJ PR k - pI PR k)) (c.A.getD k 0))))
       (Nat.mul Yhi (Nat.sub (c.B.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k)))))
     (Nat.add (Nat.add Cm (Nat.mul Ylo (Nat.sub (c.A.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k)))))
       (Nat.mul Yhi (Nat.sub (sumR c.L (pI PR k) (pJ PR k - pI PR k)) (c.B.getD k 0)))) := by
 intro g hg
 have h0 := h g hg
 obtain ⟨hij, hjQ⟩ := hPR k hk
 set i := pI PR k with hi
 set j := pJ PR k with hj
 have hn : i + (j - i) = j := by omega
 have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
 have hsum : ∑ r ∈ Finset.range Q, ((ind (inr r i j) : ℕ) : ℝ) * (32768 * g r - (c.L.getD r 0 : ℕ))
     = 32768 * gsum g i j - (sumR c.L i (j - i) : ℕ) := by
   simp only [ind_inr, ite_mul, one_mul, zero_mul]
   rw [← Finset.sum_filter, sumR_eq, hn, gsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
   apply Finset.sum_congr
   · ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
   · intro _ _; rfl
 have hA := (hg.2 k hk).1
 have hB := (hg.2 k hk).2
 rw [hSCe] at hA hB
 have hlo : (0 : ℝ) ≤ Ylo * (32768 * gsum g i j - (c.A.getD k 0 : ℕ)) :=
   mul_nonneg (Nat.cast_nonneg _) (by rw [div_le_iff₀ (by norm_num)] at hA; linarith)
 have hhi : (0 : ℝ) ≤ Yhi * ((c.B.getD k 0 : ℕ) - 32768 * gsum g i j) :=
   mul_nonneg (Nat.cast_nonneg _) (by rw [le_div_iff₀ (by norm_num)] at hB; linarith)
 have hd1 := natsub_diff (sumR c.L i (j - i)) (c.A.getD k 0)
 have hd2 := natsub_diff (c.B.getD k 0) (sumR c.L i (j - i))
 have e : ∑ r ∈ Finset.range Q, ((((imap (fun r x => Nat.add x (Nat.mul Ylo (ind (inr r i j)))) 0 P).getD r 0 : ℕ) : ℝ)
       - (((imap (fun r x => Nat.add x (Nat.mul Yhi (ind (inr r i j)))) 0 S).getD r 0 : ℕ) : ℝ))
       * (32768 * g r - (c.L.getD r 0 : ℕ))
     = ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
       + (Ylo - Yhi) * ∑ r ∈ Finset.range Q, ((ind (inr r i j) : ℕ) : ℝ) * (32768 * g r - (c.L.getD r 0 : ℕ)) := by
   rw [Finset.mul_sum, ← Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro r hr
   rw [imap_getD _ _ _ _ (by rw [hP]; simpa using hr), imap_getD _ _ _ _ (by rw [hS]; simpa using hr)]
   simp only [Nat.zero_add, Nat.add_eq, Nat.mul_eq]
   push_cast; ring
 rw [e, hsum]
 simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
 push_cast
 have e2 : (Ylo : ℝ) * ((sumR c.L i (j - i) - c.A.getD k 0 : ℕ) : ℝ) - Ylo * ((c.A.getD k 0 - sumR c.L i (j - i) : ℕ) : ℝ)
     = Ylo * ((sumR c.L i (j - i) : ℕ) - (c.A.getD k 0 : ℕ)) := by rw [← mul_sub, hd1]
 have e3 : (Yhi : ℝ) * ((c.B.getD k 0 - sumR c.L i (j - i) : ℕ) : ℝ) - Yhi * ((sumR c.L i (j - i) - c.B.getD k 0 : ℕ) : ℝ)
     = Yhi * ((c.B.getD k 0 : ℕ) - (sumR c.L i (j - i) : ℕ)) := by rw [← mul_sub, hd2]
 nlinarith [e2, e3, hlo, hhi, h0]
theorem neg_natsub_le {X Y : ℕ} {e : ℝ} (h : (Y : ℝ) - X ≤ e) : -((X - Y : ℕ) : ℝ) ≤ e := by
 have := natsub_ge X Y; linarith
def fsum (c : Cl) (P S : List ℕ) : ℕ → ℕ
 | 0 => 0
 | n + 1 => Nat.add (fsum c P S n) (Nat.mul (Nat.sub (c.U.getD n 0) (c.L.getD n 0)) (Nat.sub (P.getD n 0) (S.getD n 0)))
theorem fsum_ge {Q : ℕ} {c : Cl} (P S : List ℕ) {g : ℕ → ℝ} (hb : InBox Q c g) : ∀ n ≤ Q,
   ∑ r ∈ Finset.range n, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
     ≤ ((fsum c P S n : ℕ) : ℝ)
 | 0, _ => by simp [fsum]
 | n + 1, hn => by
   rw [Finset.sum_range_succ]
   have ih := fsum_ge P S hb n (by omega)
   simp only [fsum, Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
   push_cast
   have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
   obtain ⟨h1, h2⟩ := hb n (by omega)
   rw [hSCe, div_le_iff₀ (by norm_num)] at h1
   rw [hSCe, le_div_iff₀ (by norm_num)] at h2
   have hd1 := natsub_ge (c.U.getD n 0) (c.L.getD n 0)
   have hn1 := natsub_nonneg (c.U.getD n 0) (c.L.getD n 0)
   have hn2 := natsub_nonneg (P.getD n 0) (S.getD n 0)
   have hd2 := natsub_ge (P.getD n 0) (S.getD n 0)
   rcases le_total (S.getD n 0) (P.getD n 0) with h | h
   · rw [Nat.cast_sub h] at hd2 hn2 ⊢
     have e : ((P.getD n 0 : ℕ) : ℝ) - (S.getD n 0 : ℕ) ≥ 0 := hn2
     nlinarith [mul_le_mul_of_nonneg_left (show 32768 * g n - (c.L.getD n 0 : ℕ) ≤ ((c.U.getD n 0 - c.L.getD n 0 : ℕ) : ℝ) by linarith) e]
   · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, mul_zero, add_zero]
     have e : ((P.getD n 0 : ℕ) : ℝ) - (S.getD n 0 : ℕ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast h)
     nlinarith [mul_nonpos_of_nonpos_of_nonneg e (show (0 : ℝ) ≤ 32768 * g n - (c.L.getD n 0 : ℕ) by linarith)]
theorem farkas_cov {Q : ℕ} {PR : List (ℕ × ℕ)} {P' : (ℕ → ℝ) → Prop} {c : Cl} {P S : List ℕ} {Cp Cm : ℕ}
   (h : MulOKg Q PR c P S Cp Cm) (hf : Nat.blt (Nat.add Cp (fsum c P S Q)) Cm = true) : CovBy Q PR P' c := by
 intro g hg
 exfalso
 have h0 := h g hg
 have h1 := fsum_ge P S hg.1 Q le_rfl
 have h2 : ((Nat.add Cp (fsum c P S Q) : ℕ) : ℝ) < Cm := by exact_mod_cast Nat.blt_eq.mp hf
 simp only [Nat.add_eq] at h2; push_cast at h2
 linarith
theorem incell_root {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} {W : ℕ}
   (hA : ∀ k < PR.length, c.A.getD k 0 = 0) (hB : ∀ k < PR.length, c.B.getD k 0 = W) (hW : sumR c.U 0 Q ≤ W)
   {g : ℕ → ℝ} (hb : InBox Q c g) : InCell Q PR c g := by
 refine ⟨hb, fun k hk => ⟨?_, ?_⟩⟩
 · rw [hA k hk, Nat.cast_zero, zero_div, gsum]
   exact Finset.sum_nonneg fun r hr =>
     le_trans (div_nonneg (Nat.cast_nonneg _) SC_pos.le) (hb r (by have := hPR k hk; simp at hr; omega)).1
 · obtain ⟨hij, hjQ⟩ := hPR k hk
   have h1 := sum_hi hb (pI PR k) (pJ PR k - pI PR k) (by omega)
   rw [show pI PR k + (pJ PR k - pI PR k) = pJ PR k by omega] at h1
   refine h1.trans (div_le_div_of_nonneg_right ?_ SC_pos.le)
   rw [hB k hk]
   have h2 : ((sumR c.U (pI PR k) (pJ PR k - pI PR k) : ℕ) : ℝ) ≤ ((sumR c.U 0 Q : ℕ) : ℝ) := by
     rw [sumR_eq, sumR_eq]
     apply Finset.sum_le_sum_of_subset_of_nonneg
     · intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
     · intro _ _ _; exact Nat.cast_nonneg _
   exact h2.trans (by exact_mod_cast hW)
theorem list_of_getD (M : List ℕ) (n : ℕ) (h : M.length = n) : (List.range n).map (fun r => M.getD r 0) = M := by
 subst h
 apply List.ext_getElem (by simp)
 intro r h1 h2
 simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
theorem brec_dep {α : Sort _} {P : α → Prop} {a b : α} {c : Bool} (ha : c = false → P a) (hb : c = true → P b) :
   P (Bool.rec (motive := fun _ => α) a b c) := by cases c <;> simp_all
def forceT {α : Sort _} (a : ℕ) (k : ℕ → α) : α := Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) a
theorem forceT_eq {α : Sort _} (a : ℕ) (k : ℕ → α) : forceT a k = k a := by cases a <;> rfl
def gptF (L U jj : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Bool.rec (motive := fun _ => ℕ) 8 5 (Nat.beq (Nat.land (Nat.shiftRight jj 6) 1) 1)) fun gs =>
    forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 gs) 1)) gs) gs) fun ga =>
    forceR (Nat.shiftLeft (Nat.shiftRight U gs) gs) fun gb =>
    forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) (Nat.land jj 63)) 5)) gs) gs) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga))
   L (Nat.beq jj 33)
def uc (L U : ℕ) : ℕ := nmax U (Nat.add L 1)
theorem le_uc (L U : ℕ) : U ≤ uc L U := le_nmax_left _ _
def mvT (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ := mval top bk f L U (mwc k m) (mw1 k m) (mw2 k m) p r
def mcpT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcp f L0 (mw1 k m) (mw2 k m) p r
def mcnT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcn f L0 (mw1 k m) (mw2 k m) p r
def mslT (f : ℕ → ℕ) (k m p r : ℕ) : ℕ := msl f (mw1 k m) (mw2 k m) p r
def mwT (k m : ℕ) : ℕ := Nat.add (mw1 k m) (mw2 k m)
def mvK (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.mul 1024 (lb top bk L U))
     (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (f p))) (Nat.mul m (lo32 (f r)))) (Nat.beq k 3))
   (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 (f p)))) (Nat.beq k 2))
   (Nat.mul 1024 (lo32 (f p))) (Nat.beq k 1)
def chg (f : ℕ → ℕ) (sg : Bool) (L0 l p : ℕ) : ℕ :=
 Nat.mul (Nat.mul l (Bool.rec (motive := fun _ => ℕ) (Nat.sub 2000000000 (hi32 (hi32 (f p)))) (Nat.sub (hi32 (hi32 (f p))) 2000000000) sg)) (Nat.sub p L0)
def mcK (f : ℕ → ℕ) (sg : Bool) (L0 k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
     (Nat.add (chg f sg L0 (Nat.sub 1024 m) p) (chg f sg L0 m r)) (Nat.beq k 3))
   (chg f sg L0 m p) (Nat.beq k 2))
   (chg f sg L0 1024 p) (Nat.beq k 1)
def mslK (f : ℕ → ℕ) (k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
     (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (hi32 (f p)))) (Nat.mul m (lo32 (hi32 (f r))))) (Nat.beq k 3))
   (Nat.mul m (lo32 (hi32 (f p)))) (Nat.beq k 2))
   (Nat.mul 1024 (lo32 (hi32 (f p)))) (Nat.beq k 1)
theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
 by_cases h : a = b
 · subst h; simp
 · simp [h, beq_false h]
theorem mvK_eq (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : mvK top bk f L U k m p r = mvT top bk f L U k m p r := by
 unfold mvK mvT mval mwc mw1 mw2
 rcases Nat.lt_or_ge k 4 with hk | hk
 · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
 · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mcpK_eq (f : ℕ → ℕ) (L0 k m p r : ℕ) : mcK f true L0 k m p r = mcpT f L0 k m p r := by
 unfold mcK chg mcpT mcp mw1 mw2
 rcases Nat.lt_or_ge k 4 with hk | hk
 · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
 · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mcnK_eq (f : ℕ → ℕ) (L0 k m p r : ℕ) : mcK f false L0 k m p r = mcnT f L0 k m p r := by
 unfold mcK chg mcnT mcn mw1 mw2
 rcases Nat.lt_or_ge k 4 with hk | hk
 · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
 · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
theorem mslK_eq (f : ℕ → ℕ) (k m p r : ℕ) : mslK f k m p r = mslT f k m p r := by
 unfold mslK mslT msl mw1 mw2
 rcases Nat.lt_or_ge k 4 with hk | hk
 · interval_cases k <;> simp [beq_dec, Nat.add_eq, Nat.mul_eq]
 · simp [beq_false (show k ≠ 1 by omega), beq_false (show k ≠ 2 by omega), beq_false (show k ≠ 3 by omega), Nat.add_eq, Nat.mul_eq]
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
abbrev Term := ℕ × ℕ × ℕ × ℕ
def tI (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).1
def tJ (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.1
def tA (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.1
def tK (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.2
def isum (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (f i)) n
def iall (f : ℕ → Bool) (n : ℕ) : Bool :=
 Nat.rec (motive := fun _ => Bool) true (fun i acc => Bool.rec (motive := fun _ => Bool) false (f i) acc) n
theorem isum_cast (f : ℕ → ℕ) : ∀ n, ((isum f n : ℕ) : ℝ) = ∑ i ∈ Finset.range n, ((f i : ℕ) : ℝ)
 | 0 => by simp [isum]
 | n + 1 => by
   rw [Finset.sum_range_succ, ← isum_cast f n]
   show ((Nat.add (isum f n) (f n) : ℕ) : ℝ) = _
   simp only [Nat.add_eq]; push_cast; ring
theorem iall_true {f : ℕ → Bool} : ∀ {n}, iall f n = true → ∀ i < n, f i = true
 | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
 | n + 1, h, i, hi => by
   have h' : Bool.rec (motive := fun _ => Bool) false (f n) (iall f n) = true := h
   cases hc : iall f n
   · rw [hc] at h'; exact absurd h' Bool.false_ne_true
   · rw [hc] at h'
     rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
     · exact iall_true hc i hi
     · subst hi; exact h'
theorem brec_and {x y : Bool} (h : Bool.rec (motive := fun _ => Bool) false x y = true) : y = true ∧ x = true := by
 cases y <;> simp_all
theorem brec0_cast (X : ℕ) (b : Bool) :
   ((Bool.rec (motive := fun _ => ℕ) 0 X b : ℕ) : ℝ) = if b = true then (X : ℝ) else 0 := by cases b <;> simp
theorem inr_true (r i j : ℕ) : inr r i j = true ↔ i ≤ r ∧ r < j := by
 unfold inr
 by_cases h1 : i ≤ r
 · rw [Nat.ble_eq_true_of_le h1]; simp [Nat.blt_eq, h1]
 · rw [show Nat.ble i r = false from Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)]; simp [h1]
def eL (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (nmax (c.A.getD (tK TS n) 0) (sumR c.L (tI TS n) (tJ TS n - tI TS n)))
   (c.L.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
def eU (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (nmin (c.B.getD (tK TS n) 0) (sumR c.U (tI TS n) (tJ TS n - tI TS n)))
   (c.U.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
def eL0 (TS : List Term) (c : Cl) (n : ℕ) : ℕ := sumR c.L (tI TS n) (tJ TS n - tI TS n)
def Ng (f : ℕ → ℕ) (bs : List ℕ) (TS FS : List Term) (P S : List ℕ) (r : ℕ) : ℕ :=
 Nat.sub (Nat.add (Nat.mul 2000000000 (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (mwT (tI FS n) (tJ FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (P.getD r 0))
   (Nat.add (Nat.add (Nat.mul 1024000000000 (bs.getD r 0)) (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (S.getD r 0))
def Fg (Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : ℝ :=
 ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * g r
   + ∑ n ∈ Finset.range TS.length, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
def Pg (cN Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : Prop := (cN : ℝ) ≤ Fg Q bs TS g ∨ g (Q - 1) < g 0
def TSok (Q : ℕ) (PR : List (ℕ × ℕ)) (TS : List Term) : Prop :=
 ∀ n < TS.length, tI TS n < tJ TS n ∧ tJ TS n ≤ Q ∧
   (tJ TS n - tI TS n = 1 ∨ (tK TS n < PR.length ∧ pI PR (tK TS n) = tI TS n ∧ pJ PR (tK TS n) = tJ TS n))
instance (Q : ℕ) (PR : List (ℕ × ℕ)) (TS : List Term) : Decidable (TSok Q PR TS) := by unfold TSok; infer_instance
theorem term_range {Q : ℕ} {PR : List (ℕ × ℕ)} {TS : List Term} (hPR : PRok Q PR) (hTS : TSok Q PR TS) {c : Cl} {g : ℕ → ℝ}
   (hg : InCell Q PR c g) {n : ℕ} (hn : n < TS.length) :
   eL0 TS c n ≤ eL TS c n ∧ ((eL TS c n : ℕ) : ℝ) / SC ≤ gsum g (tI TS n) (tJ TS n) ∧
     gsum g (tI TS n) (tJ TS n) ≤ ((eU TS c n : ℕ) : ℝ) / SC := by
 obtain ⟨hij, hjQ, h1 | ⟨hk, hpi, hpj⟩⟩ := hTS n hn
 · have hb : Nat.beq (tJ TS n - tI TS n) 1 = true := by rw [h1]; rfl
   have hj : tJ TS n = tI TS n + 1 := by omega
   have hs : gsum g (tI TS n) (tJ TS n) = g (tI TS n) := by rw [hj, gsum]; simp
   unfold eL eU eL0
   rw [hb, h1, hs]
   exact ⟨le_rfl, (hg.1 _ (by omega)).1, (hg.1 _ (by omega)).2⟩
 · have h2 := (hPR _ hk).1
   rw [hpi, hpj] at h2
   have hb : Nat.beq (tJ TS n - tI TS n) 1 = false := Bool.eq_false_iff.mpr fun h => by
     have := Nat.eq_of_beq_eq_true h; omega
   have hn' : tI TS n + (tJ TS n - tI TS n) = tJ TS n := by omega
   have hsl := sum_lo hg.1 (tI TS n) (tJ TS n - tI TS n) (by omega)
   have hsu := sum_hi hg.1 (tI TS n) (tJ TS n - tI TS n) (by omega)
   rw [hn'] at hsl hsu
   have hA := (hg.2 _ hk).1
   have hB := (hg.2 _ hk).2
   rw [hpi, hpj] at hA hB
   unfold eL eU eL0
   rw [hb]
   exact ⟨le_nmax_right _ _, lo_nmax hA hsl, hi_nmin hB hsu⟩
theorem span_eq {Q : ℕ} {TS : List Term} {c : Cl} (g : ℕ → ℝ) {n : ℕ} (hij : tI TS n ≤ tJ TS n) (hjQ : tJ TS n ≤ Q) :
   gsum g (tI TS n) (tJ TS n) - ((eL0 TS c n : ℕ) : ℝ) / 32768 =
     ∑ r ∈ Finset.range Q, if tI TS n ≤ r ∧ r < tJ TS n then g r - ((c.L.getD r 0 : ℕ) : ℝ) / 32768 else 0 := by
 rw [← Finset.sum_filter]
 have hf : Finset.filter (fun r => tI TS n ≤ r ∧ r < tJ TS n) (Finset.range Q) = Finset.Ico (tI TS n) (tJ TS n) := by
   ext r; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
 rw [hf, Finset.sum_sub_distrib, ← Finset.sum_div, gsum, eL0, sumR_eq, show tI TS n + (tJ TS n - tI TS n) = tJ TS n by omega]
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def coverChk (cN aAdj : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
 | pos, S, [] => decide (S ≤ pos)
 | pos, S, (a, b, cl) :: rest =>
     decide (a = pos) && decide (a ≤ b) && decide (b < KB)
       && (!cl || Nat.ble (cN * SW) (aAdj * CellN.WZ ⟨a * KB + b, 0⟩))
       && coverChk cN aAdj b S rest
def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
 cover.filterMap fun s => if s.2.2 then none else some (s.1, s.2.1)
theorem coverChk_sound (cN aAdj : ℕ) :
   ∀ (cover : List (ℕ × ℕ × Bool)) (pos S : ℕ), coverChk cN aAdj pos S cover = true →
     ∀ v : ℝ, (pos : ℝ) / SC ≤ v → v < (S : ℝ) / SC →
       (cN : ℝ) ≤ (aAdj : ℝ) * wfun v ∨
         ∃ s ∈ cover, s.2.2 = false ∧ (s.1 : ℝ) / SC ≤ v ∧ v ≤ (s.2.1 : ℝ) / SC ∧ s.2.1 < KB := by
 intro cover
 induction cover with
 | nil =>
   intro pos S h v hv1 hv2
   simp only [coverChk, decide_eq_true_eq] at h
   have : (S : ℝ) / SC ≤ (pos : ℝ) / SC := div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num [SC])
   exact absurd (lt_of_le_of_lt (this.trans hv1) hv2) (lt_irrefl _)
 | cons s rest ih =>
   intro pos S h v hv1 hv2
   obtain ⟨a, b, cl⟩ := s
   simp only [coverChk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
     Bool.not_true] at h
   obtain ⟨⟨⟨⟨hpos, hab⟩, hbK⟩, hcl⟩, hrest⟩ := h
   rcases le_total v ((b : ℝ) / SC) with hvb | hvb
   · rcases hcl with hcl | hcl
     · right
       exact ⟨(a, b, cl), List.mem_cons_self .., hcl, by rw [hpos]; exact hv1, hvb, hbK⟩
     · left
       rw [Nat.ble_eq] at hcl
       have hLN : (⟨a * KB + b, 0⟩ : CellN).LN = a := by
         simp only [CellN.LN]; rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by norm_num [KB]), Nat.div_eq_of_lt hbK, Nat.zero_add]
       have hUN : (⟨a * KB + b, 0⟩ : CellN).UN = b := by
         simp only [CellN.UN]; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbK]
       have hW := cellN_soundWZ ⟨a * KB + b, 0⟩ v (by rw [hLN, hpos]; exact hv1) (by rw [hUN]; exact hvb)
       have hq := (Nat.cast_le (α := ℝ)).mpr hcl
       push_cast at hq
       have hSW : (0:ℝ) < SW := by norm_num [SW]
       have hm2 : (aAdj : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) ≤ (aAdj : ℝ) * wfun v :=
         mul_le_mul_of_nonneg_left hW (by positivity)
       calc (cN : ℝ) = (cN : ℝ) * SW / SW := by field_simp
         _ ≤ (aAdj : ℝ) * ((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW := by apply div_le_div_of_nonneg_right _ hSW.le; linarith
         _ = (aAdj : ℝ) * (((⟨a * KB + b, 0⟩ : CellN).WZ : ℝ) / SW) := by ring
         _ ≤ _ := hm2
   · rcases ih b S hrest v hvb hv2 with h | ⟨s', hs', he, h1, h2, h3⟩
     · left; exact h
     · right; exact ⟨s', List.mem_cons_of_mem _ hs', he, h1, h2, h3⟩
theorem badOf_mem {cover : List (ℕ × ℕ × Bool)} {s : ℕ × ℕ × Bool} (hs : s ∈ cover)
   (he : s.2.2 = false) : (s.1, s.2.1) ∈ badOf cover := by
 simp only [badOf, List.mem_filterMap]
 exact ⟨s, hs, by simp [he]⟩
def rootCl (Q NC W : ℕ) (cov : List (List (ℕ × ℕ × Bool))) (idx : ℕ → ℕ) : Cl :=
 ⟨(List.range Q).map fun r => ((badOf (cov.getD r [])).getD (idx r) (0, 0)).1,
  (List.range Q).map fun r => ((badOf (cov.getD r [])).getD (idx r) (0, 0)).2,
  List.replicate NC 0, List.replicate NC W⟩
theorem getD_map_range (f : ℕ → ℕ) {Q r : ℕ} (hr : r < Q) : ((List.range Q).map f).getD r 0 = f r := by
 simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr]
theorem Fg_ge_lin {Q : ℕ} {bs : List ℕ} {TS : List Term} {g : ℕ → ℝ} (hg : ∀ r < Q, 0 ≤ g r) {r : ℕ} (hr : r < Q) :
   ((bs.getD r 0 : ℕ) : ℝ) * g r ≤ Fg Q bs TS g := by
 unfold Fg
 have h1 := Finset.single_le_sum (f := fun r => ((bs.getD r 0 : ℕ) : ℝ) * g r)
   (fun r hr => mul_nonneg (Nat.cast_nonneg _) (hg r (Finset.mem_range.mp hr))) (Finset.mem_range.mpr hr)
 have h2 := Finset.sum_nonneg fun n (_ : n ∈ Finset.range TS.length) =>
   mul_nonneg (Nat.cast_nonneg (tA TS n)) (wfun_nonneg (gsum g (tI TS n) (tJ TS n)))
 linarith
theorem Fg_ge_term {Q : ℕ} {bs : List ℕ} {TS : List Term} {g : ℕ → ℝ} (hg : ∀ r < Q, 0 ≤ g r) {n : ℕ}
   (hn : n < TS.length) : ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)) ≤ Fg Q bs TS g := by
 unfold Fg
 have h1 := Finset.single_le_sum (f := fun n => ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n)))
   (fun n _ => mul_nonneg (Nat.cast_nonneg _) (wfun_nonneg _)) (Finset.mem_range.mpr hn)
 have h2 := Finset.sum_nonneg fun r (hr : r ∈ Finset.range Q) =>
   mul_nonneg (Nat.cast_nonneg (bs.getD r 0)) (hg r (Finset.mem_range.mp hr))
 linarith
theorem root_cover {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {cN : ℕ} {bs : List ℕ} {TS : List Term}
   (adj : ℕ → ℕ) (hadj : ∀ r < Q, adj r < TS.length ∧ tI TS (adj r) = r ∧ tJ TS (adj r) = r + 1)
   (Smax : ℕ → ℕ) (hS : ∀ r < Q, cN * SC ≤ bs.getD r 0 * Smax r)
   (cov : List (List (ℕ × ℕ × Bool)))
   (hcov : ∀ r < Q, coverChk cN (tA TS (adj r)) (SC / 2) (Smax r) (cov.getD r []) = true)
   (hwin : ∀ r < Q, cN * 4 ≤ tA TS (adj r)) (W : ℕ) (hW : Q * KB ≤ W)
   (hrun : ∀ idx : ℕ → ℕ, (∀ r < Q, idx r < (badOf (cov.getD r [])).length) →
     CovBy Q PR (Pg cN Q bs TS) (rootCl Q PR.length W cov idx))
   (g : ℕ → ℝ) (hg : ∀ r < Q, 0 ≤ g r) : Pg cN Q bs TS g := by
 classical
 have hSC : (0:ℝ) < SC := by norm_num [SC]
 by_cases hgood : ∃ r < Q, (cN : ℝ) ≤ Fg Q bs TS g
 · obtain ⟨r, -, h⟩ := hgood; exact Or.inl h
 push_neg at hgood
 have hbad : ∀ r < Q, ∃ i, i < (badOf (cov.getD r [])).length ∧
     (((badOf (cov.getD r [])).getD i (0, 0)).1 : ℝ) / SC ≤ g r ∧ g r ≤ (((badOf (cov.getD r [])).getD i (0, 0)).2 : ℝ) / SC ∧
     ((badOf (cov.getD r [])).getD i (0, 0)).2 < KB := by
   intro r hr
   obtain ⟨hn, hi, hj⟩ := hadj r hr
   have hsr : gsum g (tI TS (adj r)) (tJ TS (adj r)) = g r := by rw [hi, hj, gsum]; simp
   have hterm := Fg_ge_term (bs := bs) hg hn
   rw [hsr] at hterm
   by_cases hcut : (Smax r : ℝ) / SC ≤ g r
   · exfalso
     have hq := (Nat.cast_le (α := ℝ)).mpr (hS r hr); push_cast at hq
     have h1 : (cN : ℝ) ≤ (bs.getD r 0 : ℝ) * g r := by
       have : (cN : ℝ) ≤ (bs.getD r 0 : ℝ) * ((Smax r : ℝ) / SC) := by
         rw [mul_div_assoc', le_div_iff₀ hSC]; linarith
       exact this.trans (mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _))
     exact absurd (h1.trans (Fg_ge_lin hg hr)) (not_le.mpr (hgood r hr))
   push_neg at hcut
   rcases le_total (g r) (((SC / 2 : ℕ) : ℝ) / SC) with hw | hw
   · exfalso
     have hhalf : ((SC / 2 : ℕ) : ℝ) / SC = 1 / 2 := by norm_num [SC]
     have h19 := wfun_window (g r) (hg r hr) (by rw [hhalf] at hw; exact hw)
     have hq := (Nat.cast_le (α := ℝ)).mpr (hwin r hr); push_cast at hq
     have h1 : (cN : ℝ) ≤ (tA TS (adj r) : ℝ) * wfun (g r) := by
       nlinarith [mul_le_mul_of_nonneg_left h19 (Nat.cast_nonneg (tA TS (adj r)) : (0:ℝ) ≤ (tA TS (adj r) : ℝ))]
     exact absurd (h1.trans hterm) (not_le.mpr (hgood r hr))
   rcases coverChk_sound cN (tA TS (adj r)) (cov.getD r []) (SC / 2) (Smax r) (hcov r hr) (g r) hw hcut with
     hclear | ⟨s, hs, he, h1, h2, h3⟩
   · exact absurd (hclear.trans hterm) (not_le.mpr (hgood r hr))
   obtain ⟨i, hi', hsi⟩ := List.mem_iff_getElem.mp (badOf_mem hs he)
   refine ⟨i, hi', ?_, ?_, ?_⟩
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h1
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h2
   · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h3
 choose! idx hidx using hbad
 apply hrun idx (fun r hr => (hidx r hr).1) g
 refine incell_root hPR (W := W) (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk])
   (fun k hk => by simp [rootCl, List.getD_eq_getElem?_getD, hk]) ?_ (fun r hr => ?_)
 · have h1 : ((sumR (rootCl Q PR.length W cov idx).U 0 Q : ℕ) : ℝ) ≤ ((Q * KB : ℕ) : ℝ) := by
     rw [sumR_eq, Nat.zero_add]; push_cast
     calc ∑ r ∈ Finset.Ico 0 Q, (((rootCl Q PR.length W cov idx).U.getD r 0 : ℕ) : ℝ)
         ≤ ∑ r ∈ Finset.Ico 0 Q, (KB : ℝ) := by
           apply Finset.sum_le_sum; intro r hr
           have hr' : r < Q := (Finset.mem_Ico.mp hr).2
           simp only [rootCl]; rw [getD_map_range _ hr']
           exact_mod_cast (hidx r hr').2.2.2.le
       _ = (Q : ℝ) * KB := by simp
   exact (by exact_mod_cast h1 : sumR _ 0 Q ≤ Q * KB).trans hW
 · simp only [rootCl]; rw [getD_map_range _ hr, getD_map_range _ hr]
   exact ⟨(hidx r hr).2.1, (hidx r hr).2.2.1⟩
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def sI (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s else pI PR (s - Q)
def sJ (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s + 1 else pJ PR (s - Q)
def sLo (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.L.getD s 0 else c.A.getD (s - Q) 0
def sHi (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.U.getD s 0 else c.B.getD (s - Q) 0
def ClLen (Q n : ℕ) (c : Cl) : Prop := c.L.length = Q ∧ c.U.length = Q ∧ c.A.length = n ∧ c.B.length = n
theorem gsum_single (g : ℕ → ℝ) (s : ℕ) : gsum g s (s + 1) = g s := by simp [gsum]
theorem gsum_add (g : ℕ → ℝ) {i k j : ℕ} (h1 : i ≤ k) (h2 : k ≤ j) : gsum g i k + gsum g k j = gsum g i j :=
 Finset.sum_Ico_consecutive _ h1 h2
theorem gsum_nonneg {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) {i j : ℕ} (hj : j ≤ Q) :
   0 ≤ gsum g i j :=
 Finset.sum_nonneg fun r hr =>
   (div_nonneg (Nat.cast_nonneg _) SC_pos.le).trans (hg.1 r (by simp at hr; omega)).1
theorem slot_ok {Q : ℕ} {PR : List (ℕ × ℕ)} {c : Cl} {g : ℕ → ℝ} (hg : InCell Q PR c g) {s : ℕ}
   (hs : s < Q + PR.length) :
   ((sLo Q c s : ℕ) : ℝ) / SC ≤ gsum g (sI Q PR s) (sJ Q PR s) ∧
     gsum g (sI Q PR s) (sJ Q PR s) ≤ ((sHi Q c s : ℕ) : ℝ) / SC := by
 unfold sLo sHi sI sJ
 split_ifs with h
 · rw [gsum_single]; exact hg.1 s h
 · exact hg.2 (s - Q) (by omega)
theorem natsub_lo {x y : ℕ} {t : ℝ} (h : (x : ℝ) / SC - (y : ℝ) / SC ≤ t) (ht : 0 ≤ t) :
   ((Nat.sub x y : ℕ) : ℝ) / SC ≤ t := by
 rcases le_total y x with hxy | hxy
 · rw [Nat.sub_eq, Nat.cast_sub hxy, sub_div]; exact h
 · rw [Nat.sub_eq, Nat.sub_eq_zero_of_le hxy]; simpa using ht
theorem natsub_hi {x y : ℕ} {t : ℝ} (h : t ≤ (x : ℝ) / SC - (y : ℝ) / SC) (ht : 0 ≤ t) :
   t ≤ ((Nat.sub x y : ℕ) : ℝ) / SC := by
 have hSC := SC_pos
 have hyx : y ≤ x := by
   have : (y : ℝ) / SC ≤ (x : ℝ) / SC := by linarith
   exact_mod_cast (div_le_div_iff_of_pos_right hSC).mp this
 rw [Nat.sub_eq, Nat.cast_sub hyx, sub_div]; exact h
theorem cast_add_div (x y : ℕ) : ((Nat.add x y : ℕ) : ℝ) / SC = (x : ℝ) / SC + (y : ℝ) / SC := by
 rw [Nat.add_eq, Nat.cast_add, add_div]
def matC (PR : List (ℕ × ℕ)) (c : Cl) : Cl :=
 ⟨c.L, c.U, imap (fun k _ => fLe PR c k) 0 c.A, imap (fun k _ => fUe PR c k) 0 c.B⟩
theorem mat_gen {Q : ℕ} {PR : List (ℕ × ℕ)} (hPR : PRok Q PR) {c : Cl} (hc : ClLen Q PR.length c)
   {g : ℕ → ℝ} (hg : InCell Q PR c g) :
   (∀ k < PR.length, femp PR c k = false) ∧ InCell Q PR (matC PR c) g := by
 have hk : ∀ k < PR.length, ((fLe PR c k : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
     gsum g (pI PR k) (pJ PR k) ≤ ((fUe PR c k : ℕ) : ℝ) / SC := by
   intro k hk
   obtain ⟨hij, hjQ⟩ := hPR k hk
   have hn : pI PR k + (pJ PR k - pI PR k) = pJ PR k := by omega
   have hsl := sum_lo hg.1 (pI PR k) (pJ PR k - pI PR k) (by omega)
   have hsu := sum_hi hg.1 (pI PR k) (pJ PR k - pI PR k) (by omega)
   rw [hn] at hsl hsu
   exact ⟨lo_nmax (hg.2 k hk).1 hsl, hi_nmin (hg.2 k hk).2 hsu⟩
 refine ⟨fun k hkk => ?_, hg.1, fun k hkk => ?_⟩
 · have h := hk k hkk
   have h2 : fLe PR c k ≤ fUe PR c k := by
     have : ((fLe PR c k : ℕ) : ℝ) / SC ≤ ((fUe PR c k : ℕ) : ℝ) / SC := h.1.trans h.2
     exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp this
   unfold femp; exact Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (Nat.not_lt.mpr h2)
 · show (((imap (fun k _ => fLe PR c k) 0 c.A).getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
     gsum g (pI PR k) (pJ PR k) ≤ (((imap (fun k _ => fUe PR c k) 0 c.B).getD k 0 : ℕ) : ℝ) / SC
   rw [imap_getD _ _ _ _ (by rw [hc.2.2.1]; exact hkk), imap_getD _ _ _ _ (by rw [hc.2.2.2]; exact hkk), Nat.zero_add]
   exact hk k hkk
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell
def zpt (v c x lbv : ℕ) : Bool :=
 Nat.ble (Nat.add (Nat.mul v 32768) (Nat.mul (Nat.mul 10 (Nat.sub 2000000000 c)) x))
   (Nat.add (Nat.mul lbv 32768) (Nat.mul (Nat.mul 10 (Nat.sub c 2000000000)) x))
def zpc (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (forceB (lb top bk x0 x1) fun lbv =>
     Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
       (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
   true (Nat.ble x1 x0)
def zpe (a b n k : ℕ) : ℕ := Nat.add a (Nat.div (Nat.mul (Nat.sub b a) k) n)
def zside (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 iall (fun k => zpc top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n
def zsideF (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 zside top bk v c p a b 1 right || zside top bk v c p a b 2 right || zside top bk v c p a b n right
theorem line_le_ends {v d p a b c x : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (ha : v + d * (a - p) ≤ c)
   (hb : v + d * (b - p) ≤ c) : v + d * (x - p) ≤ c := by
 rcases le_total 0 d with h | h
 · nlinarith [mul_le_mul_of_nonneg_left hx2 h]
 · nlinarith [mul_le_mul_of_nonpos_left hx1 h]
theorem pieces_cover (e : ℕ → ℝ) : ∀ m : ℕ, ∀ s : ℝ, e 0 ≤ s → s ≤ e m → e 0 < e m →
   ∃ k < m, e k < e (k + 1) ∧ e k ≤ s ∧ s ≤ e (k + 1)
 | 0, _, _, _, h => absurd h (lt_irrefl _)
 | m + 1, s, h0, hm, hlt => by
   by_cases h1 : s ≤ e m
   · by_cases h2 : e 0 < e m
     · obtain ⟨k, hk, hk'⟩ := pieces_cover e m s h0 h1 h2
       exact ⟨k, by omega, hk'⟩
     · have hs : s = e m := le_antisymm h1 (by linarith [not_lt.mp h2])
       exact ⟨m, by omega, by rw [← hs]; linarith [not_lt.mp h2], le_of_eq hs.symm, hm⟩
   · exact ⟨m, by omega, by linarith [not_le.mp h1], (not_le.mp h1).le, hm⟩
theorem zpt_sound {v c x lbv : ℕ} (h : zpt v c x lbv = true) :
   (v : ℝ) * 32768 + 10 * (2000000000 - (c : ℝ)) * x ≤ (lbv : ℝ) * 32768 := by
 unfold zpt at h
 simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
 have h' : ((v * 32768 + 10 * (2000000000 - c) * x : ℕ) : ℝ) ≤ ((lbv * 32768 + 10 * (c - 2000000000) * x : ℕ) : ℝ) := by
   exact_mod_cast h
 push_cast at h'
 have e2 : ((c - 2000000000 : ℕ) : ℝ) * x - ((2000000000 - c : ℕ) : ℝ) * x = ((c : ℝ) - 2000000000) * x := by
   rw [← sub_mul, natsub_pair]
 linarith
theorem zpiece_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p x0 x1 : ℕ} {w1p : ℝ}
   (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ))
   (hz : zpt v M (Nat.sub x0 p) (lb top bk x0 x1) = true) (hz' : zpt v M (Nat.sub x1 p) (lb top bk x0 x1) = true)
   (hp : p ≤ x0) (h01 : x0 ≤ x1) {s : ℝ} (hs1 : (x0 : ℝ) / SC ≤ s) (hs2 : s ≤ (x1 : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
 have hl := hlb x0 x1 s hs1 hs2
 have h0 := zpt_sound hz
 have h1 := zpt_sound hz'
 rw [Nat.sub_eq, Nat.cast_sub hp] at h0
 rw [Nat.sub_eq, Nat.cast_sub (hp.trans h01)] at h1
 rw [hSC] at hs1 hs2 ⊢
 rw [div_le_iff₀ (by norm_num)] at hs1
 rw [le_div_iff₀ (by norm_num)] at hs2
 rw [div_le_iff₀ (by norm_num)] at hl
 have hφ := line_le_ends (v := (v : ℝ) * 32768) (d := 10 * (2000000000 - (M : ℝ))) (p := (p : ℝ))
   (c := (lb top bk x0 x1 : ℝ) * 32768) (by linarith : (x0 : ℝ) ≤ s * 32768) (by linarith : s * 32768 ≤ (x1 : ℝ)) h0 h1
 have hps : (p : ℝ) ≤ s * 32768 := le_trans (by exact_mod_cast hp) (by linarith : (x0 : ℝ) ≤ s * 32768)
 have hw := mul_le_mul_of_nonneg_right hM (sub_nonneg.mpr hps)
 rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
 have e : w1p * (s - (p : ℝ) / 32768) * 10000000000 = 1000000000 * w1p * (s * 32768 - p) * (10 / 32768) := by ring
 nlinarith [hφ, hw, hl, e]
theorem zpiece_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p x0 x1 : ℕ} {w1p : ℝ}
   (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p)
   (hz : zpt v P (Nat.sub p x0) (lb top bk x0 x1) = true) (hz' : zpt v P (Nat.sub p x1) (lb top bk x0 x1) = true)
   (hp : x1 ≤ p) (h01 : x0 ≤ x1) {s : ℝ} (hs1 : (x0 : ℝ) / SC ≤ s) (hs2 : s ≤ (x1 : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
 have hl := hlb x0 x1 s hs1 hs2
 have h0 := zpt_sound hz
 have h1 := zpt_sound hz'
 rw [Nat.sub_eq, Nat.cast_sub (h01.trans hp)] at h0
 rw [Nat.sub_eq, Nat.cast_sub hp] at h1
 rw [hSC] at hs1 hs2 ⊢
 rw [div_le_iff₀ (by norm_num)] at hs1
 rw [le_div_iff₀ (by norm_num)] at hs2
 rw [div_le_iff₀ (by norm_num)] at hl
 have h0' : (v : ℝ) * 32768 + 10 * ((P : ℝ) - 2000000000) * ((x0 : ℝ) - p) ≤ (lb top bk x0 x1 : ℝ) * 32768 := by
   linarith
 have h1' : (v : ℝ) * 32768 + 10 * ((P : ℝ) - 2000000000) * ((x1 : ℝ) - p) ≤ (lb top bk x0 x1 : ℝ) * 32768 := by
   linarith
 have hφ := line_le_ends (v := (v : ℝ) * 32768) (d := 10 * ((P : ℝ) - 2000000000)) (p := (p : ℝ))
   (c := (lb top bk x0 x1 : ℝ) * 32768) (by linarith : (x0 : ℝ) ≤ s * 32768) (by linarith : s * 32768 ≤ (x1 : ℝ))
   h0' h1'
 have hps : s * 32768 ≤ (p : ℝ) := le_trans (by linarith : s * 32768 ≤ (x1 : ℝ)) (by exact_mod_cast hp)
 have hw := mul_le_mul_of_nonpos_right hP (sub_nonpos.mpr hps)
 rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
 have e : w1p * (s - (p : ℝ) / 32768) * 10000000000 = 1000000000 * w1p * (s * 32768 - p) * (10 / 32768) := by ring
 nlinarith [hφ, hw, hl, e]
theorem zpe_eq (a b n k : ℕ) : zpe a b n k = a + (b - a) * k / n := rfl
theorem zpe_zero (a b n : ℕ) : zpe a b n 0 = a := by rw [zpe_eq]; simp
theorem zpe_n (a b n : ℕ) (hn : 0 < n) (hab : a ≤ b) : zpe a b n n = b := by
 rw [zpe_eq, Nat.mul_div_cancel _ hn]; omega
theorem zpe_ge (a b n k : ℕ) : a ≤ zpe a b n k := by rw [zpe_eq]; exact Nat.le_add_right _ _
theorem zpe_le (a b n k : ℕ) (hab : a ≤ b) (hk : k ≤ n) : zpe a b n k ≤ b := by
 rw [zpe_eq]
 have : (b - a) * k / n ≤ b - a := by
   rcases Nat.eq_zero_or_pos n with h | h
   · subst h; simp
   · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hk)
 omega
theorem zside_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p a b n : ℕ} {w1p : ℝ}
   (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ)) (h : zside top bk v M p a b n true = true)
   (hpa : p ≤ a) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 have hSC := SC_pos
 set e : ℕ → ℝ := fun k => ((zpe a b n k : ℕ) : ℝ) / SC with he
 have e0 : e 0 = (a : ℝ) / SC := by simp only [he, zpe_zero]
 have en : e n = (b : ℝ) / SC := by simp only [he, zpe_n a b n hn hab.le]
 obtain ⟨k, hk, hlt, hk1, hk2⟩ := pieces_cover e n s (e0 ▸ hs1) (en ▸ hs2)
   (by rw [e0, en]; exact div_lt_div_of_pos_right (by exact_mod_cast hab) hSC)
 have hpc := iall_true h k hk
 beta_reduce at hpc
 have hlt' : zpe a b n k < zpe a b n (Nat.add k 1) := by
   have : ((zpe a b n k : ℕ) : ℝ) < ((zpe a b n (k + 1) : ℕ) : ℝ) := (div_lt_div_iff_of_pos_right hSC).mp hlt
   exact_mod_cast this
 unfold zpc at hpc
 rw [show Nat.ble (zpe a b n (Nat.add k 1)) (zpe a b n k) = false from
   Bool.eq_false_iff.mpr fun e' => absurd (Nat.le_of_ble_eq_true e') (Nat.not_le.mpr hlt'), forceB_eq] at hpc
 simp only [Bool.and_eq_true] at hpc
 exact zpiece_right hlb hM hpc.1 hpc.2 (hpa.trans (zpe_ge a b n k)) hlt'.le hk1 hk2
theorem zside_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p a b n : ℕ} {w1p : ℝ}
   (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p) (h : zside top bk v P p a b n false = true)
   (hbp : b ≤ p) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 have hSC := SC_pos
 set e : ℕ → ℝ := fun k => ((zpe a b n k : ℕ) : ℝ) / SC with he
 have e0 : e 0 = (a : ℝ) / SC := by simp only [he, zpe_zero]
 have en : e n = (b : ℝ) / SC := by simp only [he, zpe_n a b n hn hab.le]
 obtain ⟨k, hk, hlt, hk1, hk2⟩ := pieces_cover e n s (e0 ▸ hs1) (en ▸ hs2)
   (by rw [e0, en]; exact div_lt_div_of_pos_right (by exact_mod_cast hab) hSC)
 have hpc := iall_true h k hk
 beta_reduce at hpc
 have hlt' : zpe a b n k < zpe a b n (Nat.add k 1) := by
   have : ((zpe a b n k : ℕ) : ℝ) < ((zpe a b n (k + 1) : ℕ) : ℝ) := (div_lt_div_iff_of_pos_right hSC).mp hlt
   exact_mod_cast this
 unfold zpc at hpc
 rw [show Nat.ble (zpe a b n (Nat.add k 1)) (zpe a b n k) = false from
   Bool.eq_false_iff.mpr fun e' => absurd (Nat.le_of_ble_eq_true e') (Nat.not_le.mpr hlt'), forceB_eq] at hpc
 simp only [Bool.and_eq_true] at hpc
 exact zpiece_left hlb hP hpc.1 hpc.2 ((zpe_le a b n (k + 1) hab.le (by omega)).trans hbp) hlt'.le hk1 hk2
theorem zsideF_right {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v M p a b n : ℕ} {w1p : ℝ}
   (hM : 1000000000 * w1p ≤ 2000000000 - (M : ℝ)) (h : zsideF top bk v M p a b n true = true)
   (hpa : p ≤ a) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 unfold zsideF at h
 simp only [Bool.or_eq_true] at h
 rcases h with (h | h) | h
 · exact zside_right hlb hM h hpa hab (by norm_num) hs1 hs2
 · exact zside_right hlb hM h hpa hab (by norm_num) hs1 hs2
 · exact zside_right hlb hM h hpa hab hn hs1 hs2
theorem zsideF_left {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk) {v P p a b n : ℕ} {w1p : ℝ}
   (hP : (P : ℝ) - 2000000000 ≤ 1000000000 * w1p) (h : zsideF top bk v P p a b n false = true)
   (hbp : b ≤ p) (hab : a < b) (hn : 0 < n) {s : ℝ} (hs1 : (a : ℝ) / SC ≤ s) (hs2 : s ≤ (b : ℝ) / SC) :
   (v : ℝ) / 10000000000 + w1p * (s - (p : ℝ) / SC) ≤ wfun s := by
 unfold zsideF at h
 simp only [Bool.or_eq_true] at h
 rcases h with (h | h) | h
 · exact zside_left hlb hP h hbp hab (by norm_num) hs1 hs2
 · exact zside_left hlb hP h hbp hab (by norm_num) hs1 hs2
 · exact zside_left hlb hP h hbp hab hn hs1 hs2
def TVal (f : ℕ → ℕ) (L U p : ℕ) : Prop :=
 L ≤ p ∧ p ≤ U ∧ (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) ∧
   1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) ∧
   ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
     (lo32 (f p) : ℝ) / 10000000000 + w1 ((p : ℝ) / SC) * (s - (p : ℝ) / SC) ≤ wfun s
theorem mterm_minV {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ} (hlb : LBSound top bk)
   (L0 L U Uc lc l1 l2 p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hsum : lc + l1 + l2 = 1024)
   (h1 : l1 = 0 ∨ TVal f L U p1) (h2 : l2 = 0 ∨ TVal f L U p2)
   (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
   ∃ D : ℝ, (l1 : ℝ) * ((lo32 (hi32 (f p1)) : ℝ) - 2000000000) + (l2 : ℝ) * ((lo32 (hi32 (f p2)) : ℝ) - 2000000000)
       ≤ 1000000000 * D ∧
     32768 * ((lc : ℝ) * (lb top bk L Uc : ℝ) + (l1 : ℝ) * (lo32 (f p1) : ℝ) + (l2 : ℝ) * (lo32 (f p2) : ℝ))
       + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
       + 10 * ((l1 : ℝ) * ((hi32 (hi32 (f p1)) : ℝ) - 2000000000) * ((p1 : ℝ) - L0)
         + (l2 : ℝ) * ((hi32 (hi32 (f p2)) : ℝ) - 2000000000) * ((p2 : ℝ) - L0))
       ≤ 327680000000000 * 1024 * wfun s := by
 have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
 have hlbs := hlb L Uc s hs1 (hs2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hUc) (by norm_num [SC])))
 have hlbs' : (lb top bk L Uc : ℝ) ≤ 10000000000 * wfun s := by
   rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000)] at hlbs; linarith
 have tang : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal f L U pk) →
     ∃ dk : ℝ, (lk : ℝ) * ((lo32 (hi32 (f pk)) : ℝ) - 2000000000) ≤ 1000000000 * ((lk : ℝ) * dk) ∧
       32768 * ((lk : ℝ) * (lo32 (f pk) : ℝ)) + 327680000000000 * (((lk : ℝ) * dk) * (s - (L0 : ℝ) / 32768))
         + 10 * ((lk : ℝ) * ((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
         ≤ 327680000000000 * ((lk : ℝ) * wfun s) := by
   intro lk pk hk
   rcases hk with hk | ⟨hLp, hpU, hP, hM, hval⟩
   · refine ⟨0, by rw [hk]; simp, by rw [hk]; simp⟩
   have htan := hval s hs1 hs2
   rw [hSC] at htan hM hP
   refine ⟨w1 ((pk : ℝ) / 32768), ?_, ?_⟩
   · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
     nlinarith
   · have hl0 : (0 : ℝ) ≤ lk := Nat.cast_nonneg _
     have hpL : (0 : ℝ) ≤ (pk : ℝ) - L0 := sub_nonneg.mpr (by exact_mod_cast hL0.trans hLp)
     have key : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
         + 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0)) ≤ 327680000000000 * wfun s := by
       have e1 : 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (L0 : ℝ) / 32768))
           = 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
             + 10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0)) := by ring
       rw [e1]
       have h3 : 10 * (((hi32 (hi32 (f pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0))
           ≤ -(10000000000 * (w1 ((pk : ℝ) / 32768) * ((pk : ℝ) - L0))) := by
         nlinarith [mul_le_mul_of_nonneg_right hM hpL]
       have h4 : 32768 * (lo32 (f pk) : ℝ) + 327680000000000 * (w1 ((pk : ℝ) / 32768) * (s - (pk : ℝ) / 32768))
           ≤ 327680000000000 * wfun s := by
         have := mul_le_mul_of_nonneg_left htan (by norm_num : (0 : ℝ) ≤ 327680000000000)
         nlinarith [this]
       linarith
     nlinarith [mul_le_mul_of_nonneg_left key hl0]
 obtain ⟨d1, hd1, hb1⟩ := tang l1 p1 h1
 obtain ⟨d2, hd2, hb2⟩ := tang l2 p2 h2
 refine ⟨(l1 : ℝ) * d1 + (l2 : ℝ) * d2, by linarith, ?_⟩
 have hsum' : (lc : ℝ) + l1 + l2 = 1024 := by exact_mod_cast hsum
 have hc0 : (0 : ℝ) ≤ lc := Nat.cast_nonneg _
 have hcl := mul_le_mul_of_nonneg_left hlbs' hc0
 have e2 : (327680000000000 : ℝ) * 1024 * wfun s
     = 327680000000000 * ((lc : ℝ) * wfun s) + 327680000000000 * ((l1 : ℝ) * wfun s)
       + 327680000000000 * ((l2 : ℝ) * wfun s) := by rw [← hsum']; ring
 rw [e2]
 nlinarith [hb1, hb2, hcl]
end AMW.Cert.PyrD
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def plenF (lb a : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 (Nat.add 16 lb) (Nat.beq a 3))
   (Nat.add 9 lb) (Nat.beq a 2)) 9 (Nat.beq a 1)
def dec4F (lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
 forceR (Nat.land (Nat.shiftRight w o) 3) fun a =>
 forceR (Bool.rec (motive := fun _ => ℕ)
     (Bool.rec (motive := fun _ => ℕ) 0 (Nat.land (Nat.shiftRight w (Nat.add o 16)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 3))
     (Nat.land (Nat.shiftRight w (Nat.add o 9)) (Nat.sub (Nat.shiftLeft 1 lb) 1)) (Nat.beq a 2)) fun lam =>
 forceR (Bool.rec (motive := fun _ => ℕ) (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 2)) 127)) 0 (Nat.beq a 0)) fun p =>
 forceR (Bool.rec (motive := fun _ => ℕ) 0 (gptF L U (Nat.land (Nat.shiftRight w (Nat.add o 9)) 127)) (Nat.beq a 3)) fun r =>
 forceR (Nat.add o (plenF lb a)) fun o' => k a (Nat.shiftLeft lam (Nat.sub 10 lb)) p r o'
theorem rootCl_congr {Q NC W : ℕ} {cov : List (List (ℕ × ℕ × Bool))} {idx idx' : ℕ → ℕ} (h : ∀ r < Q, idx r = idx' r) :
   rootCl Q NC W cov idx = rootCl Q NC W cov idx' := by
 unfold rootCl
 congr 1 <;> exact List.map_congr_left fun r hr => by rw [h r (List.mem_range.mp hr)]
theorem gsum_range (g : ℕ → ℝ) (i j : ℕ) : gsum g i j = ∑ r ∈ Finset.range (j - i), g (i + r) :=
 Finset.sum_Ico_eq_sum_range g i j
def PV (x v : ℕ) : Prop := (lo32 v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 v) ((x : ℝ) / SC)
theorem pv_zero (x : ℕ) : PV x 0 := by
 unfold PV; rw [lo32_zero, hi32_zero]
 exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def slT (Q : ℕ) (SL : List ℕ) (a b : ℕ) : ℕ := SL.getD (a * (Q + 1) + b) 0
def SLok (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Prop :=
 ∀ a < Q + 1, ∀ b < Q + 1, a < b →
   slT Q SL a b < Q + PR.length ∧ sI Q PR (slT Q SL a b) = a ∧ sJ Q PR (slT Q SL a b) = b
instance (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Decidable (SLok Q PR SL) := by unfold SLok; infer_instance
def ov : Option ℕ → ℕ
 | none => 0
 | some a => a
def legP (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
 Bool.rec (motive := fun _ => Option ℕ) none (some (sHi Q c (slT Q SL x y))) (Nat.blt x y)
def legN (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
 Bool.rec (motive := fun _ => Option ℕ) none (some (sLo Q c (slT Q SL y x))) (Nat.blt y x)
theorem gsum_sub (g : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) : gsum g a b = gsum g 0 b - gsum g 0 a := by
 have := gsum_add g (Nat.zero_le a) h; linarith
section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {c : Cl} {g : ℕ → ℝ}
theorem leg_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {x y : ℕ} (hx : x ≤ Q) (hy : y ≤ Q) :
   gsum g 0 y - gsum g 0 x ≤ ((ov (legP Q SL c x y) : ℕ) : ℝ) / SC - ((ov (legN Q SL c x y) : ℕ) : ℝ) / SC := by
 rcases lt_trichotomy x y with h | h | h
 · have hb : Nat.blt x y = true := Nat.blt_eq.mpr h
   have hb' : Nat.blt y x = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
   simp only [legP, legN, hb, hb', ov, Nat.cast_zero, zero_div, sub_zero]
   obtain ⟨h1, h2, h3⟩ := hSL x (by omega) y (by omega) h
   have := (slot_ok hg h1).2
   rw [h2, h3] at this
   rw [← gsum_sub g h.le]; exact this
 · subst h
   have hb : Nat.blt x x = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (lt_irrefl _)
   simp [legP, legN, hb, ov]
 · have hb : Nat.blt y x = true := Nat.blt_eq.mpr h
   have hb' : Nat.blt x y = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
   simp only [legP, legN, hb, hb', ov, Nat.cast_zero, zero_div, zero_sub]
   obtain ⟨h1, h2, h3⟩ := hSL y (by omega) x (by omega) h
   have := (slot_ok hg h1).1
   rw [h2, h3] at this
   rw [gsum_sub g h.le] at this; linarith
end
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def bdist (s z : ℕ) : ℕ := Nat.add (Nat.sub (Nat.add z z) s) (Nat.sub s (Nat.add z z))
def bcutL (BND : List ℕ) (bm lo hi : ℕ) : ℕ :=
 (List.rec (motive := fun _ => ℕ × Bool → ℕ × Bool) (fun acc => acc)
   (fun z _ ih acc => ih (Bool.rec (motive := fun _ => ℕ × Bool) acc (z, true)
     (Nat.ble (Nat.add lo bm) z && Nat.ble (Nat.add z bm) hi &&
       (!acc.2 || Nat.blt (bdist (Nat.add lo hi) z) (bdist (Nat.add lo hi) acc.1)))))
   BND (Nat.shiftRight (Nat.add lo hi) 1, false)).1
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell
def lbDrF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 6)) fun k =>
       forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov2 top bk k ib g)
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
theorem lbDrF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbDrF top bk lo hi = lbDr top bk lo hi := by
 simp only [lbDrF, lbDr, forceR_eq]
def treadUF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
def treadDF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)
theorem treadUF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) :
   treadUF R tD bD U p = treadU R tD bD U p := by
 simp only [treadUF, treadU, lbDrF_eq]
theorem treadDF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) :
   treadDF R tD bD L p = treadD R tD bD L p := by
 simp only [treadDF, treadD, lbDrF_eq]
def lbF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 5)) fun k =>
       forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov top bk k ib g)
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
theorem lbF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbF top bk lo hi = lb top bk lo hi := by
 simp only [lbF, lb, forceR_eq]
def zpcF (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (forceB (lbF top bk x0 x1) fun lbv =>
     Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
       (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
   true (Nat.ble x1 x0)
def zsideG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 iall (fun k => zpcF top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n
def zsideFG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 zsideG top bk v c p a b 1 right || zsideG top bk v c p a b 2 right || zsideG top bk v c p a b n right
theorem zpcF_eq (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) :
   zpcF top bk v c p x0 x1 right = zpc top bk v c p x0 x1 right := by
 simp only [zpcF, zpc, lbF_eq]
end AMW.Cert.PyrD
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def mvKF (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.mul 1024 (lbF top bk L U))
     (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (f p))) (Nat.mul m (lo32 (f r)))) (Nat.beq k 3))
   (Nat.add (Nat.mul (Nat.sub 1024 m) (lbF top bk L U)) (Nat.mul m (lo32 (f p)))) (Nat.beq k 2))
   (Nat.mul 1024 (lo32 (f p))) (Nat.beq k 1)
theorem mvKF_eq (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : mvKF top bk f L U k m p r = mvK top bk f L U k m p r := by
 simp only [mvKF, mvK, lbF_eq]
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell
def rup (U j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight (Nat.add U (Nat.sub (Nat.shiftLeft 1 j) 1)) j) j
def rdn (L j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight L j) j
theorem le_rup (U j : ℕ) : U ≤ rup U j := by
 unfold rup
 simp only [Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_eq, Nat.sub_eq,
   Nat.one_mul]
 have hp : 0 < 2 ^ j := by positivity
 have := Nat.lt_div_mul_add (a := U + (2 ^ j - 1)) hp
 omega
theorem rdn_le (L j : ℕ) : rdn L j ≤ L := by
 unfold rdn
 simp only [Nat.shiftLeft_eq', Nat.shiftRight_eq', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
 exact Nat.div_mul_le_self L _
theorem zsideFG_eq (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) :
   zsideFG top bk v c p a b n right = zsideF top bk v c p a b n right := by
 simp only [zsideFG, zsideF, zsideG, zside, zpcF_eq]
def tcheckZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
   Bool :=
 forceB (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Nat.blt k 16 && Nat.ble (rgA R k) p && Nat.ble p (rgB R k) && Nat.ble L p && Nat.ble p U
     && Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))
     && (Nat.ble U (rgB R k)
       || (forceB (blen (Nat.shiftRight (Nat.sub U (rgB R k)) csh)) fun jj => forceB (rup U jj) fun uc =>
            (Nat.ble 1 (lo32 (treadUF R tD bD uc p))
              && Nat.ble 4000000000 (Nat.add (lo32 (treadUF R tD bD uc p)) (hi32 (hi32 X))))
            || zsideFG top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) uc n true)
       || (Nat.ble 1 (lo32 EU) && Nat.ble 4000000000 (Nat.add (lo32 EU) (hi32 (hi32 X))))
       || zsideFG top bk (lo32 X) (hi32 (hi32 X)) p (rgB R k) U n true)
     && (Nat.ble (rgA R k) L
       || (forceB (blen (Nat.shiftRight (Nat.sub (rgA R k) L) csh)) fun jj => forceB (rdn L jj) fun lc =>
            (Nat.ble 1 (hi32 (treadDF R tD bD lc p))
              && Nat.ble 4000000000 (Nat.add (hi32 (treadDF R tD bD lc p)) (lo32 (hi32 X))))
            || zsideFG top bk (lo32 X) (lo32 (hi32 X)) p lc (rgA R k) n false)
       || (Nat.ble 1 (hi32 ED) && Nat.ble 4000000000 (Nat.add (hi32 ED) (lo32 (hi32 X))))
       || zsideFG top bk (lo32 X) (lo32 (hi32 X)) p L (rgA R k) n false)
def tcheckPZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
   Bool :=
 Bool.rec (motive := fun _ => Bool) (tcheckZC R top bk tD bD n csh L U p X EU ED)
   (Nat.ble 1 (lo32 (hi32 X)) && Nat.ble 1 (hi32 (hi32 X))) (Nat.beq L U && Nat.beq L p)
theorem tangent_valZC {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
   (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : PTF f) (hR : rgOk R = true) {n csh L U p : ℕ} (hn : 0 < n)
   (h : tcheckPZC R top bk tD bD n csh L U p (f p) (treadUF R tD bD U p) (treadDF R tD bD L p) = true) :
   TVal f L U p := by
 have hSC := SC_pos
 have hU1 := U1_posR
 have eU : (U1 : ℝ) = 1000000000 := by norm_num [U1]
 have cast_le : ∀ {m n : ℕ}, m ≤ n → (m : ℝ) / SC ≤ (n : ℝ) / SC := fun hmn =>
   div_le_div_of_nonneg_right (by exact_mod_cast hmn) hSC.le
 unfold tcheckPZC at h
 cases hc : (Nat.beq L U && Nat.beq L p)
 case true =>
   rw [hc] at h
   simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hc h
   obtain ⟨hLU, hLp⟩ := hc
   subst hLU; subst hLp
   have hp := hpt L
   obtain ⟨-, hPq⟩ := hp.2.1 (by omega)
   obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
   simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
   rw [div_le_iff₀ hU1, eU] at hPq hMq
   refine ⟨le_rfl, le_rfl, by linarith, by linarith, fun s hs1 hs2 => ?_⟩
   rw [le_antisymm hs2 hs1, sub_self, mul_zero, add_zero]; exact hp.1
 rw [hc] at h
 unfold tcheckZC at h
 simp only [forceB_eq, treadUF_eq, treadDF_eq, zsideFG_eq] at h
 unfold treadU treadD at h
 simp only [forceR_eq] at h
 set k := Nat.shiftRight (Nat.add p 16384) 15 with hkdef
 set uc := rup U (blen (Nat.shiftRight (Nat.sub U (rgB R k)) csh)) with huc
 set lc := rdn L (blen (Nat.shiftRight (Nat.sub (rgA R k) L) csh)) with hlc
 have hUuc : U ≤ uc := le_rup _ _
 have hlcL : lc ≤ L := rdn_le _ _
 simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
 obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, hap⟩, hpb⟩, hLp⟩, hpU⟩, hP1⟩, hM1⟩, hup⟩, hdn⟩ := h
 have hp := hpt p
 obtain ⟨hkp, hPq⟩ := hp.2.1 (by omega)
 obtain ⟨-, hMq⟩ := hp.2.2 (by omega)
 simp only [fD, ↓reduceIte, Bool.false_eq_true] at hPq hMq
 rw [div_le_iff₀ hU1, eU] at hPq hMq
 have hP : (lo32 (hi32 (f p)) : ℝ) - 2000000000 ≤ 1000000000 * w1 ((p : ℝ) / SC) := by linarith
 have hM : 1000000000 * w1 ((p : ℝ) / SC) ≤ 2000000000 - (hi32 (hi32 (f p)) : ℝ) := by linarith
 have hc := rg_conv hR hk (by omega)
 have hap' := cast_le hap
 have hpb' := cast_le hpb
 set za : ℝ := ((rgA R k : ℕ) : ℝ) / SC
 set zb : ℝ := ((rgB R k : ℕ) : ℝ) / SC
 set q : ℝ := (p : ℝ) / SC
 set v : ℝ := (lo32 (f p) : ℝ) / 10000000000
 have hv : v ≤ wfun q := hp.1
 have hmid : ∀ s, za ≤ s → s ≤ zb → v + w1 q * (s - q) ≤ wfun s := by
   intro s h1 h2
   have := ext_tangent (za := za) (zb := zb) (L := za) (U := zb) hc hap' hpb'
     (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
       by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
     (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
       by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
     hap' hpb' h1 h2
   linarith
 have hderR : ∀ E : ℕ, U ≤ E → rgB R k < U →
     1 ≤ lo32 (lbDr tD bD (rgB R k) E) →
     4000000000 ≤ Nat.add (lo32 (lbDr tD bD (rgB R k) E)) (hi32 (hi32 (f p))) →
     ∀ s, zb ≤ s → s ≤ (U : ℝ) / SC → v + w1 q * (s - q) ≤ wfun s := by
   intro E hUE hbU he1 he2 s h1 h2
   have hR' : ∀ x : ℝ, zb ≤ x → x ≤ (U : ℝ) / SC → kD x < 0 ∧ w1 q ≤ w1 x := by
     intro x hx1 hx2
     have hb := (hD _ E x hx1 (hx2.trans (cast_le hUE))).1 (by omega)
     obtain ⟨hkx, hbx⟩ := hb
     simp only [fD, ↓reduceIte] at hbx
     rw [div_le_iff₀ hU1, eU] at hbx
     refine ⟨hkx, ?_⟩
     have : (4000000000 : ℝ) ≤ (lo32 (lbDr tD bD (rgB R k) E) : ℝ) + (hi32 (hi32 (f p)) : ℝ) := by
       simp only [Nat.add_eq] at he2; exact_mod_cast he2
     linarith
   have := ext_tangent (za := za) (zb := zb) (L := za) (U := (U : ℝ) / SC) hc hap' hpb' hR'
     (fun x hx1 hx2 => ⟨(hc x hx1 (le_trans hx2 (le_trans hap' hpb'))).1,
       by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc le_rfl hap' hpb'⟩)
     hap' (cast_le hpU) (le_trans hap' (le_trans hpb' h1)) h2
   linarith
 have hderL : ∀ E : ℕ, E ≤ L → L < rgA R k →
     1 ≤ hi32 (lbDr tD bD E (rgA R k)) →
     4000000000 ≤ Nat.add (hi32 (lbDr tD bD E (rgA R k))) (lo32 (hi32 (f p))) →
     ∀ s, (L : ℝ) / SC ≤ s → s ≤ za → v + w1 q * (s - q) ≤ wfun s := by
   intro E hEL hLa he1 he2 s h1 h2
   have hL' : ∀ x : ℝ, (L : ℝ) / SC ≤ x → x ≤ za → kD x < 0 ∧ w1 x ≤ w1 q := by
     intro x hx1 hx2
     have hb := (hD E _ x ((cast_le hEL).trans hx1) hx2).2 (by omega)
     obtain ⟨hkx, hbx⟩ := hb
     simp only [fD, ↓reduceIte, Bool.false_eq_true] at hbx
     rw [div_le_iff₀ hU1, eU] at hbx
     refine ⟨hkx, ?_⟩
     have : (4000000000 : ℝ) ≤ (hi32 (lbDr tD bD E (rgA R k)) : ℝ) + (lo32 (hi32 (f p)) : ℝ) := by
       simp only [Nat.add_eq] at he2; exact_mod_cast he2
     linarith
   have := ext_tangent (za := za) (zb := zb) (L := (L : ℝ) / SC) (U := zb) hc hap' hpb'
     (fun x hx1 hx2 => ⟨(hc x (le_trans hap' (le_trans hpb' hx1)) hx2).1,
       by rw [le_antisymm hx2 hx1]; exact w1_mono_of_conv hc hap' hpb' le_rfl⟩)
     hL' (cast_le hLp) hpb' h1 (le_trans h2 (le_trans hap' hpb'))
   linarith
 have hright : ∀ s, zb ≤ s → s ≤ (U : ℝ) / SC → v + w1 q * (s - q) ≤ wfun s := by
   intro s h1 h2
   rcases le_or_gt U (rgB R k) with hUb | hbU
   · exact hmid s (le_trans hap' (le_trans hpb' h1)) (le_trans h2 (cast_le hUb))
   have hbuc : rgB R k < uc := lt_of_lt_of_le hbU hUuc
   have nb1 : Nat.ble U (rgB R k) = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
   have nb2 : Nat.ble uc (rgB R k) = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
   rw [nb2] at hup
   rw [nb1] at hup
   rcases hup with (((hub | ⟨he1, he2⟩ | hz) | ⟨he1, he2⟩) | hz)
   · exact absurd hub (by omega)
   · exact hderR uc hUuc hbU he1 he2 s h1 h2
   · exact zsideF_right hlb hM hz hpb hbuc hn h1 (h2.trans (cast_le hUuc))
   · exact hderR U le_rfl hbU he1 he2 s h1 h2
   · exact zsideF_right hlb hM hz hpb hbU hn h1 h2
 have hleft : ∀ s, (L : ℝ) / SC ≤ s → s ≤ za → v + w1 q * (s - q) ≤ wfun s := by
   intro s h1 h2
   rcases le_or_gt (rgA R k) L with haL | hLa
   · exact hmid s (le_trans (cast_le haL) h1) (le_trans h2 (le_trans hap' hpb'))
   have hlca : lc < rgA R k := lt_of_le_of_lt hlcL hLa
   have nb1 : Nat.ble (rgA R k) L = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
   have nb2 : Nat.ble (rgA R k) lc = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.le_of_ble_eq_true e) (by omega)
   rw [nb2] at hdn
   rw [nb1] at hdn
   rcases hdn with (((haL | ⟨he1, he2⟩ | hz) | ⟨he1, he2⟩) | hz)
   · exact absurd haL (by omega)
   · exact hderL lc hlcL hLa he1 he2 s h1 h2
   · exact zsideF_left hlb hP hz hap hlca hn ((cast_le hlcL).trans h1) h2
   · exact hderL L le_rfl hLa he1 he2 s h1 h2
   · exact zsideF_left hlb hP hz hap hLa hn h1 h2
 refine ⟨hLp, hpU, hP, hM, fun s hs1 hs2 => ?_⟩
 rcases le_total s za with h1 | h1
 · exact hleft s hs1 h1
 rcases le_total s zb with h2 | h2
 · exact hmid s h1 h2
 · exact hright s h2 hs2
end AMW.Cert.PyrD
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
def mcheckGX (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (Q : ℕ) (bs : List ℕ)
   (TS : List Term) (cN : ℕ) (c : Cl) (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool) false
   (Nat.ble
     (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (isum (fun n => Nat.mul (tA TS n)
       (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) TS.length) Cp)
       (isum (fun r => Nat.mul (Nat.sub (c.U.getD r 0) (c.L.getD r 0)) (Ng f bs TS FS P S r)) Q))))
     (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (bs.getD r 0) (c.L.getD r 0)) Q))
       (Nat.mul 32768 (isum (fun n => Nat.mul (tA TS n) (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n))
         (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) TS.length)))
       (Nat.mul 10 (Nat.add (isum (fun n => Nat.mul (tA TS n) (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)))
         TS.length) Cm))))
   (Bool.rec (motive := fun _ => Bool) false
     (iall (fun n => ok (eL TS c n) (eU TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n)) TS.length)
     (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) Q))
theorem mcheckGX_sound {ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {top : ℕ} {bk : ℕ → ℕ} {f : ℕ → ℕ}
   (hok : ∀ (L0 L U k m p r : ℕ), L0 ≤ L → ok L U k m p r = true → ∀ s : ℝ, (L : ℝ) / SC ≤ s → s ≤ (U : ℝ) / SC →
     ∃ D : ℝ, (mslT f k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
       32768 * (mvT top bk f L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
         + 10 * (mcpT f L0 k m p r : ℝ) - 10 * (mcnT f L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s)
   {Q : ℕ} {PR : List (ℕ × ℕ)} {bs : List ℕ} {TS : List Term} {cN : ℕ} (hPR : PRok Q PR) (hTS : TSok Q PR TS)
   {c : Cl} {FS : List Term} {P S : List ℕ} {Cp Cm : ℕ} (hY : MulOKg Q PR c P S Cp Cm)
   (h : mcheckGX ok top bk f Q bs TS cN c FS P S Cp Cm = true) : CovBy Q PR (Pg cN Q bs TS) c := by
 intro g hg
 left
 unfold mcheckGX at h
 obtain ⟨hpre, hmain⟩ := brec_and h
 obtain ⟨hbox, hterm⟩ := brec_and hpre
 have hbox' := iall_true hbox
 have hterm' := iall_true hterm
 rw [Nat.ble_eq] at hmain
 set NT := TS.length with hNT
 have hT : ∀ n, n < NT → ∃ D : ℝ,
     (mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ) - 2000000000 * (mwT (tI FS n) (tJ FS n) : ℝ) ≤ 1000000000 * D ∧
     32768 * (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n)) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
       + 327680000000000 * (D * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
       + 10 * (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
       - 10 * (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
       ≤ 327680000000000 * 1024 * wfun (gsum g (tI TS n) (tJ TS n)) := by
   intro n hn
   obtain ⟨h0, h1, h2⟩ := term_range hPR hTS hg hn
   exact hok _ _ _ _ _ _ _ h0 (hterm' n hn) _ h1 h2
 choose! D hD1 hD2 using hT
 set a : ℕ → ℝ := fun n => ((tA TS n : ℕ) : ℝ) with ha
 set e : ℕ → ℝ := fun r => g r - ((c.L.getD r 0 : ℕ) : ℝ) / 32768 with he
 set ind : ℕ → ℕ → Prop := fun n r => tI TS n ≤ r ∧ r < tJ TS n with hind
 set DD : ℕ → ℝ := fun r => ∑ n ∈ Finset.range NT, if tI TS n ≤ r ∧ r < tJ TS n then a n * D n else 0 with hDD
 have ha0 : ∀ n, 0 ≤ a n := fun n => Nat.cast_nonneg _
 have S1 : 32768 * ∑ n ∈ Finset.range NT, a n * (mvT top bk f (eL TS c n) (uc (eL TS c n) (eU TS c n)) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
     + 327680000000000 * ∑ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
     + 10 * ∑ n ∈ Finset.range NT, a n * (mcpT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
     - 10 * ∑ n ∈ Finset.range NT, a n * (mcnT f (eL0 TS c n) (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℝ)
     ≤ 327680000000000 * 1024 * ∑ n ∈ Finset.range NT, a n * wfun (gsum g (tI TS n) (tJ TS n)) := by
   have := Finset.sum_le_sum fun n (hn : n ∈ Finset.range NT) =>
     mul_le_mul_of_nonneg_left (hD2 n (Finset.mem_range.mp hn)) (ha0 n)
   simp only [Finset.mul_sum]
   rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
   refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
   · apply Finset.sum_congr rfl; intro n _; ring
   · apply Finset.sum_congr rfl; intro n _; ring
 have S2 : ∑ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
     = ∑ r ∈ Finset.range Q, e r * DD r := by
   have hx : ∀ n ∈ Finset.range NT, a n * (D n * (gsum g (tI TS n) (tJ TS n) - (eL0 TS c n : ℝ) / 32768))
       = ∑ r ∈ Finset.range Q, if tI TS n ≤ r ∧ r < tJ TS n then e r * (a n * D n) else 0 := by
     intro n hn
     obtain ⟨hij, hjQ, -⟩ := hTS n (Finset.mem_range.mp hn)
     rw [span_eq (Q := Q) g hij.le hjQ, Finset.mul_sum, Finset.mul_sum]
     apply Finset.sum_congr rfl; intro r _
     split_ifs <;> ring
   rw [Finset.sum_congr rfl hx, Finset.sum_comm]
   apply Finset.sum_congr rfl; intro r _
   rw [hDD, Finset.mul_sum]
   apply Finset.sum_congr rfl; intro n _
   split_ifs <;> ring
 have S3 : ∀ r ∈ Finset.range Q, -(10 * (((Ng f bs TS FS P S r : ℕ) : ℝ) * ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ)))
     ≤ 327680000000000 * ((1024 * ((bs.getD r 0 : ℕ) : ℝ) + DD r - (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) / 1000000000) * e r) := by
   intro r hr
   have hr' := Finset.mem_range.mp hr
   have hlu : c.L.getD r 0 ≤ c.U.getD r 0 := Nat.le_of_ble_eq_true (hbox' r hr')
   have hgr := hg.1 r hr'
   have hSCe : (SC : ℝ) = 32768 := by norm_num [SC]
   rw [hSCe] at hgr
   refine gap_lo (natsub_nonneg _ _) ?_ (by simp only [he]; linarith [hgr.1]) ?_
   · -- `−N_r ≤ 10⁹ E_r`
     refine neg_natsub_le ?_
     simp only [Nat.add_eq, Nat.mul_eq]
     push_cast
     rw [isum_cast, isum_cast]
     simp only [brec0_cast, inr_true]
     have hsum : ∑ n ∈ Finset.range NT, (if tI TS n ≤ r ∧ r < tJ TS n then ((tA TS n * mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n) : ℕ) : ℝ) else 0)
         - 2000000000 * ∑ n ∈ Finset.range NT, (if tI TS n ≤ r ∧ r < tJ TS n then ((tA TS n * mwT (tI FS n) (tJ FS n) : ℕ) : ℝ) else 0)
         ≤ 1000000000 * DD r := by
       rw [hDD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
       apply Finset.sum_le_sum; intro n hn
       split_ifs
       · push_cast
         have := mul_le_mul_of_nonneg_left (hD1 n (Finset.mem_range.mp hn)) (ha0 n)
         simp only [ha] at this; nlinarith [this]
       · simp
     linarith
   · rw [Nat.cast_sub hlu, sub_div]; simp only [he]; linarith [hgr.2]
 have S4 := hY g hg
 have S4' : ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * (32768 * g r - (c.L.getD r 0 : ℕ))
     = 32768 * ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * e r := by
   rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
 have S5 := (Nat.cast_le (α := ℝ)).mpr hmain
 simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at S5
 push_cast at S5
 rw [isum_cast, isum_cast, isum_cast, isum_cast, isum_cast] at S5
 push_cast at S5
 have S3s := Finset.sum_le_sum S3
 have e1 : ∑ r ∈ Finset.range Q, 327680000000000 * ((1024 * ((bs.getD r 0 : ℕ) : ℝ) + DD r
       - (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) / 1000000000) * e r)
     = 327680000000000 * 1024 * ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * e r
       + 327680000000000 * ∑ r ∈ Finset.range Q, e r * DD r
       - 327680 * ∑ r ∈ Finset.range Q, (((P.getD r 0 : ℕ) : ℝ) - (S.getD r 0 : ℕ)) * e r := by
   rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
   apply Finset.sum_congr rfl; intro r _; ring
 have e2 : ∑ r ∈ Finset.range Q, -(10 * (((Ng f bs TS FS P S r : ℕ) : ℝ) * ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ)))
     = -(10 * ∑ r ∈ Finset.range Q, ((c.U.getD r 0 - c.L.getD r 0 : ℕ) : ℝ) * ((Ng f bs TS FS P S r : ℕ) : ℝ)) := by
   rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro r _; ring
 have e3 : ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * g r
     = (∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * ((c.L.getD r 0 : ℕ) : ℝ)) / 32768
       + ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * e r := by
   rw [Finset.sum_div, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro r _; simp only [he]; ring
 rw [e1, e2] at S3s
 rw [S2] at S1
 rw [S4'] at S4
 unfold Fg
 rw [e3, ← hNT]
 simp only [ha] at S1
 linarith [S1, S3s, S4, S5]
end AMW.Cert.PCell
end

section

/-! ###### polytope cells: the closure through one point, biased (bridge-port, 2026-10-07; one helper for every split)

A split at `q` on the pair `(i, j)`, `i < j`, has two children: `x_j − x_i ≤ q` (the edge `i → j`, weight `q`) and
`x_j − x_i ≥ q` (the edge `j → i`, weight `−q`). Through an edge `s → t` of weight `w`, every slot `(a, b)` is bounded
by the path through it: `x_b − x_a ≤ D(a, s) + w + D(t, b)` and `x_b − x_a ≥ −(D(b, s) + w + D(t, a))`, where
`D(x, y)` is the cell's bound of `x_y − x_x` (`hi`, `0` or `−lo`, as in `PCellClose`).

With the column `X_x = BB + D(x, s)` and the row `Y_x = BB + w + D(t, x)`, both in ℕ (`BB = 2^42`), the update is the
same expression for every slot (`cuB`): `hi(a, b) := min(hi(a, b), X_a + Y_b − 2BB)` and
`lo(a, b) := max(lo(a, b), 2BB − X_b − Y_a)`. Soundness needs only that `X` and `Y` are upper bounds (`ColOK`); Nat
truncation in them only loosens, and a truncated candidate still bounds a nonnegative pair sum (`natsub_hi`,
`natsub_lo`). The split's own slot gets the candidate `q`, so a child is the closure of the parent's fields plus the
edge (`cov_splitB`). On a closed parent the candidates that `cupd` skips never bind, so the states are `cupd`'s.
###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the bias `2^42` -/
def BB : ℕ := 4398046511104
/-- twice the bias -/
def TB : ℕ := 8796093022208

theorem TB_eq : (TB : ℝ) / SC = (BB : ℝ) / SC + (BB : ℝ) / SC := by
  rw [← add_div]; norm_num [TB, BB]

/-- `X` bounds the column through `s` and `Y` the row: `x_s − x_x ≤ X_x − BB` and `x_x − x_s ≤ Y_x − BB` -/
def ColOK (Q : ℕ) (g : ℕ → ℝ) (s : ℕ) (X Y : List ℕ) : Prop :=
  ∀ x ≤ Q, gsum g 0 s - gsum g 0 x ≤ ((X.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC ∧
    gsum g 0 x - gsum g 0 s ≤ ((Y.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC

/-- the closure update through the column `X` and the row `Y` -/
def cuB (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (X Y : List ℕ) : Cl :=
  ⟨(List.range Q).map (fun r => nmax (c.L.getD r 0) (Nat.sub TB (Nat.add (X.getD (r + 1) 0) (Y.getD r 0)))),
   (List.range Q).map (fun r => nmin (c.U.getD r 0) (Nat.sub (Nat.add (X.getD r 0) (Y.getD (r + 1) 0)) TB)),
   (List.range PR.length).map (fun k =>
     nmax (c.A.getD k 0) (Nat.sub TB (Nat.add (X.getD (pJ PR k) 0) (Y.getD (pI PR k) 0)))),
   (List.range PR.length).map (fun k =>
     nmin (c.B.getD k 0) (Nat.sub (Nat.add (X.getD (pI PR k) 0) (Y.getD (pJ PR k) 0)) TB))⟩

section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {g : ℕ → ℝ} {s : ℕ} {X Y : List ℕ}

/-- the upper candidate of `x_b − x_a` -/
theorem candB_hi (hX : ColOK Q g s X Y) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (h0 : 0 ≤ gsum g a b) :
    gsum g a b ≤ ((Nat.sub (Nat.add (X.getD a 0) (Y.getD b 0)) TB : ℕ) : ℝ) / SC := by
  have h1 := (hX a (hab.trans hb)).1
  have h2 := (hX b hb).2
  refine natsub_hi ?_ h0
  rw [cast_add_div, TB_eq, gsum_sub g hab]
  linarith

/-- the lower candidate of `x_b − x_a` -/
theorem candB_lo (hX : ColOK Q g s X Y) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ Q) (h0 : 0 ≤ gsum g a b) :
    ((Nat.sub TB (Nat.add (X.getD b 0) (Y.getD a 0)) : ℕ) : ℝ) / SC ≤ gsum g a b := by
  have h1 := (hX b hb).1
  have h2 := (hX a (hab.trans hb)).2
  refine natsub_lo ?_ h0
  rw [cast_add_div, TB_eq, gsum_sub g hab]
  linarith

/-- the update keeps every point of the cell whose column and row bounds hold -/
theorem cuB_ok {c : Cl} (hPR : PRok Q PR) (hg : InCell Q PR c g) (hX : ColOK Q g s X Y) :
    InCell Q PR (cuB Q PR c X Y) g := by
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · have h0 : 0 ≤ gsum g r (r + 1) := gsum_nonneg hg (by omega)
    have hlo := candB_lo hX (Nat.le_succ r) (by omega) h0
    have hhi := candB_hi hX (Nat.le_succ r) (by omega) h0
    rw [gsum_single] at hlo hhi
    show (((List.range Q).map (fun r => nmax (c.L.getD r 0) (Nat.sub TB (Nat.add (X.getD (r + 1) 0) (Y.getD r 0))))).getD
        r 0 : ℝ) / SC ≤ g r ∧
      g r ≤ (((List.range Q).map (fun r => nmin (c.U.getD r 0)
        (Nat.sub (Nat.add (X.getD r 0) (Y.getD (r + 1) 0)) TB))).getD r 0 : ℝ) / SC
    rw [getD_map_range _ hr, getD_map_range _ hr]
    exact ⟨lo_nmax (hg.1 r hr).1 hlo, hi_nmin (hg.1 r hr).2 hhi⟩
  · obtain ⟨h1, h2⟩ := hPR k hk
    have h0 : 0 ≤ gsum g (pI PR k) (pJ PR k) := gsum_nonneg hg h2
    have hlo := candB_lo hX (a := pI PR k) (b := pJ PR k) (by omega) h2 h0
    have hhi := candB_hi hX (a := pI PR k) (b := pJ PR k) (by omega) h2 h0
    show (((List.range PR.length).map (fun k => nmax (c.A.getD k 0)
        (Nat.sub TB (Nat.add (X.getD (pJ PR k) 0) (Y.getD (pI PR k) 0))))).getD k 0 : ℝ) / SC ≤
        gsum g (pI PR k) (pJ PR k) ∧
      gsum g (pI PR k) (pJ PR k) ≤ (((List.range PR.length).map (fun k => nmin (c.B.getD k 0)
        (Nat.sub (Nat.add (X.getD (pI PR k) 0) (Y.getD (pJ PR k) 0)) TB))).getD k 0 : ℝ) / SC
    rw [getD_map_range _ hk, getD_map_range _ hk]
    exact ⟨lo_nmax (hg.2 k hk).1 hlo, hi_nmin (hg.2 k hk).2 hhi⟩

end

/-! ### the column and the row read from the cell -/

/-- `E + D(a, b)` in ℕ: `D(a, b)` is `hi(a, b)` if `a < b`, `0` if `a = b`, `−lo(b, a)` if `b < a` (truncated) -/
def dE (Q : ℕ) (SL : List ℕ) (c : Cl) (E a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Nat.sub E (sLo Q c (slT Q SL b a))) E (Nat.beq a b))
    (Nat.add E (sHi Q c (slT Q SL a b))) (Nat.blt a b)

/-- the column through `s` -/
def colB (Q : ℕ) (SL : List ℕ) (c : Cl) (s : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c BB x s)

/-- the row from `t`, with the base `E` (`BB` plus the edge's weight) -/
def rowB (Q : ℕ) (SL : List ℕ) (c : Cl) (E t : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c E t x)

section
variable {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ} {c : Cl} {g : ℕ → ℝ}

theorem dE_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) (E : ℕ) {a b : ℕ} (ha : a ≤ Q) (hb : b ≤ Q) :
    gsum g 0 b - gsum g 0 a ≤ ((dE Q SL c E a b : ℕ) : ℝ) / SC - (E : ℝ) / SC := by
  have l := leg_ok hSL hg ha hb
  rcases lt_trichotomy a b with h | h | h
  · have e1 : Nat.blt a b = true := Nat.blt_eq.mpr h
    have e2 : Nat.blt b a = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    simp only [legP, legN, e1, e2, ov, Nat.cast_zero, zero_div, sub_zero] at l
    simp only [dE, e1]
    rw [cast_add_div]; linarith
  · rw [h]
    have e1 : Nat.blt b b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (lt_irrefl _)
    simp only [dE, e1, Nat.beq_refl, sub_self, le_refl]
  · have e1 : Nat.blt a b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
    have e2 : Nat.blt b a = true := Nat.blt_eq.mpr h
    have e3 : Nat.beq a b = false := Bool.eq_false_iff.mpr fun e => absurd (Nat.eq_of_beq_eq_true e) (by omega)
    simp only [legP, legN, e1, e2, ov, Nat.cast_zero, zero_div, zero_sub] at l
    simp only [dE, e1, e3]
    have := natsub_ge E (sLo Q c (slT Q SL b a))
    have hSC := SC_pos
    have : ((E : ℝ) - (sLo Q c (slT Q SL b a) : ℕ)) / SC ≤ ((Nat.sub E (sLo Q c (slT Q SL b a)) : ℕ) : ℝ) / SC :=
      (div_le_div_iff_of_pos_right hSC).mpr (by simpa [Nat.sub_eq] using this)
    rw [sub_div] at this; linarith

/-- the column through `s` and the row from `t` (base `E`) bound the cell, given the edge `x_t − x_s ≤ E − BB` -/
theorem colB_ok (hSL : SLok Q PR SL) (hg : InCell Q PR c g) {s t E : ℕ} (hs : s ≤ Q) (ht : t ≤ Q)
    (hE : gsum g 0 t - gsum g 0 s ≤ (E : ℝ) / SC - (BB : ℝ) / SC) :
    ColOK Q g s (colB Q SL c s) (rowB Q SL c E t) := by
  intro x hx
  have hx' : x < Q + 1 := by omega
  rw [colB, rowB, getD_map_range _ hx', getD_map_range _ hx']
  have h1 := dE_ok hSL hg BB hx hs
  have h2 := dE_ok hSL hg E ht hx
  exact ⟨h1, by linarith⟩

/-- a split at any `q` on `(i, j)`, `i < j ≤ Q`: the children are the closures through `i → j` (weight `q`) and
`j → i` (weight `−q`) -/
theorem cov_splitB {P : (ℕ → ℝ) → Prop} (hSL : SLok Q PR SL) (hPR : PRok Q PR) {i j : ℕ} (hij : i < j) (hj : j ≤ Q)
    (q : ℕ) (hA : CovBy Q PR P (cuB Q PR c (colB Q SL c i) (rowB Q SL c (Nat.add BB q) j)))
    (hB : CovBy Q PR P (cuB Q PR c (colB Q SL c j) (rowB Q SL c (Nat.sub BB q) i))) : CovBy Q PR P c := by
  intro g hg
  have hSC := SC_pos
  rcases le_total (gsum g 0 j - gsum g 0 i) ((q : ℝ) / SC) with h | h
  · refine hA g (cuB_ok hPR hg (colB_ok hSL hg (by omega) hj ?_))
    rw [cast_add_div]; linarith
  · refine hB g (cuB_ok hPR hg (colB_ok hSL hg hj (by omega) ?_))
    have := natsub_ge BB q
    have : ((BB : ℝ) - q) / SC ≤ ((Nat.sub BB q : ℕ) : ℝ) / SC :=
      (div_le_div_iff_of_pos_right hSC).mpr (by simpa [Nat.sub_eq] using this)
    rw [sub_div] at this; linarith

end

end AMW.Cert.PCell

end
end

section

/-! ###### precertified tangent intervals (am-cert, lever 1)

A tangent's value-form claim `TVal f L U p` depends on the range `[L, U]` only through `L ≤ p ≤ U` and the
inequality on `[L/SC, U/SC]`, so it passes to every subrange that still contains `p` (`TVal_mono`).  Each point word of
the table carries, above its 96 triple bits, one interval `[a, b]` (`a + 2^24·b`, `b = 0`: none) on which the tangent
claim is checked ONCE, with the same coarse-first check as before (`ivOk`, `ptlI_sound`).  A minorant leaf then needs,
per tangent point, only `a ≤ L ≤ p ≤ U ≤ b` (`ivIn`, `mokI`, `mtermTI`) in place of `mokTZC`'s per-leaf derivative
reads and Z extension.  Every triple decoder reads the word through `trip` (the low 96 bits). ###### -/

noncomputable section

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- the triple (low 96 bits) of a point word -/
def trip (v : ℕ) : ℕ := Nat.land v 79228162514264337593543950335
/-- the interval's lower end (bits 96–119) -/
def ivA (v : ℕ) : ℕ := Nat.land (Nat.shiftRight v 96) 16777215
/-- the interval's upper end (bits 120–); `0` means no interval -/
def ivB (v : ℕ) : ℕ := Nat.shiftRight v 120
/-- the point function the decoders see -/
def tf (g : ℕ → ℕ) (x : ℕ) : ℕ := trip (g x)

theorem trip_zero : trip 0 = 0 := rfl
theorem ivB_zero : ivB 0 = 0 := rfl

/-- `TVal` reads `f` only at `p` -/
theorem TVal_congr {f f' : ℕ → ℕ} {L U p : ℕ} (h : f p = f' p) : TVal f L U p ↔ TVal f' L U p := by
  unfold TVal; rw [h]

/-- **monotonicity**: a tangent valid on `[a, b]` is valid on every `[L, U] ⊆ [a, b]` that contains `p` -/
theorem TVal_mono {f : ℕ → ℕ} {a b L U p : ℕ} (h : TVal f a b p) (haL : a ≤ L) (hUb : U ≤ b) (hLp : L ≤ p)
    (hpU : p ≤ U) : TVal f L U p := by
  obtain ⟨-, -, h1, h2, h3⟩ := h
  refine ⟨hLp, hpU, h1, h2, fun s hs1 hs2 => h3 s ?_ ?_⟩
  · exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast haL) SC_pos.le) hs1
  · exact le_trans hs2 (div_le_div_of_nonneg_right (by exact_mod_cast hUb) SC_pos.le)

/-- the pointwise soundness of a point word: the triple's claims, and the interval's tangent claim -/
def PVI (x v : ℕ) : Prop := PV x (trip v) ∧ (ivB v ≠ 0 → TVal (fun _ => trip v) (ivA v) (ivB v) x)

theorem pvi_zero (x : ℕ) : PVI x 0 := by
  refine ⟨?_, fun h => absurd ivB_zero h⟩
  rw [trip_zero]; exact pv_zero x


/-- a point function equal to `w` at `p` and `0` elsewhere -/
def fpt (p w y : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 w (Nat.beq y p)
theorem fpt_self (p w : ℕ) : fpt p w p = w := by simp [fpt]
theorem fpt_ptf {p w : ℕ} (h : PV p w) : PTF (fpt p w) := by
  intro y
  unfold fpt
  cases hb : Nat.beq y p
  · exact pv_zero y
  · have hy : y = p := by simpa using hb
    subst hy; exact h

/-- the one-time check of a point word's interval: none, or the coarse-first tangent check on it -/
def ivOk (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh x v : ℕ) : Bool :=
  Nat.beq (ivB v) 0 || tcheckPZC R top bk tD bD n csh (ivA v) (ivB v) x (trip v) (treadUF R tD bD (ivB v) x)
    (treadDF R tD bD (ivA v) x)

theorem ivOk_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh x v : ℕ} (hn : 0 < n)
    (hpv : PV x (trip v)) (h : ivOk R top bk tD bD n csh x v = true) :
    ivB v ≠ 0 → TVal (fun _ => trip v) (ivA v) (ivB v) x := by
  intro hb
  unfold ivOk at h
  have hb' : Nat.beq (ivB v) 0 = false := by
    cases hc : Nat.beq (ivB v) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) hb
  rw [hb', Bool.false_or] at h
  rw [← fpt_self x (trip v)] at h
  have ht := tangent_valZC hlb hD (fpt_ptf hpv) hR hn h
  exact (TVal_congr (fpt_self x (trip v))).mp ht


/-- the per-leaf interval test of one tangent point `p` on the range `[L, U]` -/
def ivIn (v L U p : ℕ) : Bool :=
  Nat.ble 1 (ivB v) && Nat.ble (ivA v) L && Nat.ble L p && Nat.ble p U && Nat.ble U (ivB v)

theorem tval_of_ivIn {g : ℕ → ℕ} (hg : ∀ x, PVI x (g x)) {L U p : ℕ} (h : ivIn (g p) L U p = true) :
    TVal (tf g) L U p := by
  unfold ivIn at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨h1, haL⟩, hLp⟩, hpU⟩, hUb⟩ := h
  have hb : ivB (g p) ≠ 0 := by omega
  have ht := TVal_mono ((hg p).2 hb) haL hUb hLp hpU
  exact (TVal_congr (f := fun _ => trip (g p)) (f' := tf g) rfl).mp ht

/-- a term's side conditions by precertified intervals (in place of `mokTZC`) -/
def mokI (g : ℕ → ℕ) (L U k m p r : ℕ) : Bool :=
  Nat.ble m 1024 && ((Nat.beq (mw1 k m) 0 || ivIn (g p) L U p) && (Nat.beq (mw2 k m) 0 || ivIn (g r) L U r))

end AMW.Cert.PCell

namespace AMW.Cert.PyrD

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell

/-- `mterm_okZC` with the tangents' validity from precertified intervals -/
theorem mterm_okI {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVI x (g x))
    (L0 L U Uc κ lam p1 p2 : ℕ) (hL0 : L0 ≤ L) (hUc : U ≤ Uc) (hl : lam ≤ 1024)
    (hok : ((Nat.beq (mw1 κ lam) 0 || ivIn (g p1) L U p1) && (Nat.beq (mw2 κ lam) 0 || ivIn (g p2) L U p2)) = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (msl (tf g) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 2000000000 * ((mw1 κ lam : ℝ) + (mw2 κ lam : ℝ))
        ≤ 1000000000 * D ∧
      32768 * (mval top bk (tf g) L Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcp (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ) - 10 * (mcn (tf g) L0 (mw1 κ lam) (mw2 κ lam) p1 p2 : ℝ)
        ≤ 327680000000000 * 1024 * wfun s := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hok
  have tv : ∀ (lk pk : ℕ), (lk = 0 ∨ ivIn (g pk) L U pk = true) → lk = 0 ∨ TVal (tf g) L U pk :=
    fun lk pk h => h.imp id (tval_of_ivIn hg)
  obtain ⟨h1, h2⟩ := hok
  obtain ⟨D, hD1, hb⟩ := mterm_minV hlb L0 L U Uc (mwc κ lam) (mw1 κ lam) (mw2 κ lam) p1 p2 hL0 hUc
    (mw_sum κ lam hl) (tv _ _ h1) (tv _ _ h2) s hs1 hs2
  have pk : ∀ (lk pk : ℕ), (lk = 0 ∨ TVal (tf g) L U pk) →
      (lk : ℝ) * (((hi32 (hi32 (tf g pk)) - 2000000000 : ℕ) : ℝ) - ((2000000000 - hi32 (hi32 (tf g pk)) : ℕ) : ℝ))
        * ((pk - L0 : ℕ) : ℝ) = (lk : ℝ) * ((hi32 (hi32 (tf g pk)) : ℝ) - 2000000000) * ((pk : ℝ) - L0) := by
    intro lk pk h
    rw [natsub_pair]
    rcases h with h | h
    · rw [h]; simp
    · rw [Nat.cast_sub (hL0.trans h.1)]
  have e1 := pk _ _ (tv _ _ h1)
  have e2 := pk _ _ (tv _ _ h2)
  refine ⟨D, ?_, ?_⟩
  · unfold msl; simp only [Nat.add_eq, Nat.mul_eq]; push_cast; linarith
  · unfold mval mcp mcn
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at *
    push_cast at *
    nlinarith [hb, e1, e2]

end AMW.Cert.PyrD

namespace AMW.Cert.PCell

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- `mtermTZC` with `mokI`: the per-term bound `mcheckGX_sound` consumes -/
theorem mtermTI {top : ℕ} {bk : ℕ → ℕ} {g : ℕ → ℕ} (hlb : LBSound top bk) (hg : ∀ x, PVI x (g x))
    (L0 L U k m p r : ℕ) (hL0 : L0 ≤ L) (hok : mokI g L U k m p r = true)
    (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ∃ D : ℝ, (mslT (tf g) k m p r : ℝ) - 2000000000 * (mwT k m : ℝ) ≤ 1000000000 * D ∧
      32768 * (mvT top bk (tf g) L (uc L U) k m p r : ℝ) + 327680000000000 * (D * (s - (L0 : ℝ) / 32768))
        + 10 * (mcpT (tf g) L0 k m p r : ℝ) - 10 * (mcnT (tf g) L0 k m p r : ℝ) ≤ 327680000000000 * 1024 * wfun s := by
  unfold mokI at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨D, h1, h2⟩ := mterm_okI hlb hg L0 L U (uc L U) k m p r hL0 (le_uc L U) hok.1
    (by simp only [Bool.and_eq_true]; exact hok.2) s hs1 hs2
  refine ⟨D, ?_, h2⟩
  simp only [mslT, mwT, Nat.add_eq]; push_cast; linarith

end AMW.Cert.PCell

end

end
end -- development split closes the original anonymous section
