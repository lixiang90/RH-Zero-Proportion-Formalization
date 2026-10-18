/- Performance update: explicit noncomputable certificate definitions omit
unused executable code. Every evaluator, finite guard, public target and
inherited notice is retained. Source-specific verification is separate. -/
/- Shared continuation elimination keeps decoded values abstract in
the existing leaf soundness proof, without changing its evaluator. -/
/-
Zero Forge / @zkvoxels (GitHub:cafeai), 2026-10-18.
Changes to attributed ajp88/rhajp s1R (Apache-2.0): exact rational certificate
floor and, where selected, reflection-symmetric pair/gap weights optimized
against every actual fixed-tree leaf and every original cover/tail/capacity
guard. Profile, geometric trees, point data and original soundness machinery
retained. All inherited comments/notices retained verbatim.
Candidate pending complete Lean elaboration, Comparator and two-kernel replay.
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
import ChallengeDeps.CandidateSpec
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
noncomputable def cAMn : ℕ → ℤ
 | 0 => 1000000000
 | 1 => 13474154
 | 2 => -15663835
 | 3 => 4014071
 | 4 => 6888777
 | 5 => -1266079
 | 6 => 4677638
 | 7 => -6896515
 | 8 => 3494966
 | 9 => -6098202
 | 10 => 5362661
 | 11 => -626814
 | 12 => -251883
 | _ => 0
noncomputable def cAM (j : ℕ) : ℚ := (cAMn j : ℚ) / 10 ^ 9
noncomputable def ωAM (j : ℕ) : ℝ := if j = 0 then Real.sqrt 2 else 2 * π * j
noncomputable def vAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, (cAM j : ℝ) * Real.cos (ωAM j * s)
noncomputable def MAM : ℝ := 5 / 4
noncomputable def phiW (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ :=
 Real.sqrt (vAM (u / L) / MAM) * Taper.phi ϱ L w u
noncomputable def fW (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (vAM (u / L) / MAM)
theorem phiW_eq_mul (ϱ : ℝ → ℝ) (L w u : ℝ) : phiW ϱ L w u = fW L u * Taper.phi ϱ L w u := rfl
noncomputable def localFunW (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
 AdmWindow.localFun (phiW P.ϱ (P.L T) P.w) (P.L T)
theorem MAM_pos : (0 : ℝ) < MAM := by norm_num [MAM]
theorem cAM_zero : (cAM 0 : ℝ) = 1 := by norm_num [cAM, cAMn]
theorem ωAM_zero : ωAM 0 = Real.sqrt 2 := by simp [ωAM]
theorem ωAM_succ (j : ℕ) : ωAM (j + 1) = 2 * π * ((j : ℝ) + 1) := by
 simp [ωAM]
noncomputable def pAM (s : ℝ) : ℝ := ∑ j ∈ Finset.range 12, (cAM (j + 1) : ℝ) * Real.cos (ωAM (j + 1) * s)
theorem vAM_eq (s : ℝ) : vAM s = Real.cos (Real.sqrt 2 * s) + pAM s := by
 rw [vAM, Finset.sum_range_succ', cAM_zero, ωAM_zero, one_mul, add_comm]
 rfl
theorem sum_abs_cAM_succ :
   ∑ j ∈ Finset.range 12, |(cAM (j + 1) : ℝ)| ≤ 13743119 / 200000000 := by
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num [abs_div]
theorem abs_pAM_le (s : ℝ) : |pAM s| ≤ 13743119 / 200000000 := by
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
theorem vAM_zero : vAM 0 = 1007108939 / 10 ^ 9 := by
 simp only [vAM, mul_zero, Real.cos_zero, mul_one, Finset.sum_range_succ, Finset.sum_range_zero,
   cAM, cAMn]
 norm_num
theorem vAM_continuous : Continuous vAM := by
 unfold vAM; fun_prop
theorem vAM_contDiff : ContDiff ℝ ⊤ vAM := by
 unfold vAM
 exact ContDiff.sum fun j _ => contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
noncomputable def vAMd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j * Real.sin (ωAM j * s))
noncomputable def vAMdd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 13, -((cAM j : ℝ) * ωAM j ^ 2 * Real.cos (ωAM j * s))
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
noncomputable def hW (L : ℝ) (u : ℝ) : ℝ := vAM (u / L) / MAM
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
noncomputable def KfunAM (x : ℝ) : ℝ := ∫ t in (-(1:ℝ)/2)..(1/2), vAM t * Real.cos (2 * π * x * t)
noncomputable def kfunAM (x : ℝ) : ℝ := KfunAM x / KfunAM 0
noncomputable def wfunAM (x : ℝ) : ℝ := kfunAM x ^ 2
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
noncomputable def KMT (x : ℝ) : ℝ :=
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
noncomputable def corrAM (x : ℝ) : ℝ :=
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
noncomputable def vConvAM (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2 - r), vAM s * vAM (s + r)
noncomputable def aInf : ℝ := (∫ s in (-(1:ℝ)/2)..(1/2), vAM s) / MAM
noncomputable def bInf : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), (vAM s / MAM) ^ 2
noncomputable def JInf : ℝ := 2 * (∫ r in (0:ℝ)..1, vConvAM r * r) / MAM ^ 2
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
noncomputable def sW (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (hW L) u
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
noncomputable def ext0 (q : ℝ → ℝ) : ℝ → ℝ := (Icc (-(1:ℝ)/2) (1/2)).indicator q
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
noncomputable def acor (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s, ext0 q s * ext0 q (s + r)
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
noncomputable def Xk (n : ℕ) : ℝ :=
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
noncomputable def dAM (n : ℕ) : ℝ := (cAM (n + 1) : ℝ)
noncomputable def ek (n : ℕ) (t : ℝ) : ℝ := Real.cos (2 * π * ((n : ℝ) + 1) * t)
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
noncomputable def betaV : ℝ :=
 Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2)
   + ∑ n ∈ Finset.range 12, dAM n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
noncomputable def rV (s : ℝ) : ℝ :=
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
noncomputable def PAM : ℝ := ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
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
noncomputable def HW : ℝ := 2 - (ThmD.cRatio 1 aInf bInf JInf)⁻¹
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
noncomputable def PAMhi : ℝ :=
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
   (6721290091768038344368273523390880473594 / 10 ^ 40 : ℝ) ≤ 3 / 2 - (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30))
     - PAMhi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) := by
 unfold PAMhi dAM
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num
theorem HW_ge : (6721290091768038344368273523390880473594 / 10 ^ 40 : ℝ) ≤ HW := by
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
noncomputable def atW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : Params := ⟨fun x => W T (P.L T / 2 - P.w * x), P.lam, P.w⟩
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
noncomputable def tCosQ (t : ℚ) : ℚ :=
 let s := t * t
 1 + s * (-1/2 + s * (1/24 + s * (-1/720 + s * (1/40320 + s * (-1/3628800)))))
noncomputable def tSinQ (t : ℚ) : ℚ :=
 let s := t * t
 t * (1 + s * (-1/6 + s * (1/120 + s * (-1/5040 + s * (1/362880 + s * (-1/39916800))))))
noncomputable def errQ : ℚ := 13/5748019200
noncomputable def fl (x : ℚ) : ℚ := ((⌊x * 10000000000⌋ : ℤ) : ℚ) / 10000000000
noncomputable def cl (x : ℚ) : ℚ := ((⌈x * 10000000000⌉ : ℤ) : ℚ) / 10000000000
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
noncomputable def piLoQ : ℚ := 3141592 / 10 ^ 6
noncomputable def piHiQ : ℚ := 3141593 / 10 ^ 6
noncomputable def s2LoQ : ℚ := 14142135 / 10 ^ 7
noncomputable def s2HiQ : ℚ := 14142136 / 10 ^ 7
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
noncomputable def imulZ (e : ℤ) (I : ℚ × ℚ) : ℚ × ℚ :=
 if 0 ≤ e then ((e:ℚ) * I.1, (e:ℚ) * I.2) else ((e:ℚ) * I.2, (e:ℚ) * I.1)
noncomputable def iadd (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 + J.1, I.2 + J.2)
noncomputable def isub (I J : ℚ × ℚ) : ℚ × ℚ := (I.1 - J.2, I.2 - J.1)
noncomputable def InI (I : ℚ × ℚ) (x : ℝ) : Prop := ((I.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((I.2 : ℚ) : ℝ)
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
noncomputable def piMul (S : ℚ × ℚ) : ℚ × ℚ := (min (piLoQ * S.1) (piHiQ * S.1), max (piLoQ * S.2) (piHiQ * S.2))
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
noncomputable def TLo (a : ℚ) : ℚ := fl (piLoQ * a)
noncomputable def THi (a : ℚ) : ℚ := cl (piHiQ * a)
noncomputable def cosI (a : ℚ) : ℚ × ℚ := (fl (tCosQ (THi a) - errQ), cl (tCosQ (TLo a) + errQ))
noncomputable def sinI (a : ℚ) : ℚ × ℚ := (fl (tSinQ (TLo a) - errQ), cl (tSinQ (THi a) + errQ))
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
noncomputable def csA : ℕ → ℤ × ℤ
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
noncomputable def kOf (t : ℚ) : ℕ := (⌊2 * t + 1 / 2⌋).toNat
noncomputable def rOf (t : ℚ) : ℚ := t - (kOf t : ℚ) / 2
noncomputable def sinPiI (t : ℚ) : ℚ × ℚ :=
 if 0 ≤ rOf t then iadd (imulZ (csA (kOf t)).2 (cosI (rOf t))) (imulZ (csA (kOf t)).1 (sinI (rOf t)))
 else isub (imulZ (csA (kOf t)).2 (cosI (-rOf t))) (imulZ (csA (kOf t)).1 (sinI (-rOf t)))
noncomputable def sinPiOk (t : ℚ) : Bool := decide (0 ≤ TLo |rOf t|) && decide (THi |rOf t| ≤ 1)
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
noncomputable def phiM (f : ℝ → ℝ) (ϱ : ℝ → ℝ) (L w : ℝ) (u : ℝ) : ℝ := f u * Taper.phi ϱ L w u
noncomputable def cMod (ϱ : ℝ → ℝ) (A B : ℝ) : ℝ := Taper.cRho ϱ + A + A ^ 2 + B
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
noncomputable def fP (p : ℝ → ℝ) (L : ℝ) (u : ℝ) : ℝ := Real.sqrt (p (u / L))
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
noncomputable def sumQ (f : ℕ → ℚ) : ℕ → ℚ
 | 0 => 0
 | n + 1 => sumQ f n + f n
noncomputable def allQ (f : ℕ → Bool) : ℕ → Bool
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
noncomputable def sinTabZ : List (ℤ × ℤ) := [(-23, 23), (122715334, 122715420), (245412211, 245412336), (368072129, 368072293), (490676618, 490676821), (613207212, 613207454), (735645460, 735645741), (857972922, 857973241), (980171177, 980171535), (1102221821, 1102222218), (1224106475, 1224106910), (1345806783, 1345807256), (1467304418, 1467304929), (1588581082, 1588581631), (1709618512, 1709619097), (1830398479, 1830399103), (1950902796, 1950903456), (2071113314, 2071114011), (2191011930, 2191012663), (2310580587, 2310581356), (2429801281, 2429802085), (2548656054, 2548656894), (2667127010, 2667127885), (2785196306, 2785197216), (2902846163, 2902847107), (3020058861, 3020059840), (3136816751, 3136817762), (3253102246, 3253103291), (3368897838, 3368898914), (3484186085, 3484187194), (3598949628, 3598950767), (3713171181, 3713172353), (3826833546, 3826834747), (3939919603, 3939920835), (4052412323, 4052413585), (4164294765, 4164296055), (4275550080, 4275551398), (4386161513, 4386162859), (4496112407, 4496113780), (4605386202, 4605387601), (4713966444, 4713967869), (4821836780, 4821838231), (4928980966, 4928982440), (5035382865, 5035384364), (5141026455, 5141027976), (5245895825, 5245897369), (5349975184, 5349976748), (5453248855, 5453250441), (5555701288, 5555702893), (5657317053, 5657318678), (5758080847, 5758082491), (5857977496, 5857979157), (5956991955, 5956993634), (6055109314, 6055111008), (6152314796, 6152316505), (6248593762, 6248595486), (6343931713, 6343933451), (6438314292, 6438316043), (6531727285, 6531729047), (6624156624, 6624158398), (6715588390, 6715590173), (6806008813, 6806010606), (6895404278, 6895406078), (6983761319, 6983763128), (7071067175, 7071068989), (7157307633, 7157309399), (7242470227, 7242471943), (7326542131, 7326543799), (7409510684, 7409512305), (7491363392, 7491364966), (7572087929, 7572089455), (7651672136, 7651673616), (7730104029, 7730105464), (7807371797, 7807373186), (7883463803, 7883465147), (7958368588, 7958369889), (8032074872, 8032076129), (8104571555, 8104572769), (8175847718, 8175848890), (8245892629, 8245893759), (8314695739, 8314696827), (8382246685, 8382247733), (8448535296, 8448536304), (8513551588, 8513552557), (8577285771, 8577286701), (8639728245, 8639729137), (8700869608, 8700870463), (8760700651, 8760701470), (8819212365, 8819213148), (8876395938, 8876396686), (8932242757, 8932243471), (8986744414, 8986745095), (9039892700, 9039893347), (9091679610, 9091680226), (9142097347, 9142097932), (9191138318, 9191138872), (9238795136, 9238795661), (9285060626, 9285061122), (9329927819, 9329928287), (9373389959, 9373390400), (9415440501, 9415440916), (9456073112, 9456073501), (9495281672, 9495282037), (9533060278, 9533060620), (9569403240, 9569403558), (9604305084, 9604305381), (9637760555, 9637760831), (9669764615, 9669764870), (9700312443, 9700312679), (9729399439, 9729399657), (9757021224, 9757021424), (9783173636, 9783173820), (9807852739, 9807852907), (9831054814, 9831054968), (9852776368, 9852776508), (9873014130, 9873014257), (9891765053, 9891765168), (9909026311, 9909026415), (9924795306, 9924795400), (9939069663, 9939069749), (9951847233, 9951847310), (9963126091, 9963126160), (9972904538, 9972904601), (9981181102, 9981181160), (9987954536, 9987954590), (9993223821, 9993223872), (9996988163, 9996988211), (9999246995, 9999247042), (9999999977, 10000000023)]
noncomputable def tabI (q : ℕ) : ℚ × ℚ :=
 (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)
noncomputable def tabOk : Bool :=
 allQ (fun q => sinPiOk ((q : ℚ) / 256) && decide ((tabI q).1 ≤ (sinPiI ((q : ℚ) / 256)).1)
   && decide ((sinPiI ((q : ℚ) / 256)).2 ≤ (tabI q).2)) 129
noncomputable def ineg (I : ℚ × ℚ) : ℚ × ℚ := (-I.2, -I.1)
noncomputable def sinLook (r : ℕ) : ℚ × ℚ :=
 if r % 512 ≤ 128 then tabI (r % 512)
 else if r % 512 ≤ 256 then tabI (256 - r % 512)
 else if r % 512 ≤ 384 then ineg (tabI (r % 512 - 256))
 else ineg (tabI (512 - r % 512))
noncomputable def midQ (i : ℕ) : ℚ := (2 * i + 1) / 512
noncomputable def termU (i j : ℕ) : ℚ :=
 if j = 0 then -(s2LoQ * max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)))
 else if 0 ≤ -(2 * j * cAM j) then -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).2
 else -(2 * j * cAM j) * (piMul (sinLook (j * (2 * i + 1)))).1
noncomputable def termOk (i : ℕ) : Bool := decide (0 ≤ fl (s2LoQ * midQ i)) && decide (s2HiQ * midQ i ≤ 1)
noncomputable def cellU (i : ℕ) : ℚ := sumQ (termU i) 13 + 87 / 512
noncomputable def pvCheck (ρ : ℚ) : Bool :=
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
noncomputable def cAMW (ϱ : ℝ → ℝ) : ℝ := cMod ϱ (14 / 5) (348 / 5 + 2 * (14 / 5) ^ 2)
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
noncomputable def WAM (P : Params) (T : ℝ) : ℝ → ℝ := phiW P.ϱ (P.L T) P.w
noncomputable def atAM (P : Params) (T : ℝ) : Params := atW P (WAM P) T
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
noncomputable def lfW (P : Params) (W : ℝ → ℝ → ℝ) (T : ℝ) : PrimeSide.LocalFun := AdmWindow.localFun (W T) (P.L T)
variable (P : Params) (W : ℝ → ℝ → ℝ)
noncomputable def concreteDataW (Z : ZeroConfig) : DataD P where
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
noncomputable def LocalHypsCoreWEventually (c : ℝ) : Prop :=
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
noncomputable def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3
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
noncomputable def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
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
noncomputable def Kfun (x : ℝ) : ℝ := AMW.KfunAM x
noncomputable def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0
noncomputable def wfun (x : ℝ) : ℝ := kfun x ^ 2
noncomputable def ptsN (n : ℕ) (g : Fin (n - 1) → ℝ) (i : Fin n) : ℝ :=
 ∑ j : Fin (n - 1), if (j : ℕ) < (i : ℕ) then g j else 0
section Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def offDiagSqOn (G : Matrix ι ι ℂ) (B : Finset ι) : ℝ :=
 ∑ i ∈ B, ∑ j ∈ B, if i = j then 0 else ‖G i j‖ ^ 2
noncomputable def spanOf (x : ι → ℝ) (B : Finset ι) : ℝ :=
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
noncomputable def defect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : ℝ := rtrace (specMap hM Psi)
lemma defect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : 0 ≤ defect hM := by
 unfold defect
 rw [rtrace_specMap]
 exact Finset.sum_nonneg fun _ _ => Psi_nonneg _
noncomputable def blockDefect {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) : ℝ :=
 defect (hM.submatrix (Subtype.val : B → ι))
lemma blockDefect_nonneg {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (B : Finset ι) :
   0 ≤ blockDefect hM B :=
 defect_nonneg _
end Blocks
section BlockLevel
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)
noncomputable def Vsimple (c : ℝ) : Matrix d D.S₁ ℂ := fun k z => D.v z k / (Real.sqrt c : ℂ)
noncomputable def P₁ (c : ℝ) : Matrix d d ℂ := Vsimple D c * (Vsimple D c)ᴴ
noncomputable def Q' (c : ℝ) : Matrix d d ℂ := D.blockP c + D.blockQ c - P₁ D c
noncomputable def gramS₁ (c : ℝ) : Matrix D.S₁ D.S₁ ℂ := (Vsimple D c)ᴴ * Vsimple D c
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
noncomputable def mtParams (T : ℝ) : Params := AMW.atAM (paramsOf stdProfile 1) T
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
noncomputable def xnorm (ρ : ℂ) : ℝ := P.L T * (ρ.im - T) / (2 * Real.pi)
noncomputable def aL2 : ℝ := P.a T * P.L T ^ 2
noncomputable def bdata : ZeroBlockData (ZI Z T) (Fin (P.d T)) := blockData Z T P phiHatConj
noncomputable def retained : Finset (ZI Z T) :=
 (bdata Z P T).S₁.filter fun z =>
   P.L T ^ 2 ≤ xnorm P T z ∧ xnorm P T z ≤ (P.d T : ℝ) - P.L T ^ 2
lemma mem_S₁_of_mem_retained {z : ZI Z T} (hz : z ∈ retained Z P T) : z ∈ (bdata Z P T).S₁ :=
 (Finset.mem_filter.mp hz).1
noncomputable def toS₁ : retained Z P T → (bdata Z P T).S₁ :=
 fun z => ⟨z.1, mem_S₁_of_mem_retained Z P T z.2⟩
lemma toS₁_injective : Function.Injective (toS₁ Z P T) :=
 fun _ _ h => Subtype.ext (congrArg (Subtype.val : (bdata Z P T).S₁ → ZI Z T) h)
noncomputable def gram : Matrix (retained Z P T) (retained Z P T) ℂ :=
 (gramS₁ (bdata Z P T) (aL2 P T)).submatrix (toS₁ Z P T) (toS₁ Z P T)
lemma gram_isHermitian : (gram Z P T).IsHermitian :=
 (gramS₁_isHermitian _ _).submatrix _
noncomputable def Dcirc : ℝ := defect (gram_isHermitian Z P T)
noncomputable def xret : retained Z P T → ℝ := fun z => xnorm P T (z.1 : ℂ)
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
noncomputable def sortedExt (y : Fin m → ℝ) (n : ℕ) : ℝ := if h : n < m then y ⟨n, h⟩ else 0
lemma sortedExt_of_lt (y : Fin m → ℝ) {n : ℕ} (h : n < m) : sortedExt y n = y ⟨n, h⟩ := by
 unfold sortedExt; rw [dif_pos h]
lemma sortedExt_mono {y : Fin m → ℝ} (hy : StrictMono y) {a b : ℕ} (hab : a ≤ b) (hb : b < m) :
   sortedExt y a ≤ sortedExt y b := by
 rw [sortedExt_of_lt y (lt_of_le_of_lt hab hb), sortedExt_of_lt y hb]
 exact hy.monotone (Fin.mk_le_mk.mpr hab)
noncomputable def windowGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 1) → ℝ :=
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
noncomputable def compressWeight {M : Matrix ι ι 𝕜} (hM : M.IsHermitian) (g : κ → ι) (i : ι) : ℝ :=
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
noncomputable def multPart (c : ℝ) : Matrix d d ℂ :=
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
noncomputable def P₀ : Params := paramsOf stdProfile 1
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
noncomputable def Fw (W : WCert n) (g : Fin (n - 1) → ℝ) : ℝ :=
 ∑ r, W.b r * g r
   + ∑ i : Fin n, ∑ j : Fin n,
       if (i : ℕ) < (j : ℕ) then W.a i j * wfun (ptsN n g j - ptsN n g i) else 0
noncomputable def WCert.B (W : WCert n) : ℝ := ∑ r, W.b r
noncomputable def WCert.spanMass (W : WCert n) (s : ℕ) : ℝ :=
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
noncomputable def sortedOn (x : ι → ℝ) (B : Finset ι) : ℕ → ℝ :=
 sortedExt (⇑((B.image x).orderEmbOfFin (rfl : (B.image x).card = (B.image x).card)))
noncomputable def blkPress (b : Fin (n - 1) → ℝ) (x : ι → ℝ) (B : Finset ι) : ℝ :=
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
noncomputable def sRank (x : ι → ℝ) {m : ℕ} (hS : (univ.image x).card = m) (i : ι) : Fin m :=
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
noncomputable def DZ : ℕ := 1000000000000000
noncomputable def ndivc (a b : ℕ) : ℕ := Nat.div (Nat.sub (Nat.add a b) 1) b
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
noncomputable def v (a : SZ) : ℝ := (a.p : ℝ) - a.n
noncomputable def ofN (m : ℕ) : SZ := ⟨m, 0⟩
noncomputable def add (a b : SZ) : SZ := ⟨Nat.add a.p b.p, Nat.add a.n b.n⟩
noncomputable def sub (a b : SZ) : SZ := ⟨Nat.add a.p b.n, Nat.add a.n b.p⟩
noncomputable def neg (a : SZ) : SZ := ⟨a.n, a.p⟩
noncomputable def mul (a b : SZ) : SZ := ⟨Nat.add (Nat.mul a.p b.p) (Nat.mul a.n b.n), Nat.add (Nat.mul a.p b.n) (Nat.mul a.n b.p)⟩
noncomputable def muln (m : ℕ) (a : SZ) : SZ := ⟨Nat.mul m a.p, Nat.mul m a.n⟩
noncomputable def le (a b : SZ) : Bool := Nat.ble (Nat.add a.p b.n) (Nat.add b.p a.n)
noncomputable def nonneg (a : SZ) : Bool := Nat.ble a.n a.p
noncomputable def min (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) b a (a.le b)
noncomputable def max (a b : SZ) : SZ := Bool.rec (motive := fun _ => SZ) a b (a.le b)
noncomputable def fl (a : SZ) (d : ℕ) : SZ :=
 Bool.rec (motive := fun _ => SZ) ⟨0, ndivc (Nat.sub a.n a.p) d⟩ ⟨Nat.div (Nat.sub a.p a.n) d, 0⟩ (Nat.ble a.n a.p)
noncomputable def ce (a : SZ) (d : ℕ) : SZ :=
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
noncomputable def Enc (I : IV) (a : ℝ) : Prop := I.lo.v / DZ ≤ a ∧ a ≤ I.hi.v / DZ
noncomputable def ofN (a b : ℕ) : IV := ⟨⟨a, 0⟩, ⟨b, 0⟩⟩
noncomputable def zero : IV := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩
noncomputable def add (I J : IV) : IV := ⟨I.lo.add J.lo, I.hi.add J.hi⟩
noncomputable def sub (I J : IV) : IV := ⟨I.lo.sub J.hi, I.hi.sub J.lo⟩
noncomputable def neg (I : IV) : IV := ⟨I.hi.neg, I.lo.neg⟩
noncomputable def muln (m : ℕ) (I : IV) : IV := ⟨I.lo.muln m, I.hi.muln m⟩
noncomputable def mul (I J : IV) : IV :=
 ⟨SZ.fl (SZ.min (SZ.min (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.min (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ,
  SZ.ce (SZ.max (SZ.max (I.lo.mul J.lo) (I.lo.mul J.hi)) (SZ.max (I.hi.mul J.lo) (I.hi.mul J.hi))) DZ⟩
noncomputable def mulc (C I : IV) : IV :=
 ⟨SZ.fl (Bool.rec (motive := fun _ => SZ) (C.hi.mul I.lo) (C.lo.mul I.lo) I.lo.nonneg) DZ,
  SZ.ce (Bool.rec (motive := fun _ => SZ) (C.lo.mul I.hi) (C.hi.mul I.hi) I.hi.nonneg) DZ⟩
noncomputable def divn (I : IV) (d : ℕ) : IV := ⟨I.lo.fl d, I.hi.ce d⟩
noncomputable def divp (I : IV) (e0 e1 : ℕ) : IV :=
 ⟨Bool.rec (motive := fun _ => SZ) ((I.lo.muln DZ).fl e0) ((I.lo.muln DZ).fl e1) I.lo.nonneg,
  Bool.rec (motive := fun _ => SZ) ((I.hi.muln DZ).ce e1) ((I.hi.muln DZ).ce e0) I.hi.nonneg⟩
noncomputable def scl (ng : Bool) (m : ℕ) (I : IV) : IV := Bool.rec (motive := fun _ => IV) (I.muln m) (I.muln m).neg ng
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
noncomputable def SC : ℕ := 32768
noncomputable def DZ2 : ℕ := 500000000000000
noncomputable def PLN : ℕ := 314159265358979323846
noncomputable def PUN : ℕ := 314159265358979323847
noncomputable def E20 : ℕ := 100000000000000000000
noncomputable def ERRD : ℕ := 2262000
noncomputable def E9 : ℕ := 1000000000
noncomputable def CDEN : ℕ := Nat.mul 3628800 (Nat.pow DZ 9)
noncomputable def SDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 10)
noncomputable def SCDEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)
noncomputable def S1DEN : ℕ := Nat.mul 3991680 (Nat.pow DZ 8)
noncomputable def S2DEN : ℕ := Nat.mul 39916800 (Nat.pow DZ 9)
noncomputable def DZp (k : ℕ) : ℕ := Nat.pow DZ k
noncomputable def cosP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 3628800 (DZp 10)) (Nat.mul (Nat.mul 151200 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))
noncomputable def cosN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1814400 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 5040 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
noncomputable def sinP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 39916800 T) (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 5)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 9)) (DZp 2))
noncomputable def sinN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 3)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 7)) (DZp 4))) (Nat.pow T 11)
noncomputable def scP (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 39916800 (DZp 10)) (Nat.mul (Nat.mul 332640 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 110 (Nat.pow T 8)) (DZp 2))
noncomputable def scN (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 6652800 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 7920 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
noncomputable def s1P (T : ℕ) : ℕ := Nat.add (Nat.mul (Nat.mul 133056 (Nat.pow T 3)) (DZp 6)) (Nat.mul (Nat.mul 88 (Nat.pow T 7)) (DZp 2))
noncomputable def s1N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 1330560 T) (DZp 8)) (Nat.mul (Nat.mul 4752 (Nat.pow T 5)) (DZp 4))) (Nat.pow T 9)
noncomputable def s2P (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul (Nat.mul 3991680 (Nat.pow T 2)) (DZp 8)) (Nat.mul (Nat.mul 6160 (Nat.pow T 6)) (DZp 4))) (Nat.pow T 10)
noncomputable def s2N (T : ℕ) : ℕ := Nat.add (Nat.add (Nat.mul 13305600 (DZp 10)) (Nat.mul (Nat.mul 237600 (Nat.pow T 4)) (DZp 6))) (Nat.mul (Nat.mul 90 (Nat.pow T 8)) (DZp 2))
noncomputable def PIC : IV := IV.ofN 3141592653589793 3141592653589794
noncomputable def PI2C : IV := IV.ofN 9869604401089357 9869604401089364
noncomputable def GAM0 : ℕ := 1654998581400000
noncomputable def GAM1 : ℕ := 1654998603600000
noncomputable def G1C : IV := IV.ofN 2654998581400000 2654998603600000
noncomputable def G2C : IV := IV.ofN 4309997162800000 4309997207200000
noncomputable def RHOC : IV := IV.ofN 1088464550157349 1088464557864635
noncomputable def SIGC : IV := IV.ofN 346469027075676 346469029528983
noncomputable def TAUC : IV := IV.ofN 3419512234467246 3419512258680401
noncomputable def CE : List (ℕ × ℕ × Bool) :=
 [(1, 13474154, true), (2, 15663835, true), (3, 4014071, true), (4, 6888777, false), (5, 1266079, false),
  (6, 4677638, false), (7, 6896515, false), (8, 3494966, false), (9, 6098202, false), (10, 5362661, false),
  (11, 626814, false), (12, 251883, true)]
noncomputable def CJ (j : ℕ) : ℕ × Bool :=
 match j with
 | 1 => (13474154, false) | 2 => (15663835, true) | 3 => (4014071, false) | 4 => (6888777, false)
 | 5 => (1266079, true) | 6 => (4677638, false) | 7 => (6896515, true) | 8 => (3494966, false)
 | 9 => (6098202, true) | 10 => (5362661, false) | 11 => (626814, true) | 12 => (251883, true) | _ => (0, false)
structure Acc where
 (pl ph nl nh : ℕ)
noncomputable def Acc.put (a : Acc) (ng : Bool) (e m0 m1 : ℕ) : Acc :=
 Bool.rec (motive := fun _ => Acc) ⟨Nat.add a.pl (Nat.mul e m0), Nat.add a.ph (Nat.mul e m1), a.nl, a.nh⟩
   ⟨a.pl, a.ph, Nat.add a.nl (Nat.mul e m0), Nat.add a.nh (Nat.mul e m1)⟩ ng
noncomputable def mnum (n X X2 J2 : ℕ) : ℕ :=
 Nat.rec (motive := fun _ => ℕ) (Nat.mul X (DZp 2))
   (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul (Nat.add X2 J2) (DZp 3))
     (fun _ _ => Nat.mul (Nat.mul (Nat.mul 2 X) (Nat.add X2 (Nat.mul 3 J2))) (DZp 4)) m) n
noncomputable def hden (n Y : ℕ) : ℕ :=
 Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 Y)
   (fun m _ => Nat.rec (motive := fun _ => ℕ) (Nat.mul 2 (Nat.mul Y Y)) (fun _ _ => Nat.pow Y 3) m) n
noncomputable def mneg (n : ℕ) (ab : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (!ab) true (Nat.beq n 1)
noncomputable def hneg (n : ℕ) : Bool := Nat.beq n 1
noncomputable def farJ (n k XL XU XL2 XU2 : ℕ) (a : Acc) (j e : ℕ) (sg : Bool) : Acc :=
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
noncomputable def farAcc (n k XL XU XL2 XU2 : ℕ) : List (ℕ × ℕ × Bool) → Acc → Acc
 | [], a => a
 | (j, e, sg) :: rest, a => farAcc n k XL XU XL2 XU2 rest (farJ n k XL XU XL2 XU2 a j e sg)
structure CellA where
 (LN UN : ℕ)
namespace CellA
noncomputable def k (c : CellA) : ℕ := Nat.div (Nat.add (Nat.mul 2 (Nat.add c.LN c.UN)) SC) (Nat.mul 2 SC)
noncomputable def side (c : CellA) : Bool := Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)
noncomputable def LLO (c : CellA) : ℕ := Nat.div (Nat.mul c.LN DZ) SC
noncomputable def UHI (c : CellA) : ℕ := ndivc (Nat.mul c.UN DZ) SC
noncomputable def AD (c : CellA) : ℕ := Nat.mul c.k DZ2
noncomputable def RLO (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.UHI) (Nat.sub c.LLO c.AD) c.side
noncomputable def RHI (c : CellA) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.sub c.AD c.LLO) (Nat.sub c.UHI c.AD) c.side
noncomputable def TLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.RLO) E20
noncomputable def TUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.RHI) E20
noncomputable def CI (c : CellA) : IV :=
 ⟨⟨Nat.div (Nat.sub (cosP c.TUZ) (cosN c.TUZ)) CDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (cosP c.TLZ) (cosN c.TLZ)) CDEN) ERRD, 0⟩⟩
noncomputable def SI (c : CellA) : IV :=
 ⟨⟨Nat.div (Nat.sub (sinP c.TLZ) (sinN c.TLZ)) SDEN, ERRD⟩, ⟨Nat.add (ndivc (Nat.sub (sinP c.TUZ) (sinN c.TUZ)) SDEN) ERRD, 0⟩⟩
noncomputable def km4 (c : CellA) : ℕ := Nat.mod c.k 4
noncomputable def CX (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV)
   (Bool.rec (motive := fun _ => IV)
     (Bool.rec (motive := fun _ => IV) (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) c.CI.neg (Nat.beq c.km4 2))
     (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 1))
   c.CI (Nat.beq c.km4 0)
noncomputable def SX (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV)
   (Bool.rec (motive := fun _ => IV)
     (Bool.rec (motive := fun _ => IV) c.CI.neg (Bool.rec (motive := fun _ => IV) c.SI c.SI.neg c.side) (Nat.beq c.km4 2))
     c.CI (Nat.beq c.km4 1))
   (Bool.rec (motive := fun _ => IV) c.SI.neg c.SI c.side) (Nat.beq c.km4 0)
noncomputable def BLZ (c : CellA) : ℕ := Nat.div (Nat.mul PLN c.LLO) E20
noncomputable def BUZ (c : CellA) : ℕ := ndivc (Nat.mul PUN c.UHI) E20
noncomputable def BI (c : CellA) : IV := IV.ofN c.BLZ c.BUZ
noncomputable def PG (c : CellA) : IV := IV.ofN (Nat.div (Nat.mul GAM0 c.BLZ) DZ) (ndivc (Nat.mul GAM1 c.BUZ) DZ)
noncomputable def NI (c : CellA) : IV := c.CX.sub (IV.mulc c.PG c.SX)
noncomputable def E0 (c : CellA) : ℕ := Nat.sub (Nat.div (Nat.mul 2 (Nat.mul c.BLZ c.BLZ)) DZ) DZ
noncomputable def E1 (c : CellA) : ℕ := Nat.sub (ndivc (Nat.mul 2 (Nat.mul c.BUZ c.BUZ)) DZ) DZ
noncomputable def EI (c : CellA) : IV := IV.ofN c.E0 c.E1
noncomputable def ok (c : CellA) : Bool :=
 Nat.ble c.LN c.UN && Nat.ble c.TUZ DZ
   && Bool.rec (motive := fun _ => Bool) (Nat.ble (Nat.mul 2 c.UN) (Nat.mul c.k SC)) (Nat.ble (Nat.mul c.k SC) (Nat.mul 2 c.LN)) c.side
   && Nat.blt 0 c.E0
noncomputable def FA (c : CellA) (n : ℕ) : IV :=
 let k := c.k
 let XL := c.LLO
 let XU := c.UHI
 let XL2 := Nat.mul XL XL
 let XU2 := Nat.mul XU XU
 let a := (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 (farJ n k XL XU XL2 XU2 ⟨0, 0, 0, 0⟩ 1 13474154 true) 2 15663835 true) 3 4014071 true) 4 6888777 false) 5 1266079 false) 6 4677638 false) 7 6896515 false) 8 3494966 false) 9 6098202 false) 10 5362661 false) 11 626814 false) 12 251883 true)
 IV.divn ⟨⟨a.pl, a.nh⟩, ⟨a.ph, a.nl⟩⟩ E9
noncomputable def nearOn (c : CellA) : Bool := Nat.beq (Nat.mod c.k 2) 0 && Nat.ble 2 c.k && Nat.ble c.k 24
noncomputable def S0 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨scP c.TLZ, scN c.TUZ⟩ SCDEN).sub (SZ.ofN ERRD), (SZ.ce ⟨scP c.TUZ, scN c.TLZ⟩ SCDEN).add (SZ.ofN ERRD)⟩
noncomputable def G1 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨s1P c.TLZ, s1N c.TUZ⟩ S1DEN).sub (SZ.ofN (Nat.mul 2 ERRD)), (SZ.ce ⟨s1P c.TUZ, s1N c.TLZ⟩ S1DEN).add (SZ.ofN (Nat.mul 2 ERRD))⟩
noncomputable def G2 (c : CellA) : IV :=
 ⟨(SZ.fl ⟨s2P c.TLZ, s2N c.TUZ⟩ S2DEN).sub (SZ.ofN (Nat.mul 5 ERRD)), (SZ.ce ⟨s2P c.TUZ, s2N c.TLZ⟩ S2DEN).add (SZ.ofN (Nat.mul 5 ERRD))⟩
noncomputable def j0 (c : CellA) : ℕ := Nat.div c.k 2
noncomputable def B0 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 c.S0).divn (Nat.mul 2 E9)) c.nearOn
noncomputable def B1 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero
   ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PIC (Bool.rec (motive := fun _ => IV) c.G1.neg c.G1 c.side))).divn (Nat.mul 2 E9))
   c.nearOn
noncomputable def B2 (c : CellA) : IV :=
 Bool.rec (motive := fun _ => IV) IV.zero ((IV.scl (CJ c.j0).2 (CJ c.j0).1 (IV.mulc PI2C c.G2)).divn (Nat.mul 2 E9)) c.nearOn
noncomputable def SF0 (c : CellA) : IV := c.SX.mul (c.FA 0)
noncomputable def K0 (c : CellA) : IV := (c.NI.neg.divp c.E0 c.E1).add ((IV.mulc SIGC c.SF0).add (IV.mulc RHOC c.B0))
noncomputable def MI (c : CellA) : IV :=
 (IV.mulc c.EI ((IV.mulc G1C c.SX).add (IV.mulc c.PG c.CX))).add (IV.mulc (c.BI.muln 4) c.NI)
noncomputable def E2L (c : CellA) : ℕ := Nat.div (Nat.mul c.E0 c.E0) DZ
noncomputable def E2U (c : CellA) : ℕ := ndivc (Nat.mul c.E1 c.E1) DZ
noncomputable def K1 (c : CellA) : IV :=
 (IV.mulc PIC (c.MI.divp c.E2L c.E2U)).add
   (((IV.mulc RHOC (c.CX.mul (c.FA 0))).add (IV.mulc SIGC (c.SX.mul (c.FA 1)))).add (IV.mulc RHOC c.B1))
noncomputable def N2 (c : CellA) : IV := (IV.mulc c.PG c.SX).sub (IV.mulc G2C c.CX)
noncomputable def E3L (c : CellA) : ℕ := Nat.div (Nat.mul c.E2L c.E0) DZ
noncomputable def E3U (c : CellA) : ℕ := ndivc (Nat.mul c.E2U c.E1) DZ
noncomputable def PP (c : CellA) : IV :=
 ((IV.mulc (IV.ofN c.E2L c.E2U) c.N2).sub ((IV.mulc c.EI c.NI).muln 4)).add ((IV.mulc c.BI c.MI).muln 8)
noncomputable def K2 (c : CellA) : IV :=
 (IV.mulc PI2C (c.PP.divp c.E3L c.E3U)).neg.add
   ((((IV.mulc RHOC (c.CX.mul (c.FA 1))).muln 2).sub (IV.mulc TAUC c.SF0)).add
     ((IV.mulc SIGC (c.SX.mul (c.FA 2))).add (IV.mulc RHOC c.B2)))
noncomputable def KA (c : CellA) : SZ := SZ.max (SZ.ofN 0) (SZ.max c.K0.lo c.K0.hi.neg)
noncomputable def W1 (c : CellA) : IV := (c.K0.mul c.K1).muln 2
noncomputable def W2L (c : CellA) : SZ :=
 SZ.add (SZ.mul (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)) (SZ.max (SZ.ofN 0) (SZ.max c.K1.lo c.K1.hi.neg)))
   ((c.K0.mul c.K2).lo.muln DZ)
end CellA
end AMW.G
noncomputable section
open Real Filter Topology Asymptotics
namespace AMW
noncomputable def sc1 (θ : ℝ) : ℝ := if θ = 0 then 0 else (θ * Real.cos θ - Real.sin θ) / θ ^ 2
noncomputable def sc2 (θ : ℝ) : ℝ := if θ = 0 then -1 / 3 else (-θ ^ 2 * Real.sin θ - 2 * θ * Real.cos θ + 2 * Real.sin θ) / θ ^ 3
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
noncomputable def K1AM (x : ℝ) : ℝ :=
 ∑ j ∈ Finset.range 13, (cAM j : ℝ) *
   ((-(π * sc1 ((ωAM j - 2 * π * x) / 2)) + π * sc1 ((ωAM j + 2 * π * x) / 2)) / 2)
noncomputable def K2AM (x : ℝ) : ℝ :=
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
noncomputable def k1AM (x : ℝ) : ℝ := K1AM x / KfunAM 0
noncomputable def k2AM (x : ℝ) : ℝ := K2AM x / KfunAM 0
noncomputable def w1AM (x : ℝ) : ℝ := 2 * kfunAM x * k1AM x
noncomputable def w2AM (x : ℝ) : ℝ := 2 * (k1AM x ^ 2 + kfunAM x * k2AM x)
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
noncomputable def gamAM : ℝ := (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) / Real.sin (Real.sqrt 2 / 2)
noncomputable def mN (x : ℝ) : ℝ := Real.cos (π * x) - 2 * gamAM * (π * x) * Real.sin (π * x)
noncomputable def mD (x : ℝ) : ℝ := 1 - 2 * (π * x) ^ 2
noncomputable def mNb (x : ℝ) : ℝ := -(1 + 2 * gamAM) * Real.sin (π * x) - 2 * gamAM * (π * x) * Real.cos (π * x)
noncomputable def mM (x : ℝ) : ℝ := mNb x * mD x + 4 * (π * x) * mN x
noncomputable def mN2 (x : ℝ) : ℝ := -(1 + 4 * gamAM) * Real.cos (π * x) + 2 * gamAM * (π * x) * Real.sin (π * x)
noncomputable def mP (x : ℝ) : ℝ := mN2 x * mD x ^ 2 + 4 * mN x * mD x + 8 * (π * x) * mM x
noncomputable def K0AM : ℝ := Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)
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
noncomputable def KMT1 (x : ℝ) : ℝ :=
 (-(π * sc1 ((Real.sqrt 2 - 2 * π * x) / 2)) + π * sc1 ((Real.sqrt 2 + 2 * π * x) / 2)) / 2
noncomputable def KMT2 (x : ℝ) : ℝ :=
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
noncomputable def Tj (n : ℕ) (x : ℝ) : ℝ := (Real.sinc (π * (x - ((n : ℝ) + 1))) + Real.sinc (π * (x + ((n : ℝ) + 1)))) / 2
noncomputable def T1j (n : ℕ) (x : ℝ) : ℝ := (sc1 (π * (x - ((n : ℝ) + 1))) + sc1 (π * (x + ((n : ℝ) + 1)))) / 2
noncomputable def T2j (n : ℕ) (x : ℝ) : ℝ := (sc2 (π * (x - ((n : ℝ) + 1))) + sc2 (π * (x + ((n : ℝ) + 1)))) / 2
noncomputable def rhoAM : ℝ := 1 / K0AM
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
noncomputable def tcos (t : ℝ) : ℝ := 1 - t^2/2 + t^4/24 - t^6/720 + t^8/40320 - t^10/3628800
noncomputable def tsin (t : ℝ) : ℝ := t - t^3/6 + t^5/120 - t^7/5040 + t^9/362880 - t^11/39916800
noncomputable def tsinc (t : ℝ) : ℝ := 1 - t^2/6 + t^4/120 - t^6/5040 + t^8/362880 - t^10/39916800
noncomputable def tsc1 (t : ℝ) : ℝ := -t/3 + t^3/30 - t^5/840 + t^7/45360 - t^9/3991680
noncomputable def tsc2 (t : ℝ) : ℝ := -1/3 + t^2/10 - t^4/168 + t^6/6480 - t^8/443520 + t^10/39916800
noncomputable def terr : ℝ := 13 / 5748019200
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
noncomputable def roff (x : ℝ) : ℝ := if c.side then x - (c.k : ℝ) / 2 else (c.k : ℝ) / 2 - x
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
noncomputable def mf (n : ℕ) (j x : ℝ) : ℝ :=
 if n = 0 then x / (x ^ 2 - j ^ 2) else if n = 1 then -(x ^ 2 + j ^ 2) / (x ^ 2 - j ^ 2) ^ 2
 else 2 * x * (x ^ 2 + 3 * j ^ 2) / (x ^ 2 - j ^ 2) ^ 3
noncomputable def hf (n : ℕ) (j x : ℝ) : ℝ :=
 if n = 0 then 1 / (2 * (x + j)) else if n = 1 then -1 / (2 * (x + j) ^ 2) else 1 / (x + j) ^ 3
noncomputable def fv (n k j : ℕ) (x : ℝ) : ℝ := if 2 * j = k then hf n j x else mf n j x
noncomputable def mmag (n : ℕ) (j x d : ℝ) : ℝ :=
 if n = 0 then x / d else if n = 1 then (x ^ 2 + j ^ 2) / d ^ 2 else 2 * x * (x ^ 2 + 3 * j ^ 2) / d ^ 3
noncomputable def hmag (n : ℕ) (j x : ℝ) : ℝ :=
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
noncomputable def AccEnc (a : Acc) (S : ℝ) : Prop := (a.pl : ℝ) - a.nh ≤ S ∧ S ≤ (a.ph : ℝ) - a.nl
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
noncomputable def fsum (n k : ℕ) (x : ℝ) : List (ℕ × ℕ × Bool) → ℝ
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
noncomputable def Ps0 (u : ℝ) : ℝ := 1 + u ^ 4 / 120 + u ^ 8 / 362880
noncomputable def Ns0 (u : ℝ) : ℝ := u ^ 2 / 6 + u ^ 6 / 5040 + u ^ 10 / 39916800
noncomputable def Ps1 (u : ℝ) : ℝ := u ^ 3 / 30 + u ^ 7 / 45360
noncomputable def Ns1 (u : ℝ) : ℝ := u / 3 + u ^ 5 / 840 + u ^ 9 / 3991680
noncomputable def Ps2 (u : ℝ) : ℝ := u ^ 2 / 10 + u ^ 6 / 6480 + u ^ 10 / 39916800
noncomputable def Ns2 (u : ℝ) : ℝ := 1 / 3 + u ^ 4 / 168 + u ^ 8 / 443520
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
noncomputable def nsel (k : ℕ) (f : ℕ → ℝ) : ℝ :=
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
noncomputable def mabs (I : IV) : SZ := SZ.max (SZ.ofN 0) (SZ.max I.lo I.hi.neg)
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
noncomputable def KAn (c : CellA) : ℕ := Nat.sub c.KA.p c.KA.n
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
noncomputable def SC : ℕ := 32768
noncomputable def KB : ℕ := 1048576
noncomputable def SW : ℕ := 10000000000000
noncomputable def U1 : ℕ := 1000000000
noncomputable def KU1 : ℕ := 2000000000
noncomputable def wfun (x : ℝ) : ℝ := AMW.wfunAM x
noncomputable def w1 (x : ℝ) : ℝ := AMW.w1AM x
noncomputable def w2 (x : ℝ) : ℝ := AMW.w2AM x
noncomputable def kD (_ : ℝ) : ℝ := -1
theorem kD_neg (x : ℝ) : kD x < 0 := by norm_num [kD]
theorem wfun_nonneg (x : ℝ) : 0 ≤ wfun x := AMW.wfunAM_nonneg x
theorem hasDerivAt_wfun (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt wfun (w1 x) x := AMW.hasDerivAt_wfunAM x
theorem hasDerivAt_w1 (x : ℝ) (_ : kD x ≠ 0) : HasDerivAt w1 (w2 x) x := AMW.hasDerivAt_w1AM x
structure CellN where
 (key : ℕ) (WN : ℕ)
namespace CellN
noncomputable def LN (c : CellN) : ℕ := c.key / KB
noncomputable def UN (c : CellN) : ℕ := c.key % KB
noncomputable def A (c : CellN) : AMW.G.CellA := ⟨c.LN, c.UN⟩
noncomputable def okC (c : CellN) : Bool := c.A.ok
noncomputable def NLOZ (c : CellN) : ℤ := (c.A.KAn : ℤ)
noncomputable def DHIZ (c : CellN) : ℤ := (AMW.G.DZ : ℤ)
noncomputable def WZ (c : CellN) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) 0 (Nat.div (Nat.mul (Nat.mul c.A.KAn c.A.KAn) SW) (Nat.mul AMW.G.DZ AMW.G.DZ)) c.okC
noncomputable def okD (c : CellN) : Bool := c.A.ok && Nat.blt 0 c.A.E2L
noncomputable def W1LO (c : CellN) : ℤ := ((c.A.W1.lo.fl 1000000).p : ℤ) - ((c.A.W1.lo.fl 1000000).n : ℤ)
noncomputable def W1HI (c : CellN) : ℤ := ((c.A.W1.hi.ce 1000000).p : ℤ) - ((c.A.W1.hi.ce 1000000).n : ℤ)
noncomputable def convOk (c : CellN) : Bool := c.okD && Nat.blt 0 c.A.E3L && c.A.W2L.nonneg
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
noncomputable def forceR (a : ℕ) (k : ℕ → ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) (k 0) (fun n _ => k (Nat.succ n)) a
noncomputable def fld (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 32 i)) 4294967295
noncomputable def entB (X l i j : ℕ) : ℕ :=
 let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
 let d := Nat.sub 10 kk
 fld (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))
noncomputable def entry (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB (bk j) l i j)
   (Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
   (Nat.ble 11 l)
noncomputable def nmin (a b : ℕ) : ℕ := Nat.sub a (Nat.sub a b)
noncomputable def dstep (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
 let d := Nat.sub E g
 let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
 let h := Nat.shiftRight g t
 let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
 Bool.rec (motive := fun _ => ℕ) (nmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))
noncomputable def dcov (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
 let E := Nat.add ib 1
 dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (dstep top bk k E (fun _ => 0))))))))))))))
noncomputable def BL8 : ℕ := 0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888877777777777777777777777777777777777777777777777777777777777777776666666666666666666666666666666655555555555555554444444433332210
noncomputable def blen (x : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 x)) 15)
   (Nat.add 8 (Nat.land (Nat.shiftRight BL8 (Nat.mul 4 (Nat.shiftRight x 8))) 15)) (Nat.ble 256 x)
noncomputable def lb (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (let k := blen (Nat.shiftRight (Nat.sub hi lo) 5)
      dcov top bk k (Nat.shiftRight (Nat.sub hi 1) k) (Nat.shiftRight lo k))
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
noncomputable def allBelow (n : ℕ) (f : ℕ → Bool) : Bool :=
 Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f k) ih) n
noncomputable def allFrom (a n : ℕ) (f : ℕ → Bool) : Bool :=
 Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false (f (Nat.add a k)) ih) n
noncomputable def cellAt (l i : ℕ) : CellN := ⟨Nat.add (Nat.mul (Nat.shiftLeft i l) KB) (Nat.shiftLeft (Nat.add i 1) l), 0⟩
noncomputable def cellOkCore (c : CellN) (v : ℕ) : Bool :=
 c.okC && decide (((Nat.mul v 1000 : ℕ) : ℤ) * c.DHIZ * c.DHIZ ≤ c.NLOZ * c.NLOZ * SW)
noncomputable def cellOk (l i v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false (cellOkCore (cellAt l i) v) (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
   true (Nat.beq v 0)
noncomputable def blockOkX (X j : ℕ) : Bool :=
 let r := Nat.land X 31
 let D := Nat.sub 10 r
 let Y := Nat.shiftRight X 5
 Nat.ble r 10
   && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk r (Nat.add (Nat.shiftLeft j D) t) (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
   && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
        Nat.ble (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
          (nmin (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                (fld Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))
noncomputable def blockOk (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOkX X j) true (Nat.beq X 0)
noncomputable def topv (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (fld top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)
noncomputable def topOk (top : ℕ) (bk : ℕ → ℕ) : Bool :=
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
noncomputable def CS (l i v : ℕ) : Prop :=
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
noncomputable def BlockSound (X j : ℕ) : Prop :=
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
noncomputable def DSound (k E : ℕ) (f : ℕ → ℕ) : Prop :=
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
noncomputable def LBSound (top : ℕ) (bk : ℕ → ℕ) : Prop :=
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
noncomputable def forceB (a : ℕ) (k : ℕ → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) a
noncomputable def cellOkD (sgn : Bool) (l i v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false
     ((cellAt l i).okD && Bool.rec (motive := fun _ => Bool)
       (decide ((v : ℤ) ≤ (KU1 : ℤ) - (cellAt l i).W1HI)) (decide ((v : ℤ) ≤ (KU1 : ℤ) + (cellAt l i).W1LO)) sgn)
     (Nat.ble (Nat.add (Nat.shiftLeft (Nat.add i 1) l) 1) KB))
   true (Nat.beq v 0)
noncomputable def ptOk (x v : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (Bool.rec (motive := fun _ => Bool) false (cellOkCore ⟨Nat.add (Nat.mul x KB) x, 0⟩ v) (Nat.ble (Nat.add x 1) KB))
   true (Nat.beq v 0)
end AMW.Cert.PyrD
end
section MvtPairDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
noncomputable def fld2 (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 64 i)) 18446744073709551615
noncomputable def lo32 (v : ℕ) : ℕ := Nat.land v 4294967295
noncomputable def hi32 (v : ℕ) : ℕ := Nat.shiftRight v 32
noncomputable def pmin (a b : ℕ) : ℕ :=
 Nat.add (Nat.sub (Nat.land a 4294967295) (Nat.sub (Nat.land a 4294967295) (Nat.land b 4294967295)))
   (Nat.shiftLeft (Nat.sub (Nat.shiftRight a 32) (Nat.sub (Nat.shiftRight a 32) (Nat.shiftRight b 32))) 32)
noncomputable def ple (a b : ℕ) : Bool := Nat.ble (lo32 a) (lo32 b) && Nat.ble (hi32 a) (hi32 b)
noncomputable def entB2 (X l i j : ℕ) : ℕ :=
 let kk := Nat.add l (Nat.sub (Nat.land X 31) l)
 let d := Nat.sub 10 kk
 fld2 (Nat.shiftRight X 5) (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) (Nat.sub (Nat.shiftRight i (Nat.sub kk l)) (Nat.shiftLeft j d)))
noncomputable def entry2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Nat.shiftRight i (Nat.sub 10 l)) fun j => entB2 (bk j) l i j)
   (Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) 0 (Nat.ble 20 l))
   (Nat.ble 11 l)
noncomputable def dstep2 (top : ℕ) (bk : ℕ → ℕ) (k E : ℕ) (ih : ℕ → ℕ) (g : ℕ) : ℕ :=
 let d := Nat.sub E g
 let t := Nat.land (Nat.shiftRight 27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912 (Nat.mul 3 (Nat.add (Nat.mul 17 (Nat.land g 15)) (Nat.sub d (Nat.sub d 16))))) 7
 let h := Nat.shiftRight g t
 let v := forceR (Nat.add (Nat.shiftLeft (Nat.add k t) 40) h) fun lh => entry2 top bk (Nat.shiftRight lh 40) (Nat.land lh 1099511627775)
 Bool.rec (motive := fun _ => ℕ) (pmin v (ih (Nat.shiftLeft (Nat.add h 1) t))) v (Nat.ble E (Nat.shiftLeft (Nat.add h 1) t))
noncomputable def dcov2 (top : ℕ) (bk : ℕ → ℕ) (k ib : ℕ) : ℕ → ℕ :=
 let E := Nat.add ib 1
 dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (dstep2 top bk k E (fun _ => 0))))))))))))))
noncomputable def cellOk2 (l i v : ℕ) : Bool := cellOkD true l i (lo32 v) && cellOkD false l i (hi32 v)
noncomputable def blockOk2X (X j : ℕ) : Bool :=
 let r := Nat.land X 31
 let D := Nat.sub 10 r
 let Y := Nat.shiftRight X 5
 Nat.ble r 10
   && allBelow (Nat.shiftLeft 1 D) (fun t => cellOk2 r (Nat.add (Nat.shiftLeft j D) t) (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 D) 1) t)))
   && allBelow D (fun d => allBelow (Nat.shiftLeft 1 d) (fun t =>
        ple (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 d) 1) t))
          (pmin (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.mul 2 t)))
                (fld2 Y (Nat.add (Nat.sub (Nat.shiftLeft 1 (Nat.add d 1)) 1) (Nat.add (Nat.mul 2 t) 1))))))
noncomputable def blockOk2 (X j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) (blockOk2X X j) true (Nat.beq X 0)
noncomputable def topv2 (top : ℕ) (bk : ℕ → ℕ) (l i : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i)) (fld2 (Nat.shiftRight (bk i) 5) 0) (Nat.beq l 10)
noncomputable def topOk2 (top : ℕ) (bk : ℕ → ℕ) : Bool :=
 allFrom 11 9 fun l => allBelow (Nat.shiftLeft 1 (Nat.sub 19 l)) fun i =>
   ple (fld2 top (Nat.add (Nat.shiftLeft 1 (Nat.sub 19 l)) i))
     (pmin (topv2 top bk (Nat.sub l 1) (Nat.mul 2 i)) (topv2 top bk (Nat.sub l 1) (Nat.add (Nat.mul 2 i) 1)))
end AMW.Cert.PyrD
end MvtPairDefs
noncomputable section
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
noncomputable def fD (sgn : Bool) (x : ℝ) : ℝ := if sgn then w1 x + 2 else 2 - w1 x
noncomputable def CSD (sgn : Bool) (l i v : ℕ) : Prop :=
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
noncomputable def PS (v : ℕ) (x : ℝ) : Prop :=
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
noncomputable def CS2 (l i v : ℕ) : Prop :=
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
noncomputable def BlockSound2 (X j : ℕ) : Prop :=
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
noncomputable def DSound2 (k E : ℕ) (f : ℕ → ℕ) : Prop :=
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
noncomputable def dcell (x : ℕ) : CellN := ⟨Nat.add (Nat.mul x KB) x, 0⟩
noncomputable def ptdOk (x p m : ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool) false
   ((Nat.beq p 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((p : ℤ) ≤ (KU1 : ℤ) + (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1LO)))
     && (Nat.beq m 0 || ((⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).okD && decide ((m : ℤ) ≤ (KU1 : ℤ) - (⟨Nat.add (Nat.mul x KB) x, 0⟩ : CellN).W1HI))))
   (Nat.ble (Nat.add x 1) KB)
noncomputable def lbDr (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
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
noncomputable def LBSoundD (top : ℕ) (bk : ℕ → ℕ) : Prop :=
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
noncomputable def ccell (a b : ℕ) : CellN := ⟨Nat.add (Nat.mul a KB) b, 0⟩
noncomputable def chainOk (a : ℕ) (l : List ℕ) : Bool :=
 List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
   (fun b _ ih a => Nat.ble a b && Nat.ble (Nat.add b 1) KB && (ccell a b).convOk && ih b) l a
noncomputable def chainLast (a : ℕ) (l : List ℕ) : ℕ :=
 List.rec (motive := fun _ => ℕ → ℕ) (fun a => a) (fun b _ ih _ => ih b) l a
noncomputable def dsel (j m a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) a b (Nat.ble m j)
noncomputable def dpk (j k v : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 v (Nat.beq j k)
noncomputable def pt3e (x v : ℕ) : Bool := ptOk x (lo32 v) && ptdOk x (lo32 (hi32 v)) (hi32 (hi32 v))
noncomputable def rgA (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.1 (Nat.mul 20 k)) 1048575
noncomputable def rgB (R : ℕ × ℕ × List (List ℕ)) (k : ℕ) : ℕ := Nat.land (Nat.shiftRight R.2.1 (Nat.mul 20 k)) 1048575
noncomputable def rgOk (R : ℕ × ℕ × List (List ℕ)) : Bool :=
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
noncomputable def PTF (f : ℕ → ℕ) : Prop :=
 ∀ x : ℕ, (lo32 (f x) : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 (f x)) ((x : ℝ) / SC)
end AMW.Cert.PyrD
end
section MinDefs
namespace AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr
noncomputable def treadU (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDr tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
noncomputable def treadD (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDr tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)
noncomputable def mwc (κ lam : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 1024 0 (Nat.beq κ 3)) (Nat.sub 1024 lam) (Nat.beq κ 2))
   0 (Nat.beq κ 1)
noncomputable def mw1 (κ lam : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 (Nat.sub 1024 lam) (Nat.beq κ 3)) lam (Nat.beq κ 2))
   1024 (Nat.beq κ 1)
noncomputable def mw2 (κ lam : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 lam (Nat.beq κ 3)
noncomputable def mval (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U c l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul c (lb top bk L U)) (Nat.add (Nat.mul l1 (lo32 (f p1))) (Nat.mul l2 (lo32 (f p2))))
noncomputable def mcp (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul (Nat.mul l1 (Nat.sub (hi32 (hi32 (f p1))) 2000000000)) (Nat.sub p1 L))
   (Nat.mul (Nat.mul l2 (Nat.sub (hi32 (hi32 (f p2))) 2000000000)) (Nat.sub p2 L))
noncomputable def mcn (f : ℕ → ℕ) (L l1 l2 p1 p2 : ℕ) : ℕ :=
 Nat.add (Nat.mul (Nat.mul l1 (Nat.sub 2000000000 (hi32 (hi32 (f p1))))) (Nat.sub p1 L))
   (Nat.mul (Nat.mul l2 (Nat.sub 2000000000 (hi32 (hi32 (f p2))))) (Nat.sub p2 L))
noncomputable def msl (f : ℕ → ℕ) (l1 l2 p1 p2 : ℕ) : ℕ := Nat.add (Nat.mul l1 (lo32 (hi32 (f p1)))) (Nat.mul l2 (lo32 (hi32 (f p2))))
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
noncomputable def winCell (i : ℕ) : AMW.G.CellA := ⟨8192 + 512 * i, 8704 + 512 * i⟩
noncomputable def winOk (i : ℕ) : Bool := (winCell i).ok && Nat.ble (Nat.mul AMW.G.DZ AMW.G.DZ) (Nat.mul 4 (Nat.mul (winCell i).KAn (winCell i).KAn))
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
noncomputable def nmax (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)
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
noncomputable def gsum (g : ℕ → ℝ) (i j : ℕ) : ℝ := ∑ r ∈ Finset.Ico i j, g r
noncomputable def pI (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).1
noncomputable def pJ (PR : List (ℕ × ℕ)) (k : ℕ) : ℕ := (PR.getD k (0, 0)).2
noncomputable def InCell (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (g : ℕ → ℝ) : Prop :=
 (∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC) ∧
 ∀ k < PR.length, ((c.A.getD k 0 : ℕ) : ℝ) / SC ≤ gsum g (pI PR k) (pJ PR k) ∧
   gsum g (pI PR k) (pJ PR k) ≤ ((c.B.getD k 0 : ℕ) : ℝ) / SC
noncomputable def CovBy (Q : ℕ) (PR : List (ℕ × ℕ)) (P : (ℕ → ℝ) → Prop) (c : Cl) : Prop := ∀ g, InCell Q PR c g → P g
noncomputable def PRok (Q : ℕ) (PR : List (ℕ × ℕ)) : Prop := ∀ k < PR.length, pI PR k + 2 ≤ pJ PR k ∧ pJ PR k ≤ Q
instance (Q : ℕ) (PR : List (ℕ × ℕ)) : Decidable (PRok Q PR) := by unfold PRok; infer_instance
noncomputable def sumR (L : List ℕ) (i : ℕ) : ℕ → ℕ
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
noncomputable def imap (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → List ℕ
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
noncomputable def InBox (Q : ℕ) (c : Cl) (g : ℕ → ℝ) : Prop :=
 ∀ r < Q, ((c.L.getD r 0 : ℕ) : ℝ) / SC ≤ g r ∧ g r ≤ ((c.U.getD r 0 : ℕ) : ℝ) / SC
theorem sum_lo {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
   ((sumR c.L i n : ℕ) : ℝ) / SC ≤ gsum g i (i + n) := by
 rw [sumR_eq, gsum, Finset.sum_div]
 exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).1
theorem sum_hi {Q : ℕ} {c : Cl} {g : ℕ → ℝ} (hg : InBox Q c g) (i n : ℕ) (hn : i + n ≤ Q) :
   gsum g i (i + n) ≤ ((sumR c.U i n : ℕ) : ℝ) / SC := by
 rw [sumR_eq, gsum, Finset.sum_div]
 exact Finset.sum_le_sum fun r hr => (hg r (by simp at hr; omega)).2
noncomputable def fLe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmax (c.A.getD k 0) (sumR c.L (pI PR k) (pJ PR k - pI PR k))
noncomputable def fUe (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : ℕ := nmin (c.B.getD k 0) (sumR c.U (pI PR k) (pJ PR k - pI PR k))
noncomputable def femp (PR : List (ℕ × ℕ)) (c : Cl) (k : ℕ) : Bool := Nat.blt (fUe PR c k) (fLe PR c k)
noncomputable def ind (b : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 1 b
noncomputable def inr (r i j : ℕ) : Bool := Bool.rec (motive := fun _ => Bool) false (Nat.blt r j) (Nat.ble i r)
theorem ind_inr (r i j : ℕ) : ((ind (inr r i j) : ℕ) : ℝ) = if i ≤ r ∧ r < j then 1 else 0 := by
 unfold ind inr
 by_cases h1 : i ≤ r
 · rw [Nat.ble_eq_true_of_le h1]
   by_cases h2 : r < j
   · rw [show Nat.blt r j = true from Nat.blt_eq.mpr h2]; simp [h1, h2]
   · rw [show Nat.blt r j = false from Bool.eq_false_iff.mpr fun h => h2 (Nat.blt_eq.mp h)]; simp [h2]
 · rw [show Nat.ble i r = false from Bool.eq_false_iff.mpr fun h => h1 (Nat.le_of_ble_eq_true h)]; simp [h1]
noncomputable def MulOKg (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (P S : List ℕ) (Cp Cm : ℕ) : Prop :=
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
noncomputable def fsum (c : Cl) (P S : List ℕ) : ℕ → ℕ
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
noncomputable def forceT {α : Sort _} (a : ℕ) (k : ℕ → α) : α := Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) a
theorem forceT_eq {α : Sort _} (a : ℕ) (k : ℕ → α) : forceT a k = k a := by cases a <;> rfl
noncomputable def gptF (L U jj : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (forceR (Bool.rec (motive := fun _ => ℕ) 8 5 (Nat.beq (Nat.land (Nat.shiftRight jj 6) 1) 1)) fun gs =>
    forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 gs) 1)) gs) gs) fun ga =>
    forceR (Nat.shiftLeft (Nat.shiftRight U gs) gs) fun gb =>
    forceR (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) (Nat.land jj 63)) 5)) gs) gs) fun x =>
    Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) x gb (Nat.ble gb x)) ga (Nat.ble x ga))
   L (Nat.beq jj 33)
noncomputable def uc (L U : ℕ) : ℕ := nmax U (Nat.add L 1)
theorem le_uc (L U : ℕ) : U ≤ uc L U := le_nmax_left _ _
noncomputable def mvT (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ := mval top bk f L U (mwc k m) (mw1 k m) (mw2 k m) p r
noncomputable def mcpT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcp f L0 (mw1 k m) (mw2 k m) p r
noncomputable def mcnT (f : ℕ → ℕ) (L0 k m p r : ℕ) : ℕ := mcn f L0 (mw1 k m) (mw2 k m) p r
noncomputable def mslT (f : ℕ → ℕ) (k m p r : ℕ) : ℕ := msl f (mw1 k m) (mw2 k m) p r
noncomputable def mwT (k m : ℕ) : ℕ := Nat.add (mw1 k m) (mw2 k m)
noncomputable def mvK (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Nat.mul 1024 (lb top bk L U))
     (Nat.add (Nat.mul (Nat.sub 1024 m) (lo32 (f p))) (Nat.mul m (lo32 (f r)))) (Nat.beq k 3))
   (Nat.add (Nat.mul (Nat.sub 1024 m) (lb top bk L U)) (Nat.mul m (lo32 (f p)))) (Nat.beq k 2))
   (Nat.mul 1024 (lo32 (f p))) (Nat.beq k 1)
noncomputable def chg (f : ℕ → ℕ) (sg : Bool) (L0 l p : ℕ) : ℕ :=
 Nat.mul (Nat.mul l (Bool.rec (motive := fun _ => ℕ) (Nat.sub 2000000000 (hi32 (hi32 (f p)))) (Nat.sub (hi32 (hi32 (f p))) 2000000000) sg)) (Nat.sub p L0)
noncomputable def mcK (f : ℕ → ℕ) (sg : Bool) (L0 k m p r : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0
     (Nat.add (chg f sg L0 (Nat.sub 1024 m) p) (chg f sg L0 m r)) (Nat.beq k 3))
   (chg f sg L0 m p) (Nat.beq k 2))
   (chg f sg L0 1024 p) (Nat.beq k 1)
noncomputable def mslK (f : ℕ → ℕ) (k m p r : ℕ) : ℕ :=
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
noncomputable def tI (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).1
noncomputable def tJ (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.1
noncomputable def tA (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.1
noncomputable def tK (TS : List Term) (n : ℕ) : ℕ := (TS.getD n (0, 0, 0, 0)).2.2.2
noncomputable def isum (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (f i)) n
noncomputable def iall (f : ℕ → Bool) (n : ℕ) : Bool :=
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
noncomputable def eL (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (nmax (c.A.getD (tK TS n) 0) (sumR c.L (tI TS n) (tJ TS n - tI TS n)))
   (c.L.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
noncomputable def eU (TS : List Term) (c : Cl) (n : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (nmin (c.B.getD (tK TS n) 0) (sumR c.U (tI TS n) (tJ TS n - tI TS n)))
   (c.U.getD (tI TS n) 0) (Nat.beq (tJ TS n - tI TS n) 1)
noncomputable def eL0 (TS : List Term) (c : Cl) (n : ℕ) : ℕ := sumR c.L (tI TS n) (tJ TS n - tI TS n)
noncomputable def Ng (f : ℕ → ℕ) (bs : List ℕ) (TS FS : List Term) (P S : List ℕ) (r : ℕ) : ℕ :=
 Nat.sub (Nat.add (Nat.mul 2000000000 (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (mwT (tI FS n) (tJ FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (P.getD r 0))
   (Nat.add (Nat.add (Nat.mul 1024000000000 (bs.getD r 0)) (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (mslT f (tI FS n) (tJ FS n) (tA FS n) (tK FS n))) (inr r (tI TS n) (tJ TS n))) TS.length)) (S.getD r 0))
noncomputable def Fg (Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : ℝ :=
 ∑ r ∈ Finset.range Q, ((bs.getD r 0 : ℕ) : ℝ) * g r
   + ∑ n ∈ Finset.range TS.length, ((tA TS n : ℕ) : ℝ) * wfun (gsum g (tI TS n) (tJ TS n))
noncomputable def Pg (cN Q : ℕ) (bs : List ℕ) (TS : List Term) (g : ℕ → ℝ) : Prop := (cN : ℝ) ≤ Fg Q bs TS g ∨ g (Q - 1) < g 0
noncomputable def TSok (Q : ℕ) (PR : List (ℕ × ℕ)) (TS : List Term) : Prop :=
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
noncomputable def coverChk (cN aAdj : ℕ) : ℕ → ℕ → List (ℕ × ℕ × Bool) → Bool
 | pos, S, [] => decide (S ≤ pos)
 | pos, S, (a, b, cl) :: rest =>
     decide (a = pos) && decide (a ≤ b) && decide (b < KB)
       && (!cl || Nat.ble (cN * SW) (aAdj * CellN.WZ ⟨a * KB + b, 0⟩))
       && coverChk cN aAdj b S rest
noncomputable def badOf (cover : List (ℕ × ℕ × Bool)) : List (ℕ × ℕ) :=
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
noncomputable def rootCl (Q NC W : ℕ) (cov : List (List (ℕ × ℕ × Bool))) (idx : ℕ → ℕ) : Cl :=
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
noncomputable def sI (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s else pI PR (s - Q)
noncomputable def sJ (Q : ℕ) (PR : List (ℕ × ℕ)) (s : ℕ) : ℕ := if s < Q then s + 1 else pJ PR (s - Q)
noncomputable def sLo (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.L.getD s 0 else c.A.getD (s - Q) 0
noncomputable def sHi (Q : ℕ) (c : Cl) (s : ℕ) : ℕ := if s < Q then c.U.getD s 0 else c.B.getD (s - Q) 0
noncomputable def ClLen (Q n : ℕ) (c : Cl) : Prop := c.L.length = Q ∧ c.U.length = Q ∧ c.A.length = n ∧ c.B.length = n
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
noncomputable def matC (PR : List (ℕ × ℕ)) (c : Cl) : Cl :=
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
noncomputable def zpt (v c x lbv : ℕ) : Bool :=
 Nat.ble (Nat.add (Nat.mul v 32768) (Nat.mul (Nat.mul 10 (Nat.sub 2000000000 c)) x))
   (Nat.add (Nat.mul lbv 32768) (Nat.mul (Nat.mul 10 (Nat.sub c 2000000000)) x))
noncomputable def zpc (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (forceB (lb top bk x0 x1) fun lbv =>
     Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
       (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
   true (Nat.ble x1 x0)
noncomputable def zpe (a b n k : ℕ) : ℕ := Nat.add a (Nat.div (Nat.mul (Nat.sub b a) k) n)
noncomputable def zside (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 iall (fun k => zpc top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n
noncomputable def zsideF (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
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
noncomputable def TVal (f : ℕ → ℕ) (L U p : ℕ) : Prop :=
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
noncomputable def plenF (lb a : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 2 (Nat.add 16 lb) (Nat.beq a 3))
   (Nat.add 9 lb) (Nat.beq a 2)) 9 (Nat.beq a 1)
noncomputable def dec4F (lb w o L U : ℕ) (k : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ :=
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
noncomputable def PV (x v : ℕ) : Prop := (lo32 v : ℝ) / 10000000000 ≤ wfun ((x : ℝ) / SC) ∧ PS (hi32 v) ((x : ℝ) / SC)
theorem pv_zero (x : ℕ) : PV x 0 := by
 unfold PV; rw [lo32_zero, hi32_zero]
 exact ⟨by simp only [Nat.cast_zero, zero_div]; exact wfun_nonneg _, PS_zero _⟩
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
noncomputable def slT (Q : ℕ) (SL : List ℕ) (a b : ℕ) : ℕ := SL.getD (a * (Q + 1) + b) 0
noncomputable def SLok (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Prop :=
 ∀ a < Q + 1, ∀ b < Q + 1, a < b →
   slT Q SL a b < Q + PR.length ∧ sI Q PR (slT Q SL a b) = a ∧ sJ Q PR (slT Q SL a b) = b
instance (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ) : Decidable (SLok Q PR SL) := by unfold SLok; infer_instance
noncomputable def ov : Option ℕ → ℕ
 | none => 0
 | some a => a
noncomputable def legP (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
 Bool.rec (motive := fun _ => Option ℕ) none (some (sHi Q c (slT Q SL x y))) (Nat.blt x y)
noncomputable def legN (Q : ℕ) (SL : List ℕ) (c : Cl) (x y : ℕ) : Option ℕ :=
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
noncomputable def bdist (s z : ℕ) : ℕ := Nat.add (Nat.sub (Nat.add z z) s) (Nat.sub s (Nat.add z z))
noncomputable def bcutL (BND : List ℕ) (bm lo hi : ℕ) : ℕ :=
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
noncomputable def lbDrF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 6)) fun k =>
       forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov2 top bk k ib g)
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
theorem lbDrF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbDrF top bk lo hi = lbDr top bk lo hi := by
 simp only [lbDrF, lbDr, forceR_eq]
noncomputable def treadUF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD (rgB R k) U) 0 (Nat.ble U (rgB R k))
noncomputable def treadDF (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) : ℕ :=
 forceR (Nat.shiftRight (Nat.add p 16384) 15) fun k =>
   Bool.rec (motive := fun _ => ℕ) (lbDrF tD bD L (rgA R k)) 0 (Nat.ble (rgA R k) L)
theorem treadUF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (U p : ℕ) :
   treadUF R tD bD U p = treadU R tD bD U p := by
 simp only [treadUF, treadU, lbDrF_eq]
theorem treadDF_eq (R : ℕ × ℕ × List (List ℕ)) (tD : ℕ) (bD : ℕ → ℕ) (L p : ℕ) :
   treadDF R tD bD L p = treadD R tD bD L p := by
 simp only [treadDF, treadD, lbDrF_eq]
noncomputable def lbF (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
 Bool.rec (motive := fun _ => ℕ)
   (Bool.rec (motive := fun _ => ℕ)
     (forceR (blen (Nat.shiftRight (Nat.sub hi lo) 5)) fun k =>
       forceR (Nat.shiftRight (Nat.sub hi 1) k) fun ib => forceR (Nat.shiftRight lo k) fun g => dcov top bk k ib g)
     0 (Nat.ble 524289 hi))
   0 (Nat.ble hi lo)
theorem lbF_eq (top : ℕ) (bk : ℕ → ℕ) (lo hi : ℕ) : lbF top bk lo hi = lb top bk lo hi := by
 simp only [lbF, lb, forceR_eq]
noncomputable def zpcF (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) : Bool :=
 Bool.rec (motive := fun _ => Bool)
   (forceB (lbF top bk x0 x1) fun lbv =>
     Bool.rec (motive := fun _ => Bool) (zpt v c (Nat.sub p x0) lbv && zpt v c (Nat.sub p x1) lbv)
       (zpt v c (Nat.sub x0 p) lbv && zpt v c (Nat.sub x1 p) lbv) right)
   true (Nat.ble x1 x0)
noncomputable def zsideG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 iall (fun k => zpcF top bk v c p (zpe a b n k) (zpe a b n (Nat.add k 1)) right) n
noncomputable def zsideFG (top : ℕ) (bk : ℕ → ℕ) (v c p a b n : ℕ) (right : Bool) : Bool :=
 zsideG top bk v c p a b 1 right || zsideG top bk v c p a b 2 right || zsideG top bk v c p a b n right
theorem zpcF_eq (top : ℕ) (bk : ℕ → ℕ) (v c p x0 x1 : ℕ) (right : Bool) :
   zpcF top bk v c p x0 x1 right = zpc top bk v c p x0 x1 right := by
 simp only [zpcF, zpc, lbF_eq]
end AMW.Cert.PyrD
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
noncomputable def mvKF (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (L U k m p r : ℕ) : ℕ :=
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
noncomputable def rup (U j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight (Nat.add U (Nat.sub (Nat.shiftLeft 1 j) 1)) j) j
noncomputable def rdn (L j : ℕ) : ℕ := Nat.shiftLeft (Nat.shiftRight L j) j
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
noncomputable def tcheckZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
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
noncomputable def tcheckPZC (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh L U p X EU ED : ℕ) :
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
noncomputable def mcheckGX (ok : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (top : ℕ) (bk : ℕ → ℕ) (f : ℕ → ℕ) (Q : ℕ) (bs : List ℕ)
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
noncomputable def BB : ℕ := 4398046511104
/-- twice the bias -/
noncomputable def TB : ℕ := 8796093022208

theorem TB_eq : (TB : ℝ) / SC = (BB : ℝ) / SC + (BB : ℝ) / SC := by
  rw [← add_div]; norm_num [TB, BB]

/-- `X` bounds the column through `s` and `Y` the row: `x_s − x_x ≤ X_x − BB` and `x_x − x_s ≤ Y_x − BB` -/
noncomputable def ColOK (Q : ℕ) (g : ℕ → ℝ) (s : ℕ) (X Y : List ℕ) : Prop :=
  ∀ x ≤ Q, gsum g 0 s - gsum g 0 x ≤ ((X.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC ∧
    gsum g 0 x - gsum g 0 s ≤ ((Y.getD x 0 : ℕ) : ℝ) / SC - (BB : ℝ) / SC

/-- the closure update through the column `X` and the row `Y` -/
noncomputable def cuB (Q : ℕ) (PR : List (ℕ × ℕ)) (c : Cl) (X Y : List ℕ) : Cl :=
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
noncomputable def dE (Q : ℕ) (SL : List ℕ) (c : Cl) (E a b : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ)
    (Bool.rec (motive := fun _ => ℕ) (Nat.sub E (sLo Q c (slT Q SL b a))) E (Nat.beq a b))
    (Nat.add E (sHi Q c (slT Q SL a b))) (Nat.blt a b)

/-- the column through `s` -/
noncomputable def colB (Q : ℕ) (SL : List ℕ) (c : Cl) (s : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c BB x s)

/-- the row from `t`, with the base `E` (`BB` plus the edge's weight) -/
noncomputable def rowB (Q : ℕ) (SL : List ℕ) (c : Cl) (E t : ℕ) : List ℕ := (List.range (Q + 1)).map (fun x => dE Q SL c E t x)

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
noncomputable def trip (v : ℕ) : ℕ := Nat.land v 79228162514264337593543950335
/-- the interval's lower end (bits 96–119) -/
noncomputable def ivA (v : ℕ) : ℕ := Nat.land (Nat.shiftRight v 96) 16777215
/-- the interval's upper end (bits 120–); `0` means no interval -/
noncomputable def ivB (v : ℕ) : ℕ := Nat.shiftRight v 120
/-- the point function the decoders see -/
noncomputable def tf (g : ℕ → ℕ) (x : ℕ) : ℕ := trip (g x)

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
noncomputable def PVI (x v : ℕ) : Prop := PV x (trip v) ∧ (ivB v ≠ 0 → TVal (fun _ => trip v) (ivA v) (ivB v) x)

theorem pvi_zero (x : ℕ) : PVI x 0 := by
  refine ⟨?_, fun h => absurd ivB_zero h⟩
  rw [trip_zero]; exact pv_zero x


/-- a point function equal to `w` at `p` and `0` elsewhere -/
noncomputable def fpt (p w y : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) 0 w (Nat.beq y p)
theorem fpt_self (p w : ℕ) : fpt p w p = w := by simp [fpt]
theorem fpt_ptf {p w : ℕ} (h : PV p w) : PTF (fpt p w) := by
  intro y
  unfold fpt
  cases hb : Nat.beq y p
  · exact pv_zero y
  · have hy : y = p := by simpa using hb
    subst hy; exact h

/-- the one-time check of a point word's interval: none, or the coarse-first tangent check on it -/
noncomputable def ivOk (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh x v : ℕ) : Bool :=
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
noncomputable def ivIn (v L U p : ℕ) : Bool :=
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
noncomputable def mokI (g : ℕ → ℕ) (L U k m p r : ℕ) : Bool :=
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
-- SWAP BEGIN certificate: instance + data + full cert + RiemannFail (W8, W8_adm, W8_B, cert_AM)
/- Mechanical extraction of attempt016 at commit 296f7bb9c4e01b0c97554cf76af91ed99a410e8d,
   original physical lines 22795-23023; mathematical body retained byte-for-byte.
   Full original attribution retained above. Imports/global options and, where
   necessary, balanced closing ends are the only added commands. Source-only;
   no new compilation or acceptance claim. Original SHA256 5000dfb504e4cba831b3a7976974849f7574e2d7384a14f974b4a8bb02de2945.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace AMW.Cert.PC9QB6M
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
-- Modified by the GP-4 session (rhajp): window s1R (cAMn, H, window tables, pvCheck at 128 cells and dependent literals), nine-point weights, floor, tangent table, cover and walks regenerated; κ and the literals above were the earlier file's.
noncomputable def cN : ℕ := 893616123055294719
noncomputable def SIG : ℕ := 1562500000000000000000000000
noncomputable def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 8)]
theorem hPR : PRok 8 PR := by decide
noncomputable def BS : List ℕ := [28195867368000000, 50516979727000000, 69185101351000000, 80158024056000000, 80158024056000000, 69185101351000000, 50516979727000000, 28195867368000000]
noncomputable def TS : List Term := [(0, 1, 12145025938708000000, 0), (0, 3, 8651269219434000000, 1), (0, 4, 17776096184552000000, 2), (0, 5, 36889575523970000000, 3), (0, 6, 90239673332399000000, 4), (0, 7, 100000000000000000000, 5), (0, 8, 200000000000000000000, 6), (1, 2, 22223820732794000000, 0), (1, 3, 21042948716829000000, 7), (1, 4, 41416939206756000000, 8), (1, 5, 46995446251313000000, 9), (1, 6, 63110424476029000000, 10), (1, 7, 19520653335201000000, 11), (1, 8, 100000000000000000000, 12), (2, 3, 31202320231433000000, 0), (2, 4, 47970464688707000000, 13), (2, 5, 49931791573808000000, 14), (2, 6, 70456915128268000000, 15), (2, 7, 63110424476029000000, 16), (2, 8, 90239673332399000000, 17), (3, 4, 34428833097063000000, 0), (3, 5, 61973173188925000000, 18), (3, 6, 49931791573808000000, 19), (3, 7, 46995446251313000000, 20), (3, 8, 36889575523970000000, 21), (4, 5, 34428833097063000000, 0), (4, 6, 47970464688707000000, 22), (4, 7, 41416939206756000000, 23), (4, 8, 17776096184552000000, 24), (5, 6, 31202320231433000000, 0), (5, 7, 21042948716829000000, 25), (5, 8, 8651269219434000000, 26), (6, 7, 22223820732794000000, 0), (7, 8, 12145025938708000000, 0)]
theorem hTS : TSok 8 PR TS := by decide
noncomputable def SL : List ℕ := [0, 0, 8, 9, 10, 11, 12, 13, 14, 0, 0, 1, 15, 16, 17, 18, 19, 20, 0, 0, 0, 2, 21, 22, 23, 24, 25, 0, 0, 0, 0, 3, 26, 27, 28, 29, 0, 0, 0, 0, 0, 4, 30, 31, 32, 0, 0, 0, 0, 0, 0, 5, 33, 34, 0, 0, 0, 0, 0, 0, 0, 6, 35, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem hSL : SLok 8 PR SL := by decide
noncomputable def BND : List ℕ := [16384, 40384, 56768, 73728, 89920, 106240, 122304, 138496, 155136, 171456, 187776, 203904, 220224, 236480, 253120, 269440, 285696, 301888, 318464, 334912, 351744, 368320, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]
noncomputable def SA : ℕ := 100000000000000000000
noncomputable def G (g0 g1 g2 g3 g4 g5 g6 g7 : ℝ) : ℝ :=
  (28195867368000000 / (SA:ℝ)) * g0 + (50516979727000000 / (SA:ℝ)) * g1 + (69185101351000000 / (SA:ℝ)) * g2 + (80158024056000000 / (SA:ℝ)) * g3 + (80158024056000000 / (SA:ℝ)) * g4 + (69185101351000000 / (SA:ℝ)) * g5 + (50516979727000000 / (SA:ℝ)) * g6 + (28195867368000000 / (SA:ℝ)) * g7
    + (12145025938708000000 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (8651269219434000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (17776096184552000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (36889575523970000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (90239673332399000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (100000000000000000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (200000000000000000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7) + (22223820732794000000 / (SA:ℝ)) * wfun (g1) + (21042948716829000000 / (SA:ℝ)) * wfun (g1 + g2) + (41416939206756000000 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (46995446251313000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (63110424476029000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (19520653335201000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (100000000000000000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6 + g7) + (31202320231433000000 / (SA:ℝ)) * wfun (g2) + (47970464688707000000 / (SA:ℝ)) * wfun (g2 + g3) + (49931791573808000000 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (70456915128268000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (63110424476029000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (90239673332399000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6 + g7) + (34428833097063000000 / (SA:ℝ)) * wfun (g3) + (61973173188925000000 / (SA:ℝ)) * wfun (g3 + g4) + (49931791573808000000 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (46995446251313000000 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (36889575523970000000 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6 + g7) + (34428833097063000000 / (SA:ℝ)) * wfun (g4) + (47970464688707000000 / (SA:ℝ)) * wfun (g4 + g5) + (41416939206756000000 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (17776096184552000000 / (SA:ℝ)) * wfun (g4 + g5 + g6 + g7) + (31202320231433000000 / (SA:ℝ)) * wfun (g5) + (21042948716829000000 / (SA:ℝ)) * wfun (g5 + g6) + (8651269219434000000 / (SA:ℝ)) * wfun (g5 + g6 + g7) + (22223820732794000000 / (SA:ℝ)) * wfun (g6) + (0 / (SA:ℝ)) * wfun (g6 + g7) + (12145025938708000000 / (SA:ℝ)) * wfun (g7)
theorem Fg_G (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : Fg 8 BS TS (fun r => [x0, x1, x2, x3, x4, x5, x6, x7].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 x4 x5 x6 x7 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring
abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M : ℕ)
noncomputable def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3, s.l4, s.l5, s.l6, s.l7], [s.u0, s.u1, s.u2, s.u3, s.u4, s.u5, s.u6, s.u7],
   [s.A02, s.A03, s.A04, s.A05, s.A06, s.A07, s.A08, s.A13, s.A14, s.A15, s.A16, s.A17, s.A18, s.A24, s.A25, s.A26, s.A27, s.A28, s.A35, s.A36, s.A37, s.A38, s.A46, s.A47, s.A48, s.A57, s.A58, s.A68], [s.B02, s.B03, s.B04, s.B05, s.B06, s.B07, s.B08, s.B13, s.B14, s.B15, s.B16, s.B17, s.B18, s.B24, s.B25, s.B26, s.B27, s.B28, s.B35, s.B36, s.B37, s.B38, s.B46, s.B47, s.B48, s.B57, s.B58, s.B68]⟩
noncomputable def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.L.getD 4 0, c.U.getD 4 0, c.L.getD 5 0, c.U.getD 5 0, c.L.getD 6 0, c.U.getD 6 0, c.L.getD 7 0, c.U.getD 7 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, c.A.getD 6 0, c.B.getD 6 0, c.A.getD 7 0, c.B.getD 7 0, c.A.getD 8 0, c.B.getD 8 0, c.A.getD 9 0, c.B.getD 9 0, c.A.getD 10 0, c.B.getD 10 0, c.A.getD 11 0, c.B.getD 11 0, c.A.getD 12 0, c.B.getD 12 0, c.A.getD 13 0, c.B.getD 13 0, c.A.getD 14 0, c.B.getD 14 0, c.A.getD 15 0, c.B.getD 15 0, c.A.getD 16 0, c.B.getD 16 0, c.A.getD 17 0, c.B.getD 17 0, c.A.getD 18 0, c.B.getD 18 0, c.A.getD 19 0, c.B.getD 19 0, c.A.getD 20 0, c.B.getD 20 0, c.A.getD 21 0, c.B.getD 21 0, c.A.getD 22 0, c.B.getD 22 0, c.A.getD 23 0, c.B.getD 23 0, c.A.getD 24 0, c.B.getD 24 0, c.A.getD 25 0, c.B.getD 25 0, c.A.getD 26 0, c.B.getD 26 0, c.A.getD 27 0, c.B.getD 27 0, m⟩
theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28) (h4 : c.B.length = 28) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]
abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
noncomputable def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M
noncomputable def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
noncomputable def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
noncomputable def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h
theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28)
    (h4 : c.B.length = 28) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h
noncomputable def cuH (k : ST) (x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  k (nmax a (Nat.sub 8796093022208 (Nat.add x1 y0)))
    (nmin b (Nat.sub (Nat.add x0 y1) 8796093022208))
    (nmax c (Nat.sub 8796093022208 (Nat.add x2 y1)))
    (nmin d (Nat.sub (Nat.add x1 y2) 8796093022208))
    (nmax e (Nat.sub 8796093022208 (Nat.add x3 y2)))
    (nmin f (Nat.sub (Nat.add x2 y3) 8796093022208))
    (nmax g (Nat.sub 8796093022208 (Nat.add x4 y3)))
    (nmin h (Nat.sub (Nat.add x3 y4) 8796093022208))
    (nmax i (Nat.sub 8796093022208 (Nat.add x5 y4)))
    (nmin j (Nat.sub (Nat.add x4 y5) 8796093022208))
    (nmax l (Nat.sub 8796093022208 (Nat.add x6 y5)))
    (nmin m (Nat.sub (Nat.add x5 y6) 8796093022208))
    (nmax n (Nat.sub 8796093022208 (Nat.add x7 y6)))
    (nmin o (Nat.sub (Nat.add x6 y7) 8796093022208))
    (nmax r (Nat.sub 8796093022208 (Nat.add x8 y7)))
    (nmin s (Nat.sub (Nat.add x7 y8) 8796093022208))
    (nmax t (Nat.sub 8796093022208 (Nat.add x2 y0)))
    (nmin u (Nat.sub (Nat.add x0 y2) 8796093022208))
    (nmax v (Nat.sub 8796093022208 (Nat.add x3 y0)))
    (nmin w (Nat.sub (Nat.add x0 y3) 8796093022208))
    (nmax x (Nat.sub 8796093022208 (Nat.add x4 y0)))
    (nmin y (Nat.sub (Nat.add x0 y4) 8796093022208))
    (nmax z (Nat.sub 8796093022208 (Nat.add x5 y0)))
    (nmin A (Nat.sub (Nat.add x0 y5) 8796093022208))
    (nmax B (Nat.sub 8796093022208 (Nat.add x6 y0)))
    (nmin C (Nat.sub (Nat.add x0 y6) 8796093022208))
    (nmax D (Nat.sub 8796093022208 (Nat.add x7 y0)))
    (nmin E (Nat.sub (Nat.add x0 y7) 8796093022208))
    (nmax F (Nat.sub 8796093022208 (Nat.add x8 y0)))
    (nmin G (Nat.sub (Nat.add x0 y8) 8796093022208))
    (nmax H (Nat.sub 8796093022208 (Nat.add x3 y1)))
    (nmin I (Nat.sub (Nat.add x1 y3) 8796093022208))
    (nmax J (Nat.sub 8796093022208 (Nat.add x4 y1)))
    (nmin K (Nat.sub (Nat.add x1 y4) 8796093022208))
    (nmax L (Nat.sub 8796093022208 (Nat.add x5 y1)))
    (nmin M (Nat.sub (Nat.add x1 y5) 8796093022208))
    (nmax N (Nat.sub 8796093022208 (Nat.add x6 y1)))
    (nmin O (Nat.sub (Nat.add x1 y6) 8796093022208))
    (nmax P (Nat.sub 8796093022208 (Nat.add x7 y1)))
    (nmin Q (Nat.sub (Nat.add x1 y7) 8796093022208))
    (nmax R (Nat.sub 8796093022208 (Nat.add x8 y1)))
    (nmin S (Nat.sub (Nat.add x1 y8) 8796093022208))
    (nmax T (Nat.sub 8796093022208 (Nat.add x4 y2)))
    (nmin U (Nat.sub (Nat.add x2 y4) 8796093022208))
    (nmax V (Nat.sub 8796093022208 (Nat.add x5 y2)))
    (nmin W (Nat.sub (Nat.add x2 y5) 8796093022208))
    (nmax X (Nat.sub 8796093022208 (Nat.add x6 y2)))
    (nmin Y (Nat.sub (Nat.add x2 y6) 8796093022208))
    (nmax Z (Nat.sub 8796093022208 (Nat.add x7 y2)))
    (nmin aa (Nat.sub (Nat.add x2 y7) 8796093022208))
    (nmax ab (Nat.sub 8796093022208 (Nat.add x8 y2)))
    (nmin ac (Nat.sub (Nat.add x2 y8) 8796093022208))
    (nmax ad (Nat.sub 8796093022208 (Nat.add x5 y3)))
    (nmin ae (Nat.sub (Nat.add x3 y5) 8796093022208))
    (nmax af (Nat.sub 8796093022208 (Nat.add x6 y3)))
    (nmin ag (Nat.sub (Nat.add x3 y6) 8796093022208))
    (nmax ah (Nat.sub 8796093022208 (Nat.add x7 y3)))
    (nmin ai (Nat.sub (Nat.add x3 y7) 8796093022208))
    (nmax aj (Nat.sub 8796093022208 (Nat.add x8 y3)))
    (nmin al (Nat.sub (Nat.add x3 y8) 8796093022208))
    (nmax am (Nat.sub 8796093022208 (Nat.add x6 y4)))
    (nmin an (Nat.sub (Nat.add x4 y6) 8796093022208))
    (nmax ao (Nat.sub 8796093022208 (Nat.add x7 y4)))
    (nmin ar (Nat.sub (Nat.add x4 y7) 8796093022208))
    (nmax au (Nat.sub 8796093022208 (Nat.add x8 y4)))
    (nmin av (Nat.sub (Nat.add x4 y8) 8796093022208))
    (nmax aw (Nat.sub 8796093022208 (Nat.add x7 y5)))
    (nmin ax (Nat.sub (Nat.add x5 y7) 8796093022208))
    (nmax ay (Nat.sub 8796093022208 (Nat.add x8 y5)))
    (nmin az (Nat.sub (Nat.add x5 y8) 8796093022208))
    (nmax ba (Nat.sub 8796093022208 (Nat.add x8 y6)))
    (nmin bb (Nat.sub (Nat.add x6 y8) 8796093022208))
    bc
noncomputable def cuL (k : ST) (X Y : List ℕ) (s : St) : ℕ :=
  cuH k (X.getD 0 0) (X.getD 1 0) (X.getD 2 0) (X.getD 3 0) (X.getD 4 0) (X.getD 5 0) (X.getD 6 0) (X.getD 7 0) (X.getD 8 0) (Y.getD 0 0) (Y.getD 1 0) (Y.getD 2 0) (Y.getD 3 0) (Y.getD 4 0) (Y.getD 5 0) (Y.getD 6 0) (Y.getD 7 0) (Y.getD 8 0)
    s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M
theorem cuL_eq (k : ST) (X Y : List ℕ) (s : St) : cuL k X Y s = U k (ofCl (cuB 8 PR (toCl s) X Y) s.M) := by
  simp only [cuL, U, ofCl, cuB, toCl, PR, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, pI, pJ]
  rfl
theorem cuH_ok {k : ST} (hk : CovK k) (X Y : List ℕ) (s : St) (h : cuL k X Y s ≠ 0) :
    Covered (cuB 8 PR (toCl s) X Y) :=
  ofCl_ok hk (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR]) (by simp [cuB, PR]) (m := s.M) (by rw [← cuL_eq]; exact h)
theorem spH_ok {ih : WF} (hih : WalkOK ih) {pos : ℕ} (i j : ℕ) (hij : i < j) (hj : j ≤ 8) {s : St} {q : ℕ}
    (h : Bool.rec (motive := fun _ => ℕ)
      (cuL (ih (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s)) (colB 8 SL (toCl s) j) (rowB 8 SL (toCl s) (Nat.sub BB q) i) s) 0
      (Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0) ≠ 0) : Covered (toCl s) := by
  have hc := cov_splitB (P := Pg cN 8 BS TS) (c := toCl s) hSL hPR hij hj q
  cases hp : Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0
  · rw [hp] at h
    exact hc (cuH_ok (hih _) _ _ s fun h0 => by rw [h0] at hp; exact absurd hp (by decide)) (cuH_ok (hih _) _ _ s h)
  · rw [hp] at h; exact absurd rfl h
noncomputable def colK0 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F)
noncomputable def colK1 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R)
noncomputable def colK2 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab)
noncomputable def colK3 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj)
noncomputable def colK4 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au)
noncomputable def colK5 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay)
noncomputable def colK6 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba)
noncomputable def colK7 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r)
noncomputable def colK8 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb
noncomputable def rowK0 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk ee (Nat.add ee b) (Nat.add ee u) (Nat.add ee w) (Nat.add ee y) (Nat.add ee A) (Nat.add ee C) (Nat.add ee E) (Nat.add ee G)
noncomputable def rowK1 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee a) ee (Nat.add ee d) (Nat.add ee I) (Nat.add ee K) (Nat.add ee M) (Nat.add ee O) (Nat.add ee Q) (Nat.add ee S)
noncomputable def rowK2 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee t) (Nat.sub ee c) ee (Nat.add ee f) (Nat.add ee U) (Nat.add ee W) (Nat.add ee Y) (Nat.add ee aa) (Nat.add ee ac)
noncomputable def rowK3 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee v) (Nat.sub ee H) (Nat.sub ee e) ee (Nat.add ee h) (Nat.add ee ae) (Nat.add ee ag) (Nat.add ee ai) (Nat.add ee al)
noncomputable def rowK4 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee x) (Nat.sub ee J) (Nat.sub ee T) (Nat.sub ee g) ee (Nat.add ee j) (Nat.add ee an) (Nat.add ee ar) (Nat.add ee av)
noncomputable def rowK5 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee z) (Nat.sub ee L) (Nat.sub ee V) (Nat.sub ee ad) (Nat.sub ee i) ee (Nat.add ee m) (Nat.add ee ax) (Nat.add ee az)
noncomputable def rowK6 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee B) (Nat.sub ee N) (Nat.sub ee X) (Nat.sub ee af) (Nat.sub ee am) (Nat.sub ee l) ee (Nat.add ee o) (Nat.add ee bb)
noncomputable def rowK7 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee D) (Nat.sub ee P) (Nat.sub ee Z) (Nat.sub ee ah) (Nat.sub ee ao) (Nat.sub ee aw) (Nat.sub ee n) ee (Nat.add ee s)
noncomputable def rowK8 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee F) (Nat.sub ee R) (Nat.sub ee ab) (Nat.sub ee aj) (Nat.sub ee au) (Nat.sub ee ay) (Nat.sub ee ba) (Nat.sub ee r) ee
noncomputable def splG (ih : WF) (pos : ℕ) (qs : ST) (cA : (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) (rA : ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) (cB : (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST)
    (rB : ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) : ST := fun a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc =>
  let q := qs a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc; let qe := Nat.add 4398046511104 q; let qf := Nat.sub 4398046511104 q;
  let pp := cA (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => rA qe (fun y0 y1 y2 y3 y4 y5 y6 y7 y8 => cuH (ih pos) x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cB (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => rB qf (fun y0 y1 y2 y3 y4 y5 y6 y7 y8 => cuH (ih pp) x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq pp 0)
noncomputable def qs_gsplit0 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add a b) 1) (bcutL BND 64 a b) (Nat.beq md 1)
noncomputable def gsplit0 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit0 md) colK0 rowK1 colK1 rowK0
noncomputable def qs_gsplit1 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add c d) 1) (bcutL BND 64 c d) (Nat.beq md 1)
noncomputable def gsplit1 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit1 md) colK1 rowK2 colK2 rowK1
noncomputable def qs_gsplit2 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add e f) 1) (bcutL BND 64 e f) (Nat.beq md 1)
noncomputable def gsplit2 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit2 md) colK2 rowK3 colK3 rowK2
noncomputable def qs_gsplit3 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add g h) 1) (bcutL BND 64 g h) (Nat.beq md 1)
noncomputable def gsplit3 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit3 md) colK3 rowK4 colK4 rowK3
noncomputable def qs_gsplit4 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add i j) 1) (bcutL BND 64 i j) (Nat.beq md 1)
noncomputable def gsplit4 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit4 md) colK4 rowK5 colK5 rowK4
noncomputable def qs_gsplit5 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add l m) 1) (bcutL BND 64 l m) (Nat.beq md 1)
noncomputable def gsplit5 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit5 md) colK5 rowK6 colK6 rowK5
noncomputable def qs_gsplit6 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add n o) 1) (bcutL BND 64 n o) (Nat.beq md 1)
noncomputable def gsplit6 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit6 md) colK6 rowK7 colK7 rowK6
noncomputable def qs_gsplit7 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add r s) 1) (bcutL BND 64 r s) (Nat.beq md 1)
noncomputable def gsplit7 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit7 md) colK7 rowK8 colK8 rowK7
noncomputable def qs_ssplit02 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add t u) 1) (bcutL BND 64 t u) (Nat.beq md 1)
noncomputable def ssplit02 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit02 md) colK0 rowK2 colK2 rowK0
noncomputable def qs_ssplit03 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add v w) 1) (bcutL BND 64 v w) (Nat.beq md 1)
noncomputable def ssplit03 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit03 md) colK0 rowK3 colK3 rowK0
noncomputable def qs_ssplit04 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add x y) 1) (bcutL BND 64 x y) (Nat.beq md 1)
noncomputable def ssplit04 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit04 md) colK0 rowK4 colK4 rowK0
noncomputable def qs_ssplit05 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add z A) 1) (bcutL BND 64 z A) (Nat.beq md 1)
noncomputable def ssplit05 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit05 md) colK0 rowK5 colK5 rowK0
noncomputable def qs_ssplit06 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add B C) 1) (bcutL BND 64 B C) (Nat.beq md 1)
noncomputable def ssplit06 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit06 md) colK0 rowK6 colK6 rowK0
noncomputable def qs_ssplit07 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add D E) 1) (bcutL BND 64 D E) (Nat.beq md 1)
noncomputable def ssplit07 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit07 md) colK0 rowK7 colK7 rowK0
noncomputable def qs_ssplit08 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add F G) 1) (bcutL BND 64 F G) (Nat.beq md 1)
noncomputable def ssplit08 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit08 md) colK0 rowK8 colK8 rowK0
noncomputable def qs_ssplit13 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add H I) 1) (bcutL BND 64 H I) (Nat.beq md 1)
noncomputable def ssplit13 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit13 md) colK1 rowK3 colK3 rowK1
noncomputable def qs_ssplit14 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add J K) 1) (bcutL BND 64 J K) (Nat.beq md 1)
noncomputable def ssplit14 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit14 md) colK1 rowK4 colK4 rowK1
noncomputable def qs_ssplit15 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add L M) 1) (bcutL BND 64 L M) (Nat.beq md 1)
noncomputable def ssplit15 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit15 md) colK1 rowK5 colK5 rowK1
noncomputable def qs_ssplit16 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add N O) 1) (bcutL BND 64 N O) (Nat.beq md 1)
noncomputable def ssplit16 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit16 md) colK1 rowK6 colK6 rowK1
noncomputable def qs_ssplit17 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add P Q) 1) (bcutL BND 64 P Q) (Nat.beq md 1)
noncomputable def ssplit17 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit17 md) colK1 rowK7 colK7 rowK1
noncomputable def qs_ssplit18 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add R S) 1) (bcutL BND 64 R S) (Nat.beq md 1)
noncomputable def ssplit18 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit18 md) colK1 rowK8 colK8 rowK1
noncomputable def qs_ssplit24 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add T U) 1) (bcutL BND 64 T U) (Nat.beq md 1)
noncomputable def ssplit24 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit24 md) colK2 rowK4 colK4 rowK2
noncomputable def qs_ssplit25 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add V W) 1) (bcutL BND 64 V W) (Nat.beq md 1)
noncomputable def ssplit25 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit25 md) colK2 rowK5 colK5 rowK2
noncomputable def qs_ssplit26 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add X Y) 1) (bcutL BND 64 X Y) (Nat.beq md 1)
noncomputable def ssplit26 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit26 md) colK2 rowK6 colK6 rowK2
noncomputable def qs_ssplit27 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add Z aa) 1) (bcutL BND 64 Z aa) (Nat.beq md 1)
noncomputable def ssplit27 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit27 md) colK2 rowK7 colK7 rowK2
noncomputable def qs_ssplit28 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ab ac) 1) (bcutL BND 64 ab ac) (Nat.beq md 1)
noncomputable def ssplit28 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit28 md) colK2 rowK8 colK8 rowK2
noncomputable def qs_ssplit35 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ad ae) 1) (bcutL BND 64 ad ae) (Nat.beq md 1)
noncomputable def ssplit35 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit35 md) colK3 rowK5 colK5 rowK3
noncomputable def qs_ssplit36 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add af ag) 1) (bcutL BND 64 af ag) (Nat.beq md 1)
noncomputable def ssplit36 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit36 md) colK3 rowK6 colK6 rowK3
noncomputable def qs_ssplit37 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ah ai) 1) (bcutL BND 64 ah ai) (Nat.beq md 1)
noncomputable def ssplit37 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit37 md) colK3 rowK7 colK7 rowK3
noncomputable def qs_ssplit38 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aj al) 1) (bcutL BND 64 aj al) (Nat.beq md 1)
noncomputable def ssplit38 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit38 md) colK3 rowK8 colK8 rowK3
noncomputable def qs_ssplit46 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add am an) 1) (bcutL BND 64 am an) (Nat.beq md 1)
noncomputable def ssplit46 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit46 md) colK4 rowK6 colK6 rowK4
noncomputable def qs_ssplit47 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ao ar) 1) (bcutL BND 64 ao ar) (Nat.beq md 1)
noncomputable def ssplit47 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit47 md) colK4 rowK7 colK7 rowK4
noncomputable def qs_ssplit48 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add au av) 1) (bcutL BND 64 au av) (Nat.beq md 1)
noncomputable def ssplit48 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit48 md) colK4 rowK8 colK8 rowK4
noncomputable def qs_ssplit57 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aw ax) 1) (bcutL BND 64 aw ax) (Nat.beq md 1)
noncomputable def ssplit57 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit57 md) colK5 rowK7 colK7 rowK5
noncomputable def qs_ssplit58 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ay az) 1) (bcutL BND 64 ay az) (Nat.beq md 1)
noncomputable def ssplit58 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit58 md) colK5 rowK8 colK8 rowK5
noncomputable def qs_ssplit68 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ba bb) 1) (bcutL BND 64 ba bb) (Nat.beq md 1)
noncomputable def ssplit68 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit68 md) colK6 rowK8 colK8 rowK6
section
variable {ih : WF} (hih : WalkOK ih) (md pos : ℕ)
include hih
theorem gsplit0_ok : CovK (gsplit0 ih md pos) := fun s h => spH_ok hih 0 1 (by decide) (by decide) (s := s) h
theorem gsplit1_ok : CovK (gsplit1 ih md pos) := fun s h => spH_ok hih 1 2 (by decide) (by decide) (s := s) h
theorem gsplit2_ok : CovK (gsplit2 ih md pos) := fun s h => spH_ok hih 2 3 (by decide) (by decide) (s := s) h
theorem gsplit3_ok : CovK (gsplit3 ih md pos) := fun s h => spH_ok hih 3 4 (by decide) (by decide) (s := s) h
theorem gsplit4_ok : CovK (gsplit4 ih md pos) := fun s h => spH_ok hih 4 5 (by decide) (by decide) (s := s) h
theorem gsplit5_ok : CovK (gsplit5 ih md pos) := fun s h => spH_ok hih 5 6 (by decide) (by decide) (s := s) h
theorem gsplit6_ok : CovK (gsplit6 ih md pos) := fun s h => spH_ok hih 6 7 (by decide) (by decide) (s := s) h
theorem gsplit7_ok : CovK (gsplit7 ih md pos) := fun s h => spH_ok hih 7 8 (by decide) (by decide) (s := s) h
theorem ssplit02_ok : CovK (ssplit02 ih md pos) := fun s h => spH_ok hih 0 2 (by decide) (by decide) (s := s) h
theorem ssplit03_ok : CovK (ssplit03 ih md pos) := fun s h => spH_ok hih 0 3 (by decide) (by decide) (s := s) h
theorem ssplit04_ok : CovK (ssplit04 ih md pos) := fun s h => spH_ok hih 0 4 (by decide) (by decide) (s := s) h
theorem ssplit05_ok : CovK (ssplit05 ih md pos) := fun s h => spH_ok hih 0 5 (by decide) (by decide) (s := s) h
theorem ssplit06_ok : CovK (ssplit06 ih md pos) := fun s h => spH_ok hih 0 6 (by decide) (by decide) (s := s) h
theorem ssplit07_ok : CovK (ssplit07 ih md pos) := fun s h => spH_ok hih 0 7 (by decide) (by decide) (s := s) h
theorem ssplit08_ok : CovK (ssplit08 ih md pos) := fun s h => spH_ok hih 0 8 (by decide) (by decide) (s := s) h
theorem ssplit13_ok : CovK (ssplit13 ih md pos) := fun s h => spH_ok hih 1 3 (by decide) (by decide) (s := s) h
theorem ssplit14_ok : CovK (ssplit14 ih md pos) := fun s h => spH_ok hih 1 4 (by decide) (by decide) (s := s) h
theorem ssplit15_ok : CovK (ssplit15 ih md pos) := fun s h => spH_ok hih 1 5 (by decide) (by decide) (s := s) h
theorem ssplit16_ok : CovK (ssplit16 ih md pos) := fun s h => spH_ok hih 1 6 (by decide) (by decide) (s := s) h
theorem ssplit17_ok : CovK (ssplit17 ih md pos) := fun s h => spH_ok hih 1 7 (by decide) (by decide) (s := s) h
theorem ssplit18_ok : CovK (ssplit18 ih md pos) := fun s h => spH_ok hih 1 8 (by decide) (by decide) (s := s) h
theorem ssplit24_ok : CovK (ssplit24 ih md pos) := fun s h => spH_ok hih 2 4 (by decide) (by decide) (s := s) h
theorem ssplit25_ok : CovK (ssplit25 ih md pos) := fun s h => spH_ok hih 2 5 (by decide) (by decide) (s := s) h
theorem ssplit26_ok : CovK (ssplit26 ih md pos) := fun s h => spH_ok hih 2 6 (by decide) (by decide) (s := s) h
theorem ssplit27_ok : CovK (ssplit27 ih md pos) := fun s h => spH_ok hih 2 7 (by decide) (by decide) (s := s) h
theorem ssplit28_ok : CovK (ssplit28 ih md pos) := fun s h => spH_ok hih 2 8 (by decide) (by decide) (s := s) h
theorem ssplit35_ok : CovK (ssplit35 ih md pos) := fun s h => spH_ok hih 3 5 (by decide) (by decide) (s := s) h
theorem ssplit36_ok : CovK (ssplit36 ih md pos) := fun s h => spH_ok hih 3 6 (by decide) (by decide) (s := s) h
theorem ssplit37_ok : CovK (ssplit37 ih md pos) := fun s h => spH_ok hih 3 7 (by decide) (by decide) (s := s) h
theorem ssplit38_ok : CovK (ssplit38 ih md pos) := fun s h => spH_ok hih 3 8 (by decide) (by decide) (s := s) h
theorem ssplit46_ok : CovK (ssplit46 ih md pos) := fun s h => spH_ok hih 4 6 (by decide) (by decide) (s := s) h
theorem ssplit47_ok : CovK (ssplit47 ih md pos) := fun s h => spH_ok hih 4 7 (by decide) (by decide) (s := s) h
theorem ssplit48_ok : CovK (ssplit48 ih md pos) := fun s h => spH_ok hih 4 8 (by decide) (by decide) (s := s) h
theorem ssplit57_ok : CovK (ssplit57 ih md pos) := fun s h => spH_ok hih 5 7 (by decide) (by decide) (s := s) h
theorem ssplit58_ok : CovK (ssplit58 ih md pos) := fun s h => spH_ok hih 5 8 (by decide) (by decide) (s := s) h
theorem ssplit68_ok : CovK (ssplit68 ih md pos) := fun s h => spH_ok hih 6 8 (by decide) (by decide) (s := s) h
end
noncomputable def splitAx (ih : WF) (md pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit68 ih md pos) (Nat.beq ax 35)) (ssplit58 ih md pos) (Nat.beq ax 34)) (ssplit57 ih md pos) (Nat.beq ax 33)) (ssplit48 ih md pos) (Nat.beq ax 32)) (ssplit47 ih md pos) (Nat.beq ax 31)) (ssplit46 ih md pos) (Nat.beq ax 30)) (ssplit38 ih md pos) (Nat.beq ax 29)) (ssplit37 ih md pos) (Nat.beq ax 28)) (ssplit36 ih md pos) (Nat.beq ax 27)) (ssplit35 ih md pos) (Nat.beq ax 26)) (ssplit28 ih md pos) (Nat.beq ax 25)) (ssplit27 ih md pos) (Nat.beq ax 24)) (ssplit26 ih md pos) (Nat.beq ax 23)) (ssplit25 ih md pos) (Nat.beq ax 22)) (ssplit24 ih md pos) (Nat.beq ax 21)) (ssplit18 ih md pos) (Nat.beq ax 20)) (ssplit17 ih md pos) (Nat.beq ax 19)) (ssplit16 ih md pos) (Nat.beq ax 18)) (ssplit15 ih md pos) (Nat.beq ax 17)) (ssplit14 ih md pos) (Nat.beq ax 16)) (ssplit13 ih md pos) (Nat.beq ax 15)) (ssplit08 ih md pos) (Nat.beq ax 14)) (ssplit07 ih md pos) (Nat.beq ax 13)) (ssplit06 ih md pos) (Nat.beq ax 12)) (ssplit05 ih md pos) (Nat.beq ax 11)) (ssplit04 ih md pos) (Nat.beq ax 10)) (ssplit03 ih md pos) (Nat.beq ax 9)) (ssplit02 ih md pos) (Nat.beq ax 8)) (gsplit7 ih md pos) (Nat.beq ax 7)) (gsplit6 ih md pos) (Nat.beq ax 6)) (gsplit5 ih md pos) (Nat.beq ax 5)) (gsplit4 ih md pos) (Nat.beq ax 4)) (gsplit3 ih md pos) (Nat.beq ax 3)) (gsplit2 ih md pos) (Nat.beq ax 2)) (gsplit1 ih md pos) (Nat.beq ax 1)) (gsplit0 ih md pos) (Nat.beq ax 0)
theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit68_ok hih md pos)) (fun _ => ssplit58_ok hih md pos)) (fun _ => ssplit57_ok hih md pos)) (fun _ => ssplit48_ok hih md pos)) (fun _ => ssplit47_ok hih md pos)) (fun _ => ssplit46_ok hih md pos)) (fun _ => ssplit38_ok hih md pos)) (fun _ => ssplit37_ok hih md pos)) (fun _ => ssplit36_ok hih md pos)) (fun _ => ssplit35_ok hih md pos)) (fun _ => ssplit28_ok hih md pos)) (fun _ => ssplit27_ok hih md pos)) (fun _ => ssplit26_ok hih md pos)) (fun _ => ssplit25_ok hih md pos)) (fun _ => ssplit24_ok hih md pos)) (fun _ => ssplit18_ok hih md pos)) (fun _ => ssplit17_ok hih md pos)) (fun _ => ssplit16_ok hih md pos)) (fun _ => ssplit15_ok hih md pos)) (fun _ => ssplit14_ok hih md pos)) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit08_ok hih md pos)) (fun _ => ssplit07_ok hih md pos)) (fun _ => ssplit06_ok hih md pos)) (fun _ => ssplit05_ok hih md pos)) (fun _ => ssplit04_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit7_ok hih md pos)) (fun _ => gsplit6_ok hih md pos)) (fun _ => gsplit5_ok hih md pos)) (fun _ => gsplit4_ok hih md pos)) (fun _ => gsplit3_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos)
noncomputable def tm (k : ST) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  forceR (nmax t (Nat.add a c)) fun t' => forceR (nmin u (Nat.add b d)) fun u' =>
  forceR (nmax v (Nat.add (Nat.add a c) e)) fun v' => forceR (nmin w (Nat.add (Nat.add b d) f)) fun w' =>
  forceR (nmax x (Nat.add (Nat.add (Nat.add a c) e) g)) fun x' => forceR (nmin y (Nat.add (Nat.add (Nat.add b d) f) h)) fun y' =>
  forceR (nmax z (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i)) fun z' => forceR (nmin A (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j)) fun A' =>
  forceR (nmax B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l)) fun B' => forceR (nmin C (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m)) fun C' =>
  forceR (nmax D (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n)) fun D' => forceR (nmin E (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o)) fun E' =>
  forceR (nmax F (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n) r)) fun F' => forceR (nmin G (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o) s)) fun G' =>
  forceR (nmax H (Nat.add c e)) fun H' => forceR (nmin I (Nat.add d f)) fun I' =>
  forceR (nmax J (Nat.add (Nat.add c e) g)) fun J' => forceR (nmin K (Nat.add (Nat.add d f) h)) fun K' =>
  forceR (nmax L (Nat.add (Nat.add (Nat.add c e) g) i)) fun L' => forceR (nmin M (Nat.add (Nat.add (Nat.add d f) h) j)) fun M' =>
  forceR (nmax N (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l)) fun N' => forceR (nmin O (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m)) fun O' =>
  forceR (nmax P (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n)) fun P' => forceR (nmin Q (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o)) fun Q' =>
  forceR (nmax R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n) r)) fun R' => forceR (nmin S (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o) s)) fun S' =>
  forceR (nmax T (Nat.add e g)) fun T' => forceR (nmin U (Nat.add f h)) fun U' =>
  forceR (nmax V (Nat.add (Nat.add e g) i)) fun V' => forceR (nmin W (Nat.add (Nat.add f h) j)) fun W' =>
  forceR (nmax X (Nat.add (Nat.add (Nat.add e g) i) l)) fun X' => forceR (nmin Y (Nat.add (Nat.add (Nat.add f h) j) m)) fun Y' =>
  forceR (nmax Z (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n)) fun Z' => forceR (nmin aa (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o)) fun aa' =>
  forceR (nmax ab (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n) r)) fun ab' => forceR (nmin ac (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o) s)) fun ac' =>
  forceR (nmax ad (Nat.add g i)) fun ad' => forceR (nmin ae (Nat.add h j)) fun ae' =>
  forceR (nmax af (Nat.add (Nat.add g i) l)) fun af' => forceR (nmin ag (Nat.add (Nat.add h j) m)) fun ag' =>
  forceR (nmax ah (Nat.add (Nat.add (Nat.add g i) l) n)) fun ah' => forceR (nmin ai (Nat.add (Nat.add (Nat.add h j) m) o)) fun ai' =>
  forceR (nmax aj (Nat.add (Nat.add (Nat.add (Nat.add g i) l) n) r)) fun aj' => forceR (nmin al (Nat.add (Nat.add (Nat.add (Nat.add h j) m) o) s)) fun al' =>
  forceR (nmax am (Nat.add i l)) fun am' => forceR (nmin an (Nat.add j m)) fun an' =>
  forceR (nmax ao (Nat.add (Nat.add i l) n)) fun ao' => forceR (nmin ar (Nat.add (Nat.add j m) o)) fun ar' =>
  forceR (nmax au (Nat.add (Nat.add (Nat.add i l) n) r)) fun au' => forceR (nmin av (Nat.add (Nat.add (Nat.add j m) o) s)) fun av' =>
  forceR (nmax aw (Nat.add l n)) fun aw' => forceR (nmin ax (Nat.add m o)) fun ax' =>
  forceR (nmax ay (Nat.add (Nat.add l n) r)) fun ay' => forceR (nmin az (Nat.add (Nat.add m o) s)) fun az' =>
  forceR (nmax ba (Nat.add n r)) fun ba' => forceR (nmin bb (Nat.add o s)) fun bb' =>
  k a b c d e f g h i j l m n o r s t' u' v' w' x' y' z' A' B' C' D' E' F' G' H' I' J' K' L' M' N' O' P' Q' R' S' T' U' V' W' X' Y' Z' aa' ab' ac' ad' ae' af' ag' ah' ai' aj' al' am' an' ao' ar' au' av' aw' ax' ay' az' ba' bb' bc
theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2
structure YA where
  (o P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ)
noncomputable def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 8 PR (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] y.Cp y.Cm
noncomputable def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.P4 (Nat.mul Ylo (ind (inr 4 i j)))), (Nat.add y.P5 (Nat.mul Ylo (ind (inr 5 i j)))), (Nat.add y.P6 (Nat.mul Ylo (ind (inr 6 i j)))), (Nat.add y.P7 (Nat.mul Ylo (ind (inr 7 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add y.S4 (Nat.mul Yhi (ind (inr 4 i j)))), (Nat.add y.S5 (Nat.mul Yhi (ind (inr 5 i j)))), (Nat.add y.S6 (Nat.mul Yhi (ind (inr 6 i j)))), (Nat.add y.S7 (Nat.mul Yhi (ind (inr 7 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 28))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)
noncomputable def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel
theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp
theorem ystep_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :
    MulOK s (ystep (toCl s).L (toCl s).A (toCl s).B qb w ih y) := by
  unfold ystep
  simp only [forceT_eq]
  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (mul_step hPR rfl rfl h (Nat.blt_eq.mp hc) _ _)
theorem ydec_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydec (toCl s).L (toCl s).A (toCl s).B qb w fuel y)
  | 0, _, h => h
  | n + 1, y, h => ystep_ok s qb w (ydec_ok s qb w n) y h
noncomputable def mcheckP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 cN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mcK (tf f) false s.l0 k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mcK (tf f) false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mcK (tf f) false s.l1 k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mcK (tf f) false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mcK (tf f) false (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mcK (tf f) false s.l2 k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mcK (tf f) false (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mcK (tf f) false (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mcK (tf f) false s.l3 k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mcK (tf f) false (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mcK (tf f) false (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mcK (tf f) false s.l4 k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mcK (tf f) false (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mcK (tf f) false (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mcK (tf f) false s.l5 k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mcK (tf f) false (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mcK (tf f) false (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mcK (tf f) false s.l6 k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mcK (tf f) false s.l7 k78 m78 p78 r78))) Cp) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mwT k01 m01))) (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 28195867368000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mslK (tf f) k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 22223820732794000000 (mwT k12 m12))) (Nat.mul 21042948716829000000 (mwT k13 m13))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 50516979727000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mslK (tf f) k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 21042948716829000000 (mwT k13 m13))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 31202320231433000000 (mwT k23 m23))) (Nat.mul 47970464688707000000 (mwT k24 m24))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 69185101351000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 21042948716829000000 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mslK (tf f) k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28)))) S2)))) (Nat.mul (Nat.sub s.u3 s.l3) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 47970464688707000000 (mwT k24 m24))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 34428833097063000000 (mwT k34 m34))) (Nat.mul 61973173188925000000 (mwT k35 m35))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38)))) P3) (Nat.add (Nat.add (Nat.mul 1024000000000 80158024056000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 47970464688707000000 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mslK (tf f) k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38)))) S3)))) (Nat.mul (Nat.sub s.u4 s.l4) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 61973173188925000000 (mwT k35 m35))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 34428833097063000000 (mwT k45 m45))) (Nat.mul 47970464688707000000 (mwT k46 m46))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48)))) P4) (Nat.add (Nat.add (Nat.mul 1024000000000 80158024056000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 61973173188925000000 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mslK (tf f) k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48)))) S4)))) (Nat.mul (Nat.sub s.u5 s.l5) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 47970464688707000000 (mwT k46 m46))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 31202320231433000000 (mwT k56 m56))) (Nat.mul 21042948716829000000 (mwT k57 m57))) (Nat.mul 8651269219434000000 (mwT k58 m58)))) P5) (Nat.add (Nat.add (Nat.mul 1024000000000 69185101351000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 47970464688707000000 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mslK (tf f) k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58)))) S5)))) (Nat.mul (Nat.sub s.u6 s.l6) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 21042948716829000000 (mwT k57 m57))) (Nat.mul 8651269219434000000 (mwT k58 m58))) (Nat.mul 22223820732794000000 (mwT k67 m67)))) P6) (Nat.add (Nat.add (Nat.mul 1024000000000 50516979727000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 21042948716829000000 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mslK (tf f) k67 m67 p67 r67)))) S6)))) (Nat.mul (Nat.sub s.u7 s.l7) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 8651269219434000000 (mwT k58 m58))) (Nat.mul 12145025938708000000 (mwT k78 m78)))) P7) (Nat.add (Nat.add (Nat.mul 1024000000000 28195867368000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 12145025938708000000 (mslK (tf f) k78 m78 p78 r78)))) S7))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 28195867368000000 s.l0)) (Nat.mul 50516979727000000 s.l1)) (Nat.mul 69185101351000000 s.l2)) (Nat.mul 80158024056000000 s.l3)) (Nat.mul 80158024056000000 s.l4)) (Nat.mul 69185101351000000 s.l5)) (Nat.mul 50516979727000000 s.l6)) (Nat.mul 28195867368000000 s.l7))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mvKF top bk (tf f) s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mvKF top bk (tf f) (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mvKF top bk (tf f) (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (uc (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3))) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mvKF top bk (tf f) (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (uc (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4))) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mvKF top bk (tf f) (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5))) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mvKF top bk (tf f) (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6))) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mvKF top bk (tf f) (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mvKF top bk (tf f) s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mvKF top bk (tf f) (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mvKF top bk (tf f) (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (uc (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3))) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mvKF top bk (tf f) (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (uc (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4))) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mvKF top bk (tf f) (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5))) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mvKF top bk (tf f) (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6))) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mvKF top bk (tf f) (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mvKF top bk (tf f) s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mvKF top bk (tf f) (nmax s.A24 (Nat.add s.l2 s.l3)) (uc (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3))) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mvKF top bk (tf f) (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (uc (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4))) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mvKF top bk (tf f) (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (uc (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5))) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mvKF top bk (tf f) (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6))) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mvKF top bk (tf f) (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7))) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mvKF top bk (tf f) s.l3 (uc s.l3 s.u3) k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mvKF top bk (tf f) (nmax s.A35 (Nat.add s.l3 s.l4)) (uc (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4))) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mvKF top bk (tf f) (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (uc (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5))) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mvKF top bk (tf f) (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (uc (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6))) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mvKF top bk (tf f) (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7))) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mvKF top bk (tf f) s.l4 (uc s.l4 s.u4) k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mvKF top bk (tf f) (nmax s.A46 (Nat.add s.l4 s.l5)) (uc (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5))) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mvKF top bk (tf f) (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (uc (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6))) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mvKF top bk (tf f) (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (uc (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7))) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mvKF top bk (tf f) s.l5 (uc s.l5 s.u5) k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mvKF top bk (tf f) (nmax s.A57 (Nat.add s.l5 s.l6)) (uc (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6))) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mvKF top bk (tf f) (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (uc (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7))) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mvKF top bk (tf f) s.l6 (uc s.l6 s.u6) k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mvKF top bk (tf f) s.l7 (uc s.l7 s.u7) k78 m78 p78 r78))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mcK (tf f) true s.l0 k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mcK (tf f) true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mcK (tf f) true s.l1 k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mcK (tf f) true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mcK (tf f) true (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mcK (tf f) true s.l2 k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mcK (tf f) true (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mcK (tf f) true (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mcK (tf f) true s.l3 k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mcK (tf f) true (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mcK (tf f) true (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mcK (tf f) true s.l4 k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mcK (tf f) true (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mcK (tf f) true (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mcK (tf f) true s.l5 k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mcK (tf f) true (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mcK (tf f) true (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mcK (tf f) true s.l6 k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mcK (tf f) true s.l7 k78 m78 p78 r78))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokI f s.l7 s.u7 k78 m78 p78 r78) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l6 s.u6 k67 m67 p67 r67) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) k58 m58 p58 r58) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6)) k57 m57 p57 r57) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l5 s.u5 k56 m56 p56 r56) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) k48 m48 p48 r48) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) k47 m47 p47 r47) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5)) k46 m46 p46 r46) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l4 s.u4 k45 m45 p45 r45) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) k38 m38 p38 r38) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) k37 m37 p37 r37) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) k36 m36 p36 r36) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4)) k35 m35 p35 r35) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l3 s.u3 k34 m34 p34 r34) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) k28 m28 p28 r28) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) k27 m27 p27 r27) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) k26 m26 p26 r26) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) k25 m25 p25 r25) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3)) k24 m24 p24 r24) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k18 m18 p18 r18) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) k17 m17 p17 r17) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) k16 m16 p16 r16) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) k15 m15 p15 r15) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) k14 m14 p14 r14) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k08 m08 p08 r08) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) k07 m07 p07 r07) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) k06 m06 p06 r06) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) k05 m05 p05 r05) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) k04 m04 p04 r04) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l0 s.u0 k01 m01 p01 r01) (true))))))))))))))))))))))))))))))))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l7 s.u7) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l6 s.u6) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l5 s.u5) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l4 s.u4) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l3 s.u3) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true))))))))))
theorem mcheckP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) (h : mcheckP top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm = true) :
    mcheckGX (mokI f) top bk (tf f) 8 BS TS cN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k04, m04, p04, r04), (k05, m05, p05, r05), (k06, m06, p06, r06), (k07, m07, p07, r07), (k08, m08, p08, r08), (k12, m12, p12, r12), (k13, m13, p13, r13), (k14, m14, p14, r14), (k15, m15, p15, r15), (k16, m16, p16, r16), (k17, m17, p17, r17), (k18, m18, p18, r18), (k23, m23, p23, r23), (k24, m24, p24, r24), (k25, m25, p25, r25), (k26, m26, p26, r26), (k27, m27, p27, r27), (k28, m28, p28, r28), (k34, m34, p34, r34), (k35, m35, p35, r35), (k36, m36, p36, r36), (k37, m37, p37, r37), (k38, m38, p38, r38), (k45, m45, p45, r45), (k46, m46, p46, r46), (k47, m47, p47, r47), (k48, m48, p48, r48), (k56, m56, p56, r56), (k57, m57, p57, r57), (k58, m58, p58, r58), (k67, m67, p67, r67), (k78, m78, p78, r78)]
      [P0, P1, P2, P3, P4, P5, P6, P7] [S0, S1, S2, S3, S4, S5, S6, S7] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq] at h; exact h
noncomputable def mleafP (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
  forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
  forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
  forceR (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) fun L07 => forceR (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) fun U07 =>
  forceR (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L08 => forceR (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U08 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
  forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
  forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
  forceR (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) fun L17 => forceR (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) fun U17 =>
  forceR (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L18 => forceR (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U18 =>
  forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
  forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
  forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
  forceR (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) fun L27 => forceR (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) fun U27 =>
  forceR (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) fun L28 => forceR (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) fun U28 =>
  forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
  forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
  forceR (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) fun L37 => forceR (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) fun U37 =>
  forceR (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) fun L38 => forceR (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) fun U38 =>
  forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
  forceR (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) fun L47 => forceR (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) fun U47 =>
  forceR (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) fun L48 => forceR (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) fun U48 =>
  forceR (nmax s.A57 (Nat.add s.l5 s.l6)) fun L57 => forceR (nmin s.B57 (Nat.add s.u5 s.u6)) fun U57 =>
  forceR (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) fun L58 => forceR (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) fun U58 =>
  forceR (nmax s.A68 (Nat.add s.l6 s.l7)) fun L68 => forceR (nmin s.B68 (Nat.add s.u6 s.u7)) fun U68 =>
  forceR 0 fun o0 =>
  dec4F 10 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4F 10 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4F 10 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
  dec4F 10 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
  dec4F 10 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
  dec4F 10 w o5 L07 U07 fun k07 m07 p07 r07 o6 =>
  dec4F 10 w o6 L08 U08 fun k08 m08 p08 r08 o7 =>
  dec4F 10 w o7 s.l1 s.u1 fun k12 m12 p12 r12 o8 =>
  dec4F 10 w o8 L13 U13 fun k13 m13 p13 r13 o9 =>
  dec4F 10 w o9 L14 U14 fun k14 m14 p14 r14 o10 =>
  dec4F 10 w o10 L15 U15 fun k15 m15 p15 r15 o11 =>
  dec4F 10 w o11 L16 U16 fun k16 m16 p16 r16 o12 =>
  dec4F 10 w o12 L17 U17 fun k17 m17 p17 r17 o13 =>
  dec4F 10 w o13 L18 U18 fun k18 m18 p18 r18 o14 =>
  dec4F 10 w o14 s.l2 s.u2 fun k23 m23 p23 r23 o15 =>
  dec4F 10 w o15 L24 U24 fun k24 m24 p24 r24 o16 =>
  dec4F 10 w o16 L25 U25 fun k25 m25 p25 r25 o17 =>
  dec4F 10 w o17 L26 U26 fun k26 m26 p26 r26 o18 =>
  dec4F 10 w o18 L27 U27 fun k27 m27 p27 r27 o19 =>
  dec4F 10 w o19 L28 U28 fun k28 m28 p28 r28 o20 =>
  dec4F 10 w o20 s.l3 s.u3 fun k34 m34 p34 r34 o21 =>
  dec4F 10 w o21 L35 U35 fun k35 m35 p35 r35 o22 =>
  dec4F 10 w o22 L36 U36 fun k36 m36 p36 r36 o23 =>
  dec4F 10 w o23 L37 U37 fun k37 m37 p37 r37 o24 =>
  dec4F 10 w o24 L38 U38 fun k38 m38 p38 r38 o25 =>
  dec4F 10 w o25 s.l4 s.u4 fun k45 m45 p45 r45 o26 =>
  dec4F 10 w o26 L46 U46 fun k46 m46 p46 r46 o27 =>
  dec4F 10 w o27 L47 U47 fun k47 m47 p47 r47 o28 =>
  dec4F 10 w o28 L48 U48 fun k48 m48 p48 r48 o29 =>
  dec4F 10 w o29 s.l5 s.u5 fun k56 m56 p56 r56 o30 =>
  dec4F 10 w o30 L57 U57 fun k57 m57 p57 r57 o31 =>
  dec4F 10 w o31 L58 U58 fun k58 m58 p58 r58 o32 =>
  dec4F 10 w o32 s.l6 s.u6 fun k67 m67 p67 r67 o33 =>
  dec4F 10 w o33 s.l7 s.u7 fun k78 m78 p78 r78 o34 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.P6 y.P7 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.S6 y.S7 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 14 w 42 ⟨o34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
/- Eliminate forced decoder values without duplicating their expressions.
   This preserves the actual evaluator and every guard; it changes only the
   proof term used to establish the existing universal leaf theorem. -/
theorem zeroForge_forceR_cov {P : Prop} {a : ℕ} {k : ℕ → ℕ}
    (hk : ∀ x, k x ≠ 0 → P) (h : forceR a k ≠ 0) : P := by
  rw [forceR_eq] at h
  exact hk _ h

theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  revert h
  unfold mleafP dec4F
  iterate 227 refine zeroForge_forceR_cov (fun _ => ?_)
  intro h
  exact mcheckGX_sound (f := tf pb) (mtermTI hlb hpt) hPR hTS (ydec_ok s 14 w 42 _ (MulOK_zero s _)) (mcheckP_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))
noncomputable def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] 8)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 14 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
noncomputable def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u7 l0)
theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s 14 w 42 _ (MulOK_zero s 0)) (brec_ne h)
theorem leafStep_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u7 s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u7 s.l0
  · rw [hs, forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
    · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · intro g hg
    right
    have h1 : g 7 ≤ (s.u7 : ℝ) / SC := (hg.1 7 (by norm_num)).2
    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have : (s.u7 : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    show g 7 < g 0
    linarith
noncomputable def WMASK : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
noncomputable def rdw (f : ℕ → ℕ) (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (f (Nat.div pos 32768)) (Nat.mod pos 32768)) WMASK
noncomputable def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (bits pos))
    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 1) (Nat.add pos 8) (Nat.land (Nat.shiftRight (bits pos) 1) 63))
    (Nat.beq (Nat.land (bits pos) 1) 1)
noncomputable def walkC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel
noncomputable def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)
theorem walkC_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from
      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)
theorem walk_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)
theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)
noncomputable def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.l3 b.l3 && Nat.beq a.u3 b.u3 && Nat.beq a.l4 b.l4 && Nat.beq a.u4 b.u4 && Nat.beq a.l5 b.l5 && Nat.beq a.u5 b.u5 && Nat.beq a.l6 b.l6 && Nat.beq a.u6 b.u6 && Nat.beq a.l7 b.l7 && Nat.beq a.u7 b.u7 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A04 b.A04 && Nat.beq a.B04 b.B04 && Nat.beq a.A05 b.A05 && Nat.beq a.B05 b.B05 && Nat.beq a.A06 b.A06 && Nat.beq a.B06 b.B06 && Nat.beq a.A07 b.A07 && Nat.beq a.B07 b.B07 && Nat.beq a.A08 b.A08 && Nat.beq a.B08 b.B08 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.A14 b.A14 && Nat.beq a.B14 b.B14 && Nat.beq a.A15 b.A15 && Nat.beq a.B15 b.B15 && Nat.beq a.A16 b.A16 && Nat.beq a.B16 b.B16 && Nat.beq a.A17 b.A17 && Nat.beq a.B17 b.B17 && Nat.beq a.A18 b.A18 && Nat.beq a.B18 b.B18 && Nat.beq a.A24 b.A24 && Nat.beq a.B24 b.B24 && Nat.beq a.A25 b.A25 && Nat.beq a.B25 b.B25 && Nat.beq a.A26 b.A26 && Nat.beq a.B26 b.B26 && Nat.beq a.A27 b.A27 && Nat.beq a.B27 b.B27 && Nat.beq a.A28 b.A28 && Nat.beq a.B28 b.B28 && Nat.beq a.A35 b.A35 && Nat.beq a.B35 b.B35 && Nat.beq a.A36 b.A36 && Nat.beq a.B36 b.B36 && Nat.beq a.A37 b.A37 && Nat.beq a.B37 b.B37 && Nat.beq a.A38 b.A38 && Nat.beq a.B38 b.B38 && Nat.beq a.A46 b.A46 && Nat.beq a.B46 b.B46 && Nat.beq a.A47 b.A47 && Nat.beq a.B47 b.B47 && Nat.beq a.A48 b.A48 && Nat.beq a.B48 b.B48 && Nat.beq a.A57 b.A57 && Nat.beq a.B57 b.B57 && Nat.beq a.A58 b.A58 && Nat.beq a.B58 b.B58 && Nat.beq a.A68 b.A68 && Nat.beq a.B68 b.B68 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩, h43⟩, h44⟩, h45⟩, h46⟩, h47⟩, h48⟩, h49⟩, h50⟩, h51⟩, h52⟩, h53⟩, h54⟩, h55⟩, h56⟩, h57⟩, h58⟩, h59⟩, h60⟩, h61⟩, h62⟩, h63⟩, h64⟩, h65⟩, h66⟩, h67⟩, h68⟩, h69⟩, h70⟩, h71⟩, h72⟩ := h
  subst_vars; rfl
theorem covered_of_walkCP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel pos e : ℕ) (s : St)
    (h : U (walkC top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walkC_ok hlb hD hpt hR bits fuel pos s (h ▸ he)
noncomputable def kEqE (t : St) (e : ℕ) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ) 0 e (stEq ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩ t)
theorem kEqE_ok {t : St} {e : ℕ} (h : Covered (toCl t)) : CovK (kEqE t e) := fun s hs => by
  have e' : U (kEqE t e) s = Bool.rec (motive := fun _ => ℕ) 0 e (stEq s t) := rfl
  rw [e'] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
noncomputable def cutAt (cuts : List (ℕ × St × ℕ)) (pos : ℕ) (k : ST) : ST :=
  List.rec (motive := fun _ => ST) k (fun c _ ih => Bool.rec (motive := fun _ => ST) ih (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos)) cuts
noncomputable def CutsOk (cuts : List (ℕ × St × ℕ)) : Prop := ∀ c ∈ cuts, Covered (toCl c.2.1)
theorem cutsOk_nil : CutsOk [] := fun _ h => absurd h (by simp)
theorem cutsOk_cons {p e : ℕ} {t : St} {cs : List (ℕ × St × ℕ)} (h : Covered (toCl t)) (hs : CutsOk cs) :
    CutsOk ((p, t, e) :: cs) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h
  · exact hs c hc
theorem cutAt_ok {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (pos : ℕ) {k : ST} (hk : CovK k) : CovK (cutAt cuts pos k) := by
  induction cuts with
  | nil => exact hk
  | cons c cs ih =>
    show CovK (Bool.rec (motive := fun _ => ST) (cutAt cs pos k) (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos))
    cases Nat.beq c.1 pos
    · exact ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))
    · exact kEqE_ok (hc c (List.mem_cons.mpr (Or.inl rfl)))
noncomputable def walkCut (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => cutAt cuts pos (node top bk tD bD pb R bits ih pos)) fuel
noncomputable def walkCutR (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  fun pos => tm (walkCut top bk tD bD pb R bits cuts fuel pos)
theorem walkCut_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) : ∀ fuel, WalkOK (walkCut top bk tD bD pb R bits cuts fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => cutAt_ok hc pos
      (show CovK (node top bk tD bD pb R bits (walkCut top bk tD bD pb R bits cuts n) pos) from
        brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
        (splitAx_ok (walkCut_ok hlb hD hpt hR bits hc n) _ _ _))
theorem covered_of_walkCutR {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (fuel pos e : ℕ) (s : St)
    (h : U (walkCutR top bk tD bD pb R bits cuts fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  tm_ok (walkCut_ok hlb hD hpt hR bits hc fuel pos) s (h ▸ he)
noncomputable def ADJ : List ℕ := [0, 7, 14, 20, 25, 29, 32, 33]
theorem hADJ : ∀ r < 8, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 8, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 8, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 8, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 8 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 8, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 8 28 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 8, 0 ≤ g r) → Pg cN 8 BS TS g :=
  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW hrun
end AMW.Cert.PC9QB6M
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
end AMW.Cert.PCell
end
noncomputable section
namespace AMW.Cert.PCell
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
noncomputable def pwD (x w : ℕ) : ℕ :=
  Nat.add (trip w) (Nat.add (Nat.shiftLeft (Nat.sub x (Nat.land (Nat.shiftRight w 96) 1048575)) 96)
    (Nat.shiftLeft (Nat.add x (Nat.shiftRight w 116)) 120))
noncomputable def ptlD (L : List (ℕ × ℕ)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ ih => Bool.rec (motive := fun _ => ℕ) ih (pwD x e.2) (Nat.beq e.1 (Nat.mod x 1024))) L
noncomputable def ptlOkD (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh j : ℕ)
    (L : List (ℕ × ℕ)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2))
      && ivOk R top bk tD bD n csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2) && ih) L
theorem ptlD_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) (j : ℕ) :
    ∀ L : List (ℕ × ℕ), ptlOkD R top bk tD bD n csh j L = true → ∀ x, x / 1024 = j → PVI x (ptlD L x) := by
  intro L
  induction L with
  | nil => intro _ x _; exact pvi_zero x
  | cons e r ih =>
    intro h x hx
    have h' : (pt3e (Nat.add (Nat.mul 1024 j) e.1) (trip (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2))
      && ivOk R top bk tD bD n csh (Nat.add (Nat.mul 1024 j) e.1) (pwD (Nat.add (Nat.mul 1024 j) e.1) e.2)
      && ptlOkD R top bk tD bD n csh j r) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨he, hiv⟩, hr⟩ := h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptlD r x) (pwD x e.2) (Nat.beq e.1 (Nat.mod x 1024)))
    cases hb : Nat.beq e.1 (Nat.mod x 1024)
    · exact ih hr x hx
    · have he1 : e.1 = x % 1024 := by have := Nat.eq_of_beq_eq_true hb; exact this
      have hxe : Nat.add (Nat.mul 1024 j) e.1 = x := by
        show 1024 * j + e.1 = x
        rw [he1, ← hx]; exact Nat.div_add_mod x 1024
      rw [hxe] at he hiv
      simp only [pt3e, Bool.and_eq_true] at he
      have hpv : PV x (trip (pwD x e.2)) := ⟨ptOk_sound he.1, PS_of_ptdOk he.2⟩
      exact ⟨hpv, ivOk_sound hlb hD hR hn hpv hiv⟩
inductive PTrD where
  | lf (j : ℕ) (L : List (ℕ × ℕ))
  | nd (k : ℕ) (l r : PTrD)
noncomputable def ptGetD (t : PTrD) (x : ℕ) : ℕ :=
  PTrD.rec (motive := fun _ => ℕ) (fun j L => Bool.rec (motive := fun _ => ℕ) 0 (ptlD L x) (Nat.beq (Nat.div x 1024) j))
    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt (Nat.div x 1024) k)) t
noncomputable def ptOkTD (R : ℕ × ℕ × List (List ℕ)) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (n csh : ℕ) (t : PTrD) : Bool :=
  PTrD.rec (motive := fun _ => Bool) (fun j L => ptlOkD R top bk tD bD n csh j L) (fun _ _ _ bl br => bl && br) t
theorem ptTD_sound {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hR : rgOk R = true) {n csh : ℕ} (hn : 0 < n) :
    ∀ t : PTrD, ptOkTD R top bk tD bD n csh t = true → ∀ x, PVI x (ptGetD t x) := by
  intro t
  induction t with
  | lf j L =>
    intro h x
    show PVI x (Bool.rec (motive := fun _ => ℕ) 0 (ptlD L x) (Nat.beq (Nat.div x 1024) j))
    cases hb : Nat.beq (Nat.div x 1024) j
    · exact pvi_zero x
    · exact ptlD_sound hlb hD hR hn j L h x (Nat.eq_of_beq_eq_true hb)
  | nd k l r ihl ihr =>
    intro h x
    have h' : (ptOkTD R top bk tD bD n csh l && ptOkTD R top bk tD bD n csh r) = true := h
    simp only [Bool.and_eq_true] at h'
    show PVI x (Bool.rec (motive := fun _ => ℕ) (ptGetD r x) (ptGetD l x) (Nat.blt (Nat.div x 1024) k))
    cases Nat.blt (Nat.div x 1024) k
    · exact ihr h'.2 x
    · exact ihl h'.1 x
theorem ptOkTD_nd {R : ℕ × ℕ × List (List ℕ)} {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {n csh k : ℕ}
    {l r : PTrD} (hl : ptOkTD R top bk tD bD n csh l = true) (hr : ptOkTD R top bk tD bD n csh r = true) :
    ptOkTD R top bk tD bD n csh (.nd k l r) = true := by
  show (ptOkTD R top bk tD bD n csh l && ptOkTD R top bk tD bD n csh r) = true
  rw [hl, hr]; rfl
end AMW.Cert.PCell
end
set_option Elab.async false
noncomputable section
namespace AMW.Cert.PC9QB6MData
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC9QB6M
set_option maxRecDepth 100000
noncomputable def TOP : ℕ := 0x1870001d64a0006b76b000df8ea00168eb0001f341000269caa002ba740002bf1e200271da3001fc0200016f78a000e1ed60006998d00019d6700000000000001fa00021e4c0007b8d000100d9f0019ea3c0023daa3002c61350032311800329021002d05d400248e5a001a728e00104225000797a70001d99f000000000000029c000279050008fc100012aa67001e21d80029b3350033a305003a6d5c003aea8400347c80002aa252001eda710012f7470008d9490002257a00000000000003820002ee1b000a9bd90016062500238dc700313759003cf73e004501c200459aed003dfdf700324f92002455a400163c44000a4303000264ef00000000000009560003c9ad000d53e6001b70cf002c2a65003d235e004bd8010056112300577be6004e63430040228b002eda44001d3c9e000dfb960003a095000000000000003c0003fa96000f51490020a86d0035b4fa004b8e48005f1a47006d82a90072ef3a006951390058bdfa004396f1002d75050018cd12000923010000e32300000000000168e0000ac636001bb50a003199280049abc40060108e00716618007ad5480071f46f006109f9004a9d200032a160001beeef000a7bae00011a590000000000016e24000ba79d001e68380036982a00516da5006a5988007d7e710086f0b7007c2a4f00686379004e9f7800332c93001a3a9e000820ea00002e9c000000000004362a0014595d002eca43004fc8a7007358350093fe6300ace17f00b8e3ea00aa985d009072c7006e478f0049d2280027dd65000e322f000118dc000000000002f63b001417090032679e005913640083b64d00ab315e00c96e5f00d7d1fd00c633b700a64b83007cf7fc0050c2900028ebdb000c47af00002c3600000000000748780021ec2b004d16da0082839a00bb982000ef368501155cff01220a560106707100d80bc4009df74d0061909c002d1db6000a3a0f0000000000003e910012d75000421f760089513100df7fae0139797e018a400101c5c67701d9dc5101aef73e016644ab010a68b800a992c10053822f001718c3000008090000000000140c370053f70700b8f3df0134c7c701b84992022e63c002845c6602994da70252a57a01dfe19a0152fdf800c4c60b004e48330009638b000000000008fd740057854500f4960c01d2590a02d7483b03e110f204c9431a056b0e7c0572428304caad1503c79fa4029148ff0162d6fd0072ab6700026a77000000000044e479015a793103472e4a05ee485d090e772a0c55ec960f5119ab118cbd20123b9d23105de9ed0d2508c109040ed704c0aefb015493bb000000000000f8870231d80309440d2216797cb02accad3c46be8e286a79013a954be118c5e334c10000000000000000000000000000000000000000000000000000000000000000000001870006b76b00168eb000269caa00271da30016f78a0006998d00000000000001fa0007b8d00019ea3c002c6135002d05d4001a728e000797a7000000000000029c0008fc10001e21d80033a30500347c80001eda710008d9490000000000000382000a9bd900238dc7003cf73e003dfdf7002455a4000a43030000000000000956000d53e6002c2a65004bd801004e6343002eda44000dfb96000000000000003c000f51490035b4fa005f1a4700695139004396f10018cd120000e32300000000000ac636003199280060108e0071f46f004a9d20001beeef00011a5900000000000ba79d0036982a006a5988007c2a4f004e9f78001a3a9e00002e9c000000000014595d004fc8a70093fe6300aa985d006e478f0027dd65000118dc00000000001417090059136400ab315e00c633b7007cf7fc0028ebdb00002c36000000000021ec2b0082839a00ef368501067071009df74d002d1db60000000000003e9100421f7600df7fae018a400101aef73e010a68b80053822f00000809000000000053f7070134c7c7022e63c00252a57a0152fdf8004e4833000000000008fd7400f4960c02d7483b04c9431a04caad15029148ff0072ab67000000000044e47903472e4a090e772a0f5119ab105de9ed09040ed7015493bb000000000231d80316797cb046be8e28954be118000000000000000000000000000000000000018700168eb00016f78a00000000000001fa0019ea3c001a728e000000000000029c001e21d8001eda71000000000000038200238dc7002455a40000000000000956002c2a65002eda44000000000000003c0035b4fa004396f10000e3230000000000319928004a9d2000011a59000000000036982a004e9f7800002e9c00000000004fc8a7006e478f000118dc0000000000591364007cf7fc00002c36000000000082839a009df74d0000000000003e9100df7fae010a68b800000809000000000134c7c70152fdf8000000000008fd7402d7483b029148ff000000000044e479090e772a09040ed7000000000231d80346be8e2800000000000000000000018700000000000001fa000000000000029c00000000000003820000000000000956000000000000003c0000e3230000000000011a590000000000002e9c00000000000118dc0000000000002c36000000000000000000003e910000080900000000000000000008fd74000000000044e479000000000231d8030000000000000000000000000000000000000000000000000000003c0000000000000000000000000000000000000000000008090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable def BK_16 : ℕ := 0x1bf6e140fcc8d8649d9bc48b5e6f70bebbf6e140fd9bc48b5bf6e140e8
noncomputable def BK_17 : ℕ := 0x18bc66983988a7581a5699a71b26119dd8bc66983a5699a718bc669828
noncomputable def BK_18 : ℕ := 0x159f7d353663675b77299f84b7f20151559f7d3537299f84b59f7d3528
noncomputable def BK_19 : ℕ := 0x12a97c231362e4b5941f1bc754de03b3f2a97c23141f1bc752a97c2308
noncomputable def BK_20 : ℕ := 0xfe20416d08f29f0d13f851191f2fe1a4fe20416d13f85118fe20416c8
noncomputable def BK_21 : ℕ := 0xd4f20274deea5426e91ae224f38295e4d4f20274e91ae224d4f202748
noncomputable def BK_22 : ℕ := 0xaf55b3f0b863fe8cc1adfa84cb32ec6caf55b3f0c1adfa84af55b3f08
noncomputable def BK_23 : ℕ := 0x8d7d1c50959704d49deeb252a683c0068d7d1c509deeb2528d7d1c508
noncomputable def BK_24 : ℕ := 0x6fa734fe76c6b7127e24c07085c13da06fa734fe7e24c0706fa734fe8
noncomputable def BK_25 : ℕ := 0x55995a785bbf7bce6223b3bc68c63a3c55995a786223b3bc55995a788
noncomputable def BK_26 : ℕ := 0x3f66f1aa449845dc4a06231c4fb105f43f66f1aa4a06231c3f66f1aa8
noncomputable def BK_27 : ℕ := 0x2cf2f96031384d9235b79f003a719a0c2cf2f96035b79f002cf2f9608
noncomputable def BK_28 : ℕ := 0x1e1136082176e12625131e4028e6db281e11360825131e401e1136088
noncomputable def BK_29 : ℕ := 0x12881a44151da9ce17e5a4621ae1235a12881a4417e5a46212881a448
noncomputable def BK_30 : ℕ := 0xa12d1ae0bea666a0defa8541023d2fc0a12d1ae0defa8540a12d1ae8
noncomputable def BK_31 : ℕ := 0x463b0060591685006e79eb20867a77c0463b00606e79eb20463b0068
noncomputable def BK_32 : ℕ := 0x120a56201ba75de02780c8e035adacc0120a56202780c8e0120a5628
noncomputable def BK_33 : ℕ := 0x1f10e001b51840052885a00a927c80001f10e0052885a0001f10e8
noncomputable def BK_34 : ℕ := 0x5791020021c76a0004d940000000000021c76a00000000000000008
noncomputable def BK_35 : ℕ := 0x20bb2000180412801082da600a4d3620180412800a4d36200a4d3628
noncomputable def BK_36 : ℕ := 0x4e065ce0414d01203574c7a02a927760414d01202a9277602a927768
noncomputable def BK_37 : ℕ := 0x8822e06078ae3b2069caef205b8c628078ae3b205b8c62805b8c6288
noncomputable def BK_38 : ℕ := 0xca2d7020b92d0e40a874a4a09815df60b92d0e409815df609815df68
noncomputable def BK_39 : ℕ := 0x10fae4d60fe34f460ecc1d4e0db6498a0fe34f460db6498a0db6498a8
noncomputable def BK_40 : ℕ := 0x1542363c1431bcf4131e178612081dae1431bcf412081dae12081dae8
noncomputable def BK_41 : ℕ := 0x1954cf781858b84617567424164eb4f61858b846164eb4f6164eb4f68
noncomputable def BK_42 : ℕ := 0x1cfad7fe1c1da5b01b37dfd81a4a11821c1da5b01a4a11821a4a11828
noncomputable def BK_43 : ℕ := 0x201055241f5a1d181e9986701dcef5701f5a1d181dcef5701dcef5708
noncomputable def BK_44 : ℕ := 0x227afa9e21f169ce215c480620bbd3da21f169ce20bbd3da20bbd3da8
noncomputable def BK_45 : ℕ := 0x2429ede823d05dea236a9cac22f8c50c23d05dea22f8c50c22f8c50c8
noncomputable def BK_46 : ℕ := 0x25154d7c24ece80a24b838f624773a4624ece80a24773a4624773a468
noncomputable def BK_47 : ℕ := 0x253d82c4254571c8254179a0253176f8253d82c4253176f8253176f88
noncomputable def BK_48 : ℕ := 0x2482dc1824c3880824f957942524081a2482dc1824f957942482dc188
noncomputable def BK_49 : ℕ := 0x23197a40238296c623e2140824379bbe23197a4023e2140823197a408
noncomputable def BK_50 : ℕ := 0x211ba18821a7b3f8222ba1c022a705a6211ba188222ba1c0211ba1888
noncomputable def BK_51 : ℕ := 0x1ea233561f4aad461fecb2242087d2a21ea233561fecb2241ea233568
noncomputable def BK_52 : ℕ := 0x1bc8a26a1c8678c21d3fa5f41df3b5621bc8a26a1d3fa5f41bc8a26a8
noncomputable def BK_53 : ℕ := 0x18abd92c1977be041a40cf781b06982418abd92c1a40cf7818abd92c8
noncomputable def BK_54 : ℕ := 0x15691992163bc372170d683217dd95d615691992170d6832156919928
noncomputable def BK_55 : ℕ := 0x121cee5412ef599613c276c41495db10121cee5413c276c4121cee548
noncomputable def BK_56 : ℕ := 0xeeb377e0fb656ea1083bc681153079e0eeb377e1083bc680eeb377e8
noncomputable def BK_57 : ℕ := 0xbdc90ba0c9b13000d5d3d0c0e22bb7e0bdc90ba0d5d3d0c0bdc90ba8
noncomputable def BK_58 : ℕ := 0x90d190809ba03d00a6bbef00b220602090d19080a6bbef0090d19088
noncomputable def BK_59 : ℕ := 0x68e5c940725aa9e07c2b22008653f04068e5c9407c2b220068e5c948
noncomputable def BK_60 : ℕ := 0x46de0ac04ec94b20571a81e05fcf7de046de0ac0571a81e046de0ac8
noncomputable def BK_61 : ℕ := 0x2b4f26203191f9003840db803f5aad802b4f26203840db802b4f2628
noncomputable def BK_62 : ℕ := 0x1689d6e01b1660202010e06025793fe01689d6e02010e0601689d6e8
noncomputable def BK_63 : ℕ := 0x89c8f200b753a800eb9c980126b1c40089c8f200eb9c980089c8f28
noncomputable def BK_64 : ℕ := 0x15046200286c1a0042480c0062b9f8001504620042480c001504628
noncomputable def BK_65 : ℕ := 0x3f4c0000000000011c9c0007e8aa0000000000011c9c000000008
noncomputable def BK_66 : ℕ := 0x33d22c001ecc82000f12fc0004d4ee001ecc820004d4ee0004d4ee8
noncomputable def BK_67 : ℕ := 0xb8e3e60090b1c4006cf974004df2620090b1c4004df262004df2628
noncomputable def BK_68 : ℕ := 0x181e47a014a13840115cff400e556ce014a138400e556ce00e556ce8
noncomputable def BK_69 : ℕ := 0x27fca92023c37b001fb35c201bd04d8023c37b001bd04d801bd04d88
noncomputable def BK_70 : ℕ := 0x3a2b48e035763a6030da13e02c5adfa035763a602c5adfa02c5adfa8
noncomputable def BK_71 : ℕ := 0x4da875c048b7c24043d009603ef538c048b7c2403ef538c03ef538c8
noncomputable def BK_72 : ℕ := 0x610e38005c1bf6e05723b34052291fe05c1bf6e052291fe052291fe8
noncomputable def BK_73 : ℕ := 0x745426406f9d31c06ad250c065f6d8606f9d31c065f6d86065f6d868
noncomputable def BK_74 : ℕ := 0x8629f34081e1c9a07d797fc078f3f48081e1c9a078f3f48078f3f488
noncomputable def BK_75 : ℕ := 0x95d484e09226eea08e4f10408a4f3ee09226eea08a4f3ee08a4f3ee8
noncomputable def BK_76 : ℕ := 0xa2ba7ca09fca6fe09ca83d409955a2a09fca6fe09955a2a09955a2a8
noncomputable def BK_77 : ℕ := 0xac67be20aa4ea120a7fdf0c0a576ccc0aa4ea120a576ccc0a576ccc8
noncomputable def BK_78 : ℕ := 0xb28f6fe0b15cbd40afef8800ae485060b15cbd40ae485060ae485068
noncomputable def BK_79 : ℕ := 0xb50c7960b4c5c460b4441200b3874760b4c5c460b3874760b3874768
noncomputable def BK_80 : ℕ := 0xb30072c0b3e0c080b488d500b4f7dee0b30072c0b488d500b30072c8
noncomputable def BK_81 : ℕ := 0xad61cf80af184c60b09b16a0b1e8de80ad61cf80b09b16a0ad61cf88
noncomputable def BK_82 : ℕ := 0xa4a0dfa0a716e680a95f8860ab790bc0a4a0dfa0a95f8860a4a0dfa8
noncomputable def BK_83 : ℕ := 0x992863409c4102809f33fce0a1ff4500992863409f33fce099286348
noncomputable def BK_84 : ℕ := 0x8b78c5008f122c00928ec24095ec3e608b78c500928ec2408b78c508
noncomputable def BK_85 : ℕ := 0x7c221e408017256083f8dfc087c4e1807c221e4083f8dfc07c221e48
noncomputable def BK_86 : ℕ := 0x6bbdf8a06fe7b3207407f080781c3b606bbdf8a07407f0806bbdf8a8
noncomputable def BK_87 : ℕ := 0x5ae907605f2052e06357d9c0678d35405ae907606357d9c05ae90768
noncomputable def BK_88 : ℕ := 0x4a3cb5004e5ba94052841bc056b3cb404a3cb50052841bc04a3cb508
noncomputable def BK_89 : ℕ := 0x3a4b21403e2e9a0042240da0462974003a4b214042240da03a4b2148
noncomputable def BK_90 : ℕ := 0x2b9745e02f1fe50032c1eb40367b9ac02b9745e032c1eb402b9745e8
noncomputable def BK_91 : ℕ := 0x1e92c18021a6030024d8cc402829b7001e92c18024d8cc401e92c188
noncomputable def BK_92 : ℕ := 0x1399c9001622c8c018cff9e01ba056e01399c90018cff9e01399c908
noncomputable def BK_93 : ℕ := 0xaf0a8a00ce0aac00ef7f4601135e6c00af0a8a00ef7f4600af0a8a8
noncomputable def BK_94 : ℕ := 0x4c247a00610fea0078874c00928732004c247a0078874c004c247a8
noncomputable def BK_95 : ℕ := 0x11fae8001cb4240029f7240039c6ce0011fae80029f7240011fae88
noncomputable def BK_96 : ℕ := 0xcd9c000408540009c0580000000000040854000000008
noncomputable def BK_97 : ℕ := 0xaa8d40004c9c8000137f20000000a0004c9c80000000a0000000a8
noncomputable def BK_98 : ℕ := 0x37ff0c00298328001d15540012c716002983280012c7160012c7168
noncomputable def BK_99 : ℕ := 0x84f880006f0824005ad5a000487668006f082400487668004876688
noncomputable def BK_100 : ℕ := 0xec5b4e00d059e400b5b8ca009c906600d059e4009c9066009c90668
noncomputable def BK_101 : ℕ := 0x16829180147a51001281a9c0109a40c0147a5100109a40c0109a40c8
noncomputable def BK_102 : ℕ := 0x1f1e17a01ce835c01abb33001898c1601ce835c01898c1601898c168
noncomputable def BK_103 : ℕ := 0x282c6be025e3ff60239dae00215b25c025e3ff60215b25c0215b25c8
noncomputable def BK_104 : ℕ := 0x312ec6e02eeda6c02ca81b402a5fbf002eeda6c02a5fbf002a5fbf08
noncomputable def BK_105 : ℕ := 0x39e8180037c80d80359d80803369e86037c80d803369e8603369e868
noncomputable def BK_106 : ℕ := 0x41e35c603ffb23a03e02fe003bfc33403ffb23a03bfc33403bfc3348
noncomputable def BK_107 : ℕ := 0x48cd53c047307f00457f2e4043ba6e8047307f0043ba6e8043ba6e88
noncomputable def BK_108 : ℕ := 0x4e6100404d1f58c04bc5a4e04a54af404d1f58c04a54af404a54af48
noncomputable def BK_109 : ℕ := 0x5269bac0518ecba0509957e04f89e260518ecba04f89e2604f89e268
noncomputable def BK_110 : ℕ := 0x54c49620545764a053ce5c005329b4e0545764a05329b4e05329b4e8
noncomputable def BK_111 : ℕ := 0x556109805563fc20554aec805515ca00556109805515ca005515ca08
noncomputable def BK_112 : ℕ := 0x53cf6a405460570054d699405531c70053cf6a4054d6994053cf6a48
noncomputable def BK_113 : ℕ := 0x508b8cc05181bdc0525f8ba053244da0508b8cc0525f8ba0508b8cc8
noncomputable def BK_114 : ℕ := 0x4bcdfe004d1e10204e58eac04f7dafa04bcdfe004e58eac04bcdfe08
noncomputable def BK_115 : ℕ := 0x45cc78004767d6c048f1e6a04a699e6045cc780048f1e6a045cc7808
noncomputable def BK_116 : ℕ := 0x3ec7d5a0409d6640426621204420dd203ec7d5a0426621203ec7d5a8
noncomputable def BK_117 : ℕ := 0x37093240390612603afaf5403ce69e80370932403afaf54037093248
noncomputable def BK_118 : ℕ := 0x2eded30030ef21e032fc7860350593e02eded30032fc78602eded308
noncomputable def BK_119 : ℕ := 0x2698f8e028a8a3402aba53c02cccce002698f8e02aba53c02698f8e8
noncomputable def BK_120 : ℕ := 0x1eae63e020a8dfa022aa204024b0fbe01eae63e022aa20401eae63e8
noncomputable def BK_121 : ℕ := 0x171e7be018f2cb801ad241401cbbd040171e7be01ad24140171e7be8
noncomputable def BK_122 : ℕ := 0x1050736011ee6660139b53e0155655e010507360139b53e010507368
noncomputable def BK_123 : ℕ := 0xa7ee0e00bd8cee00d44ddc00ec256000a7ee0e00d44ddc00a7ee0e8
noncomputable def BK_124 : ℕ := 0x5d9100006e44c20080407a00937bf0005d91000080407a005d91008
noncomputable def BK_125 : ℕ := 0x28186e00336b1c00401e18004e2c9c0028186e00401e180028186e8
noncomputable def BK_126 : ℕ := 0x8d10c000e84940015a29c001e29ee0008d10c0015a29c0008d10c8
noncomputable def BK_127 : ℕ := 0x346c0001a9f40004885c000000000001a9f4000000008
noncomputable def BK_128 : ℕ := 0x785d40003ad8800012dd6000010120003ad8800001012000010128
noncomputable def BK_129 : ℕ := 0x23f670001af2cc00132f1a000cb31a001af2cc000cb31a000cb31a8
noncomputable def BK_130 : ℕ := 0x53d06a004628ae00399ae4002e3186004628ae002e3186002e31868
noncomputable def BK_131 : ℕ := 0x948c680082f178007240c0006286fe0082f178006286fe006286fe8
noncomputable def BK_132 : ℕ := 0xe30fc600ce544c00ba4bb000a7045e00ce544c00a7045e00a7045e8
noncomputable def BK_133 : ℕ := 0x13bcea60124de36010e63ec00f86f560124de3600f86f5600f86f568
noncomputable def BK_134 : ℕ := 0x19af1760182c6ec016ad2ee015325820182c6ec01532582015325828
noncomputable def BK_135 : ℕ := 0x1fc7c2801e417c801cba9ea01b3427a01e417c801b3427a01b3427a8
noncomputable def BK_136 : ℕ := 0x25c83e60244e014022cf4de0214d1700244e0140214d1700214d1708
noncomputable def BK_137 : ℕ := 0x2b723a802a12f5e028ab9fa0273d16602a12f5e0273d1660273d1668
noncomputable def BK_138 : ℕ := 0x308e25202f5750c02e1535802cc895602f5750c02cc895602cc89568
noncomputable def BK_139 : ℕ := 0x34eaaba033e7dfc032d719a031b8f88033e7dfc031b8f88031b8f888
noncomputable def BK_140 : ℕ := 0x385ef94037998b0036c4082035dee7c037998b0035dee7c035dee7c8
noncomputable def BK_141 : ℕ := 0x3acc08003a4abee039b7efc03913e6203a4abee03913e6203913e628
noncomputable def BK_142 : ℕ := 0x3c1d89603be46f403b990fe03b3b8a203be46f403b3b8a203b3b8a28
noncomputable def BK_143 : ℕ := 0x3c4a62a03c5aaec03c58ab803c444ae03c4a62a03c444ae03c444ae8
noncomputable def BK_144 : ℕ := 0x3b0f4a203b7b01603bd547603c1dd6603b0f4a203bd547603b0f4a28
noncomputable def BK_145 : ℕ := 0x38b8cee03966cba03a04d0a03a92714038b8cee03a04d0a038b8cee8
noncomputable def BK_146 : ℕ := 0x356ae0c03653ce60372ecda037fb5020356ae0c0372ecda0356ae0c8
noncomputable def BK_147 : ℕ := 0x31480020326283a033719ac034749b203148002033719ac031480028
noncomputable def BK_148 : ℕ := 0x2c79c8602dbae8002ef37a603022c0802c79c8602ef37a602c79c868
noncomputable def BK_149 : ℕ := 0x272f2fc0288ac7a029e0f0602b30de60272f2fc029e0f060272f2fc8
noncomputable def BK_150 : ℕ := 0x219a9f402303de00246aeb6025cef6a0219a9f40246aeb60219a9f48
noncomputable def BK_151 : ℕ := 0x1beff5c01d59dcc01ec4cf20202fffa01beff5c01ec4cf201beff5c8
noncomputable def BK_152 : ℕ := 0x1668c6e017c67b80192857c01a8d99201668c6e0192857c01668c6e8
noncomputable def BK_153 : ℕ := 0x112a2620126ff50013bccb60150ff8a0112a262013bccb60112a2628
noncomputable def BK_154 : ℕ := 0xc663fa00d897b000eb646c00fec0a400c663fa00eb646c00c663fa8
noncomputable def BK_155 : ℕ := 0x843eec0093b7ea00a3eba600b4d26800843eec00a3eba600843eec8
noncomputable def BK_156 : ℕ := 0x4e2f2c005a7a1a00679990007587e6004e2f2c00679990004e2f2c8
noncomputable def BK_157 : ℕ := 0x25aea0002e79e600382aca0042bde20025aea000382aca0025aea08
noncomputable def BK_158 : ℕ := 0xbaa540010c8460016d3d2001dcbd8000baa540016d3d2000baa548
noncomputable def BK_159 : ℕ := 0x7d220001e4d2000438e800077a8c00007d22000438e800007d228
noncomputable def BK_160 : ℕ := 0x186420000520200000000000000200000520200000000000000008
noncomputable def BK_161 : ℕ := 0xf0166000a5e720006908000039c5a000a5e7200039c5a00039c5a8
noncomputable def BK_162 : ℕ := 0x296f900021b192001ab0e40014741e0021b1920014741e0014741e8
noncomputable def BK_163 : ℕ := 0x4f3b300044d1a0003b07280031e3e40044d1a00031e3e40031e3e48
noncomputable def BK_164 : ℕ := 0x7e6b840071dcba0065c99c005a3b6c0071dcba005a3b6c005a3b6c8
noncomputable def BK_165 : ℕ := 0xb4ba6400a69de40098d5e6008b6c7a00a69de4008b6c7a008b6c7a8
noncomputable def BK_166 : ℕ := 0xefac5600e0a49a00d1c81600c3213800e0a49a00c3213800c321388
noncomputable def BK_167 : ℕ := 0x12caa20011d5e24010e139200fed4d0011d5e2400fed4d000fed4d08
noncomputable def BK_168 : ℕ := 0x1691cc6015a315a014b1ea2013bee9a015a315a013bee9a013bee9a8
noncomputable def BK_169 : ℕ := 0x1a27fea019491f60186569e0177d714019491f60177d7140177d7148
noncomputable def BK_170 : ℕ := 0x1d6831401ca215801bd502401b0178801ca215801b0178801b017888
noncomputable def BK_171 : ℕ := 0x203199a01f8bfb601edd97c01e26d9801f8bfb601e26d9801e26d988
noncomputable def BK_172 : ℕ := 0x2268e4c021ea07c02160faa020ce0e2021ea07c020ce0e2020ce0e28
noncomputable def BK_173 : ℕ := 0x23f920c023a59de02346ef0022dd482023a59de022dd482022dd4828
noncomputable def BK_174 : ℕ := 0x24d4636024af0640247df68024414ac024af064024414ac024414ac8
noncomputable def BK_175 : ℕ := 0x24f4276024fddd6024fbd28024edff4024f4276024edff4024edff48
noncomputable def BK_176 : ℕ := 0x242b17402470058024a9bca024d81020242b174024a9bca0242b1748
noncomputable def BK_177 : ℕ := 0x22ab9fe0231b260023806a2023db258022ab9fe023806a2022ab9fe8
noncomputable def BK_178 : ℕ := 0x208d4e202122a0c021af07a0223224e0208d4e2021af07a0208d4e28
noncomputable def BK_179 : ℕ := 0x1de6d0a01e9bc5801f4976601fef72c01de6d0a01f4976601de6d0a8
noncomputable def BK_180 : ℕ := 0x1ad3a9a01ba0fc001c68f1e01d2b0cc01ad3a9a01c68f1e01ad3a9a8
noncomputable def BK_181 : ℕ := 0x177304001850a2e0192af8401a017c8017730400192af84017730408
noncomputable def BK_182 : ℕ := 0x13e66b4014cbcd6015b00ee01692a4a013e66b4015b00ee013e66b48
noncomputable def BK_183 : ℕ := 0x105073401134ee00121a71201300738010507340121a712010507348
noncomputable def BK_184 : ℕ := 0xce4d3a00dbf7ea00e9d41e00f7d9b800ce4d3a00e9d41e00ce4d3a8
noncomputable def BK_185 : ℕ := 0x9a2db400a6c4c800b3ac0000c0dc00009a2db400b3ac00009a2db48
noncomputable def BK_186 : ℕ := 0x6b7d5400768f3c00820c32008dede2006b7d5400820c32006b7d548
noncomputable def BK_187 : ℕ := 0x43d856004d04c80056b28a0060dc860043d8560056b28a0043d8568
noncomputable def BK_188 : ℕ := 0x248d22002b8880003315fc003b31f200248d22003315fc00248d228
noncomputable def BK_189 : ℕ := 0xe90f0001326c20018598e001e2730000e90f00018598e000e90f08
noncomputable def BK_190 : ℕ := 0x2781400048ca4000742bc000a99d000027814000742bc000278148
noncomputable def BK_191 : ℕ := 0x3200000000000033be0001053200000000000033be000000008
noncomputable def BK_192 : ℕ := 0x50eb80002e22e00014f4e0000586c0002e22e0000586c0000586c8
noncomputable def BK_193 : ℕ := 0x138d58000f1562000b2b540007d2b6000f15620007d2b60007d2b68
noncomputable def BK_194 : ℕ := 0x2aa68600242096001e174600188f5e0024209600188f5e00188f5e8
noncomputable def BK_195 : ℕ := 0x4933920040f042003913d00031a40a0040f0420031a40a0031a40a8
noncomputable def BK_196 : ℕ := 0x6dc9ae0064294a005ad66e0051d7b60064294a0051d7b60051d7b68
noncomputable def BK_197 : ℕ := 0x96c92a008c37aa0081d7d60077b0d6008c37aa0077b0d60077b0d68
noncomputable def BK_198 : ℕ := 0xc26e8000b75f2800ac643c00a1852000b75f2800a1852000a185208
noncomputable def BK_199 : ℕ := 0xeee46200e3cd2c00d8ace400cd8ae000e3cd2c00cd8ae000cd8ae08
noncomputable def BK_200 : ℕ := 0x11a5cb8010fb1180104dfd800f9eff8010fb11800f9eff800f9eff88
noncomputable def BK_201 : ℕ := 0x1430ba4013939ce012f27bc0124dbda013939ce0124dbda0124dbda8
noncomputable def BK_202 : ℕ := 0x1675750015ec28c0155d5ee014c9706015ec28c014c9706014c97068
noncomputable def BK_203 : ℕ := 0x185d4d6017ed25201776426016f8ee0017ed252016f8ee0016f8ee08
noncomputable def BK_204 : ℕ := 0x19d598801982d4a01928624018c676e01982d4a018c676e018c676e8
noncomputable def BK_205 : ℕ := 0x1ad056601a9dffa01a6356e01a207d001a9dffa01a207d001a207d08
noncomputable def BK_206 : ℕ := 0x1b44a7c01b3476401b1ba5201afa3fa01b3476401afa3fa01afa3fa8
noncomputable def BK_207 : ℕ := 0x1b2f10001b4160201b4b1a401b4c33e01b2f10001b4b1a401b2f1008
noncomputable def BK_208 : ℕ := 0x1a704a401aad81e01ae29a601b0f6e801a704a401ae29a601a704a48
noncomputable def BK_209 : ℕ := 0x192dcbe01989a8a019de2c201a2b1e00192dcbe019de2c20192dcbe8
noncomputable def BK_210 : ℕ := 0x1779dc0017f093c01860fe4018cad2c01779dc001860fe401779dc08
noncomputable def BK_211 : ℕ := 0x15662bc015f2f6e0167abbc016fd240015662bc0167abbc015662bc8
noncomputable def BK_212 : ℕ := 0x1307e46013a530e0143eeba014d4b4001307e460143eeba01307e468
noncomputable def BK_213 : ℕ := 0x1076c9a0111e752011c421a0126768a01076c9a011c421a01076c9a8
noncomputable def BK_214 : ℕ := 0xdcc46400e77dc600f2314c00fcd86c00dcc46400f2314c00dcc4648
noncomputable def BK_215 : ℕ := 0xb226c800bcb67000c75a3a00d20bb400b226c800c75a3a00b226c88
noncomputable def BK_216 : ℕ := 0x8a806200947924009e9e7c00a8ea5e008a8062009e9e7c008a80628
noncomputable def BK_217 : ℕ := 0x64cf3c006ddc0200772c1e0080ba1e0064cf3c00772c1e0064cf3c8
noncomputable def BK_218 : ℕ := 0x43a3ee004b70a800539496005c0b120043a3ee005394960043a3ee8
noncomputable def BK_219 : ℕ := 0x282e12002e741600352192003c32d600282e120035219200282e128
noncomputable def BK_220 : ℕ := 0x13613c0017e9ca001ce5e6002252f40013613c001ce5e60013613c8
noncomputable def BK_221 : ℕ := 0x5ec7600089296000bb3c2000f4e8c0005ec76000bb3c20005ec768
noncomputable def BK_222 : ℕ := 0x347a0000e628000215920003c2840000347a000215920000347a8
noncomputable def BK_223 : ℕ := 0xfa1600003e5c000000000000000000003e5c00000000000000008
noncomputable def BK_224 : ℕ := 0x8ab7600060c340003e334000231b800060c34000231b8000231b88
noncomputable def BK_225 : ℕ := 0x179a240013391c000f446c000bbefe0013391c000bbefe000bbefe8
noncomputable def BK_226 : ℕ := 0x2d17140027269400219464001c645e00272694001c645e001c645e8
noncomputable def BK_227 : ℕ := 0x4833b80040f4b0003a0280003361ce0040f4b0003361ce003361ce8
noncomputable def BK_228 : ℕ := 0x67cdb8005f8cf8005784ea004fbaca005f8cf8004fbaca004fbaca8
noncomputable def BK_229 : ℕ := 0x8a9a9e0081add60078e3ac007041c60081add6007041c6007041c68
noncomputable def BK_230 : ℕ := 0xaf350800a5f754009cc5260093a45000a5f7540093a4500093a4508
noncomputable def BK_231 : ℕ := 0xd42a8e00caf8fa00c1bbac00b8786c00caf8fa00b8786c00b8786c8
noncomputable def BK_232 : ℕ := 0xf7741a00ee9dba00e5a4e400dc8f1e00ee9dba00dc8f1e00dc8f1e8
noncomputable def BK_233 : ℕ := 0x1190a5e0110f2da0108a3ea0100229c0110f2da0100229c0100229c8
noncomputable def BK_234 : ℕ := 0x136dea2012fd42c01287fae0120e58e012fd42c0120e58e0120e58e8
noncomputable def BK_235 : ℕ := 0x14fd344014a18de014404e2013d9ade014a18de013d9ade013d9ade8
noncomputable def BK_236 : ℕ := 0x162fd76015ec894015a2e20015530ba015ec894015530ba015530ba8
noncomputable def BK_237 : ℕ := 0x16fad6c016d241c016a2d3a0166ca64016d241c0166ca640166ca648
noncomputable def BK_238 : ℕ := 0x17574380174abe6017372420171c7d40174abe60171c7d40171c7d48
noncomputable def BK_239 : ℕ := 0x17426ca0175237a0175afd40175caf4017426ca0175afd4017426ca8
noncomputable def BK_240 : ℕ := 0x16a5312016d781a01703296017280ac016a531201703296016a53128
noncomputable def BK_241 : ℕ := 0x159c2fe015e7ae00162d2020166c5980159c2fe0162d2020159c2fe8
noncomputable def BK_242 : ℕ := 0x1435b5e01497608014f3d3e0154ad6001435b5e014f3d3e01435b5e8
noncomputable def BK_243 : ℕ := 0x127fcc6012f3d8601363b0c013cf10c0127fcc601363b0c0127fcc68
noncomputable def BK_244 : ℕ := 0x108b43e0110d4380118c37c01207d3c0108b43e0118c37c0108b43e8
noncomputable def BK_245 : ℕ := 0xe6b06a00ef617200f7f5d40100687200e6b06a00f7f5d400e6b06a8
noncomputable def BK_246 : ℕ := 0xc335a200cc254800d50d1e00dde7e800c335a200d50d1e00c335a28
noncomputable def BK_247 : ℕ := 0x9f914e00a86c1000b153d000ba4368009f914e00b153d0009f914e8
noncomputable def BK_248 : ℕ := 0x7db01c0086207a008eb1aa00975ecc007db01c008eb1aa007db01c8
noncomputable def BK_249 : ℕ := 0x5d94860065530e006d44ca00756552005d9486006d44ca005d94868
noncomputable def BK_250 : ℕ := 0x40eda00047b626004ec20600560d780040eda0004ec2060040eda08
noncomputable def BK_251 : ℕ := 0x28b2ba002e4b80003434f8003a6c180028b2ba003434f80028b2ba8
noncomputable def BK_252 : ℕ := 0x15ac260019e7e8001e7e6a00236d7e0015ac26001e7e6a0015ac268
noncomputable def BK_253 : ℕ := 0x86c54000b2bd0000e4c7e0011cd1800086c54000e4c7e00086c548
noncomputable def BK_254 : ℕ := 0x14b1c00027e08000414c800060f1000014b1c000414c800014b1c8
noncomputable def BK_255 : ℕ := 0x6ee00000000000010ba00007c1200000000000010ba000000008
noncomputable def BK_256 : ℕ := 0x3a30200022ca40001150600005d3800022ca400005d3800005d388
noncomputable def BK_257 : ℕ := 0xd0d72000a2dde0007a5820005768e000a2dde0005768e0005768e8
noncomputable def BK_258 : ℕ := 0x1bc0f400179e740013c86c001041d400179e74001041d4001041d48
noncomputable def BK_259 : ℕ := 0x2f06900029d3200024deaa00202ccc0029d32000202ccc00202ccc8
noncomputable def BK_260 : ℕ := 0x45fd78003ff4ba003a1b4a0034753c003ff4ba0034753c0034753c8
noncomputable def BK_261 : ℕ := 0x5fa45c0059092600528bfe004c315200590926004c3152004c31528
noncomputable def BK_262 : ℕ := 0x7ae3ae0073fd5e006d2300006659260073fd5e00665926006659268
noncomputable def BK_263 : ℕ := 0x9698bc008fb06e0088c1c80081d158008fb06e0081d1580081d1588
noncomputable def BK_264 : ℕ := 0xb17c0400aad3c600a4134a009d3ef000aad3c6009d3ef0009d3ef08
noncomputable def BK_265 : ℕ := 0xcad64800c4b8ec00be72be00b807be00c4b8ec00b807be00b807be8
noncomputable def BK_266 : ℕ := 0xe167d800dc134800d6872600d0c6f200dc134800d0c6f200d0c6f28
noncomputable def BK_267 : ℕ := 0xf446c600eff2a800eb5aee00e6818400eff2a800e6818400e681848
noncomputable def BK_268 : ℕ := 0x102c0c200ff93ce00fc19ba00f8549e00ff93ce00f8549e00f8549e8
noncomputable def BK_269 : ℕ := 0x10c4e76010a66f001082bea01059eb2010a66f001059eb201059eb28
noncomputable def BK_270 : ℕ := 0x11097620110066e010f1ef8010de16e0110066e010de16e010de16e8
noncomputable def BK_271 : ℕ := 0x10f78e40110420c0110b5180110d19a010f78e40110b518010f78e48
noncomputable def BK_272 : ℕ := 0x107ceaa010a403c010c6040010e2d400107ceaa010c60400107ceaa8
noncomputable def BK_273 : ℕ := 0xfafce200fea2300101fdb201050d3400fafce20101fdb200fafce28
noncomputable def BK_274 : ℕ := 0xe9b82c00ee6b0800f2deaa00f7103000e9b82c00f2deaa00e9b82c8
noncomputable def BK_275 : ℕ := 0xd4b31000da433200dfa10400e4c91c00d4b31000dfa10400d4b3108
noncomputable def BK_276 : ℕ := 0xbcc3ba00c2f8b600c90a2200cef42a00bcc3ba00c90a2200bcc3ba8
noncomputable def BK_277 : ℕ := 0xa2db4a00a976d200affec800b66f1800a2db4a00affec800a2db4a8
noncomputable def BK_278 : ℕ := 0x87fc3c008ebc9c00957a06009c304e0087fc3c00957a060087fc3c8
noncomputable def BK_279 : ℕ := 0x6d30540073d2fe007a834600813d12006d3054007a8346006d30548
noncomputable def BK_280 : ℕ := 0x545a18005a981c0060f35c006767f600545a180060f35c00545a188
noncomputable def BK_281 : ℕ := 0x3cd070004274b4004844c0004e3d12003cd070004844c0003cd0708
noncomputable def BK_282 : ℕ := 0x2836a4002d0b5c0032189400375b50002836a400321894002836a48
noncomputable def BK_283 : ℕ := 0x174f3a001b2718001f41e600239d4200174f3a001f41e600174f3a8
noncomputable def BK_284 : ℕ := 0xab676000d6e58001070e80013bc7c000ab676001070e8000ab6768
noncomputable def BK_285 : ℕ := 0x2dc4800045c8c00062c6200084ac20002dc4800062c620002dc488
noncomputable def BK_286 : ℕ := 0x27a00003f2e0000cd2c0001ac520000027a0000cd2c0000027a8
noncomputable def BK_287 : ℕ := 0x12fb200007a74000016040000000000007a7400000000000000008
noncomputable def BK_288 : ℕ := 0x71568000528980003881a000234b200052898000234b2000234b28
noncomputable def BK_289 : ℕ := 0x11a55a000e96f4000bce3e00094d26000e96f400094d2600094d268
noncomputable def BK_290 : ℕ := 0x206bde001c5d1600188abc0014f75c001c5d160014f75c0014f75c8
noncomputable def BK_291 : ℕ := 0x32cbba002de756002933e00024b468002de7560024b4680024b4688
noncomputable def BK_292 : ℕ := 0x48059200427e36003d1a7e0037ddde00427e360037ddde0037ddde8
noncomputable def BK_293 : ℕ := 0x5f3f9600594dbc005370fa004dad0800594dbc004dad08004dad088
noncomputable def BK_294 : ℕ := 0x778e0600716dce006b5370006542c000716dce006542c0006542c08
noncomputable def BK_295 : ℕ := 0x8ffc640089eb3e0083d094007db03a0089eb3e007db03a007db03a8
noncomputable def BK_296 : ℕ := 0xa6eec800a11f24009b371400953a4000a11f2400953a4000953a408
noncomputable def BK_297 : ℕ := 0xbcf29800b7a7b400b2368800aca26a00b7a7b400aca26a00aca26a8
noncomputable def BK_298 : ℕ := 0xd0600e00cbcda400c708a400c213f200cbcda400c213f200c213f28
noncomputable def BK_299 : ℕ := 0xe07a4e00dccca800d8e22400d4bd1a00dccca800d4bd1a00d4bd1a8
noncomputable def BK_300 : ℕ := 0xeca65600ea00b200e7164c00e3e8de00ea00b200e3e8de00e3e8de8
noncomputable def BK_301 : ℕ := 0xf470aa00f2ebf200f11d4400ef05a800f2ebf200ef05a800ef05a88
noncomputable def BK_302 : ℕ := 0xf7916e00f73b5a00f698f400f5aa9000f73b5a00f5aa9000f5aa908
noncomputable def BK_303 : ℕ := 0xf5eebe00f6c96400f7584e00f79b1000f5eebe00f7584e00f5eebe8
noncomputable def BK_304 : ℕ := 0xee9af200f0e51e00f2e84c00f4a33400ee9af200f2e84c00ee9af28
noncomputable def BK_305 : ℕ := 0xe2cc3000e6220600e937b200ec0b4400e2cc3000e937b200e2cc308
noncomputable def BK_306 : ℕ := 0xd31bfc00d75e3000db688e00df384a00d31bfc00db688e00d31bfc8
noncomputable def BK_307 : ℕ := 0xc0211c00c524c800c9fc7600cea52600c0211c00c9fc7600c0211c8
noncomputable def BK_308 : ℕ := 0xaa998200b02d6c00b5a23600baf48800aa998200b5a23600aa99828
noncomputable def BK_309 : ℕ := 0x93578800994556009f21f800a4e9de00935788009f21f8009357888
noncomputable def BK_310 : ℕ := 0x7b3cf400814b3a008756d8008d5c2a007b3cf4008756d8007b3cf48
noncomputable def BK_311 : ℕ := 0x633250006926c2006f271600752fb200633250006f2716006332508
noncomputable def BK_312 : ℕ := 0x4c940800522f6a0057e49a005db032004c94080057e49a004c94088
noncomputable def BK_313 : ℕ := 0x376a14003c7dae0041b7f4004715cc00376a140041b7f400376a148
noncomputable def BK_314 : ℕ := 0x24d87400293498002dc2b20032801e0024d874002dc2b20024d8748
noncomputable def BK_315 : ℕ := 0x158c6c0019089c001cc0200020b0d400158c6c001cc02000158c6c8
noncomputable def BK_316 : ℕ := 0xa128e000c8f02000f4dda00124d8e000a128e000f4dda000a128e8
noncomputable def BK_317 : ℕ := 0x2d1c0000438800005e62c0007d9e00002d1c00005e62c0002d1c08
noncomputable def BK_318 : ℕ := 0x79a00004d420000dbaa0001b29e0000079a0000dbaa0000079a8
noncomputable def BK_319 : ℕ := 0xea14000055e800000a6c00000000000055e800000000000000008
noncomputable def BK_320 : ℕ := 0x5ffee000451fa0002e9320001c646000451fa0001c6460001c6468
noncomputable def BK_321 : ℕ := 0xf525e000c9caa000a26a60007f1ec000c9caa0007f1ec0007f1ec8
noncomputable def BK_322 : ℕ := 0x1c80f00018df64001575b2001246020018df6400124602001246028
noncomputable def BK_323 : ℕ := 0x2d060a00289d2e0024624e0020580c00289d2e0020580c0020580c8
noncomputable def BK_324 : ℕ := 0x403d10003b38a0003656a400319a24003b38a000319a2400319a248
noncomputable def BK_325 : ℕ := 0x5568ce004ffa00004aa0f0004560e4004ffa00004560e4004560e48
noncomputable def BK_326 : ℕ := 0x6bbab00066165e00607a5a005aea0a0066165e005aea0a005aea0a8
noncomputable def BK_327 : ℕ := 0x825aaa007cb74a00770e90007163e4007cb74a007163e4007163e48
noncomputable def BK_328 : ℕ := 0x97bec000924ab2008cc3f800872de200924ab200872de200872de28
noncomputable def BK_329 : ℕ := 0xac948800a78ae400a26200009d1cea00a78ae4009d1cea009d1cea8
noncomputable def BK_330 : ℕ := 0xbf489600bad8ba00b63e4800b17bf400bad8ba00b17bf400b17bf48
noncomputable def BK_331 : ℕ := 0xcf2c1200cb7f5000c79e4e00c38b4400cb7f5000c38b4400c38b448
noncomputable def BK_332 : ℕ := 0xdbac1600d8e43c00d5e07400d2a27200d8e43c00d2a27200d2a2728
noncomputable def BK_333 : ℕ := 0xe456e800e28d0a00e081d800de366e00e28d0a00de366e00de366e8
noncomputable def BK_334 : ℕ := 0xe8dfda00e8238200e722e000e5de7400e8238200e5de7400e5de748
noncomputable def BK_335 : ℕ := 0xe921d200e9787c00e98a7200e9578e00e921d200e9578e00e921d28
noncomputable def BK_336 : ℕ := 0xe4292000e5d3b600e73c9a00e862e200e4292000e73c9a00e429208
noncomputable def BK_337 : ℕ := 0xdb055200ddaa9800e0134a00e23dea00db055200e0134a00db05528
noncomputable def BK_338 : ℕ := 0xce351000d1bb0800d50bb800d8251c00ce351000d50bb800ce35108
noncomputable def BK_339 : ℕ := 0xbe348e00c2794800c691e400ca7bf000be348e00c691e400be348e8
noncomputable def BK_340 : ℕ := 0xab9c9600b0778400b530fe00b9c64000ab9c9600b530fe00ab9c968
noncomputable def BK_341 : ℕ := 0x971c90009c601200a18dea00a6a31600971c9000a18dea00971c908
noncomputable def BK_342 : ℕ := 0x8173ba0086eee8008c60de0091c676008173ba008c60de008173ba8
noncomputable def BK_343 : ℕ := 0x6b69f40070ea7200766e56007bf27c006b69f400766e56006b69f48
noncomputable def BK_344 : ℕ := 0x55c7ee005b1bc400607f580065efa00055c7ee00607f580055c7ee8
noncomputable def BK_345 : ℕ := 0x4150da0046486e004b5b5c005086d0004150da004b5b5c004150da8
noncomputable def BK_346 : ℕ := 0x2eb964003329160037be90003c7758002eb9640037be90002eb9648
noncomputable def BK_347 : ℕ := 0x1ea29200226454002654c8002a71dc001ea292002654c8001ea2928
noncomputable def BK_348 : ℕ := 0x119398001488500017b2ca001b1172001193980017b2ca001193988
noncomputable def BK_349 : ℕ := 0x7f52c000a05c0000c5110000ed6120007f52c000c51100007f52c8
noncomputable def BK_350 : ℕ := 0x20dfa00032c14000487a60006203800020dfa000487a600020dfa8
noncomputable def BK_351 : ℕ := 0x78000026f200008b4e00012da80000007800008b4e000000788
noncomputable def BK_352 : ℕ := 0xfcbc00006be00000179a0000000000006be000000000000000008
noncomputable def BK_353 : ℕ := 0x58e54000413500002d1560001c97e000413500001c97e0001c97e8
noncomputable def BK_354 : ℕ := 0xd9a8c000b48ce00092a7c0007412a000b48ce0007412a0007412a8
noncomputable def BK_355 : ℕ := 0x18c0040015b2b60012d15e00101e000015b2b600101e0000101e008
noncomputable def BK_356 : ℕ := 0x26812e0022da16001f55f4001bf72c0022da16001bf72c001bf72c8
noncomputable def BK_357 : ℕ := 0x36494a00322f74002e2e68002a48ca00322f74002a48ca002a48ca8
noncomputable def BK_358 : ℕ := 0x47725000431086003ebc92003a793c00431086003a793c003a793c8
noncomputable def BK_359 : ℕ := 0x594b5e0054ce7e00505422004bdf220054ce7e004bdf22004bdf228
noncomputable def BK_360 : ℕ := 0x6b0e1e0066a2ba00622e9a005db4880066a2ba005db488005db4888
noncomputable def BK_361 : ℕ := 0x7c2dda0078008a0073bfb8006f6e060078008a006f6e06006f6e068
noncomputable def BK_362 : ℕ := 0x8bed920088275a008443ba008045160088275a00804516008045168
noncomputable def BK_363 : ℕ := 0x99b3ee0096795c009318be008f941a0096795c008f941a008f941a8
noncomputable def BK_364 : ℕ := 0xa4fcb600a26c96009faf52009cc68600a26c96009cc686009cc6868
noncomputable def BK_365 : ℕ := 0xad5d8a00ab8fd000a98fa600a75e3200ab8fd000a75e3200a75e328
noncomputable def BK_366 : ℕ := 0xb2898400b18e7e00b05db600aef7cc00b18e7e00aef7cc00aef7cc8
noncomputable def BK_367 : ℕ := 0xb453c000b4339000b3dc5c00b34e4400b4339000b34e4400b34e448
noncomputable def BK_368 : ℕ := 0xb1efe000b2e0d400b39c1800b4212600b1efe000b39c1800b1efe08
noncomputable def BK_369 : ℕ := 0xac224600ade22200af6fae00b0c9e600ac224600af6fae00ac22468
noncomputable def BK_370 : ℕ := 0xa3443a00a5c0ce00a8104c00aa313e00a3443a00a8104c00a3443a8
noncomputable def BK_371 : ℕ := 0x97b002009ad038009dca3800a09c240097b002009dca380097b0028
noncomputable def BK_372 : ℕ := 0x89d8f2008d7ddc009104c600946b840089d8f2009104c60089d8f28
noncomputable def BK_373 : ℕ := 0x7a46bc007e4ccc00823e1a00861844007a46bc00823e1a007a46bc8
noncomputable def BK_374 : ℕ := 0x699014006dd0860072061e00762e5c006990140072061e006990148
noncomputable def BK_375 : ℕ := 0x5854ca005ca7240060f8d600654756005854ca0060f8d6005854ca8
noncomputable def BK_376 : ℕ := 0x474030004b7b92004fc06400540c2800474030004fc064004740308
noncomputable def BK_377 : ℕ := 0x36e19e003adf0c003eef86004310b20036e19e003eef860036e19e8
noncomputable def BK_378 : ℕ := 0x27d6f8002b720c002f28ec0032f9800027d6f8002f28ec0027d6f88
noncomputable def BK_379 : ℕ := 0x1aa7cc001dc04e0020fc32002459b4001aa7cc0020fc32001aa7cc8
noncomputable def BK_380 : ℕ := 0xfc7ee001242fe0014e79a0017b45e000fc7ee0014e79a000fc7ee8
noncomputable def BK_381 : ℕ := 0x7935a00095c66000b5382000d77b60007935a000b53820007935a8
noncomputable def BK_382 : ℕ := 0x24b000003547800048eb60005f93600024b0000048eb600024b008
noncomputable def BK_383 : ℕ := 0x12ac0000566c0000cbc4000172ae000012ac0000cbc4000012ac8
noncomputable def BK_384 : ℕ := 0x6f6a00001f720000006a0000000000001f7200000000000000008
noncomputable def BK_385 : ℕ := 0x38e1800027ff00001a0440000efde00027ff00000efde0000efde8
noncomputable def BK_386 : ℕ := 0x984680007c62c000632420004c9de0007c62c0004c9de0004c9de8
noncomputable def BK_387 : ℕ := 0x12095e000fafae000d7a98000b6bae000fafae000b6bae000b6bae8
noncomputable def BK_388 : ℕ := 0x1cbc200019e13c001723e8001486060019e13c00148606001486068
noncomputable def BK_389 : ℕ := 0x2927e40025ea9c0022c2d6001fb2a80025ea9c001fb2a8001fb2a88
noncomputable def BK_390 : ℕ := 0x36c8a200334b22002fda58002c788800334b22002c7888002c78888
noncomputable def BK_391 : ℕ := 0x45104e004176ba003de0ba003a5098004176ba003a5098003a50988
noncomputable def BK_392 : ℕ := 0x536c80004fdb9a004c451a0048ab48004fdb9a0048ab480048ab488
noncomputable def BK_393 : ℕ := 0x614b72005de732005a74820056f58c005de7320056f58c0056f58c8
noncomputable def BK_394 : ℕ := 0x6e226e006b0ca00067e03600649f24006b0ca000649f2400649f248
noncomputable def BK_395 : ℕ := 0x7972680076c96e007402a200711fb60076c96e00711fb600711fb68
noncomputable def BK_396 : ℕ := 0x82cce00080aa94007e647a007bfbee0080aa94007bfbee007bfbee8
noncomputable def BK_397 : ℕ := 0x89d7da0088509e0086a1080084ca160088509e0084ca160084ca168
noncomputable def BK_398 : ℕ := 0x8e5112008d7318008c69d4008b35da008d7318008b35da008b35da8
noncomputable def BK_399 : ℕ := 0x901034008fe30e008f895c008f0348008fe30e008f0348008f03488
noncomputable def BK_400 : ℕ := 0x8e6dd6008f1dec008fa24c008ffa8e008e6dd6008fa24c008e6dd68
noncomputable def BK_401 : ℕ := 0x8a0384008b5c9c008c8c88008d9282008a0384008c8c88008a03848
noncomputable def BK_402 : ℕ := 0x8316a800850a9a0086d97c00888226008316a80086d97c008316a88
noncomputable def BK_403 : ℕ := 0x79ee7c007c695e007ec4ac0080fee80079ee7c007ec4ac0079ee7c8
noncomputable def BK_404 : ℕ := 0x6ee74c0071d0440074a04600775594006ee74c0074a046006ee74c8
noncomputable def BK_405 : ℕ := 0x626eb20065a8f40068d1c2006be72c00626eb20068d1c200626eb28
noncomputable def BK_406 : ℕ := 0x54ff3a00586b2e005bcdc8005f24f80054ff3a005bcdc80054ff3a8
noncomputable def BK_407 : ℕ := 0x471b8e004a980e004e139200518bfe00471b8e004e139200471b8e8
noncomputable def BK_408 : ℕ := 0x394960003cb500004027f20043a02800394960004027f2003949608
noncomputable def BK_409 : ℕ := 0x2c0c4a002f469c003290300035e71a002c0c4a00329030002c0c4a8
noncomputable def BK_410 : ℕ := 0x1fe0d20022cba00025ccfa0028e322001fe0d20025ccfa001fe0d28
noncomputable def BK_411 : ℕ := 0x1537b20017b826001a557e001d0e3c001537b2001a557e001537b28
noncomputable def BK_412 : ℕ := 0xc71b6000e7152001092fc0012d586000c71b6001092fc000c71b68
noncomputable def BK_413 : ℕ := 0x5dc36000749a00008dce8000a953e0005dc360008dce80005dc368
noncomputable def BK_414 : ℕ := 0x1ae4c00027df0000375c8000495620001ae4c000375c80001ae4c8
noncomputable def BK_415 : ℕ := 0x70400003374000088dc0001073000000704000088dc000007048
noncomputable def BK_416 : ℕ := 0x7672000028ba0000038000000000000028ba00000000000000008
noncomputable def BK_417 : ℕ := 0x339de00024e9a000189e00000ec4e00024e9a0000ec4e0000ec4e8
noncomputable def BK_418 : ℕ := 0x8589c0006db440005810c00044af40006db4400044af400044af48
noncomputable def BK_419 : ℕ := 0xf96fe000d987a000bb8660009f80a000d987a0009f80a0009f80a8
noncomputable def BK_420 : ℕ := 0x18a52e00163b2e0013e9cc0011b29200163b2e0011b2920011b2928
noncomputable def BK_421 : ℕ := 0x23227e00206690001dbc8a001b262e00206690001b262e001b262e8
noncomputable def BK_422 : ℕ := 0x2ea13c002bafc80028c8ee0025ee8e002bafc80025ee8e0025ee8e8
noncomputable def BK_423 : ℕ := 0x3aab080037a23800349c5e00319b660037a23800319b6600319b668
noncomputable def BK_424 : ℕ := 0x46c5700043c3fe0040bdd8003db4e20043c3fe003db4e2003db4e28
noncomputable def BK_425 : ℕ := 0x52769e004f9ab2004cb2a40049c046004f9ab20049c0460049c0468
noncomputable def BK_426 : ℕ := 0x5d4a10005ab00a00580304005544a4005ab00a005544a4005544a48
noncomputable def BK_427 : ℕ := 0x66d4e80064965e00623ec0005fcf7c0064965e005fcf7c005fcf7c8
noncomputable def BK_428 : ℕ := 0x6eb9f6006cecba006b015a0068f900006cecba0068f9000068f9008
noncomputable def BK_429 : ℕ := 0x74ad1c007362700071f5c8007067fc00736270007067fc007067fc8
noncomputable def BK_430 : ℕ := 0x78760a0077ba0a0076d98a0075d5080077ba0a0075d5080075d5088
noncomputable def BK_431 : ℕ := 0x79f23a0079cb6800797f0000790d220079cb6800790d2200790d228
noncomputable def BK_432 : ℕ := 0x78935a0079277c007996ac0079e0980078935a007996ac0078935a8
noncomputable def BK_433 : ℕ := 0x74dab80075fdc00076fdf40077daae0074dab80076fdf40074dab88
noncomputable def BK_434 : ℕ := 0x6f02660070a88400722f3e0073959c006f026600722f3e006f02668
noncomputable def BK_435 : ℕ := 0x67460a00695e8c006b5c42006d3df00067460a006b5c420067460a8
noncomputable def BK_436 : ℕ := 0x5df340006069380062c9fc00651410005df3400062c9fc005df3408
noncomputable def BK_437 : ℕ := 0x53666a005621900058cdd6005b699a0053666a0058cdd60053666a8
noncomputable def BK_438 : ℕ := 0x48070a004aeca8004dca4000509e140048070a004dca400048070a8
noncomputable def BK_439 : ℕ := 0x3c43b0003f37b600422aca00451b2a003c43b000422aca003c43b08
noncomputable def BK_440 : ℕ := 0x308db2003373c400365ff40039508400308db200365ff400308db28
noncomputable def BK_441 : ℕ := 0x2554ce00281160002adad0002daf7a002554ce002adad0002554ce8
noncomputable def BK_442 : ℕ := 0x1b02ee001d7c48002008b60022a6bc001b02ee002008b6001b02ee8
noncomputable def BK_443 : ℕ := 0x11f8200014176200164f2000189e140011f82000164f200011f8208
noncomputable def BK_444 : ℕ := 0xa8716000c3900000e07d4000ff290000a8716000e07d4000a87168
noncomputable def BK_445 : ℕ := 0x4f20a000627be00077da20008f3020004f20a00077da20004f20a8
noncomputable def BK_446 : ℕ := 0x1686a000217ea0002e99e0003dd260001686a0002e99e0001686a8
noncomputable def BK_447 : ℕ := 0x538000029bc000071260000db6c0000053800007126000005388
noncomputable def BK_448 : ℕ := 0x6840000024a40000039000000000000024a400000000000000008
noncomputable def BK_449 : ℕ := 0x2c8f00001feea000155ca0000ce160001feea0000ce160000ce168
noncomputable def BK_450 : ℕ := 0x72cb80005e5ee0004bd2a0003b33e0005e5ee0003b33e0003b33e8
noncomputable def BK_451 : ℕ := 0xd612e000babee000a10b8000890a4000babee000890a4000890a48
noncomputable def BK_452 : ℕ := 0x15229e001311500011151c000f2f4e00131150000f2f4e000f2f4e8
noncomputable def BK_453 : ℕ := 0x1e1ed0001bc73600197efe001747a4001bc736001747a4001747a48
noncomputable def BK_454 : ℕ := 0x27f854002572a20022f6160020844a002572a20020844a0020844a8
noncomputable def BK_455 : ℕ := 0x324a1c002fb018002d18b0002a858e002fb018002a858e002a858e8
noncomputable def BK_456 : ℕ := 0x3cab82003a177200377f6e0034e51c003a17720034e51c0034e51c8
noncomputable def BK_457 : ℕ := 0x46b43c00443ff00041c158003f3a0200443ff0003f3a02003f3a028
noncomputable def BK_458 : ℕ := 0x500062004dc438004b77da00491cb4004dc43800491cb400491cb48
noncomputable def BK_459 : ℕ := 0x58343400564624005442a800522afa0056462400522afa00522afa8
noncomputable def BK_460 : ℕ := 0x5eff82005d7258005bcb64005a0ba8005d7258005a0ba8005a0ba88
noncomputable def BK_461 : ℕ := 0x6420aa0063034e0061c8d2006071f60063034e006071f6006071f68
noncomputable def BK_462 : ℕ := 0x6766f20066c3e000660180006520420066c3e000652042006520428
noncomputable def BK_463 : ℕ := 0x68b43a0068912a00684dd60067ea5c0068912a0067ea5c0067ea5c8
noncomputable def BK_464 : ℕ := 0x678dd200680b52006869160068a6d600678dd20068691600678dd28
noncomputable def BK_465 : ℕ := 0x64623000655a90006634fc0066f0e600646230006634fc006462308
noncomputable def BK_466 : ℕ := 0x5f62c20060cbf800621a2800634c7c005f62c200621a28005f62c28
noncomputable def BK_467 : ℕ := 0x58c26a005a8e32005c42e2005ddf6a0058c26a005c42e20058c26a8
noncomputable def BK_468 : ℕ := 0x50c3840052dff80054ea1a0056e0a80050c3840054ea1a0050c3848
noncomputable def BK_469 : ℕ := 0x47b546004a0d8c004c58f2004e96100047b546004c58f20047b5468
noncomputable def BK_470 : ℕ := 0x3df09000406db80042e3e400455192003df0900042e3e4003df0908
noncomputable def BK_471 : ℕ := 0x33d47800365e5c0038e75c003b6df00033d4780038e75c0033d4788
noncomputable def BK_472 : ℕ := 0x29c294002c40c4002ec42800314b3a0029c294002ec4280029c2948
noncomputable def BK_473 : ℕ := 0x201b3e002275f80024dbb800274b1200201b3e0024dbb800201b3e8
noncomputable def BK_474 : ℕ := 0x1739e800195af6001b8c66001dccf0001739e8001b8c66001739e88
noncomputable def BK_475 : ℕ := 0xf71a00011453600132dda00152a78000f71a000132dda000f71a08
noncomputable def BK_476 : ℕ := 0x90a06000a7f74000c0dca000db42800090a06000c0dca00090a068
noncomputable def BK_477 : ℕ := 0x43c98000546f200066d0e0007ae5000043c9800066d0e00043c988
noncomputable def BK_478 : ℕ := 0x132ac0001c93800027d4a00034e8c000132ac00027d4a000132ac8
noncomputable def BK_479 : ℕ := 0x3f40000227a00005f240000b9ea000003f400005f24000003f48
noncomputable def BK_480 : ℕ := 0x5caa0000213200000390000000000000213200000000000000008
noncomputable def BK_481 : ℕ := 0x26f200001bf6200012c1c0000b5be0001bf620000b5be0000b5be8
noncomputable def BK_482 : ℕ := 0x63f5a00052398000421d800033ace0005239800033ace00033ace8
noncomputable def BK_483 : ℕ := 0xba212000a269a0008c1b600077454000a269a00077454000774548
noncomputable def BK_484 : ℕ := 0x125d00001091ae000ed8ac000d331a001091ae000d331a000d331a8
noncomputable def BK_485 : ℕ := 0x1a2936001820d2001625cc00143972001820d200143972001439728
noncomputable def BK_486 : ℕ := 0x22b5f40020856a001e5cde001c3dac0020856a001c3dac001c3dac8
noncomputable def BK_487 : ℕ := 0x2babcc0029696c0027295e0024ed120029696c0024ed120024ed128
noncomputable def BK_488 : ℕ := 0x34b014003272a4003031d6002def14003272a4002def14002def148
noncomputable def BK_489 : ℕ := 0x3d685a003b464000391b440036e8c0003b46400036e8c00036e8c08
noncomputable def BK_490 : ℕ := 0x457dde00438c4200418ca4003f804000438c42003f8040003f80408
noncomputable def BK_491 : ℕ := 0x4ca0dc004af2dc0049325000476046004af2dc00476046004760468
noncomputable def BK_492 : ℕ := 0x528b8400513180004fc122004e3b4600513180004e3b46004e3b468
noncomputable def BK_493 : ℕ := 0x57049600560b900054f9460053ce5c00560b900053ce5c0053ce5c8
noncomputable def BK_494 : ℕ := 0x59e1720059529c0058a8960057e3c40059529c0057e3c40057e3c48
noncomputable def BK_495 : ℕ := 0x5b079e005ae804005aac5e005a54c8005ae804005a54c8005a54c88
noncomputable def BK_496 : ℕ := 0x5a0c12005a781c005ac886005afd18005a0c12005ac886005a0c128
noncomputable def BK_497 : ℕ := 0x574e800058257a0058e260005984b600574e800058e26000574e808
noncomputable def BK_498 : ℕ := 0x52f996005432da0055548e00565dfe0052f9960055548e0052f9968
noncomputable def BK_499 : ℕ := 0x4d3954004ec886005043920051a98e004d395400504392004d39548
noncomputable def BK_500 : ℕ := 0x46473e00481cd80049e272004b96f60046473e0049e2720046473e8
noncomputable def BK_501 : ℕ := 0x3e682000407204004270a6004462ca003e6820004270a6003e68208
noncomputable def BK_502 : ℕ := 0x35e93e0038137a003a3792003c54380035e93e003a37920035e93e8
noncomputable def BK_503 : ℕ := 0x2d1d60002f52ea003187a20033ba30002d1d60003187a2002d1d608
noncomputable def BK_504 : ℕ := 0x24598e0026851c0028b524002ae8560024598e0028b5240024598e8
noncomputable def BK_505 : ℕ := 0x1bf1d4001dfea80020150e002233c6001bf1d40020150e001bf1d48
noncomputable def BK_506 : ℕ := 0x14360c001610c00017f9b40019efc80014360c0017f9b40014360c8
noncomputable def BK_507 : ℕ := 0xd6ed6000f06160010afb000126aae000d6ed60010afb0000d6ed68
noncomputable def BK_508 : ℕ := 0x7dade00092012000a7afc000bead80007dade000a7afc0007dade8
noncomputable def BK_509 : ℕ := 0x3ac9400049460000594660006ac180003ac94000594660003ac948
noncomputable def BK_510 : ℕ := 0x1085000018b06000227840002dd7c0001085000022784000108508
noncomputable def BK_511 : ℕ := 0x30e00001cea0000511e00009fa00000030e0000511e0000030e8
noncomputable def BKs1_3 (j : ℕ) : ℕ := dsel j 18 (dpk j 17 BK_17) (dpk j 18 BK_18)
noncomputable def BKs0_3 (j : ℕ) : ℕ := dsel j 17 (dpk j 16 BK_16) (BKs1_3 j)
noncomputable def BKs3_5 (j : ℕ) : ℕ := dsel j 20 (dpk j 19 BK_19) (dpk j 20 BK_20)
noncomputable def BKs5_7 (j : ℕ) : ℕ := dsel j 22 (dpk j 21 BK_21) (dpk j 22 BK_22)
noncomputable def BKs3_7 (j : ℕ) : ℕ := dsel j 21 (BKs3_5 j) (BKs5_7 j)
noncomputable def BKs0_7 (j : ℕ) : ℕ := dsel j 19 (BKs0_3 j) (BKs3_7 j)
noncomputable def BKs7_9 (j : ℕ) : ℕ := dsel j 24 (dpk j 23 BK_23) (dpk j 24 BK_24)
noncomputable def BKs9_11 (j : ℕ) : ℕ := dsel j 26 (dpk j 25 BK_25) (dpk j 26 BK_26)
noncomputable def BKs7_11 (j : ℕ) : ℕ := dsel j 25 (BKs7_9 j) (BKs9_11 j)
noncomputable def BKs11_13 (j : ℕ) : ℕ := dsel j 28 (dpk j 27 BK_27) (dpk j 28 BK_28)
noncomputable def BKs13_15 (j : ℕ) : ℕ := dsel j 30 (dpk j 29 BK_29) (dpk j 30 BK_30)
noncomputable def BKs11_15 (j : ℕ) : ℕ := dsel j 29 (BKs11_13 j) (BKs13_15 j)
noncomputable def BKs7_15 (j : ℕ) : ℕ := dsel j 27 (BKs7_11 j) (BKs11_15 j)
noncomputable def BKs0_15 (j : ℕ) : ℕ := dsel j 23 (BKs0_7 j) (BKs7_15 j)
noncomputable def BKs15_17 (j : ℕ) : ℕ := dsel j 32 (dpk j 31 BK_31) (dpk j 32 BK_32)
noncomputable def BKs17_19 (j : ℕ) : ℕ := dsel j 34 (dpk j 33 BK_33) (dpk j 34 BK_34)
noncomputable def BKs15_19 (j : ℕ) : ℕ := dsel j 33 (BKs15_17 j) (BKs17_19 j)
noncomputable def BKs19_21 (j : ℕ) : ℕ := dsel j 36 (dpk j 35 BK_35) (dpk j 36 BK_36)
noncomputable def BKs21_23 (j : ℕ) : ℕ := dsel j 38 (dpk j 37 BK_37) (dpk j 38 BK_38)
noncomputable def BKs19_23 (j : ℕ) : ℕ := dsel j 37 (BKs19_21 j) (BKs21_23 j)
noncomputable def BKs15_23 (j : ℕ) : ℕ := dsel j 35 (BKs15_19 j) (BKs19_23 j)
noncomputable def BKs23_25 (j : ℕ) : ℕ := dsel j 40 (dpk j 39 BK_39) (dpk j 40 BK_40)
noncomputable def BKs25_27 (j : ℕ) : ℕ := dsel j 42 (dpk j 41 BK_41) (dpk j 42 BK_42)
noncomputable def BKs23_27 (j : ℕ) : ℕ := dsel j 41 (BKs23_25 j) (BKs25_27 j)
noncomputable def BKs27_29 (j : ℕ) : ℕ := dsel j 44 (dpk j 43 BK_43) (dpk j 44 BK_44)
noncomputable def BKs29_31 (j : ℕ) : ℕ := dsel j 46 (dpk j 45 BK_45) (dpk j 46 BK_46)
noncomputable def BKs27_31 (j : ℕ) : ℕ := dsel j 45 (BKs27_29 j) (BKs29_31 j)
noncomputable def BKs23_31 (j : ℕ) : ℕ := dsel j 43 (BKs23_27 j) (BKs27_31 j)
noncomputable def BKs15_31 (j : ℕ) : ℕ := dsel j 39 (BKs15_23 j) (BKs23_31 j)
noncomputable def BKs0_31 (j : ℕ) : ℕ := dsel j 31 (BKs0_15 j) (BKs15_31 j)
noncomputable def BKs32_34 (j : ℕ) : ℕ := dsel j 49 (dpk j 48 BK_48) (dpk j 49 BK_49)
noncomputable def BKs31_34 (j : ℕ) : ℕ := dsel j 48 (dpk j 47 BK_47) (BKs32_34 j)
noncomputable def BKs34_36 (j : ℕ) : ℕ := dsel j 51 (dpk j 50 BK_50) (dpk j 51 BK_51)
noncomputable def BKs36_38 (j : ℕ) : ℕ := dsel j 53 (dpk j 52 BK_52) (dpk j 53 BK_53)
noncomputable def BKs34_38 (j : ℕ) : ℕ := dsel j 52 (BKs34_36 j) (BKs36_38 j)
noncomputable def BKs31_38 (j : ℕ) : ℕ := dsel j 50 (BKs31_34 j) (BKs34_38 j)
noncomputable def BKs38_40 (j : ℕ) : ℕ := dsel j 55 (dpk j 54 BK_54) (dpk j 55 BK_55)
noncomputable def BKs40_42 (j : ℕ) : ℕ := dsel j 57 (dpk j 56 BK_56) (dpk j 57 BK_57)
noncomputable def BKs38_42 (j : ℕ) : ℕ := dsel j 56 (BKs38_40 j) (BKs40_42 j)
noncomputable def BKs42_44 (j : ℕ) : ℕ := dsel j 59 (dpk j 58 BK_58) (dpk j 59 BK_59)
noncomputable def BKs44_46 (j : ℕ) : ℕ := dsel j 61 (dpk j 60 BK_60) (dpk j 61 BK_61)
noncomputable def BKs42_46 (j : ℕ) : ℕ := dsel j 60 (BKs42_44 j) (BKs44_46 j)
noncomputable def BKs38_46 (j : ℕ) : ℕ := dsel j 58 (BKs38_42 j) (BKs42_46 j)
noncomputable def BKs31_46 (j : ℕ) : ℕ := dsel j 54 (BKs31_38 j) (BKs38_46 j)
noncomputable def BKs46_48 (j : ℕ) : ℕ := dsel j 63 (dpk j 62 BK_62) (dpk j 63 BK_63)
noncomputable def BKs48_50 (j : ℕ) : ℕ := dsel j 65 (dpk j 64 BK_64) (dpk j 65 BK_65)
noncomputable def BKs46_50 (j : ℕ) : ℕ := dsel j 64 (BKs46_48 j) (BKs48_50 j)
noncomputable def BKs50_52 (j : ℕ) : ℕ := dsel j 67 (dpk j 66 BK_66) (dpk j 67 BK_67)
noncomputable def BKs52_54 (j : ℕ) : ℕ := dsel j 69 (dpk j 68 BK_68) (dpk j 69 BK_69)
noncomputable def BKs50_54 (j : ℕ) : ℕ := dsel j 68 (BKs50_52 j) (BKs52_54 j)
noncomputable def BKs46_54 (j : ℕ) : ℕ := dsel j 66 (BKs46_50 j) (BKs50_54 j)
noncomputable def BKs54_56 (j : ℕ) : ℕ := dsel j 71 (dpk j 70 BK_70) (dpk j 71 BK_71)
noncomputable def BKs56_58 (j : ℕ) : ℕ := dsel j 73 (dpk j 72 BK_72) (dpk j 73 BK_73)
noncomputable def BKs54_58 (j : ℕ) : ℕ := dsel j 72 (BKs54_56 j) (BKs56_58 j)
noncomputable def BKs58_60 (j : ℕ) : ℕ := dsel j 75 (dpk j 74 BK_74) (dpk j 75 BK_75)
noncomputable def BKs60_62 (j : ℕ) : ℕ := dsel j 77 (dpk j 76 BK_76) (dpk j 77 BK_77)
noncomputable def BKs58_62 (j : ℕ) : ℕ := dsel j 76 (BKs58_60 j) (BKs60_62 j)
noncomputable def BKs54_62 (j : ℕ) : ℕ := dsel j 74 (BKs54_58 j) (BKs58_62 j)
noncomputable def BKs46_62 (j : ℕ) : ℕ := dsel j 70 (BKs46_54 j) (BKs54_62 j)
noncomputable def BKs31_62 (j : ℕ) : ℕ := dsel j 62 (BKs31_46 j) (BKs46_62 j)
noncomputable def BKs0_62 (j : ℕ) : ℕ := dsel j 47 (BKs0_31 j) (BKs31_62 j)
noncomputable def BKs63_65 (j : ℕ) : ℕ := dsel j 80 (dpk j 79 BK_79) (dpk j 80 BK_80)
noncomputable def BKs62_65 (j : ℕ) : ℕ := dsel j 79 (dpk j 78 BK_78) (BKs63_65 j)
noncomputable def BKs65_67 (j : ℕ) : ℕ := dsel j 82 (dpk j 81 BK_81) (dpk j 82 BK_82)
noncomputable def BKs67_69 (j : ℕ) : ℕ := dsel j 84 (dpk j 83 BK_83) (dpk j 84 BK_84)
noncomputable def BKs65_69 (j : ℕ) : ℕ := dsel j 83 (BKs65_67 j) (BKs67_69 j)
noncomputable def BKs62_69 (j : ℕ) : ℕ := dsel j 81 (BKs62_65 j) (BKs65_69 j)
noncomputable def BKs69_71 (j : ℕ) : ℕ := dsel j 86 (dpk j 85 BK_85) (dpk j 86 BK_86)
noncomputable def BKs71_73 (j : ℕ) : ℕ := dsel j 88 (dpk j 87 BK_87) (dpk j 88 BK_88)
noncomputable def BKs69_73 (j : ℕ) : ℕ := dsel j 87 (BKs69_71 j) (BKs71_73 j)
noncomputable def BKs73_75 (j : ℕ) : ℕ := dsel j 90 (dpk j 89 BK_89) (dpk j 90 BK_90)
noncomputable def BKs75_77 (j : ℕ) : ℕ := dsel j 92 (dpk j 91 BK_91) (dpk j 92 BK_92)
noncomputable def BKs73_77 (j : ℕ) : ℕ := dsel j 91 (BKs73_75 j) (BKs75_77 j)
noncomputable def BKs69_77 (j : ℕ) : ℕ := dsel j 89 (BKs69_73 j) (BKs73_77 j)
noncomputable def BKs62_77 (j : ℕ) : ℕ := dsel j 85 (BKs62_69 j) (BKs69_77 j)
noncomputable def BKs77_79 (j : ℕ) : ℕ := dsel j 94 (dpk j 93 BK_93) (dpk j 94 BK_94)
noncomputable def BKs79_81 (j : ℕ) : ℕ := dsel j 96 (dpk j 95 BK_95) (dpk j 96 BK_96)
noncomputable def BKs77_81 (j : ℕ) : ℕ := dsel j 95 (BKs77_79 j) (BKs79_81 j)
noncomputable def BKs81_83 (j : ℕ) : ℕ := dsel j 98 (dpk j 97 BK_97) (dpk j 98 BK_98)
noncomputable def BKs83_85 (j : ℕ) : ℕ := dsel j 100 (dpk j 99 BK_99) (dpk j 100 BK_100)
noncomputable def BKs81_85 (j : ℕ) : ℕ := dsel j 99 (BKs81_83 j) (BKs83_85 j)
noncomputable def BKs77_85 (j : ℕ) : ℕ := dsel j 97 (BKs77_81 j) (BKs81_85 j)
noncomputable def BKs85_87 (j : ℕ) : ℕ := dsel j 102 (dpk j 101 BK_101) (dpk j 102 BK_102)
noncomputable def BKs87_89 (j : ℕ) : ℕ := dsel j 104 (dpk j 103 BK_103) (dpk j 104 BK_104)
noncomputable def BKs85_89 (j : ℕ) : ℕ := dsel j 103 (BKs85_87 j) (BKs87_89 j)
noncomputable def BKs89_91 (j : ℕ) : ℕ := dsel j 106 (dpk j 105 BK_105) (dpk j 106 BK_106)
noncomputable def BKs91_93 (j : ℕ) : ℕ := dsel j 108 (dpk j 107 BK_107) (dpk j 108 BK_108)
noncomputable def BKs89_93 (j : ℕ) : ℕ := dsel j 107 (BKs89_91 j) (BKs91_93 j)
noncomputable def BKs85_93 (j : ℕ) : ℕ := dsel j 105 (BKs85_89 j) (BKs89_93 j)
noncomputable def BKs77_93 (j : ℕ) : ℕ := dsel j 101 (BKs77_85 j) (BKs85_93 j)
noncomputable def BKs62_93 (j : ℕ) : ℕ := dsel j 93 (BKs62_77 j) (BKs77_93 j)
noncomputable def BKs94_96 (j : ℕ) : ℕ := dsel j 111 (dpk j 110 BK_110) (dpk j 111 BK_111)
noncomputable def BKs93_96 (j : ℕ) : ℕ := dsel j 110 (dpk j 109 BK_109) (BKs94_96 j)
noncomputable def BKs96_98 (j : ℕ) : ℕ := dsel j 113 (dpk j 112 BK_112) (dpk j 113 BK_113)
noncomputable def BKs98_100 (j : ℕ) : ℕ := dsel j 115 (dpk j 114 BK_114) (dpk j 115 BK_115)
noncomputable def BKs96_100 (j : ℕ) : ℕ := dsel j 114 (BKs96_98 j) (BKs98_100 j)
noncomputable def BKs93_100 (j : ℕ) : ℕ := dsel j 112 (BKs93_96 j) (BKs96_100 j)
noncomputable def BKs100_102 (j : ℕ) : ℕ := dsel j 117 (dpk j 116 BK_116) (dpk j 117 BK_117)
noncomputable def BKs102_104 (j : ℕ) : ℕ := dsel j 119 (dpk j 118 BK_118) (dpk j 119 BK_119)
noncomputable def BKs100_104 (j : ℕ) : ℕ := dsel j 118 (BKs100_102 j) (BKs102_104 j)
noncomputable def BKs104_106 (j : ℕ) : ℕ := dsel j 121 (dpk j 120 BK_120) (dpk j 121 BK_121)
noncomputable def BKs106_108 (j : ℕ) : ℕ := dsel j 123 (dpk j 122 BK_122) (dpk j 123 BK_123)
noncomputable def BKs104_108 (j : ℕ) : ℕ := dsel j 122 (BKs104_106 j) (BKs106_108 j)
noncomputable def BKs100_108 (j : ℕ) : ℕ := dsel j 120 (BKs100_104 j) (BKs104_108 j)
noncomputable def BKs93_108 (j : ℕ) : ℕ := dsel j 116 (BKs93_100 j) (BKs100_108 j)
noncomputable def BKs108_110 (j : ℕ) : ℕ := dsel j 125 (dpk j 124 BK_124) (dpk j 125 BK_125)
noncomputable def BKs110_112 (j : ℕ) : ℕ := dsel j 127 (dpk j 126 BK_126) (dpk j 127 BK_127)
noncomputable def BKs108_112 (j : ℕ) : ℕ := dsel j 126 (BKs108_110 j) (BKs110_112 j)
noncomputable def BKs112_114 (j : ℕ) : ℕ := dsel j 129 (dpk j 128 BK_128) (dpk j 129 BK_129)
noncomputable def BKs114_116 (j : ℕ) : ℕ := dsel j 131 (dpk j 130 BK_130) (dpk j 131 BK_131)
noncomputable def BKs112_116 (j : ℕ) : ℕ := dsel j 130 (BKs112_114 j) (BKs114_116 j)
noncomputable def BKs108_116 (j : ℕ) : ℕ := dsel j 128 (BKs108_112 j) (BKs112_116 j)
noncomputable def BKs116_118 (j : ℕ) : ℕ := dsel j 133 (dpk j 132 BK_132) (dpk j 133 BK_133)
noncomputable def BKs118_120 (j : ℕ) : ℕ := dsel j 135 (dpk j 134 BK_134) (dpk j 135 BK_135)
noncomputable def BKs116_120 (j : ℕ) : ℕ := dsel j 134 (BKs116_118 j) (BKs118_120 j)
noncomputable def BKs120_122 (j : ℕ) : ℕ := dsel j 137 (dpk j 136 BK_136) (dpk j 137 BK_137)
noncomputable def BKs122_124 (j : ℕ) : ℕ := dsel j 139 (dpk j 138 BK_138) (dpk j 139 BK_139)
noncomputable def BKs120_124 (j : ℕ) : ℕ := dsel j 138 (BKs120_122 j) (BKs122_124 j)
noncomputable def BKs116_124 (j : ℕ) : ℕ := dsel j 136 (BKs116_120 j) (BKs120_124 j)
noncomputable def BKs108_124 (j : ℕ) : ℕ := dsel j 132 (BKs108_116 j) (BKs116_124 j)
noncomputable def BKs93_124 (j : ℕ) : ℕ := dsel j 124 (BKs93_108 j) (BKs108_124 j)
noncomputable def BKs62_124 (j : ℕ) : ℕ := dsel j 109 (BKs62_93 j) (BKs93_124 j)
noncomputable def BKs0_124 (j : ℕ) : ℕ := dsel j 78 (BKs0_62 j) (BKs62_124 j)
noncomputable def BKs125_127 (j : ℕ) : ℕ := dsel j 142 (dpk j 141 BK_141) (dpk j 142 BK_142)
noncomputable def BKs124_127 (j : ℕ) : ℕ := dsel j 141 (dpk j 140 BK_140) (BKs125_127 j)
noncomputable def BKs127_129 (j : ℕ) : ℕ := dsel j 144 (dpk j 143 BK_143) (dpk j 144 BK_144)
noncomputable def BKs129_131 (j : ℕ) : ℕ := dsel j 146 (dpk j 145 BK_145) (dpk j 146 BK_146)
noncomputable def BKs127_131 (j : ℕ) : ℕ := dsel j 145 (BKs127_129 j) (BKs129_131 j)
noncomputable def BKs124_131 (j : ℕ) : ℕ := dsel j 143 (BKs124_127 j) (BKs127_131 j)
noncomputable def BKs131_133 (j : ℕ) : ℕ := dsel j 148 (dpk j 147 BK_147) (dpk j 148 BK_148)
noncomputable def BKs133_135 (j : ℕ) : ℕ := dsel j 150 (dpk j 149 BK_149) (dpk j 150 BK_150)
noncomputable def BKs131_135 (j : ℕ) : ℕ := dsel j 149 (BKs131_133 j) (BKs133_135 j)
noncomputable def BKs135_137 (j : ℕ) : ℕ := dsel j 152 (dpk j 151 BK_151) (dpk j 152 BK_152)
noncomputable def BKs137_139 (j : ℕ) : ℕ := dsel j 154 (dpk j 153 BK_153) (dpk j 154 BK_154)
noncomputable def BKs135_139 (j : ℕ) : ℕ := dsel j 153 (BKs135_137 j) (BKs137_139 j)
noncomputable def BKs131_139 (j : ℕ) : ℕ := dsel j 151 (BKs131_135 j) (BKs135_139 j)
noncomputable def BKs124_139 (j : ℕ) : ℕ := dsel j 147 (BKs124_131 j) (BKs131_139 j)
noncomputable def BKs139_141 (j : ℕ) : ℕ := dsel j 156 (dpk j 155 BK_155) (dpk j 156 BK_156)
noncomputable def BKs141_143 (j : ℕ) : ℕ := dsel j 158 (dpk j 157 BK_157) (dpk j 158 BK_158)
noncomputable def BKs139_143 (j : ℕ) : ℕ := dsel j 157 (BKs139_141 j) (BKs141_143 j)
noncomputable def BKs143_145 (j : ℕ) : ℕ := dsel j 160 (dpk j 159 BK_159) (dpk j 160 BK_160)
noncomputable def BKs145_147 (j : ℕ) : ℕ := dsel j 162 (dpk j 161 BK_161) (dpk j 162 BK_162)
noncomputable def BKs143_147 (j : ℕ) : ℕ := dsel j 161 (BKs143_145 j) (BKs145_147 j)
noncomputable def BKs139_147 (j : ℕ) : ℕ := dsel j 159 (BKs139_143 j) (BKs143_147 j)
noncomputable def BKs147_149 (j : ℕ) : ℕ := dsel j 164 (dpk j 163 BK_163) (dpk j 164 BK_164)
noncomputable def BKs149_151 (j : ℕ) : ℕ := dsel j 166 (dpk j 165 BK_165) (dpk j 166 BK_166)
noncomputable def BKs147_151 (j : ℕ) : ℕ := dsel j 165 (BKs147_149 j) (BKs149_151 j)
noncomputable def BKs151_153 (j : ℕ) : ℕ := dsel j 168 (dpk j 167 BK_167) (dpk j 168 BK_168)
noncomputable def BKs153_155 (j : ℕ) : ℕ := dsel j 170 (dpk j 169 BK_169) (dpk j 170 BK_170)
noncomputable def BKs151_155 (j : ℕ) : ℕ := dsel j 169 (BKs151_153 j) (BKs153_155 j)
noncomputable def BKs147_155 (j : ℕ) : ℕ := dsel j 167 (BKs147_151 j) (BKs151_155 j)
noncomputable def BKs139_155 (j : ℕ) : ℕ := dsel j 163 (BKs139_147 j) (BKs147_155 j)
noncomputable def BKs124_155 (j : ℕ) : ℕ := dsel j 155 (BKs124_139 j) (BKs139_155 j)
noncomputable def BKs156_158 (j : ℕ) : ℕ := dsel j 173 (dpk j 172 BK_172) (dpk j 173 BK_173)
noncomputable def BKs155_158 (j : ℕ) : ℕ := dsel j 172 (dpk j 171 BK_171) (BKs156_158 j)
noncomputable def BKs158_160 (j : ℕ) : ℕ := dsel j 175 (dpk j 174 BK_174) (dpk j 175 BK_175)
noncomputable def BKs160_162 (j : ℕ) : ℕ := dsel j 177 (dpk j 176 BK_176) (dpk j 177 BK_177)
noncomputable def BKs158_162 (j : ℕ) : ℕ := dsel j 176 (BKs158_160 j) (BKs160_162 j)
noncomputable def BKs155_162 (j : ℕ) : ℕ := dsel j 174 (BKs155_158 j) (BKs158_162 j)
noncomputable def BKs162_164 (j : ℕ) : ℕ := dsel j 179 (dpk j 178 BK_178) (dpk j 179 BK_179)
noncomputable def BKs164_166 (j : ℕ) : ℕ := dsel j 181 (dpk j 180 BK_180) (dpk j 181 BK_181)
noncomputable def BKs162_166 (j : ℕ) : ℕ := dsel j 180 (BKs162_164 j) (BKs164_166 j)
noncomputable def BKs166_168 (j : ℕ) : ℕ := dsel j 183 (dpk j 182 BK_182) (dpk j 183 BK_183)
noncomputable def BKs168_170 (j : ℕ) : ℕ := dsel j 185 (dpk j 184 BK_184) (dpk j 185 BK_185)
noncomputable def BKs166_170 (j : ℕ) : ℕ := dsel j 184 (BKs166_168 j) (BKs168_170 j)
noncomputable def BKs162_170 (j : ℕ) : ℕ := dsel j 182 (BKs162_166 j) (BKs166_170 j)
noncomputable def BKs155_170 (j : ℕ) : ℕ := dsel j 178 (BKs155_162 j) (BKs162_170 j)
noncomputable def BKs170_172 (j : ℕ) : ℕ := dsel j 187 (dpk j 186 BK_186) (dpk j 187 BK_187)
noncomputable def BKs172_174 (j : ℕ) : ℕ := dsel j 189 (dpk j 188 BK_188) (dpk j 189 BK_189)
noncomputable def BKs170_174 (j : ℕ) : ℕ := dsel j 188 (BKs170_172 j) (BKs172_174 j)
noncomputable def BKs174_176 (j : ℕ) : ℕ := dsel j 191 (dpk j 190 BK_190) (dpk j 191 BK_191)
noncomputable def BKs176_178 (j : ℕ) : ℕ := dsel j 193 (dpk j 192 BK_192) (dpk j 193 BK_193)
noncomputable def BKs174_178 (j : ℕ) : ℕ := dsel j 192 (BKs174_176 j) (BKs176_178 j)
noncomputable def BKs170_178 (j : ℕ) : ℕ := dsel j 190 (BKs170_174 j) (BKs174_178 j)
noncomputable def BKs178_180 (j : ℕ) : ℕ := dsel j 195 (dpk j 194 BK_194) (dpk j 195 BK_195)
noncomputable def BKs180_182 (j : ℕ) : ℕ := dsel j 197 (dpk j 196 BK_196) (dpk j 197 BK_197)
noncomputable def BKs178_182 (j : ℕ) : ℕ := dsel j 196 (BKs178_180 j) (BKs180_182 j)
noncomputable def BKs182_184 (j : ℕ) : ℕ := dsel j 199 (dpk j 198 BK_198) (dpk j 199 BK_199)
noncomputable def BKs184_186 (j : ℕ) : ℕ := dsel j 201 (dpk j 200 BK_200) (dpk j 201 BK_201)
noncomputable def BKs182_186 (j : ℕ) : ℕ := dsel j 200 (BKs182_184 j) (BKs184_186 j)
noncomputable def BKs178_186 (j : ℕ) : ℕ := dsel j 198 (BKs178_182 j) (BKs182_186 j)
noncomputable def BKs170_186 (j : ℕ) : ℕ := dsel j 194 (BKs170_178 j) (BKs178_186 j)
noncomputable def BKs155_186 (j : ℕ) : ℕ := dsel j 186 (BKs155_170 j) (BKs170_186 j)
noncomputable def BKs124_186 (j : ℕ) : ℕ := dsel j 171 (BKs124_155 j) (BKs155_186 j)
noncomputable def BKs187_189 (j : ℕ) : ℕ := dsel j 204 (dpk j 203 BK_203) (dpk j 204 BK_204)
noncomputable def BKs186_189 (j : ℕ) : ℕ := dsel j 203 (dpk j 202 BK_202) (BKs187_189 j)
noncomputable def BKs189_191 (j : ℕ) : ℕ := dsel j 206 (dpk j 205 BK_205) (dpk j 206 BK_206)
noncomputable def BKs191_193 (j : ℕ) : ℕ := dsel j 208 (dpk j 207 BK_207) (dpk j 208 BK_208)
noncomputable def BKs189_193 (j : ℕ) : ℕ := dsel j 207 (BKs189_191 j) (BKs191_193 j)
noncomputable def BKs186_193 (j : ℕ) : ℕ := dsel j 205 (BKs186_189 j) (BKs189_193 j)
noncomputable def BKs193_195 (j : ℕ) : ℕ := dsel j 210 (dpk j 209 BK_209) (dpk j 210 BK_210)
noncomputable def BKs195_197 (j : ℕ) : ℕ := dsel j 212 (dpk j 211 BK_211) (dpk j 212 BK_212)
noncomputable def BKs193_197 (j : ℕ) : ℕ := dsel j 211 (BKs193_195 j) (BKs195_197 j)
noncomputable def BKs197_199 (j : ℕ) : ℕ := dsel j 214 (dpk j 213 BK_213) (dpk j 214 BK_214)
noncomputable def BKs199_201 (j : ℕ) : ℕ := dsel j 216 (dpk j 215 BK_215) (dpk j 216 BK_216)
noncomputable def BKs197_201 (j : ℕ) : ℕ := dsel j 215 (BKs197_199 j) (BKs199_201 j)
noncomputable def BKs193_201 (j : ℕ) : ℕ := dsel j 213 (BKs193_197 j) (BKs197_201 j)
noncomputable def BKs186_201 (j : ℕ) : ℕ := dsel j 209 (BKs186_193 j) (BKs193_201 j)
noncomputable def BKs201_203 (j : ℕ) : ℕ := dsel j 218 (dpk j 217 BK_217) (dpk j 218 BK_218)
noncomputable def BKs203_205 (j : ℕ) : ℕ := dsel j 220 (dpk j 219 BK_219) (dpk j 220 BK_220)
noncomputable def BKs201_205 (j : ℕ) : ℕ := dsel j 219 (BKs201_203 j) (BKs203_205 j)
noncomputable def BKs205_207 (j : ℕ) : ℕ := dsel j 222 (dpk j 221 BK_221) (dpk j 222 BK_222)
noncomputable def BKs207_209 (j : ℕ) : ℕ := dsel j 224 (dpk j 223 BK_223) (dpk j 224 BK_224)
noncomputable def BKs205_209 (j : ℕ) : ℕ := dsel j 223 (BKs205_207 j) (BKs207_209 j)
noncomputable def BKs201_209 (j : ℕ) : ℕ := dsel j 221 (BKs201_205 j) (BKs205_209 j)
noncomputable def BKs209_211 (j : ℕ) : ℕ := dsel j 226 (dpk j 225 BK_225) (dpk j 226 BK_226)
noncomputable def BKs211_213 (j : ℕ) : ℕ := dsel j 228 (dpk j 227 BK_227) (dpk j 228 BK_228)
noncomputable def BKs209_213 (j : ℕ) : ℕ := dsel j 227 (BKs209_211 j) (BKs211_213 j)
noncomputable def BKs213_215 (j : ℕ) : ℕ := dsel j 230 (dpk j 229 BK_229) (dpk j 230 BK_230)
noncomputable def BKs215_217 (j : ℕ) : ℕ := dsel j 232 (dpk j 231 BK_231) (dpk j 232 BK_232)
noncomputable def BKs213_217 (j : ℕ) : ℕ := dsel j 231 (BKs213_215 j) (BKs215_217 j)
noncomputable def BKs209_217 (j : ℕ) : ℕ := dsel j 229 (BKs209_213 j) (BKs213_217 j)
noncomputable def BKs201_217 (j : ℕ) : ℕ := dsel j 225 (BKs201_209 j) (BKs209_217 j)
noncomputable def BKs186_217 (j : ℕ) : ℕ := dsel j 217 (BKs186_201 j) (BKs201_217 j)
noncomputable def BKs218_220 (j : ℕ) : ℕ := dsel j 235 (dpk j 234 BK_234) (dpk j 235 BK_235)
noncomputable def BKs217_220 (j : ℕ) : ℕ := dsel j 234 (dpk j 233 BK_233) (BKs218_220 j)
noncomputable def BKs220_222 (j : ℕ) : ℕ := dsel j 237 (dpk j 236 BK_236) (dpk j 237 BK_237)
noncomputable def BKs222_224 (j : ℕ) : ℕ := dsel j 239 (dpk j 238 BK_238) (dpk j 239 BK_239)
noncomputable def BKs220_224 (j : ℕ) : ℕ := dsel j 238 (BKs220_222 j) (BKs222_224 j)
noncomputable def BKs217_224 (j : ℕ) : ℕ := dsel j 236 (BKs217_220 j) (BKs220_224 j)
noncomputable def BKs224_226 (j : ℕ) : ℕ := dsel j 241 (dpk j 240 BK_240) (dpk j 241 BK_241)
noncomputable def BKs226_228 (j : ℕ) : ℕ := dsel j 243 (dpk j 242 BK_242) (dpk j 243 BK_243)
noncomputable def BKs224_228 (j : ℕ) : ℕ := dsel j 242 (BKs224_226 j) (BKs226_228 j)
noncomputable def BKs228_230 (j : ℕ) : ℕ := dsel j 245 (dpk j 244 BK_244) (dpk j 245 BK_245)
noncomputable def BKs230_232 (j : ℕ) : ℕ := dsel j 247 (dpk j 246 BK_246) (dpk j 247 BK_247)
noncomputable def BKs228_232 (j : ℕ) : ℕ := dsel j 246 (BKs228_230 j) (BKs230_232 j)
noncomputable def BKs224_232 (j : ℕ) : ℕ := dsel j 244 (BKs224_228 j) (BKs228_232 j)
noncomputable def BKs217_232 (j : ℕ) : ℕ := dsel j 240 (BKs217_224 j) (BKs224_232 j)
noncomputable def BKs232_234 (j : ℕ) : ℕ := dsel j 249 (dpk j 248 BK_248) (dpk j 249 BK_249)
noncomputable def BKs234_236 (j : ℕ) : ℕ := dsel j 251 (dpk j 250 BK_250) (dpk j 251 BK_251)
noncomputable def BKs232_236 (j : ℕ) : ℕ := dsel j 250 (BKs232_234 j) (BKs234_236 j)
noncomputable def BKs236_238 (j : ℕ) : ℕ := dsel j 253 (dpk j 252 BK_252) (dpk j 253 BK_253)
noncomputable def BKs238_240 (j : ℕ) : ℕ := dsel j 255 (dpk j 254 BK_254) (dpk j 255 BK_255)
noncomputable def BKs236_240 (j : ℕ) : ℕ := dsel j 254 (BKs236_238 j) (BKs238_240 j)
noncomputable def BKs232_240 (j : ℕ) : ℕ := dsel j 252 (BKs232_236 j) (BKs236_240 j)
noncomputable def BKs240_242 (j : ℕ) : ℕ := dsel j 257 (dpk j 256 BK_256) (dpk j 257 BK_257)
noncomputable def BKs242_244 (j : ℕ) : ℕ := dsel j 259 (dpk j 258 BK_258) (dpk j 259 BK_259)
noncomputable def BKs240_244 (j : ℕ) : ℕ := dsel j 258 (BKs240_242 j) (BKs242_244 j)
noncomputable def BKs244_246 (j : ℕ) : ℕ := dsel j 261 (dpk j 260 BK_260) (dpk j 261 BK_261)
noncomputable def BKs246_248 (j : ℕ) : ℕ := dsel j 263 (dpk j 262 BK_262) (dpk j 263 BK_263)
noncomputable def BKs244_248 (j : ℕ) : ℕ := dsel j 262 (BKs244_246 j) (BKs246_248 j)
noncomputable def BKs240_248 (j : ℕ) : ℕ := dsel j 260 (BKs240_244 j) (BKs244_248 j)
noncomputable def BKs232_248 (j : ℕ) : ℕ := dsel j 256 (BKs232_240 j) (BKs240_248 j)
noncomputable def BKs217_248 (j : ℕ) : ℕ := dsel j 248 (BKs217_232 j) (BKs232_248 j)
noncomputable def BKs186_248 (j : ℕ) : ℕ := dsel j 233 (BKs186_217 j) (BKs217_248 j)
noncomputable def BKs124_248 (j : ℕ) : ℕ := dsel j 202 (BKs124_186 j) (BKs186_248 j)
noncomputable def BKs0_248 (j : ℕ) : ℕ := dsel j 140 (BKs0_124 j) (BKs124_248 j)
noncomputable def BKs249_251 (j : ℕ) : ℕ := dsel j 266 (dpk j 265 BK_265) (dpk j 266 BK_266)
noncomputable def BKs248_251 (j : ℕ) : ℕ := dsel j 265 (dpk j 264 BK_264) (BKs249_251 j)
noncomputable def BKs251_253 (j : ℕ) : ℕ := dsel j 268 (dpk j 267 BK_267) (dpk j 268 BK_268)
noncomputable def BKs253_255 (j : ℕ) : ℕ := dsel j 270 (dpk j 269 BK_269) (dpk j 270 BK_270)
noncomputable def BKs251_255 (j : ℕ) : ℕ := dsel j 269 (BKs251_253 j) (BKs253_255 j)
noncomputable def BKs248_255 (j : ℕ) : ℕ := dsel j 267 (BKs248_251 j) (BKs251_255 j)
noncomputable def BKs255_257 (j : ℕ) : ℕ := dsel j 272 (dpk j 271 BK_271) (dpk j 272 BK_272)
noncomputable def BKs257_259 (j : ℕ) : ℕ := dsel j 274 (dpk j 273 BK_273) (dpk j 274 BK_274)
noncomputable def BKs255_259 (j : ℕ) : ℕ := dsel j 273 (BKs255_257 j) (BKs257_259 j)
noncomputable def BKs259_261 (j : ℕ) : ℕ := dsel j 276 (dpk j 275 BK_275) (dpk j 276 BK_276)
noncomputable def BKs261_263 (j : ℕ) : ℕ := dsel j 278 (dpk j 277 BK_277) (dpk j 278 BK_278)
noncomputable def BKs259_263 (j : ℕ) : ℕ := dsel j 277 (BKs259_261 j) (BKs261_263 j)
noncomputable def BKs255_263 (j : ℕ) : ℕ := dsel j 275 (BKs255_259 j) (BKs259_263 j)
noncomputable def BKs248_263 (j : ℕ) : ℕ := dsel j 271 (BKs248_255 j) (BKs255_263 j)
noncomputable def BKs263_265 (j : ℕ) : ℕ := dsel j 280 (dpk j 279 BK_279) (dpk j 280 BK_280)
noncomputable def BKs265_267 (j : ℕ) : ℕ := dsel j 282 (dpk j 281 BK_281) (dpk j 282 BK_282)
noncomputable def BKs263_267 (j : ℕ) : ℕ := dsel j 281 (BKs263_265 j) (BKs265_267 j)
noncomputable def BKs267_269 (j : ℕ) : ℕ := dsel j 284 (dpk j 283 BK_283) (dpk j 284 BK_284)
noncomputable def BKs269_271 (j : ℕ) : ℕ := dsel j 286 (dpk j 285 BK_285) (dpk j 286 BK_286)
noncomputable def BKs267_271 (j : ℕ) : ℕ := dsel j 285 (BKs267_269 j) (BKs269_271 j)
noncomputable def BKs263_271 (j : ℕ) : ℕ := dsel j 283 (BKs263_267 j) (BKs267_271 j)
noncomputable def BKs271_273 (j : ℕ) : ℕ := dsel j 288 (dpk j 287 BK_287) (dpk j 288 BK_288)
noncomputable def BKs273_275 (j : ℕ) : ℕ := dsel j 290 (dpk j 289 BK_289) (dpk j 290 BK_290)
noncomputable def BKs271_275 (j : ℕ) : ℕ := dsel j 289 (BKs271_273 j) (BKs273_275 j)
noncomputable def BKs275_277 (j : ℕ) : ℕ := dsel j 292 (dpk j 291 BK_291) (dpk j 292 BK_292)
noncomputable def BKs277_279 (j : ℕ) : ℕ := dsel j 294 (dpk j 293 BK_293) (dpk j 294 BK_294)
noncomputable def BKs275_279 (j : ℕ) : ℕ := dsel j 293 (BKs275_277 j) (BKs277_279 j)
noncomputable def BKs271_279 (j : ℕ) : ℕ := dsel j 291 (BKs271_275 j) (BKs275_279 j)
noncomputable def BKs263_279 (j : ℕ) : ℕ := dsel j 287 (BKs263_271 j) (BKs271_279 j)
noncomputable def BKs248_279 (j : ℕ) : ℕ := dsel j 279 (BKs248_263 j) (BKs263_279 j)
noncomputable def BKs280_282 (j : ℕ) : ℕ := dsel j 297 (dpk j 296 BK_296) (dpk j 297 BK_297)
noncomputable def BKs279_282 (j : ℕ) : ℕ := dsel j 296 (dpk j 295 BK_295) (BKs280_282 j)
noncomputable def BKs282_284 (j : ℕ) : ℕ := dsel j 299 (dpk j 298 BK_298) (dpk j 299 BK_299)
noncomputable def BKs284_286 (j : ℕ) : ℕ := dsel j 301 (dpk j 300 BK_300) (dpk j 301 BK_301)
noncomputable def BKs282_286 (j : ℕ) : ℕ := dsel j 300 (BKs282_284 j) (BKs284_286 j)
noncomputable def BKs279_286 (j : ℕ) : ℕ := dsel j 298 (BKs279_282 j) (BKs282_286 j)
noncomputable def BKs286_288 (j : ℕ) : ℕ := dsel j 303 (dpk j 302 BK_302) (dpk j 303 BK_303)
noncomputable def BKs288_290 (j : ℕ) : ℕ := dsel j 305 (dpk j 304 BK_304) (dpk j 305 BK_305)
noncomputable def BKs286_290 (j : ℕ) : ℕ := dsel j 304 (BKs286_288 j) (BKs288_290 j)
noncomputable def BKs290_292 (j : ℕ) : ℕ := dsel j 307 (dpk j 306 BK_306) (dpk j 307 BK_307)
noncomputable def BKs292_294 (j : ℕ) : ℕ := dsel j 309 (dpk j 308 BK_308) (dpk j 309 BK_309)
noncomputable def BKs290_294 (j : ℕ) : ℕ := dsel j 308 (BKs290_292 j) (BKs292_294 j)
noncomputable def BKs286_294 (j : ℕ) : ℕ := dsel j 306 (BKs286_290 j) (BKs290_294 j)
noncomputable def BKs279_294 (j : ℕ) : ℕ := dsel j 302 (BKs279_286 j) (BKs286_294 j)
noncomputable def BKs294_296 (j : ℕ) : ℕ := dsel j 311 (dpk j 310 BK_310) (dpk j 311 BK_311)
noncomputable def BKs296_298 (j : ℕ) : ℕ := dsel j 313 (dpk j 312 BK_312) (dpk j 313 BK_313)
noncomputable def BKs294_298 (j : ℕ) : ℕ := dsel j 312 (BKs294_296 j) (BKs296_298 j)
noncomputable def BKs298_300 (j : ℕ) : ℕ := dsel j 315 (dpk j 314 BK_314) (dpk j 315 BK_315)
noncomputable def BKs300_302 (j : ℕ) : ℕ := dsel j 317 (dpk j 316 BK_316) (dpk j 317 BK_317)
noncomputable def BKs298_302 (j : ℕ) : ℕ := dsel j 316 (BKs298_300 j) (BKs300_302 j)
noncomputable def BKs294_302 (j : ℕ) : ℕ := dsel j 314 (BKs294_298 j) (BKs298_302 j)
noncomputable def BKs302_304 (j : ℕ) : ℕ := dsel j 319 (dpk j 318 BK_318) (dpk j 319 BK_319)
noncomputable def BKs304_306 (j : ℕ) : ℕ := dsel j 321 (dpk j 320 BK_320) (dpk j 321 BK_321)
noncomputable def BKs302_306 (j : ℕ) : ℕ := dsel j 320 (BKs302_304 j) (BKs304_306 j)
noncomputable def BKs306_308 (j : ℕ) : ℕ := dsel j 323 (dpk j 322 BK_322) (dpk j 323 BK_323)
noncomputable def BKs308_310 (j : ℕ) : ℕ := dsel j 325 (dpk j 324 BK_324) (dpk j 325 BK_325)
noncomputable def BKs306_310 (j : ℕ) : ℕ := dsel j 324 (BKs306_308 j) (BKs308_310 j)
noncomputable def BKs302_310 (j : ℕ) : ℕ := dsel j 322 (BKs302_306 j) (BKs306_310 j)
noncomputable def BKs294_310 (j : ℕ) : ℕ := dsel j 318 (BKs294_302 j) (BKs302_310 j)
noncomputable def BKs279_310 (j : ℕ) : ℕ := dsel j 310 (BKs279_294 j) (BKs294_310 j)
noncomputable def BKs248_310 (j : ℕ) : ℕ := dsel j 295 (BKs248_279 j) (BKs279_310 j)
noncomputable def BKs311_313 (j : ℕ) : ℕ := dsel j 328 (dpk j 327 BK_327) (dpk j 328 BK_328)
noncomputable def BKs310_313 (j : ℕ) : ℕ := dsel j 327 (dpk j 326 BK_326) (BKs311_313 j)
noncomputable def BKs313_315 (j : ℕ) : ℕ := dsel j 330 (dpk j 329 BK_329) (dpk j 330 BK_330)
noncomputable def BKs315_317 (j : ℕ) : ℕ := dsel j 332 (dpk j 331 BK_331) (dpk j 332 BK_332)
noncomputable def BKs313_317 (j : ℕ) : ℕ := dsel j 331 (BKs313_315 j) (BKs315_317 j)
noncomputable def BKs310_317 (j : ℕ) : ℕ := dsel j 329 (BKs310_313 j) (BKs313_317 j)
noncomputable def BKs317_319 (j : ℕ) : ℕ := dsel j 334 (dpk j 333 BK_333) (dpk j 334 BK_334)
noncomputable def BKs319_321 (j : ℕ) : ℕ := dsel j 336 (dpk j 335 BK_335) (dpk j 336 BK_336)
noncomputable def BKs317_321 (j : ℕ) : ℕ := dsel j 335 (BKs317_319 j) (BKs319_321 j)
noncomputable def BKs321_323 (j : ℕ) : ℕ := dsel j 338 (dpk j 337 BK_337) (dpk j 338 BK_338)
noncomputable def BKs323_325 (j : ℕ) : ℕ := dsel j 340 (dpk j 339 BK_339) (dpk j 340 BK_340)
noncomputable def BKs321_325 (j : ℕ) : ℕ := dsel j 339 (BKs321_323 j) (BKs323_325 j)
noncomputable def BKs317_325 (j : ℕ) : ℕ := dsel j 337 (BKs317_321 j) (BKs321_325 j)
noncomputable def BKs310_325 (j : ℕ) : ℕ := dsel j 333 (BKs310_317 j) (BKs317_325 j)
noncomputable def BKs325_327 (j : ℕ) : ℕ := dsel j 342 (dpk j 341 BK_341) (dpk j 342 BK_342)
noncomputable def BKs327_329 (j : ℕ) : ℕ := dsel j 344 (dpk j 343 BK_343) (dpk j 344 BK_344)
noncomputable def BKs325_329 (j : ℕ) : ℕ := dsel j 343 (BKs325_327 j) (BKs327_329 j)
noncomputable def BKs329_331 (j : ℕ) : ℕ := dsel j 346 (dpk j 345 BK_345) (dpk j 346 BK_346)
noncomputable def BKs331_333 (j : ℕ) : ℕ := dsel j 348 (dpk j 347 BK_347) (dpk j 348 BK_348)
noncomputable def BKs329_333 (j : ℕ) : ℕ := dsel j 347 (BKs329_331 j) (BKs331_333 j)
noncomputable def BKs325_333 (j : ℕ) : ℕ := dsel j 345 (BKs325_329 j) (BKs329_333 j)
noncomputable def BKs333_335 (j : ℕ) : ℕ := dsel j 350 (dpk j 349 BK_349) (dpk j 350 BK_350)
noncomputable def BKs335_337 (j : ℕ) : ℕ := dsel j 352 (dpk j 351 BK_351) (dpk j 352 BK_352)
noncomputable def BKs333_337 (j : ℕ) : ℕ := dsel j 351 (BKs333_335 j) (BKs335_337 j)
noncomputable def BKs337_339 (j : ℕ) : ℕ := dsel j 354 (dpk j 353 BK_353) (dpk j 354 BK_354)
noncomputable def BKs339_341 (j : ℕ) : ℕ := dsel j 356 (dpk j 355 BK_355) (dpk j 356 BK_356)
noncomputable def BKs337_341 (j : ℕ) : ℕ := dsel j 355 (BKs337_339 j) (BKs339_341 j)
noncomputable def BKs333_341 (j : ℕ) : ℕ := dsel j 353 (BKs333_337 j) (BKs337_341 j)
noncomputable def BKs325_341 (j : ℕ) : ℕ := dsel j 349 (BKs325_333 j) (BKs333_341 j)
noncomputable def BKs310_341 (j : ℕ) : ℕ := dsel j 341 (BKs310_325 j) (BKs325_341 j)
noncomputable def BKs342_344 (j : ℕ) : ℕ := dsel j 359 (dpk j 358 BK_358) (dpk j 359 BK_359)
noncomputable def BKs341_344 (j : ℕ) : ℕ := dsel j 358 (dpk j 357 BK_357) (BKs342_344 j)
noncomputable def BKs344_346 (j : ℕ) : ℕ := dsel j 361 (dpk j 360 BK_360) (dpk j 361 BK_361)
noncomputable def BKs346_348 (j : ℕ) : ℕ := dsel j 363 (dpk j 362 BK_362) (dpk j 363 BK_363)
noncomputable def BKs344_348 (j : ℕ) : ℕ := dsel j 362 (BKs344_346 j) (BKs346_348 j)
noncomputable def BKs341_348 (j : ℕ) : ℕ := dsel j 360 (BKs341_344 j) (BKs344_348 j)
noncomputable def BKs348_350 (j : ℕ) : ℕ := dsel j 365 (dpk j 364 BK_364) (dpk j 365 BK_365)
noncomputable def BKs350_352 (j : ℕ) : ℕ := dsel j 367 (dpk j 366 BK_366) (dpk j 367 BK_367)
noncomputable def BKs348_352 (j : ℕ) : ℕ := dsel j 366 (BKs348_350 j) (BKs350_352 j)
noncomputable def BKs352_354 (j : ℕ) : ℕ := dsel j 369 (dpk j 368 BK_368) (dpk j 369 BK_369)
noncomputable def BKs354_356 (j : ℕ) : ℕ := dsel j 371 (dpk j 370 BK_370) (dpk j 371 BK_371)
noncomputable def BKs352_356 (j : ℕ) : ℕ := dsel j 370 (BKs352_354 j) (BKs354_356 j)
noncomputable def BKs348_356 (j : ℕ) : ℕ := dsel j 368 (BKs348_352 j) (BKs352_356 j)
noncomputable def BKs341_356 (j : ℕ) : ℕ := dsel j 364 (BKs341_348 j) (BKs348_356 j)
noncomputable def BKs356_358 (j : ℕ) : ℕ := dsel j 373 (dpk j 372 BK_372) (dpk j 373 BK_373)
noncomputable def BKs358_360 (j : ℕ) : ℕ := dsel j 375 (dpk j 374 BK_374) (dpk j 375 BK_375)
noncomputable def BKs356_360 (j : ℕ) : ℕ := dsel j 374 (BKs356_358 j) (BKs358_360 j)
noncomputable def BKs360_362 (j : ℕ) : ℕ := dsel j 377 (dpk j 376 BK_376) (dpk j 377 BK_377)
noncomputable def BKs362_364 (j : ℕ) : ℕ := dsel j 379 (dpk j 378 BK_378) (dpk j 379 BK_379)
noncomputable def BKs360_364 (j : ℕ) : ℕ := dsel j 378 (BKs360_362 j) (BKs362_364 j)
noncomputable def BKs356_364 (j : ℕ) : ℕ := dsel j 376 (BKs356_360 j) (BKs360_364 j)
noncomputable def BKs364_366 (j : ℕ) : ℕ := dsel j 381 (dpk j 380 BK_380) (dpk j 381 BK_381)
noncomputable def BKs366_368 (j : ℕ) : ℕ := dsel j 383 (dpk j 382 BK_382) (dpk j 383 BK_383)
noncomputable def BKs364_368 (j : ℕ) : ℕ := dsel j 382 (BKs364_366 j) (BKs366_368 j)
noncomputable def BKs368_370 (j : ℕ) : ℕ := dsel j 385 (dpk j 384 BK_384) (dpk j 385 BK_385)
noncomputable def BKs370_372 (j : ℕ) : ℕ := dsel j 387 (dpk j 386 BK_386) (dpk j 387 BK_387)
noncomputable def BKs368_372 (j : ℕ) : ℕ := dsel j 386 (BKs368_370 j) (BKs370_372 j)
noncomputable def BKs364_372 (j : ℕ) : ℕ := dsel j 384 (BKs364_368 j) (BKs368_372 j)
noncomputable def BKs356_372 (j : ℕ) : ℕ := dsel j 380 (BKs356_364 j) (BKs364_372 j)
noncomputable def BKs341_372 (j : ℕ) : ℕ := dsel j 372 (BKs341_356 j) (BKs356_372 j)
noncomputable def BKs310_372 (j : ℕ) : ℕ := dsel j 357 (BKs310_341 j) (BKs341_372 j)
noncomputable def BKs248_372 (j : ℕ) : ℕ := dsel j 326 (BKs248_310 j) (BKs310_372 j)
noncomputable def BKs373_375 (j : ℕ) : ℕ := dsel j 390 (dpk j 389 BK_389) (dpk j 390 BK_390)
noncomputable def BKs372_375 (j : ℕ) : ℕ := dsel j 389 (dpk j 388 BK_388) (BKs373_375 j)
noncomputable def BKs375_377 (j : ℕ) : ℕ := dsel j 392 (dpk j 391 BK_391) (dpk j 392 BK_392)
noncomputable def BKs377_379 (j : ℕ) : ℕ := dsel j 394 (dpk j 393 BK_393) (dpk j 394 BK_394)
noncomputable def BKs375_379 (j : ℕ) : ℕ := dsel j 393 (BKs375_377 j) (BKs377_379 j)
noncomputable def BKs372_379 (j : ℕ) : ℕ := dsel j 391 (BKs372_375 j) (BKs375_379 j)
noncomputable def BKs379_381 (j : ℕ) : ℕ := dsel j 396 (dpk j 395 BK_395) (dpk j 396 BK_396)
noncomputable def BKs381_383 (j : ℕ) : ℕ := dsel j 398 (dpk j 397 BK_397) (dpk j 398 BK_398)
noncomputable def BKs379_383 (j : ℕ) : ℕ := dsel j 397 (BKs379_381 j) (BKs381_383 j)
noncomputable def BKs383_385 (j : ℕ) : ℕ := dsel j 400 (dpk j 399 BK_399) (dpk j 400 BK_400)
noncomputable def BKs385_387 (j : ℕ) : ℕ := dsel j 402 (dpk j 401 BK_401) (dpk j 402 BK_402)
noncomputable def BKs383_387 (j : ℕ) : ℕ := dsel j 401 (BKs383_385 j) (BKs385_387 j)
noncomputable def BKs379_387 (j : ℕ) : ℕ := dsel j 399 (BKs379_383 j) (BKs383_387 j)
noncomputable def BKs372_387 (j : ℕ) : ℕ := dsel j 395 (BKs372_379 j) (BKs379_387 j)
noncomputable def BKs387_389 (j : ℕ) : ℕ := dsel j 404 (dpk j 403 BK_403) (dpk j 404 BK_404)
noncomputable def BKs389_391 (j : ℕ) : ℕ := dsel j 406 (dpk j 405 BK_405) (dpk j 406 BK_406)
noncomputable def BKs387_391 (j : ℕ) : ℕ := dsel j 405 (BKs387_389 j) (BKs389_391 j)
noncomputable def BKs391_393 (j : ℕ) : ℕ := dsel j 408 (dpk j 407 BK_407) (dpk j 408 BK_408)
noncomputable def BKs393_395 (j : ℕ) : ℕ := dsel j 410 (dpk j 409 BK_409) (dpk j 410 BK_410)
noncomputable def BKs391_395 (j : ℕ) : ℕ := dsel j 409 (BKs391_393 j) (BKs393_395 j)
noncomputable def BKs387_395 (j : ℕ) : ℕ := dsel j 407 (BKs387_391 j) (BKs391_395 j)
noncomputable def BKs395_397 (j : ℕ) : ℕ := dsel j 412 (dpk j 411 BK_411) (dpk j 412 BK_412)
noncomputable def BKs397_399 (j : ℕ) : ℕ := dsel j 414 (dpk j 413 BK_413) (dpk j 414 BK_414)
noncomputable def BKs395_399 (j : ℕ) : ℕ := dsel j 413 (BKs395_397 j) (BKs397_399 j)
noncomputable def BKs399_401 (j : ℕ) : ℕ := dsel j 416 (dpk j 415 BK_415) (dpk j 416 BK_416)
noncomputable def BKs401_403 (j : ℕ) : ℕ := dsel j 418 (dpk j 417 BK_417) (dpk j 418 BK_418)
noncomputable def BKs399_403 (j : ℕ) : ℕ := dsel j 417 (BKs399_401 j) (BKs401_403 j)
noncomputable def BKs395_403 (j : ℕ) : ℕ := dsel j 415 (BKs395_399 j) (BKs399_403 j)
noncomputable def BKs387_403 (j : ℕ) : ℕ := dsel j 411 (BKs387_395 j) (BKs395_403 j)
noncomputable def BKs372_403 (j : ℕ) : ℕ := dsel j 403 (BKs372_387 j) (BKs387_403 j)
noncomputable def BKs404_406 (j : ℕ) : ℕ := dsel j 421 (dpk j 420 BK_420) (dpk j 421 BK_421)
noncomputable def BKs403_406 (j : ℕ) : ℕ := dsel j 420 (dpk j 419 BK_419) (BKs404_406 j)
noncomputable def BKs406_408 (j : ℕ) : ℕ := dsel j 423 (dpk j 422 BK_422) (dpk j 423 BK_423)
noncomputable def BKs408_410 (j : ℕ) : ℕ := dsel j 425 (dpk j 424 BK_424) (dpk j 425 BK_425)
noncomputable def BKs406_410 (j : ℕ) : ℕ := dsel j 424 (BKs406_408 j) (BKs408_410 j)
noncomputable def BKs403_410 (j : ℕ) : ℕ := dsel j 422 (BKs403_406 j) (BKs406_410 j)
noncomputable def BKs410_412 (j : ℕ) : ℕ := dsel j 427 (dpk j 426 BK_426) (dpk j 427 BK_427)
noncomputable def BKs412_414 (j : ℕ) : ℕ := dsel j 429 (dpk j 428 BK_428) (dpk j 429 BK_429)
noncomputable def BKs410_414 (j : ℕ) : ℕ := dsel j 428 (BKs410_412 j) (BKs412_414 j)
noncomputable def BKs414_416 (j : ℕ) : ℕ := dsel j 431 (dpk j 430 BK_430) (dpk j 431 BK_431)
noncomputable def BKs416_418 (j : ℕ) : ℕ := dsel j 433 (dpk j 432 BK_432) (dpk j 433 BK_433)
noncomputable def BKs414_418 (j : ℕ) : ℕ := dsel j 432 (BKs414_416 j) (BKs416_418 j)
noncomputable def BKs410_418 (j : ℕ) : ℕ := dsel j 430 (BKs410_414 j) (BKs414_418 j)
noncomputable def BKs403_418 (j : ℕ) : ℕ := dsel j 426 (BKs403_410 j) (BKs410_418 j)
noncomputable def BKs418_420 (j : ℕ) : ℕ := dsel j 435 (dpk j 434 BK_434) (dpk j 435 BK_435)
noncomputable def BKs420_422 (j : ℕ) : ℕ := dsel j 437 (dpk j 436 BK_436) (dpk j 437 BK_437)
noncomputable def BKs418_422 (j : ℕ) : ℕ := dsel j 436 (BKs418_420 j) (BKs420_422 j)
noncomputable def BKs422_424 (j : ℕ) : ℕ := dsel j 439 (dpk j 438 BK_438) (dpk j 439 BK_439)
noncomputable def BKs424_426 (j : ℕ) : ℕ := dsel j 441 (dpk j 440 BK_440) (dpk j 441 BK_441)
noncomputable def BKs422_426 (j : ℕ) : ℕ := dsel j 440 (BKs422_424 j) (BKs424_426 j)
noncomputable def BKs418_426 (j : ℕ) : ℕ := dsel j 438 (BKs418_422 j) (BKs422_426 j)
noncomputable def BKs426_428 (j : ℕ) : ℕ := dsel j 443 (dpk j 442 BK_442) (dpk j 443 BK_443)
noncomputable def BKs428_430 (j : ℕ) : ℕ := dsel j 445 (dpk j 444 BK_444) (dpk j 445 BK_445)
noncomputable def BKs426_430 (j : ℕ) : ℕ := dsel j 444 (BKs426_428 j) (BKs428_430 j)
noncomputable def BKs430_432 (j : ℕ) : ℕ := dsel j 447 (dpk j 446 BK_446) (dpk j 447 BK_447)
noncomputable def BKs432_434 (j : ℕ) : ℕ := dsel j 449 (dpk j 448 BK_448) (dpk j 449 BK_449)
noncomputable def BKs430_434 (j : ℕ) : ℕ := dsel j 448 (BKs430_432 j) (BKs432_434 j)
noncomputable def BKs426_434 (j : ℕ) : ℕ := dsel j 446 (BKs426_430 j) (BKs430_434 j)
noncomputable def BKs418_434 (j : ℕ) : ℕ := dsel j 442 (BKs418_426 j) (BKs426_434 j)
noncomputable def BKs403_434 (j : ℕ) : ℕ := dsel j 434 (BKs403_418 j) (BKs418_434 j)
noncomputable def BKs372_434 (j : ℕ) : ℕ := dsel j 419 (BKs372_403 j) (BKs403_434 j)
noncomputable def BKs435_437 (j : ℕ) : ℕ := dsel j 452 (dpk j 451 BK_451) (dpk j 452 BK_452)
noncomputable def BKs434_437 (j : ℕ) : ℕ := dsel j 451 (dpk j 450 BK_450) (BKs435_437 j)
noncomputable def BKs437_439 (j : ℕ) : ℕ := dsel j 454 (dpk j 453 BK_453) (dpk j 454 BK_454)
noncomputable def BKs439_441 (j : ℕ) : ℕ := dsel j 456 (dpk j 455 BK_455) (dpk j 456 BK_456)
noncomputable def BKs437_441 (j : ℕ) : ℕ := dsel j 455 (BKs437_439 j) (BKs439_441 j)
noncomputable def BKs434_441 (j : ℕ) : ℕ := dsel j 453 (BKs434_437 j) (BKs437_441 j)
noncomputable def BKs441_443 (j : ℕ) : ℕ := dsel j 458 (dpk j 457 BK_457) (dpk j 458 BK_458)
noncomputable def BKs443_445 (j : ℕ) : ℕ := dsel j 460 (dpk j 459 BK_459) (dpk j 460 BK_460)
noncomputable def BKs441_445 (j : ℕ) : ℕ := dsel j 459 (BKs441_443 j) (BKs443_445 j)
noncomputable def BKs445_447 (j : ℕ) : ℕ := dsel j 462 (dpk j 461 BK_461) (dpk j 462 BK_462)
noncomputable def BKs447_449 (j : ℕ) : ℕ := dsel j 464 (dpk j 463 BK_463) (dpk j 464 BK_464)
noncomputable def BKs445_449 (j : ℕ) : ℕ := dsel j 463 (BKs445_447 j) (BKs447_449 j)
noncomputable def BKs441_449 (j : ℕ) : ℕ := dsel j 461 (BKs441_445 j) (BKs445_449 j)
noncomputable def BKs434_449 (j : ℕ) : ℕ := dsel j 457 (BKs434_441 j) (BKs441_449 j)
noncomputable def BKs449_451 (j : ℕ) : ℕ := dsel j 466 (dpk j 465 BK_465) (dpk j 466 BK_466)
noncomputable def BKs451_453 (j : ℕ) : ℕ := dsel j 468 (dpk j 467 BK_467) (dpk j 468 BK_468)
noncomputable def BKs449_453 (j : ℕ) : ℕ := dsel j 467 (BKs449_451 j) (BKs451_453 j)
noncomputable def BKs453_455 (j : ℕ) : ℕ := dsel j 470 (dpk j 469 BK_469) (dpk j 470 BK_470)
noncomputable def BKs455_457 (j : ℕ) : ℕ := dsel j 472 (dpk j 471 BK_471) (dpk j 472 BK_472)
noncomputable def BKs453_457 (j : ℕ) : ℕ := dsel j 471 (BKs453_455 j) (BKs455_457 j)
noncomputable def BKs449_457 (j : ℕ) : ℕ := dsel j 469 (BKs449_453 j) (BKs453_457 j)
noncomputable def BKs457_459 (j : ℕ) : ℕ := dsel j 474 (dpk j 473 BK_473) (dpk j 474 BK_474)
noncomputable def BKs459_461 (j : ℕ) : ℕ := dsel j 476 (dpk j 475 BK_475) (dpk j 476 BK_476)
noncomputable def BKs457_461 (j : ℕ) : ℕ := dsel j 475 (BKs457_459 j) (BKs459_461 j)
noncomputable def BKs461_463 (j : ℕ) : ℕ := dsel j 478 (dpk j 477 BK_477) (dpk j 478 BK_478)
noncomputable def BKs463_465 (j : ℕ) : ℕ := dsel j 480 (dpk j 479 BK_479) (dpk j 480 BK_480)
noncomputable def BKs461_465 (j : ℕ) : ℕ := dsel j 479 (BKs461_463 j) (BKs463_465 j)
noncomputable def BKs457_465 (j : ℕ) : ℕ := dsel j 477 (BKs457_461 j) (BKs461_465 j)
noncomputable def BKs449_465 (j : ℕ) : ℕ := dsel j 473 (BKs449_457 j) (BKs457_465 j)
noncomputable def BKs434_465 (j : ℕ) : ℕ := dsel j 465 (BKs434_449 j) (BKs449_465 j)
noncomputable def BKs466_468 (j : ℕ) : ℕ := dsel j 483 (dpk j 482 BK_482) (dpk j 483 BK_483)
noncomputable def BKs465_468 (j : ℕ) : ℕ := dsel j 482 (dpk j 481 BK_481) (BKs466_468 j)
noncomputable def BKs468_470 (j : ℕ) : ℕ := dsel j 485 (dpk j 484 BK_484) (dpk j 485 BK_485)
noncomputable def BKs470_472 (j : ℕ) : ℕ := dsel j 487 (dpk j 486 BK_486) (dpk j 487 BK_487)
noncomputable def BKs468_472 (j : ℕ) : ℕ := dsel j 486 (BKs468_470 j) (BKs470_472 j)
noncomputable def BKs465_472 (j : ℕ) : ℕ := dsel j 484 (BKs465_468 j) (BKs468_472 j)
noncomputable def BKs472_474 (j : ℕ) : ℕ := dsel j 489 (dpk j 488 BK_488) (dpk j 489 BK_489)
noncomputable def BKs474_476 (j : ℕ) : ℕ := dsel j 491 (dpk j 490 BK_490) (dpk j 491 BK_491)
noncomputable def BKs472_476 (j : ℕ) : ℕ := dsel j 490 (BKs472_474 j) (BKs474_476 j)
noncomputable def BKs476_478 (j : ℕ) : ℕ := dsel j 493 (dpk j 492 BK_492) (dpk j 493 BK_493)
noncomputable def BKs478_480 (j : ℕ) : ℕ := dsel j 495 (dpk j 494 BK_494) (dpk j 495 BK_495)
noncomputable def BKs476_480 (j : ℕ) : ℕ := dsel j 494 (BKs476_478 j) (BKs478_480 j)
noncomputable def BKs472_480 (j : ℕ) : ℕ := dsel j 492 (BKs472_476 j) (BKs476_480 j)
noncomputable def BKs465_480 (j : ℕ) : ℕ := dsel j 488 (BKs465_472 j) (BKs472_480 j)
noncomputable def BKs480_482 (j : ℕ) : ℕ := dsel j 497 (dpk j 496 BK_496) (dpk j 497 BK_497)
noncomputable def BKs482_484 (j : ℕ) : ℕ := dsel j 499 (dpk j 498 BK_498) (dpk j 499 BK_499)
noncomputable def BKs480_484 (j : ℕ) : ℕ := dsel j 498 (BKs480_482 j) (BKs482_484 j)
noncomputable def BKs484_486 (j : ℕ) : ℕ := dsel j 501 (dpk j 500 BK_500) (dpk j 501 BK_501)
noncomputable def BKs486_488 (j : ℕ) : ℕ := dsel j 503 (dpk j 502 BK_502) (dpk j 503 BK_503)
noncomputable def BKs484_488 (j : ℕ) : ℕ := dsel j 502 (BKs484_486 j) (BKs486_488 j)
noncomputable def BKs480_488 (j : ℕ) : ℕ := dsel j 500 (BKs480_484 j) (BKs484_488 j)
noncomputable def BKs488_490 (j : ℕ) : ℕ := dsel j 505 (dpk j 504 BK_504) (dpk j 505 BK_505)
noncomputable def BKs490_492 (j : ℕ) : ℕ := dsel j 507 (dpk j 506 BK_506) (dpk j 507 BK_507)
noncomputable def BKs488_492 (j : ℕ) : ℕ := dsel j 506 (BKs488_490 j) (BKs490_492 j)
noncomputable def BKs492_494 (j : ℕ) : ℕ := dsel j 509 (dpk j 508 BK_508) (dpk j 509 BK_509)
noncomputable def BKs494_496 (j : ℕ) : ℕ := dsel j 511 (dpk j 510 BK_510) (dpk j 511 BK_511)
noncomputable def BKs492_496 (j : ℕ) : ℕ := dsel j 510 (BKs492_494 j) (BKs494_496 j)
noncomputable def BKs488_496 (j : ℕ) : ℕ := dsel j 508 (BKs488_492 j) (BKs492_496 j)
noncomputable def BKs480_496 (j : ℕ) : ℕ := dsel j 504 (BKs480_488 j) (BKs488_496 j)
noncomputable def BKs465_496 (j : ℕ) : ℕ := dsel j 496 (BKs465_480 j) (BKs480_496 j)
noncomputable def BKs434_496 (j : ℕ) : ℕ := dsel j 481 (BKs434_465 j) (BKs465_496 j)
noncomputable def BKs372_496 (j : ℕ) : ℕ := dsel j 450 (BKs372_434 j) (BKs434_496 j)
noncomputable def BKs248_496 (j : ℕ) : ℕ := dsel j 388 (BKs248_372 j) (BKs372_496 j)
noncomputable def BKs0_496 (j : ℕ) : ℕ := dsel j 264 (BKs0_248 j) (BKs248_496 j)
noncomputable def BK (j : ℕ) : ℕ := (BKs0_496 j)
theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel
theorem blk_0 : Pyr.allFrom 0 133 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_1 : Pyr.allFrom 133 120 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_2 : Pyr.allFrom 253 120 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_3 : Pyr.allFrom 373 120 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_4 : Pyr.allFrom 493 19 (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel
theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by
  have h := (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add blk_0 blk_1) blk_2) blk_3) blk_4)
  exact h
theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok
noncomputable def TOPD : ℕ := 0x771dc4c1774a4127000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007736d3cd772999ea0000000000000000000000000000000000000000000000007717ea00774ef1d9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007756b900771117e400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000077102a37775387b20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000776bac5176fa052000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000076f85fa57765733976f79296776e428b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007775f64176edb2800000000000000000775a8ebc76fa912d000000000000000000000000000000000000000000000000000000000000000076ebb86177701b3300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000778b824576d524fd00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000076cf4c2a77891f560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000077bd4a25769d978c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007691f31277b880bc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000077fa76a77654e7c3000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000763c14ec77fffd1a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable def BKD_103 : ℕ := 0xec78d624f02c1ffeec78fe9ef02bd4deec7a85b2f02a35f8ec7d6e9ef02740eaec78d624f02bd4deec7a85b2f02740eaec78d624f02740ea8
noncomputable def BKD_104 : ℕ := 0xec83fc72f01ee998ec7ec02ef023a758ec7acd46f027242eec7829d8f0295a18ec7ec02ef01ee998ec7829d8f027242eec7829d8f01ee9988
noncomputable def BKD_105 : ℕ := 0xeca53736effffa34ec9b2138f0097192ec9234e6f011c6f6ec8a7b38f018f1a8ec9b2138effffa34ec8a7b38f011c6f6ec8a7b38effffa348
noncomputable def BKD_113 : ℕ := 0xef1f1b52ed94f418ef0bc3daeda8fe06eef7d118edbd9148eee35fe4edd28aeaef0bc3daed94f418eee35fe4edbd9148eee35fe4ed94f4188
noncomputable def BKD_118 : ℕ := 0xeffefcdaecabe3cceffca2ececae76c4eff94842ecb21070eff4ed4eecb6b098effca2ececabe3cceff4ed4eecb21070eff4ed4eecabe3cc8
noncomputable def BKD_119 : ℕ := 0xeffe6a22ecabc838f0000b32ecaa4b5ef000afe6eca9cf86f0005640ecaa5714effe6a22ecaa4b5ef0005640eca9cf86effe6a22eca9cf868
noncomputable def BKD_135 : ℕ := 0xed2320ceef970b60ed21c392ef985848ed2134deef98dc26ed217664ef989556ed21c392ef970b60ed2134deef989556ed2134deef970b608
noncomputable def BKD_136 : ℕ := 0xed2f68faef891c94ed2ad322ef8d5ae4ed26fee0ef90da02ed23e624ef93965ced2ad322ef891c94ed23e624ef90da02ed23e624ef891c948
noncomputable def BKD_137 : ℕ := 0xed48fb64ef710178ed418ab2ef781088ed3ac956ef7e72cced34bc80ef842314ed418ab2ef710178ed34bc80ef7e72cced34bc80ef7101788
noncomputable def BKD_150 : ℕ := 0xef81d81ced3ccdd0ef801188ed3e9b68ef7da576ed4112b0ef7a944aed44334cef801188ed3ccdd0ef7a944aed4112b0ef7a944aed3ccdd08
noncomputable def BKD_151 : ℕ := 0xef828118ed3c3148ef834cb2ed3b5ca8ef83751ced3b2f18ef82f92ced3ba9dcef828118ed3b5ca8ef82f92ced3b2f18ef828118ed3b2f188
noncomputable def BKD_167 : ℕ := 0xed9dc486ef27daa8ed9d44b0ef2852c4ed9d4bbaef2846d8ed9dda90ef27b5feed9d44b0ef27daa8ed9d4bbaef27b5feed9d44b0ef27b5fe8
noncomputable def BKD_168 : ℕ := 0xeda4c4bcef20c766eda2355aef233ce8eda025d4ef2534e2ed9e9854ef26ad32eda2355aef20c766ed9e9854ef2534e2ed9e9854ef20c7668
noncomputable def BKD_169 : ℕ := 0xedb3cba8ef123eacedaf5828ef168f50edab5906ef1a6dc2eda7d18aef1dd6c8edaf5828ef123eaceda7d18aef1a6dc2eda7d18aef123eac8
noncomputable def BKD_182 : ℕ := 0xef1af514edaaf572ef1a13a4edabf332ef18c35aedad6114ef17048aedaf3edaef1a13a4edaaf572ef17048aedad6114ef17048aedaaf5728
noncomputable def BKD_183 : ℕ := 0xef1a2910edab5b10ef1b0102edaa9b5aef1b6b6eedaa49faef1b679cedaa67d0ef1a2910edaa9b5aef1b679cedaa49faef1a2910edaa49fa8
noncomputable def BKD_199 : ℕ := 0xedd6dce0eef3b378edd603b8eef489b8edd58950eef502f8edd56e66eef51e7cedd603b8eef3b378edd56e66eef502f8edd56e66eef3b3788
noncomputable def BKD_200 : ℕ := 0xeddd60aeeeec4e28eddb0ca2eeee80d6edd91176eef05b00edd770c2eef1dafeeddb0ca2eeec4e28edd770c2eef05b00edd770c2eeec4e288
noncomputable def BKD_201 : ℕ := 0xedea02a2eee03666ede65f18eee3b69aede30c04eee6e6e4ede00bceeee9c4d4ede65f18eee03666ede00bceeee6e6e4ede00bceeee036668
noncomputable def BKD_203 : ℕ := 0xee1113f4eeba536aee0b5868eebfe760ee05d3eeeec544bcee008a36eeca67d4ee0b5868eeba536aee008a36eec544bcee008a36eeba536a8
noncomputable def BKD_210 : ℕ := 0xeec4b764ee072a92eebfbd1cee0c4d32eeba88c6ee11aa5aeeb51d78ee173eeaeebfbd1cee072a92eeb51d78ee11aa5aeeb51d78ee072a928
noncomputable def BKD_211 : ℕ := 0xeed62366edf5225aeed22d34edf93ecaeecdf224edfda0a4eec974a8ee024572eed22d34edf5225aeec974a8edfda0a4eec974a8edf5225a8
noncomputable def BKD_214 : ℕ := 0xeeee2f08eddb7230eeedef56eddbd30eeeed5bf2eddc87c2eeec7502eddd9036eeedef56eddb7230eeec7502eddc87c2eeec7502eddb72308
noncomputable def BKD_215 : ℕ := 0xeeebec82eddd2f02eeecf946eddc4414eeedb3aaeddbab26eeee1b10eddb6500eeebec82eddc4414eeedb3aaeddb6500eeebec82eddb65008
noncomputable def BKD_230 : ℕ := 0xedef252ceede536eedef6f1aeede0d86edf004e0eedd7d04edf0e660eedca200edef252ceede0d86edf004e0eedca200edef252ceedca2008
noncomputable def BKD_231 : ℕ := 0xedf0efc4eedc8516edf00cd4eedd671eedef7460eeddffe2edef2702eede4eceedf00cd4eedc8516edef2702eeddffe2edef2702eedc85168
noncomputable def BKD_232 : ℕ := 0xedf63d88eed52300edf4235eeed70a62edf24e3aeed8ab62edf0bf4aeeda049aedf4235eeed52300edf0bf4aeed8ab62edf0bf4aeed523008
noncomputable def BKD_233 : ℕ := 0xee013ab8eecae672edfe1bb8eecdd698edfb3b50eed0875aedf89b5aeed2f6c4edfe1bb8eecae672edf89b5aeed0875aedf89b5aeecae6728
noncomputable def BKD_246 : ℕ := 0xeed93984edf433aeeed8dbf4edf4a046eed83b9cedf55016eed758a2edf64300eed8dbf4edf433aeeed758a2edf55016eed758a2edf433ae8
noncomputable def BKD_247 : ℕ := 0xeed81648edf51de6eed8c24aedf47fd2eed92c74edf423c2eed9544cedf40a40eed81648edf47fd2eed92c74edf40a40eed81648edf40a408
noncomputable def BKD_263 : ℕ := 0xee0f4fdeeec081c6ee0ec348eec10de0ee0e714eeec16030ee0e5a60eec17848ee0ec348eec081c6ee0e5a60eec16030ee0e5a60eec081c68
noncomputable def BKD_264 : ℕ := 0xee1357b6eebbb848ee11dd76eebd1a48ee109a24eebe451aee0f8eb4eebf37b4ee11dd76eebbb848ee0f8eb4eebe451aee0f8eb4eebbb8488
noncomputable def BKD_295 : ℕ := 0xee1ad9deeeb6204aee1a3028eeb6cab4ee19b78aeeb744aaee197068eeb78dc8ee1a3028eeb6204aee197068eeb744aaee197068eeb6204a8
noncomputable def BKD_303 : ℕ := 0xee77bf46ee5a2a7aee73f3e8ee5de8ecee7021eeee61ae5aee6c4baaee657a2eee73f3e8ee5a2a7aee6c4baaee61ae5aee6c4baaee5a2a7a8
noncomputable def BKD_310 : ℕ := 0xeeb58c8aee1aa0f2eeb57512ee1acb3ceeb52ed8ee1b2406eeb4b9fcee1bab3eeeb57512ee1aa0f2eeb4b9fcee1b2406eeb4b9fcee1aa0f28
noncomputable def BKD_327 : ℕ := 0xee20bfb2eeb10edeee204ffceeb17e54ee200c18eeb1c27cee1ff43eeeb1db1aee204ffceeb10edeee1ff43eeeb1c27cee1ff43eeeb10ede8
noncomputable def BKD_328 : ℕ := 0xee23507ceeacd056ee222890eeaddb90ee2129aeeeaebcaaee20546eeeaf72f4ee222890eeacd056ee20546eeeaebcaaee20546eeeacd0568
noncomputable def BKD_329 : ℕ := 0xee297baeeea70f64ee27b74eeea8ba50ee2618b0eeaa3eccee24a0caeeab9bccee27b74eeea70f64ee24a0caeeaa3eccee24a0caeea70f648
noncomputable def BKD_342 : ℕ := 0xeeaf4d8aee22a222eeaed71cee231860eeae3882ee23b728eead7200ee247e3eeeaed71cee22a222eead7200ee23b728eead7200ee22a2228
noncomputable def BKD_343 : ℕ := 0xeeaf940aee226018eeafbed4ee2233aaeeafc16aee222fc8eeaf9baaee225496eeaf940aee2233aaeeaf9baaee222fc8eeaf940aee222fc88
noncomputable def BKD_359 : ℕ := 0xee2fc510eea30a86ee2fc046eea30e48ee2fe018eea2edc8ee302496eea2a8f4ee2fc046eea30a86ee2fe018eea2a8f4ee2fc046eea2a8f48
noncomputable def BKD_360 : ℕ := 0xee312c10eea17f06ee3095c8eea2105aee3022f6eea27e66ee2fd400eea2c8c4ee3095c8eea17f06ee2fd400eea27e66ee2fd400eea17f068
noncomputable def BKD_361 : ℕ := 0xee34dd3aee9de3b2ee33be9aee9efc90ee32c110ee9ff48aee31e558eea0cae8ee33be9aee9de3b2ee31e558ee9ff48aee31e558ee9de3b28
noncomputable def BKD_368 : ℕ := 0xee75c492ee5d9e0aee73170eee6051d6ee706202ee630c86ee6da79aee65cbb6ee73170eee5d9e0aee6da79aee630c86ee6da79aee5d9e0a8
noncomputable def BKD_369 : ℕ := 0xee8016d6ee5333d4ee7d9458ee55bc1aee7b04c8ee585198ee7869acee5af2c2ee7d9458ee5333d4ee7869acee585198ee7869acee5333d48
noncomputable def BKD_391 : ℕ := 0xee3b7ee4ee980e0eee3b8eb2ee97fd84ee3bbc34ee97cf84ee3c0766ee978414ee3b7ee4ee97fd84ee3bbc34ee978414ee3b7ee4ee9784148
noncomputable def BKD_392 : ℕ := 0xee3c6460ee9729deee3bfe4cee978d9aee3bb540ee97d47eee3b8982ee97fe4cee3bfe4cee9729deee3b8982ee97d47eee3b8982ee9729de8
noncomputable def BKD_393 : ℕ := 0xee3f1752ee94824eee3e4122ee95555cee3d863aee960d50ee3ce728ee96a9a4ee3e4122ee94824eee3ce728ee960d50ee3ce728ee94824e8
noncomputable def BKDs1_3 (j : ℕ) : ℕ := dsel j 105 (dpk j 104 BKD_104) (dpk j 105 BKD_105)
noncomputable def BKDs0_3 (j : ℕ) : ℕ := dsel j 104 (dpk j 103 BKD_103) (BKDs1_3 j)
noncomputable def BKDs4_6 (j : ℕ) : ℕ := dsel j 119 (dpk j 118 BKD_118) (dpk j 119 BKD_119)
noncomputable def BKDs3_6 (j : ℕ) : ℕ := dsel j 118 (dpk j 113 BKD_113) (BKDs4_6 j)
noncomputable def BKDs0_6 (j : ℕ) : ℕ := dsel j 113 (BKDs0_3 j) (BKDs3_6 j)
noncomputable def BKDs7_9 (j : ℕ) : ℕ := dsel j 137 (dpk j 136 BKD_136) (dpk j 137 BKD_137)
noncomputable def BKDs6_9 (j : ℕ) : ℕ := dsel j 136 (dpk j 135 BKD_135) (BKDs7_9 j)
noncomputable def BKDs10_12 (j : ℕ) : ℕ := dsel j 167 (dpk j 151 BKD_151) (dpk j 167 BKD_167)
noncomputable def BKDs9_12 (j : ℕ) : ℕ := dsel j 151 (dpk j 150 BKD_150) (BKDs10_12 j)
noncomputable def BKDs6_12 (j : ℕ) : ℕ := dsel j 150 (BKDs6_9 j) (BKDs9_12 j)
noncomputable def BKDs0_12 (j : ℕ) : ℕ := dsel j 135 (BKDs0_6 j) (BKDs6_12 j)
noncomputable def BKDs13_15 (j : ℕ) : ℕ := dsel j 182 (dpk j 169 BKD_169) (dpk j 182 BKD_182)
noncomputable def BKDs12_15 (j : ℕ) : ℕ := dsel j 169 (dpk j 168 BKD_168) (BKDs13_15 j)
noncomputable def BKDs16_18 (j : ℕ) : ℕ := dsel j 200 (dpk j 199 BKD_199) (dpk j 200 BKD_200)
noncomputable def BKDs15_18 (j : ℕ) : ℕ := dsel j 199 (dpk j 183 BKD_183) (BKDs16_18 j)
noncomputable def BKDs12_18 (j : ℕ) : ℕ := dsel j 183 (BKDs12_15 j) (BKDs15_18 j)
noncomputable def BKDs19_21 (j : ℕ) : ℕ := dsel j 210 (dpk j 203 BKD_203) (dpk j 210 BKD_210)
noncomputable def BKDs18_21 (j : ℕ) : ℕ := dsel j 203 (dpk j 201 BKD_201) (BKDs19_21 j)
noncomputable def BKDs22_24 (j : ℕ) : ℕ := dsel j 215 (dpk j 214 BKD_214) (dpk j 215 BKD_215)
noncomputable def BKDs21_24 (j : ℕ) : ℕ := dsel j 214 (dpk j 211 BKD_211) (BKDs22_24 j)
noncomputable def BKDs18_24 (j : ℕ) : ℕ := dsel j 211 (BKDs18_21 j) (BKDs21_24 j)
noncomputable def BKDs12_24 (j : ℕ) : ℕ := dsel j 201 (BKDs12_18 j) (BKDs18_24 j)
noncomputable def BKDs0_24 (j : ℕ) : ℕ := dsel j 168 (BKDs0_12 j) (BKDs12_24 j)
noncomputable def BKDs25_27 (j : ℕ) : ℕ := dsel j 232 (dpk j 231 BKD_231) (dpk j 232 BKD_232)
noncomputable def BKDs24_27 (j : ℕ) : ℕ := dsel j 231 (dpk j 230 BKD_230) (BKDs25_27 j)
noncomputable def BKDs28_30 (j : ℕ) : ℕ := dsel j 247 (dpk j 246 BKD_246) (dpk j 247 BKD_247)
noncomputable def BKDs27_30 (j : ℕ) : ℕ := dsel j 246 (dpk j 233 BKD_233) (BKDs28_30 j)
noncomputable def BKDs24_30 (j : ℕ) : ℕ := dsel j 233 (BKDs24_27 j) (BKDs27_30 j)
noncomputable def BKDs31_33 (j : ℕ) : ℕ := dsel j 295 (dpk j 264 BKD_264) (dpk j 295 BKD_295)
noncomputable def BKDs30_33 (j : ℕ) : ℕ := dsel j 264 (dpk j 263 BKD_263) (BKDs31_33 j)
noncomputable def BKDs34_36 (j : ℕ) : ℕ := dsel j 327 (dpk j 310 BKD_310) (dpk j 327 BKD_327)
noncomputable def BKDs33_36 (j : ℕ) : ℕ := dsel j 310 (dpk j 303 BKD_303) (BKDs34_36 j)
noncomputable def BKDs30_36 (j : ℕ) : ℕ := dsel j 303 (BKDs30_33 j) (BKDs33_36 j)
noncomputable def BKDs24_36 (j : ℕ) : ℕ := dsel j 263 (BKDs24_30 j) (BKDs30_36 j)
noncomputable def BKDs37_39 (j : ℕ) : ℕ := dsel j 342 (dpk j 329 BKD_329) (dpk j 342 BKD_342)
noncomputable def BKDs36_39 (j : ℕ) : ℕ := dsel j 329 (dpk j 328 BKD_328) (BKDs37_39 j)
noncomputable def BKDs40_42 (j : ℕ) : ℕ := dsel j 360 (dpk j 359 BKD_359) (dpk j 360 BKD_360)
noncomputable def BKDs39_42 (j : ℕ) : ℕ := dsel j 359 (dpk j 343 BKD_343) (BKDs40_42 j)
noncomputable def BKDs36_42 (j : ℕ) : ℕ := dsel j 343 (BKDs36_39 j) (BKDs39_42 j)
noncomputable def BKDs43_45 (j : ℕ) : ℕ := dsel j 369 (dpk j 368 BKD_368) (dpk j 369 BKD_369)
noncomputable def BKDs42_45 (j : ℕ) : ℕ := dsel j 368 (dpk j 361 BKD_361) (BKDs43_45 j)
noncomputable def BKDs46_48 (j : ℕ) : ℕ := dsel j 393 (dpk j 392 BKD_392) (dpk j 393 BKD_393)
noncomputable def BKDs45_48 (j : ℕ) : ℕ := dsel j 392 (dpk j 391 BKD_391) (BKDs46_48 j)
noncomputable def BKDs42_48 (j : ℕ) : ℕ := dsel j 391 (BKDs42_45 j) (BKDs45_48 j)
noncomputable def BKDs36_48 (j : ℕ) : ℕ := dsel j 361 (BKDs36_42 j) (BKDs42_48 j)
noncomputable def BKDs24_48 (j : ℕ) : ℕ := dsel j 328 (BKDs24_36 j) (BKDs36_48 j)
noncomputable def BKDs0_48 (j : ℕ) : ℕ := dsel j 230 (BKDs0_24 j) (BKDs24_48 j)
noncomputable def BKD (j : ℕ) : ℕ := (BKDs0_48 j)
theorem topD_ok : topOk2 TOPD BKD = true := by decide +kernel
theorem dblk_0 : Pyr.allFrom 0 112 (fun j => blockOk2 (BKD j) j) = true := by decide +kernel
theorem dblk_1 : Pyr.allFrom 112 103 (fun j => blockOk2 (BKD j) j) = true := by decide +kernel
theorem dblk_2 : Pyr.allFrom 215 114 (fun j => blockOk2 (BKD j) j) = true := by decide +kernel
theorem dblk_3 : Pyr.allFrom 329 183 (fun j => blockOk2 (BKD j) j) = true := by decide +kernel
theorem dblk_all : Pyr.allFrom 0 512 (fun j => blockOk2 (BKD j) j) = true := by
  have h := (Pyr.allFrom_add (Pyr.allFrom_add (Pyr.allFrom_add dblk_0 dblk_1) dblk_2) dblk_3)
  exact h
theorem lbD : LBSoundD TOPD BKD := lbDr_sound (blocks2_of dblk_all) topD_ok
noncomputable def REG : ℕ × ℕ × List (List ℕ) := (984427029232648270362177440545211561271274767355772679792014246692970529099121123198160622059521, 1017671488070813640073266609830480162040790493579660591113292136282035160360493930629788206104576, [[], [16448, 16512, 16576, 16640, 16704, 16768, 16832, 16896, 16960, 17024, 17088, 17152, 17280, 17408, 17536, 17664, 17792, 17920, 18048, 18176, 18304, 18432, 18560, 18688, 18944, 19200, 19456, 19712, 19968, 20224, 20480, 20736, 20992, 21504, 22016, 22528, 23040, 23552, 24064, 24576, 25600, 26624, 27648, 28672, 30720, 32768, 34672, 36576, 37528, 38480, 38956, 39432, 39670, 39908, 40146, 40265, 40324, 40384], [56836, 56905, 57042, 57179, 57316, 57590, 57864, 58412, 58960, 60056, 61152, 63344, 65536, 69632, 71680, 72704, 73216, 73472, 73600, 73664, 73728], [89985, 90051, 90182, 90444, 90968, 92016, 94112, 98304, 102272, 104256, 105248, 105744, 105992, 106116, 106178, 106240], [122372, 122441, 122578, 122852, 123400, 124496, 126688, 131072, 134784, 136640, 137568, 138032, 138264, 138380, 138496], [155204, 155272, 155408, 155680, 156224, 157312, 159488, 163840, 167648, 169552, 170504, 170980, 171218, 171337, 171456], [187845, 187914, 188052, 188328, 188880, 189984, 192192, 196608, 200256, 202080, 202992, 203448, 203676, 203790, 203904], [220295, 220367, 220510, 220796, 221368, 222512, 224800, 229376, 232928, 234704, 235592, 236036, 236258, 236369, 236480], [253190, 253261, 253402, 253684, 254248, 255376, 257632, 262144, 265792, 267616, 268528, 268984, 269212, 269326, 269383, 269440], [285768, 285840, 285984, 286272, 286848, 288000, 290304, 294912, 298400, 300144, 301016, 301452, 301670, 301888], [318536, 318608, 318752, 319040, 319616, 320768, 323072, 327680, 331296, 333104, 334008, 334460, 334686, 334912], [351812, 351880, 352016, 352288, 352832, 353920, 356096, 360448, 364384, 366352, 367336, 367828, 368074, 368197, 368320], [385156, 385416, 385936, 386976, 389056, 393216, 397248, 399264, 400272, 400776, 401028, 401154, 401217, 401280], [418244, 418760, 419792, 421856, 425984, 430016, 432032, 433040, 433544, 433796, 433922, 433985, 434048], [450754, 451012, 451528, 452560, 454624, 458752, 462784, 464800, 465808, 466312, 466564, 466690, 466816], [483522, 483780, 484296, 485328, 487392, 491520, 495552, 497568, 498576, 499080, 499332, 499584]])
theorem hR : rgOk REG = true := by decide +kernel
noncomputable def PTT_0 : PTrD := (.nd 59 (.nd 32 (.nd 29 (.nd 27 (.lf 25 [(512, 0xf7a0000000a236e17c4c3446613241264e)]) (.nd 28 (.lf 27 [(897, 0x8707f00000933b8aec5b2f9cff17f845a8)]) (.lf 28 [(0, 0x8700000a00927e87325beca0b816e5e551), (768, 0x1a3b700d008e26ed2a60443ac411042712), (994, 0x3895000008cead3906180545f0f7a0013)]))) (.nd 30 (.lf 29 [(0, 0x1c8e900e008cc143c961a9e4270f474fff), (512, 0x20e40010008a0ae6d1646041200c201b3d), (672, 0x20720010a08937e502653342f00b39da88), (768, 0x22eac0110088bab3c365b0742f0ab49f4c), (800, 0x2168f011208891359965d9f2590a890661), (832, 0x21a97011408867d615660351dd0a5dd50a), (864, 0x21e6601160883e9553662c92a00a330afd), (896, 0x221f3011808815736e6655b4850a08a7ea), (928, 0x22620011a087ec7082667eb77109deab86), (960, 0x22883011c087c38cab66a79b4809b51582)]) (.nd 31 (.lf 30 [(0, 0x2468301200877222a866f9054c09631b63), (96, 0x23d700126086f8ef5f6772389508eb1c67), (128, 0x2408f0128086d0c838679a5fbc08c3e63a), (160, 0x24544012a086a8c0df67c26715089d1448), (192, 0x24918012c08680d96f67ea4e850876a63f), (224, 0x24cf7012e086591200681215f408509bd2), (256, 0x26c600130086316aac6839bd48082af4af), (288, 0x252e1013208609e38b686144690805b086), (384, 0x26017013808594105668d7179f079832bf), (512, 0x289d60140084f8bf4c697268a9070b8c2e), (576, 0x277470144084abdc1a69bf4bdb06c77cc5), (608, 0x27afe0146084859c2669e58bcf06a604e7), (640, 0x27e4101480845f7d696a0baa8d0684ec80), (672, 0x281fe014a084397ff86a31a7fd0664333c), (736, 0x28a6a014e083ede9556a7d3ea10623dcd1), (768, 0x2aaf90150083c8504d6aa2d7a906043f02), (928, 0x2a0e0015a0830e4d516b5cdaa5056ba2d4), (960, 0x2a507015c082e97f516b81a8a6054e330d), (992, 0x2a9bb015e082c4d36d6ba6548905311f1f)]) (.lf 31 [(0, 0x2c90c0160082a049bb6bcade3b051466b4), (32, 0x2b0bf01620827be24d6bef45aa04f80976), (128, 0x2bd1101680820f7a596c5bad9e04a51172), (160, 0x2c127016a081eb9cb96c7f8b3e048a1d8e), (192, 0x2c52f016c081c7e1b96ca3463e046f8329), (224, 0x2c8fd016e081a4496d6cc6de8a045541ed), (256, 0x2e86c017008180d3e66cea5411043b5981), (320, 0x2d46001740813a516c6d30d68b040891c2), (352, 0x2d89e017608117449c6d53e35b03efb1c0), (416, 0x2deba017a080d194296d9993cf03bef7c0), (448, 0x2e238017c080aef0a66dbc375203a71d14), (480, 0x2e65d017e0808c705e6ddeb79a038f98d4), (512, 0x307b901800806a13606e01149803786aa9), (544, 0x2ef89018208047d9bc6e234e3c0361923a), (576, 0x2f318018408025c3816e456477034b0f2e), (608, 0x2f760018608003d0be6e67573a0334e12e), (640, 0x2fb13018807fe201836e892676031f07e1), (672, 0x2fc3e018a07fc055dd6eaad21c030982ed), (704, 0x3033b018c07f9ecddc6ecc5a1d02f451fa), (736, 0x306d9018e07f7d698d6eedbe6c02df74ae), (768, 0x326fc019007f5c28fe6f0efefa02caeab0), (832, 0x30f19019407f1a135a6f51149f02a2cf39), (864, 0x315b2019607ef93e5e6f71e99b028f3d0d), (896, 0x319c1019807ed88d596f929aa0027bfcc7), (928, 0x31d67019a07eb800566fb327a302690e10), (960, 0x321d4019c07e9797636fd390960256708c), (992, 0x32576019e07e77528c6ff3d56d024423e1)])))) (.nd 35 (.nd 33 (.lf 32 [(0, 0x3446f01a007e5731dc7013f61d023227b5), (32, 0x32bff01a207e3735617033f29902207bad), (64, 0x3310e01a407e175d247053cad5020f1f70), (96, 0x334a201a607df7a93370737ec701fe12a1), (128, 0x3397b01a807dd8199770930e6201ed54e7), (160, 0x33c9b01aa07db8ae5d70b2799d01dce5e7), (192, 0x3413901ac07d99678e70d1c06b01ccc545), (224, 0x3450001ae07d7a453670f0e2c401bcf2a7), (256, 0x3648d01b007d5b475e710fe09c01ad6db1), (288, 0x34b5d01b207d3c6e10712eb9e9019e3607), (320, 0x34ffa01b407d1db957714d6ea3018f4b50), (352, 0x3543b01b607cff293c716bfebe0180ad2e), (384, 0x355d801b807ce0bdc8718a6a3201725b47), (416, 0x35bfe01ba07cc2770471a8b0f50164553f), (448, 0x35ec301bc07ca454fa71c6d30001569ab9), (480, 0x3640501be07c8657b271e4d04801492b5b), (512, 0x383c101c007c687f347202a8c6013c06c8), (544, 0x36b1b01c207c4acb8972205c71012f2ca4), (576, 0x36cc201c407c2d3cb8723deb4201229c94), (608, 0x371e801c607c0fd2ca725b55300116563a), (640, 0x3751101c807bf28dc672789a34010a593b), (672, 0x37ae101ca07bd56db27295ba4800fea53a), (704, 0x37cb601cc07bb8729772b2b56300f339dc), (736, 0x3826701ce07b9b9c7b72cf8b7e00e816c3), (768, 0x3a2c401d007b7eeb6572ec3c9500dd3b92), (800, 0x387b301d207b625f5b7308c89f00d2a7ef), (832, 0x1b87201d407b45f86473252f9600c85b7b), (864, 0x3924001d607b29b6847341717600be55da), (896, 0x395d701d807b0d99c3735d8e3700b496af), (928, 0x3993c01da07af1a225737985d600ab1d9e), (960, 0x39d2a01dc07ad5cfaf7395584b00a1ea49), (992, 0x3a1ca01de07aba226873b105920098fc55)]) (.nd 34 (.lf 33 [(0, 0x3c1d301e007a9e9a5373cc8da700905362), (32, 0x3a9df01e207a83377573e7f0850087ef16), (64, 0x3acad01e407a67f9d374032e27007fcf12), (96, 0x3af9b01e607a4ce170741e468a0077f2fa), (128, 0x3b46701e807a31ee52743939a900705a70), (160, 0x3b6c601ea07a17207a7454078000690517), (192, 0x3bc7a01ec079fc77ee746eb00d0061f292), (224, 0x3c0f301ee079e1f4af7489334b005b2284), (256, 0x3d70001f0079c796c274a3913800549490), (268, 0xa80000079bdbd2974ad6ad20052304c), (288, 0x3c8c101f2079ad5e2974bdc9d1004e4857), (320, 0x3ca8a01f4079934ae674d7dd1400483d7e), (352, 0x1d7a001f6079795cfd74f1cafe004273a6), (384, 0x3d3ae01f80795f946e750b938c003cea72), (400, 0x389000007952be2a751869d0003a3df8), (416, 0x3d71701fa07945f13d752536bd0037a184), (428, 0x3ef00000793c5dad752eca4d0035b6ab), (448, 0x1dde401fc0792c736b753eb49000329880), (480, 0x1dff001fe079131af975580d02002dcf08), (490, 0xa4200000790b3700755ff0fb002c5d0c), (512, 0x3fd800200078f9e7e875714012002944be), (544, 0x1e3d20202078e0da3b758a4dc00024f945), (576, 0x138e00204078c7f1f175a3360a0020ec40), (608, 0x1e7830206078af2f0b75bbf8f0001d1d51), (640, 0x1e86c020807896918a75d4967100198c1a), (672, 0x1ea96020a0787e196d75ed0e8d0016383e), (704, 0x1ecb0020c07865c6b6760561450013215f), (736, 0x1eed5020e0784d9963761d8e9800104721), (768, 0x41b37021007835917576359686000da925), (800, 0x1f0fb02120781daeea764d7911000b470e), (832, 0x1f45e021407805f1c17665363a0009207f), (864, 0x1f6600216077ee59fb767cce000007351b), (896, 0xea8c0218077d6e7947694406700058482), (928, 0x1f8e0021a077bf9a8d76ab8d6e00040e59), (960, 0x1fc00021c077a872e376c2b5190002d242), (992, 0x41a57021e07791709376d9b7680001cfe0)]) (.lf 34 [(0, 0x304ec02200777a939d76f0945e000106d4), (64, 0x201c202240774d49b3771dde4800001f4d), (96, 0x3048c022607736dcb977344b4200000017), (128, 0x70ff022807720950e774a92ed000018c3), (160, 0x6d17022a0770a72ae7760b54d000068f3), (192, 0x68a0022c076f475957776b2660000f04a), (224, 0x6326022e076de9dc1778c8a3a0001ae6c), (256, 0x66000230076c8eb2e77a23ccd0002a2fa), (320, 0x5c8002340769df5b877cd324300052dea), (352, 0x5cbe023607688b2cd77e2752e0006c391), (384, 0x5d00023807673951277f792e900088e31), (416, 0x5d51023a0765e9c80780c8b7b000a8d6d), (480, 0x5519023e076351ac878360d33000f2844), (512, 0x58f20240076209197784a96640011c326), (544, 0x564102420760c2d7b785efa8000149131), (576, 0x53800244075f7ee6e7873398d00179208), (640, 0x53400248075cfdf69789b4892001e2aa7), (672, 0x5320024a075bc0f6478af18970021c1b6), (704, 0x512d024c075a8645578c2c3a500258a1f), (736, 0x4a6a024e07594de3578d649c500298386), (768, 0x4fee0250075817cfd78e9aafd002dad8d), (832, 0x4c6502540755b2928790ffed30036920f), (896, 0x49b102580753568987935bf62004034c4), (928, 0x4a29025a07522bf777948688300454c8c), (960, 0x4900025c075103b10795aecea004a92cc), (992, 0x485c025e074fddb5a796d4ca10050072a)]))) (.nd 36 (.lf 35 [(0, 0x48f90260074eba04c797f87ae0055a949), (96, 0x3fb40266074b5cabc79b55d3e00679e9b), (160, 0x4114026a074929dab79d88a4f007475b6), (224, 0x40f2026e07470025d79fb259d0081fb47), (256, 0x424002700745eeb467a0c3cb30088fe97), (320, 0x3bc802740743d2a067a2dfdf400978483), (384, 0x398901dff741bf9ba7a4f2e4000a6b1c9), (448, 0x3a00027c073fb5a0b7a6fcdef00b68398), (512, 0x3c600280073db4a9e7a8fdd5c00c6f71c), (544, 0x339f0282073cb78e37a9faf1700cf6ca1), (608, 0x1e1701a7e73ac41287abee6d100e0cd70), (768, 0x369f029007360a8027b0a7ff7010ede1a), (864, 0x3559029607334f7787b363081012c3fa2), (928, 0x33ca0000f7318884d7b529fac01408a01)]) (.nd 58 (.lf 36 [(0, 0x316202a0072eeea3b7b7c3dbf016000b0), (512, 0x265102c007225aa3a7c457dbe021b37ba), (768, 0x244e02d0071cde7cc7c9d402d0283f1b1), (928, 0xdd90295f719b53bf7ccfd43902c8c11c)]) (.lf 58 [(768, 0xc40801b007ba9ac9772c17b6504eedc2c)]))))) (.nd 65 (.nd 62 (.nd 60 (.lf 59 [(0, 0x3763f024407b89639e72e1c45e04970a65), (256, 0x48b6102b017b6787e37303a0190441ce38), (512, 0x4b86602d787b4433f97326f40303ef4615), (768, 0x24dd60305c7b1f82ce734ba52e039f8e52)]) (.nd 61 (.lf 60 [(0, 0x2300f02ad57af98fa07371985c0352c128), (128, 0xa1bf0353d7ae625dd73850220032d7a28), (256, 0x51350031317ad275ea7398b2120308f6ac), (384, 0x459e02b937abe833e73aca4bf02e53960), (512, 0x52290037707aaa515073c0d6ac02c244ce), (544, 0x27a8102a407aa53b5b73c5eca102b9a750), (768, 0x2566d03a977a813d9673e9ea66027ebf52), (864, 0x1858603d247a719e3773f989c60266425d)]) (.lf 61 [(0, 0x29fb503ed27a57568a7413d173023e77cf), (256, 0x522e0041517a2cb7f5743e700802017db4), (288, 0xa17e02d407a27589d7443cf6001fa1a90), (384, 0xe52f036867a172c827453fb7b01e441e6), (448, 0x237ad02a907a0c5941745ecebc01d5f4f8), (512, 0x598eb042d17a017d8f7469aa6e01c7de40), (640, 0x2432d02ea079ebae8d747f797001ac5412), (672, 0x28c1602ee079e636317484f1cc01a593a6), (736, 0x1a79e0444879db4052748fe7ab01983bdf), (768, 0x4c9000464b79d5c2ea749565130191a48c), (896, 0x4c8800278079bfbe1274ab69eb0177d0bc)]))) (.nd 63 (.lf 62 [(0, 0x58800049b579a9a36a74c18493015ed98b), (64, 0x25c5103387799e8ef874cc99050152b0f0), (96, 0x1d588030807999032674d224d7014cb16b), (128, 0x2a86d04a357993765674d7b1a70146bfc5), (160, 0x2625d03860798de89474dd3f690140dc00), (192, 0x5874004b27798859f074e2ce0d013b061f), (256, 0x2f04004cd0797d3a3174ededcc012f840f), (288, 0x2e3a004c767977a93274f37ecc0129d7e4), (320, 0x5b0a04c3e7972178474f91079012439a5), (352, 0x81c403ae0796c853674fea2c7011ea953), (384, 0x2e979031a07966f254750435a9011926f0), (416, 0x2716d03e8679615eec7509c9110113b27c), (448, 0x1c31704b75795bcb0b750f5cf3010e4bfa), (480, 0x2ef6004a7c795636bd7514f1400108f369), (512, 0x2f3bc04f217950a211751a85ec0103a8cc), (544, 0x1e69f04bd5794b0d1475201aea00fe6c23), (576, 0x6f6004c10794577d27525b02c00f93d6f), (608, 0x62159047c8793fe258752b45a500f41cb0), (640, 0x2f89d032a0793a4cb47530db4900ef09e7), (672, 0x163e004fa37934b6f37536710a00ea0515), (704, 0x2caec04a5f792f2122753c06db00e50e39), (736, 0x1ed99046ad79298b4e75419cb000e02553), (768, 0x32d19051cb7923f5837547327b00db4a64), (800, 0x288a504800791e5fcf754cc82f00d67d6c), (832, 0x1d1be04cf57918ca3e75525dc000d1be69), (864, 0x1f25f0461b791334de7557f32000cd0d5c), (896, 0x2d61f03f31790d9fbb755d884300c86a44), (928, 0x1a5fd051fa79080ae275631d1c00c3d521), (960, 0x1f663051f7790276607568b19e00bf4df2), (992, 0x1077e0527978fce241756e45bc00bad4b5)]) (.nd 64 (.lf 63 [(0, 0x65127054ef78f74e937573d96b00b6696a), (32, 0x1f1230539678f1bb6275796c9c00b20c10), (64, 0x311bf0514378ec28ba757eff4300adbca5), (96, 0x2e1df0512b78e696a97584915400a97b28), (128, 0xf10f0473b78e1053b758a22c300a54797), (160, 0x29d640536178db747c758fb38200a121f1), (192, 0x139de0526878d5e47975954385009d0a34), (224, 0x2eaff057d678d0553f759ad2bf0099005e), (256, 0x68193057b878cac6d975a061250095046d), (288, 0x1b48a056e078c5395575a5eea90091165f), (320, 0x1e53d0570078bfacbe75ab7b3f008d3632), (352, 0x205f50587378ba212275b106dc008963e2), (384, 0x1b8cd0594078b4968c75b6917200859f6f), (416, 0x179300577e78af0d0975bc1af50081e8d5), (448, 0x2f67c0578078a984a475c1a359007e4011), (480, 0x163420562c78a3fd6b75c72a93007aa521), (512, 0x37f0b05b00789e776975ccb09500771801), (544, 0x1ed87059007898f2ab75d23553007398ae), (576, 0x113e80594078936f3c75d7b8c200702726), (608, 0x126da05620788ded2875dd3ad5006cc365), (640, 0x17ea405a2e78886c7d75e2bb8100696d67), (672, 0x1c307055a57882ed4475e83ab900662529), (704, 0x1809e05c0d787d6f8c75edb8720062eaa8), (736, 0x181a00533f7877f35e75f3349f005fbdde), (768, 0x340d005ddf787278c975f8af35005c9eca), (800, 0x1f6fc059ce786cffd675fe282800598d65), (832, 0x34090053e57867889276039f6c005689ad), (864, 0x12c1f04aa078621309760914f50053939d), (896, 0x16e7f058e6785c9f46760e88b80050ab30), (928, 0x11b4205ec078572d557613faa9004dd063), (960, 0x1880f05df17851bd4276196abc004b0330), (992, 0x21e1105f3f784c4f17761ed8e600484393)]) (.lf 64 [(0, 0x320f1060407846e2e27624451c00459187), (32, 0x1d13f05f21784178ad7629af510042ed07), (64, 0x11e9604078783c1083762f177a0040560e), (96, 0x2d6fd061997836aa7176347d8d003dcc97), (128, 0xa00705e80783146817639e17d003b509c), (160, 0x176b6061f9782be4bf763f433f0038e218), (192, 0x206fe061f9782685367644a2c800368106), (224, 0x1784c0634b782127f1764a000d00342d60), (256, 0x36100063b8781bccfb764f5b030031e721), (288, 0xd4ce05a3e781674607654b39e002fae41), (320, 0x20bee0551378111e2b765a09d3002d82bd), (352, 0x1de4f05d20780bca66765f5d98002b648d), (384, 0x1dead065337806791d7664aee1002953ab), (416, 0xec680642078012a5b7669fda300275011), (448, 0xecd00658877fbde2b766f49d3002559b9), (480, 0x2312b066c577f69496767493680023709c), (512, 0x2370c066ea77f14da97679da55002194b4), (544, 0x1e52d05be077ec096e767f1e90001fc5f9), (576, 0x1e63d0645f77e6c7f07684600e001e0466), (608, 0x1e70c0541577e1893976899ec5001c4ff3), (640, 0x19b020588277dc4d55768edaa9001aa89a), (672, 0x1e9d9068ce77d7144d769413b100190e52), (704, 0x1129d0681e77d1de2c769949d200178116), (736, 0x100200695077ccaafc769e7d02001600dd), (768, 0x34cce069e077c77ac976a3ad3500148da0), (800, 0x187ff06a7777c24d9c76a8da6200132758), (832, 0x1889e06ac177bd238076ae047e0011cdfe), (864, 0x141ae06ad877b7fc7f76b32b7f00108188), (896, 0xb82f05d4077b2d8a376b84f5b000f41f1), (928, 0x169ff03bc077adb7f676bd7008000e0f2e), (960, 0x2430006c2377a89a8376c28d7b000ce93a), (992, 0xf606069fe77a3805476c7a7aa000bd00b)])))) (.nd 68 (.nd 66 (.lf 65 [(0, 0x7546e06d84779e697376ccbe8b000ac39a), (64, 0x3594b0618d779445c076d6e23e0008d0cd), (96, 0x190ee05d36778f390376dbeefb0007ea62), (192, 0x1aace05675778027b376eb004b000582a1), (224, 0x1941507030777b290676effef90004ce6e), (256, 0x453b5071f077762df476f4fa0a000426b4), (288, 0x4539506ea17771368876f9f17600038b6a), (352, 0x1af6007310776752c77703d538000279fd), (384, 0x234f3073b6776266847708c17a000203c8), (416, 0x235eb03bdf775d7e0d770da9f1000199dd), (448, 0x3a1f3072407758996a77128e9400013c32), (480, 0x14f8c073527753b8a577176f590000eabf), (512, 0x2122d0763f774edbc6771c4c380000a578), (704, 0x6e4203b907732027d7739258100000357), (736, 0x7050034c0772d41eb773de61300001234), (768, 0x6e1c03f20772885887742a27600002cee), (832, 0x648003c10771f196e774c0e90000085cb), (864, 0x612b025df771a69ca7750be340000c3da), (896, 0x649a097ff7715be767755698800010d9b), (928, 0x61a7057657711177b775a108300016302), (960, 0x621e03c90770c74e1775eb31d0001c406), (992, 0x61fe03cb07707d6b17763514d0002309a)]) (.nd 67 (.lf 66 [(0, 0x61de0a20077033cf37767eb0b0002a8b4), (32, 0x5a7d0269f76fea7b0776c804e00032c4a), (64, 0x5e80090de76fa16ef7771110f0003bb4e), (96, 0x5e600408076f58ab877759d46000455b7), (128, 0x580003d5076f10314777a24ea0004fb79), (160, 0x5a06040c076ec800b777ea7f30005ac88), (192, 0x56a403e8676e801a47783265a000668d9), (224, 0x591707c4776e387e77787a01700073060), (256, 0x595d0a30076df12dc778c152200080311), (288, 0x56200479f76daa28b779085730008e0e1), (320, 0x560003e1076d636fc7794f1020009c9c5), (352, 0x55e003e3076d1d036779957c8000abdaf), (384, 0x55c00a38076cd6e40779db9be000bbc93), (416, 0x53cc03bd576c9112377a216db000cc667), (448, 0x549e039c076c4b8e577a66f19000ddb1e), (480, 0x52880422076c0658e77aac270000efaab), (512, 0x52bb0a40076bc172677af10d800102502), (544, 0x4db70289f76b7cdb377b35a4b00115a17), (576, 0x4df5028bf76b3893d77b79ec1001299dd), (608, 0x4f9d028df76af49cb77bbde330013e448), (640, 0x50400771976ab0f6477c0189a0015394c), (672, 0x4bb7042c076a6da0f77c44def001698db), (704, 0x4e2e077ed76a2a9d277c87e2b001802e9), (736, 0x46c20295f769e7eb677cca9480019776a), (768, 0x4cf0085b0769a58c177d0cf3d001af64f), (800, 0x4c4709a4c769637f877d4f005001c7f8e), (832, 0x478102f5c76921c6477d90b99001e1317), (864, 0x47aa04d96768e060b77dd21f3001fb0df), (896, 0x463a029ff7689f4f477e1330a002158d9), (928, 0x484106d657685e92477e53eda00230af6), (960, 0x4881040907681e2a277e9455c0024c72a), (992, 0x46ae0313e767de17677ed468800268d68)]) (.lf 67 [(0, 0x478b0882c7679e5a477f1425a00285da3), (32, 0x45b0056fa7675ef3477f538ca002a37cc), (64, 0x40c00294e7671fe2b77f929d3002c1bd6), (96, 0x444d046da766e129077fd156d002e09b4), (128, 0x44c903c80766a2c697800fb9400300159), (160, 0x44e003c9f76664bbc7804dc41003202b6), (192, 0x41f5044e07662708f7808b76f00340dbd), (224, 0x42ea02b5f765e9ae7780c8d1600362262), (256, 0x42f808d00765acacb78105d3200384096), (288, 0x419502b9f76570041781427bd003a684c), (320, 0x40ed02e8876533b4d7817ecb1003c9974), (352, 0x415504580764f7bf6781bac08003ed402), (512, 0x3ebe0a800763d1432782e13cb004a83cb), (608, 0x34e00995976324dd77838da270051f412), (672, 0x388a02d1f762b3be6783fec1800571627), (704, 0x3a3b046e07627bbad78436c510059b465), (768, 0x39820a9007620ccd2784a5b2c005f0afe), (928, 0x33ca04034760fdf27785b48d6006cf91f)]))) (.nd 69 (.lf 68 [(0, 0x360f048207605fe9e7865295f0075b918), (64, 0x35300404075ff8712786ba0eb007bb737), (256, 0x30800623275ecb286787e7577008e7046), (352, 0x30200ab6075e39b2d78878cd00098351c), (512, 0x2dd306ad675d4f0707896378d00a9120f), (672, 0x2b740477b75c6e25178a445ad00baa288), (768, 0x29b40554075bebf3d78ac68c100c57f64)]) (.nd 87 (.lf 69 [(0, 0x26070ae0075aa24c378c1033a00e398b6), (256, 0x178f06632759725d778d4022701033e0d)]) (.lf 87 [(832, 0x101c00000078ead0b07580574e02fb3f67)]))))))
theorem PTT_0_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_0 = true := by decide +kernel
noncomputable def PTT_1 : PTrD := (.nd 119 (.nd 96 (.nd 93 (.nd 92 (.lf 91 [(256, 0xd265026fc789391a075d7965e01467bfd), (512, 0x1965a029c07887b11075e376ee012b99f1), (768, 0x102f0002e02787b3ae275efed1c0111ab58)]) (.lf 92 [(0, 0x1062703100786e387c75fcef8200f8bb85), (256, 0x2f71e033597860b37a760a748400e0d50c), (512, 0xea1f035987852b5af7618724f00ca01bf), (768, 0x1aae8039207844491a7626dee400b44aab), (832, 0x6da180388f78409dd5762a8a2a00af0a4b)])) (.nd 94 (.lf 93 [(0, 0x1557703c91783577df7635b01f009fb812), (64, 0x719603c537831b50a763972f4009ac203), (192, 0x7471036c0782a1f13764108eb00910e95), (224, 0x5e3d03e237828364e7642f1b0008ead9c), (256, 0x1bec303fe878264c447644dbba008c516a), (288, 0x1524503e88782460fa7646c7050089fa03), (320, 0x8d5103c00782274757648b38a0087a76a), (352, 0xa7a003d8d782086ba764aa144008559a2), (384, 0xc64f04068781e97cf764c9030008310ae), (416, 0xd99f037a0781ca7b8764e80460080cc90), (448, 0x61d804151781ab67c76507182007e8d4c), (512, 0x2190a041df7816d0a676545758007a1d5c), (576, 0xa718041607812e677765841870075c0f5), (672, 0xa66004330780cff65765e2899006f5b27), (736, 0xe56b0408478090b0f76621cef006b2fef), (768, 0x118710460078070f7776641888006921c0), (800, 0x1515a04620780512f27666150c00671887), (832, 0x7080045f7780315867668127800651446), (864, 0xe9a00466078011739766a10c500631500), (896, 0xc7b10439a77ff180f766c0fef00611ab7), (928, 0xb40e0465777fd180d766e0ff1005f256c), (960, 0xdafe0467777fb173a767010c4005d3523), (992, 0x1f7af0469777f9159a76721265005b49dd)]) (.nd 95 (.lf 94 [(0, 0x158cb0483f77f71332767414cc0059639c), (64, 0x814f046f777f30c2176781bde0055a630), (96, 0xa4a00476077f10782767a207d0053cf09), (128, 0xf47b04a0c77ef0230767c25ce0051fcef), (160, 0xbd6e04a1777ecfc32767e2bcd00502fe3), (192, 0xe5400477777eaf58b76803274004e67e7), (224, 0x7cf804af477e8ee41768239bd004ca4fc), (256, 0x3706d04bc677e6e65a768441a4004ae724), (288, 0x10a2004a6077e4dddb76864a2300492e61), (320, 0xcbb004c7577e2d4c97688533600477ab3), (384, 0xc24f04b0c77dec100768c66fe004422a0), (448, 0x100ed0487777daab2a76907cd40040def5), (480, 0xbb3604d1577d89f8776928877003f44c9), (512, 0x1a34d04eae77d693717694948d003dafbb), (544, 0x1038204e7377d486ec7696a112003c1fcc), (576, 0x1089503bc077d279fe7698ae00003a94fd), (608, 0x929104d9577d06cad769abb5200390f4f), (640, 0x10ae004cfd77ce5efc769cc90200378ec2), (672, 0x732d04fec77cc50f2769ed70c00361358), (704, 0xd57f047de77ca429476a0e56a00349d11), (736, 0x1321f0511177c833e776a2f41800332bef), (768, 0x7ff3a0517177c624f076a5030f0031bff2), (800, 0xb41f050a577c415b476a7124a0030591b), (832, 0xaea204e7577c2063976a921c6002ef76a), (896, 0x22c9504a3777bde69976ad4166002c437d), (928, 0xbdf70547177bbd67e76af5180002af143), (960, 0xc7cb0509877b9c63976b161c50029a431), (992, 0xfe6104cf077b7b5cf76b3723000285c48)]) (.lf 95 [(0, 0x814f50551e77b5a54376b582bb00271988), (32, 0x929f0416f77b3949d76b793620025dbf2), (64, 0xb7380418f77b183e076b9a41e0024a385), (96, 0xd2d30562177af731376bbb4ec00237042), (128, 0x81475055e177ad623976bdc5c50022422a), (160, 0x10f9604b5777ab515976bfd6a50021193b), (192, 0x801e0578077a9407876c1e787001ff577), (224, 0x3eebe057f177a72f9a76c3f865001ed6dd), (256, 0x18f9f058ac77a51ec476c6093a001dbd6d), (288, 0x9d2003e0e77a30dfc76c81a02001ca927), (320, 0x10dc003d0077a0fd4776ca2ab7001b9a0b), (352, 0x176b204c17779eecaa76cc3b54001a9019), (448, 0x46c005af37798bb9576d26c6900179139), (480, 0xe02005b8a7796ab8a76d47c7400169bea), (512, 0x2396b05b4277949bb176d68c4e0015abc3), (576, 0xd7cd0546577907ca576daab590013daea), (608, 0xca8105195778e6d7d76dcba810012fa38), (640, 0x7b8b05478778c5e9b76dec96400121eaa), (672, 0xb16b05ea0778a500276e0d7fc00114842), (704, 0x5eae05ec0778841b976e2e645001076fe), (736, 0x8abb05f80778633c476e4f43a000faadd), (768, 0x29dc205fb17784262876e701d6000ee3df), (800, 0xde2005f20778218eb76e90f14000e2202), (832, 0xcd6805f4077800c1076eb1bef000d6546), (864, 0xff1105e8c777dff9d76ed2861000cadaa), (896, 0xac2e0610d777bf39876ef3467000bfb2c), (928, 0x108980626e7779e80476f13ffb000b4dcb), (960, 0xaf89062887777dce776f34b18000aa587), (992, 0x6d70c062b37775d24576f555b9000a025e)])))) (.nd 99 (.nd 97 (.lf 96 [(0, 0x1f135063157773c82476f75fda0009644f), (32, 0xccce041207771be8876f969760008cb59), (64, 0x1123f06470776fb57776fb72880008377a), (96, 0x3ec003e60776dacf476fd7b0a0007a8b1), (128, 0xc5dd059ca776ba50676ff82f900071efd), (160, 0x1106d065b277699db077018a4f00069a5c), (192, 0x1335e06652776796f87703910700061acc), (224, 0x43f70659f776590e17705971d0005a04c), (256, 0x41efc067f177638b7277079c8c00052adb), (288, 0xfae004620776186af7709a1500004ba77), (320, 0xb029068d1775f829c770ba56200044f1d), (352, 0x9f20068db775d7f3f770da8c00003e8cd), (384, 0xf00006982775b7c9b770fab6300038784), (416, 0x1609e068d377597ab77711ad4800032b41), (448, 0x100fa06abe775779967713ae690002d402), (480, 0xb15406a577755793c7715aec2000281c5), (512, 0x1400206b53775379b07717ae4f00023487), (544, 0x5ba0050d777517af57719ad090001ec48), (576, 0x3f4f0478f774f7d10771baaee0001a904), (608, 0xbf9c06dd5774d8006771da7f800016aba), (640, 0x1c2f023f6774b83db771fa42300013167), (672, 0xcacc06f707749889577219f6a0000fd09), (704, 0x9a4006d3177478e36772399c90000cd9f), (736, 0xfa1006d57774594c57725933a0000a326), (768, 0x1b8360700777439c4577278bba00007d9b), (864, 0x5fbf0732c773db89c772d6f6200002a78), (896, 0x9512073c5773bc410772f63ee0000188e), (928, 0x53be049c07739d08c7731577200000b87), (992, 0x61fe073177735ecae77353b5100000013)]) (.nd 98 (.lf 97 [(0, 0x7477064677733fc5d77372ba2000001a2), (32, 0x6b670bc4077320d2677391ad900000809), (64, 0x6cf504a6077301f0d773b08f200001344), (96, 0x6bcc049af772e3216773cf5e800002350), (128, 0x65bf04aa0772c4647773ee1b80000382c), (160, 0x684e05dbe772a5ba27740cc5c000051d4), (192, 0x6615049587728722e7742b5d100007045), (224, 0x66170a7c0772689ed77449e120000937c), (256, 0x65b506dae7724a2e47746851a0000bb76), (288, 0x58a004a6f7722bd1877486ae60000e831), (320, 0x6146054587720d88d774a4f72000119a8), (352, 0x612005a1a771ef546774c32b800014fd9), (384, 0x584004acf771d1349774e14b600018ac0), (416, 0x5c4206607771b3299774ff5660001ca5b), (448, 0x5c5b07d247719533a7751d4c400020ea6), (480, 0x5c7c091d0771775317753b2cd0002579e), (512, 0x5d630801f7715988277558f7c0002a53f), (544, 0x5b6f048957713bd3177576ace0002f786), (576, 0x578004c607711e342775944bd00034e70), (608, 0x57610675c77100ab9775b1d460003a9f9), (640, 0x5857062d6770e339a775cf46500040a1d), (672, 0x572006961770c5de9775eca1600046eda), (704, 0x570006fda770a89ab77609e540004d82a), (736, 0x56c00460c7708b6e27762711c0005460c), (768, 0x57650ddc97706e5947764426a0005b87b), (800, 0x56a006720770515c47766123a00062f73), (832, 0x4c5c04540770347777767e0880006aaf1), (864, 0x52310b9a977017aaf7769ad5000072af0), (896, 0x525f04da076ffaf71776b788d0007af6e), (928, 0x533504dc076fde5c1776d423d00083866), (960, 0x4ef704de076fc1da3776f0a5b0008c5d4), (992, 0x4d20045e076fa571a7770d0e4000957b4)]) (.lf 98 [(0, 0x51270c02076f8922b777295d30009ee03), (32, 0x4fa007b6f76f6ced977745926000a88bc), (64, 0x4e2d04e6076f50d2877761ad7000b27db), (96, 0x49a10617e76f34d1b7777dae3000bcb5d), (128, 0x4ede057f076f18eb777799947000c733c), (160, 0x496c04ec076efd1ff777b55ff000d1f76), (192, 0x4a0004b5d76ee16f7777d1108000dd005), (224, 0x486e04f0076ec5da2777eca5c000e84e6), (256, 0x4ccf0c12076eaa605778081fa000f3e13), (352, 0x47ee0476076e5899c77859e6300118341), (416, 0x475504eef76e22a2c7788fdd300131be6), (480, 0x476e04f2f76ded1ee778c56100014c557), (512, 0x47bf0fe1076dd288b778dff730015a050), (544, 0x46d50504076db80ff778fa70000167f6f), (576, 0x42f0042bf76d9db4d77914cb1001762ae), (640, 0x43400432176d69587779492770019357b), (672, 0x432005c7876d4f57977963285001a24ff), (768, 0x43e01250076d020cd779b0732001d0bcc), (800, 0x415706b2076ce8873779c9f8c001e0b6b), (832, 0x41ed03a1976ccf20e779e35f1001f0f05), (864, 0x42600518076cb5da1779fca5d00201693), (896, 0x3c08050cf76c9cb3077a15cce00212213), (960, 0x3fb90443f76c6ac4d77a47bb1002344cf), (992, 0x3dc905a9776c51fe277a6081d00245c03)]))) (.nd 100 (.lf 99 [(0, 0x3fd31148076c3957e77a7928000257712), (32, 0x38650524076c20d2677a91ad9002695f9), (64, 0x35a00526076c086dc77aaa1230027b8b3), (96, 0x3cfe044df76bf02a377ac255b0028df39), (128, 0x3732051cf76bd807f77ada780002a0988), (256, 0x3b950c1d076b78cf377b39b0c002ed829), (416, 0x38600461f76b04caa77badb5400352d0b), (448, 0x30400463f76aedff177bc480e00367c06), (480, 0x356b049fe76ad756b77bdb2940037ce8d), (512, 0x37d6073fc76ac0d1b77bf1ae30039249d), (544, 0x36c3038bd76aaa70577c080f9003a7e2e), (576, 0x2fa8035d476a9432a77c1e4d4003bdb3c), (608, 0x3520053af76a7e18e77c34670003d3bc0), (640, 0x3532046ff76a6823377c4a5cb003e9fb6), (672, 0x3338053ee76a5251c77c602e300400717), (768, 0x33000740776a11b8577ca0c7a00445188), (992, 0x2de00552f769800e077d3271e004ec814)]) (.nd 101 (.lf 100 [(0, 0x2f70070797696bd5477d46aaa00505399), (64, 0x214303add76943d6177d6ea9e0053740e), (128, 0x289003b1d7691c70177d960fd0056a0eb), (192, 0x235c03acf768f5a4877dbcdb60059da00), (224, 0x2b200495f768e278f77dd006f005b7b10), (256, 0x2c630c5d0768cf74677de30b9005d1f1c), (288, 0xde003bbd768bc96e77df5e90005ec61e), (320, 0x2ac0049bf768a9e0b77e089f30060700f), (352, 0x1d0f03bfd7689751e77e1b2e100621cea), (384, 0x2a7e03c1d76884ea877e2d9560063cca7), (512, 0x2847058207683cda977e75a55006aa803), (608, 0x268e021d77680873377eaa0cb006fe9a9), (736, 0x1ef303d7d767c4ca877eedb560077116f), (768, 0x239c07300767b446377efe39b0078e1ed), (896, 0x1e530c85076773cfa77f3eb0400803d50)]) (.lf 101 [(0, 0x17000501e76735eea77f7c9140087c02f), (256, 0x12f51257f766c204577ff07ba009735e0)]))))) (.nd 127 (.nd 124 (.nd 122 (.lf 119 [(448, 0x1b17f00000780b202f766007d0015f1612)]) (.nd 123 (.lf 122 [(768, 0x1a1460242f77e004ee768b231000919958)]) (.lf 123 [(0, 0x159dd02a0077d9d32c769154d3008485e4), (256, 0x19d4402d4077d34b367697dcc90077f1b8), (768, 0x1d2730330277c54b7c76a5dc8200606113)]))) (.nd 125 (.lf 124 [(0, 0x1d3f6036b077bddd8576ad4a7a00557096), (256, 0x1aac00394677b62cea76b4fb14004b1753), (512, 0x1384003c7577ae3ee976bce91500415a4a), (768, 0x1499103f8077a618da76c50f2500383e14), (800, 0x36c20156077a5106c76c6179300372612), (992, 0x613d04257779ecdd776cc5a280030cc99)]) (.nd 126 (.lf 125 [(0, 0x18d80042e0779dc02d76cd67d2002fc6da), (128, 0xd653043ee7799829476d1a56a002bca4b), (224, 0x64d80435777964d6776d4da970028e8d1), (256, 0x177da0463f77953a6876d5ed960027f859), (512, 0x1766b04953778c8d2476de9ada0020d5e1), (768, 0x14cd004c927783be0776e769f7001a624d), (992, 0x403f04feb777bf18376ef367c00154e8f)]) (.lf 126 [(0, 0x1ff9d050e0777ad2c276f0553d0014a00b), (64, 0x116b5046b77778943576f293c900134b6d), (160, 0x5b2a0423f777533f476f5f40b00116193), (192, 0xdf4e03e747774134376f714bc0010c3ec), (256, 0x1af9e052ed7771d10b76f956f4000f9115), (416, 0xa39f05588776c271f76ff00e0000cc379), (448, 0x1232a0565a776b047a77002385000c3c75), (480, 0x1f65d056977769e1a37701465c000bb847), (512, 0x19308057cd7768be9e77026961000b36f1), (544, 0x6a610513077679b6c77038c92000ab872), (576, 0x64500586b776678127704afed000a3ccc), (640, 0x620505a80776430ed7706f71200094e09), (672, 0x13dfd05aa077630d2977081ad60008daee), (704, 0x1e6c0048e27761e94777093eb800086aab), (736, 0x950d05be07760c54a770a62b50007fd43), (768, 0x13cc005c00775fa135770b86ca000792b5), (800, 0xa49b04ace775e7d0b770caaf400072b01), (832, 0xc83505b00775d58cf770dcf300006c628), (864, 0x16780052df775c3484770ef37b00066429), (896, 0x1280205789775b102c771017d300060505), (928, 0x4c9f05ba07759ebca77113c350005a8bc), (960, 0x654f05e137758c7627712609d00054f4e), (992, 0xa05c05f497757a2f57713850a0004f8bc)])))) (.nd 130 (.nd 128 (.lf 127 [(0, 0x20b5905fd377567e887714a9770004a504), (32, 0x68ec0592077555a1c7715cde300045427), (64, 0xe3fe06110775435b47716f24a00040625), (96, 0xcabd0613077531154771816aa0003bafe), (128, 0xcab605ea97751ecff77193b00000372b2), (160, 0x8fa00538e7750c8b6771a5f4900032d41), (192, 0x10d9e06190774fa47d771b83820002eaab), (256, 0x20e0b06472774d5c46771dcbb900026e0d), (320, 0x4f4e05d40774b14707720138f0001fcd7), (352, 0x4dbe02e9f7749f0b07721374f0001c883), (480, 0x60b00663e774563147725c4ea000113aa), (512, 0x10f2e0692e774440147726e7eb0000ed90), (640, 0x1060806c80773fb602772b71fd0000718d), (672, 0x7e1806abe773e9407772c93f8000059a2), (768, 0x1e64b06fc5773b2f8b772ff874000022dc), (992, 0x69be0514d77334efa7737d904000005bd)]) (.nd 129 (.lf 128 [(0, 0x74c80b0947732302f7738f7d000000cd0), (32, 0x685706d30773111bf773a1640000016b0), (64, 0x71a10a100772ff3ab773b34530000235b), (96, 0x6c95054fe772ed5f8773c5207000032d1), (128, 0x6b0006080772db8a7773d6f5800004511), (160, 0x69970520d772c9bbb773e8c4300005a19), (192, 0x6ac006db0772b7f38773fa8c7000071ea), (224, 0x679706cfe772a631f7740c4e000008c81), (256, 0x69370c1ee772947737741e08c0000a9de), (288, 0x5fef0612077282c377742fbc80000c9ff), (352, 0x61d30739a7725f71a774530e50001128c), (384, 0x61530710c7724dd3e77464ac100013af4), (416, 0x653006e907723c3dc774764230001661d), (448, 0x6320066907722aaf777487d0800019405), (480, 0x61d90848e772192927749956c0001c4aa), (512, 0x62e0075af77207ab0774aad4f0001f80b), (544, 0x5be0066f0771f6352774bc4ad00022e28), (576, 0x5bc007f43771e4c7c774cdb83000266fe), (608, 0x5e1006f50771d3630774df1cf0002a28d), (640, 0x5f250ba75771c2070774f078f0002e0d3), (672, 0x5e6007541771b0b4077501cbf000321ce), (704, 0x5c05070c07719f6a17751315d0003657e), (736, 0x5c40066467718e297775245670003abe1), (768, 0x5b9307e1f7717cf24775358db0003f4f5), (800, 0x5ae0070107716bc4a77546bb4000440b9), (832, 0x5b3b06eba7715aa0d77557df200048f2b), (864, 0x5aa0054cd7714986d77568f920004e04a), (896, 0x5a800704f7713876f7757a09000053414), (928, 0x589d07090771277147758b0eb00058a88), (960, 0x58ee070b07711675f7759c0a00005e3a4), (992, 0x579f06c8877105853775acfac00063f67)]) (.lf 129 [(0, 0x5796083d8770f49f1775bde0e00069dce), (32, 0x55a0068f0770e3c3d775cebc20006fed8), (64, 0x52de052bf770d2f39775df8c600076284), (96, 0x530006930770c22e7775f05180007c8d0), (128, 0x53f707117770b174a776010b4000831b9), (160, 0x532706ab6770a0c6577611b9a00089d3f), (192, 0x53f9084ac77090238776225c600090b5e), (224, 0x516b065007707f8c877632f3600097c17), (256, 0x52de1237f7706f017776437e80009ef66), (288, 0x5030054ff7705e82677653fd9000a654a), (320, 0x4ef5065607704e0f977664706000addc0), (352, 0x5031075df7703da9177674d6e000b58c8), (384, 0x4f070745f7702d4f17768530e000bd65f), (416, 0x4dc2067c97701d01c776957e3000c5683), (448, 0x4ecd0650f7700cc13776a5bec000cd932), (480, 0x4f040732376ffc8da776b5f25000d5e6a), (512, 0x4df70cb4f76fec671776c618d000de629), (544, 0x4d6906af076fdc4dd776d6322000e706d), (576, 0x486a0666076fcc41f776e63e0000efd34), (608, 0x4b54065af76fbc439776f63c6000f8c7c), (640, 0x483f0729e76fac52d777062d200101e42), (672, 0x460a065ef76f9c6ff777161000010b285), (704, 0x4a90050de76f8c9af77725e4f00114942), (736, 0x4a1a0670076f7cd4177735abd0011e278), (768, 0x49f50b79476f6d1b77774564700127e23), (800, 0x462a0842376f5d713777550ec00131c42), (832, 0x464c06bd976f4dd5777764aa80013bcd3), (864, 0x4648066af76f3e4857777437a00145fd3), (896, 0x46ec067a076f2eca077783b5f00150540), (928, 0x45600669f76f1f5aa777932550015ad17), (960, 0x43b705af576f0ffa4777a285a00165757), (992, 0x45a507cac76f00a92777b1d6d001703fc)]))) (.nd 131 (.lf 130 [(0, 0x45ec0c8ee76ef1675777c118a0017b305), (32, 0x413e05a5e76ee2350777d04af0018646f), (64, 0x43e306f6076ed3124777df6db00191838), (96, 0x4420059cd76ec3ff4777ee80b0019ce5c), (128, 0x43b4067cf76eb4fc1777fd83d001a86db), (160, 0x42e005a0d76ea608f7780c770001b41b1), (192, 0x41d90628076e9725f7781b5a0001bfedb), (224, 0x3c4705a4d76e885337782a2cc001cbe58), (256, 0x41fe1277f76e7990d77838ef2001d8024), (288, 0x3cce058cb76e6adef77847a10001e443e), (320, 0x401e05b7e76e5c3dc77856423001f0aa2), (352, 0x3c8e05b9e76e4dad577864d2a001fd34e), (416, 0x3d090683876e30bf477881c0b00216b73), (448, 0x3d97056cc76e2261e778901e000223ae6), (480, 0x3bc0056ec76e1415d7789e6a200230c97), (512, 0x3de9082e876e05db2778aca4d0023e082), (544, 0x3bce0573e76df7b1f778bace00024b6a6), (576, 0x390e0827f76de99a7778c8e5800258efe), (608, 0x3bee0576c76ddb94a778d6eb400266988), (640, 0x3bf40578c76dcda0c778e4df200274642), (672, 0x3b4e0629f76dbfbee778f2c1000282529), (704, 0x3b2e05cfe76db1ef27790090c0029063a), (736, 0x386e07de776da431a7790e4e40029e972), (768, 0x3a400833776d968687791bf97002acecd), (832, 0x38f805e4876d7b67c77937183002c9fe6), (896, 0x384e05dbe76d6093d77951ec2002e796d), (928, 0x2f600703976d534637795f39c002f6952), (960, 0x349906b0f76d460ba7796c74500305b4a)]) (.nd 132 (.lf 131 [(0, 0x369e09b2c76d2bd0177986afe00324565), (32, 0x343905a9f76d1ecf477993b0a00333d83), (96, 0x303705adf76d05085779ad77a003533d0), (128, 0x30c00569e76cf8425779ba3d9003631f8), (192, 0x33d806ce076cdef1f779d38e00038343e), (224, 0x332005e4d76cd267b779e018400393855), (256, 0x335907c9576cc5f19779ec8e5003a3e60), (320, 0x322a06e1876cad42377a053dc003c5046), (384, 0x2f17062d576c94e4877a1d9b6003e69d6), (448, 0x2e9e05c3f76c7cd9677a35a6900408af7), (512, 0x2ec0072d076c6521977a4d5e50042b38e), (544, 0x2b2705f8d76c5965377a591ac0043ca9e), (608, 0xf3e0362076c422bd77a705410045fe35), (768, 0x2c000620876c0993077aa8ecf004b9e7c)]) (.lf 132 [(0, 0x27a80876b76bb375477aff0ab0054f87a), (32, 0x2774046db76ba915a77b096a400562b31), (64, 0x26bc054dd76b9ecca77b13b3500575f86), (96, 0x254a054fd76b949a377b1de5c00589574), (128, 0x24a2057c776b8a7e777b280170059ccf9), (256, 0x244b0626d76b62f4077b4f8bf005ebaa0), (320, 0x1f9f057d476b4fb8f77b62c7000613a9b), (512, 0x165a0643e76b1837577b9a48a0068ddd1), (640, 0xecf04fae76af50e177bbd71d006e1187), (768, 0x126505db976ad363477bdf1ca00735abf)]))))))
theorem PTT_1_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_1 = true := by decide +kernel
noncomputable def PTT_2 : PTrD := (.nd 163 (.nd 157 (.nd 154 (.nd 151 (.lf 133 [(512, 0x70005a9d76a298ab77c88f540094a09c), (768, 0x60005894769fd74f77cb50b000a03876)]) (.lf 151 [(512, 0x1b3670000077c796ad76a3915200f83d75)])) (.nd 155 (.lf 154 [(768, 0xcdb70251277acd8c176be4f3e006d6003)]) (.nd 156 (.lf 155 [(0, 0xe080028b277a8e55476c242ab006435c4), (256, 0x1ef0002c6877a4b89876c66f67005b5ccc), (768, 0x10482032c0779bbf0576cf68fa004aafe7)]) (.lf 156 [(0, 0x2ff000350f7796f85e76d42fa10042e400), (128, 0x1eb8003755779483f976d6a406003f2251), (256, 0x160ff0389c779204c076d9233e003b7964), (512, 0x175df03b80778ce78176de407e00347377), (768, 0x122a503f057787a40476e383fa002dd557)])))) (.nd 160 (.nd 158 (.lf 157 [(0, 0x14e3c0414777823dc476e8ea3a0027a1de), (128, 0xaad6043b4777f7eb576eba94a0024b0f1), (256, 0x1e700045ff777cb84976ee6fb60021dba1), (512, 0x1beb5048f17777172576f410d9001c84eb), (640, 0xd53c04a6077743d5776f6eaa8001a0408), (704, 0x6b7f018c07772ce5376f859ab0018ce4e), (768, 0x1e50004b7077715dfb76f9ca0400179fc3), (864, 0x83db04cab776f331876fbf4e70015e777)]) (.nd 159 (.lf 158 [(0, 0x1354704fa6776b907276ff978d00132de4), (96, 0x4a3d03f3577695ede7701c9210011a137), (128, 0xc27f04bf57768a330770284cf001120a6), (192, 0x73ed0512077672b247703fcdb00102506), (256, 0x12bac052e97765b238770575c6000f30c0), (320, 0x12b6c02f0a7764387d7706ef81000e43d9), (384, 0xc0bf04bd97762be01770869fd000d5e55), (448, 0x8c2705435776142d37709e52c000c8036), (480, 0x10dc00554a776084fe770aa301000c13ee), (512, 0x1e20005677775fc702770b60fd000ba981), (736, 0x1cdce03af7775a91737710968b0008f491), (768, 0x1e53f05a017759d2827711557d00089906), (864, 0x7fdf05bc67757952f771392d000079196), (896, 0x5c2105bfa7756d5ef7714521000073d83)]) (.lf 159 [(0, 0x1e00005e6b7753d86d77174f920005ffe2), (32, 0xd35c05f20775318f577180f0a0005b526), (64, 0xb5df05f40775259787718ce8700056c49), (96, 0xa9e705fc0775199f677198e090005254b), (128, 0x1b8c705f807750da72771a4d8c0004e02c), (160, 0x11f2005fa077501aef771b0d1000049ceb), (192, 0x128d805fd8774f5b6c771bcc9200045b89), (224, 0x808005fe0774e9bee771c8c1100041c06), (256, 0x1df0006255774ddc74771d4b8a0003de61), (320, 0x154e304e94774c5d99771eca66000368b4), (352, 0xdbe004895774b9e3a771f89c4000330ab), (384, 0x527a06080774adee9772049160002fa81), (416, 0x6f1f060fe774a1fa57721085a0002c635), (448, 0xbcdb0647c774960727721c78d000293c7), (480, 0x9af305e207748a151772286ae00026336), (512, 0x1de00066a57747e244772345bb00023484), (576, 0xa8dc058557746646c7724c3920001dcb7), (608, 0xed0d05ca47745a5a6772582590001b39d), (640, 0x819b04dae7744e6fa7726410400018c5f), (672, 0xb69006a747744286c7726ff93000166fe), (704, 0x371e03e64774369fc7727be0300014379), (736, 0x3b5f04c217742abad77287c52000121d0), (768, 0x149a006be37741ed8077293a7f00010202), (832, 0x4a3706c5e77407195772ab66a0000c7f9), (864, 0x118be04e8e773fb3da772b74250000adbc), (896, 0x603c06c9e773ef648772c31b700009559), (960, 0x8b0006e19773d7ba9772dac5600006a21), (992, 0x2621e070f7773cbe9e772e69610000574a)]))) (.nd 161 (.lf 160 [(0, 0x18759071f5773c01c5772f263a0000464c), (96, 0x7b460391c7739cc6d77315b9200001e5e), (128, 0x53cd05ec47739106777321798000014bc), (160, 0x545e05f607738549b7732d36400000cef), (192, 0x444f071ae7737990a77338ef5000006f8), (256, 0x1f71e07ce6773622a17735055e00000088), (288, 0x6d51085b6773567cc7735c0330000000d), (320, 0x74750722e7734ad3a77367ac500000164), (352, 0x739c072707733f2eb773735140000048e), (384, 0x6f880726e773338e27737ef1d0000098a), (416, 0x6de107aae77327f207738a8df00001056), (448, 0x6b4d077e07731c5a777396258000018f2), (480, 0x68600738477310c79773a1b860000235d), (512, 0x6af50782077305398773ad46700002f97), (544, 0x693008910772f9b04773b8cfb00003d9f), (576, 0x665d073cf772ee2c1773c453e00004d74), (608, 0x65fe077af772e2acf773cfd3000005f15), (640, 0x661e05340772d7331773db4ce00007281), (672, 0x61c8077ef772cbbe7773e6c17000087b9), (704, 0x5dc3070c0772c04f5773f230a00009eba), (736, 0x5aa0091ac772b4e5a773fd9a50000b783), (768, 0x62ed08afe772a981a77408fe50000d215), (800, 0x5f1f0740e7729e236774145c90000ee6f), (832, 0x5cc70788f77292cae7741fb5000010c8e), (864, 0x5aa009830772877867742b07900012c73), (896, 0x5be00861a7727c2bf7743654000014e1c), (928, 0x5ca80781b77270e5a774419a500017189), (960, 0x58990640077265a597744cda6000196b8), (992, 0x5d070792f7725a6bd774581410001bda9)]) (.nd 162 (.lf 161 [(0, 0x5c07090e27724f389774634760001e65a), (32, 0x59600796f772440be7746e741000210cb), (64, 0x59d90798f77238e5e774799a100023cfa), (96, 0x592007d6e7722dc6977484b9600026ae7), (160, 0x593d12564772179cb7749ae340002cbf4), (192, 0x55f307a0f7720c925774a5eda0002ff12), (224, 0x574c07a2f772018f1774b0f0d000333ea), (256, 0x56fd08557771f6932774bbecd00036a79), (288, 0x565f07e2e771eb9e8774c6e160003a2bf), (320, 0x54dd0663f771e0b16774d1ce90003dcbb), (352, 0x500a07aaf771d5cbd774dcb420004186b), (384, 0x531e07acf771caede774e7921000455cf), (416, 0x52c80768e771c017b774f2684000494e5), (448, 0x512008cb0771b5496774fd3690004d5ab), (480, 0x52e007c00771aa83077507fcf00051821), (512, 0x51510dd8a7719fc4b77512bb400055c46), (544, 0x44da07f2e771950e87751d7170005a217), (576, 0x4bde079e97718a609775281f60005e995), (608, 0x501e07c807717fbb077532c4f000632bd), (640, 0x4d310776e771751dd7753d62200067d8e), (672, 0x4ea707cc07716a89277547f6d0006ca07), (704, 0x4dbf07c0f7715ffd27755282d00071827), (768, 0x4db109a267714aff47756780a0007b954), (800, 0x4628079c8771408da77571f2400080c5f), (832, 0x4ca007a52771362517757c5ae0008610b), (864, 0x4b250784e7712bc5877586ba70008b757), (896, 0x4ac408d72771216f27759110d00090f41), (928, 0x485908e90771172207759b5de000968c8), (960, 0x48d0075e87710cde5775a5a1a0009c3ea), (992, 0x483f080ee77102a40775afdbf000a20a6)]) (.lf 162 [(0, 0x48ec0810e770f8734775ba0cb000a7efa), (32, 0x46f20745e770ee4c2775c433d000adee5), (64, 0x468907d8f770e42ec775ce513000b4066), (96, 0x459508f50770da1b2775d864d000ba37a), (128, 0x43ff13ea9770d0117775e26e8000c0821), (160, 0x463d074de770c611c775ec6e3000c6e58), (192, 0x44c90713f770bc1c1775f663e000cd61f), (224, 0x44260715f770b230a776004f5000d3f73), (256, 0x44f508c89770a84f67760a309000daa53), (288, 0x4450077207709e78777614078000e16be), (320, 0x42530824e77094abf7761dd40000e84b1), (352, 0x439b07eaf7708ae9f7762795f000ef42b), (384, 0x42fb075be77081329776314d6000f652b), (416, 0x42450750d7707785d7763afa1000fd7af), (448, 0x41c7088f17706de3e776449c100104bb5), (480, 0x40e70647d770644cc7764e3330010c13b), (512, 0x410009ed07705ac0877657bf700113840), (544, 0x40d407f6f770513f57766140a0011b0c2), (576, 0x3fda075ad77047c937766ab6c00122ac0), (608, 0x3f1707b4e7703e5e37767421b0012a637), (640, 0x3ef70978877034fe87767d81700132326), (672, 0x3d55068fc7702baa277686d5d0013a18b), (704, 0x39bf078c077022613776901ec00142164), (736, 0x3dbd07bce7701923b776995c40014a2b0), (768, 0x3d63097147700ff1c776a28e30015256c), (800, 0x3c470697c77006cb8776abb470015a998), (832, 0x3c27068cb76ffdb0f776b4cf000162f30), (864, 0x395007ff276ff4a23776bdddb0016b634), (928, 0x3941066ac76fe2a87776cfd780017c875), (960, 0x37f7063de76fd9bd9776d8c26001853b0), (992, 0x3a1306a3c76fd0ded776e1a120018e04d)]))))) (.nd 187 (.nd 165 (.nd 164 (.lf 163 [(0, 0x39ef08de176fc80c3776ea73c00196e4d), (96, 0x3809069eb76fadde477704a1b001b2085), (128, 0x37c0077ed76fa53d27770d42d001bb3f9), (160, 0x3513076fc76f9ca8977715d76001c48c5), (192, 0x36050782d76f9420a7771e5f5001cdee7), (224, 0x2e890755f76f8ba5577726da9001d765e), (256, 0x35a41532076f8336d7772f491001e0f27), (320, 0x34c7073e176f728067773fff8001f44a8), (416, 0x317b070d476f59d0377758afc00211e9f), (448, 0x2a060563c76f51afb77760d030021bf2c), (512, 0x32330918976f4196977770e960023040e), (544, 0x30da0873676f399e077778e1f0023a860), (576, 0x2f6406bcb76f31b2e77780cd000244df0), (672, 0x1451069ac76f1a42d777983d1002645fd), (768, 0x2f160844f76f034e0777af31e002848ea), (864, 0x2ca0069fd76eecd62777c5a9d002a567c), (992, 0x270307dd576ecfa61777e2d9e002d2369)]) (.lf 164 [(0, 0x2aff07c3e76ec87da777ea025002dd979), (128, 0x26c00553b76eac6bf7780613f0030bcc4), (256, 0x276e081ee76e91436778213c80033b151), (352, 0x24e00561b76e7d80077834fff0035f3b6), (512, 0x1f7b0705c76e5dbb077854c4f0039cbe6), (544, 0x19750114076e578db7785af23003a93ae), (576, 0x1b1f056fb76e516fb77861104003b5c6d), (704, 0x152005aea76e3990977878ef5003e88d1), (768, 0x14f90975576e2dfd97788482600402489)])) (.nd 166 (.lf 165 [(0, 0x129f06e9d76e0221c778b05e20046b66e), (256, 0xdf10806d76dda3bd778d8442004d7cae), (512, 0xcf105abb76db65d3778fc22c0054724a)]) (.nd 186 (.lf 166 [(0, 0x6b9058cf76d7aef57793790a0062d73d)]) (.lf 186 [(512, 0x1031800251b7780e1db76ea46240041b5cc), (768, 0x25f1d02523777e483276ecdfcd003bed73)])))) (.nd 190 (.nd 188 (.lf 187 [(0, 0xb3860289a777b86bd76efa14200365aad), (256, 0x1be6c02e9f77789f6776f2889700310082), (512, 0x1caff032137775943276f593cd002be1d4), (768, 0x8d5b034077772673176f8c0ce0027015b)]) (.nd 189 (.lf 188 [(0, 0x1de1e037af776f1a8a76fc0d74002261a7), (256, 0x12bef03b0b776bb07676ff7788001e051a), (768, 0x1d08e0418577648d2f77069ad000161e1e), (992, 0x579d0442f776150677709d79700130451)]) (.lf 189 [(0, 0x3f6e9044a07760d8b3770a4f4c00129790), (256, 0x17353048ac775d1033770e17cc000f5be7), (416, 0x1847d04a55775aa9d177107e2e000d7d50), (512, 0x1851e04b8e775936267711f1d9000c6c9d), (704, 0x4d9a04d92775648967714df69000a6c08), (768, 0x1829504ff977554d087715daf70009caf6)]))) (.nd 191 (.lf 190 [(0, 0x1e3de053007751575f7719d0a000077807), (96, 0xa1a00547f774fd887771b4f770006ad69), (128, 0x935f0555e774f58a0771bcf5f00066c5d), (160, 0xa1600557e774ed896771c4f6900062c92), (192, 0xb5b305271774e586a771ccf950005ee06), (224, 0x1a852054ff774dd81e771d4fe10005b0bc), (256, 0x1f4f7056b6774d57b2771dd04d000574b2), (384, 0x52ff05920774b54e6771fd31900049119), (416, 0x80cc04f97774ad3f27720540d00045b58), (480, 0x5c1e059f77749d1c47721563b0003f39e), (512, 0x18c9e059b57749508e7721d7710003c1a5), (640, 0x9d4e05cc077474afa7723dd0400030662), (672, 0xbabe05ce07746c96e77245e910002dabb), (704, 0x77ce05d00774647d47724e02a0002b057), (736, 0x993d05d207745c62f772561d000028738), (768, 0x24ea305f877745447e7725e38000025f5c), (896, 0x5da40605e77433d6b7727ea940001cc9a), (960, 0x7d7d06170774239c27728ee3d00018ad4)]) (.nd 192 (.lf 191 [(0, 0x1462a063c0774136127729f1ed00014e21), (64, 0xb91e0644f77403264772af59b00011680), (256, 0x4b14f06974773d27d2772e002d00008e08), (352, 0x6b7e06b40773ba30b772f84f400005ae6), (416, 0x69ed06cbe773aa022773087dd00003f22), (448, 0x38de06cde773a1ec67731093800003325), (512, 0x4085406f9e77391c4877320bb700001ef6), (544, 0x13be0020a077389b2877328cd7000016c3), (608, 0x7aa00e887737992b77338ed400000a24), (672, 0x74200617773697907734906f0000028e), (704, 0x95100637773616eb77351114000000a6), (768, 0x730e0c1b8773515f7773612080000009a), (864, 0x700a0a42c773395737737928c000009ee), (896, 0x6b3f09c707733158b7738127400000f8a), (928, 0x6ac007e8e773295c67738923900001666), (960, 0x6bb30812d77321626773911d900001e81), (992, 0x67890ad43773196ad77399152000027db)]) (.lf 192 [(0, 0x6ad50fed37731175b773a10a400003274), (32, 0x67e80a85f77309831773a8fce00003e4a), (64, 0x689e081ad77301932773b0ecd00004b5f), (96, 0x602906013772f9a5d773b8da2000059b0), (128, 0x64f7084df772f1bb5773c0c4a0000693f), (160, 0x633f0827c772e9d3b773c8ac400007a0a), (192, 0x634306dba772e1eef773d091000008c10), (224, 0x614208390772da0d3773d872c00009f53), (256, 0x61f709df0772d22e8773e05160000b3d0), (288, 0x603e09115772ca530773e82cf0000c988), (320, 0x5f4f06cc0772c27ab773f00540000e07a), (352, 0x5e3107fdf772baa5b773f7da40000f8a6), (384, 0x5ed909650772b2d41773ffabe0001120a), (416, 0x5eb909e90772ab05e774077a100012ca7), (448, 0x5d3e083fe772a33b37740f44c0001487c), (480, 0x5a60088ce7729b742774170bd00016588), (512, 0x5cd70922077293b0c7741ecf3000183cc), (544, 0x5a200810e7728bf11774268ee0001a345), (576, 0x5a58083ad772843537742e4ac0001c3f4), (608, 0x5a49097307727c7d47743602b0001e5d8), (640, 0x5a6e084be77274c947743db6b000208f1), (672, 0x549b0a76c7726d1947744566a00022d3d), (704, 0x578908440772656d77744d128000252bc), (736, 0x56c8084bc7725dc5c77454ba30002796f), (768, 0x58000853e772562257745c5da0002a152), (800, 0x51250884c7724e83377463fcc0002ca68), (832, 0x53280851c77246e887746b9770002f4ad), (864, 0x54ef0824e7723f524774732db00032023), (896, 0x53a40825277237c097747abf600034cc7), (928, 0x52c8085de77230337774824c800037a9a), (960, 0x51b3080ee77228ab177489d4e0003a99b), (992, 0x52560890c77221276774915890003d9c9)]))))))
theorem PTT_2_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_2 = true := by decide +kernel
noncomputable def PTT_3 : PTrD := (.nd 225 (.nd 219 (.nd 195 (.nd 194 (.lf 193 [(0, 0x52f80a1f977219a8877498d7600040b22), (32, 0x50d10972e772122e9774a051600043da8), (64, 0x512f0896c7720ab9a774a7c6500047158), (96, 0x505c08ca87720349a774af3640004a631), (128, 0x505e09950771fbded774b6a120004dc34), (160, 0x4f490831f771f4792774be06d0005135f), (192, 0x4f5e0940f771ed18b774c567400054bb2), (224, 0x4e9708a0c771e5bd9774ccc260005852b), (256, 0x4ee90980e771de67d774d41820005bfcb), (288, 0x49ff0946f771d7178774db6870005fb8f), (320, 0x4c10090bf771cfccc774e2b3300063877), (352, 0x477f07cb0771c8879774e9f8600067682), (384, 0x4c5e098ae771c1480774f137f0006b5b0), (416, 0x4bb0082ce771ba0e3774f871c0006f600), (448, 0x4a7a07a5d771b2da2774ffa5d00073770), (480, 0x4603084ce771ababf77506d40000779ff), (512, 0x4a3d0b54c771a483a7750dfc40007bdad), (544, 0x4895095697719d616775151e90008027a), (576, 0x48df08d76771964527751c3ad00084863), (608, 0x46b204e8a7718f2f07752350f00088f68), (640, 0x483507b1d771881f17752a60e0008d788), (672, 0x478306b4c77181156775316a8000920c2), (704, 0x3fa7085ae7717a121775386de00096b15), (736, 0x46df07a84771731517753f6ae0009b680), (768, 0x467f0f26d7716c1e877546617000a0302), (800, 0x451a09341771652e77754d518000a509a), (832, 0x44d80968f7715e450775543af000a9f47), (864, 0x444d08c8c771576227755b1dd000aef08), (896, 0x430908f237715086077561f9f000b3fdc), (928, 0x43120a10977149b0a77568cf5000b91c2), (960, 0x424006d5077142e217756f9de000be4b8), (992, 0x425707f6b7713c1a777576658000c38bf)]) (.lf 194 [(0, 0x42b20e29d7713559b7757d264000c8dd4), (32, 0x3edf089fc7712ea0077583dff000ce3f6), (64, 0x41c006d3e77127ed67758a929000d3b25), (96, 0x41610771a7712141e775913e1000d9360), (160, 0x3ac009d70771140087759e7f7000e46f2), (192, 0x237f08a2d7710d6ac775a5153000ea248), (224, 0x3d4608a4d77106dc6775aba38000efea4), (256, 0x3eb10961e77100558775b22a7000f5c06), (288, 0x3e140880e770f9d61775b8a9e000fba6d), (352, 0x3d9f0a5fa770ecede775c592100107a43), (416, 0x376006da0770e0247775d25b800113e1d), (448, 0x3ac0093ff770d9cb5775d8b490011a189), (480, 0x3ab8088ce770d37a2775df05d001205f1), (512, 0x3b210aecc770cd30c775e54f300126b56), (544, 0x37f508bfc770c6ef6775eb9090012d1b6), (576, 0x31c007edd770c0b60775f1c9f0013390f), (608, 0x362c04a20770ba84b775f7fb40013a160), (704, 0x368f0893f770a821c7760a5e20014e01a), (736, 0x374e07ae0770a2115776106ea00154c40), (768, 0x37e509c897709c0937761676c0015b958), (800, 0x36d109e2e770960977761c76700162761), (832, 0x35e208cad77090123776226dc00169659), (864, 0x2c6907f037708a237776285c80017063f), (896, 0x361f090ac770843d37762e42b00177711), (928, 0x3309090cc7707e5fa776342050017e8cf), (960, 0x30400781c770788ab77639f5400185b77), (992, 0x34ac087e077072be77763fc170018cf07)])) (.nd 196 (.lf 195 [(0, 0x345009f0e7706cfb07764584f0019437f), (32, 0x32b609247770674067764b3f90019b8dd), (64, 0x332c09c60770618ea77650f15001a2f1e), (96, 0x31620585d7705be5c776569a3001aa643), (128, 0x317c08ded7705645e7765c3a1001b1e4a), (160, 0x24e8083c077050af077661d0f001b9731), (192, 0x313c08e2e7704b214776675eb001c10f7), (224, 0x30200786b770459c97766ce36001c8b9a), (256, 0x30af09c4f77040211776725ee001d071a), (288, 0x2f99093567703aaec77677d13001d8373), (320, 0x2f470926c7703545b7767d3a4001e00a6), (384, 0x2f070755e7702a8fa77687f05001efd92), (416, 0x2c2008f0d7702542a7768d3d5001f7d48), (448, 0x2dc00794b7701fff27769280d001ffdd1), (480, 0x2a7b08c5f7701ac5177697bae00207f2c), (512, 0x2d1d08cee770159497769ceb600210157), (576, 0x29b908d2e7700b506776a72f900220818), (672, 0x26a40604d76ffc32c776b64d20023982f), (704, 0x2a640902d76ff73c7776bb43800241f1c), (768, 0x294309f2076fed6d6776c512900252f46), (800, 0x275f07ff676fe894c776c9eb30025b880), (832, 0x256407f0776fe3c61776ceb9e0026427b), (928, 0x214b07b2b76fd5964776dce9b0027e4e3), (960, 0x1e5907a8076fd0efe776e1901002871d3), (992, 0x21a8079ef76fcc53a776e62c50028ff7c)]) (.nd 197 (.lf 196 [(0, 0x25e10952c76fc7c1a776eabe500298ddc), (64, 0x2008034cc76fbebc7776f3c38002aacbe), (96, 0x23890958c76fba494776f836a002b3d3b), (224, 0x116006f9b76fa8e4c777099b3002d860e), (256, 0x16de0a40e76fa4a5d7770dda2002e19f1), (512, 0x131f0936d76f842cb7772e5340032d045), (736, 0xa000356076f69f9b7774886400370fd6), (768, 0x11a008b5c76f666767774c1880037ad81), (864, 0x920087fd76f5bf2f777568d0003989ce)]) (.lf 197 [(0, 0xd6a07d7176f4b654777671ab003cae3b), (256, 0x93d073bb76f3333b7777f4c30041cef7), (512, 0x94c0769676f1dde977794a1600470c29)])))) (.nd 222 (.nd 220 (.lf 219 [(0, 0xf63a02ef27766a145770486ba002218f1), (256, 0x122a9032a77764480b7706dff4001e5b37), (512, 0x12820036077761d4a977095356001acd7e), (768, 0xc1370394a775f48b8770bdf47001771c0)]) (.nd 221 (.lf 220 [(0, 0xcf3703b67775ca5e0770e821f001449da), (256, 0x2851d03e9e7759edd477113a2b00115783), (512, 0x229640431777572255771405aa000e9c52), (768, 0x1a9bb044217754452c7716e2d3000c19bb)]) (.lf 221 [(0, 0x1ea0004a177751582d7719cfd20009d10d), (256, 0x1415f04d78774e5d33771ccacc0007c371), (416, 0x5ae705081774c7a13771eadeb00069965), (512, 0x1839e04f91774b5621771fd1de0005f1ed), (768, 0x1cdb1055e0774844de7722e32100045d60)]))) (.nd 223 (.lf 222 [(0, 0x10ed8059ff77452b587725fca700030682), (160, 0x2388d05c207743380e7727eff100024fcc), (192, 0x665805c407742d3f27728540d00022e2f), (224, 0x2a0205d5577426fc17728b83d00020d8c), (256, 0x1c28005df777420b7f77291c800001ede4), (384, 0x3b7e05ece774079cf772aae3000017911), (480, 0x77b1060b9773f4bf8772bdc0700012bc1), (512, 0x2307306215773ee745772c40ba000113f3), (608, 0xb15f06414773db8f4772d6f0b0000d270), (672, 0x35320654d773cef45772e38ba0000abaf), (736, 0xd11d06500773c2583772f027c000088df), (768, 0x12040067b2773bc09d772f6762000078f2), (928, 0x47a00511a7739c81777315fe800003815), (960, 0xede706bfc773963347731c4cb00002e11)]) (.nd 224 (.lf 223 [(0, 0xf4e006ebf7738997c77328e8300001cfd), (128, 0x6e2007ac77370658773421a6000006a7), (320, 0x6cc007eae7734aadb77367d24000002a4), (352, 0x6f67059e1773446777736e18800000568), (384, 0x6eff0a68e7733e223773745db00000927), (416, 0x6f4006fcd77337de17737aa1e00000de1), (448, 0x62700759d773319b277380e4d00001396), (480, 0x6b910a6ee7732b5957738726a00001a45), (512, 0x6ea70967f7732518d7738d672000021ee), (544, 0x6bb30711e7731ed9a77393a6500002a91), (576, 0x6ca4158dd773189be77399e410000342e), (608, 0x6ba007699773125f8773a020700003ec4), (640, 0x6a7f063d47730c24b773a65b400004a54), (704, 0x692d076f9772ffb3d773b2cc20000645e), (736, 0x672007fa0772f97de773b9021000072d8), (768, 0x66c10ab9d772f349b773bf3640000824b), (800, 0x630f07a7b772ed174773c568b000092b5), (832, 0x60190a210772e6e6c773cb9930000a417), (864, 0x5d6009b7d772e0b82773d1c7d0000b671), (896, 0x614e07e63772da8b8773d7f470000c9c2), (928, 0x60e209b0d772d460f773de1f00000de09), (960, 0x61cf0b3e8772ce387773e44780000f347), (992, 0x5dd908a38772c8122773ea6dd0001097c)]) (.lf 224 [(0, 0x60db0b1cb772c1ee0773f091f000120a6), (32, 0x5d99077eb772bbcc2773f6b3c000138c5), (96, 0x5c600a96e772af8f977402f0600016be3), (128, 0x5e5806ef0772a974e774090b1000186e1), (160, 0x5d510900d772a35cb7740f2340001a2d2), (192, 0x5cd3091487729d4727741538d0001bfb8), (224, 0x5be00933b772973427741b4bd0001dd90), (256, 0x5bed1033e7729123d774215c20001fc5b), (288, 0x59f007f147728b1647742769b00021c19), (320, 0x57610917e772850b87742d74700023cc8), (352, 0x58c1081207727f039774337c600025e69), (384, 0x57c00712e77278fe977439816000280fb), (416, 0x579909c2777272fc87743f8370002a47d), (448, 0x53f50aace7726cfd8774458270002c8f0), (480, 0x56e409e1e772670197744b7e60002ee52), (512, 0x56ff0ac1e7726108c77451773000314a3), (544, 0x56270ab2e7725b132774576cd00033be3), (576, 0x547005f927725520c7745d5f300036411), (608, 0x5420077f57724f31a774634e500038d2c), (640, 0x509f087d97724945f774693a00003b735), (672, 0x5427095cc772435da7746f2250003e22a), (704, 0x519609bbc7723d78c7747507300040e0c), (736, 0x52fa0ac0e772379777747ae8800043ad8), (768, 0x52c915d9d77231b9c77480c6300046890), (800, 0x50400928d7722bdfa77486a0500049732), (832, 0x4f330a960772260937748c76c0004c6be), (864, 0x4f030a8af77220369774924960004f733), (896, 0x4da70a9a07721a67b7749818400052891), (928, 0x4c700a95e772149ca7749de3500055ad6), (960, 0x4ee709ffe7720ed59774a3aa600058e04), (992, 0x4edf0963b77209126774a96d90005c218)]))))) (.nd 230 (.nd 227 (.nd 226 (.lf 225 [(0, 0x4df00aa2077203534774af2cb0005f712), (32, 0x4a4b0798b771fd983774b4e7c00062cf1), (64, 0x4d3906f4c771f7e14774ba9eb000663b6), (96, 0x4adb0a730771f22e8774c051700069b5f), (128, 0x4b9008d40771ec7ff774c60000006d3eb), (160, 0x4b70063a0771e6d5b774cbaa400070d5a), (192, 0x4aac0a0fe771e12fc774d1503000747ac), (224, 0x4a3b082d4771db8e3774d6f1c000782df), (256, 0x4a120fd9e771d5f12774dc8ed0007bef3), (288, 0x47c00a7f0771d0588774e22770007fbe8), (320, 0x49400573d771cac47774e7bb8000839bc), (352, 0x48150aa26771c534f774ed4af0008786e), (384, 0x48170a850771bfaa2774f2d5d0008b7ff), (416, 0x47ec095de771ba240774f85bf0008f86d), (448, 0x46a80c8e6771b4a2a774fddd5000939b7), (480, 0x405f0a216771af2617750359e00097bde), (512, 0x46800af0e771a9ae677508d190009bedf), (544, 0x435807deb771a43b97750e446000a02bb), (576, 0x455d0989b7719ecdb77513b24000a4770), (608, 0x44d80abaf7719964d775191b2000a8cfe), (640, 0x41000a1ed771940107751e7ef000ad364), (672, 0x427b0ac5e7718ea2577523dda000b1aa2), (704, 0x435f0a22d7718948c77529373000b62b5), (736, 0x42920964d77183f467752e8b9000bab9f), (768, 0x42e00acbe7717ea5477533daa000bf55d), (800, 0x41d70903e771795b877539247000c3fef), (832, 0x41a00a66c771741707753e68f000c8b54), (864, 0x40200a39e7716ed7f77543a7f000cd78b), (896, 0x3fe5079aa771699e677548e19000d2494), (928, 0x3fce076db771646a47754e15b000d726d), (960, 0x3fa5088807715f3bb77553444000dc117), (992, 0x3e090bed07715a12b775586d4000e108f)]) (.lf 226 [(0, 0x3ee10adbe77154ef57755d90a000e60d4), (32, 0x3e3e092d87714fd1a77562ae4000eb1e7), (96, 0x3c1908deb77145a797756cd86000f5671), (128, 0x37010a4be771409b377571e4b000fa9e6), (160, 0x3a120858e7713b94c77576eb3000ffe24), (192, 0x3c3c08f1c771369437757bebc0010532b), (224, 0x3ae00ae9e7713199a77580e650010a8fa), (256, 0x3bb00aebe7712ca5077585daf0010ff8f), (288, 0x39e0163bd77127b687758ac97001156ea), (320, 0x39e406f8c77122ce17758fb1e0011af09), (352, 0x397f095df7711debc77594943001207ed), (384, 0x39a10af3e771190fa7759970500126193), (416, 0x390c09bfb7711439c7759e4630012bbfc), (448, 0x356a06de57710f6a3775a315c00131725), (480, 0x373f09c4a7710aa0e775a7df10013730e), (512, 0x38050a8bc77105ddf775aca200013cfb6), (544, 0x36ff07b5d77101217775b15e800142d1d), (576, 0x36df0af8f770fc6b6775b614900148b40), (608, 0x36bf08b87770f7bbc775bac420014ea1f), (640, 0x318009cdb770f312c775bf6d3001549b9), (672, 0x35df08a1e770ee704775c40fb0015aa0c), (704, 0x345c09a2d770e9d46775c8ab900160b19), (736, 0x315e07cc5770e53f3775cd40c00166cde), (768, 0x34a30b79e770e0b0b775d1cf40016cf59), (800, 0x304009a8d770dc28f775d65700017328a), (832, 0x33c509e6c770d7a7f775dad8000179670), (864, 0x30d80ae30770d32dd775df5220017fb09), (896, 0x2e3f09bbe770ceba8775e3c5700186055), (960, 0x30a009963770c5e8b775ec97400192d00), (992, 0x305806eb5770c18a3775f0f5c0019945e)])) (.nd 228 (.lf 227 [(0, 0x31170b50e770bd32c775f54d30019fc69), (32, 0x30400751f770b8e26775f99d9001a6521), (64, 0x302009f6c770b4991775fde6e001ace86), (224, 0x2ade0506f7709f96777612e98001ce769), (256, 0x2d750cbcc7709b78977617076001d54be), (320, 0x2ba6096c57709352e7761f2d1001e3153), (480, 0x289f060817707f7757763308a002063c2), (512, 0x29be0a12c7707b95577636eaa0020d617), (544, 0x28600589277077baf7763ac5000214907), (576, 0x2796064b277073e847763e97b0021bc90), (608, 0x1e9f093eb770701d47764262b002230b2), (640, 0x277b09aff7706c5a07764625f0022a56b), (672, 0x271e0631c770689e877649e1600231ab9), (736, 0x219003fe5770613f17765140e00240714), (768, 0x25d10b4be7705d9b277654e4d00247e1d), (960, 0x1d1f04040770486a97766a1560027540d)]) (.nd 229 (.lf 228 [(0, 0x1b1e0b2d0770419ac77670e5300284a61), (96, 0x13c50780177037a047767adfb0029bfd0), (256, 0x13460a42c77027a3c7768adc2002c3860), (416, 0xa200972b770187897769a075002ebd1d), (448, 0x11d505f6d770158967769cf69002f3f77), (512, 0x10580a16d7700fc47776a2bb700304588), (608, 0xa2003620770075d8776ab2270031d1f5), (768, 0xedb0649476ffa09b776b876300346f31)]) (.lf 229 [(0, 0xab40890776fe67f1776cc00e0038b2a6), (32, 0xa7b048a876fe435a776ce4a400393cc2), (256, 0x9b40babe76fd52ec776dd513003d0d25), (512, 0x7e30a85b76fc6218776ec5e700417be0)])))) (.nd 251 (.nd 247 (.lf 230 [(768, 0xc00757076f9d9c977714e3600587065)]) (.nd 250 (.lf 247 [(192, 0x1814000000776ee10676fc46f9005ed51a)]) (.lf 250 [(256, 0x1939101dc877652bc47705fc3b002b33fe), (512, 0xf2000274e7763a0b47707874b00278b67), (768, 0xf9cf02aba7761fcc577092b3a002402a8)]))) (.nd 252 (.lf 251 [(0, 0x1dc3f02e1877604113770ae6ec00209ba6), (256, 0x2315503100775e6ec5770cb93a001d5833), (512, 0x2cc1503280775c8711770ea0ee001a3a06), (768, 0x11df503673775a8b3777109cc8001742bf)]) (.nd 253 (.lf 252 [(0, 0x2b1c003ae677587c837712ab7b001473e3), (256, 0x1635003cd277565c4d7714cbb20011cedf), (512, 0x115ff0408877542bf27716fc0d000f5503), (768, 0x14f13044137751ecdd77193b22000d0783), (896, 0x7508046637750c83f771a5fc0000bf1bf)]) (.lf 253 [(0, 0x11e190474e774fa07c771b8783000ae779), (224, 0x6720049d5774d93e6771d941800093180), (256, 0x1eda804ab7774d4847771ddfb80008f5df), (448, 0xa99b04d0d774b7f41771fa8be00079fab), (480, 0xc6a004cfb774b3290771ff56f0007693f), (512, 0x1c7f204e14774ae5ba7720424500073393), (768, 0x1d067052e677487a577722ada80005a154), (864, 0xf7b0053cb7747901a772397e500051703), (896, 0xa04c053d7774741cf7723e6300004ea6e)]))))))
theorem PTT_3_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_3 = true := by decide +kernel
noncomputable def PTT_4 : PTrD := (.nd 284 (.nd 260 (.nd 257 (.nd 255 (.lf 254 [(0, 0x14be505603774607a37725205c00043fc6), (128, 0x1850056c07744cc0577265bfa0003a16a), (256, 0x193f50594c77438f26772798d900030f69), (448, 0x22c005b177741b1eb7729761400024bab), (480, 0x8f4a05d1c774162317729c5ce00022dc4), (512, 0x18a0f05eb67741126c772a1593000210a4), (768, 0x5004406278773e92ff772c9500000143ba), (800, 0x2160063f5773e42f4772ce50b00012da1), (896, 0x9fc0064ac773d52c1772dd53e0000f006), (992, 0x602006587773c6280772ec57f0000b974)]) (.nd 256 (.lf 255 [(0, 0x32e7f06771773c126b772f15940000a8d4), (32, 0x3719068e0773bc257772f65a8000098fc), (192, 0x69f406be7773a32287730f5d70000557e), (256, 0x19b7f06d757739923b773195c400003ff7), (448, 0xbda0072d67737b346773374b90000121c), (480, 0x19c2007340773763997733c46600000d31), (512, 0x2711207582773713f9773414060000090e), (704, 0x73f805667773537767735f08900000087), (736, 0x729e033f07734e84777363fb8000001d1), (768, 0x6ec40b6407734992a77368ed5000003e1), (800, 0x6ae00818077344a227736dddd000006b7), (864, 0x6a4005db37733ac5077377baf00000eb3), (896, 0x5f6004c1d77335d887737ca77000013d9), (928, 0x69ff0373977330ed677381929000019c3), (960, 0x5ee70b5fd7732c03c773867c200002072)]) (.lf 256 [(0, 0x67b60a96d77322353773904ac0000301e), (32, 0x631c086187731d504773952fb00003919), (64, 0x5d3f06c13773186d07739a12f000042d9), (96, 0x643d0af77773138b87739ef4700004d5b), (128, 0x61ba084407730eabb773a3d44000058a1), (160, 0x61ee080cd77309cdb773a8b24000064a9), (192, 0x62400673f77304f19773ad8e600007174), (224, 0x60a00951077300175773b268a00007f02), (256, 0x613a0cdf0772fb3f0773b740f00008d51), (288, 0x5e7e0b75d772f668b773bc17400009c62), (320, 0x551f0737f772f1946773c0eb90000ac34), (384, 0x5e0e0b4cf772e7f20773ca8df0000ce1b), (448, 0x5cc00b50f772de586773d42790000f304), (480, 0x59e008f9d772d98ee773d8f1100010698), (512, 0x5be70b83d772d4c7b773ddb8400011aeb), (544, 0x5a5f0ab8d772d002e773e27d100012ffd), (576, 0x5aa70c106772cb407773e73f8000145ce), (608, 0x59a0078c0772c6806773ebff900015c5d), (640, 0x59800ab07772c1c2e773f0bd1000173aa), (672, 0x565007b75772bd07e773f578100018bb4), (736, 0x51bd0823d772b3999773fee650001bdff), (768, 0x56d00b10c772aee67774039980001d83f), (800, 0x51400b740772aa35f774084a00001f33b), (832, 0x55440a9bf772a58837740cf7c00020ef2), (864, 0x53390b209772a0dd477411a2b00022b64), (896, 0x4fe00aced7729c353774164ac00024891), (928, 0x528c06b40772978ff7741af0000026678), (960, 0x4fe4063c077292eda7741f92500028518), (992, 0x50800baee7728e4e47742431b0002a471)]))) (.nd 258 (.lf 257 [(0, 0x51d70d0f077289b1e77428ce10002c483), (32, 0x511c0c440772851897742d6760002e54d), (64, 0x50200ba7d7728082677431fd9000306cf), (96, 0x4e7f0c3af7727bef47743690b00032908), (128, 0x4faa0a82d772775f67743b20900034bf8), (160, 0x4f4d0b8c077272d2b7743fad400036f9e), (192, 0x4b63090ea7726e4947744436b000393fa), (224, 0x4bc00898a77269c3277448bcd0003b90b), (256, 0x4d7e0cd61772654057744d3fa0003ded1), (288, 0x4a0e08c3877260c0e77451bf10004054b), (320, 0x4c100a67d7725c44f774563b000042c79), (352, 0x4c1f0c86e77257cc77745ab3800045459), (384, 0x4aa10b9a0772535777745f28800047ced), (416, 0x479f0b6ac7724ee5f774639a00004a632), (448, 0x44a804d907724a7827746807d0004d029), (480, 0x48b90ba00772460de7746c7210004fad0), (512, 0x49c70bbbe77241a7577470d8a00052628), (544, 0x478e0ba407723d448774753b700055230), (608, 0x47d008ae2772348a27747df5d0005ac4c), (640, 0x46350a8507723032b774824d40005da5f), (672, 0x46dd0b2fb7722bdf177486a0d00060920), (704, 0x45c007ae0772278f77748af080006388d), (736, 0x45d5074bf7722343c7748f3c3000668a7), (768, 0x45fc0be0e7721efc07749383f0006996c), (800, 0x4404097007721ab8577497c7a0006cadc), (832, 0x40f70ba8f7721678b7749c0730006fcf6), (864, 0x43e10be70772123d4774a042b00072fba), (896, 0x437e0b4107720e05e774a47a100076327), (928, 0x429e06be077209d2b774a8ad40007973c), (992, 0x3da40905077201792774b106d0008015c)]) (.nd 259 (.lf 258 [(0, 0x41fe0d4f0771fd52c774b52d300083766), (32, 0x3fa90797e771f930c774b94f300086e16), (64, 0x3b2e0d348771f5131774bd6ce0008a56b), (128, 0x3e320d680771ece51774c59ae00091601), (160, 0x3e1f076f2771e8d4d774c9ab200094f40), (192, 0x3e1e088ed771e4c90774cdb6e00098922), (256, 0x3dde0bf3d771dcbf4774d5c0b0009fec9), (288, 0x3dbe06699771d8c15774d9bea000a3a8d), (320, 0x354b06090771d4c80774ddb7f000a76f0), (352, 0x3c000bf9d771d0d37774e1ac8000ab3f2), (384, 0x3ae60c37c771cce3a774e59c5000af192), (416, 0x3be206f20771c8f89774e9876000b2fcf), (448, 0x3a8009e79771c5125774ed6da000b6ea8), (480, 0x3a3b0908b771c130f774f14f0000bae1d), (512, 0x3ac00c03d771bd547774f52b8000bee2d), (576, 0x39470b458771b5aa4774fcd5b000c7019), (608, 0x38ff06d4e771b1dca77500a35000cb1f5), (640, 0x35b30b2f3771ae141775046be000cf468), (672, 0x32a608c47771aa508775082f7000d3772), (704, 0x36ec08840771a69217750bede000d7b13), (736, 0x36210c11d771a2d8b7750fa74000dbf48), (768, 0x36f10c4fc7719f249775135b6000e0413), (832, 0x366c09fce77197cbd7751ab42000e8f62), (864, 0x34a308ab4771942757751e58a000ed5e5), (896, 0x33b905b007719088277521f7d000f1cf9), (928, 0x33990bfc07718cee47752591b000f649e), (960, 0x344308a1b7718959b77529263000facd2), (992, 0x32dd0b54d77185ca97752cb56000ff596)]) (.lf 259 [(0, 0x33d60c2b77718240e775303f100103ee7), (64, 0x31ac0c27d7717b3dd775374220010d32f), (96, 0x320a0c29d77177c487753abb700111e25), (128, 0x2f98074607717450d7753e2f2001169a6), (224, 0x2f4206fa37716a1727754868d00124f5d), (256, 0x2fef0b95b77166b9e7754bc6100129cff), (320, 0x2d0005f2e77160107775526f8001339d4), (352, 0x2ca005d397715cc4677555bb900138905), (416, 0x2d1404fa0771563d97755c426001428f2), (480, 0x2c110b74d7714fce177562b1e0014cae5), (512, 0x2ca50c50e7714c9f377565e0c00151c9e), (608, 0x2b200af1d771433617756f49e001614c0), (640, 0x29b5077d0771401f07757260e00166870), (672, 0x292005b9f7713d0e07757571f0016bc9a), (704, 0x279f07d177713a031775787ce0017113f), (768, 0x28f70cf2077133ff67757e8090017bbf3), (800, 0x27cf07c957713106c7758179300181201), (928, 0x245606fa0771256207758d1de00196ecd), (992, 0x23f20441f7711fb5277592cad001a1fe6)])))) (.nd 279 (.nd 261 (.lf 260 [(0, 0x25400c9fc7711ce827759597d001a791c), (32, 0x20fc033607711a218775985e7001ad2c1), (256, 0x17800ba6d77107663775ab19c001d5226), (512, 0xedd097f8770f3851775befae0020450f)]) (.nd 263 (.lf 261 [(512, 0x99b0c25b770b50d3775fd72c002ce978), (768, 0x58004a53770a9d9b77608a6400303de8)]) (.lf 263 [(128, 0x86e17708cf32776258cd00433707)]))) (.nd 282 (.lf 279 [(0, 0x3c700000007760be7d770a698100448cc7)]) (.nd 283 (.lf 282 [(0, 0x1f5b9022bf77593a787711ed87001e83f8), (512, 0x1b580028547756b36e7714749100192372), (768, 0x1e03702d607755521a7715d5e500169aab)]) (.lf 283 [(0, 0x120f5030207753de18771749e700142e3a), (256, 0x4bee0031bf775258587718cfa70011df8d), (512, 0xae400362c7750c1d7771a6627000faffc), (640, 0x87d1037e6774ff0a0771b375f000ea445), (704, 0x1a5f1038fd774f8695771ba169000e217e), (768, 0x1160003945774f1b9c771c0c63000da0cc)]))))) (.nd 290 (.nd 287 (.nd 285 (.lf 284 [(0, 0x1af8003dc9774d66b4771dc14b000bb32e), (256, 0x1457203e67774ba438771f83c70009e83b), (480, 0x4c04042ee774a0fc977211836000873e4), (512, 0x40c08044a07749d546772152b9000840f8), (768, 0x2b97a047f57747fb0677232cf90006be53), (960, 0x413d049e47746909e772497600005b4e1)]) (.nd 286 (.lf 285 [(0, 0x1b52604be2774616a37725115c00056122), (160, 0xf09f04d7b7744e348772644b700049a3f), (256, 0x2e35e04fa1774429507726feaf00042a25), (352, 0x11d4f04fd477436e427727b9bd0003bf82), (512, 0x16fa005232774234447728f3bb00031a01), (768, 0x1494005780774038b9772aef4600023146), (960, 0x1a51e05922773eb88d772c6f7200019cdd)]) (.lf 286 [(0, 0x47f4005be7773e37ee772cf01100017067), (224, 0x1fffb05eb2773c73ea772eb4150000e8a2), (256, 0x20459060c0773c3323772ef4dc0000d7c3), (384, 0x8bdb06232773b2fa3772ff85c00009a9d), (448, 0x4c7d0646d773aadae77307a5100007fd7), (512, 0x3c3c306517773a2b9c7730fc630000679c), (576, 0x4fba0672a7739a97277317e8d000051eb), (704, 0x13720069a27738a4ed7732831200002e2b), (768, 0x2e4c006bcb7738229b773305640000201c), (960, 0xab7b0707f77369ba577348c5a00000536)]))) (.nd 288 (.lf 287 [(0, 0x198b10749f7736196477350e9b00000155), (160, 0x7500020a07734d415773653ea000002c4), (192, 0x680c050be77349319773694e6000004f5), (224, 0x6bdd08b00773452257736d5da000007c8), (256, 0x70b50d0fc77341139773716c600000b3e), (352, 0x6b2404b9f77334eb07737d94f0000196c), (448, 0x69f60880377328c8b77389b7400002d4c), (480, 0x60b0097a077324bee7738dc1100003530), (512, 0x685f0bfe777320b5d77391ca200003db5), (544, 0x5de00787e7731cadb77395d24000046db), (576, 0x601d0528777318a6877399d97000050a2), (608, 0x662e09fad77314a047739ddfb00005b0b), (736, 0x5d2004c477730491c773adee300008af4), (768, 0x62bf0cc4f7730090f773b1ef00000987f), (832, 0x60ee0b0ed772f892f773b9ed00000b576), (896, 0x5e91099da772f09a0773c1e5f0000d4eb), (928, 0x5c2906320772ec9f9773c5e060000e595), (960, 0x5c400c252772e8a68773c9d970000f6dd), (992, 0x5d250763e772e4aee773cdd11000108c4)]) (.nd 289 (.lf 288 [(0, 0x5d000cd4f772e0b8b773d1c7400011b4a), (64, 0x5bc006f35772d8d0e773d9af100014231), (96, 0x5ba0073cc772d4df5773dda0a00015691), (128, 0x59480af1b772d0ef6773e190800016b8f), (160, 0x59ff0ba8c772cd012773e57ed0001812a), (192, 0x535f06a4b772c9149773e96b600019763), (256, 0x58b60a6cc772c140a773f13f50001c5aa), (288, 0x55640b20c772bd595773f526a0001ddb8), (384, 0x55ff0beaa772b1aeb77400d1400022988), (416, 0x51cf07640772adcef77404b0f00024405), (448, 0x507f08980772a9f14774088eb00025f1c), (480, 0x4f530e0ce772a61597740c6a600027acd), (512, 0x54000ad5a772a23c07741043f00029719), (544, 0x50be086617729e647774141b80002b3fe), (576, 0x502d080807729a8f177417f0e0002d17d), (608, 0x51300adf877296bbe7741bc410002ef95), (640, 0x50d609cad77292eae7741f95100030e46), (672, 0x51110afa47728f1c27742363d00032d90), (736, 0x4f290984f772878587742afa700036deb), (768, 0x4fc00c57377283bdc7742ec2300038efc), (832, 0x4e7b0a7207727c356774364a90003d2e2), (864, 0x49b607b307727874e7743a0b10003f5b7), (928, 0x4b0f0c68e77270fb67744184900043d21), (960, 0x4d31083627726d427774453d8000461b6), (992, 0x49bf05e19772698c277448f3d000486e0)]) (.lf 289 [(0, 0x4bdb0d7fc77265d887744ca770004ac9f), (32, 0x4a730d16f77262278774505870004d2f1), (64, 0x4aa808d4f7725e7937745406c0004f9d6), (96, 0x459f08b307725acdb77457b240005214f), (128, 0x484a0777b7725724e7745b5b00005495a), (160, 0x490208966772537ef7745f010000571f7), (192, 0x493f09e6c7724fdbe77462a4100059b26), (224, 0x45a00c7857724c3ba774664450005c4e6), (256, 0x47ff0d60e772489e677469e190005ef37), (288, 0x45760bac2772450407746d7bf00061a18), (320, 0x4578041c7772416ca774711340006458a), (416, 0x44fb0d2ef77236b8d7747bc720006cb38), (448, 0x446f09c18772332dc7747f5230006f8e4), (480, 0x436f05c227722fa5d77482da20007271d), (512, 0x443e09e4b7722c211774865ed000755e4), (576, 0x42ed08557772252157748d5ea0007b516), (608, 0x42df0919177221a6577490d990007e580), (640, 0x4227077d07721e2eb7749451400081676), (672, 0x402007c3e7721aba677497c59000847f5), (704, 0x411b0c46b772174977749b368000879ff), (736, 0x40df09c2077213dbf7749ea400008ac92), (768, 0x40d60de8b7721071f774a20e00008dfae), (800, 0x3ea10cb207720d0b5774a574a00091353), (832, 0x3f370a23577209a84774a8d7b0009477f), (864, 0x3ea90a18d7720648c774ac37300097c32), (896, 0x253f069f377202ecd774af9320009b16c), (928, 0x3d3907a37771ff948774b2eb70009e72c), (960, 0x3b6507c7f771fc3fd774b6402000a1d71)])))) (.nd 293 (.nd 291 (.lf 290 [(0, 0x3cbd0c4da771f5a18774bcde7000a8b8a), (96, 0x3bbe0c166771ebd01774c6afe000b348b), (128, 0x243f08115771e891e774c9ee1000b6de5), (160, 0x3abc0601b771e5578774cd287000ba7c1), (256, 0x39ef0d93d771dbbff774d6c00000c5857), (288, 0x366006860771d8955774d9eaa000c9432), (320, 0x34bb07e8f771d56eb774dd114000cd08c), (352, 0x377008360771d24c2774e033d000d0d64), (416, 0x376007af0771cc133774e66cc000d8889), (448, 0x33f209b6e771c8fce774e9831000dc6d6), (480, 0x31f906ec8771c5eab774ec954000e059e), (512, 0x36400ade0771c2dcc774efa33000e44e0), (576, 0x32ff09421771bccd7774f5b28000ec4d2), (608, 0x33f90da9d771b9cc3774f8b3c000f0580), (640, 0x307705a45771b6cf3774fbb0c000f46a6), (672, 0x339709b4c771b3d69774fea96000f8843), (704, 0x33b20a118771b0e24775019db000fca57), (736, 0x1c20057fd771adf25775048da00100ce0), (768, 0x32910e8de771ab06c7750779300104fdf), (864, 0x31810c9e0771a25ed7751021200111b93), (896, 0x313b093127719f85377512fac0011605f), (928, 0x30cf0c58c7719cb0177515cfe0011a59d), (960, 0x2e800c96b77199df877518a070011eb4c), (992, 0x2fe008dce771971387751b6c60012316b)]) (.nd 292 (.lf 291 [(0, 0x2f860ad18771944c37751e33c001277f9), (64, 0x2e180d0df7718ecb677523b4900130662), (128, 0x2dc00c2bd771895d67752922900139680), (192, 0x252703de5771840257752e7da0014284e), (224, 0x2c54069e0771815bf7753123f001471d4), (256, 0x2c10430007717eba777533c580014bbc5), (288, 0x2b600a2607717c1db775366230015061e), (352, 0x28e0061a777176f2f7753b8d000159c08), (384, 0x28c00a8757717464e7753e1b10015e797), (448, 0x2880081507716f5797754328500167fe6), (512, 0x28400d4bc7716a5e47754821b001719c6), (544, 0x26e50d1ee77167e917754a96e0017674b), (576, 0x25c20de7d7716578f7754d0700017b531), (608, 0x24da05afa771630df7754f72000180379), (640, 0x25df03cb577160a8077551d7f00185220), (672, 0x22af058597715e4727755438d0018a128), (704, 0x21a806aa07715beb7775569480018f08e), (736, 0x23f60775f7715994e77558eb100194052), (768, 0x221b0d5bc771574387755b3c700199073), (992, 0x17310a97c771479ca7756ae34001bcb46)]) (.lf 292 [(0, 0x1a400a41d771457577756d0a8001c1e33), (256, 0xa400908077134fe57757d81a001ec15e), (512, 0x9400881c77125e797758c98600217844), (768, 0x840076807711839d7759a46200244125)]))) (.nd 294 (.lf 293 [(512, 0x54004d05770f7ef3775ba90c002cf5b0), (768, 0x44006d27770f0297775c2568002ff459)]) (.nd 311 (.lf 294 [(768, 0x4006853770e06c3775d213c003c336e), (832, 0x77d6770e042d775d23d2003cf938)]) (.lf 311 [(0, 0x3193b00000775c4b3f770edcc0003dee92)]))))))
theorem PTT_4_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_4 = true := by decide +kernel
noncomputable def PTT_5 : PTrD := (.nd 343 (.nd 320 (.nd 317 (.nd 315 (.lf 314 [(0, 0x189350230c7755a6b27715814d001bca74), (256, 0x2034d0261f775491fd77169602001953ae), (512, 0x1c5ff02a5e77536b1d7717bce20016f33e), (768, 0x2af0002ddf775232cf7718f5300014aa86)]) (.nd 316 (.lf 315 [(0, 0x28259030407750e9d5771a3e2a00127adc), (256, 0x10d4003371774f90fe771b970100106586), (320, 0x2f0003530774f3867771bef98000fe472), (512, 0x29816036d7774e2922771cfedd000e6bb9), (768, 0x1fec003afe774cb320771e74df000c8e97)]) (.lf 316 [(0, 0x26c9703d38774b2fe1771ff81e000acf34), (256, 0x2db40041a57749a054772187ab00092e8e), (512, 0x25dc0044f5774805717723228e0007ad92), (736, 0xa11d04747774695637724929c0006775a), (768, 0x3f1c704840774660337724c7cc00064d19)]))) (.nd 318 (.lf 317 [(0, 0x188c004ad57744b19e7726766100050de8), (64, 0x7bbf04cc8774444a27726e35c0004c365), (256, 0x17c3504fbf7742fabb77282d440003f0b0), (512, 0x1921c053a477413c957729eb6a0002f60c), (576, 0x476d054f77740cc09772a5bf60002bcda), (768, 0x884b5056b7773f783d772bafc200021e82)]) (.nd 319 (.lf 318 [(0, 0x12fd405c19773daec6772d793900016a84), (32, 0x521005ce0773d7549772db2b600015689), (64, 0x1173605d00773d3bbc772dec430001431e), (96, 0x11f8005e13773d0220772e25df00013042), (128, 0x9b6b05d40773cc876772e5f8900011df7), (160, 0x175bd05d60773c8ebe772e994100010c3c), (192, 0x9be405d80773c54f8772ed3070000fb11), (224, 0x8fb505fbb773c1b26772f0cd90000ea77), (256, 0x2a91206092773be147772f46b80000da6e), (352, 0x43c0062cc773b3366772ff4990000adb6), (512, 0x34d89064c0773a10d87731172700006e85), (640, 0x1c9ff0674f773927de7732002100004631), (672, 0x6c60066da7738ed9177323a6e00003d88), (736, 0x5a8006964773878eb7732af1400002dec), (768, 0x3409906c8077383e927732e96d000026f8), (864, 0x8edf06efe77378f78773398870000158a), (896, 0x628006f7f773755167733d2e9000010de), (992, 0x1342906fdf7736a5f07734820f00000646)]) (.lf 319 [(0, 0x15a94072bf77366b8f7734bc70000003e3), (96, 0xb25007ad87735bc7677356b8900000023), (160, 0x735f0709f773547ca7735e0350000007c), (288, 0x72b90857077345ea87736c95700000804), (320, 0x72bf0b6227734246e7737039100000b52), (352, 0x729f0ff207733ea3b77373dc400000f32), (384, 0x6763094d07733b010773777ef000013a3), (416, 0x606007bb0773375ec7737b213000018a5), (448, 0x60400f59e77333bd17737ec2e00001e39), (512, 0x6cf40bc237732c7b87738604700002b15), (544, 0x66df0f31077328dba77389a450000325c), (608, 0x640b08220773219df77390e200000429d), (704, 0x67ff0fbf177316c717739bb8e00005f3b), (768, 0x659609c9d7730f914773a2eeb00007522), (864, 0x601208a4a77304c78773adb8700009a33), (960, 0x61ec05661772fa06d773b87920000c451), (992, 0x60f00ab55772f6737773bc0c80000d37a)])))) (.nd 323 (.nd 321 (.lf 320 [(0, 0x60340ce3f772f2e13773bf9ec0000e331), (64, 0x5dc009a40772ebc05773c6bfa0001044c), (96, 0x5da007830772e831b773ca4e4000115af), (128, 0x5da00f570772e4a46773cddb9000127a0), (160, 0x5ddf0b640772e1186773d167900013a20), (192, 0x5d40089e0772dd8db773d4f2400014d2d), (256, 0x5bee0ca92772d67c8773dc037000174ef), (448, 0x565d07dfa772c16ca773f11350001f96a), (480, 0x53b10b9af772bdef9773f490600021169), (512, 0x577f0be5c772ba742773f80bd000229f3), (544, 0x54f5070d6772b6fa6773fb85900024309), (576, 0x5421047c0772b3826773fefd900025ca9), (608, 0x548f0775b772b00c37740273c000276d4), (640, 0x54e007e38772ac97c77405e8300029189), (672, 0x52fd0ad94772a9253774095ac0002acc8), (704, 0x53bf0be0d772a5b477740ccb80002c891), (736, 0x52d40f60c772a245a774103a50002e4e4), (768, 0x52ef0f26d7729ed8c77413a73000301bf), (800, 0x52cf038107729b6dd7741712200031f24), (864, 0x503e098f9772949df7741de2000035b86), (928, 0x4ed60832e7728dd6577424a9a00039a08), (960, 0x4dfb09b0c7728a75a774280a50003ba14)]) (.nd 322 (.lf 321 [(0, 0x4eff0b9a077283bac7742ec520003fbc1), (32, 0x4dbc06b3d7728060b774321f400041d61), (64, 0x4b6a0bfc17727d08d7743577200043f87), (96, 0x4d6b0a69a77279b3377438ccc00046232), (160, 0x4c6a0b66c772730ef7743f7100004a918), (192, 0x47c50922d7726fc0577442bfa0004cd52), (224, 0x49ac085917726c742774460bd0004f210), (256, 0x4b000d2ed772692a67744955900051751), (288, 0x4987092f677265e317744c9ce00053d16), (320, 0x4a420a8af772629e47744fe1b0005635e), (352, 0x488a07cf07725f5bf7745324000058a29), (480, 0x467707bc1772526c77746013700062a64), (512, 0x47520d3677724f3737746348c000653b6), (544, 0x46370bbc07724c04a774667b500067d87), (576, 0x466c0873b77248d4d77469ab20006a7d8), (608, 0x439f0b0d677245a7b7746cd840006d2a8), (640, 0x449f08575772427d6774700290006fdf7), (672, 0x431f07b5e7723f55f774732a0000729c5), (768, 0x431f0db0f77235f0a7747c8f50007b01f), (800, 0x421f05f3077232d4b7747fab40007dde2), (832, 0x42bf082d67722fbbb77482c4400080c21), (864, 0x4210096a07722ca5b77485da400083adb), (896, 0x41b706d407722992c77488ed300086a11), (928, 0x40d50959d7722682d7748bfd2000899c1), (960, 0x3d1e088097722375f7748f0a00008c9ec)]) (.lf 322 [(0, 0x3fba0fe2e7721d658774951a700092bae), (128, 0x3e4007f73772116ad774a11520009f4d7), (160, 0x3b77078dc7720e743774a40bb000a284c), (192, 0x3ad30884e7720b80f774a6ff0000a5c37), (256, 0x3c7c0d8af77205a45774acdba000ac56d), (352, 0x3a720b54d771fcf2c774b58d2000b66a9), (384, 0x3a9a07db9771fa13d774b86c2000b9d4f), (416, 0x3a200a9fe771f7385774bb47a000bd467), (480, 0x37ff047e0771f18bd774c0f41000c43ec), (512, 0x39360c54d771eebaf774c3c50000c7c59), (576, 0x32400acad771e923e774c95c1000cee83), (608, 0x36540c5ad771e65dd774cc222000d283e), (704, 0x363c07386771de219774d45e5000dd808), (768, 0x35fb0cacc771d8b6c774d9c93000e4f5a), (800, 0x35520a4d6771d6070774dc78f000e8ba6), (832, 0x2c000a37a771d35b0774df24f000ec85c), (896, 0x3277072e7771ce0ea774e4715000f4308), (960, 0x32a306ed1771c8d1c774e9ae3000fbf59), (992, 0x32c00722f771c6393774ec46c000ffe1e)]))) (.nd 325 (.nd 324 (.lf 323 [(0, 0x32750fb6d771c3a49774eedb600103d4b), (32, 0x30600a36f771c113f774f16c000107cdf), (64, 0x2e800ad1f771be875774f3f8a0010bcd9), (256, 0x2f000eace771af90a77502ef5001244f5), (288, 0x1fe103941771ad20a775055f5001287a9), (352, 0x2b7506c7d771a84d27750a32d00130e34), (384, 0x2b4007840771a5e9b7750c9640013520a), (512, 0x2b000ebce7719c86977515f9600146513), (672, 0x242a044f6771912c27752153d0015c4fa), (768, 0x27ab0b9ac7718a91477527eeb00169c51), (800, 0x233304d20771886697752a1960016e4c8), (832, 0x208a0e32c771864067752c3f900172d95), (928, 0x1d3d057907717fe927753296d001809fb)]) (.lf 324 [(0, 0x20800c27d77179bb177538c4e0018e950), (32, 0x1f1f0447077177b4f7753acb000193465), (192, 0x1b7c04fc07716ddc977544a36001ab07a), (256, 0x14ea0e0af7716a0d877548727001b4aa2), (512, 0x12c105f7b7715b91877556ee7001dbecf)])) (.nd 327 (.lf 325 [(0, 0x9000763e771424de775703210022d9a3), (512, 0x700059207712e2837758457c00282d45)]) (.lf 327 [(0, 0x40095ee77111dd2775a0a2d0038f92a), (64, 0xa13e77111c0c775a0bf30039af7e)]))))) (.nd 351 (.nd 348 (.nd 346 (.lf 343 [(512, 0x31f29000007758f8a877122f57003b5939)]) (.nd 347 (.lf 346 [(512, 0x205850221877536f277717b8d8001bef56), (768, 0x2401f02593775284a47718a35b0019a346)]) (.lf 347 [(0, 0x1c6910297477518a8677199d7900176a25), (224, 0x5338902ae07750a35d771a84a1001588a1), (256, 0x384db02ca37750816f771aa69000154525), (512, 0x55f3503022774f6a09771bbdf50013356b), (768, 0x1a7010331c774e4509771ce2f600113c0e)]))) (.nd 349 (.lf 348 [(0, 0x59bff03399774d1327771e14d8000f5a17), (96, 0x33ff03790774c9d48771e8ab7000eab96), (256, 0x30e5e03998774bd526771f52d9000d9080), (512, 0x1fe1e03a8e774a8bcd77209c32000be035), (768, 0x1865f03f50774937ec7721f013000a4a0e)]) (.nd 350 (.lf 349 [(0, 0x2c0af043807747da5577234daa0008ced8), (256, 0x1f713046c0774673e37724b41c00076f4c), (512, 0x34acb04a10774505737726228c00062c12), (608, 0x169600255677447a287726add70005ba49), (768, 0x3690d04dc977438fe777279817000505c1)]) (.lf 350 [(0, 0x21c2a0519777421425772913da0003fcdf), (192, 0x2d429053a07740f3cc772a3433000349cc), (256, 0x3391d054c177409315772a94ea000311df), (448, 0x802e057a0773f6f5b772bb8a400027576), (480, 0x340b0569e773f3e86772be97900025d0e), (512, 0x2705905898773f0da2772c1a5d00024521), (576, 0xe270059f6773eabb1772c7c4e000216b6), (672, 0x70f005a2f773e1869772d0f960001d4ac), (768, 0x3659705bd5773d84b9772da346000196f5), (864, 0x855d05f20773cf0ad772e375200015d92), (896, 0xb91905f40773cbf42772e68bd00014b68), (928, 0x8ba005f60773c8dcf772e9a30000139ba), (960, 0xae4305f80773c5c53772ecbac00012887), (992, 0x83de05fa0773c2ad1772efd2e000117d0)])))) (.nd 354 (.nd 352 (.lf 351 [(0, 0x375db060fb773bf947772f2eb800010795), (128, 0x3bc00636f773b32e6772ff5190000cb80), (224, 0xe60063cf773a9dec77308a130000a387), (256, 0x29e7a066a9773a6c3d7730bbc20000972c), (512, 0x3e5b406bbf7738de8977324976000045d0), (608, 0x7b6006cc77738496a7732de9500002f50), (640, 0x145ff06ca7773817ba77331045000028c9), (672, 0x120e006cc77737e60c773341f3000022be), (704, 0x41fe006fdc7737b4627733739d00001d2e), (736, 0x1fe0071a0773782bb7733a5440000181c), (768, 0x7fcb507220773751197733d6e600001385), (928, 0x4639074df773659417734cebe000003d7), (992, 0x96c40751f7735f64c773531b3000000f4)]) (.nd 353 (.lf 352 [(0, 0x1269307d407735c4dd773563220000003c), (128, 0x715f0b51c7734ff7c773628830000022f), (192, 0x721007bcc77349d0777368af80000060b), (224, 0x64fe0b49677346bdd7736bc22000008b2), (256, 0x6f6310a6d77343abf7736ed4000000bd4), (320, 0x6cff08bde7733d8a877374f5700001388), (384, 0x689f06a22773376c67737b13900001d25), (448, 0x63df08f8c7733151b773812e4000028ac), (480, 0x5d60085e17732e45b773843a400002f26), (512, 0x65f40f6667732b3ab773874540000361a), (576, 0x61ef05eb97732527b7738d5840000456e), (608, 0x600e077ae773221fc7739060300004dcf), (640, 0x5fd609fb77731f18d77393672000056a8), (672, 0x631f07b7c7731c131773966ce00005ffb), (704, 0x5fce077a9773190e677399719000069c6), (736, 0x60a50a0cc773160ae7739c7510000740a), (768, 0x60db0cb6e773130897739f77600007ec7), (800, 0x5fe50b6d677310077773a2788000089fc), (832, 0x5c40085a17730d078773a5787000095a9), (864, 0x5c200819d7730a08e773a87700000a1cd), (896, 0x5c700688c773070b9773ab7460000ae6a), (928, 0x5d25075d7773040f9773ae7060000bb7e), (960, 0x5bc0084267730114e773b16b10000c909)]) (.lf 353 [(0, 0x5b800a734772fb23c773b75c30000e584), (96, 0x5860052dc772f244c773c03b3000113b6), (160, 0x50d60b856772ec624773c61db000134d0), (192, 0x55e512080772e9736773c90c90001460d), (256, 0x56dd09137772e39a6773cee59000169e7), (288, 0x55850b8d6772e0b05773d1cfa00017c84), (320, 0x550408d9e772ddc7f773d4b8000018f94), (384, 0x5150060e1772d7fc5773da83a0001b712), (416, 0x50f803d00772d5191773dd66e0001cb7e), (480, 0x50e009ac0772cf580773e327f0001f5b1), (512, 0x515a0b9b6772cc7a4773e605b00020b76), (640, 0x4e5d06480772c115e773f16a100026703), (672, 0x4e80066c8772be41a773f43e500027f02), (704, 0x4dc0060a1772bb6f5773f710a00029772), (736, 0x4e670ba96772b89f1773f9e0e0002b053), (768, 0x4df60b070772b5d0d773fcaf20002c9a4), (864, 0x4afe08eec772ad72a774050d500031837), (896, 0x4bb90904d772aaacd77407d3200033347), (928, 0x31e008e7c772a7e927740a96d00034ec5), (992, 0x4670074ab772a2687774101780003870d)]))) (.nd 356 (.nd 355 (.lf 354 [(0, 0x49d70d84b7729fab677412d490003a3d5), (32, 0x468206be07729cf0a774158f50003c10b), (64, 0x493308b9b7729a3827741847c0003deae), (96, 0x466107d32772978207741afdf0003fcbd), (128, 0x462208e2077294ce37741db1c00041b39), (160, 0x46d0094cf772921cb7742063400043a21), (224, 0x3f120d8807728cc0f77425bf000047932), (256, 0x45841126d7728a16c774286930004995b), (320, 0x44b9077a777284c9a7742db650004daed), (352, 0x30a0080f37728226e774305910004fc54), (384, 0x41610ccfe7727f86977432f9600051e24), (448, 0x3800047c07727a4dc77438323000562ff), (512, 0x41c00d6db772751f57743d60a0005a97b), (576, 0x3d6f07beb7726ffb7774428480005f193), (736, 0x3ac003a5e772635147744f2eb0006acc7), (768, 0x3ec70973777260d1277451aed0006d367)]) (.lf 355 [(0, 0x3b6c0ce7d7724d37e7746548100081644), (32, 0x3914081d57724ad2077467adf00084056), (256, 0x37800b6bb7723a5ea774782150009712b), (352, 0x3580099977723380e7747eff10009f942), (512, 0x34800b770772285017748a2fd000ae323), (704, 0x2e0b0a7407721b505774972fa000c0726), (768, 0x31470bbdf772171667749b699000c6b2a)])) (.nd 357 (.lf 356 [(0, 0x2d6b0dbcc77206bb2774abc4c000e082e), (256, 0x29a009fbd771f7477774bb388000fb915), (512, 0x264009391771e8c3b774c9bc400117cb8), (768, 0x1ef209561771db37e774d7481001351e5)]) (.lf 357 [(0, 0x138a053a7771ceab3774e3d4c00153762)]))))))
theorem PTT_5_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_5 = true := by decide +kernel
noncomputable def PTT_6 : PTrD := (.nd 389 (.nd 382 (.nd 378 (.nd 375 (.lf 359 [(704, 0xb5fd7718c049775267b6002c3d2f)]) (.nd 376 (.lf 375 [(896, 0x3ccf90000077514b6e7719dc91002d5bba)]) (.lf 376 [(0, 0x2e0cf000807751475f7719e0a0002c46a1)]))) (.nd 380 (.nd 379 (.lf 378 [(768, 0xc4ff0160a774d0fe4771e181b0015c4d2)]) (.lf 379 [(0, 0xf3c0023f0774c5709771ed0f60013f647), (256, 0x1685d0265a774b9179771f9686001236ad), (512, 0x2879f02b9d774abfb777206848001086fd), (960, 0x1f83502e19774934ee7721f311000dbc9c)])) (.nd 381 (.lf 380 [(0, 0x29f88030727748f9cb77222e34000d5b0b), (256, 0x1f267035a6774806c977232136000be084), (768, 0x3034603b58774603bc7725244300092656)]) (.lf 381 [(0, 0x1b61703de17744f4fb772633040007e821), (256, 0x1b6db041c07743de4d772749b20006bf64), (512, 0x1694c045ce7742c0627728679d0005acb5), (768, 0x198480492777419bef77298c100004b0a0)])))) (.nd 385 (.nd 383 (.lf 382 [(0, 0x30d0304ccc774071ab772ab6540003cb9f), (256, 0x3e22005040773f4252772be5ad0002fe1f), (448, 0x69e005236773e5beb772ccc14000273a5), (512, 0x20e3905283773e0ea0772d195f0002487f), (608, 0x15afd0554c773d9a46772d8db900020a9b), (768, 0x2194d0578d773cd756772e50a90001ab0e), (960, 0x23c005b40773bebf6772f3c09000144ff)]) (.nd 384 (.lf 383 [(0, 0x26f4f05bec773b9d34772f8acb0001260c), (96, 0x449005da0773b26d37730012c0000fa83), (128, 0x52e805dc0773aff4e773028b10000ecc5), (160, 0x6a7905de0773ad7c37730503c0000df6a), (192, 0xf07b05e00773ab031773077ce0000d272), (224, 0x9cf005f1d773a889977309f660000c5dd), (256, 0x24b7f060c0773a60fc7730c7030000b9ab), (384, 0x12200061d87739c254773165ab00008cc3), (448, 0x19c4006390773972e87731b517000078a2), (512, 0x42c1f065be773923717732048e0000660e), (768, 0x1c23b069967737e556773342a900002b46), (896, 0x1448a06d447737464f7733e1b000001733)]) (.lf 384 [(0, 0x1e7f5071367736a76d7734809100000957), (64, 0x5a870743e773658127734cfed000004bc), (128, 0x959407448773608c977351f36000001ae), (256, 0x78c009de077356a7a7735bd8500000036), (384, 0x5820063bf7734cc9977365b66000004eb), (416, 0x5e200b3a67734a534773682cb0000070f), (448, 0x691d04cf877347dd87736aa2700000995), (480, 0x69e203f78773456867736d17900000c7e), (512, 0x6a880818077342f3c7736f8c300000fc8), (576, 0x5d80085a07733e0c87737473700001784), (640, 0x65e609b407733927d77379582000020c8), (672, 0x63be046b877336b697737bc96000025fd), (768, 0x64f80d4507732f6737738318c000037e4), (896, 0x5d010966b77325b367738ccc900005514), (928, 0x5f4908c3e773234897738f37600005d53), (992, 0x5be009fdf7731e75c773940a300006ef1)]))) (.nd 387 (.nd 386 (.lf 385 [(0, 0x5bc00da9b7731c0dc7739672300007851), (32, 0x5ba00656077319a6c77398d9300008211), (64, 0x5b8005b7d7731740c7739b3f300008c31), (128, 0x53b408b577731277e773a00810000a190), (160, 0x5b200661677310150773a26af0000accf), (192, 0x5b00067007730db34773a4ccb0000b86d), (256, 0x59db0bbb277308f31773a98ce0000d0c7), (352, 0x55fc0397277301dba773b0a450000f815), (512, 0x54e00a78c772f622a773bc5d5000140f2), (640, 0x4b7a0b5fe772ecd9d773c5a62000181cc), (768, 0x50e10da4c772e3a7b773ced840001c86d), (960, 0x438707ec4772d60a4773dc75b00023d12), (992, 0x4cf006fdf772d3caf773deb50000251bf)]) (.lf 386 [(0, 0x4c950e08b772d18d5773e0f2a000266c7), (32, 0x35a00569f772cf515773e32ea00027c27), (96, 0x47e905eec772cade8773e7a170002a7f4), (256, 0x48ce0cfdf772bfde2773f2a1d00031b7f), (384, 0x44c20764d772b7321773fb4de00037e14), (512, 0x44d70f160772aea4c77403db30003e60a), (736, 0x2fe00a6007729ffb17741284e0004a8b2), (768, 0x40f0106b07729deb37741494c0004c5ce), (864, 0x2fa208e9f77297c8a7741ab7500051f0f)])) (.nd 388 (.lf 387 [(0, 0x3dff0d9b67728dbb677424c490005ba25), (160, 0x2b30282377283e7a7742e98500065cff), (224, 0x395005b5f7728009f774327600006a045), (256, 0x39cc0bfce7727e1eb774346130006c25c), (480, 0x36500250077270f58774418a70007b946), (512, 0x35ec0e6f07726f1e47744361b0007ddb7), (768, 0x32c00f66077260c2c77451bd300090b6c)]) (.lf 388 [(0, 0x2fe00ddb6772531457745f6ba000a4aa8), (256, 0x2b300b767772461ae7746c651000b9a8d), (512, 0x28c00c3cf77239ddc77478a23000cfa36), (640, 0x246003c8f772340807747e77f000dafa9), (768, 0x24d70fa607722e63d774841c1000e68b1)]))))) (.nd 414 (.nd 410 (.nd 390 (.lf 389 [(0, 0x14c006d4677223b387748ecc7000fe508), (256, 0x11bc093fb77219d2a77498ad500116e3a)]) (.nd 407 (.lf 390 [(256, 0x8cf05626771facd9774b7b260017feb0)]) (.lf 407 [(960, 0x2229a00000774befe7771f381800240fca)]))) (.nd 412 (.nd 411 (.lf 410 [(256, 0x121920009d77499e15772189ea00147be4)]) (.lf 411 [(256, 0x25a300278077475c9f7723cb60000e8e66), (512, 0x1bbfb029d07746b1cf77247630000d3155), (768, 0x1e1b002dac7745fd4177252abe000be1fe)])) (.nd 413 (.lf 412 [(256, 0x28ee603406774478c97726af3600096f70), (416, 0xd9570281b7743f86577272f9a0008b863), (512, 0x58d1e035687743a9db77277e2400084d98), (608, 0x241d2012a077435a387727cdc70007e51e), (768, 0x2b677039d37742d324772854db00073c3a)]) (.lf 413 [(0, 0x2c1e703d607741f530772932cf00063beb), (256, 0x29faf040697741108a772a177500054d37), (320, 0x480042e07740d666772a519900051459), (512, 0x13247042eb774025c5772b023a0004709e), (704, 0x2b07f04728773f7206772bb5f90003d754), (768, 0x22dff0471a773f3575772bf28a0003a695)])))) (.nd 417 (.nd 415 (.lf 414 [(0, 0x2cb1e04a53773e4031772ce7ce0002ef84), (256, 0x2d35804fd0773d4693772de16b00024bca), (512, 0x28431053ca773c4939772edec60001bbb6), (768, 0x2175f055d9773b48c0772fdf3f00013f8e)]) (.nd 416 (.lf 415 [(0, 0x309c305a86773a45c87730e2370000d789), (32, 0x774f05ca0773a2544773102bb0000cbf5), (64, 0x9aaf05cc0773a04b9773123460000c0b2), (96, 0x744205ce07739e427773143d80000b5c1), (128, 0x832005d007739c38f773164700000ab22), (160, 0x5f6305f347739a2f07731850f0000a0d4), (192, 0xadbf05d407739824c7731a5b3000096d7), (224, 0xb28005d60773961a27731c65d00008d2c), (256, 0x343c005eab773940f27731e70d000083d3), (480, 0x10ee80644077385bae7732cc5100004b55), (512, 0x1d2b00653f77383ae07732ed1f0000448b), (608, 0xad46067ed7737d86977334f9600003219), (768, 0x1954d06ad0773734347733f3cb000019c4), (960, 0x1fc0070fd77366f2f7734b8d000000727)]) (.lf 416 [(0, 0x20bdb0739c77362d907734fa6f00000383), (480, 0x5de0052c0773443627736e49d000010f9), (512, 0x6ae50b1ed773422e37737051c0000146b), (640, 0x5d40024537733a138773786c70000255f), (672, 0x61a10ba5e773380e27737a71c00002a66), (704, 0x5d0009ac0773360967737c76900002fbe), (768, 0x63320af837733201b773807e400003b61), (864, 0x5c60051607732bfae7738685100004f30), (960, 0x5c0005bed77325fa57738c85a000065d0)]))) (.nd 419 (.nd 418 (.lf 417 [(0, 0x5bc00979377321fda7739082500007676), (256, 0x573408300773122bc773a05430000c571), (352, 0x536005ccd7730c4bf773a63400000e824), (384, 0x5667051907730a58a773a82750000f451), (480, 0x4e82089fb7730484d773adfb200011aab), (512, 0x52d80f39e7730295a773afea50001280f), (544, 0x1d7d09ea577300a79773b1d86000135c1), (768, 0x4fec0757f772f344c773bf3b300019dfe)]) (.lf 418 [(0, 0x4b0109d85772e4425773ce3da000226e3), (256, 0x47dd0d6a9772d5976773dce890002c254), (384, 0x461006c20772ce657773e41a8000316de), (512, 0x44d206a80772c74ca773eb33500036fe0), (704, 0x3ef506f5f772bcd8f773f5a700003fd9f), (768, 0x3fe80c020772b96ac773f915300042f09)])) (.nd 420 (.lf 419 [(0, 0x3cb20fb70772abf9e774068610004ff46), (256, 0x39cd0b1e77729f021774137de0005e006), (640, 0x32830a4057728c81e77425fe100074ec1), (768, 0x324c0bae8772869bc7742be430007d092), (928, 0x300002fe07727f6e877433117000877f3)]) (.lf 420 [(0, 0x2e73125b07727b3ba774374450008df0a), (256, 0x291f0d6f277270711774420ee0009fb5e), (288, 0x1f82089a87726f229774435d6000a1fd9), (512, 0x26610dece772664267744c3d9000b24ce)]))))))
theorem PTT_6_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_6 = true := by decide +kernel
noncomputable def PTT_7 : PTrD := (.nd 451 (.nd 445 (.nd 441 (.nd 439 (.lf 423 [(896, 0x10d1e772214f677491309001e2b4b)]) (.lf 439 [(960, 0x3366e00000774883be7722a441001e8e9f)])) (.nd 443 (.lf 441 [(256, 0x321c8000097747dae477234d1b0016e260), (512, 0x323ac000607747983977238fc50015775f)]) (.nd 444 (.lf 443 [(0, 0xf237021fa774530aa7725f755000d87b2), (256, 0x19bab027717744a8ab77267f54000c54b5), (768, 0x2821502e2077437efc7727a903000a104d)]) (.lf 444 [(0, 0x19c3502f6a7742de0e772849f10009002e), (256, 0x2a36002f2d774235997728f2660007fced), (512, 0x11afe034057741860a7729a1f50007071d), (768, 0x1cae003b2f7740cfd1772a582e00061f48)])))) (.nd 448 (.nd 446 (.lf 445 [(0, 0x2e9e70386077401362772b149d000545ee), (256, 0x14a1b03883773f5135772bd6ca00047b87), (512, 0x173ab0455e773e89c4772c9e3b0003c081), (768, 0x4432804835773dbd8f772d6a7000031540)]) (.nd 447 (.lf 446 [(0, 0x202a003b83773ced14772e3aeb00027a1f), (256, 0x8841804f2a773c18d8772f0f270001ef6e), (512, 0x1060005014773b415e772fe6a100017573), (768, 0x1d25d05763773a672e7730c0d100010c69)]) (.lf 447 [(0, 0x28dd405c2477398acf77319d300000b482), (32, 0x15cbf05ca077396f227731b8dd0000aabc), (64, 0x5cf405cc0773953707731d48f0000a13a), (96, 0x116be05ce0773937b77731f048000097fe), (128, 0x9b0805d0077391bf877320c0700008f08), (160, 0xec6c05d2077390034773227cb00008657), (192, 0x2a6705d407738e46b7732439400007deb), (224, 0x48be05d607738c89d77325f62000075c5), (256, 0x1ff0c05d807738acca77327b3500006de4), (320, 0xd2fc05b1b773875177732b2e800005ef3), (448, 0xdd83064ab773805847733227b00004456), (512, 0x308c8064307737cda877335a57000038aa), (768, 0x30aac067a07736edf477343a0b000014e5)]))) (.nd 449 (.lf 448 [(224, 0x731f0a2a077354ad77735dd28000000ef), (288, 0x6c000001077351324773614db000002e9), (480, 0x5de005dae77346c7d7736bb8200000f58), (512, 0x5dc00780b773450ca7736d7350000125e), (768, 0x5cc00d68b7733742b7737b3d40000343f), (896, 0x5c400a3c07733069c7738216300004ba2), (992, 0x5be0062767732b4d37738732c00005ff9)]) (.nd 450 (.lf 449 [(0, 0x5bc00975c773299a477388e5b00006749), (256, 0x5400097907731c1bb773966440000ab4c), (512, 0x4db20f5787730ecf3773a3b0c0001000f), (768, 0x46001256777301bce773b0c310001654e), (864, 0x43970caaa772fce69773b599600018f76)]) (.lf 450 [(0, 0x42f711f8b772f4ec9773bd9360001dabb), (256, 0x41f711d80772e8660773ca19f00025fff), (512, 0x440011851772dc30b773d64f40002f4ba), (768, 0x3ff71126d772d0541773e22be00039881)]))))) (.nd 477 (.nd 471 (.nd 452 (.lf 451 [(256, 0x388009460772b9c0a773f8bf500050b5c), (768, 0x2fbb0b147772a4e157740d9ea0006b492)]) (.nd 453 (.lf 452 [(768, 0x24d209cf377280fef77431810000a9794)]) (.lf 453 [(0, 0x12b004160772795dc77439223000baab9)]))) (.nd 475 (.lf 471 [(960, 0x44c68000007745dacf77254d30001a46f0)]) (.nd 476 (.lf 475 [(512, 0x26aef02950774211e17729161e00099b0d), (768, 0x226fb02c6577418e48772999b70008a650)]) (.lf 476 [(0, 0x23b8503145774103d0772a242f0007bc20), (256, 0x22deb02b40774072d2772ab52d0006dd03), (768, 0x1d39703698773f3eba772be945000541f7)])))) (.nd 480 (.nd 478 (.lf 477 [(256, 0x39f7f03d86773df511772d32ee0003d8c8), (512, 0x11d2404200773d492a772dded5000337e2), (768, 0x2952704720773c9919772e8ee50002a495)]) (.nd 479 (.lf 478 [(0, 0x20a6004b30773be550772f42af00021f2f), (256, 0x3032e04958773b2e3e772ff9c10001a7f7), (288, 0xf08b0502b773b1726773010d900019a12), (512, 0x1004d04f3f773a74567730b3a900013f28), (768, 0x1f51f055e07739b80b77316ff40000e4f9)]) (.lf 479 [(0, 0x1ceef05b6a7738f9d477322e2b00009993), (96, 0x3fa005ce07738b218773275e700008125), (128, 0xfdcd05d0077389a2477328ddb00007977), (192, 0x9bbb05d4077386a2d7732bdd200006ad0), (224, 0x9be005d607738522b7732d5d4000063d7), (256, 0x22d7f05d8077383a257732edda00005d1a), (512, 0x2f1ac064ef773779777733ae8800002fa4), (640, 0x1627603280773718e477340f1b00001e90), (768, 0x1f34605f807736b83f77346fc000001143)]))) (.nd 481 (.lf 480 [(0, 0x2e300069007735f6f677353109000001fb), (512, 0x5dc007c80773476087736b1f6000010a2), (640, 0x5d40009a07734167b7737118400001dac)]) (.nd 484 (.lf 481 [(768, 0x4d210538c7730d2a7773a55580001383d)]) (.lf 484 [(256, 0xe8004b80772ac4a7774063580007706c)]))))))
theorem PTT_7_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_7 = true := by decide +kernel
noncomputable def PTT : PTrD := (.nd 254 (.nd 133 (.nd 88 PTT_0 PTT_1) (.nd 193 PTT_2 PTT_3)) (.nd 359 (.nd 314 PTT_4 PTT_5) (.nd 421 PTT_6 PTT_7)))
theorem PTT_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT = true := (ptOkTD_nd (ptOkTD_nd (ptOkTD_nd PTT_0_ok PTT_1_ok) (ptOkTD_nd PTT_2_ok PTT_3_ok)) (ptOkTD_nd (ptOkTD_nd PTT_4_ok PTT_5_ok) (ptOkTD_nd PTT_6_ok PTT_7_ok)))
noncomputable def PT (x : ℕ) : ℕ := ptGetD PTT x
theorem ptS : ∀ x, PVI x (PT x) := ptTD_sound (n := 32) (csh := 4) lbS lbD hR (by decide) PTT PTT_ok

end AMW.Cert.PC9QB6MData
end

noncomputable section
namespace AMW.Cert
theorem PC9QB6M_G_rev (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : PC9QB6M.G x7 x6 x5 x4 x3 x2 x1 x0 = PC9QB6M.G x0 x1 x2 x3 x4 x5 x6 x7 := by
  unfold PC9QB6M.G; ring_nf

end AMW.Cert
end
