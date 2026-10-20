/-
R. Arun Chandru
arun.chandru@gmail.com
https://github.com/arun-chandru
https://x.com/arunchandru
https://researchgate.net/profile/R_Chandru

Copyright (c) 2026 R. Arun Chandru, for the circle-enclosure refinement.
SPDX-License-Identifier: Apache-2.0

Critical-line proportion: 167031227639218487/247987190000000000.

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
/-
Copyright (c) 2026 Samuel Lavery (github: samlavery). Licensed under Apache-2.0. Built on the author's
riemannzeta.fun submissions attempt-012/013/014/015/016 and on R. Arun Chandru's "master-of-puppets"
and "master-of-puppets2".
NOTICE: reuse or adaptation of this file must retain this copyright and attribution notice
(Apache-2.0 §4(c)) and must state any changes made (§4(b)).
The internal modules are by Samuel Lavery's agent team (bridge-port, am-cert, mvt-engine, window-scope).
-/
/-
Changes (Apache-2.0 §4(b)), by Samuel Lavery's agent team, 2026-10-10. This file is derived from
R. Arun Chandru's riemannzeta.fun submission "master-of-puppets" (2026-10-09, κ = 66812491/99194876,
Apache-2.0; Solution.lean sha256 f7ef331e72e8c34804e196a4cc0c6fdd69bb1c6947a51dfbf60b88a6343aad9d).
* Dead declarations removed: every declaration outside the dependency closure of the three scored
  theorems, computed from the compiled olean (attributed lemmas kept). Non-notice comments removed.
  Every copyright, license and attribution notice is retained verbatim.
* Certificate replaced by a re-optimised 9-point certificate (2026-10-19: the W9A2 window and weights, see the last bullet;
  earlier versions of this file used the R8 window with the t570 and lp9 weights).
* Counting chain generalised to n-point certificates (OpethN, same proofs with band width n − 1:
  error 4(n − 1)δ per point, boundary (n − 1)c, δ ≤ c/(8(n − 1)), C = 4(n − 1) + 2 + c + B, and a
  parametrised copy of Kristian Muri Knausgard's card_near_le); Arun's eight-point instances replaced.
* Window bound taken from R. Arun Chandru's "master-of-puppets2" (2026-10-11, κ = 167031227639218487/247987190000000000,
  Apache-2.0; Solution.lean sha256 a99b3172fe7885abb4119b1b00d124545e2689e1f441d571b1470439d6c3b03c): its circle-enclosure
  `cos_theta0_le` / `sin_theta0_ge`, giving H_W ≥ 672168410556873948/10¹⁸; changes 2026-10-11.
* Window bound: the order-20 cos θ₀ enclosure from R. Arun Chandru's master-of-puppets3 and the terminal HW floor at
  denominator 10²⁴ from Yuhang Shi's shi-anchor-variance-refinement-2026, both taken via R. Arun Chandru's master-of-puppets4
  (2026-10-12, Apache-2.0, sha256 ba9bf43cce4421a7580b03bfb90453b9f34381296943b38f3dc1f4c2a89a9de0), whose block notice is kept
  verbatim: HW_ge 672168410564118872522651/10²⁴; changes 2026-10-13.
* Changes 2026-10-14/19, by Samuel Lavery's agent team:
  - the W9A2 window and nine-point weights of ajp88-w9a2-window-nine-point (riemannzeta.fun, 2026-10-19, Apache-2.0), the
    weights taken at full resolution (B = 454741897490/10¹⁴): from that file, the window's numerators `cAMn` and the dependent
    window declarations (the vAM bounds, the positive-variation check at 128 cells, the profile constants, the cell-evaluator
    tables CE / CJ / FA and the matching/pinching constants), transplanted unchanged (bridge-port);
  - certified on a composite tree sized at δ = 1.75e-5 (root 34 at δ = 1.8e-5): 48 roots (RCUT 1:51168,1:39936) and 12 walk
    cuts at 450 leaves, 11,857 leaves (am-cert, bridge-port);
  - tangent-position fine grid 2⁴ (in units of 2⁻¹⁵) in place of 2⁵: the one grid literal in `gptF` (bridge-port); every
    tangent is still checked per leaf by `TVal`;
  - fixed-width walk fields (no Y code) and the DCOV decoder-elimination leaf proof (am-cert);
  - the certificate's long numerals (walk limbs and table words, 257 definitions) written with the zfNat64 source packing of
    critical-strip-exclusion-attempt-1 (Zero Forge / @zkvoxels, GitHub cafeai, Apache-2.0), whose block is reproduced
    unmodified with its attribution after the imports (as also carried by ajp88-w9a2-window-nine-point): the macro elaborates
    to the same Nat numerals, and every packed literal was checked to decode to the original (bridge-port);
  - the range-end anchor: position code 34 reads the term range's end U (module PCellDKH, am-cert);
  - Yuhang Shi's anchor-variance term (shi-anchor-variance-refinement-2026) ported to the 9-point checker with a per-cell
    curvature table (here the W9A2 window's) as module PCellVarW (am-cert), applied to 21 leaves; PCellVarW's notice is kept
    verbatim;
  - certificate thinning and point pruning (am-cert): per leaf, minorant terms downgraded, multipliers dropped and rarely used
    tangent anchors moved to shared ones, while the leaf still certifies the floor below;
  - exact floor closure: c = 74913604925068882530357668923/8388608000000000000000000000000, the largest floor every leaf
    certifies (scale 2²³·10²⁴; am-cert);
  - the H_W enclosure closed to 10⁻³² with an own bound π < 3141592653589793238462643383280/10³⁰ (the lead's block, placed before
    the master-of-puppets3/4 block notice, which is kept verbatim): for the W9A2 window HW_ge
    67212374687824171413662471723172/10³².
  The matching/pinching chain is unchanged, so κ = (H_W⁻ − B)/(1 − c)
  = 2187514111273670128882891873424900096/3247536873076144967761579035576953125 = 0.67359177025.
-/

/- Source-only arithmetic probe prepared by Li Xiang with Codex, 2026-10-21.
Derived from fixed attempt-030 by Samuel Lavery and the credited authors above.
Only floor_numeric target is raised from H32 to H33; copied constants and proof
body are unchanged. No execution, compilation, kernel check or acceptance claimed. -/
import Mathlib
import Mathlib.Tactic.NormNum
set_option linter.all false
set_option Elab.async false
open scoped BigOperators
noncomputable section
namespace AMW
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
def dAM (n : ℕ) : ℝ := (cAM (n + 1) : ℝ)

def PAMhi : ℝ :=
 ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * (3141592653589793238462643383280 / 10 ^ 30 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2))
theorem floor_numeric :
   (672123746878241714136624717231727 / 10 ^ 33 : ℝ) ≤ 3 / 2 - (76024459707563015125354719862329 / 10 ^ 32) / (2 * (70710678118654752440084436210484/10^32) * (64963693908006244412947861604410 / 10 ^ 32))
     - PAMhi / (2 * (64963693908006244412947861604410 / 10 ^ 32) ^ 2) := by
 unfold PAMhi dAM
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num
theorem h33_ratio_exact :
    (((672123746878241714136624717231727 : ℝ) / 10 ^ 33
      - 38146515192197939200000000000 / 8388608000000000000000000000000)
      / (1 - 74913604925068882530357668923 / 8388608000000000000000000000000))
      = 10937570556368350644414459367124615168 / 16237684365380724838807895177884765625 := by
  norm_num

theorem h33_strict_improvement :
    (2187514111273670128882891873424900096 / 3247536873076144967761579035576953125 : ℝ)
      < 10937570556368350644414459367124615168 / 16237684365380724838807895177884765625 := by
  norm_num

end AMW
end

#print axioms AMW.floor_numeric
#print axioms AMW.h33_ratio_exact
#print axioms AMW.h33_strict_improvement
