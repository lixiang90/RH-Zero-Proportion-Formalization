/- SPDX-License-Identifier: Apache-2.0
Frozen 12- and 24-mode research window profiles. Their positivity and
domination are theorem statements about the actual cosine sums below.
No new kernel, Gram realization or zeta proportion is asserted here.
-/
import StructuralW10Followup20261016.WindowMajorantGeneral
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
open StructuralW10Followup20261016.WindowProfileGeneral
namespace StructuralW10Followup20261016.NewWindows

def nums12 : ℕ → ℤ
  | 0 => 14183114
  | 1 => -16443840
  | 2 => 5763613
  | 3 => 5685012
  | 4 => -262983
  | 5 => 4476684
  | 6 => -5977828
  | 7 => 3018694
  | 8 => -4805153
  | 9 => 5465782
  | 10 => -3315052
  | 11 => 4235519
  | _ => 0

def c12 (j : Fin 12) : ℝ := (nums12 (j : ℕ) : ℝ) / 1000000000

theorem sum_abs_c12 : ∑ j, |c12 j| ≤ (2 / 25 : ℝ) := by
  norm_num [c12, nums12, Fin.sum_univ_succ]

def v12 : ℝ → ℝ := profile c12

theorem v12_positive {s : ℝ} (hs : |s| ≤ 3 / 5) : 0 < v12 s := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 14 / 25)
    (profile_ge_wide c12 sum_abs_c12 hs)

theorem v12_dominated {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * v12 s ≤ Opeth.AMMajorant.scaledMajorant s :=
  WindowMajorantGeneral.normalized_profile_le_scaled_majorant c12 sum_abs_c12 hs

#print axioms sum_abs_c12
#print axioms v12_positive
#print axioms v12_dominated

def nums24 : ℕ → ℤ
  | 0 => 14152994
  | 1 => -16636494
  | 2 => 5847970
  | 3 => 5916828
  | 4 => -410410
  | 5 => 4365961
  | 6 => -6299724
  | 7 => 2688735
  | 8 => -4861059
  | 9 => 5064801
  | 10 => -3022207
  | 11 => 4508542
  | 12 => -1810144
  | 13 => 1344824
  | 14 => 405092
  | 15 => -288857
  | 16 => 227779
  | 17 => -187754
  | 18 => 158988
  | 19 => -137179
  | 20 => 120042
  | 21 => -106220
  | 22 => 94848
  | 23 => -85339
  | _ => 0

def c24 (j : Fin 24) : ℝ := (nums24 (j : ℕ) : ℝ) / 1000000000

theorem sum_abs_c24 : ∑ j, |c24 j| ≤ (2 / 25 : ℝ) := by
  norm_num [c24, nums24, Fin.sum_univ_succ]

def v24 : ℝ → ℝ := profile c24

theorem v24_positive {s : ℝ} (hs : |s| ≤ 3 / 5) : 0 < v24 s := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 14 / 25)
    (profile_ge_wide c24 sum_abs_c24 hs)

theorem v24_dominated {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * v24 s ≤ Opeth.AMMajorant.scaledMajorant s :=
  WindowMajorantGeneral.normalized_profile_le_scaled_majorant c24 sum_abs_c24 hs

#print axioms sum_abs_c24
#print axioms v24_positive
#print axioms v24_dominated

end StructuralW10Followup20261016.NewWindows
end
