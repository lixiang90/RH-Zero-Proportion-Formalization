/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Named simple critical-line count corollaries of the fixed c260 certificate.
The website entry uses the weaker distinct count; these separate theorems
use the actual Zeta23.N0simple definition. They do not assert acceptance
of a bundled submission, independent replay, or a website record.
-/
import RecordProportion.AnalyticBridge
import RecordProportion.FiniteCertificate

noncomputable section
open scoped BigOperators
open Filter

namespace RHWeilRecord.SimpleCorollary

open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW
open RHWeil.RecordSubmission.FiniteCertificate

private theorem fixed_pressure : W9.B = gapPressure := by
  simpa only [gapPressure] using W9_pressure

private theorem fixed_local :
    ∀ g : Fin 8 → ℝ, (∀ r, 4/5 ≤ g r) → localReward ≤ Fw W9 g := by
  intro g hg
  simpa only [localReward] using W9_local_certificate g hg

/-- The all-zero lossless gain uses the actual simple critical-line count.
All local, point, geometry, and integer premises are discharged here. -/
theorem fixed_lossless_defect :
    ∀ d > 0, ∀ᶠ T in atTop,
      localReward * (Zeta23.N0simple T (2*T) : ℝ) -
        gapPressure * (Zeta23.Ncount T (2*T) : ℝ) -
        d * (Zeta23.Ncount T (2*T) : ℝ) ≤
          Dcirc zetaZeroConfig (mtParams T) T := by
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W9 W9_adm fixed_pressure W9_upper_pairmass fixed_local

/-- Closed dyadic c260 proportion for multiplicity-one critical-line zeros. -/
theorem simple_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0simple T (2*T) := by
  have hs := am_simple_dyadic_of_lossless_defect zetaZeroConfig paperInputs_zeta
    (by simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using fixed_lossless_defect)
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hs

/-- Closed cumulative c260 proportion using the same true simple count.
Only the already proved interval additivity and dyadic summation are used. -/
theorem simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' zetaSeam) simple_dyadic

end RHWeilRecord.SimpleCorollary
