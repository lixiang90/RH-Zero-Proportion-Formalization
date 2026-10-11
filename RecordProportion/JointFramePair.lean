import RecordProportion.JointFramePairAnalytic
import RecordProportion.JointFramePairLocal
import RecordProportion.JointFramePairFinite

/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Unconditional strengthened simple critical-line zero-proportion theorem.
The new joint frame-pair finite certificate is discharged by JointFramePairFinite.
Every old c260 theorem and submission is retained in its original namespace.
-/
noncomputable section
open scoped BigOperators
open Filter

namespace RHWeilRecord.JointFramePair
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW
open RHWeil.RecordSubmission.FiniteCertificate

private theorem fixed_pressure : W9.B = RHWeilRecord.gapPressure := by
  simpa only [RHWeilRecord.gapPressure] using W9_pressure

/-- Full, unconditional local theorem on all real separated eight-gap frames. -/
theorem local_certificate (g : Fin 8 → ℝ) (hg : ∀ r, (4:ℝ)/5 ≤ g r) :
    localReward ≤ Fw W9 g := by
  simpa only [localReward] using
    RHWeil.RecordSubmission.JointFramePairLocal.local_from_low_pairs
      RHWeil.RecordSubmission.JointFramePairFinite.frame_lower
      RHWeil.RecordSubmission.JointFramePairFinite.low_pair_bound g hg

/-- Actual simple critical-line counts; all new finite hypotheses are proved. -/
theorem fixed_lossless_defect :
    ∀ d > 0, ∀ᶠ T in atTop,
      localReward * (Zeta23.N0simple T (2*T) : ℝ) -
        RHWeilRecord.gapPressure * (Zeta23.Ncount T (2*T) : ℝ) -
        d * (Zeta23.Ncount T (2*T) : ℝ) ≤
          Dcirc zetaZeroConfig (mtParams T) T := by
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W9 W9_adm fixed_pressure W9_upper_pairmass local_certificate

/-- New dyadic proportion for multiplicity-one critical-line zeros. -/
theorem simple_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0simple T (2*T) :=
  simple_dyadic_of_nine_point_certificate
    W9 W9_adm fixed_pressure W9_upper_pairmass local_certificate

/-- New cumulative proportion for the same actual simple-zero count. -/
theorem simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  simple_cumulative_of_nine_point_certificate
    W9 W9_adm fixed_pressure W9_upper_pairmass local_certificate

/-- Simple-zero inclusion gives the site's actual distinct critical-line count. -/
theorem distinct_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0star T (2*T) :=
  distinct_dyadic_of_nine_point_certificate
    W9 W9_adm fixed_pressure W9_upper_pairmass local_certificate

theorem distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T :=
  distinct_cumulative_of_nine_point_certificate
    W9 W9_adm fixed_pressure W9_upper_pairmass local_certificate

end RHWeilRecord.JointFramePair
