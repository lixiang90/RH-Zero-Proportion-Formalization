import GramDefectRecord.RefinedCounting
import GramDefectRecord.SharpWindow
import GramDefectRecord.ScaledCertificate

/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Exact refinement of the accepted master-of-puppets4 critical-line bound.
The same nine-point objective is checked at a finer rational threshold and
combined with a sharper window floor. Every premise is discharged below.
-/
noncomputable section

namespace GramDefectRecord

def windowFloor : ℝ := 672168410564118874775945444401 / 10 ^ 30
def localFloor : ℝ := 85638285989 / 10000000000000
def pressure : ℝ := 436674 / 100000000
def recordRatio : ℝ := 39282451209654051457408555553 / 58319774788300000000000000000
def previousSiteRatio : ℝ := 667801670564118872522651 / 991436171500000000000000

theorem exact_formula : (windowFloor - pressure) / (1 - localFloor) = recordRatio := by
  norm_num [windowFloor, pressure, localFloor, recordRatio]

theorem strict_improvement : previousSiteRatio < recordRatio := by
  norm_num [previousSiteRatio, recordRatio]

theorem simple_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have h := Counting.simple_dyadic (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFailScaled.W9 RiemannFailScaled.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFailScaled.W9_B)
    (by simpa only [windowFloor] using ProportionSharpWindow.HW_ge)
    (by simpa only [localFloor] using RiemannFailScaled.cert_AM)
  simpa only [exact_formula] using h

theorem simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T := by
  have h := Counting.simple_cumulative (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFailScaled.W9 RiemannFailScaled.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFailScaled.W9_B)
    (by simpa only [windowFloor] using ProportionSharpWindow.HW_ge)
    (by simpa only [localFloor] using RiemannFailScaled.cert_AM)
  simpa only [exact_formula] using h

theorem distinct_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  have h := Counting.distinct_dyadic (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFailScaled.W9 RiemannFailScaled.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFailScaled.W9_B)
    (by simpa only [windowFloor] using ProportionSharpWindow.HW_ge)
    (by simpa only [localFloor] using RiemannFailScaled.cert_AM)
  simpa only [exact_formula] using h

theorem distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T := by
  have h := Counting.distinct_cumulative (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFailScaled.W9 RiemannFailScaled.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFailScaled.W9_B)
    (by simpa only [windowFloor] using ProportionSharpWindow.HW_ge)
    (by simpa only [localFloor] using RiemannFailScaled.cert_AM)
  simpa only [exact_formula] using h

end GramDefectRecord
