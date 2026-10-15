import GramDefect20261015.RefinedCounting
import GramDefect20261015.SharpWindow

/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Exact refinement of the accepted ajp88 reweighted nine-point bound.
The same certificate tree proves a higher local floor, retaining weights
and pressures. The window uses alternating cos/sinc polynomials at
theta^2 = 1/2. Every analytic and finite premise is discharged below.
-/
noncomputable section

namespace GramDefect20261015

def windowFloor : ℝ := 6721684105641188747759983512104999330646 / 10 ^ 40
def localFloor : ℝ := 859538525913875481 / 100000000000000000000
def pressure : ℝ := 437688000000 / 100000000000000
def recordRatio : ℝ := 3338957652820594373879991756052499665323 / 4957023073704306225950000000000000000000
def previousSiteRatio : ℝ := 834739413205148593469931805501689594457 / 1239255769294131601825000000000000000000

theorem exact_formula : (windowFloor - pressure) / (1 - localFloor) = recordRatio := by
  norm_num [windowFloor, pressure, localFloor, recordRatio]

theorem strict_improvement : previousSiteRatio < recordRatio := by
  norm_num [previousSiteRatio, recordRatio]

theorem simple_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have h := Counting.simple_dyadic (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFail.W9 RiemannFail.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFail.W9_B)
    (by simpa only [windowFloor] using GramDefect20261015.Window.HW_ge)
    (by simpa only [localFloor] using RiemannFail.cert_AM)
  simpa only [exact_formula] using h

theorem simple_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T := by
  have h := Counting.simple_cumulative (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFail.W9 RiemannFail.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFail.W9_B)
    (by simpa only [windowFloor] using GramDefect20261015.Window.HW_ge)
    (by simpa only [localFloor] using RiemannFail.cert_AM)
  simpa only [exact_formula] using h

theorem distinct_dyadic :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  have h := Counting.distinct_dyadic (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFail.W9 RiemannFail.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFail.W9_B)
    (by simpa only [windowFloor] using GramDefect20261015.Window.HW_ge)
    (by simpa only [localFloor] using RiemannFail.cert_AM)
  simpa only [exact_formula] using h

theorem distinct_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T := by
  have h := Counting.distinct_cumulative (hw := windowFloor) (c := localFloor) (B := pressure)
    (by norm_num : 2 ≤ 9) RiemannFail.W9 RiemannFail.W9_adm
    (by norm_num [localFloor]) (by norm_num [localFloor])
    (by simpa only [pressure] using RiemannFail.W9_B)
    (by simpa only [windowFloor] using GramDefect20261015.Window.HW_ge)
    (by simpa only [localFloor] using RiemannFail.cert_AM)
  simpa only [exact_formula] using h

end GramDefect20261015
