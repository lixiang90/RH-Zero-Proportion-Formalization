/- SPDX-License-Identifier: Apache-2.0
The actual redesigned-window zero-counting theorem with a single remaining
finite-dimensional energy-floor obligation. This is conditional until that
explicit floor is supplied; it is not an unconditional record assertion.
-/
import StructuralGoal20261016.WindowCounting
import StructuralGoal20261016.WindowPairCertificate
import StructuralGoal20261016.WindowEnergyBound
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowRecordFromFloor
open StructuralW10Followup20261016.NewLedger

def Floor : Prop := ∀ g : Fin 9 → ℝ, (∀ i, (123:ℝ)/128 ≤ g i) →
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g
def kappa : ℝ := 1669185178522559118481/2477900000000000000000

theorem kappa_eq : kappa =
 ((6720963398090236473924/10^22:ℝ)-11055671/2500000000)/(1-221/25000) := by
 norm_num [kappa]

theorem improvement :
 (34191001116882886388531117129201664:ℝ)/50760020691785094633026544189453125 + 1/100000 < kappa := by
 norm_num [kappa]

theorem summed (hfloor : Floor) :
 WindowDiscreteEnergy.SeparatedSummedCertificate W (221/25000) 0 (123/128) :=
 WindowDiscreteEnergy.summed_of_pointwise (by decide : 2 ≤ 10) W hfloor

theorem simple_cumulative (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0simple 0 T := by
 have h := WindowCounting.simple_cumulative (n := 10) (by decide) W adm
   (c := (221:ℝ)/25000) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun t ht => WindowPairCertificate.short_pair_floor ht)
   pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

theorem distinct_cumulative (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T := by
 have h := WindowCounting.distinct_cumulative (n := 10) (by decide) W adm
   (c := (221:ℝ)/25000) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun t ht => WindowPairCertificate.short_pair_floor ht)
   pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

set_option pp.fullNames true
#print axioms improvement
#print axioms simple_cumulative
#print axioms distinct_cumulative
end StructuralGoal20261016.WindowRecordFromFloor
end
