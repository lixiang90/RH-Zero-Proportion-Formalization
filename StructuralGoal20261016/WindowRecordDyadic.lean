/- SPDX-License-Identifier: Apache-2.0
Dyadic forms of the redesigned-window candidate. The only remaining input
is the same explicit actual nine-gap energy floor as the cumulative forms.
-/
import StructuralGoal20261016.WindowRecordFromFloor
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowRecordDyadic
open StructuralW10Followup20261016.NewLedger WindowRecordFromFloor

theorem simple_dyadic (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0simple T (2*T) := by
 have h := WindowCounting.simple_dyadic (n := 10) (by decide) W adm
   (c := (221:ℝ)/25000) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun t ht => WindowPairCertificate.short_pair_floor ht)
   pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

theorem distinct_dyadic (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) := by
 have h := WindowCounting.distinct_dyadic (n := 10) (by decide) W adm
   (c := (221:ℝ)/25000) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun t ht => WindowPairCertificate.short_pair_floor ht)
   pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

set_option pp.fullNames true
#print axioms simple_dyadic
#print axioms distinct_dyadic
end StructuralGoal20261016.WindowRecordDyadic
end
