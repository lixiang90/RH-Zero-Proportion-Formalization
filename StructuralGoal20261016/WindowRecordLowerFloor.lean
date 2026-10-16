/- SPDX-License-Identifier: Apache-2.0
The actual redesigned-window counting candidate for floor 11/1250 = 0.0088.
This floor is distinct from the 0.00884 candidate. Only the explicit actual
nine-gap floor remains an input; all window analysis and short-pair payment
are reused from already checked modules.
-/
import StructuralGoal20261016.WindowRecordDyadic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowRecordLowerFloor
open StructuralW10Followup20261016.NewLedger

def Floor : Prop := ∀ g : Fin 9 → ℝ, (∀ i, (123:ℝ)/128 ≤ g i) →
 (11:ℝ)/1250 ≤ WindowGapEnergy.Fw24 g
def kappa : ℝ := 1669185178522559118481/2478000000000000000000

theorem kappa_eq : kappa =
 ((6720963398090236473924/10^22:ℝ)-11055671/2500000000)/(1-11/1250) := by
 norm_num [kappa]

theorem improvement :
 (34191001116882886388531117129201664:ℝ)/50760020691785094633026544189453125 + 1/100000 < kappa := by
 norm_num [kappa]

theorem short_pair {t : ℝ} (ht : |t| ≤ (123:ℝ)/128) :
 (11:ℝ)/1250 ≤ WindowDiscreteEnergy.wfun t :=
 (show (11:ℝ)/1250 ≤ 221/25000 by norm_num).trans (WindowPairCertificate.short_pair_floor ht)

theorem summed (hfloor : Floor) :
 WindowDiscreteEnergy.SeparatedSummedCertificate W (11/1250) 0 (123/128) :=
 WindowDiscreteEnergy.summed_of_pointwise (by decide : 2 ≤ 10) W hfloor

theorem simple_dyadic (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0simple T (2*T) := by
 have h := WindowCounting.simple_dyadic (n := 10) (by decide) W adm
   (c := (11:ℝ)/1250) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun _ ht => short_pair ht) pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

theorem simple_cumulative (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0simple 0 T := by
 have h := WindowCounting.simple_cumulative (n := 10) (by decide) W adm
   (c := (11:ℝ)/1250) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun _ ht => short_pair ht) pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

theorem distinct_dyadic (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) := by
 have h := WindowCounting.distinct_dyadic (n := 10) (by decide) W adm
   (c := (11:ℝ)/1250) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun _ ht => short_pair ht) pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

theorem distinct_cumulative (hfloor : Floor) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 (kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T := by
 have h := WindowCounting.distinct_cumulative (n := 10) (by decide) W adm
   (c := (11:ℝ)/1250) (C := (0:ℝ)) (B := (11055671:ℝ)/2500000000)
   (hw := (6720963398090236473924:ℝ)/10^22) (sep := (123:ℝ)/128)
   (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
   (fun _ ht => short_pair ht) pressure_eq WindowEnergyBound.H24_ge (summed hfloor)
 rw [← kappa_eq] at h
 exact h

set_option pp.fullNames true
#print axioms improvement
#print axioms short_pair
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative
end StructuralGoal20261016.WindowRecordLowerFloor
end
