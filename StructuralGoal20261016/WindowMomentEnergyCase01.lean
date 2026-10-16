/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentEnergyData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMomentEnergyCase01
open WindowMomentEnergyCertificate WindowMomentEnergyData

theorem geometry : checkGeometry cell1 packet1 = true := by decide +kernel
theorem second : checkSecond cell1 packet1 = true := by decide +kernel
theorem checked : check cell1 packet1 = true := by
 simpa only [check,Bool.and_eq_true] using And.intro geometry second

theorem lower {g : Fin 9 → ℝ} (hg : WindowDifferenceCell.Contains cell1 g) :
 polynomial packet1 g ≤ WindowGapEnergy.Fw24 g :=
 WindowMomentEnergyCertificate.lower checked hg

theorem sublevel {g : Fin 9 → ℝ} {c : ℝ}
 (hg : WindowDifferenceCell.Contains cell1 g) (hbelow : WindowGapEnergy.Fw24 g < c) :
 polynomial packet1 g < c := WindowMomentEnergyCertificate.sublevel checked hg hbelow

set_option pp.fullNames true
#print axioms geometry
#print axioms second
#print axioms checked
#print axioms lower
#print axioms sublevel
end StructuralGoal20261016.WindowMomentEnergyCase01
end
