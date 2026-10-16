/- SPDX-License-Identifier: Apache-2.0
The compact raw integer coefficient table equals the already checked
rational table at every required centre and derivative order.
-/
import StructuralGoal20261016.WindowRawCoefficientData
import StructuralGoal20261016.WindowFixedTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowRawCoefficients
open WindowFixedInterval WindowRationalInterval WindowNormalizedJets

theorem table_eq : ∀ n : Fin 33, 1 ≤ (n:ℕ) → ∀ r : Fin 24,
 decode (WindowRawCoefficientData.W n r) = WindowJetTableData.W n r := by decide +kernel

theorem sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (r : ℕ) (hr : r ≤ 23) :
 Holds (decode (WindowRawCoefficientData.W n r)) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 have he := table_eq ⟨n,by omega⟩ (by change 1 ≤ n; exact hn0) ⟨r,by omega⟩
 change decode (WindowRawCoefficientData.W n r) = WindowJetTableData.W n r at he
 rw [he]
 exact WindowFixedTablesAll.w_sound hn0 hn1 r hr

set_option pp.fullNames true
#print axioms table_eq
#print axioms sound
end StructuralGoal20261016.WindowRawCoefficients
end
