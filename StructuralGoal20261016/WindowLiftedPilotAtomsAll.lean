/- SPDX-License-Identifier: Apache-2.0
All 43 actual derivative-graph atoms in the lifted pilot.
-/
import StructuralGoal20261016.WindowLiftedPilotAtoms00
import StructuralGoal20261016.WindowLiftedPilotAtoms01
import StructuralGoal20261016.WindowLiftedPilotAtoms02
import StructuralGoal20261016.WindowLiftedPilotAtoms03
import StructuralGoal20261016.WindowLiftedPilotAtoms04
import StructuralGoal20261016.WindowLiftedPilotAtoms05
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowLiftedPilotAtomsAll
open WindowLiftedPilotData WindowLiftedPilotAtoms
theorem pairAlignment : ∀ e : Fin 41,
 (WindowGramTransfer.pairI e:ℕ) = pairFirst e ∧
 (WindowGramTransfer.pairJ e:ℕ) = pairLast e := by decide +kernel
theorem checked (i : Fin 43) : WindowLiftedKKT.checkAtom (123/128) cell (atoms i) = true := by
 fin_cases i
 · exact checks00 ⟨0,by decide⟩ (by decide)
 · exact checks00 ⟨1,by decide⟩ (by decide)
 · exact checks00 ⟨2,by decide⟩ (by decide)
 · exact checks00 ⟨3,by decide⟩ (by decide)
 · exact checks00 ⟨4,by decide⟩ (by decide)
 · exact checks00 ⟨5,by decide⟩ (by decide)
 · exact checks00 ⟨6,by decide⟩ (by decide)
 · exact checks00 ⟨7,by decide⟩ (by decide)
 · exact checks01 ⟨0,by decide⟩ (by decide)
 · exact checks01 ⟨1,by decide⟩ (by decide)
 · exact checks01 ⟨2,by decide⟩ (by decide)
 · exact checks01 ⟨3,by decide⟩ (by decide)
 · exact checks01 ⟨4,by decide⟩ (by decide)
 · exact checks01 ⟨5,by decide⟩ (by decide)
 · exact checks01 ⟨6,by decide⟩ (by decide)
 · exact checks01 ⟨7,by decide⟩ (by decide)
 · exact checks02 ⟨0,by decide⟩ (by decide)
 · exact checks02 ⟨1,by decide⟩ (by decide)
 · exact checks02 ⟨2,by decide⟩ (by decide)
 · exact checks02 ⟨3,by decide⟩ (by decide)
 · exact checks02 ⟨4,by decide⟩ (by decide)
 · exact checks02 ⟨5,by decide⟩ (by decide)
 · exact checks02 ⟨6,by decide⟩ (by decide)
 · exact checks02 ⟨7,by decide⟩ (by decide)
 · exact checks03 ⟨0,by decide⟩ (by decide)
 · exact checks03 ⟨1,by decide⟩ (by decide)
 · exact checks03 ⟨2,by decide⟩ (by decide)
 · exact checks03 ⟨3,by decide⟩ (by decide)
 · exact checks03 ⟨4,by decide⟩ (by decide)
 · exact checks03 ⟨5,by decide⟩ (by decide)
 · exact checks03 ⟨6,by decide⟩ (by decide)
 · exact checks03 ⟨7,by decide⟩ (by decide)
 · exact checks04 ⟨0,by decide⟩ (by decide)
 · exact checks04 ⟨1,by decide⟩ (by decide)
 · exact checks04 ⟨2,by decide⟩ (by decide)
 · exact checks04 ⟨3,by decide⟩ (by decide)
 · exact checks04 ⟨4,by decide⟩ (by decide)
 · exact checks04 ⟨5,by decide⟩ (by decide)
 · exact checks04 ⟨6,by decide⟩ (by decide)
 · exact checks04 ⟨7,by decide⟩ (by decide)
 · exact checks05 ⟨0,by decide⟩ (by decide)
 · exact checks05 ⟨1,by decide⟩ (by decide)
 · exact checks05 ⟨2,by decide⟩ (by decide)
set_option pp.fullNames true
#print axioms pairAlignment
#print axioms checked
end StructuralGoal20261016.WindowLiftedPilotAtomsAll
