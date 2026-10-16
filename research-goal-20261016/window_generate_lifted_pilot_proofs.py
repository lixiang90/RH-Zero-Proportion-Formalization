"""Assemble atom checkpoints and cache the finite lifted aggregate once."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
pilot_only='--pilot-only' in sys.argv
mods=json.loads((HERE/'window_lifted_pilot_atom_modules.json').read_bytes())
source='''/- SPDX-License-Identifier: Apache-2.0
All 43 actual derivative-graph atoms in the lifted pilot.
-/
'''+''.join(f'import {m}\n'for m in mods)+'''set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowLiftedPilotAtomsAll
open WindowLiftedPilotData WindowLiftedPilotAtoms
theorem pairAlignment : ∀ e : Fin 41,
 (WindowGramTransfer.pairI e:ℕ) = pairFirst e ∧
 (WindowGramTransfer.pairJ e:ℕ) = pairLast e := by decide +kernel
theorem checked (i : Fin 43) : WindowLiftedKKT.checkAtom (123/128) cell (atoms i) = true := by
 fin_cases i
'''
for k in range(43):
    g,r=divmod(k,8);source+=f' · exact checks{g:02} ⟨{r},by decide⟩ (by decide)\n'
source+='set_option pp.fullNames true\n#print axioms pairAlignment\n#print axioms checked\nend StructuralGoal20261016.WindowLiftedPilotAtomsAll\n'
if not pilot_only:
    (ROOT/'StructuralGoal20261016/WindowLiftedPilotAtomsAll.lean').write_text(source,encoding='utf8',newline='\n')
aggregate='''/- SPDX-License-Identifier: Apache-2.0
The 43 lifted forms are summed once. Stored coefficients have no analytic
meaning until their exact equality with this actual aggregate is checked.
-/
import StructuralGoal20261016.WindowLiftedPilotData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowLiftedPilotAggregate
open WindowLiftedPilotData WindowLiftedFarkas
def forms (i : Fin 43) : Form := WindowLiftedKKT.form cell (atoms i)
theorem gap : ∀ r : Fin 9, (aggregate forms weights).gap r = stated.gap r := by decide +kernel
set_option pp.fullNames true
#print axioms gap
theorem scalar : ∀ e : Fin 41, (aggregate forms weights).scalar e = stated.scalar e := by decide +kernel
#print axioms scalar
theorem bound : (aggregate forms weights).bound = stated.bound := by decide +kernel
#print axioms bound
theorem form_ext {a b : Form} (hg : a.gap = b.gap) (hs : a.scalar = b.scalar)
 (hb : a.bound = b.bound) : a = b := by
 cases a with
 | mk ga sa ba =>
   cases b with
   | mk gb sb bb =>
     change ga = gb at hg
     change sa = sb at hs
     change ba = bb at hb
     cases hg
     cases hs
     cases hb
     rfl
theorem equal : aggregate forms weights = stated :=
 form_ext (funext gap) (funext scalar) bound
#print axioms equal
theorem farkas_checked : WindowLiftedFarkas.check cell forms weights minimum edges = true := by
 unfold WindowLiftedFarkas.check
 rw [equal]
 decide +kernel
#print axioms farkas_checked
end StructuralGoal20261016.WindowLiftedPilotAggregate
'''
if not pilot_only:
    (ROOT/'StructuralGoal20261016/WindowLiftedPilotAggregate.lean').write_text(aggregate,encoding='utf8',newline='\n')
proof='''/- SPDX-License-Identifier: Apache-2.0
A complete actual lifted graph/KKT pilot on one frozen difference cell.
All scalar, facet and finite aggregate premises are discharged. This local
exclusion is not a complete global cover or an unconditional zero record.
-/
import StructuralGoal20261016.WindowLiftedPilotAtomsAll
import StructuralGoal20261016.WindowLiftedPilotAggregate
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowLiftedPilot
open WindowLiftedPilotData
theorem checked : WindowLiftedKKT.check (123/128) cell atoms weights minimum edges = true := by
 unfold WindowLiftedKKT.check
 simp only [Bool.and_eq_true]
 constructor
 · simpa only [decide_eq_true_eq] using WindowLiftedPilotAtomsAll.checked
 · exact WindowLiftedPilotAggregate.farkas_checked
theorem exclude {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell g) : False := by
 apply WindowLiftedKKT.exclude atoms weights minimum edges checked
 · simpa only [Rat.cast_div,Rat.cast_ofNat] using hg
 · exact hcell
set_option pp.fullNames true
#print axioms checked
#print axioms exclude
end StructuralGoal20261016.WindowLiftedPilot
'''
(ROOT/'StructuralGoal20261016/WindowLiftedPilot.lean').write_text(proof,encoding='utf8',newline='\n')
print('Lifted atom aggregation, cached finite Farkas check, and actual pilot written; not yet Lean checked')
