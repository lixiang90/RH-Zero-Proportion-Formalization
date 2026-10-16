/- SPDX-License-Identifier: Apache-2.0
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
