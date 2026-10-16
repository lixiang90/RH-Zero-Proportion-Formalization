/- SPDX-License-Identifier: Apache-2.0
Raw integer witness dispatch for isolating certificate decoding costs.
-/
import StructuralW10Cert20261016.EagerLeaf

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
namespace StructuralW10Cert20261016.RawLeaf
abbrev Certificate := List Term × List DualMove

def dispatch (raw : ℕ → Certificate) (c : Cl) (id : ℕ) : Bool :=
  if id ≤ 45 then LeafDispatch.check (fun _ => 0) c id
  else
    let d := raw (id-46)
    EagerLeaf.checkLeaf c d.1 d.2

theorem dispatch_sound (raw : ℕ → Certificate) (c : Cl) (id : ℕ)
    (h : dispatch raw c id = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  unfold dispatch at h
  split_ifs at h
  · exact LeafDispatch.check_sound (fun _ => 0) c id h
  · rw [EagerLeaf.checkLeaf_eq] at h
    exact checkLeaf_sound h

#print axioms dispatch_sound
end StructuralW10Cert20261016.RawLeaf
end
