/-
Local core audit for Li Xiang (lixiang90), Apache-2.0.
The primitive list and kernel replay follow Comparator Main.lean at
273294467ce06429e6667ece7f5699f8678c9f4e.
Copyright (c) 2025 Lean FRO, LLC. Authors: Henrik Böving.
This driver uses the pinned Comparator modules directly. It does not run
landrun or certify official website acceptance; nanoda is checked separately.
-/
import Lean
import Comparator
import Export.Parse

private def allowed : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def primitive : Array Lean.Name :=
  #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div,
    ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
    ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat,
    ``List, ``eagerReduce]

private def readExport (path : String) : IO Export.ExportedEnv := do
  let handle ← IO.FS.Handle.mk path .read
  Export.parseStream (IO.FS.Stream.ofHandle handle)

def main (args : List String) : IO Unit := do
  let challengePath :: solutionPath :: targets := args
    | throw <| IO.userError "Expected challenge export, solution export and theorem names"
  if targets.isEmpty then
    throw <| IO.userError "At least one theorem target is required"
  let challenge ← readExport challengePath
  let solution ← readExport solutionPath
  let theoremNames := targets.toArray.map String.toName
  IO.ofExcept <| Comparator.compareAt challenge solution (theoremNames ++ allowed) #[] primitive
  IO.println "Pinned Comparator statement, dependency and primitive comparison passed"
  IO.ofExcept <| Comparator.checkAxioms solution theoremNames #[] allowed
  IO.println "Pinned Comparator transitive axiom check passed"
  let env ← Lean.mkEmptyEnvironment
  let declarations := solution.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay declarations
  IO.println "Lean default kernel replay passed"
  IO.println "Local Comparator core audit passed; official sandbox and nanoda are separate"
