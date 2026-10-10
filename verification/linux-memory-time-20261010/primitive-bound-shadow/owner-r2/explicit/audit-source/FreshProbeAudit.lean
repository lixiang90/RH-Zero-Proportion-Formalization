import PrimitiveExplicit
import Comparator.Util
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option pp.universes true
open Lean Elab Command
private def usedConsts (info : Lean.ConstantInfo) : Array Lean.Name :=
  ((Comparator.runForUsedConsts info (fun n => modify (fun ns => ns.push n)) :
      StateM (Array Lean.Name) Unit).run #[]).2
run_cmd do
  let env ← Lean.getEnv
  let probe := `RHWeil.RecordSubmission.FiniteCertificate.primitiveBound_sound_probe_explicit
  let old := `RHWeil.RecordSubmission.FiniteCertificate.primitiveBound_sound
  let some p := env.find? probe | throwError "missing probe theorem"
  let some o := env.find? old | throwError "missing original target type"
  unless p.type == o.type do
    throwError "shadow type differs structurally from original"
  IO.eprintln "PROBE_TYPE_IDENTICAL true"
  let mut pending := #[probe]
  let mut seen : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      if n == old then throwError "original theorem used by shadow closure"
      let some info := env.find? n | throwError "missing dependency {n}"
      seen := seen.insert n
      if let .axiomInfo _ := info then
        unless n == `propext || n == `Quot.sound || n == `Classical.choice do
          throwError "nonstandard axiom {n}"
        axioms := axioms.insert n
      pending := pending ++ usedConsts info
  IO.eprintln s!"PROBE_CLOSURE_CHECKED {seen.size} ORIGINAL_TARGET_PRESENT false"
  IO.eprintln s!"PROBE_STANDARD_AXIOMS {axioms.toArray}"
#check RHWeil.RecordSubmission.FiniteCertificate.primitiveBound_sound_probe_explicit
#print axioms RHWeil.RecordSubmission.FiniteCertificate.primitiveBound_sound_probe_explicit
