import RecordProportion.ImportedAM
import Lean.Parser.Module
open Matrix
run_cmd do
  let file := "/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/memory-optimization-20261010/am/AMSyncAlias8.lean"
  let content ← IO.FS.readFile file
  let parsedModule ← Lean.Parser.testParseModule (←Lean.getEnv) file content
  let cmds := parsedModule[1].getArgs
  let rows := cmds.filterMap fun cmd =>
    if Lean.Parser.isTerminalCommand cmd then none else do
      let start ← cmd.getPos?
      let stop ← cmd.getTailPos?
      let isProof := cmd.find? (fun s => s.isOfKind ``Lean.Parser.Command.theorem || s.isOfKind `lemma) |>.isSome
      return s!"{start.byteIdx}\t{stop.byteIdx}\t{isProof}\t{cmd.getKind}"
  IO.FS.writeFile "/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp/memory-optimization-20261010/am/command-boundaries.tsv" (String.intercalate "\n" rows.toList)
  Lean.logInfo s!"BOUNDARIES {rows.size}"
