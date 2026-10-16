/-
SPDX-License-Identifier: Apache-2.0
Source packaging only. The pure decoder reconstructs UTF-8 commands, which are
then parsed and elaborated normally. It supplies no proof, changes no kernel
checking rule, and invokes no external process or filesystem operation.
-/
import Lean

namespace StructuralW10Cert20261016.CompressedCommands
open Lean Elab Command

/-- Printable ASCII 33..126, with quote and backslash omitted. -/
def decode92 (text : String) : Nat :=
  text.foldl (fun acc ch =>
    let digit := ch.toNat - 33 - (if 34 < ch.toNat then 1 else 0) -
      (if 92 < ch.toNat then 1 else 0)
    acc * 92 + digit) 0

/-- Each source literal contains at most 256 little-endian bytes. -/
def unpackChunks (size : Nat) (chunks : Array String) : Except String ByteArray := do
  if chunks.size != (size + 255) / 256 then
    throw "wrong compressed chunk count"
  let mut output := ByteArray.empty
  for text in chunks do
    let mut word := decode92 text
    let count := min 256 (size - output.size)
    for _ in [:count] do
      output := output.push (UInt8.ofNat (word % 256))
      word := word / 256
    if word != 0 then throw "compressed chunk exceeds its declared byte length"
  if output.size != size then throw "compressed byte length mismatch"
  return output

/-- Eight tokens share one low-bit-first flag byte. Literal tokens are one
byte. Copy tokens are distance-minus-one in two little-endian bytes followed
by length-minus-three. The growing output implements overlapping copies. -/
def decompress (expected : Nat) (input : ByteArray) : Except String ByteArray := do
  let mut output := ByteArray.empty
  let mut pos := 0
  for _ in [:input.size + 1] do
    if output.size = expected then break
    if input.size ≤ pos then throw "truncated flag byte"
    let flags := (input.get! pos).toNat
    pos := pos + 1
    for bit in [:8] do
      if output.size = expected then break
      if (flags / (2 ^ bit)) % 2 = 0 then
        if input.size ≤ pos then throw "truncated literal"
        output := output.push (input.get! pos)
        pos := pos + 1
      else
        if input.size < pos + 3 then throw "truncated copy"
        let distance := (input.get! pos).toNat +
          256 * (input.get! (pos+1)).toNat + 1
        let count := (input.get! (pos+2)).toNat + 3
        pos := pos + 3
        if output.size < distance then throw "copy points before output"
        if expected < output.size + count then throw "copy exceeds declared output length"
        for _ in [:count] do
          let byte := output.get! (output.size - distance)
          output := output.push byte
  if output.size != expected then throw "decompressed length mismatch"
  if pos != input.size then throw "unused compressed input"
  return output

/-- Replay in the current command state, so namespace, section, local options,
notation and every generated declaration have the ordinary Lean meaning.
Imports remain outside the compressed body. EOI is not elaborated here,
allowing a namespace/section to continue in subsequent ordinary commands. -/
def elaborateSource (text : String) : CommandElabM Unit := do
  let outer ← read
  let input := Parser.mkInputContext text (outer.fileName ++ ":w10-expanded")
  let mut parserState : Parser.ModuleParserState := { pos := 0 }
  for _ in [:text.utf8ByteSize + 1] do
    let before := parserState.pos
    let state ← get
    let scope := state.scopes.head!
    let context : Parser.ParserModuleContext := {
      env := state.env, options := scope.opts,
      currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (command, next, messages) := Parser.parseCommand input context parserState state.messages
    parserState := next
    modify fun s => { s with messages := messages }
    if command.isOfKind ``Lean.Parser.Command.eoi then return
    if Parser.isTerminalCommand command then
      throwError "imports and exit are not permitted inside w10_expand"
    if messages.hasErrors then throwError "parsing an expanded command failed"
    if parserState.pos == before then throwError "expanded command parser made no progress"
    withReader (fun ctx => { ctx with
        fileName := input.fileName, fileMap := input.fileMap,
        cmdPos := before, ref := command, snap? := none }) do
      elabCommandTopLevel command #[]
    if (← get).messages.hasErrors then throwError "elaborating an expanded command failed"
  throwError "expanded command count exceeds its byte length"

end StructuralW10Cert20261016.CompressedCommands

syntax (name := w10ExpandCommands) "w10_expand" num num "[" str,* "]" : command
elab_rules : command
  | `(w10_expand $expected:num $size:num [$chunks:str,*]) => do
    let texts := chunks.getElems.map (fun s => s.getString)
    let input ← match StructuralW10Cert20261016.CompressedCommands.unpackChunks size.getNat texts with
      | .ok bytes => pure bytes
      | .error message => throwError "w10_expand: {message}"
    let bytes ← match StructuralW10Cert20261016.CompressedCommands.decompress expected.getNat input with
      | .ok bytes => pure bytes
      | .error message => throwError "w10_expand: {message}"
    let text ← match String.fromUTF8? bytes with
      | some text => pure text
      | none => throwError "w10_expand: decompressed source is not valid UTF-8"
    StructuralW10Cert20261016.CompressedCommands.elaborateSource text
