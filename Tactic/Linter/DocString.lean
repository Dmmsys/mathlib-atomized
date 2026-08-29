/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public meta import Std.Data.Iterators.Combinators.Zip
public import Lean.Parser.Command
meta import Std.Data.Iterators.Producers.Range

/-!
# The "DocString" style linter

The "DocString" linter validates style conventions regarding doc-string formatting.
-/

meta section

open Lean Elab Linter

namespace Mathlib.Linter

/--
The "DocString" linter validates style conventions regarding doc-string formatting.
-/
public register_option linter.style.docString : Bool := {
  defValue := false
  descr := "enable the style.docString linter"
}

/--
The "empty doc string" warns on empty doc-strings.
-/
public register_option linter.style.docString.empty : Bool := {
  defValue := true
  descr := "enable the style.docString.empty linter"
}

/--
The `docStringVerso` linter warns on docstrings that cannot be parsed by Verso.
Since this linter only checks syntax, not semantics, it is no assurance that complying docstrings
are actually accepted by Verso.
-/
public register_option linter.style.docStringVerso : Bool := {
  defValue := false
  descr := "enable the style.docStringVerso linter"
}

/--
Extract all `declModifiers` from the input syntax. We later extract the `docstring` from it,
but we avoid extracting directly the `docComment` node, to skip `#adaptation_note`s.
-/
public def getDeclModifiers : Syntax -> Array Syntax
  | s@(.node _ kind args) =>
    (if kind == ``Parser.Command.declModifiers then #[s] else #[]) ++ args.flatMap getDeclModifiers
  | _ => #[]

/--
Definition of `deindentString` / `deindentString` 的定义

English:
definition deindentString
  signature: (currIndent : Nat) (docString : String)
  body: let indent : String := String.ofList ('\n' :: List.replicate currIndent ' ')
  docString.replace indent " "

中文:
定义 deindentString
  签名: (currIndent : 自然数) (docString : String)
  定义体: let indent : String := String.ofList ('\n' :: List.replicate currIndent ' ')
  docString.replace indent " "

Depends on / 依赖: List.replicate, String.ofList, currIndent, docString, docString.replace, indent, ofList, replace, replicate
-/
def deindentString (currIndent : Nat) (docString : String) : String :=
  let indent : String := String.ofList ('\n' :: List.replicate currIndent ' ')
  docString.replace indent " "

open Command Parser in
/--
Definition of `checkVersoSyntax` / `checkVersoSyntax` 的定义

English:
definition checkVersoSyntax
  signature: (docComment : String) (fileName : Option String := none)
  body: do
  let fileName := fileName.getD (← getFileName)
  let env ← getEnv
  let ictx : InputContext := .mk docComment fileName
  let text := ictx.fileMap
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDec

中文:
定义 checkVersoSyntax
  签名: (docComment : String) (fileName : 选项类型 String := none)
  定义体: do
  let fileName := fileName.getD (← getFileName)
  let env ← getEnv
  let ictx : InputContext := .mk docComment fileName
  let text := ictx.fileMap
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDec
-/
def checkVersoSyntax (docComment : String) (fileName : Option String := none) :
    CommandElabM (Array (String.Pos.Raw × SyntaxStack × Error)) := do
  let fileName := fileName.getD (← getFileName)
  let env ← getEnv
  let ictx : InputContext := .mk docComment fileName
  let text := ictx.fileMap
  let pmctx : ParserModuleContext := {
    env,
    options := ← getOptions,
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
  let s := mkParserState docComment
  let s := Doc.Parser.document.run ictx pmctx (getTokenTable env) s
  return s.allErrors

/--
Definition of `isSilencedVersoWarning` / `isSilencedVersoWarning` 的定义

English:
definition isSilencedVersoWarning
  signature: (err : Parser.Error)
  body: -- Ignore Markdown link/reference syntax (this should be fixed automatically and all at once).
  "link target '(url)' or '[ref]' (use '\\[' for a literal '[')" in err.expected

中文:
定义 isSilencedVersoWarning
  签名: (err : Parser.Error)
  定义体: -- Ignore Markdown link/reference syntax (this should be fixed automatically and all at once).
  "link target '(url)' or '[ref]' (use '\\[' for a literal '[')" in err.expected
-/
def isSilencedVersoWarning (err : Parser.Error) : Bool :=
  -- Ignore Markdown link/reference syntax (this should be fixed automatically and all at once).
  "link target '(url)' or '[ref]' (use '\\[' for a literal '[')" in err.expected

open Command Parser in
/--
Definition of `lintVersoSyntax` / `lintVersoSyntax` 的定义

English:
definition lintVersoSyntax
  signature: (docComment : String) (fileName : Option String := none)
  body: do
  -- Drop anything that looks like an autolink: this is not supported by Verso. Adding full links
  -- everywhere would be very noisy.
let trimmedStr := Std.Iter.fold (· ++ ·) ""
.map fun str => docComment.splitInclusive Char.isWhitespace
      if (str.contains "http://" || str.contains "https://

中文:
定义 lintVersoSyntax
  签名: (docComment : String) (fileName : 选项类型 String := none)
  定义体: do
  -- Drop anything that looks like an autolink: this is not supported by Verso. Adding full links
  -- everywhere would be very noisy.
let trimmedStr := Std.Iter.fold (· ++ ·) ""
.map fun str => docComment.splitInclusive Char.isWhitespace
      if (str.contains "http://" || str.contains "https://
-/
def lintVersoSyntax (docComment : String) (fileName : Option String := none) :
    CommandElabM (Array (String.Pos.Raw × SyntaxStack × Error)) := do
  -- Drop anything that looks like an autolink: this is not supported by Verso. Adding full links
  -- everywhere would be very noisy.
let trimmedStr := Std.Iter.fold (· ++ ·) ""
.map fun str => docComment.splitInclusive Char.isWhitespace
      if (str.contains "http://" || str.contains "https://") && !str.contains "(http" then "URL"
      else str.toString
  -- Drop anything between LaTeX `$$`s.
  -- We keep single `$`s, since those also occur in `backquoted` code snippets (e.g. as `· <$> ·`),
  -- and so we'd need to build an actual parser to figure out if they are in a snippet or not.
let trimmedStr := Std.Iter.fold (· ++ ·) ""
trimmedStr.split " "
.zip (0...docComment.length).iter
.map fun (str, i) => if i % 2 == 0 then str.toString else "LaTeX"
  let errs ← checkVersoSyntax trimmedStr fileName
  return errs.filter fun (_, _, err) => !isSilencedVersoWarning err

namespace Style

@[inherit_doc Mathlib.Linter.linter.style.docString]
/--
Definition of `docStringLinter` / `docStringLinter` 的定义

English:
definition docStringLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docString (← getLinterOptions) ||
      getLinterValue linter.style.docString.empty (← getLinterOptions) ||
      getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    

中文:
定义 docStringLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docString (← getLinterOptions) ||
      getLinterValue linter.style.docString.empty (← getLinterOptions) ||
      getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    

Depends on / 依赖: withSetOptionIn
-/
def docStringLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docString (← getLinterOptions) ||
      getLinterValue linter.style.docString.empty (← getLinterOptions) ||
      getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let fm ← getFileMap
  for declMods in getDeclModifiers stx do
    -- `docStx` extracts the `Lean.Parser.Command.docComment` node from the declaration modifiers.
    -- In particular, this ignores parsing `#adaptation_note`s.
    let docStx := declMods[0][0]

    let some pos := docStx.getPos? | continue
.column let currIndent := fm.toPosition pos

    if docStx.isMissing then continue -- this is probably superfluous, thanks to `some pos` above.
    -- ignore antiquotations from syntax patterns like `$(_)?`
    unless docStx.getKind == ``Parser.Command.docComment do continue
    -- `docString` contains e.g. trailing spaces before the `-/`, but does not contain
    -- any leading whitespace before the actual string starts.
    let docString ← try getDocStringText ⟨docStx⟩ catch _ => continue
    if docString.trimAscii.isEmpty then
      Linter.logLintIf linter.style.docString.empty docStx m!"warning: this doc-string is empty"
      continue
    -- `startSubstring` is the whitespace between `/--` and the actual doc-string text.
    let startSubstring := match docStx with
      | .node _ _ #[(.atom si ..), _] => si.getTrailing?.getD default
      | _ => default
    -- We replace all line-breaks followed by `currIndent` spaces with a single space.
    let start := deindentString currIndent startSubstring.toString
    if !#["\n", " "].contains start then
      let startRange := {start := startSubstring.startPos, stop := startSubstring.stopPos}
      Linter.logLintIf linter.style.docString (.ofRange startRange)
        s!"error: doc-strings should start with a single space or newline"

    let deIndentedDocString := deindentString currIndent docString

    let docTrim := deIndentedDocString.trimAsciiEnd.copy
    let tail := docTrim.length
    -- `endRange` creates an 0-wide range `n` characters from the end of `docStx`
    let endRange (n : Nat) : Syntax := .ofRange
      {start := docStx.getTailPos?.get!.unoffsetBy ⟨n⟩, stop := docStx.getTailPos?.get!.unoffsetBy ⟨n⟩}
    if docTrim.takeEnd 1 == ",".toSlice then
      Linter.logLintIf linter.style.docString (endRange (docString.length - tail + 3))
        s!"error: doc-strings should not end with a comma"
    if tail + 1 != deIndentedDocString.length then
      Linter.logLintIf linter.style.docString (endRange 3)
        s!"error: doc-strings should end with a single space or newline"
    -- Check for verso syntax, but only if it is not already enabled.
    -- If Verso is already enabled for docstrings, then this check would be superfluous.
    if !doc.verso.get (← getOptions) &&
        getLinterValue linter.style.docStringVerso (← getLinterOptions) then do
      let errs ← lintVersoSyntax docString
      for (pos, stxStack, err) in errs do
        Linter.logLint linter.style.docStringVerso stxStack.back m!"{err}"

initialize addLinter docStringLinter

/--
Definition of `moduleDocVersoLinter` / `moduleDocVersoLinter` 的定义

English:
definition moduleDocVersoLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  -- Check for verso syntax, but only if it is not already enabled.
  -- If Verso is already enabled for module docs, then this check would be superfluous.
  let opts ← getOptions
  i

中文:
定义 moduleDocVersoLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  -- Check for verso syntax, but only if it is not already enabled.
  -- If Verso is already enabled for module docs, then this check would be superfluous.
  let opts ← getOptions
  i

Depends on / 依赖: withSetOptionIn
-/
def moduleDocVersoLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.style.docStringVerso (← getLinterOptions) do
    return
  -- Check for verso syntax, but only if it is not already enabled.
  -- If Verso is already enabled for module docs, then this check would be superfluous.
  let opts ← getOptions
  if (doc.verso.module.get? opts).getD (doc.verso.get opts) then return
  if (← get).messages.hasErrors then
    return
  let some moduleDoc := (match stx with
  | s@(.node _ ``Parser.Command.moduleDoc args) => some s
  | _ => none) | return
  try
    let docString ← getDocStringText ⟨moduleDoc⟩
    let errs ← lintVersoSyntax docString
    for (pos, stxStack, err) in errs do
      Linter.logLint linter.style.docStringVerso stxStack.back m!"{err}"
  catch _ => return

initialize addLinter moduleDocVersoLinter

end Style

end Mathlib.Linter
