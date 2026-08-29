/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Parser.Command

/-!
# The "emptyLine" linter

The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.
-/

public meta section

open Lean Elab Linter

namespace Lean

/--
Definition of `Substring.Raw.getRange` / `Substring.Raw.getRange` 的定义

English:
definition Substring.Raw.getRange
  signature: : Substring.Raw -> Syntax.Range

中文:
定义 Substring.Raw.getRange
  签名: : Substring.Raw -> Syntax.值域

Depends on / 依赖: stopPos
-/
def Substring.Raw.getRange : Substring.Raw -> Syntax.Range
  | {startPos := st, stopPos := en, ..} => ⟨st, en⟩

namespace Syntax
/-!
### `Syntax` filters
-/

/--
`filterMapM stx f` takes as input a `Syntax` `stx` and a monadic function `f : Syntax → m α`.
It produces the array of the `some` values that `f` takes while traversing `stx`.

See `filterMap` for a non-monadic version.
-/
partial
/--
Definition of `filterMapM` / `filterMapM` 的定义

English:
definition filterMapM
  signature: {m : Type -> Type} [Monad m] {α} (stx : Syntax) (f : Syntax -> m (Option α))
  body: do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

中文:
定义 filterMapM
  签名: {m : 类型 -> 类型} [单子 m] {α} (stx : Syntax) (f : Syntax -> m (选项类型 α))
  定义体: do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs
-/
def filterMapM {m : Type -> Type} [Monad m] {α} (stx : Syntax) (f : Syntax -> m (Option α)) :
    m (Array α) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

/--
Definition of `filterMap` / `filterMap` 的定义

English:
definition filterMap
  signature: {α} (stx : Syntax) (f : Syntax -> Option α)
  body: Id.run stx.filterMapM fun x => pure (f x)

中文:
定义 filterMap
  签名: {α} (stx : Syntax) (f : Syntax -> 选项类型 α)
  定义体: Id.run stx.filterMapM fun x => pure (f x)

Depends on / 依赖: Id.run, filterMapM, stx.filterMapM
-/
def filterMap {α} (stx : Syntax) (f : Syntax -> Option α) : Array α :=
Id.run stx.filterMapM fun x => pure (f x)

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (stx : Syntax) (f : Syntax -> Bool)
  body: stx.filterMap fun s => if f s then some s else none

中文:
定义 filter
  签名: (stx : Syntax) (f : Syntax -> 布尔值)
  定义体: stx.filterMap fun s => if f s then some s else none

Depends on / 依赖: filterMap, stx.filterMap
-/
def filter (stx : Syntax) (f : Syntax -> Bool) : Array Syntax :=
  stx.filterMap fun s => if f s then some s else none

end Lean.Syntax

namespace Mathlib.Linter

/--
The "emptyLine" linter emits a warning on empty lines inside a command, but outside of a
doc-string/module-doc.

The linter is only active when there are no other warnings, so as to not add noise when developing
incomplete proofs.
-/
register_option linter.style.emptyLine : Bool := {
  defValue := false
  descr := "enable the emptyLine linter"
}

namespace EmptyLine

/--
Definition of `AllowEmptyLines` / `AllowEmptyLines` 的定义

English:
abbreviation AllowEmptyLines
  signature: : Std.HashSet SyntaxNodeKind
  body: Std.HashSet.emptyWithCapacity
.insert ``Parser.Command.docComment
.insert ``Parser.Command.moduleDoc
.insert ``Parser.Command.mutual
.insert `str

中文:
缩写 AllowEmptyLines
  签名: : Std.HashSet SyntaxNodeKind
  定义体: Std.HashSet.emptyWithCapacity
.insert ``Parser.Command.docComment
.insert ``Parser.Command.moduleDoc
.insert ``Parser.Command.mutual
.insert `str

Depends on / 依赖: HashSet, Std.HashSet.emptyWithCapacity, emptyWithCapacity
-/
abbrev AllowEmptyLines : Std.HashSet SyntaxNodeKind := Std.HashSet.emptyWithCapacity
.insert ``Parser.Command.docComment
.insert ``Parser.Command.moduleDoc
.insert ``Parser.Command.mutual
.insert `str

/--
Definition of `SkippedFileSegments` / `SkippedFileSegments` 的定义

English:
abbreviation SkippedFileSegments
  signature: : Std.HashSet Name
  body: Std.HashSet.emptyWithCapacity
.insert `Tactic
.insert `Util
.insert `Meta

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]

中文:
缩写 SkippedFileSegments
  签名: : Std.HashSet Name
  定义体: Std.HashSet.emptyWithCapacity
.insert `Tactic
.insert `Util
.insert `Meta

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]

Depends on / 依赖: HashSet, Std.HashSet.emptyWithCapacity, emptyWithCapacity
-/
abbrev SkippedFileSegments : Std.HashSet Name := Std.HashSet.emptyWithCapacity
.insert `Tactic
.insert `Util
.insert `Meta

@[inherit_doc Mathlib.Linter.linter.style.emptyLine]
/--
Definition of `emptyLineLinter` / `emptyLineLinter` 的定义

English:
definition emptyLineLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.emptyLine (← getLinterOptions) do
    return
  -- The linter does not report anything on incomplete proofs, e.g. proofs containing `sorry`
  -- or `stop`.
  if (← get).messages.reportedPlusUnreported.any (!·.severity matches .

中文:
定义 emptyLineLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.emptyLine (← getLinterOptions) do
    return
  -- The linter does not report anything on incomplete proofs, e.g. proofs containing `sorry`
  -- or `stop`.
  if (← get).messages.reportedPlusUnreported.any (!·.severity matches .

Depends on / 依赖: withSetOptionIn
-/
def emptyLineLinter : Linter where run := withSetOptionIn fun stx => do
  unless Linter.getLinterValue linter.style.emptyLine (← getLinterOptions) do
    return
  -- The linter does not report anything on incomplete proofs, e.g. proofs containing `sorry`
  -- or `stop`.
  if (← get).messages.reportedPlusUnreported.any (!·.severity matches .information) then
    return
  if ((← getMainModule).components.find? SkippedFileSegments.contains).isSome then
    return
  -- We ignore empty lines "after" the command finished.
  let stx := stx.unsetTrailing
  let some str := stx.getSubstring? | return
  let allowed := stx.filter (AllowEmptyLines.contains ·.getKind)
  let allowedRanges := allowed.filterMap (·.getRange?)
  let one :: rest@(_ :: _) := str.toString.trimAsciiEnd.copy.splitOn "\n\n" | return
  -- We extract all trailing ranges of all syntax nodes in `stx`, after we remove
  -- leading and trailing whitespace from them.
  -- These ranges typically represent embedded comments and we ignore line breaks inside them.
  -- We do inspect leading and trailing whitespace though.
  -- We treat `where` specially, since we allow empty lines in `where` fields.
  let trails := stx.filterMap fun s =>
    if let some str := s.getTrailing?
    then
      -- Handle `where` and `where` fields.
      if s.getAtomVal == "where" ||
         s.isOfKind ``Parser.Term.structInstField ||
         s.isOfKind ``Parser.Command.structSimpleBinder then
        s.getTrailing?.map (·.getRange)
      else
        let strim := str.trim
        if strim.toString.toSlice.contains "\n\n" then
          some strim.getRange
        else none
    else none
  let trails : Std.HashSet Syntax.Range := .ofArray trails
  -- The entries of the array `rgs` represent
  -- * the range of the offending line breaks,
  -- * the line preceding an empty line and
  -- * the line following an empty line.
  let mut ranges : Array (Syntax.Range × String × String) := #[]
  let mut currOffset := str.startPos.offsetBy (one.rawEndPos.increaseBy 1)
  let mut prev := one.takeEndWhile (· != '\n')
  for r in rest do
    ranges := ranges.push (⟨currOffset, currOffset⟩, prev.copy, (r.takeWhile (· != '\n')).copy)
    currOffset := currOffset.offsetBy (r.rawEndPos.increaseBy 2)
    prev := r.takeEndWhile (· != '\n')
  let allowedRanges := trails.insertMany allowedRanges
  for (rg, before, after) in ranges do
    if allowedRanges.any fun okRg => okRg.start <= rg.start && rg.stop <= okRg.stop then
      continue
    -- `s` is a string of as many spaces (` `) as the characters of the previous line.
    -- This, followed by the downarrow (`↓`) creates a pointer to an offending line break.
let s : String := .join List.replicate (before.length + 1) " "
    Linter.logLint linter.style.emptyLine (.ofRange rg)
      m!"Please, write a comment here or remove this line, \
        but do not place empty lines within commands!\nContext:\
        {indentD s!"{s.push '↓'}"}{indentD s!"⏎{before}⏎⏎{after}⏎"}"

initialize addLinter emptyLineLinter

end EmptyLine

end Mathlib.Linter
