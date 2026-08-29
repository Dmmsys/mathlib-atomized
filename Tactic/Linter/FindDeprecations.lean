/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Init
public import Lean.Elab.Import

/-!
# The `#clear_deprecations` command

This file defines the `#clear_deprecations date₁ date₂ really` command.

This function is intended for automated use by the `remove_deprecations` automation.
It removes declarations that have been deprecated in the time range starting from `date₁` and
ending with `date₂`.

See the doc-string for the command for more information.
-/

meta section

open Lean Elab Command

namespace Mathlib.Tactic

/--
A convenience instance to print a `Lean.Syntax.Range` as the corresponding pair of `String.Pos`.
-/
local instance : ToString Lean.Syntax.Range where
  toString | ⟨s, e⟩ => s!"({s}, {e})"

/--
Definition of `repos` / `repos` 的定义

English:
definition repos
  signature: : NameSet
  body: .ofArray #[`Mathlib, `Archive, `Counterexamples]

中文:
定义 repos
  签名: : NameSet
  定义体: .ofArray #[`Mathlib, `Archive, `Counterexamples]

Depends on / 依赖: Archive, Counterexamples, Mathlib, ofArray
-/
def repos : NameSet := .ofArray #[`Mathlib, `Archive, `Counterexamples]

/--
Definition of `DeprecationInfo` / `DeprecationInfo` 的定义

English:
structure DeprecationInfo
  parameters: where
  axioms and operations (5):
    - module : Name
    - decl : Name
    - rgStart : Position
    - rgStop : Position
    - since : String

中文:
结构 DeprecationInfo
  参数: where
  公理与运算 (5 个):
    - module : Name
    - decl : Name
    - rgStart : Position
    - rgStop : Position
    - since : String
-/
structure DeprecationInfo where
  /-- `module` is the name of the module containing the deprecated declaration. -/
  module : Name
  /-- `decl` is the name of the deprecated declaration. -/
  decl : Name
  /-- `rgStart` is the `Position` where the deprecated declaration starts. -/
  rgStart : Position
  /-- `rgStop` is the `Position` where the deprecated declaration ends. -/
  rgStop : Position
  /-- `since` is the date when the declaration was deprecated. -/
  since : String

/--
Definition of `getPosAfterImports` / `getPosAfterImports` 的定义

English:
definition getPosAfterImports
  signature: (fname : String)
  body: do
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
  return fm.ofPosition fileStartPos

中文:
定义 getPosAfterImports
  签名: (fname : String)
  定义体: do
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
  return fm.ofPosition fileStartPos
-/
def getPosAfterImports (fname : String) : CommandElabM String.Pos.Raw := do
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let (_, fileStartPos, _) ← parseImports fm.source (← getFileName)
  return fm.ofPosition fileStartPos

/--
Definition of `addAfterImports` / `addAfterImports` 的定义

English:
definition addAfterImports
  signature: (fname s : String)
  body: do
  let pos ← getPosAfterImports fname
  let file ← IO.FS.readFile fname
  let fileSubstring := file.toRawSubstring
  return {fileSubstring with stopPos := pos}.toString ++ s ++
    {fileSubstring with startPos := pos}.toString

中文:
定义 addAfterImports
  签名: (fname s : String)
  定义体: do
  let pos ← getPosAfterImports fname
  let file ← IO.FS.readFile fname
  let fileSubstring := file.toRawSubstring
  return {fileSubstring with stopPos := pos}.toString ++ s ++
    {fileSubstring with startPos := pos}.toString
-/
def addAfterImports (fname s : String) : CommandElabM String := do
  let pos ← getPosAfterImports fname
  let file ← IO.FS.readFile fname
  let fileSubstring := file.toRawSubstring
  return {fileSubstring with stopPos := pos}.toString ++ s ++
    {fileSubstring with startPos := pos}.toString

/--
Definition of `getDeprecatedInfo` / `getDeprecatedInfo` 的定义

English:
definition getDeprecatedInfo
  signature: (nm : Name) (verbose? : Bool)
  body: do
  let env ← getEnv
  -- if there is a `since` in the deprecation
  if let some {since? := some since, ..} := Linter.deprecatedAttr.getParam? env nm
  then
    -- retrieve the `range` for the declaration
    if let some {range := rg, ..} ← findDeclarationRanges? nm
    then
      -- retrieve the module where the declaration is located
      if let some mod ← findModuleOf? nm
      then
        -- We filter here based on the top dir of the declaration.
        unless repos.contains mod.getRoot do
          return none
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some { module := mod
                      decl := nm
                      rgStart := rg.pos
                      rgStop := rg.endPos
                      since := since }
  return none

中文:
定义 getDeprecatedInfo
  签名: (nm : Name) (verbose? : 布尔值)
  定义体: do
  let env ← getEnv
  -- if there is a `since` in the deprecation
  if let some {since? := some since, ..} := Linter.deprecatedAttr.getParam? env nm
  then
    -- retrieve the `range` for the declaration
    if let some {range := rg, ..} ← findDeclarationRanges? nm
    then
      -- retrieve the module where the declaration is located
      if let some mod ← findModuleOf? nm
      then
        -- We filter here based on the top dir of the declaration.
        unless repos.contains mod.getRoot do
          return none
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some { module := mod
                      decl := nm
                      rgStart := rg.pos
                      rgStop := rg.endPos
                      since := since }
  return none
-/
def getDeprecatedInfo (nm : Name) (verbose? : Bool) :
    CommandElabM (Option DeprecationInfo) := do
  let env ← getEnv
  -- if there is a `since` in the deprecation
  if let some {since? := some since, ..} := Linter.deprecatedAttr.getParam? env nm
  then
    -- retrieve the `range` for the declaration
    if let some {range := rg, ..} ← findDeclarationRanges? nm
    then
      -- retrieve the module where the declaration is located
      if let some mod ← findModuleOf? nm
      then
        -- We filter here based on the top dir of the declaration.
        unless repos.contains mod.getRoot do
          return none
        if verbose? then
          logInfo
            s!"In the module '{mod}', the declaration {nm} at {rg.pos}--{rg.endPos} \
              is deprecated since {since}"
        return some { module := mod
                      decl := nm
                      rgStart := rg.pos
                      rgStop := rg.endPos
                      since := since }
  return none

/--
Definition of `deprecatedHashMap` / `deprecatedHashMap` 的定义

English:
definition deprecatedHashMap
  signature: (oldDate newDate : String)
  body: do
  let mut fin := ∅
  --let searchPath ← getSrcSearchPath
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, decl, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      unless repos.contains modName.getRoot do continue
      if !(oldDate <= since && since <= newDate) then
        continue
      -- Ideally, `lean` would be computed by `← findLean (← getSrcSearchPath) modName`
      -- However, while this works locally, CI throws the error ` unknown module prefix 'Mathlib'`
      let lean := (modName.components.foldl (init := "")
        fun a b => (a.push System.FilePath.pathSeparator) ++ b.toString) ++ ".lean" |>.drop 1
.copy
      --let lean ← findLean searchPath modName
      let file ← IO.FS.readFile lean
      let fm := FileMap.ofString file
      let rg : Lean.Syntax.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      fin := fin.alter (modName, lean) fun a =>
        (a.getD #[]).binInsert (·.2.1 < ·.2.1) (decl, rg)
  return fin

中文:
定义 deprecatedHashMap
  签名: (oldDate newDate : String)
  定义体: do
  let mut fin := ∅
  --let searchPath ← getSrcSearchPath
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, decl, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      unless repos.contains modName.getRoot do continue
      if !(oldDate <= since && since <= newDate) then
        continue
      -- Ideally, `lean` would be computed by `← findLean (← getSrcSearchPath) modName`
      -- However, while this works locally, CI throws the error ` unknown module prefix 'Mathlib'`
      let lean := (modName.components.foldl (init := "")
        fun a b => (a.push System.FilePath.pathSeparator) ++ b.toString) ++ ".lean" |>.drop 1
.copy
      --let lean ← findLean searchPath modName
      let file ← IO.FS.readFile lean
      let fm := FileMap.ofString file
      let rg : Lean.Syntax.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      fin := fin.alter (modName, lean) fun a =>
        (a.getD #[]).binInsert (·.2.1 < ·.2.1) (decl, rg)
  return fin
-/
def deprecatedHashMap (oldDate newDate : String) :
    CommandElabM (Std.HashMap (Name × String) (Array (Name × Lean.Syntax.Range))) := do
  let mut fin := ∅
  --let searchPath ← getSrcSearchPath
  for (nm, _) in (← getEnv).constants.map₁ do
    if let some ⟨modName, decl, rgStart, rgStop, since⟩ ← getDeprecatedInfo nm false
    then
      unless repos.contains modName.getRoot do continue
      if !(oldDate <= since && since <= newDate) then
        continue
      -- Ideally, `lean` would be computed by `← findLean (← getSrcSearchPath) modName`
      -- However, while this works locally, CI throws the error ` unknown module prefix 'Mathlib'`
      let lean := (modName.components.foldl (init := "")
        fun a b => (a.push System.FilePath.pathSeparator) ++ b.toString) ++ ".lean" |>.drop 1
.copy
      --let lean ← findLean searchPath modName
      let file ← IO.FS.readFile lean
      let fm := FileMap.ofString file
      let rg : Lean.Syntax.Range := ⟨fm.ofPosition rgStart, fm.ofPosition rgStop⟩
      fin := fin.alter (modName, lean) fun a =>
        (a.getD #[]).binInsert (·.2.1 < ·.2.1) (decl, rg)
  return fin

/--
`removeRanges file rgs` removes from the string `file` the substrings whose ranges are in the array
`rgs`.

*Notes*.
* The command makes the assumption that `rgs` is *sorted*.
* The command removes all consecutive whitespace following the end of each range.
-/
public -- for use in unit tests, but perhaps useful more broadly
/--
Definition of `removeRanges` / `removeRanges` 的定义

English:
definition removeRanges
  signature: (file : String) (rgs : Array Lean.Syntax.Range)
  body: Id.run do
  let mut curr : String.Pos.Raw := 0
  let mut fileSubstring := file.toRawSubstring
  let mut tot := ""
  let last := fileSubstring.stopPos
  for next in rgs.push ⟨last, last⟩ do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := {fileSubstring with startPos := next.stop}.trimLeft
  return tot

中文:
定义 removeRanges
  签名: (file : String) (rgs : 数组 Lean.Syntax.值域)
  定义体: Id.run do
  let mut curr : String.Pos.Raw := 0
  let mut fileSubstring := file.toRawSubstring
  let mut tot := ""
  let last := fileSubstring.stopPos
  for next in rgs.push ⟨last, last⟩ do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := {fileSubstring with startPos := next.stop}.trimLeft
  return tot

Depends on / 依赖: Id.run
-/
def removeRanges (file : String) (rgs : Array Lean.Syntax.Range) : String := Id.run do
  let mut curr : String.Pos.Raw := 0
  let mut fileSubstring := file.toRawSubstring
  let mut tot := ""
  let last := fileSubstring.stopPos
  for next in rgs.push ⟨last, last⟩ do
    if next.start < curr then continue
    let part := {fileSubstring with stopPos := next.start}.toString
    tot := tot ++ part
    curr := next.start
    fileSubstring := {fileSubstring with startPos := next.stop}.trimLeft
  return tot

/--
Definition of `removeDeprecations` / `removeDeprecations` 的定义

English:
definition removeDeprecations
  signature: (fname : String) (rgs : Array Lean.Syntax.Range)
  body: return removeRanges (← IO.FS.readFile fname) rgs

中文:
定义 removeDeprecations
  签名: (fname : String) (rgs : 数组 Lean.Syntax.值域)
  定义体: return removeRanges (← IO.FS.readFile fname) rgs

Depends on / 依赖: IO.FS.readFile, readFile, removeRanges, return
-/
def removeDeprecations (fname : String) (rgs : Array Lean.Syntax.Range) : IO String :=
  return removeRanges (← IO.FS.readFile fname) rgs

/--
`parseLine line` assumes that the input string is of the form
```
info: File/Path.lean:12:0: [362, 398, 399]
```
and extracts `[362, 398, 399]`.
It makes the assumption that there is a unique `: [` substring and then retrieves the numbers.

Note that this is the output of `Mathlib.Linter.CommandRanges.commandRangesLinter`
that the script here is parsing.
-/
public -- for use in unit tests, but perhaps useful more broadly
/--
Definition of `parseLine` / `parseLine` 的定义

English:
definition parseLine
  signature: (line : String)
  body: match (line.dropEnd 1).copy.splitOn ": [" with
  | [_, rest] =>
    let nums := rest.splitOn ", "
    if nums == [""] then some [] else
some nums.map fun s => ⟨s.toNat?.getD 0⟩
  | _ => none

中文:
定义 parseLine
  签名: (line : String)
  定义体: match (line.dropEnd 1).copy.splitOn ": [" with
  | [_, rest] =>
    let nums := rest.splitOn ", "
    if nums == [""] then some [] else
some nums.map fun s => ⟨s.toNat?.getD 0⟩
  | _ => none

Depends on / 依赖: copy.splitOn, dropEnd, line.dropEnd, nums.map, rest.splitOn, s.toNat, splitOn
-/
def parseLine (line : String) : Option (List String.Pos.Raw) :=
  match (line.dropEnd 1).copy.splitOn ": [" with
  | [_, rest] =>
    let nums := rest.splitOn ", "
    if nums == [""] then some [] else
some nums.map fun s => ⟨s.toNat?.getD 0⟩
  | _ => none

/--
Definition of `rewriteOneFile` / `rewriteOneFile` 的定义

English:
definition rewriteOneFile
  signature: (fname : String) (rgs : Array (Name × Lean.Syntax.Range))
  body: do
  -- `option` is the extra text that we add to the files that contain deprecations.
  -- We save these modified files with a different name then their originals, so that all their
  -- dependencies still have valid `olean`s and we build them to collect the ranges of the commands
  -- in each one of them.
  let option :=
    s!"\nimport Mathlib.Tactic.Linter.CommandRanges\n\
      set_option linter.commandRanges true\n"
  -- `offset` represents the difference between a position in the modified file and the
  -- corresponding position in the original file.
  -- Since we added the modification right after the imports, the command positions of the old file
  -- are always smaller than the command positions of the new file.
  let offset := option.toRawSubstring.stopPos
  let fileWithOptionAdded ← addAfterImports fname option
  let fname_with_option := (fname.dropEnd ".lean".length).copy ++ "_with_option.lean"
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let rgsPos := rgs.map fun (decl, ⟨s, e⟩) =>
    m!"* {.ofConstName decl} {(fm.toPosition s, fm.toPosition e)}"
  let rgsStringPos := rgs.map (m!"{·.2}")
.toList let combinedRanges := rgsPos.zipWith (· ++ m!" " ++ ·) rgsStringPos
  logInfo m!"Adding '{option}' to '{fname}'\nWriting to {indentD fname_with_option}\n\
          Removing the following declarations\n{m!"\n".joinSep combinedRanges}"
  IO.FS.writeFile fname_with_option fileWithOptionAdded
  let ranges := rgs.map (·.2)

  logInfo m!"Retrieving command positions from '{fname_with_option}'"
  let commandPositions ←
    IO.Process.output {cmd := "lake", args := #["build", fname_with_option]}
  -- `stringPositions` consists of lists of the form `[p₁, p₂, p₃]`, where
  -- * `p₁` is the start of a command;
  -- * `p₂` is the end of the command, excluding trailing whitespace and comments;
  -- * `p₁` is the end of the command, including trailing whitespace and comments.
.reduceOption let stringPositions := (commandPositions.stdout.splitOn "\n").map parseLine
  let mut removals : Std.HashSet (List String.Pos.Raw) := ∅
  -- For each range `rg` in `ranges`, we isolate the unique entry of `stringPositions` that
  -- entirely contains `rg`. This helps catching the full range of `open Nat in @[deprecated] ...`,
  -- rather than just the `@[deprecated] ...` range.
  let : Sub String.Pos.Raw := ⟨fun | ⟨a⟩, ⟨b⟩ => ⟨a - b⟩⟩
  for rg in ranges do
    let candidate := stringPositions.filterMap (fun arr =>
      let a := arr.head! - offset
      let b := arr[arr.length - 1]! - offset
      if a <= rg.start ∧ rg.stop <= b then some (arr.map (· - offset)) else none)
    match candidate with
    | [d@([_, _, _])] => removals := removals.insert d
    | _ => logInfo "Something went wrong!"
  -- We only remember the `start` and `end` of each command, ignoring trailing whitespace and
  -- comments. This means that we may err on the side of preserving comments that may have to be
  -- manually removed, instead of having to manually add them back later on.
  let rems : Std.HashSet _ := removals.fold (init := ∅) fun tot => fun
    | [a, b, _c] => tot.insert (⟨a, b⟩ : Lean.Syntax.Range)
    | _ => tot
  return (fname_with_option, ← removeDeprecations fname (rems.toArray.qsort (·.1 < ·.1)))

中文:
定义 rewriteOneFile
  签名: (fname : String) (rgs : 数组 (Name × Lean.Syntax.值域))
  定义体: do
  -- `option` is the extra text that we add to the files that contain deprecations.
  -- We save these modified files with a different name then their originals, so that all their
  -- dependencies still have valid `olean`s and we build them to collect the ranges of the commands
  -- in each one of them.
  let option :=
    s!"\nimport Mathlib.Tactic.Linter.CommandRanges\n\
      set_option linter.commandRanges true\n"
  -- `offset` represents the difference between a position in the modified file and the
  -- corresponding position in the original file.
  -- Since we added the modification right after the imports, the command positions of the old file
  -- are always smaller than the command positions of the new file.
  let offset := option.toRawSubstring.stopPos
  let fileWithOptionAdded ← addAfterImports fname option
  let fname_with_option := (fname.dropEnd ".lean".length).copy ++ "_with_option.lean"
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let rgsPos := rgs.map fun (decl, ⟨s, e⟩) =>
    m!"* {.ofConstName decl} {(fm.toPosition s, fm.toPosition e)}"
  let rgsStringPos := rgs.map (m!"{·.2}")
.toList let combinedRanges := rgsPos.zipWith (· ++ m!" " ++ ·) rgsStringPos
  logInfo m!"Adding '{option}' to '{fname}'\nWriting to {indentD fname_with_option}\n\
          Removing the following declarations\n{m!"\n".joinSep combinedRanges}"
  IO.FS.writeFile fname_with_option fileWithOptionAdded
  let ranges := rgs.map (·.2)

  logInfo m!"Retrieving command positions from '{fname_with_option}'"
  let commandPositions ←
    IO.Process.output {cmd := "lake", args := #["build", fname_with_option]}
  -- `stringPositions` consists of lists of the form `[p₁, p₂, p₃]`, where
  -- * `p₁` is the start of a command;
  -- * `p₂` is the end of the command, excluding trailing whitespace and comments;
  -- * `p₁` is the end of the command, including trailing whitespace and comments.
.reduceOption let stringPositions := (commandPositions.stdout.splitOn "\n").map parseLine
  let mut removals : Std.HashSet (List String.Pos.Raw) := ∅
  -- For each range `rg` in `ranges`, we isolate the unique entry of `stringPositions` that
  -- entirely contains `rg`. This helps catching the full range of `open Nat in @[deprecated] ...`,
  -- rather than just the `@[deprecated] ...` range.
  let : Sub String.Pos.Raw := ⟨fun | ⟨a⟩, ⟨b⟩ => ⟨a - b⟩⟩
  for rg in ranges do
    let candidate := stringPositions.filterMap (fun arr =>
      let a := arr.head! - offset
      let b := arr[arr.length - 1]! - offset
      if a <= rg.start ∧ rg.stop <= b then some (arr.map (· - offset)) else none)
    match candidate with
    | [d@([_, _, _])] => removals := removals.insert d
    | _ => logInfo "Something went wrong!"
  -- We only remember the `start` and `end` of each command, ignoring trailing whitespace and
  -- comments. This means that we may err on the side of preserving comments that may have to be
  -- manually removed, instead of having to manually add them back later on.
  let rems : Std.HashSet _ := removals.fold (init := ∅) fun tot => fun
    | [a, b, _c] => tot.insert (⟨a, b⟩ : Lean.Syntax.Range)
    | _ => tot
  return (fname_with_option, ← removeDeprecations fname (rems.toArray.qsort (·.1 < ·.1)))
-/
def rewriteOneFile (fname : String) (rgs : Array (Name × Lean.Syntax.Range)) :
    CommandElabM (String × String) := do
  -- `option` is the extra text that we add to the files that contain deprecations.
  -- We save these modified files with a different name then their originals, so that all their
  -- dependencies still have valid `olean`s and we build them to collect the ranges of the commands
  -- in each one of them.
  let option :=
    s!"\nimport Mathlib.Tactic.Linter.CommandRanges\n\
      set_option linter.commandRanges true\n"
  -- `offset` represents the difference between a position in the modified file and the
  -- corresponding position in the original file.
  -- Since we added the modification right after the imports, the command positions of the old file
  -- are always smaller than the command positions of the new file.
  let offset := option.toRawSubstring.stopPos
  let fileWithOptionAdded ← addAfterImports fname option
  let fname_with_option := (fname.dropEnd ".lean".length).copy ++ "_with_option.lean"
  let file ← IO.FS.readFile fname
  let fm := file.toFileMap
  let rgsPos := rgs.map fun (decl, ⟨s, e⟩) =>
    m!"* {.ofConstName decl} {(fm.toPosition s, fm.toPosition e)}"
  let rgsStringPos := rgs.map (m!"{·.2}")
.toList let combinedRanges := rgsPos.zipWith (· ++ m!" " ++ ·) rgsStringPos
  logInfo m!"Adding '{option}' to '{fname}'\nWriting to {indentD fname_with_option}\n\
          Removing the following declarations\n{m!"\n".joinSep combinedRanges}"
  IO.FS.writeFile fname_with_option fileWithOptionAdded
  let ranges := rgs.map (·.2)

  logInfo m!"Retrieving command positions from '{fname_with_option}'"
  let commandPositions ←
    IO.Process.output {cmd := "lake", args := #["build", fname_with_option]}
  -- `stringPositions` consists of lists of the form `[p₁, p₂, p₃]`, where
  -- * `p₁` is the start of a command;
  -- * `p₂` is the end of the command, excluding trailing whitespace and comments;
  -- * `p₁` is the end of the command, including trailing whitespace and comments.
.reduceOption let stringPositions := (commandPositions.stdout.splitOn "\n").map parseLine
  let mut removals : Std.HashSet (List String.Pos.Raw) := ∅
  -- For each range `rg` in `ranges`, we isolate the unique entry of `stringPositions` that
  -- entirely contains `rg`. This helps catching the full range of `open Nat in @[deprecated] ...`,
  -- rather than just the `@[deprecated] ...` range.
  let : Sub String.Pos.Raw := ⟨fun | ⟨a⟩, ⟨b⟩ => ⟨a - b⟩⟩
  for rg in ranges do
    let candidate := stringPositions.filterMap (fun arr =>
      let a := arr.head! - offset
      let b := arr[arr.length - 1]! - offset
      if a <= rg.start ∧ rg.stop <= b then some (arr.map (· - offset)) else none)
    match candidate with
    | [d@([_, _, _])] => removals := removals.insert d
    | _ => logInfo "Something went wrong!"
  -- We only remember the `start` and `end` of each command, ignoring trailing whitespace and
  -- comments. This means that we may err on the side of preserving comments that may have to be
  -- manually removed, instead of having to manually add them back later on.
  let rems : Std.HashSet _ := removals.fold (init := ∅) fun tot => fun
    | [a, b, _c] => tot.insert (⟨a, b⟩ : Lean.Syntax.Range)
    | _ => tot
  return (fname_with_option, ← removeDeprecations fname (rems.toArray.qsort (·.1 < ·.1)))

/--
Definition of `importLT` / `importLT` 的定义

English:
definition importLT
  signature: (env : Environment) (f1 f2 : Name)
  body: (env.findRedundantImports #[f1, f2]).contains f1

中文:
定义 importLT
  签名: (env : Environment) (f1 f2 : Name)
  定义体: (env.findRedundantImports #[f1, f2]).contains f1

Depends on / 依赖: contains, env.findRedundantImports, findRedundantImports
-/
def importLT (env : Environment) (f1 f2 : Name) : Bool :=
  (env.findRedundantImports #[f1, f2]).contains f1

/--
`#clear_deprecations "YYYY₁-MM₁-DD₁" "YYYY₂-MM₂-DD₂" really` computes the declarations that have
the `@[deprecated]` attribute and the `since` field satisfies
`YYYY₁-MM₁-DD₁ ≤ since ≤ YYYY₂-MM₂-DD₂`.
For each one of them, it retrieves the command that generated it and removes it.
It also verbosely logs various steps of the computation.

Running `#clear_deprecations "YYYY₁-MM₁-DD₁" "YYYY₂-MM₂-DD₂"`, without the trailing `really` skips
the removal, but still emits the same verbose output.

This function is intended for automated use by the `remove_deprecations` automation.
-/
elab "#clear_deprecations " oldDate:str ppSpace newDate:str really?:(&" really")? : command => do
  let oldDate := oldDate.getString
  let newDate := newDate.getString
  let fmap ← deprecatedHashMap oldDate newDate
  let mut filesToRemove := #[]
  let env ← getEnv
  let sortedFMap := fmap.toArray.qsort fun ((a, _), _) ((b, _), _) => importLT env b a
  if sortedFMap.isEmpty then
    logInfo m!"No deprecations in the range from {oldDate} to {newDate}"
    return
  for ((modName, fname), noDeprs) in sortedFMap do
    let (toRemove, fileWithoutDeprecations) ← rewriteOneFile fname noDeprs
    let message :=
      m!"Click to see the file with the deprecations in the date range \
        {oldDate} to {newDate} removed"
    let collapsibleMessage := .trace {cls := modName} message #[fileWithoutDeprecations]
    logInfo collapsibleMessage
    if really?.isSome then
      IO.FS.writeFile fname fileWithoutDeprecations
    filesToRemove := filesToRemove.push toRemove
  logInfo
    m!"Removing the temporary files\n* {m!"\n* ".joinSep (filesToRemove.map (m!"{·}")).toList}"
  for tmp in filesToRemove do
    IO.FS.removeFile tmp

end Mathlib.Tactic
