/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Server.InfoUtils
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Batteries.Tactic.Unreachable
public import Lean.Parser.Syntax
public import Mathlib.Tactic.Linter.UnusedTacticExtension

/-!
# The unused tactic linter

The unused linter makes sure that every tactic call actually changes *something*.

The inner workings of the linter are as follows.

The linter inspects the goals before and after each tactic execution.
If they are not identical, the linter is happy.
If they are identical, then the linter checks if the tactic is whitelisted.
Possible reason for whitelisting are
* tactics that emit messages, such as `have?`, `extract_goal`, or `says`;
* tactics that are in place to assert something, such as `guard`;
* tactics that allow to work on a specific goal, such as `on_goal`;
* "flow control" tactics, such as `success_if_fail` and related.

The only tactic that has a bespoke criterion is `swap_var`: the reason is that the only change that
`swap_var` has is to relabel the usernames of local declarations.
Thus, to check that `swap_var` was used, so we inspect the names of all the local declarations
before and after and see if there is some change.

## Notable exclusions

* The linter does not enter a "sequence tactic": upon finding `tac <;> [tac1, tac2, ...]`
  the linter assumes that the tactic is doing something and does not recurse into each
  `tac1, tac2, ...`.
  This is just for lack of an implementation: it may not be hard to do this.

* The tactic does not check the discharger for `linear_combination`,
  but checks `linear_combination` itself.
  The main reason is that `skip` is a common discharger tactic and the linter would
  then always fail whenever the user explicitly chose to pass `skip` as a discharger tactic.

## TODO
* The linter seems to be silenced by `set_option ... in`: maybe it should enter `in`s?

## Implementation notes

Yet another linter copied from the `unreachableTactic` linter!
-/

meta section

open Lean Elab Std Linter

namespace Mathlib.Linter

/-- The unused tactic linter makes sure that every tactic call actually changes *something*. -/
public register_option linter.unusedTactic : Bool := {
  defValue := true
  descr := "enable the unused tactic linter"
}

namespace UnusedTactic

/--
Definition of `M` / `M` 的定义

English:
abbreviation M
  body: StateRefT (Std.HashMap Lean.Syntax.Range Syntax) IO

中文:
缩写 M
  定义体: StateRefT (Std.HashMap Lean.Syntax.Range Syntax) IO

Depends on / 依赖: HashMap, Lean.Syntax.Range, StateRefT, Std.HashMap, Syntax
-/
abbrev M := StateRefT (Std.HashMap Lean.Syntax.Range Syntax) IO

-- Tactics that are expected to not change the state but should also not be flagged by the
-- unused tactic linter.
#allow_unused_tactic!
  Lean.Parser.Term.byTactic
  Lean.Parser.Tactic.tacticSeq
  Lean.Parser.Tactic.tacticSeq1Indented
  Lean.Parser.Tactic.tacticTry_
  -- the following `SyntaxNodeKind`s play a role in silencing `test`s
  Lean.Parser.Tactic.guardHyp
  Lean.Parser.Tactic.guardHypConv
  Lean.Parser.Tactic.guardTarget
  Lean.Parser.Tactic.guardTargetConv
  Lean.Parser.Tactic.failIfSuccess

/--
A list of blocklisted syntax kinds, which are expected to have subterms that contain
unused tactics.
-/
initialize ignoreTacticKindsRef : IO.Ref NameHashSet ←
IO.mkRef .ofArray #[
    `Mathlib.Tactic.Says.says,
    ``Parser.Term.binderTactic,
    ``Lean.Parser.Term.dynamicQuot,
    ``Lean.Parser.Tactic.quotSeq,
    ``Lean.Parser.Tactic.tacticStop_,
    ``Lean.Parser.Command.notation,
    ``Lean.Parser.Command.mixfix,
    ``Lean.Parser.Tactic.discharger,
    ``Lean.Parser.Command.registerTryTactic,
    `Batteries.Tactic.seq_focus,
    `Mathlib.Tactic.Hint.registerHintStx,
    `Mathlib.Tactic.LinearCombination.linearCombination,
    `Mathlib.Tactic.LinearCombinationPrime.linearCombination',
    `Aesop.Frontend.Parser.addRules,
    `Aesop.Frontend.Parser.aesopTactic,
    `Aesop.Frontend.Parser.aesopTactic?,
    ``Mathlib.Linter.UnusedTactic.«command#show_kind_»,
    -- the following `SyntaxNodeKind`s play a role in silencing `test`s
    ``Lean.Parser.Tactic.failIfSuccess,
    `Mathlib.Tactic.successIfFailWithMsg,
    `Mathlib.Tactic.failIfNoProgress
  ]

/--
Definition of `isIgnoreTacticKind` / `isIgnoreTacticKind` 的定义

English:
definition isIgnoreTacticKind
  signature: (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind)
  body: k matches .str _ "quot" ||
  ignoreTacticKinds.contains k

中文:
定义 isIgnoreTacticKind
  签名: (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind)
  定义体: k matches .str _ "quot" ||
  ignoreTacticKinds.contains k

Depends on / 依赖: contains, ignoreTacticKinds, ignoreTacticKinds.contains, matches
-/
def isIgnoreTacticKind (ignoreTacticKinds : NameHashSet) (k : SyntaxNodeKind) : Bool :=
  k matches .str _ "quot" ||
  ignoreTacticKinds.contains k

/--
Definition of `addIgnoreTacticKind` / `addIgnoreTacticKind` 的定义

English:
definition addIgnoreTacticKind
  signature: (kind : SyntaxNodeKind)
  body: ignoreTacticKindsRef.modify (·.insert kind)

中文:
定义 addIgnoreTacticKind
  签名: (kind : SyntaxNodeKind)
  定义体: ignoreTacticKindsRef.modify (·.insert kind)

Depends on / 依赖: ignoreTacticKindsRef, ignoreTacticKindsRef.modify, insert, modify
-/
def addIgnoreTacticKind (kind : SyntaxNodeKind) : IO Unit :=
  ignoreTacticKindsRef.modify (·.insert kind)

/--
Definition of `getTactics` / `getTactics` 的定义

English:
definition getTactics
  signature: (ignoreTacticKinds : NameHashSet)
  body: do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM (getTactics ignoreTacticKinds isTacKind)
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx

中文:
定义 getTactics
  签名: (ignoreTacticKinds : NameHashSet)
  定义体: do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM (getTactics ignoreTacticKinds isTacKind)
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx
-/
@[specialize] partial def getTactics (ignoreTacticKinds : NameHashSet)
    (isTacKind : SyntaxNodeKind -> Bool) (stx : Syntax) : M Unit := do
  if let .node _ k args := stx then
    if !isIgnoreTacticKind ignoreTacticKinds k then
      args.forM (getTactics ignoreTacticKinds isTacKind)
    if isTacKind k then
      if let some r := stx.getRange? true then
        modify fun m => m.insert r stx

/--
Definition of `getNames` / `getNames` 的定义

English:
definition getNames
  signature: (mctx : MetavarContext)
  body: let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName

中文:
定义 getNames
  签名: (mctx : MetavarContext)
  定义体: let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName

Depends on / 依赖: LocalContext, LocalContext.decls, LocalDecl, LocalDecl.userName, MetavarDecl, MetavarDecl.lctx, PersistentArray, PersistentArray.toList, Prod.snd, flatten, flatten.reduceOption, lcts.map, locDecls, locDecls.map, mctx.decls.toList.map, reduceOption, toList, userName
-/
def getNames (mctx : MetavarContext) : List Name :=
  let lcts := mctx.decls.toList.map (MetavarDecl.lctx ∘ Prod.snd)
  let locDecls := (lcts.map (PersistentArray.toList ∘ LocalContext.decls)).flatten.reduceOption
  locDecls.map LocalDecl.userName

/--
Definition of `eraseUsedTactics` / `eraseUsedTactics` 的定义

English:
definition eraseUsedTactics
  signature: (exceptions : Std.HashSet SyntaxNodeKind)
  body: let ranges := trees.foldl (init := #[]) InfoTree.foldInfo fun _ i ranges => Id.run do
    let .ofTacticInfo i := i | return ranges
    let stx := i.stx
    let some r := stx.getRange? true | return ranges
    let kind := stx.getKind
    -- if the tactic is allowed to not change the goals
    if exceptions.contains kind then
      return ranges.push r
    -- if the goals have changed
    if i.goalsAfter != i.goalsBefore then
      return ranges.push r
    -- bespoke check for `swap_var`: the only change that it does is
    -- in the usernames of local declarations, so we check the names before and after
    if (kind == `Mathlib.Tactic.«tacticSwap_var__,,») &&
            (getNames i.mctxBefore != getNames i.mctxAfter) then
      return ranges.push r
    return ranges
  for r in ranges do
    modify (·.erase r)

中文:
定义 eraseUsedTactics
  签名: (exceptions : Std.HashSet SyntaxNodeKind)
  定义体: let ranges := trees.foldl (init := #[]) InfoTree.foldInfo fun _ i ranges => Id.run do
    let .ofTacticInfo i := i | return ranges
    let stx := i.stx
    let some r := stx.getRange? true | return ranges
    let kind := stx.getKind
    -- if the tactic is allowed to not change the goals
    if exceptions.contains kind then
      return ranges.push r
    -- if the goals have changed
    if i.goalsAfter != i.goalsBefore then
      return ranges.push r
    -- bespoke check for `swap_var`: the only change that it does is
    -- in the usernames of local declarations, so we check the names before and after
    if (kind == `Mathlib.Tactic.«tacticSwap_var__,,») &&
            (getNames i.mctxBefore != getNames i.mctxAfter) then
      return ranges.push r
    return ranges
  for r in ranges do
    modify (·.erase r)
-/
partial def eraseUsedTactics (exceptions : Std.HashSet SyntaxNodeKind)
    (trees : PersistentArray InfoTree) : M Unit :=
let ranges := trees.foldl (init := #[]) InfoTree.foldInfo fun _ i ranges => Id.run do
    let .ofTacticInfo i := i | return ranges
    let stx := i.stx
    let some r := stx.getRange? true | return ranges
    let kind := stx.getKind
    -- if the tactic is allowed to not change the goals
    if exceptions.contains kind then
      return ranges.push r
    -- if the goals have changed
    if i.goalsAfter != i.goalsBefore then
      return ranges.push r
    -- bespoke check for `swap_var`: the only change that it does is
    -- in the usernames of local declarations, so we check the names before and after
    if (kind == `Mathlib.Tactic.«tacticSwap_var__,,») &&
            (getNames i.mctxBefore != getNames i.mctxAfter) then
      return ranges.push r
    return ranges
  for r in ranges do
    modify (·.erase r)

/--
Definition of `unusedTacticLinter` / `unusedTacticLinter` 的定义

English:
definition unusedTacticLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless getLinterValue linter.unusedTactic (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
let some tactics := Parser.ParserCategory.kinds < > cats.find? `tactic
    | return
let some convs := Parser.ParserCategory.kinds < > cats.find? `conv
    | return
  let trees ← getInfoTrees
let exceptions := (← allowedRef.get).union allowedUnusedTacticExt.getState env
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTactics exceptions trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind in [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start <= r.start && r.stop <= last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"Unused tactic linter: `{stx}` does nothing"
    last := r

中文:
定义 unusedTacticLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless getLinterValue linter.unusedTactic (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
let some tactics := Parser.ParserCategory.kinds < > cats.find? `tactic
    | return
let some convs := Parser.ParserCategory.kinds < > cats.find? `conv
    | return
  let trees ← getInfoTrees
let exceptions := (← allowedRef.get).union allowedUnusedTacticExt.getState env
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTactics exceptions trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind in [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start <= r.start && r.stop <= last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"Unused tactic linter: `{stx}` does nothing"
    last := r

Depends on / 依赖: withSetOptionIn
-/
def unusedTacticLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.unusedTactic (← getLinterOptions) && (← getInfoState).enabled do
    return
  if (← get).messages.hasErrors then
    return
  let env ← getEnv
  let cats := (Parser.parserExtension.getState env).categories
  -- These lookups may fail when the linter is run in a fresh, empty environment
let some tactics := Parser.ParserCategory.kinds < > cats.find? `tactic
    | return
let some convs := Parser.ParserCategory.kinds < > cats.find? `conv
    | return
  let trees ← getInfoTrees
let exceptions := (← allowedRef.get).union allowedUnusedTacticExt.getState env
  let go : M Unit := do
    getTactics (← ignoreTacticKindsRef.get) (fun k => tactics.contains k || convs.contains k) stx
    eraseUsedTactics exceptions trees
  let (_, map) ← go.run {}
  let unused := map.toArray
  let key (r : Lean.Syntax.Range) := (r.start.byteIdx, (-r.stop.byteIdx : Int))
  let mut last : Lean.Syntax.Range := ⟨0, 0⟩
  for (r, stx) in let _ := @lexOrd; let _ := @ltOfOrd.{0}; unused.qsort (key ·.1 < key ·.1) do
    if stx.getKind in [``Batteries.Tactic.unreachable, ``Batteries.Tactic.unreachableConv] then
      continue
    if last.start <= r.start && r.stop <= last.stop then continue
    Linter.logLint linter.unusedTactic stx m!"Unused tactic linter: `{stx}` does nothing"
    last := r

initialize addLinter unusedTacticLinter
