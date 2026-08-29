/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Edward van de Meent
-/
module

public meta import Mathlib.Tactic.TacticAnalysis
public meta import Lean.Elab.Command
public meta import Mathlib.Lean.Elab.InfoTree
public meta import Lean.Meta.Tactic.TryThis
public import Mathlib.Tactic.ExtractGoal
public import Mathlib.Tactic.TacticAnalysis
public import Mathlib.Util.ParseCommand

/-!
# Tactic linters

This file defines passes to run from the tactic analysis framework.
-/

public meta section

open Lean Meta

namespace Mathlib.TacticAnalysis

/--
Inductive type `TerminalReplacementOutcome` / 归纳类型 `TerminalReplacementOutcome`

English:
inductive TerminalReplacementOutcome
  parameters: where
  constructors (3):
    - success: (stx : TSyntax `tactic)
    - remainingGoals: (stx : TSyntax `tactic) (goals : List MessageData)
    - error: (stx : TSyntax `tactic) (msg : MessageData)

中文:
归纳类型 TerminalReplacementOutcome
  参数: where
  构造子 (3 个):
    - success: (stx : TSyntax `tactic)
    - remainingGoals: (stx : TSyntax `tactic) (goals : List MessageData)
    - error: (stx : TSyntax `tactic) (msg : MessageData)
-/
private inductive TerminalReplacementOutcome where
| success (stx : TSyntax `tactic)
| remainingGoals (stx : TSyntax `tactic) (goals : List MessageData)
| error (stx : TSyntax `tactic) (msg : MessageData)

open Elab Command

/--
Definition of `terminalReplacement` / `terminalReplacement` 的定义

English:
definition terminalReplacement
  signature: (oldTacticName newTacticName : String) (oldTacticKind : SyntaxNodeKind)
  body: .ofComplex {
  out := TerminalReplacementOutcome
  ctx := Syntax
  trigger _ stx := if stx.getKind == oldTacticKind
    then .accept stx else .skip
  test ctxI i stx goal := do
    let tac ← newTactic ctxI i stx
    try
      let goalTypes ← ctxI.runTacticCode i goal tac ⟨Expr, MVarId.getType'⟩
    

中文:
定义 terminalReplacement
  签名: (oldTacticName newTacticName : String) (oldTacticKind : SyntaxNodeKind)
  定义体: .ofComplex {
  out := TerminalReplacementOutcome
  ctx := Syntax
  trigger _ stx := if stx.getKind == oldTacticKind
    then .accept stx else .skip
  test ctxI i stx goal := do
    let tac ← newTactic ctxI i stx
    try
      let goalTypes ← ctxI.runTacticCode i goal tac ⟨Expr, MVarId.getType'⟩
    

Depends on / 依赖: reportSuccess
-/
def terminalReplacement (oldTacticName newTacticName : String) (oldTacticKind : SyntaxNodeKind)
    (newTactic : ContextInfo -> TacticInfo -> Syntax -> CommandElabM (TSyntax `tactic))
    (reportFailure : Bool := true) (reportSuccess : Bool := false)
    (reportSlowdown : Bool := false) (maxSlowdown : Float := 1) :
    TacticAnalysis.Config := .ofComplex {
  out := TerminalReplacementOutcome
  ctx := Syntax
  trigger _ stx := if stx.getKind == oldTacticKind
    then .accept stx else .skip
  test ctxI i stx goal := do
    let tac ← newTactic ctxI i stx
    try
      let goalTypes ← ctxI.runTacticCode i goal tac ⟨Expr, MVarId.getType'⟩
      match goalTypes with
      | [] => return .success tac
      | _ => do
        let goalsMessages := goalTypes.map fun e => m!"⊢ {MessageData.ofExpr e}\n"
        return .remainingGoals tac goalsMessages
    catch _e =>
      let name ← mkAuxDeclName `extracted
      -- Rerun in the original tactic context, since `omega` changes the state.
      let ((sig, _, modules, _), _) ← ctxI.runTactic i goal (fun goal =>
        (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run)
      let imports := modules.toList.map (s!"import {·}")
      return .error tac m!"{"\n".intercalate imports}\n\ntheorem {sig} := by\n fail_if_success {tac}\n {stx}"
  tell stx old oldHeartbeats new newHeartbeats :=
    -- If the original tactic failed, then we do not need to check the replacement.
    if !old.isEmpty then
      return none
    else match new with
    | .error _ msg =>
      if reportFailure then
        let msg :=
          m!"`{newTacticName}` failed where `{oldTacticName}` succeeded.\n" ++
          m!"Original tactic:{indentD stx}\n" ++
          m!"Counterexample:{indentD msg}"
        return msg
      else
        return none
    | .remainingGoals newStx goals =>
      if reportFailure then
        let msg :=
          m!"`{newTacticName}` left unsolved goals where `{oldTacticName}` succeeded.\n" ++
          m!"Original tactic:{indentD stx}\n" ++
          m!"Replacement tactic:{indentD newStx}\n" ++
          m!"Unsolved goals:{indentD goals}"
        return msg
      else
        return none
    | .success newStx => do
      -- TODO: we should add a "Try this:" suggestion with code action.
      let msg := if (← liftCoreM <| PrettyPrinter.ppTactic newStx).pretty = newTacticName then
        m!"`{newTacticName}` can replace `{stx}`"
      else
        m!"`{newTacticName}` can replace `{stx}` using `{newStx}`"
      if reportSlowdown ∧ maxSlowdown * oldHeartbeats.toFloat < newHeartbeats.toFloat then
        return some m!"{msg}, but is slower: {newHeartbeats / 1000} versus {oldHeartbeats / 1000} heartbeats"
      else if reportSuccess then
        return some msg
      else
        return none
    }


/--
Definition of `termToGrindParam` / `termToGrindParam` 的定义

English:
definition termToGrindParam
  signature: (t : Syntax)
  body: -- grindLemma := ppGroup((Attr.grindMod ppSpace)? term)
  -- grindParam := grindErase <|> grindLemmaMin <|> grindLemma <|> anchor
  -- With no modifier, the first child is a null node
  -- If t is a simple identifier, wrap as `(id t)` to force term interpretation
  let t' : Syntax := if t.isIdent th

中文:
定义 termToGrindParam
  签名: (t : Syntax)
  定义体: -- grindLemma := ppGroup((Attr.grindMod ppSpace)? term)
  -- grindParam := grindErase <|> grindLemmaMin <|> grindLemma <|> anchor
  -- With no modifier, the first child is a null node
  -- If t is a simple identifier, wrap as `(id t)` to force term interpretation
  let t' : Syntax := if t.isIdent th

Depends on / 依赖: Limits, Limits.isTerminalTop, homOfLE, isTerminalTop, le_top, subsingleton_fiber_obj
-/
private def termToGrindParam (t : Syntax) : Syntax :=
  -- grindLemma := ppGroup((Attr.grindMod ppSpace)? term)
  -- grindParam := grindErase <|> grindLemmaMin <|> grindLemma <|> anchor
  -- With no modifier, the first child is a null node
  -- If t is a simple identifier, wrap as `(id t)` to force term interpretation
  let t' : Syntax := if t.isIdent then
      -- Create `id t` application - this ensures grind sees it as a term, not an e-match candidate
      mkNode ``Lean.Parser.Term.app #[mkIdent `id, mkNullNode #[t]]
    else t
  let grindLemma := mkNode ``Lean.Parser.Tactic.grindLemma #[mkNullNode, t']
  mkNode ``Lean.Parser.Tactic.grindParam #[grindLemma]

/--
Definition of `grindReplacementWith` / `grindReplacementWith` 的定义

English:
definition grindReplacementWith
  signature: (tacticName : String) (tacticKind : SyntaxNodeKind)
  body: let newTactic : ContextInfo -> TacticInfo -> Syntax -> CommandElabM (TSyntax `tactic) :=
    fun _ctxI tacI stx => do
      match extractArgs stx with
      | some args =>
        if args.getElems.isEmpty then
          return ← `(tactic| grind)
        -- Get local hypothesis names from the goal's 

中文:
定义 grindReplacementWith
  签名: (tacticName : String) (tacticKind : SyntaxNodeKind)
  定义体: let newTactic : ContextInfo -> TacticInfo -> Syntax -> CommandElabM (TSyntax `tactic) :=
    fun _ctxI tacI stx => do
      match extractArgs stx with
      | some args =>
        if args.getElems.isEmpty then
          return ← `(tactic| grind)
        -- Get local hypothesis names from the goal's 
-/
def grindReplacementWith (tacticName : String) (tacticKind : SyntaxNodeKind)
    (extractArgs : Syntax -> Option (Syntax.TSepArray `term ",") := fun _ => none)
    (reportFailure : Bool := true) (reportSuccess : Bool := false)
    (reportSlowdown : Bool := false) (maxSlowdown : Float := 1) :
    TacticAnalysis.Config :=
  let newTactic : ContextInfo -> TacticInfo -> Syntax -> CommandElabM (TSyntax `tactic) :=
    fun _ctxI tacI stx => do
      match extractArgs stx with
      | some args =>
        if args.getElems.isEmpty then
          return ← `(tactic| grind)
        -- Get local hypothesis names from the goal's local context
        let lctxNames : Std.HashSet Name :=
          match tacI.goalsBefore.head? with
          | some goal =>
            let goalDecl := tacI.mctxBefore.decls.find! goal
            goalDecl.lctx.foldl (init := {}) fun s decl =>
              if decl.isImplementationDetail then s else s.insert decl.userName
          | none => {}
        -- Filter out terms that are simple identifiers matching local hypotheses
        let filteredElems := args.getElems.filter fun term =>
          match term.raw with
          | .ident _ _ name _ => !lctxNames.contains name
          | _ => true -- Keep non-identifier terms (like `foo.bar x`)
        if filteredElems.isEmpty then
          return ← `(tactic| grind)
        -- Build comma-separated list from filtered elements
        let grindElemsAndSeps := filteredElems.foldl (init := #[]) fun acc elem =>
          if acc.isEmpty then #[termToGrindParam elem]
.push (termToGrindParam elem) else acc.push (mkAtom ",")
        let grindArgs : Syntax.TSepArray ``Lean.Parser.Tactic.grindParam "," :=
          ⟨grindElemsAndSeps⟩
        `(tactic| grind [$grindArgs,*])
      | none => `(tactic| grind)
  terminalReplacement tacticName "grind" tacticKind newTactic
    reportFailure reportSuccess reportSlowdown maxSlowdown

end Mathlib.TacticAnalysis

open Mathlib TacticAnalysis

/-- Debug `grind` by identifying places where it does not yet supersede `linarith`. -/
register_option linter.tacticAnalysis.regressions.linarithToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.linarithToGrind,
  inherit_doc linter.tacticAnalysis.regressions.linarithToGrind]
/--
Definition of `linarithToGrindRegressions` / `linarithToGrindRegressions` 的定义

English:
definition linarithToGrindRegressions
  body: grindReplacementWith "linarith" `Mathlib.Tactic.linarith
    (extractArgs := fun stx => do
      -- linarith syntax: "linarith" "!"? linarithArgsRest
      -- linarithArgsRest := optConfig (&" only")? (" [" term,* "]")?
      let rest := stx[2] -- linarithArgsRest
      let argsGroup := rest[2] -- t

中文:
定义 linarithToGrindRegressions
  定义体: grindReplacementWith "linarith" `Mathlib.Tactic.linarith
    (extractArgs := fun stx => do
      -- linarith syntax: "linarith" "!"? linarithArgsRest
      -- linarithArgsRest := optConfig (&" only")? (" [" term,* "]")?
      let rest := stx[2] -- linarithArgsRest
      let argsGroup := rest[2] -- t

Depends on / 依赖: Mathlib, Mathlib.Tactic.linarith, Tactic, grindReplacementWith
-/
def linarithToGrindRegressions := grindReplacementWith "linarith" `Mathlib.Tactic.linarith
    (extractArgs := fun stx => do
      -- linarith syntax: "linarith" "!"? linarithArgsRest
      -- linarithArgsRest := optConfig (&" only")? (" [" term,* "]")?
      let rest := stx[2] -- linarithArgsRest
      let argsGroup := rest[2] -- the optional bracket group
      guard (argsGroup.getNumArgs >= 2)
      return ⟨argsGroup[1].getArgs⟩)

/-- Debug `grind` by identifying places where it does not yet supersede `ring`. -/
register_option linter.tacticAnalysis.regressions.ringToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.ringToGrind,
  inherit_doc linter.tacticAnalysis.regressions.ringToGrind]
/--
Definition of `ringToGrindRegressions` / `ringToGrindRegressions` 的定义

English:
definition ringToGrindRegressions
  body: grindReplacementWith "ring" `Mathlib.Tactic.RingNF.ring

中文:
定义 ringToGrindRegressions
  定义体: grindReplacementWith "ring" `Mathlib.Tactic.RingNF.ring

Depends on / 依赖: Mathlib, Mathlib.Tactic.RingNF.ring, RingNF, Tactic, grindReplacementWith
-/
def ringToGrindRegressions := grindReplacementWith "ring" `Mathlib.Tactic.RingNF.ring

/-- Debug `lia` by identifying places where it does not yet supersede `omega`. -/
register_option linter.tacticAnalysis.regressions.omegaToLia : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.omegaToLia,
  inherit_doc linter.tacticAnalysis.regressions.omegaToLia]
/--
Definition of `omegaToLiaRegressions` / `omegaToLiaRegressions` 的定义

English:
definition omegaToLiaRegressions
  body: terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := false) (reportFailure := true)

中文:
定义 omegaToLiaRegressions
  定义体: terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := false) (reportFailure := true)

Depends on / 依赖: Category, Lean.Parser.Tactic.omega, Parser, Tactic, reportFailure, reportSuccess, tactic, terminalReplacement
-/
def omegaToLiaRegressions :=
  terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := false) (reportFailure := true)

/-- Report places where `omega` can be replaced by `lia`. -/
register_option linter.tacticAnalysis.omegaToLia : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.omegaToLia,
  inherit_doc linter.tacticAnalysis.omegaToLia]
/--
Definition of `omegaToLia` / `omegaToLia` 的定义

English:
definition omegaToLia
  body: terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := true) (reportFailure := false)

中文:
定义 omegaToLia
  定义体: terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := true) (reportFailure := false)

Depends on / 依赖: Lean.Parser.Tactic.omega, Parser, Tactic, reportFailure, reportSuccess, tactic, terminalReplacement
-/
def omegaToLia :=
  terminalReplacement "omega" "lia" ``Lean.Parser.Tactic.omega (fun _ _ _ => `(tactic| lia))
    (reportSuccess := true) (reportFailure := false)

/-- Suggest merging two adjacent `rw` tactics if that also solves the goal. -/
register_option linter.tacticAnalysis.rwMerge : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.rwMerge, inherit_doc linter.tacticAnalysis.rwMerge]
/--
Definition of `Mathlib.TacticAnalysis.rwMerge` / `Mathlib.TacticAnalysis.rwMerge` 的定义

English:
definition Mathlib.TacticAnalysis.rwMerge
  signature: : TacticAnalysis.Config
  body: .ofComplex {
  out := (List MVarId × Array Syntax)
  ctx := (Array (Array Syntax))
  trigger ctx stx :=
    match stx with
    | `(tactic| rw [$args,*]) => .continue ((ctx.getD #[]).push args)
    | _ => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctx

中文:
定义 Mathlib.TacticAnalysis.rwMerge
  签名: : TacticAnalysis.Config
  定义体: .ofComplex {
  out := (List MVarId × Array Syntax)
  ctx := (Array (Array Syntax))
  trigger ctx stx :=
    match stx with
    | `(tactic| rw [$args,*]) => .continue ((ctx.getD #[]).push args)
    | _ => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctx

Depends on / 依赖: ofComplex
-/
def Mathlib.TacticAnalysis.rwMerge : TacticAnalysis.Config := .ofComplex {
  out := (List MVarId × Array Syntax)
  ctx := (Array (Array Syntax))
  trigger ctx stx :=
    match stx with
    | `(tactic| rw [$args,*]) => .continue ((ctx.getD #[]).push args)
    | _ => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctxI i ctx goal := do
    let ctxT : Array (TSyntax `Lean.Parser.Tactic.rwRule) := ctx.flatten.map (⟨·⟩)
    let tac ← `(tactic| rw [$ctxT,*])
    let oldMessages := (← get).messages
    try
      let goals ← ctxI.runTacticCode i goal tac
      return (goals, ctxT.map (↑·))
    catch _e => -- rw throws an error if it fails to pattern-match.
      return ([goal], ctxT.map (↑·))
    finally
      -- Drop any messages, since they will appear as if they are genuine errors.
      modify fun s => { s with messages := oldMessages }
tell _stx _old _oldHeartbeats new _newHeartbeats := pure
    if new.1.isEmpty then
      m!"Try this: rw {new.2}"
    else none }

/-- Suggest merging `tac; grind` into just `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.mergeWithGrind : Bool := {
  defValue := false
}

/--
Definition of `mergeWithGrindAllowed` / `mergeWithGrindAllowed` 的定义

English:
abbreviation mergeWithGrindAllowed
  signature: : Std.HashSet Name
  body: { `«tactic#adaptation_note_» }

@[tacticAnalysis linter.tacticAnalysis.mergeWithGrind,
  inherit_doc linter.tacticAnalysis.mergeWithGrind]

中文:
缩写 mergeWithGrindAllowed
  签名: : Std.HashSet Name
  定义体: { `«tactic#adaptation_note_» }

@[tacticAnalysis linter.tacticAnalysis.mergeWithGrind,
  inherit_doc linter.tacticAnalysis.mergeWithGrind]
-/
private abbrev mergeWithGrindAllowed : Std.HashSet Name := { `«tactic#adaptation_note_» }

@[tacticAnalysis linter.tacticAnalysis.mergeWithGrind,
  inherit_doc linter.tacticAnalysis.mergeWithGrind]
/--
Definition of `Mathlib.TacticAnalysis.mergeWithGrind` / `Mathlib.TacticAnalysis.mergeWithGrind` 的定义

English:
definition Mathlib.TacticAnalysis.mergeWithGrind
  signature: : TacticAnalysis.Config where
  body: do
    if let #[preI, postI] := seq[seq.size - 2:].toArray then
      if postI.tacI.stx.getKind == ``Lean.Parser.Tactic.grind &&
          preI.tacI.stx.getKind ∉ mergeWithGrindAllowed then
        if let [goal] := preI.tacI.goalsBefore then
          let goals ← try
            preI.runTacticCode g

中文:
定义 Mathlib.TacticAnalysis.mergeWithGrind
  签名: : TacticAnalysis.Config where
  定义体: do
    if let #[preI, postI] := seq[seq.size - 2:].toArray then
      if postI.tacI.stx.getKind == ``Lean.Parser.Tactic.grind &&
          preI.tacI.stx.getKind ∉ mergeWithGrindAllowed then
        if let [goal] := preI.tacI.goalsBefore then
          let goals ← try
            preI.runTacticCode g
-/
def Mathlib.TacticAnalysis.mergeWithGrind : TacticAnalysis.Config where
  run seq := do
    if let #[preI, postI] := seq[seq.size - 2:].toArray then
      if postI.tacI.stx.getKind == ``Lean.Parser.Tactic.grind &&
          preI.tacI.stx.getKind ∉ mergeWithGrindAllowed then
        if let [goal] := preI.tacI.goalsBefore then
          let goals ← try
            preI.runTacticCode goal postI.tacI.stx
          catch _e =>
            pure [goal]
          if goals.isEmpty then
            let msg ← addMessageContext m!"'{preI.tacI.stx}; grind' can be replaced with 'grind'"
            let header := (← msg.toString) ++ "\n\nTry this:"
            if let some start := preI.tacI.stx.getPos? then
            if let some stop := postI.tacI.stx.getTailPos? then
            let synth := Lean.Syntax.setInfo (Lean.SourceInfo.synthetic start stop) preI.tacI.stx
Elab.Command.liftCoreM
              Tactic.TryThis.addSuggestion (header := header) synth (← `(tactic | grind))

/-- Suggest replacing a sequence of tactics with `grind` if that also solves the goal. -/
register_option linter.tacticAnalysis.terminalToGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.terminalToGrind,
  inherit_doc linter.tacticAnalysis.terminalToGrind]
/--
Definition of `Mathlib.TacticAnalysis.terminalToGrind` / `Mathlib.TacticAnalysis.terminalToGrind` 的定义

English:
definition Mathlib.TacticAnalysis.terminalToGrind
  signature: : TacticAnalysis.Config where
  body: do
    let threshold := 3
    -- `replaced` will hold the terminal tactic sequence that can be replaced with `grind`.
    -- We prepend each tactic in turn, starting with the last.
    let mut replaced : List (TSyntax `tactic) := []
    let mut success := false
    let mut oldHeartbeats := 0
    let

中文:
定义 Mathlib.TacticAnalysis.terminalToGrind
  签名: : TacticAnalysis.Config where
  定义体: do
    let threshold := 3
    -- `replaced` will hold the terminal tactic sequence that can be replaced with `grind`.
    -- We prepend each tactic in turn, starting with the last.
    let mut replaced : List (TSyntax `tactic) := []
    let mut success := false
    let mut oldHeartbeats := 0
    let
-/
def Mathlib.TacticAnalysis.terminalToGrind : TacticAnalysis.Config where
  run seq := do
    let threshold := 3
    -- `replaced` will hold the terminal tactic sequence that can be replaced with `grind`.
    -- We prepend each tactic in turn, starting with the last.
    let mut replaced : List (TSyntax `tactic) := []
    let mut success := false
    let mut oldHeartbeats := 0
    let mut newHeartbeats := 0
    -- We iterate through the tactic sequence in reverse, checking at each tactic if the goal is
    -- already solved by `grind` and if so pushing that tactic onto `replaced`.
    -- By repeating this until `grind` fails for the first time, we get a terminal sequence
    -- of replaceable tactics.
    for i in seq.reverse do
      if replaced.length >= threshold - 1 && i.tacI.stx.getKind != ``Lean.Parser.Tactic.grind then
        if let [goal] := i.tacI.goalsBefore then
          -- Count the heartbeats of the original tactic sequence, verifying that this indeed
          -- closes the goal like it does in userspace.
          let suffix := ⟨i.tacI.stx⟩ :: replaced
          let seq ← `(tactic| $suffix.toArray;*)
let (oldGoals, heartbeats) ← withHeartbeats
            try
              i.runTacticCode goal seq
            catch _e =>
              pure [goal]
          if !oldGoals.isEmpty then
            logWarningAt i.tacI.stx m!"Original tactics failed to solve the goal: {seq}"
          oldHeartbeats := heartbeats

          -- To check if `grind` can close the goal, run `grind` on the current goal
          -- and verify that no goals remain afterwards.
          let tac ← `(tactic| grind)
let (newGoals, heartbeats) ← withHeartbeats
            try
              i.runTacticCode goal tac
            catch _e =>
              pure [goal]
          newHeartbeats := heartbeats
          if newGoals.isEmpty then
            success := true
          else
            break
        else
          break
      replaced := ⟨i.tacI.stx⟩ :: replaced

    if h : replaced.length >= threshold ∧ success then
      let stx := replaced[0]
      let seq ← `(tactic| $replaced.toArray;*)
      logWarningAt stx m!"replace the proof with 'grind': {seq}"
      if oldHeartbeats * 2 < newHeartbeats then
        logWarningAt stx m!"'grind' is slower than the original: {oldHeartbeats} -> {newHeartbeats}"

open Elab.Command

/--
When running the "tryAtEachStep" tactic analysis linters,
only run on a fraction `1/n` of the goals found in the library.

This is useful for running quick benchmarks.
-/
register_option linter.tacticAnalysis.tryAtEachStep.fraction : Nat := {
  defValue := 1
}

/--
Whether to show timing information in "tryAtEachStep" tactic analysis output.

When true (default), messages include elapsed time like `(23ms)`.
Set to false in tests to avoid non-deterministic output.
-/
register_option linter.tacticAnalysis.tryAtEachStep.showTiming : Bool := {
  defValue := true
}

/--
Whether to report when a tactic can be replaced with itself.

When true (default), all successful replacements are reported, including when
the suggested tactic matches the existing proof.
When false, self-replacements are suppressed.
-/
register_option linter.tacticAnalysis.tryAtEachStep.selfReplacements : Bool := {
  defValue := true
}

/--
Definition of `Mathlib.TacticAnalysis.tryAtEachStepCore` / `Mathlib.TacticAnalysis.tryAtEachStepCore` 的定义

English:
definition Mathlib.TacticAnalysis.tryAtEachStepCore
  body: do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    let showTiming := linter.tacticAnalysis.tryAtEachStep.showTiming.get opts
    let selfReplacements := linter.tacticAnalysis.tryAtEachStep.selfReplacements.get opts
    for h : idx in [:seq.size

中文:
定义 Mathlib.TacticAnalysis.tryAtEachStepCore
  定义体: do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    let showTiming := linter.tacticAnalysis.tryAtEachStep.showTiming.get opts
    let selfReplacements := linter.tacticAnalysis.tryAtEachStep.selfReplacements.get opts
    for h : idx in [:seq.size

Depends on / 依赖: Config, TacticAnalysis, TacticAnalysis.Config
-/
def Mathlib.TacticAnalysis.tryAtEachStepCore
    (tac : Syntax -> MVarId -> CommandElabM (TSyntax `tactic))
    (label : Option String := none) : TacticAnalysis.Config where
  run seq := do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    let showTiming := linter.tacticAnalysis.tryAtEachStep.showTiming.get opts
    let selfReplacements := linter.tacticAnalysis.tryAtEachStep.selfReplacements.get opts
    for h : idx in [:seq.size] do
      let i := seq[idx]
      if let [goal] := i.tacI.goalsBefore then
        -- Hash the pretty-printed goal for stability across runs
        let goalDecl := i.tacI.mctxBefore.decls.find! goal
        let goalPP ← i.ctxI.runMetaM goalDecl.lctx do
          withOptions (·.setBool `pp.mvars false) do
            return toString (← Meta.ppGoal goal)
        if (hash goalPP) % fraction = 0 then
          let tac ← tac i.tacI.stx goal
          let startTime ← IO.monoMsNow
          let goalsAfter ← try
            i.runTacticCode goal tac
          catch _e =>
            pure [goal]
          let elapsedMs := (← IO.monoMsNow) - startTime
          if goalsAfter.isEmpty then
            -- Extract just the tactic name, ignoring trailing comments/whitespace
            -- Use try/catch because ppTactic can fail on certain syntax (e.g., `congr($h x)`)
            let oldTacticPP := (← try
              pure (((← liftCoreM <| PrettyPrinter.ppTactic ⟨i.tacI.stx⟩).pretty.splitOn "\n")[0]!.trimAscii)
            catch _ =>
              pure (i.tacI.stx.reprint.getD "???"))
            let newTacticPP ← label.getDM (try
              return ((← liftCoreM <| PrettyPrinter.ppTactic tac).pretty.splitOn "\n")[0]!.trimAscii.copy
            catch _ =>
              return tac.raw.reprint.getD "???")
            -- Check if this is a self-replacement (tactic replacing itself)
            if !selfReplacements && oldTacticPP == newTacticPP then
              continue
            let laterSteps := seq.size - 1 - idx
            let laterMsg := if laterSteps > 0 then s!" (+{laterSteps} later steps)" else ""
            if showTiming then
              logInfoAt i.tacI.stx m!"`{oldTacticPP}`{laterMsg} can be replaced with `{newTacticPP}` ({elapsedMs}ms)"
            else
              logInfoAt i.tacI.stx m!"`{oldTacticPP}`{laterMsg} can be replaced with `{newTacticPP}`"

/--
Definition of `Mathlib.TacticAnalysis.tryAtEachStep` / `Mathlib.TacticAnalysis.tryAtEachStep` 的定义

English:
definition Mathlib.TacticAnalysis.tryAtEachStep
  body: tryAtEachStepCore tac

中文:
定义 Mathlib.TacticAnalysis.tryAtEachStep
  定义体: tryAtEachStepCore tac

Depends on / 依赖: tryAtEachStepCore
-/
def Mathlib.TacticAnalysis.tryAtEachStep
    (tac : Syntax -> MVarId -> CommandElabM (TSyntax `tactic)) : TacticAnalysis.Config :=
  tryAtEachStepCore tac

/--
Definition of `Mathlib.TacticAnalysis.tryAtEachStepFromStrings` / `Mathlib.TacticAnalysis.tryAtEachStepFromStrings` 的定义

English:
definition Mathlib.TacticAnalysis.tryAtEachStepFromStrings
  body: do
    -- Parse using `tacticSeq.fn` directly since `tacticSeq` is not a parser category.
    -- See https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/piggy.20back.20off.20of.20the.20lean4.20parser
    let tacSeq ← try
ofExcept
        Mathlib.GuardExceptions.captureException (← 

中文:
定义 Mathlib.TacticAnalysis.tryAtEachStepFromStrings
  定义体: do
    -- Parse using `tacticSeq.fn` directly since `tacticSeq` is not a parser category.
    -- See https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/piggy.20back.20off.20of.20the.20lean4.20parser
    let tacSeq ← try
ofExcept
        Mathlib.GuardExceptions.captureException (← 
-/
def Mathlib.TacticAnalysis.tryAtEachStepFromStrings
    (label : String) (tacticStr : String) : TacticAnalysis.Config where
  run seq := do
    -- Parse using `tacticSeq.fn` directly since `tacticSeq` is not a parser category.
    -- See https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/piggy.20back.20off.20of.20the.20lean4.20parser
    let tacSeq ← try
ofExcept
        Mathlib.GuardExceptions.captureException (← getEnv) Parser.Tactic.tacticSeq.fn tacticStr
    catch _ =>
      -- Tactic not available (e.g., `aesop` before Aesop is imported) - skip silently
      return
    let tac : TSyntax `tactic := ⟨mkNode ``Lean.Parser.Tactic.tacticSeq1Indented #[tacSeq]⟩
    (tryAtEachStepCore (fun _ _ => pure tac) label).run seq

/--
Definition of `Mathlib.TacticAnalysis.tryAtEachStepFromEnvImpl` / `Mathlib.TacticAnalysis.tryAtEachStepFromEnvImpl` 的定义

English:
definition Mathlib.TacticAnalysis.tryAtEachStepFromEnvImpl
  signature: : TacticAnalysis.Config where
  body: do
    let some tacticStr := (← IO.getEnv "TRY_AT_EACH_STEP_TACTIC") | return
    let label := (← IO.getEnv "TRY_AT_EACH_STEP_LABEL").getD tacticStr
    (tryAtEachStepFromStrings label tacticStr).run seq

中文:
定义 Mathlib.TacticAnalysis.tryAtEachStepFromEnvImpl
  签名: : TacticAnalysis.Config where
  定义体: do
    let some tacticStr := (← IO.getEnv "TRY_AT_EACH_STEP_TACTIC") | return
    let label := (← IO.getEnv "TRY_AT_EACH_STEP_LABEL").getD tacticStr
    (tryAtEachStepFromStrings label tacticStr).run seq
-/
def Mathlib.TacticAnalysis.tryAtEachStepFromEnvImpl : TacticAnalysis.Config where
  run seq := do
    let some tacticStr := (← IO.getEnv "TRY_AT_EACH_STEP_TACTIC") | return
    let label := (← IO.getEnv "TRY_AT_EACH_STEP_LABEL").getD tacticStr
    (tryAtEachStepFromStrings label tacticStr).run seq

/-- Run `grind` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepGrind,
   inherit_doc linter.tacticAnalysis.tryAtEachStepGrind]
/--
Definition of `tryAtEachStepGrind` / `tryAtEachStepGrind` 的定义

English:
definition tryAtEachStepGrind
  body: tryAtEachStep fun _ _ => `(tactic| grind)

中文:
定义 tryAtEachStepGrind
  定义体: tryAtEachStep fun _ _ => `(tactic| grind)

Depends on / 依赖: tactic, tryAtEachStep
-/
def tryAtEachStepGrind := tryAtEachStep fun _ _ => `(tactic| grind)

/-- Run `simp_all` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepSimpAll : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepSimpAll,
   inherit_doc linter.tacticAnalysis.tryAtEachStepSimpAll]
/--
Definition of `tryAtEachStepSimpAll` / `tryAtEachStepSimpAll` 的定义

English:
definition tryAtEachStepSimpAll
  body: tryAtEachStep fun _ _ => `(tactic| simp_all)

中文:
定义 tryAtEachStepSimpAll
  定义体: tryAtEachStep fun _ _ => `(tactic| simp_all)

Depends on / 依赖: tactic, tryAtEachStep
-/
def tryAtEachStepSimpAll := tryAtEachStep fun _ _ => `(tactic| simp_all)

/-- Run `aesop` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepAesop : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepAesop,
   inherit_doc linter.tacticAnalysis.tryAtEachStepAesop]
/--
Definition of `tryAtEachStepAesop` / `tryAtEachStepAesop` 的定义

English:
definition tryAtEachStepAesop
  body: tryAtEachStep
  -- As `aesop` isn't imported here, we construct the tactic syntax manually.
fun _ _ => return ⟨TSyntax.raw
    mkNode `Aesop.Frontend.Parser.aesopTactic #[mkAtom "aesop", mkNullNode]⟩

中文:
定义 tryAtEachStepAesop
  定义体: tryAtEachStep
  -- As `aesop` isn't imported here, we construct the tactic syntax manually.
fun _ _ => return ⟨TSyntax.raw
    mkNode `Aesop.Frontend.Parser.aesopTactic #[mkAtom "aesop", mkNullNode]⟩

Depends on / 依赖: tryAtEachStep
-/
def tryAtEachStepAesop := tryAtEachStep
  -- As `aesop` isn't imported here, we construct the tactic syntax manually.
fun _ _ => return ⟨TSyntax.raw
    mkNode `Aesop.Frontend.Parser.aesopTactic #[mkAtom "aesop", mkNullNode]⟩

/-- Run `grind +suggestions` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepGrindSuggestions : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepGrindSuggestions,
   inherit_doc linter.tacticAnalysis.tryAtEachStepGrindSuggestions]
/--
Definition of `tryAtEachStepGrindSuggestions` / `tryAtEachStepGrindSuggestions` 的定义

English:
definition tryAtEachStepGrindSuggestions
  body: tryAtEachStep fun _ _ => `(tactic| grind +suggestions)

中文:
定义 tryAtEachStepGrindSuggestions
  定义体: tryAtEachStep fun _ _ => `(tactic| grind +suggestions)

Depends on / 依赖: suggestions, tactic, tryAtEachStep
-/
def tryAtEachStepGrindSuggestions := tryAtEachStep fun _ _ => `(tactic| grind +suggestions)

/-- Run `simp_all? +suggestions` at every step in proofs, reporting where it succeeds. -/
register_option linter.tacticAnalysis.tryAtEachStepSimpAllSuggestions : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepSimpAllSuggestions,
   inherit_doc linter.tacticAnalysis.tryAtEachStepSimpAllSuggestions]
/--
Definition of `tryAtEachStepSimpAllSuggestions` / `tryAtEachStepSimpAllSuggestions` 的定义

English:
definition tryAtEachStepSimpAllSuggestions
  body: tryAtEachStep fun _ _ => `(tactic| simp_all? +suggestions)

中文:
定义 tryAtEachStepSimpAllSuggestions
  定义体: tryAtEachStep fun _ _ => `(tactic| simp_all? +suggestions)

Depends on / 依赖: suggestions, tactic, tryAtEachStep
-/
def tryAtEachStepSimpAllSuggestions := tryAtEachStep fun _ _ => `(tactic| simp_all? +suggestions)

/-- Run a custom tactic at every step in proofs, configured via environment variables.

Set `TRY_AT_EACH_STEP_TACTIC` to the tactic syntax to try (required).
Set `TRY_AT_EACH_STEP_LABEL` to the label for output messages (optional, defaults to tactic).
-/
register_option linter.tacticAnalysis.tryAtEachStepFromEnv : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.tryAtEachStepFromEnv,
   inherit_doc linter.tacticAnalysis.tryAtEachStepFromEnv]
/--
Definition of `tryAtEachStepFromEnv` / `tryAtEachStepFromEnv` 的定义

English:
definition tryAtEachStepFromEnv
  body: tryAtEachStepFromEnvImpl

中文:
定义 tryAtEachStepFromEnv
  定义体: tryAtEachStepFromEnvImpl

Depends on / 依赖: tryAtEachStepFromEnvImpl
-/
def tryAtEachStepFromEnv := tryAtEachStepFromEnvImpl

/--
Definition of `introMergeArgOfRCasesPat?` / `introMergeArgOfRCasesPat?` 的定义

English:
definition introMergeArgOfRCasesPat?
  signature: (pat : TSyntax `rcasesPat)
  body: match pat with
  | `(rcasesPat| _%$x) => some ⟨mkHole x⟩
  | `(rcasesPat| $h:ident) =>
      if h.getId == `rfl then none else some ⟨h.raw⟩
  | _ => none

中文:
定义 introMergeArgOfRCasesPat?
  签名: (pat : TSyntax `rcasesPat)
  定义体: match pat with
  | `(rcasesPat| _%$x) => some ⟨mkHole x⟩
  | `(rcasesPat| $h:ident) =>
      if h.getId == `rfl then none else some ⟨h.raw⟩
  | _ => none
-/
private def introMergeArgOfRCasesPat? (pat : TSyntax `rcasesPat) : Option Term :=
  match pat with
  | `(rcasesPat| _%$x) => some ⟨mkHole x⟩
  | `(rcasesPat| $h:ident) =>
      if h.getId == `rfl then none else some ⟨h.raw⟩
  | _ => none

/--
Definition of `introMergeArgOfRIntroPat?` / `introMergeArgOfRIntroPat?` 的定义

English:
definition introMergeArgOfRIntroPat?
  signature: (pat : TSyntax `rintroPat)
  body: match pat with
  | `(rintroPat| $pat:rcasesPat) => introMergeArgOfRCasesPat? pat
  | _ => none

中文:
定义 introMergeArgOfRIntroPat?
  签名: (pat : TSyntax `rintroPat)
  定义体: match pat with
  | `(rintroPat| $pat:rcasesPat) => introMergeArgOfRCasesPat? pat
  | _ => none
-/
private def introMergeArgOfRIntroPat? (pat : TSyntax `rintroPat) : Option Term :=
  match pat with
  | `(rintroPat| $pat:rcasesPat) => introMergeArgOfRCasesPat? pat
  | _ => none

/--
Definition of `introMergeArgs?` / `introMergeArgs?` 的定义

English:
definition introMergeArgs?
  signature: (stx : TSyntax `tactic)
  body: match stx with
  | `(tactic| intro%$x $args*) =>
some if args.size = 0 then #[⟨mkHole x⟩] else args
  | `(tactic| intros $ids*) =>
if ids.size = 0 then none else some ids.map fun stx => ⟨stx.raw⟩
  | `(tactic| rintro $pats*) =>
      pats.mapM introMergeArgOfRIntroPat?
  | _ => none

中文:
定义 introMergeArgs?
  签名: (stx : TSyntax `tactic)
  定义体: match stx with
  | `(tactic| intro%$x $args*) =>
some if args.size = 0 then #[⟨mkHole x⟩] else args
  | `(tactic| intros $ids*) =>
if ids.size = 0 then none else some ids.map fun stx => ⟨stx.raw⟩
  | `(tactic| rintro $pats*) =>
      pats.mapM introMergeArgOfRIntroPat?
  | _ => none
-/
private def introMergeArgs? (stx : TSyntax `tactic) : Option (Array Term) :=
  match stx with
  | `(tactic| intro%$x $args*) =>
some if args.size = 0 then #[⟨mkHole x⟩] else args
  | `(tactic| intros $ids*) =>
if ids.size = 0 then none else some ids.map fun stx => ⟨stx.raw⟩
  | `(tactic| rintro $pats*) =>
      pats.mapM introMergeArgOfRIntroPat?
  | _ => none

/-- Suggest merging adjacent `intro`-like tactics whose effect is equivalent to a single `intro`. -/
register_option linter.tacticAnalysis.introMerge : Bool := {
  defValue := true
}

@[tacticAnalysis linter.tacticAnalysis.introMerge, inherit_doc linter.tacticAnalysis.introMerge]
/--
Definition of `Mathlib.TacticAnalysis.introMerge` / `Mathlib.TacticAnalysis.introMerge` 的定义

English:
definition Mathlib.TacticAnalysis.introMerge
  signature: : TacticAnalysis.Config
  body: .ofComplex {
  out := Option (TSyntax `tactic)
  ctx := Array (Array Term)
  trigger ctx stx :=
    match introMergeArgs? ⟨stx⟩ with
    | some args => .continue ((ctx.getD #[]).push args)
    | none => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctxI

中文:
定义 Mathlib.TacticAnalysis.introMerge
  签名: : TacticAnalysis.Config
  定义体: .ofComplex {
  out := Option (TSyntax `tactic)
  ctx := Array (Array Term)
  trigger ctx stx :=
    match introMergeArgs? ⟨stx⟩ with
    | some args => .continue ((ctx.getD #[]).push args)
    | none => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctxI

Depends on / 依赖: ofComplex
-/
def Mathlib.TacticAnalysis.introMerge : TacticAnalysis.Config := .ofComplex {
  out := Option (TSyntax `tactic)
  ctx := Array (Array Term)
  trigger ctx stx :=
    match introMergeArgs? ⟨stx⟩ with
    | some args => .continue ((ctx.getD #[]).push args)
    | none => if let some args := ctx then if args.size > 1 then .accept args else .skip else .skip
  test ctxI i ctx goal := do
    let ctxT := ctx.flatten
    let tac ← `(tactic| intro $ctxT*)
    try
      let _ ← ctxI.runTacticCode i goal tac
      return some tac
    catch _e => -- if for whatever reason we can't run `intro` here.
      return none
tell _stx _old _oldHeartbeats new _newHeartbeats := pure
    if let some tac := new then m!"Try this: {tac}" else none}

/--
Definition of `parseSuggestionToTactic` / `parseSuggestionToTactic` 的定义

English:
definition parseSuggestionToTactic
  signature: (s : Lean.Meta.Tactic.TryThis.Suggestion)
  body: do
  match s.suggestion with
  | .tsyntax stx =>
    -- Return the suggestion as-is
    return ⟨stx.raw⟩
  | .string str =>
    match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) str with
    | .ok tacSeq =>
      `(tactic| ($tacSeq:tacticSeq))
    | .error err => throwError "Failed to parse 

中文:
定义 parseSuggestionToTactic
  签名: (s : Lean.Meta.Tactic.TryThis.Suggestion)
  定义体: do
  match s.suggestion with
  | .tsyntax stx =>
    -- Return the suggestion as-is
    return ⟨stx.raw⟩
  | .string str =>
    match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) str with
    | .ok tacSeq =>
      `(tactic| ($tacSeq:tacticSeq))
    | .error err => throwError "Failed to parse 
-/
private def parseSuggestionToTactic (s : Lean.Meta.Tactic.TryThis.Suggestion) :
    CommandElabM (TSyntax `tactic) := do
  match s.suggestion with
  | .tsyntax stx =>
    -- Return the suggestion as-is
    return ⟨stx.raw⟩
  | .string str =>
    match Mathlib.GuardExceptions.parseAsTacticSeq (← getEnv) str with
    | .ok tacSeq =>
      `(tactic| ($tacSeq:tacticSeq))
    | .error err => throwError "Failed to parse suggestion: {str}\n{err}"

/--
Definition of `Mathlib.TacticAnalysis.verifyTryThisSuggestions` / `Mathlib.TacticAnalysis.verifyTryThisSuggestions` 的定义

English:
definition Mathlib.TacticAnalysis.verifyTryThisSuggestions
  body: do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    for i in seq do
      if let [goal] := i.tacI.goalsBefore then
        let goalDecl := i.tacI.mctxBefore.decls.find! goal
        let goalPP ← i.ctxI.runMetaM goalDecl.lctx do
          withOpt

中文:
定义 Mathlib.TacticAnalysis.verifyTryThisSuggestions
  定义体: do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    for i in seq do
      if let [goal] := i.tacI.goalsBefore then
        let goalDecl := i.tacI.mctxBefore.decls.find! goal
        let goalPP ← i.ctxI.runMetaM goalDecl.lctx do
          withOpt
-/
def Mathlib.TacticAnalysis.verifyTryThisSuggestions
    (tac : Syntax -> MVarId -> CommandElabM (Option (TSyntax `tactic)))
    (label : String) : TacticAnalysis.Config where
  run seq := do
    let opts ← getOptions
    let fraction := linter.tacticAnalysis.tryAtEachStep.fraction.get opts
    for i in seq do
      if let [goal] := i.tacI.goalsBefore then
        let goalDecl := i.tacI.mctxBefore.decls.find! goal
        let goalPP ← i.ctxI.runMetaM goalDecl.lctx do
          withOptions (·.setBool `pp.mvars.anonymous false) do
            return toString (← Meta.ppGoal goal)
        if (hash goalPP) % fraction = 0 then
          if let some tac ← tac i.tacI.stx goal then
          -- Save message state to suppress "Try this:" info messages from grind?
          let savedMessages := (← get).messages
          -- Run tactic and capture InfoTree
          let (goalsAfter, trees) ← try
            i.runTacticCodeCapturingInfoTree goal tac
          catch _e =>
            continue -- Tactic failed, nothing to verify
          finally
            -- Restore messages (discard info messages from grind?)
            modify fun s => { s with messages := savedMessages }

          -- Only verify if tactic succeeded (closed goal)
          if !goalsAfter.isEmpty then continue

          -- Extract suggestions from InfoTree
          let suggestions := Elab.collectTryThisSuggestions trees
          for s in suggestions do
            -- Parse suggestion to syntax
            let suggestedTac ← try
              parseSuggestionToTactic s
            catch e =>
              logWarningAt i.tacI.stx m!"`{label}` produced unparseable suggestion: {e.toMessageData}"
              continue

            -- Skip empty interactive mode suggestions (just `grind => {}` with no body).
            -- These are intermediate suggestions that aren't meant to be used standalone.
            -- Syntax structure: grind[0]="grind" [1]=optConfig [2]=only? [3]=params? [4]=(=> grindSeq)?
            -- When [4].getNumArgs == 2: [4][0]="=>" [4][1]=grindSeq
            -- grindSeq[0] is grindSeqBracketed: { content }, empty when content.getNumArgs == 0
            if suggestedTac.raw.getKind == ``Lean.Parser.Tactic.grind then
              if suggestedTac.raw[4]!.getNumArgs == 2 then
                if suggestedTac.raw[4]![1]![0]![1]!.getNumArgs == 0 then
                  continue

            -- Skip suggestions containing hexcode anchors (e.g., #962a, #8ef1)
            -- These are proof-context-specific references that aren't valid in a fresh goal
.isSome then if suggestedTac.raw.find? (·.isOfKind ``Lean.Parser.Tactic.anchor)
              continue

            -- Skip suggestions containing `approx` - these are incomplete approximations
            if suggestedTac.raw.find? (fun stx => stx.isOfKind ``Lean.Parser.Tactic.Grind.instantiate &&
              (stx.find? (·.getAtomVal == "approx")).isSome) |>.isSome
            then
              continue

            -- Verify suggestion works (suppress any messages from verification)
            let savedMessages2 := (← get).messages
            let verifyGoals ← try
              i.runTacticCode goal suggestedTac
            catch _e =>
              pure [goal] -- Treat exception as failure
            modify fun s => { s with messages := savedMessages2 }

            if !verifyGoals.isEmpty then
              logWarningAt i.tacI.stx
                m!"`{label}` suggestion failed: `{suggestedTac}` did not close the goal"

/-- Verify that `grind?` suggestions actually work. -/
register_option linter.tacticAnalysis.verifyGrind : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.verifyGrind,
   inherit_doc linter.tacticAnalysis.verifyGrind]
/--
Definition of `verifyGrind` / `verifyGrind` 的定义

English:
definition verifyGrind
  body: verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind?))
  "grind?"

中文:
定义 verifyGrind
  定义体: verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind?))
  "grind?"

Depends on / 依赖: verifyTryThisSuggestions
-/
def verifyGrind := verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind?))
  "grind?"

/-- Verify that `grind? +suggestions` suggestions actually work. -/
register_option linter.tacticAnalysis.verifyGrindSuggestions : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.verifyGrindSuggestions,
   inherit_doc linter.tacticAnalysis.verifyGrindSuggestions]
/--
Definition of `verifyGrindSuggestions` / `verifyGrindSuggestions` 的定义

English:
definition verifyGrindSuggestions
  body: verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind? +suggestions))
  "grind? +suggestions"

中文:
定义 verifyGrindSuggestions
  定义体: verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind? +suggestions))
  "grind? +suggestions"

Depends on / 依赖: verifyTryThisSuggestions
-/
def verifyGrindSuggestions := verifyTryThisSuggestions
  (fun _ _ => `(tactic| grind? +suggestions))
  "grind? +suggestions"

/-- Verify that replacing `grind` with `grind?` produces a valid `grind only` suggestion. -/
register_option linter.tacticAnalysis.verifyGrindOnly : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.verifyGrindOnly,
   inherit_doc linter.tacticAnalysis.verifyGrindOnly]
/--
Definition of `verifyGrindOnly` / `verifyGrindOnly` 的定义

English:
definition verifyGrindOnly
  body: verifyTryThisSuggestions
  (fun stx _ =>
    return match stx with
    | .node info ``Lean.Parser.Tactic.grind args => some ⟨.node info ``Lean.Parser.Tactic.grindTrace args⟩
    | _ => none
  )
  "grind?"

中文:
定义 verifyGrindOnly
  定义体: verifyTryThisSuggestions
  (fun stx _ =>
    return match stx with
    | .node info ``Lean.Parser.Tactic.grind args => some ⟨.node info ``Lean.Parser.Tactic.grindTrace args⟩
    | _ => none
  )
  "grind?"

Depends on / 依赖: verifyTryThisSuggestions
-/
def verifyGrindOnly := verifyTryThisSuggestions
  (fun stx _ =>
    return match stx with
    | .node info ``Lean.Parser.Tactic.grind args => some ⟨.node info ``Lean.Parser.Tactic.grindTrace args⟩
    | _ => none
  )
  "grind?"
