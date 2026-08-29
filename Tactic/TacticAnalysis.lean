/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Lean.Util.Heartbeats
public meta import Lean.Server.InfoUtils
public meta import Mathlib.Lean.Elab.Tactic.Meta
public meta import Lean.Compiler.IR.CompilerM
public import Lean.Elab.Command
public import Mathlib.Lean.ContextInfo

/-! # Tactic analysis framework

In this file we define a framework for analyzing sequences of tactics.
This can be used for linting (for instance: report when two `rw` calls can be merged into one),
but it can also be run in a more batch-like mode to report larger potential refactors
(for instance: report when a sequence of three or more tactics can be replaced with `grind`,
without taking more heartbeats than the original proof did).

## Using the framework

The framework runs, but does nothing by default (`set_option linter.tacticAnalysis false`
to turn it off completely). Enable the analysis round `roundName` by enabling its corresponding
option: `set_option linter.tacticAnalysis.roundName true`.

To add a round of analysis called `roundName`, declare an option `linter.tacticAnalysis.roundName`,
make a definition of type `Mathlib.TacticAnalysis.Config` and give the `Config` declaration the
`@[tacticAnalysis linter.tacticAnalysis.roundName]` attribute. Don't forget to enable the option.

## Warning

The `ComplexConfig` interface doesn't feel quite intuitive and flexible yet and should be changed
in the future. Please do not rely on this interface being stable.
-/

public meta section

open Lean Elab Term Command Linter

/-- The tactic analysis framework hooks into the linter to run analysis rounds on sequences
of tactics.
This can be used for linting, or in a more batch-like mode to report potential refactors.
-/
register_option linter.tacticAnalysis : Bool := {
  defValue := true
  descr := "enable the tactic analysis framework"
}

namespace Mathlib.TacticAnalysis

/--
Definition of `TacticNode` / `TacticNode` 的定义

English:
structure TacticNode
  parameters: where
  axioms and operations (3):
    - ctxI : ContextInfo
    - tacI : TacticInfo
    - mayFail : Bool

中文:
结构 TacticNode
  参数: where
  公理与运算 (3 个):
    - ctxI : ContextInfo
    - tacI : TacticInfo
    - mayFail : 布尔值
-/
structure TacticNode where
  /-- `ContextInfo` at the infotree node. -/
  ctxI : ContextInfo
  /-- `TacticInfo` at the infotree node. -/
  tacI : TacticInfo
  /-- This tactic is allowed to fail because it is in a `try`/`anyGoals`/etc block. -/
  mayFail : Bool

/--
Definition of `TacticNode.runTacticCode` / `TacticNode.runTacticCode` 的定义

English:
abbreviation TacticNode.runTacticCode
  signature: (i : TacticNode)
  body: i.ctxI.runTacticCode i.tacI

中文:
缩写 TacticNode.runTacticCode
  签名: (i : TacticNode)
  定义体: i.ctxI.runTacticCode i.tacI

Depends on / 依赖: i.ctxI.runTacticCode, i.tacI, runTacticCode
-/
abbrev TacticNode.runTacticCode (i : TacticNode) :
    MVarId -> Syntax -> CommandElabM (List MVarId) :=
  i.ctxI.runTacticCode i.tacI

/--
Definition of `TacticNode.runTacticCodeCapturingInfoTree` / `TacticNode.runTacticCodeCapturingInfoTree` 的定义

English:
abbreviation TacticNode.runTacticCodeCapturingInfoTree
  signature: (i : TacticNode)
  body: i.ctxI.runTacticCodeCapturingInfoTree i.tacI

中文:
缩写 TacticNode.runTacticCodeCapturingInfoTree
  签名: (i : TacticNode)
  定义体: i.ctxI.runTacticCodeCapturingInfoTree i.tacI

Depends on / 依赖: i.ctxI.runTacticCodeCapturingInfoTree, i.tacI, runTacticCodeCapturingInfoTree
-/
abbrev TacticNode.runTacticCodeCapturingInfoTree (i : TacticNode) :
    MVarId -> Syntax -> CommandElabM (List MVarId × PersistentArray InfoTree) :=
  i.ctxI.runTacticCodeCapturingInfoTree i.tacI

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  parameters: where
  axioms and operations (1):
    - run : Array TacticNode -> CommandElabM Unit

中文:
结构 余nfig
  参数: where
  公理与运算 (1 个):
    - run : 数组 TacticNode -> CommandElabM 单元
-/
structure Config where
  /-- The function that runs this pass. Takes an array of infotree nodes corresponding
  to a sequence of tactics from the source file. Should do all reporting itself,
  for example by `Lean.Linter.logLint`.
  -/
  run : Array TacticNode -> CommandElabM Unit

/--
Definition of `Pass` / `Pass` 的定义

English:
structure Pass
  parameters: extends Config
  extends: Config
  axioms and operations (1):
    - opt : Option (Lean.Option Bool)

中文:
结构 Pass
  参数: extends 余nfig
  继承: 余nfig
  公理与运算 (1 个):
    - opt : 选项类型 (Lean.选项类型 布尔值)
-/
structure Pass extends Config where
  /-- The option corresponding to this pass, used to enable it.

  Example: `linter.tacticAnalysis.grindReplacement`.
  -/
  opt : Option (Lean.Option Bool)

/--
Definition of `Entry` / `Entry` 的定义

English:
structure Entry
  parameters: where
  axioms and operations (2):
    - declName : Name
    - optionName : Name

中文:
结构 Entry
  参数: where
  公理与运算 (2 个):
    - declName : Name
    - optionName : Name
-/
structure Entry where
  /-- The declaration, of type `Config`, that defines this pass. -/
  declName : Name
  /-- The option, of type `Lean.Option Bool`, that controls whether the pass is enabled. -/
  optionName : Name

/--
Definition of `Entry.import` / `Entry.import` 的定义

English:
definition Entry.import
  signature: (e : Entry)
  body: do
  let { env, opts, .. } ← read
let cfg ← IO.ofExcept
    unsafe env.evalConstCheck Config opts ``Config e.declName
  -- This next line can return `none` in the file where the option is declared:
  let opt := (unsafe env.evalConst (Lean.Option Bool) opts e.optionName).toOption
  return { cfg with 

中文:
定义 Entry.import
  签名: (e : Entry)
  定义体: do
  let { env, opts, .. } ← read
let cfg ← IO.ofExcept
    unsafe env.evalConstCheck Config opts ``Config e.declName
  -- This next line can return `none` in the file where the option is declared:
  let opt := (unsafe env.evalConst (Lean.Option Bool) opts e.optionName).toOption
  return { cfg with 
-/
def Entry.import (e : Entry) : ImportM Pass := do
  let { env, opts, .. } ← read
let cfg ← IO.ofExcept
    unsafe env.evalConstCheck Config opts ``Config e.declName
  -- This next line can return `none` in the file where the option is declared:
  let opt := (unsafe env.evalConst (Lean.Option Bool) opts e.optionName).toOption
  return { cfg with opt }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord Entry
  body: (@lexOrd _ _ ⟨Lean.Name.cmp⟩ ⟨Lean.Name.cmp⟩).compare (a.1, a.2) (b.1, b.2)

中文:
实例 :
  签名: 序 Entry
  定义体: (@lexOrd _ _ ⟨Lean.Name.cmp⟩ ⟨Lean.Name.cmp⟩).compare (a.1, a.2) (b.1, b.2)

Depends on / 依赖: Lean.Name.cmp, compare, lexOrd
-/
instance : Ord Entry where
  compare a b := (@lexOrd _ _ ⟨Lean.Name.cmp⟩ ⟨Lean.Name.cmp⟩).compare (a.1, a.2) (b.1, b.2)

/-- Environment extensions for `tacticAnalysis` declarations -/
initialize tacticAnalysisExt : PersistentEnvExtension Entry (Entry × Pass)
    -- Like `SimplePersistentEnvExtension`, store the locally declared entries separately from all
    -- of the passes. Otherwise we end up re-exporting the entries and spending a lot of time
    -- deduplicating them downstream.
    (List Entry × Array Pass) ←
  registerPersistentEnvExtension {
    mkInitial := pure ([], #[])
    addImportedFn s := do
      let localEntries := []
      let allPasses ← s.flatten.mapM fun e => e.import
      return (localEntries, allPasses)
    addEntryFn := fun (localEntries, allPasses) (entry, pass) =>
      (entry :: localEntries, allPasses.push pass)
    exportEntriesFn := fun (localEntries, _) => localEntries.reverse.toArray
  }

/-- Attribute adding a tactic analysis pass from a `Config` structure. -/
initialize registerBuiltinAttribute {
  name := `tacticAnalysis
  descr := "adds a tacticAnalysis pass"
  applicationTime := .afterCompilation
  add declName stx kind := match stx with
    | `(attr| tacticAnalysis) => do
      throwError m!"tacticAnalysis: missing option name."
    | `(attr| tacticAnalysis $optionName) => do
      unless kind == AttributeKind.global do
        throwError "invalid attribute 'tacticAnalysis', must be global"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'tacticAnalysis', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let entry := {
        declName
        optionName := Syntax.getId optionName
      }
      let ext ← entry.import
setEnv tacticAnalysisExt.addEntry env (entry, ext)
    | _ => throwUnsupportedSyntax
}

/--
Definition of `findTacticSeqs` / `findTacticSeqs` 的定义

English:
definition findTacticSeqs
  signature: (tree : InfoTree)
  body: do
  -- Turn the CommandElabM into a surrounding context for traversing the tree.
  let ctx ← read
  let state ← get
  let ctxInfo := { env := state.env, fileMap := ctx.fileMap, ngen := state.ngen }
  let out ← tree.visitM (m := CommandElabM) (ctx? := some ctxInfo)
    (fun _ _ _ => pure true) -- As

中文:
定义 findTacticSeqs
  签名: (tree : InfoTree)
  定义体: do
  -- Turn the CommandElabM into a surrounding context for traversing the tree.
  let ctx ← read
  let state ← get
  let ctxInfo := { env := state.env, fileMap := ctx.fileMap, ngen := state.ngen }
  let out ← tree.visitM (m := CommandElabM) (ctx? := some ctxInfo)
    (fun _ _ _ => pure true) -- As
-/
def findTacticSeqs (tree : InfoTree) : CommandElabM (Array (Array TacticNode)) := do
  -- Turn the CommandElabM into a surrounding context for traversing the tree.
  let ctx ← read
  let state ← get
  let ctxInfo := { env := state.env, fileMap := ctx.fileMap, ngen := state.ngen }
  let out ← tree.visitM (m := CommandElabM) (ctx? := some ctxInfo)
    (fun _ _ _ => pure true) -- Assumption: a tactic can occur as a child of any piece of syntax.
    (fun ctx i _c cs => do
      let relevantChildren := (cs.filterMap id).toArray
      let childTactics := relevantChildren.filterMap Prod.fst
      let childSequences := (relevantChildren.map Prod.snd).flatten
      let stx := i.stx
      -- Tactic sequencing operators: collect all the child tactics into a new sequence.
      -- This must happen regardless of source info, as `have h := by ...` creates tacticSeq
      -- nodes with synthetic source info.
      if stx.getKind in [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
          ``Lean.Parser.Term.byTactic] then
        return (none, if childTactics.isEmpty then
            childSequences
          else
            childSequences.push childTactics)
      if let some (.original _ _ _ _) := stx.getHeadInfo? then
        -- Punctuation: skip this.
        if stx.getKind in [`«;», `Lean.cdotTk, `«]», nullKind, `«by»] then
          return (none, childSequences)
        -- Tactic modifiers: return the children unmodified.
        if stx.getKind in [``Lean.Parser.Tactic.withAnnotateState] then
          return (childTactics[0]?, childSequences)

        -- Remaining options: plain pieces of syntax.
        -- We discard `childTactics` here, because those are either already picked up by a
        -- sequencing operator, or come from macros.
        if let .ofTacticInfo i := i then
          let childSequences :=
            -- This tactic accepts the failure of its children.
            if stx.getKind in [``Lean.Parser.Tactic.tacticTry_, ``Lean.Parser.Tactic.anyGoals] then
              childSequences.map (·.map fun i => { i with mayFail := true })
            else
              childSequences
          return (some ⟨ctx, i, false⟩, childSequences)
        return (none, childSequences)
      else
        return (none, childSequences))
  return (out.map Prod.snd).getD #[]

/--
Definition of `runPasses` / `runPasses` 的定义

English:
definition runPasses
  signature: (configs : Array Pass) (trees : PersistentArray InfoTree)
  body: do
  let opts ← getLinterOptions
  let enabledConfigs := configs.filter fun config =>
    -- This can be `none` in the file where the option is declared.
    if let some opt := config.opt then getLinterValue opt opts else false
  if enabledConfigs.isEmpty then
    return
  for i in trees do
    for 

中文:
定义 runPasses
  签名: (configs : 数组 Pass) (trees : PersistentArray InfoTree)
  定义体: do
  let opts ← getLinterOptions
  let enabledConfigs := configs.filter fun config =>
    -- This can be `none` in the file where the option is declared.
    if let some opt := config.opt then getLinterValue opt opts else false
  if enabledConfigs.isEmpty then
    return
  for i in trees do
    for 
-/
def runPasses (configs : Array Pass) (trees : PersistentArray InfoTree) : CommandElabM Unit := do
  let opts ← getLinterOptions
  let enabledConfigs := configs.filter fun config =>
    -- This can be `none` in the file where the option is declared.
    if let some opt := config.opt then getLinterValue opt opts else false
  if enabledConfigs.isEmpty then
    return
  for i in trees do
    for seq in (← findTacticSeqs i) do
      for config in enabledConfigs do
        config.run seq

/--
Definition of `tacticAnalysis` / `tacticAnalysis` 的定义

English:
definition tacticAnalysis
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  profileitM Exception "tacticAnalysis" (← getOptions) do
  let env ← getEnv
  let configs := (tacticAnalysisExt.getState env).2
  let trees ← getInfoTrees
  runPasses configs trees

中文:
定义 tacticAnalysis
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  profileitM Exception "tacticAnalysis" (← getOptions) do
  let env ← getEnv
  let configs := (tacticAnalysisExt.getState env).2
  let trees ← getInfoTrees
  runPasses configs trees

Depends on / 依赖: withSetOptionIn
-/
def tacticAnalysis : Linter where run := withSetOptionIn fun stx => do
  if (← get).messages.hasErrors then
    return
  profileitM Exception "tacticAnalysis" (← getOptions) do
  let env ← getEnv
  let configs := (tacticAnalysisExt.getState env).2
  let trees ← getInfoTrees
  runPasses configs trees

initialize addLinter tacticAnalysis

section ComplexConfig

/-!
### Work in progress: `Config` building blocks

In this section we define `ComplexConfig` which is supposed to make it easier to build standard
analysis rounds.

**Work in progress** note: This interface does not feel intuitive yet and might be redesigned.
Please do not rely on it being stable!
-/

/--
Inductive type `TriggerCondition` / 归纳类型 `TriggerCondition`

English:
inductive TriggerCondition
  parameters: (ctx : Type _)
  constructors (3):
    - skip: 
    - continue: (context : ctx)
    - accept: (context : ctx)

中文:
归纳类型 TriggerCondition
  参数: (ctx : 类型 _)
  构造子 (3 个):
    - skip: 
    - continue: (context : ctx)
    - accept: (context : ctx)
-/
inductive TriggerCondition (ctx : Type _)
  /-- `skip` means that the current tactic and the ones before it will be discarded. -/
  | skip
  /-- `continue` means to accumulate the current tactic, but not yet run the test on it. -/
  | continue (context : ctx)
  /-- `accept` means to run the test on the sequence of `.continue`s up to this `.accept`. -/
  | accept (context : ctx)
deriving BEq

/--
Definition of `ComplexConfig` / `ComplexConfig` 的定义

English:
structure ComplexConfig
  parameters: where
  axioms and operations (5):
    - out : Type
    - ctx : Type
    - trigger((context : Option ctx) (currentTactic : Syntax)) : TriggerCondition ctx
    - test((ctxI : ContextInfo) (i : TacticInfo) (context : ctx) (goal : MVarId)) : CommandElabM out
    - tell((stx : Syntax) (originalSubgoals : List MVarId) (originalHeartbeats : Nat) (new : out) (newHeartbeats : Nat)) : CommandElabM (Option MessageData)

中文:
结构 余mplexConfig
  参数: where
  公理与运算 (5 个):
    - out : 类型
    - ctx : 类型
    - trigger((context : 选项类型 ctx) (currentTactic : Syntax)) : TriggerCondition ctx
    - test((ctxI : ContextInfo) (i : TacticInfo) (context : ctx) (goal : MVarId)) : CommandElabM out
    - tell((stx : Syntax) (originalSubgoals : 列表 MVarId) (originalHeartbeats : 自然数) (new : out) (newHeartbeats : 自然数)) : CommandElabM (选项类型 MessageData)
-/
structure ComplexConfig where
  /-- Type returned by the `.test` function. -/
  out : Type
  /-- Type returned by the `.trigger` function. -/
  ctx : Type

  /-- Determines which (sequences of) tactics to analyze.

  `context` is `some ctx` whenever the previous trigger returned `continue ctx`,
  `none` at the start of a tactic sequence or after a `skip`/`accept`.

  If the last returned value is `continue` at the end of the sequence, the framework inserts an
  extra `done` to run the `trigger` on.
  -/
  trigger (context : Option ctx) (currentTactic : Syntax) : TriggerCondition ctx
  /-- Code to run in the context of the tactic, for example an alternative tactic. -/
  test (ctxI : ContextInfo) (i : TacticInfo) (context : ctx) (goal : MVarId) : CommandElabM out
  /-- Decides what to report to the user. -/
  tell (stx : Syntax) (originalSubgoals : List MVarId) (originalHeartbeats : Nat)
    (new : out) (newHeartbeats : Nat) : CommandElabM (Option MessageData)

/--
Definition of `testTacticSeq` / `testTacticSeq` 的定义

English:
definition testTacticSeq
  signature: (config : ComplexConfig) (tacticSeq : Array (TSyntax `tactic))
  body: do
  /- Syntax quotations use the current ref's position info even for nodes which do not usually
  carry position info. We set the ref here to ensure we log messages on the correct range. -/
  withRef (mkNullNode tacticSeq) do
    let stx ← `(tactic| $tacticSeq;*)
    -- TODO: support more than 1 g

中文:
定义 testTacticSeq
  签名: (config : 余mplexConfig) (tacticSeq : 数组 (TSyntax `tactic))
  定义体: do
  /- Syntax quotations use the current ref's position info even for nodes which do not usually
  carry position info. We set the ref here to ensure we log messages on the correct range. -/
  withRef (mkNullNode tacticSeq) do
    let stx ← `(tactic| $tacticSeq;*)
    -- TODO: support more than 1 g
-/
def testTacticSeq (config : ComplexConfig) (tacticSeq : Array (TSyntax `tactic))
    (i : TacticNode) (ctx : config.ctx) :
    CommandElabM Unit := do
  /- Syntax quotations use the current ref's position info even for nodes which do not usually
  carry position info. We set the ref here to ensure we log messages on the correct range. -/
  withRef (mkNullNode tacticSeq) do
    let stx ← `(tactic| $tacticSeq;*)
    -- TODO: support more than 1 goal. Probably by requiring all tests to succeed in a row
    if let [goal] := i.tacI.goalsBefore then
let (oldGoals, oldHeartbeats) ← withHeartbeats
        try
          i.runTacticCode goal stx
        catch e =>
          if !i.mayFail then
            logWarning m!"original tactic '{stx}' failed: {e.toMessageData}"
          return [goal]
let (new, newHeartbeats) ← withHeartbeats config.test i.ctxI i.tacI ctx goal
      if let some msg ← config.tell stx oldGoals oldHeartbeats new newHeartbeats then
        logWarning msg

/--
Definition of `runPass` / `runPass` 的定义

English:
definition runPass
  signature: (config : ComplexConfig) (seq : Array TacticNode)
  body: do
  let mut acc := none
  let mut firstInfo := none
  let mut tacticSeq := #[]
  for i in seq do
    if firstInfo.isNone then
      firstInfo := some i
    let stx : TSyntax `tactic := ⟨i.tacI.stx⟩
    tacticSeq := tacticSeq.push stx
    match config.trigger acc stx with
    | .continue ctx =>
    

中文:
定义 runPass
  签名: (config : 余mplexConfig) (seq : 数组 TacticNode)
  定义体: do
  let mut acc := none
  let mut firstInfo := none
  let mut tacticSeq := #[]
  for i in seq do
    if firstInfo.isNone then
      firstInfo := some i
    let stx : TSyntax `tactic := ⟨i.tacI.stx⟩
    tacticSeq := tacticSeq.push stx
    match config.trigger acc stx with
    | .continue ctx =>
    
-/
def runPass (config : ComplexConfig) (seq : Array TacticNode) :
    CommandElabM Unit := do
  let mut acc := none
  let mut firstInfo := none
  let mut tacticSeq := #[]
  for i in seq do
    if firstInfo.isNone then
      firstInfo := some i
    let stx : TSyntax `tactic := ⟨i.tacI.stx⟩
    tacticSeq := tacticSeq.push stx
    match config.trigger acc stx with
    | .continue ctx =>
      acc := ctx
    | .skip =>
      acc := none
      tacticSeq := #[]
      firstInfo := none
    | .accept ctx =>
      if let some i := firstInfo then
        testTacticSeq config tacticSeq i ctx
      else
        logWarningAt stx m!"internal error in tactic analysis: accepted an empty sequence."
      acc := none
  -- Insert a `done` at the end so we can handle a final `.continue` at the end.
  match config.trigger acc (← `(tactic| done)) with
  | .accept ctx =>
    if let some i := firstInfo then
      testTacticSeq config tacticSeq i ctx
  | _ => pure ()

/--
Definition of `Config.ofComplex` / `Config.ofComplex` 的定义

English:
definition Config.ofComplex
  signature: (config : ComplexConfig)
  body: runPass config

中文:
定义 余nfig.ofComplex
  签名: (config : 余mplexConfig)
  定义体: runPass config

Depends on / 依赖: config, runPass
-/
def Config.ofComplex (config : ComplexConfig) : Config where
  run := runPass config

end ComplexConfig

end Mathlib.TacticAnalysis

/-- A dummy option for testing the tactic analysis framework -/
register_option linter.tacticAnalysis.dummy : Bool := {
  defValue := false
}
