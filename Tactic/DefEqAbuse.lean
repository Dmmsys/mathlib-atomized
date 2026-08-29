/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Mathlib.Lean.MessageData.Trace

/-!
# The `#defeq_abuse` tactic and command combinators

**WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking changes to
transparency handling (associated with `backward.isDefEq.respectTransparency`). Its syntax may
change at any time, and it may not behave as expected. Please report unexpected behavior
[on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting, helping to diagnose where Mathlib relies on
definitional equality that isn't available at instance transparency.

`#defeq_abuse in cmd` does the same for commands (e.g. `instance` declarations), where
type class synthesis failures may occur during elaboration rather than during a tactic.
It additionally traces `Meta.synthInstance` to group `isDefEq` failures by the synthesis
application that triggered them.

## Usage

### Tactic mode
```
#defeq_abuse in rw [Set.disjoint_singleton_right]
```

will report something like:
```
Tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  (i : ℕ) → (fun a ↦ Prop) i =?= Set ℕ
```

### Command mode
```
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l
```

will report the synthesis failures grouped by instance application.
-/

meta section

open Lean MessageData Meta Elab Tactic Command

namespace Lean.MessageData

/- TODO: this section should be moved to `Lean.MessageData.Trace` when finalized and made public. -/

/--
Inductive type `VisitStep` / 归纳类型 `VisitStep`

English:
inductive VisitStep
  parameters: (α)

中文:
归纳类型 VisitStep
  参数: (α)
-/
inductive VisitStep (α) where
/-- Descends through the `MessageData`, visiting all children. If the argument `butFirst` is given
as `some a` (`none` by default), starts with `a`, and combines any values produced by children with
this value. -/
| descend (butFirst : Option α := none)
/-- Skips visiting children, and ascends to the parent, returning the value given in `returning`
(if any). -/
| ascend (returning : Option α := none)

variable {m : Type -> Type} [Monad m] {α : Type}

/--
Definition of `visitTraceNodesM` / `visitTraceNodesM` 的定义

English:
definition visitTraceNodesM
  signature: (msg : MessageData)
  body: go msg

中文:
定义 visitTraceNodesM
  签名: (msg : MessageData)
  定义体: go msg
-/
partial def visitTraceNodesM (msg : MessageData)
    (onTrace : TraceData -> MessageData -> Array MessageData -> m (MessageData.VisitStep α))
    (empty : α := by exact {}) (combine : α -> α -> α := by first | exact (· ++ ·) | exact (· union ·)) :
    m α :=
  go msg
where
  /-- The continuation for `visitTraceNodesM`; this is mainly for readability (takes only one
  argument in source). -/
  go : MessageData -> m α
    | .trace td header children => do
      match ← onTrace td header children with
      | .descend a? => do
        let mut result := a?.getD empty
        for child in children do
          result := combine result (← go child)
        return result
      | .ascend a? => return a?.getD empty
    | .compose a b => return combine (← go a) (← go b)
    | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m
    | .ofOriginatingSyntax _ m => go m
    | .ofLazy _ _ | .ofWidget _ _ | .ofGoal _ | .ofFormatWithInfos _ => return empty

/--
Definition of `visitWithM` / `visitWithM` 的定义

English:
definition visitWithM
  signature: {β} (arr : Array β) (visitM : β -> m α)
  body: arr.foldlM (init := empty) fun acc msg => return combine acc (← visitM msg)

中文:
定义 visitWithM
  签名: {β} (arr : Array β) (visitM : β -> m α)
  定义体: arr.foldlM (init := empty) fun acc msg => return combine acc (← visitM msg)
-/
@[inline] def visitWithM {β} (arr : Array β) (visitM : β -> m α)
    (empty : α := by exact {}) (combine : α -> α -> α := by first | exact (· ++ ·) | exact (· union ·)) :
    m α :=
  arr.foldlM (init := empty) fun acc msg => return combine acc (← visitM msg)

/--
Definition of `visitWithAndAscendM` / `visitWithAndAscendM` 的定义

English:
definition visitWithAndAscendM
  signature: {β} (arr : Array β) (visitM : β -> m α)
  body: do
  if arr.isEmpty then return .ascend else
return .ascend ← visitWithM arr visitM empty combine

中文:
定义 visitWithAndAscendM
  签名: {β} (arr : Array β) (visitM : β -> m α)
  定义体: do
  if arr.isEmpty then return .ascend else
return .ascend ← visitWithM arr visitM empty combine
-/
@[inline] def visitWithAndAscendM {β} (arr : Array β) (visitM : β -> m α)
    (empty : α := by exact {}) (combine : α -> α -> α := by first | exact (· ++ ·) | exact (· union ·)) :
    m (VisitStep α) := do
  if arr.isEmpty then return .ascend else
return .ascend ← visitWithM arr visitM empty combine

/--
Definition of `withPPOptions` / `withPPOptions` 的定义

English:
definition withPPOptions
  signature: (msg : MessageData) (modify : Options -> Options)
  body: match msg with
  | .withContext ctx d =>
    .withContext { ctx with opts := modify ctx.opts } (withPPOptions d modify)
  | .compose a b => .compose (withPPOptions a modify) (withPPOptions b modify)
  | .nest n m => .nest n (withPPOptions m modify)
  | .group m => .group (withPPOptions m modify)
  |

中文:
定义 withPPOptions
  签名: (msg : MessageData) (modify : Options -> Options)
  定义体: match msg with
  | .withContext ctx d =>
    .withContext { ctx with opts := modify ctx.opts } (withPPOptions d modify)
  | .compose a b => .compose (withPPOptions a modify) (withPPOptions b modify)
  | .nest n m => .nest n (withPPOptions m modify)
  | .group m => .group (withPPOptions m modify)
  |
-/
partial def withPPOptions (msg : MessageData) (modify : Options -> Options) : MessageData :=
  match msg with
  | .withContext ctx d =>
    .withContext { ctx with opts := modify ctx.opts } (withPPOptions d modify)
  | .compose a b => .compose (withPPOptions a modify) (withPPOptions b modify)
  | .nest n m => .nest n (withPPOptions m modify)
  | .group m => .group (withPPOptions m modify)
  | .tagged t m => .tagged t (withPPOptions m modify)
  | .ofOriginatingSyntax stx m => .ofOriginatingSyntax stx (withPPOptions m modify)
  | .withNamingContext nc m => .withNamingContext nc (withPPOptions m modify)
  | .trace td header children =>
    .trace td (withPPOptions header modify) (children.map (withPPOptions · modify))
  | .ofWidget w m => .ofWidget w (withPPOptions m modify)
  | other@(.ofLazy _ _)
  | other@(.ofFormatWithInfos _)
  | other@(.ofGoal _) => other

end Lean.MessageData

namespace Mathlib.Tactic.DefEqAbuse

/--
Definition of `onlyOnDefEqNodes` / `onlyOnDefEqNodes` 的定义

English:
definition onlyOnDefEqNodes
  signature: {m} [Monad m] {α}
  body: fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    unless (`Meta.isDefEq).isPrefixOf td.cls do return .descend
    f td header children

中文:
定义 onlyOnDefEqNodes
  签名: {m} [Monad m] {α}
  定义体: fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    unless (`Meta.isDefEq).isPrefixOf td.cls do return .descend
    f td header children
-/
@[inline] def onlyOnDefEqNodes {m} [Monad m] {α}
    (f : TraceData -> MessageData -> Array MessageData -> m (VisitStep α)) :
    TraceData -> MessageData -> Array MessageData -> m (VisitStep α) :=
  fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    unless (`Meta.isDefEq).isPrefixOf td.cls do return .descend
    f td header children

/--
Definition of `findLeafFailures` / `findLeafFailures` 的定义

English:
definition findLeafFailures
  signature: (msg : MessageData)
  body: msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do
      return .ascend
    let childFailures ← visitWithM children findLeafFailures
    -- Leaf failure: deepest `❌️` node with no deeper `❌️` children
return .ascend if childFailures.isEm

中文:
定义 findLeafFailures
  签名: (msg : MessageData)
  定义体: msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do
      return .ascend
    let childFailures ← visitWithM children findLeafFailures
    -- Leaf failure: deepest `❌️` node with no deeper `❌️` children
return .ascend if childFailures.isEm
-/
partial def findLeafFailures (msg : MessageData) : BaseIO (Array MessageData) :=
msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do
      return .ascend
    let childFailures ← visitWithM children findLeafFailures
    -- Leaf failure: deepest `❌️` node with no deeper `❌️` children
return .ascend if childFailures.isEmpty then #[header] else childFailures

/--
Definition of `collectIsDefEqChecks` / `collectIsDefEqChecks` 的定义

English:
definition collectIsDefEqChecks
  signature: (pred : Lean.TraceResult -> Bool)
  body: msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    if let some status := td.result? then
      if pred status then
        let headerStr ← header.toString
        return .descend (butFirst := some {headerStr})
    return .descend

中文:
定义 collectIsDefEqChecks
  签名: (pred : Lean.TraceResult -> 布尔)
  定义体: msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    if let some status := td.result? then
      if pred status then
        let headerStr ← header.toString
        return .descend (butFirst := some {headerStr})
    return .descend
-/
partial def collectIsDefEqChecks (pred : Lean.TraceResult -> Bool)
    (msg : MessageData) : BaseIO (Std.HashSet String) :=
msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    if let some status := td.result? then
      if pred status then
        let headerStr ← header.toString
        return .descend (butFirst := some {headerStr})
    return .descend

/--
Definition of `findTransitionFailures` / `findTransitionFailures` 的定义

English:
definition findTransitionFailures
  signature: (permSuccesses : Std.HashSet String)
  body: if permSuccesses.isEmpty then findLeafFailures msg
else msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do return .descend
    let headerStr ← header.toString
    if permSuccesses.contains headerStr && !permFailures.contains headerStr th

中文:
定义 findTransitionFailures
  签名: (permSuccesses : Std.HashSet String)
  定义体: if permSuccesses.isEmpty then findLeafFailures msg
else msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do return .descend
    let headerStr ← header.toString
    if permSuccesses.contains headerStr && !permFailures.contains headerStr th
-/
partial def findTransitionFailures (permSuccesses : Std.HashSet String)
    (permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array MessageData) :=
  if permSuccesses.isEmpty then findLeafFailures msg
else msg.visitTraceNodesM onlyOnDefEqNodes fun td header children => do
    unless td.result? matches some .failure do return .descend
    let headerStr ← header.toString
    if permSuccesses.contains headerStr && !permFailures.contains headerStr then
      -- Transition point: fails strict, succeeds permissive, doesn't also fail permissive.
      -- Look for deeper transition points among children.
let childTransitions ← visitWithM children
        findTransitionFailures permSuccesses permFailures
return .ascend
        -- Deepest transition point: no deeper transition-point children.
        if childTransitions.isEmpty then return #[header] else return childTransitions
    else
      -- Not a transition point (fails in both modes, strict-only, or ambiguous).
      -- Still recurse: children may contain transition points.
      return .descend

/--
Definition of `findSynthAppFailures` / `findSynthAppFailures` 的定义

English:
definition findSynthAppFailures
  signature: (permSuccesses permFailures : Std.HashSet String)
  body: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if td.result? matches some .failure && headerStr.contains "apply " then
let failures ← visitWithM child

中文:
定义 findSynthAppFailures
  签名: (permSuccesses permFailures : Std.HashSet String)
  定义体: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if td.result? matches some .failure && headerStr.contains "apply " then
let failures ← visitWithM child
-/
partial def findSynthAppFailures (permSuccesses permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array (MessageData × Array MessageData)) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if td.result? matches some .failure && headerStr.contains "apply " then
let failures ← visitWithM children
          findTransitionFailures permSuccesses permFailures
        if !failures.isEmpty then
          return .ascend #[(header, failures)]
    return .descend

/--
Definition of `findSynthFailures` / `findSynthFailures` 的定义

English:
definition findSynthFailures
  signature: (permSuccesses permFailures : Std.HashSet String)
  body: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      if td.result? matches some .failure then
visitWithAndAscendM children findSynthAppFailures permSuccesses permFailures
      else return .asce

中文:
定义 findSynthFailures
  签名: (permSuccesses permFailures : Std.HashSet String)
  定义体: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      if td.result? matches some .failure then
visitWithAndAscendM children findSynthAppFailures permSuccesses permFailures
      else return .asce
-/
partial def findSynthFailures (permSuccesses permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array (MessageData × Array MessageData)) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      if td.result? matches some .failure then
visitWithAndAscendM children findSynthAppFailures permSuccesses permFailures
      else return .ascend
    -- Skip isDefEq/synthInstance subtrees that aren't top-level synthesis
    else if !(`Meta.isDefEq).isPrefixOf td.cls && !(`Meta.synthInstance).isPrefixOf td.cls then
      return .descend
    else return .ascend

/--
Definition of `findSynthSuccessApps` / `findSynthSuccessApps` 的定义

English:
definition findSynthSuccessApps
  signature: (msg : MessageData)
  body: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && td.result? == some .success then
        return .descend (butFirst := some {extractInstName headerStr})
    return .descend

中文:
定义 findSynthSuccessApps
  签名: (msg : MessageData)
  定义体: msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && td.result? == some .success then
        return .descend (butFirst := some {extractInstName headerStr})
    return .descend
-/
partial def findSynthSuccessApps (msg : MessageData) : BaseIO (Std.HashSet String) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && td.result? == some .success then
        return .descend (butFirst := some {extractInstName headerStr})
    return .descend

/--
Definition of `analyzeTraces` / `analyzeTraces` 的定义

English:
definition analyzeTraces
  signature: (strictMsgs permMsgs : Array MessageData) (includeSynth : Bool := false)
  body: do
  -- Build sets of permissive successes and failures for transition-point detection.
  let mut permSuccesses : Std.HashSet String := {}
  let mut permFailures : Std.HashSet String := {}
  for msg in permMsgs do
    permSuccesses := permSuccesses.union (← collectIsDefEqChecks (· == .success) msg)


中文:
定义 analyzeTraces
  签名: (strictMsgs permMsgs : Array MessageData) (includeSynth : 布尔 := false)
  定义体: do
  -- Build sets of permissive successes and failures for transition-point detection.
  let mut permSuccesses : Std.HashSet String := {}
  let mut permFailures : Std.HashSet String := {}
  for msg in permMsgs do
    permSuccesses := permSuccesses.union (← collectIsDefEqChecks (· == .success) msg)

-/
def analyzeTraces (strictMsgs permMsgs : Array MessageData) (includeSynth : Bool := false) :
    BaseIO (Array MessageData × Array (MessageData × Array MessageData)) := do
  -- Build sets of permissive successes and failures for transition-point detection.
  let mut permSuccesses : Std.HashSet String := {}
  let mut permFailures : Std.HashSet String := {}
  for msg in permMsgs do
    permSuccesses := permSuccesses.union (← collectIsDefEqChecks (· == .success) msg)
    permFailures := permFailures.union (← collectIsDefEqChecks (· == .failure) msg)
  -- Find flat transition failures in strict traces.
  let mut transitionFailures : Array MessageData := #[]
  for msg in strictMsgs do
    transitionFailures := transitionFailures ++
      (← findTransitionFailures permSuccesses permFailures msg)
  let uniqueFailures ← dedupByString transitionFailures
  -- Optionally find synthesis-grouped failures.
  if !includeSynth then
    return (uniqueFailures, #[])
  let mut permissiveSuccessApps : Std.HashSet String := {}
  for msg in permMsgs do
    permissiveSuccessApps := permissiveSuccessApps.union (← findSynthSuccessApps msg)
  let mut synthResults : Array (MessageData × Array MessageData) := #[]
  for msg in strictMsgs do
    synthResults := synthResults.append
      (← findSynthFailures permSuccesses permFailures msg)
  -- Filter to only applications that succeed with permissive transparency.
  let filteredResults ← synthResults.filterM fun (app, _) => do
    return permissiveSuccessApps.contains (extractInstName (← app.toString))
  -- Dedup failures within each synth result.
  let dedupedResults ← filteredResults.mapM fun (app, failures) => do
    return (app, ← dedupByString failures)
  return (uniqueFailures, dedupedResults)

/--
Definition of `isIdenticalSidesStr` / `isIdenticalSidesStr` 的定义

English:
definition isIdenticalSidesStr
  signature: (raw : String)
  body: if let [lhs, rhs] := raw.splitOn " =?= " then
    -- Compare up to whitespace so that line-break differences don't cause false negatives.
    let tokenize (s : String) : List String :=
.filter (· != "") (s.split Char.isWhitespace).toList.map (·.toString)
    tokenize lhs == tokenize rhs
  else false

中文:
定义 isIdenticalSidesStr
  签名: (raw : String)
  定义体: if let [lhs, rhs] := raw.splitOn " =?= " then
    -- Compare up to whitespace so that line-break differences don't cause false negatives.
    let tokenize (s : String) : List String :=
.filter (· != "") (s.split Char.isWhitespace).toList.map (·.toString)
    tokenize lhs == tokenize rhs
  else false

Depends on / 依赖: raw.splitOn, splitOn
-/
def isIdenticalSidesStr (raw : String) : Bool :=
  if let [lhs, rhs] := raw.splitOn " =?= " then
    -- Compare up to whitespace so that line-break differences don't cause false negatives.
    let tokenize (s : String) : List String :=
.filter (· != "") (s.split Char.isWhitespace).toList.map (·.toString)
    tokenize lhs == tokenize rhs
  else false

/--
Definition of `ppEscalations` / `ppEscalations` 的定义

English:
definition ppEscalations
  signature: : List (Options -> Options)
  body: [ fun o => o.setBool `pp.universes true
  , fun o => o.setBool `pp.explicit true
  ]

中文:
定义 ppEscalations
  签名: : List (Options -> Options)
  定义体: [ fun o => o.setBool `pp.universes true
  , fun o => o.setBool `pp.explicit true
  ]

Depends on / 依赖: explicit, o.setBool, pp.explicit, pp.universes, setBool, universes
-/
def ppEscalations : List (Options -> Options) :=
  [ fun o => o.setBool `pp.universes true
  , fun o => o.setBool `pp.explicit true
  ]

/--
Definition of `disambiguateFailures` / `disambiguateFailures` 的定义

English:
definition disambiguateFailures
  signature: (failures : Array MessageData)
  body: failures.mapM fun f => do
    unless isIdenticalSidesStr (← f.toString) do return f
    for ppLevel in ppEscalations do
      let escalated := f.withPPOptions ppLevel
      unless isIdenticalSidesStr (← escalated.toString) do return escalated
    return f

中文:
定义 disambiguateFailures
  签名: (failures : Array MessageData)
  定义体: failures.mapM fun f => do
    unless isIdenticalSidesStr (← f.toString) do return f
    for ppLevel in ppEscalations do
      let escalated := f.withPPOptions ppLevel
      unless isIdenticalSidesStr (← escalated.toString) do return escalated
    return f

Depends on / 依赖: escalated, escalated.toString, f.toString, f.withPPOptions, failures, failures.mapM, isIdenticalSidesStr, ppEscalations, ppLevel, return, toString, unless, withPPOptions
-/
def disambiguateFailures (failures : Array MessageData) : BaseIO (Array MessageData) :=
  failures.mapM fun f => do
    unless isIdenticalSidesStr (← f.toString) do return f
    for ppLevel in ppEscalations do
      let escalated := f.withPPOptions ppLevel
      unless isIdenticalSidesStr (← escalated.toString) do return escalated
    return f

/--
Definition of `reportDefEqAbuse` / `reportDefEqAbuse` 的定义

English:
definition reportDefEqAbuse
  signature: {m : Type -> Type} [Monad m] [MonadLog m] [AddMessageContext m]
  body: do
  let failureEmoji := Lean.TraceResult.failure.toEmoji
  if !synthResults.isEmpty then
    -- Structured report: group by instance application
    let mut entries : Array MessageData := #[]
    for (app, failures) in synthResults do
      let failureList := joinSep
        (failures.toList.map fu

中文:
定义 reportDefEqAbuse
  签名: {m : Type -> Type} [Monad m] [MonadLog m] [AddMessageContext m]
  定义体: do
  let failureEmoji := Lean.TraceResult.failure.toEmoji
  if !synthResults.isEmpty then
    -- Structured report: group by instance application
    let mut entries : Array MessageData := #[]
    for (app, failures) in synthResults do
      let failureList := joinSep
        (failures.toList.map fu
-/
def reportDefEqAbuse {m : Type -> Type} [Monad m] [MonadLog m] [AddMessageContext m]
    [MonadOptions m] (kind : String) (uniqueFailures : Array MessageData)
    (synthResults : Array (MessageData × Array MessageData)) : m Unit := do
  let failureEmoji := Lean.TraceResult.failure.toEmoji
  if !synthResults.isEmpty then
    -- Structured report: group by instance application
    let mut entries : Array MessageData := #[]
    for (app, failures) in synthResults do
      let failureList := joinSep
        (failures.toList.map fun f => m!" {failureEmoji} {f}") "\n"
      entries := entries.push m!" {failureEmoji} {app}\n{failureList}"
    let report := joinSep entries.toList "\n"
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        The following synthesis applications fail due to transparency:\n{report}"
  else if uniqueFailures.isEmpty then
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        Could not identify specific failing isDefEq checks from traces."
  else
    let failureList := joinSep
      (uniqueFailures.toList.map fun f => m!" {failureEmoji} {f}") "\n"
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        The following isDefEq checks are the root causes of the failure:\n{failureList}"

/--
> **WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking
changes to transparency handling. Its syntax may change at any time, and it may not behave as
expected. Please report unexpected behavior [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.
-/
elab (name := defeqAbuse) "#defeq_abuse " "in " tac:tactic : tactic => withMainContext do
    let s ← saveState
    let oldTraces ← getTraces
    -- Helper: run tactic with given options and tracing, capturing traces.
    let runAndCapture (strict : Bool) :
        TacticM (Except MessageData Unit × PersistentArray TraceElem) := do
      modifyTraces (fun _ => {})
      let result ← try
        withOptions (fun o =>
            (o.setBool `backward.isDefEq.respectTransparency strict)
.setBool `trace.Meta.isDefEq true) do
          evalTactic tac
          pure (Except.ok ())
      catch
        | .internal id ref =>
          modifyTraces (fun _ => oldTraces)
          throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      let traces ← getTraces
      modifyTraces (fun _ => oldTraces)
      return (result, traces)
    -- Pass 1: strict + tracing.
    -- If it succeeds, no abuse; if it fails, we already have the traces.
    let (strictResult, strictTraces) ← runAndCapture true
    s.restore (restoreInfo := true)
    match strictResult with
    | .ok () =>
      -- Tactic works fine with strict setting, nothing to report.
      logInfo
        "#defeq_abuse: tactic succeeds with \
          `backward.isDefEq.respectTransparency true`. No abuse detected."
      -- Re-run without tracing so proof state is updated cleanly.
      withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) do
        evalTactic tac
    | .error _ =>
      -- Pass 2: permissive + tracing.
      -- If it fails, command fails regardless; if it succeeds, we have the traces.
      let (permissiveResult, permTraces) ← runAndCapture false
      s.restore (restoreInfo := true)
      match permissiveResult with
      | .error _ =>
        logWarning
          "#defeq_abuse: tactic fails regardless of \
            `backward.isDefEq.respectTransparency` setting."
        -- Still run the tactic so the user sees the original error
        evalTactic tac
      | .ok () =>
        let strictMsgs := strictTraces.toArray.map (·.msg)
        let permMsgs := permTraces.toArray.map (·.msg)
        let (uniqueFailures, _) ← analyzeTraces strictMsgs permMsgs
        let disambiguated ← disambiguateFailures uniqueFailures
        reportDefEqAbuse "tactic" disambiguated #[]
        -- Pass 3: run the tactic with permissive setting so it actually succeeds
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac

/--
> **WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking
changes to transparency handling. Its syntax may change at any time, and it may not behave as
expected. Please report unexpected behavior [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

`#defeq_abuse in cmd` runs `cmd` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the command succeeds with `false` but fails with `true`, it identifies the specific
synthesis applications and `isDefEq` checks that fail with the stricter setting.

This is useful for diagnosing `instance` declarations or other commands where type class synthesis
failures occur during elaboration rather than within a tactic.

The command is re-executed with the permissive setting so that it actually takes effect.
-/
syntax (name := defeqAbuseCmd) "#defeq_abuse " "in" command : command

elab_rules : command
  | `(command| #defeq_abuse in $cmd) => do
    let saved ← get
    -- Helper: run command with given scope options, capturing new messages.
    -- Returns (result, newMessages). elabCommand doesn't throw on synth failures,
    -- so we check the message log for errors.
    let runAndCapture (opts : Scope -> Scope) :
        CommandElabM (Except MessageData Unit × List Message) := do
      let savedMsgCount := (← get).messages.toList.length
      let result ← try
        withScope opts do
          elabCommand cmd
          if (← get).messages.hasErrors then
            pure (Except.error m!"command produced errors")
          else
            pure (Except.ok ())
      catch
        | .internal id ref => throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      let newMsgs := ((← get).messages.toList).drop savedMsgCount
      return (result, newMsgs)
    -- We set `Elab.async false` to force synchronous proof checking,
    -- otherwise `theorem` proofs are elaborated in a background task and errors
    -- won't appear in `messages` until after `elabCommand` returns.
    -- TODO: wait on all of the tasks instead of disabling async entirely.
    let traceOpts (strict : Bool) (scope : Scope) : Scope :=
      { scope with opts := (scope.opts.setBool `Elab.async false)
.setBool `backward.isDefEq.respectTransparency strict
.setBool `trace.Meta.isDefEq true
.setBool `trace.Meta.synthInstance true }
    -- Pass 1: strict + tracing.
    -- If it succeeds, no abuse; if it fails, we already have the traces.
    let (strictResult, strictMsgs) ← runAndCapture (traceOpts true)
    set saved
    match strictResult with
    | .ok () =>
      logInfo "#defeq_abuse: command succeeds with \
        `backward.isDefEq.respectTransparency true`. No abuse detected."
      elabCommand cmd
    | .error _ =>
      -- Pass 2: permissive + tracing.
      -- If it fails, command fails regardless; if it succeeds, we have the traces.
      let (permissiveResult, permissiveMsgs) ← runAndCapture (traceOpts false)
      set saved
      match permissiveResult with
      | .error _ =>
        logWarning "#defeq_abuse: command fails regardless of \
          `backward.isDefEq.respectTransparency` setting."
        elabCommand cmd
      | .ok () =>
.toArray let strictMsgData := strictMsgs.map (·.data)
.toArray let permMsgData := permissiveMsgs.map (·.data)
        let (uniqueFailures, synthResults) ←
          analyzeTraces strictMsgData permMsgData (includeSynth := true)
        let disambiguatedFailures ← disambiguateFailures uniqueFailures
        let disambiguatedSynth ← synthResults.mapM fun (app, failures) => do
          return (app, ← disambiguateFailures failures)
        reportDefEqAbuse "command" disambiguatedFailures disambiguatedSynth
        -- Pass 3: run the command with permissive setting so it actually takes effect
        withScope (fun scope =>
          { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency false }) do
          elabCommand cmd

end Mathlib.Tactic.DefEqAbuse
