/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.Util
public import ProofWidgets.Component.FilterDetails

/-!
# Infrastructure for searching and displaying sets of lemmas

This is used for `apply`, `apply at`, `rw` and `grw` suggestions.
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions
open Lean Widget ProofWidgets Jsx

/--
Definition of `Result` / `Result` 的定义

English:
structure Result
  parameters: (α : Type)
  axioms and operations (4):
    - filtered : Option Html
    - unfiltered : Html
    - key : α
    - pattern : Html

中文:
结构 Result
  参数: (α : 类型)
  公理与运算 (4 个):
    - filtered : 选项类型 Html
    - unfiltered : Html
    - key : α
    - pattern : Html
-/
structure Result (α : Type) where
  /-- `filtered` will be shown in the filtered view. -/
  filtered : Option Html
  /-- `unfiltered` will be shown in the unfiltered view. -/
  unfiltered : Html
  /-- `key` is used for sorting and comparing theorems. -/
  key : α
  /-- The `pattern` of the first lemma in a section is shown as the header of that section. -/
  pattern : Html
deriving Inhabited

variable {α : Type} [Ord α] [Inhabited α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ord (Result α)
  body: ⟨(compare ·.key ·.key)⟩

中文:
实例 :
  签名: 序 (Result α)
  定义体: ⟨(compare ·.key ·.key)⟩

Depends on / 依赖: compare
-/
instance : Ord (Result α) := ⟨(compare ·.key ·.key)⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LT (Result α)
  body: ltOfOrd

中文:
实例 :
  签名: LT (Result α)
  定义体: ltOfOrd

Depends on / 依赖: ltOfOrd
-/
instance : LT (Result α) := ltOfOrd

/-! ### Maintaining the state of the widget -/

/--
Definition of `SectionState` / `SectionState` 的定义

English:
structure SectionState
  parameters: (α : Type)
  axioms and operations (2):
    - results : Array (Result α)  [default: #[]]
    - errors : Array Html  [default: #[]]

中文:
结构 SectionState
  参数: (α : 类型)
  公理与运算 (2 个):
    - results : 数组 (Result α)  [默认: #[]]
    - errors : 数组 Html  [默认: #[]]
-/
structure SectionState (α : Type) where
  /-- The results of the theorems that successfully applied. -/
  results : Array (Result α) := #[]
  /-- The results of the theorems that threw an error when trying to apply them.
  Usually, errors will be caught, except for when using `click_suggestions.debug`. -/
  errors : Array Html := #[]
  deriving Nonempty

/-- Insert the new result `res` into the array `arr` of already existing results.

We maintain the invariants that `results` is sorted, and for each set of duplicate results,
only the first one can have the `filtered` field set to `some`. -/
@[specialize]
/--
Definition of `Result.insertInArray` / `Result.insertInArray` 的定义

English:
definition Result.insertInArray
  signature: (res : Result α) (arr : Array (Result α)) (isDup : α -> α -> MetaM Bool)
  body: do
  if let some idx ← findDuplicate res arr then
    if res < arr[idx]! then
      return (arr.modify idx ({ · with filtered := none })).binInsert (· < ·) res
    else
      return arr.binInsert (· < ·) { res with filtered := none }
  else
    return arr.binInsert (· < ·) res

中文:
定义 Result.insertInArray
  签名: (res : Result α) (arr : 数组 (Result α)) (isDup : α -> α -> MetaM 布尔值)
  定义体: do
  if let some idx ← findDuplicate res arr then
    if res < arr[idx]! then
      return (arr.modify idx ({ · with filtered := none })).binInsert (· < ·) res
    else
      return arr.binInsert (· < ·) { res with filtered := none }
  else
    return arr.binInsert (· < ·) res
-/
def Result.insertInArray (res : Result α) (arr : Array (Result α)) (isDup : α -> α -> MetaM Bool) :
    MetaM (Array (Result α)) := do
  if let some idx ← findDuplicate res arr then
    if res < arr[idx]! then
      return (arr.modify idx ({ · with filtered := none })).binInsert (· < ·) res
    else
      return arr.binInsert (· < ·) { res with filtered := none }
  else
    return arr.binInsert (· < ·) res
where
  /-- Check if there is already a duplicate of `result` in `results`,
  for which both appear in the filtered view. -/
  findDuplicate (result : Result α) (results : Array (Result α)) : MetaM (Option Nat) := do
    unless result.filtered.isSome do
      return none
    results.findIdxM? fun res =>
      try
        pure res.filtered.isSome <&&> isDup res.key result.key
      catch _ =>
        pure false

/--
Definition of `SectionState.insertResult` / `SectionState.insertResult` 的定义

English:
definition SectionState.insertResult
  signature: (s : SectionState α) (res : Result α)
  body: do
  let { results, errors } := s
  let results ← fun c₁ c₂ c₃ c₄ =>
    (res.insertInArray results isDup c₁ c₂ c₃ c₄).catchExceptions fun ex => do
    if let .internal id _ := ex then
      if id == interruptExceptionId then
        return default
    panic! s!"an error occurred when checking for d

中文:
定义 SectionState.insertResult
  签名: (s : SectionState α) (res : Result α)
  定义体: do
  let { results, errors } := s
  let results ← fun c₁ c₂ c₃ c₄ =>
    (res.insertInArray results isDup c₁ c₂ c₃ c₄).catchExceptions fun ex => do
    if let .internal id _ := ex then
      if id == interruptExceptionId then
        return default
    panic! s!"an error occurred when checking for d
-/
def SectionState.insertResult (s : SectionState α) (res : Result α)
    (isDup : α -> α -> MetaM Bool) : MetaM (SectionState α) := do
  let { results, errors } := s
  let results ← fun c₁ c₂ c₃ c₄ =>
    (res.insertInArray results isDup c₁ c₂ c₃ c₄).catchExceptions fun ex => do
    if let .internal id _ := ex then
      if id == interruptExceptionId then
        return default
    panic! s!"an error occurred when checking for duplicate entries:\n{← ex.toMessageData.toString}"
  return { results, errors }

/--
Inductive type `SectionKind` / 归纳类型 `SectionKind`

English:
inductive SectionKind
  parameters: where
  constructors (1):
    - hyp: | currFile | imported

中文:
归纳类型 SectionKind
  参数: where
  构造子 (1 个):
    - hyp: | currFile | imported
-/
inductive SectionKind where
  | hyp | currFile | imported

-- TODO?: add a `⏳️` with hover info that shows which lemmas are still being computed?
/--
Definition of `renderSection` / `renderSection` 的定义

English:
definition renderSection
  signature: (tactic : String) (kind : SectionKind) (s : SectionState α)
  body: Id.run do
  let { results, errors } := s
  if results.isEmpty && errors.isEmpty then
    return .text ""
  let pattern := if let some head := results[0]? then head.pattern else .text ""
let mut all := .element "div" #[] results.map (·.unfiltered)
let mut filtered := .element "div" #[] results.filter

中文:
定义 renderSection
  签名: (tactic : String) (kind : SectionKind) (s : SectionState α)
  定义体: Id.run do
  let { results, errors } := s
  if results.isEmpty && errors.isEmpty then
    return .text ""
  let pattern := if let some head := results[0]? then head.pattern else .text ""
let mut all := .element "div" #[] results.map (·.unfiltered)
let mut filtered := .element "div" #[] results.filter

Depends on / 依赖: Id.run
-/
def renderSection (tactic : String) (kind : SectionKind) (s : SectionState α) : Html := Id.run do
  let { results, errors } := s
  if results.isEmpty && errors.isEmpty then
    return .text ""
  let pattern := if let some head := results[0]? then head.pattern else .text ""
let mut all := .element "div" #[] results.map (·.unfiltered)
let mut filtered := .element "div" #[] results.filterMap (·.filtered)
  unless errors.isEmpty do
    all := <div> {all} {renderErrors errors} </div>
    filtered := <div> {filtered} {renderErrors errors} </div>
  let suffix := match kind with
    | .hyp => " (local hypotheses)"
    | .currFile => " (current file)"
    | .imported => ""
  let header := <span> {.text s!"{tactic} ("} {pattern} {.text ")"} {.text suffix} </span>
  if kind matches .imported then
    return <FilterDetails summary={header} all={all} filtered={filtered} initiallyFiltered={true} />
  else
    -- We don't filter local results, because there aren't that many of them.
    return <details «open»={true}> <summary> {header} </summary> {all} </details>
where
  renderErrors (errors : Array Html) : Html :=
    <details «open»={true}>
      <summary className="mv2 pointer">
        <span «class»="error"> Failures: </span>
      </summary>
      {Html.element "ul" #[("style", json% { "padding-left" : "30px"})] errors}
    </details>

/-- Spawn a task that computes a piece of `Html` to be displayed when finished. -/
@[specialize]
/--
Definition of `spawnTask` / `spawnTask` 的定义

English:
definition spawnTask
  signature: {α} (premise : Premise) (k : ClickSuggestionsM α)
  body: do
  let premiseHtml ← premise.toHtml
  let act ← saveCtxM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
  

中文:
定义 spawnTask
  签名: {α} (premise : Premise) (k : ClickSuggestionsM α)
  定义体: do
  let premiseHtml ← premise.toHtml
  let act ← saveCtxM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
  
-/
def spawnTask {α} (premise : Premise) (k : ClickSuggestionsM α) :
ClickSuggestionsM Task (Except Html (Option α)) := do
  let premiseHtml ← premise.toHtml
  let act ← saveCtxM do
    /- Since this task may have been on the queue for a while,
    the first thing we do is check if it has been cancelled already. -/
    Core.checkInterrupted
    /- Each thread counts its own number of heartbeats, so it is important
    to use `withCurrHeartbeats` to avoid stray maxHeartbeats errors. -/
    withCurrHeartbeats do
      try
        return .ok (some (← k))
      catch ex =>
        /- By default, we catch the errors from failed lemma applications
        (apart from runtime exceptions, i.e. max heartbeats or max recursion depth,
        which aren't caught by the `try`-`catch` block).
        The `click_suggestions.debug` option allows the user to still see all errors. -/
        if click_suggestions.debug.get (← getOptions) then
          throw ex
        return .ok none
BaseIO.asTask act.catchExceptions fun ex =>
    return .error <li>
        {premiseHtml} failed:
        <br/>
        <InteractiveMessage msg={← Server.WithRpcRef.mk ex.toMessageData} />
      </li>

end Mathlib.Tactic.ClickSuggestions
