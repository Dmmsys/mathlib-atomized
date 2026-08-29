/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
public import Mathlib.Tactic.FunProp.FunctionData

/-!
## `funProp`

this file defines environment extension for `funProp`
-/

public meta section


namespace Mathlib
open Lean Meta
open Std (TreeSet)

namespace Meta.FunProp

initialize registerTraceClass `Meta.Tactic.fun_prop
initialize registerTraceClass `Meta.Tactic.fun_prop.attr
initialize registerTraceClass `Debug.Meta.Tactic.fun_prop


/--
Inductive type `Origin` / 归纳类型 `Origin`

English:
inductive Origin
  parameters: where
  constructors (2):
    - decl: (name : Name)
    - fvar: (fvarId : FVarId)

中文:
归纳类型 Origin
  参数: where
  构造子 (2 个):
    - decl: (name : Name)
    - fvar: (fvarId : FVarId)
-/
inductive Origin where
  /-- It is a constant defined in the environment. -/
  | decl (name : Name)
  /-- It is a free variable in the local context. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq

/--
Definition of `Origin.name` / `Origin.name` 的定义

English:
definition Origin.name
  signature: (origin : Origin)
  body: match origin with
  | .decl name => name
  | .fvar id => id.name

中文:
定义 Origin.name
  签名: (origin : Origin)
  定义体: match origin with
  | .decl name => name
  | .fvar id => id.name

Depends on / 依赖: id.name, origin
-/
def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name

/--
Definition of `Origin.getValue` / `Origin.getValue` 的定义

English:
definition Origin.getValue
  signature: (origin : Origin)
  body: do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

中文:
定义 Origin.getValue
  签名: (origin : Origin)
  定义体: do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)
-/
def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

/--
Definition of `ppOrigin` / `ppOrigin` 的定义

English:
definition ppOrigin
  signature: {m} [Monad m] [MonadEnv m] [MonadError m]

中文:
定义 ppOrigin
  签名: {m} [Monad m] [MonadEnv m] [MonadError m]
-/
def ppOrigin {m} [Monad m] [MonadEnv m] [MonadError m] : Origin -> m MessageData
  | .decl n => return m!"{← mkConstWithLevelParams n}"
  | .fvar n => return mkFVar n

/--
Definition of `ppOrigin'` / `ppOrigin'` 的定义

English:
definition ppOrigin'
  signature: (origin : Origin)
  body: do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)

中文:
定义 ppOrigin'
  签名: (origin : Origin)
  定义体: do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)
-/
def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)

/--
Definition of `FunctionData.getFnOrigin` / `FunctionData.getFnOrigin` 的定义

English:
definition FunctionData.getFnOrigin
  signature: (fData : FunctionData)
  body: match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

中文:
定义 FunctionData.getFnOrigin
  签名: (fData : FunctionData)
  定义体: match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

Depends on / 依赖: Name.anonymous, anonymous, fData.fn
-/
def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

/--
Definition of `defaultNamesToUnfold` / `defaultNamesToUnfold` 的定义

English:
definition defaultNamesToUnfold
  signature: : Array Name
  body: #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]

中文:
定义 defaultNamesToUnfold
  签名: : Array Name
  定义体: #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]

Depends on / 依赖: Function, Function.HasUncurry.uncurry, Function.comp, Function.const, Function.uncurry, HasUncurry, uncurry
-/
def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]

/--
Definition of `Config` / `Config` 的定义

English:
structure Config
  parameters: where
  axioms and operations (2):
    - maxTransitionDepth : = 1
    - maxSteps : = 100000

中文:
结构 Config
  参数: where
  公理与运算 (2 个):
    - maxTransitionDepth : = 1
    - maxSteps : = 100000
-/
structure Config where
  /-- Maximum number of transitions between function properties. For example inferring continuity
  from differentiability and then differentiability from smoothness (`ContDiff ℝ ∞`) requires
  `maxTransitionDepth = 2`. The default value of one expects that transition theorems are
  transitively closed e.g. there is a transition theorem that infers continuity directly from
  smoothness.

  Setting `maxTransitionDepth` to zero will disable all transition theorems. This can be very
  useful when `fun_prop` should fail quickly. For example when using `fun_prop` as discharger in
  `simp`.
  -/
  maxTransitionDepth := 1
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000
deriving Inhabited, BEq

/--
Definition of `Context` / `Context` 的定义

English:
structure Context
  parameters: where
  axioms and operations (4):
    - config : Config  [default: {}]
    - constToUnfold : TreeSet Name Name.quickCmp  [default: .ofArray defaultNamesToUnfold _]
    - disch : Expr -> MetaM (Option Expr)  [default: fun _ => pure none]
    - transitionDepth : = 0

中文:
结构 Context
  参数: where
  公理与运算 (4 个):
    - config : Config  [默认: {}]
    - constToUnfold : TreeSet Name Name.quickCmp  [默认: .ofArray defaultNamesToUnfold _]
    - disch : Expr -> MetaM (Option Expr)  [默认: fun _ => pure none]
    - transitionDepth : = 0
-/
structure Context where
  /-- `fun_prop` config -/
  config : Config := {}
  /-- Name to unfold -/
  constToUnfold : TreeSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr -> MetaM (Option Expr) := fun _ => pure none
  /-- current transition depth -/
  transitionDepth := 0

/--
Definition of `GeneralTheorem` / `GeneralTheorem` 的定义

English:
structure GeneralTheorem
  parameters: where
  axioms and operations (4):
    - funPropName : Name
    - thmName : Name
    - keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
    - priority : Nat  [default: eval_prio default]

中文:
结构 GeneralTheorem
  参数: where
  公理与运算 (4 个):
    - funPropName : Name
    - thmName : Name
    - keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
    - priority : 自然数  [默认: eval_prio default]

Depends on / 依赖: eval_prio
-/
structure GeneralTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
  /-- priority -/
  priority : Nat := eval_prio default
  deriving Inhabited

/--
Definition of `GeneralTheorems` / `GeneralTheorems` 的定义

English:
structure GeneralTheorems
  parameters: where
  axioms and operations (1):
    - theorems : RefinedDiscrTree GeneralTheorem  [default: {}]

中文:
结构 GeneralTheorems
  参数: where
  公理与运算 (1 个):
    - theorems : RefinedDiscrTree GeneralTheorem  [默认: {}]
-/
structure GeneralTheorems where
  /-- Discrimination tree indexing theorems. -/
  theorems : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/--
Definition of `State` / `State` 的定义

English:
structure State
  parameters: where
  axioms and operations (6):
    - cache : Simp.Cache  [default: {}]
    - failureCache : ExprSet  [default: {}]
    - numSteps : = 0
    - msgLog : List String  [default: []]
    - morTheorems : GeneralTheorems
    - transitionTheorems : GeneralTheorems

中文:
结构 State
  参数: where
  公理与运算 (6 个):
    - cache : Simp.Cache  [默认: {}]
    - failureCache : ExprSet  [默认: {}]
    - numSteps : = 0
    - msgLog : List String  [默认: []]
    - morTheorems : GeneralTheorems
    - transitionTheorems : GeneralTheorems
-/
structure State where
  /-- Simp's cache is used as the `fun_prop` tactic is designed to be used inside of simp and
  utilize its cache. It holds successful goals. -/
  cache : Simp.Cache := {}
  /-- Cache storing failed goals such that they are not tried again. -/
  failureCache : ExprSet := {}
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0
  /-- Log progress and failures messages that should be displayed to the user at the end. -/
  msgLog : List String := []
  /-- `RefinedDiscrTree` is lazy, so we store the partially evaluated tree. -/
  morTheorems : GeneralTheorems
  /-- `RefinedDiscrTree` is lazy, so we store the partially evaluated tree. -/
  transitionTheorems : GeneralTheorems

/--
Definition of `Context.increaseTransitionDepth` / `Context.increaseTransitionDepth` 的定义

English:
definition Context.increaseTransitionDepth
  signature: (ctx : Context)
  body: {ctx with transitionDepth := ctx.transitionDepth + 1}

中文:
定义 Context.increaseTransitionDepth
  签名: (ctx : Context)
  定义体: {ctx with transitionDepth := ctx.transitionDepth + 1}

Depends on / 依赖: ctx.transitionDepth, transitionDepth
-/
def Context.increaseTransitionDepth (ctx : Context) : Context :=
  {ctx with transitionDepth := ctx.transitionDepth + 1}

/--
Definition of `FunPropM` / `FunPropM` 的定义

English:
abbreviation FunPropM
  body: ReaderT FunProp.Context StateT FunProp.State MetaM

中文:
缩写 FunPropM
  定义体: ReaderT FunProp.Context StateT FunProp.State MetaM

Depends on / 依赖: Context, FunProp, FunProp.Context, FunProp.State, ReaderT, StateT
-/
abbrev FunPropM := ReaderT FunProp.Context StateT FunProp.State MetaM

set_option linter.style.docString.empty false in
/--
Definition of `Result` / `Result` 的定义

English:
structure Result
  parameters: where
  axioms and operations (1):
    - proof : Expr

中文:
结构 Result
  参数: where
  公理与运算 (1 个):
    - proof : Expr
-/
structure Result where
  /-- -/
  proof : Expr

/--
Definition of `defaultUnfoldPred` / `defaultUnfoldPred` 的定义

English:
definition defaultUnfoldPred
  signature: : Name -> Bool
  body: defaultNamesToUnfold.contains

中文:
定义 defaultUnfoldPred
  签名: : Name -> 布尔
  定义体: defaultNamesToUnfold.contains

Depends on / 依赖: contains, defaultNamesToUnfold, defaultNamesToUnfold.contains
-/
def defaultUnfoldPred : Name -> Bool :=
  defaultNamesToUnfold.contains

/--
Definition of `unfoldNamePred` / `unfoldNamePred` 的定义

English:
definition unfoldNamePred
  signature: : FunPropM (Name -> Bool)
  body: do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

中文:
定义 unfoldNamePred
  签名: : Fun命题M (Name -> 布尔)
  定义体: do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n
-/
def unfoldNamePred : FunPropM (Name -> Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

/--
Definition of `increaseSteps` / `increaseSteps` 的定义

English:
definition increaseSteps
  signature: : FunPropM Unit
  body: do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

中文:
定义 increaseSteps
  签名: : Fun命题M Unit
  定义体: do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})
-/
def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

/--
Definition of `withIncreasedTransitionDepth` / `withIncreasedTransitionDepth` 的定义

English:
definition withIncreasedTransitionDepth
  signature: {α} (go : FunPropM (Option α))
  body: do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
    "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `f

中文:
定义 withIncreasedTransitionDepth
  签名: {α} (go : Fun命题M (Option α))
  定义体: do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
    "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `f
-/
def withIncreasedTransitionDepth {α} (go : FunPropM (Option α)) : FunPropM (Option α) := do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
    "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `fun_prop (maxTransitionDepth := {newDepth})`"
    return none
  else
    withReader (fun s => {s with transitionDepth := newDepth}) go

/--
Definition of `logError` / `logError` 的定义

English:
definition logError
  signature: (msg : String)
  body: do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}

中文:
定义 logError
  签名: (msg : String)
  定义体: do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}
-/
def logError (msg : String) : FunPropM Unit := do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}

end Meta.FunProp

end Mathlib
