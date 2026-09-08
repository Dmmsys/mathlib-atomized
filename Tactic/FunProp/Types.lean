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


/-- Indicated origin of a function or a statement. -/
/-
**Mathlib.Meta.FunProp.Origin** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.FunProp`
。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indicated origin of a function or a statement.
-/
inductive Origin where
  /-- It is a constant defined in the environment. -/
  | decl (name : Name)
  /-- It is a free variable in the local context. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq

/-- Name of the origin. -/
/-
**Mathlib.Meta.FunProp.Origin.name** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunPr
op.Origin`。
形式化陈述：Mathlib.Meta.FunProp.Origin → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Name of the origin.
-/
def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name

/-- Get the expression specified by `origin`. -/
/-
**Mathlib.Meta.FunProp.Origin.getValue** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.F
unProp.Origin`。
形式化陈述：Mathlib.Meta.FunProp.Origin → MetaM Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the expression specified by `origin`.
-/
def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

/-- Pretty print `FunProp.Origin`. -/
/-
**Mathlib.Meta.FunProp.ppOrigin** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunProp`
。
形式化陈述：{m : Type → Type} → [Monad m] → [MonadEnv m] → [MonadError m] → Mathlib.Me
ta.FunProp.Origin → m MessageData
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pretty print `FunProp.Origin`.
-/
def ppOrigin {m} [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n => return m!"{← mkConstWithLevelParams n}"
  | .fvar n => return mkFVar n

/-- Pretty print `FunProp.Origin`. Returns string unlike `ppOrigin`. -/
/-
**Mathlib.Meta.FunProp.ppOrigin'** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunProp
`。
形式化陈述：ppOrigin' (origin : Origin) : MetaM String
参数：origin : Origin。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pretty print `FunProp.Origin`. Returns string unlike `ppOrigin`.
-/
def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)

/-- Get origin of the head function. -/
/-
**Mathlib.Meta.FunProp.FunctionData.getFnOrigin** 是 Mathlib 中的一个定义，位于命名空间 `Mathl
ib.Meta.FunProp.FunctionData`。
形式化陈述：Mathlib.Meta.FunProp.FunctionData → Mathlib.Meta.FunProp.Origin
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get origin of the head function.
-/
def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

/-- Default names to be considered reducible by `fun_prop` -/
/-
**Mathlib.Meta.FunProp.defaultNamesToUnfold** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.FunProp`。
形式化陈述：defaultNamesToUnfold : Array Name
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Default names to be considered reducible by `fun_prop`
-/
def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]

/-- `fun_prop` configuration -/
/-
**Mathlib.Meta.FunProp.Config** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.FunProp`。
形式化陈述：Config where /-- Maximum number of transitions between function properties
. For example inferring continuity from differentiability and then differentiabi
lity from smoothness (`ContDiff ℝ ∞`) requires `maxTransitionDepth = 2`. The def
ault value of one expects that transition theorems are transitively closed e.g. 
there is a transition theorem that infers continuity directly from smoothness.  
Setting `maxTransitionDepth` to zero will disable all transition theorems. This 
can be very useful when `f
参数：`ContDiff ℝ ∞`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fun_prop` configuration -/
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

/-- `fun_prop` context -/
/-
**Mathlib.Meta.FunProp.Context** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.FunProp`。
形式化陈述：Context where /-- `fun_prop` config -/ config : Config
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fun_prop` context
-/
structure Context where
  /-- `fun_prop` config -/
  config : Config := {}
  /-- Name to unfold -/
  constToUnfold : TreeSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure none
  /-- current transition depth -/
  transitionDepth := 0

/-- General theorem about a function property used for transition and morphism theorems -/
/-
**Mathlib.Meta.FunProp.GeneralTheorem** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.Fu
nProp`。
形式化陈述：GeneralTheorem where /-- function property name -/ funPropName : Name /-- 
theorem name -/ thmName : Name /-- discrimination tree keys used to index this t
heorem -/ keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry) /-- pr
iority -/ priority : Nat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
General theorem about a function property used for transition and morphism theor
ems
-/
structure GeneralTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
  /-- priority -/
  priority : Nat  := eval_prio default
  deriving Inhabited

/-- Structure holding transition or morphism theorems for `fun_prop` tactic. -/
/-
**Mathlib.Meta.FunProp.GeneralTheorems** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.F
unProp`。
形式化陈述：GeneralTheorems where /-- Discrimination tree indexing theorems. -/ theore
ms : RefinedDiscrTree GeneralTheorem
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure holding transition or morphism theorems for `fun_prop` tactic.
-/
structure GeneralTheorems where
  /-- Discrimination tree indexing theorems. -/
  theorems : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/-- `fun_prop` state -/
/-
**Mathlib.Meta.FunProp.State** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.FunProp`。
形式化陈述：State where /-- Simp's cache is used as the `fun_prop` tactic is designed 
to be used inside of simp and utilize its cache. It holds successful goals. -/ c
ache : Simp.Cache
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fun_prop` state
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

/-- Increase depth -/
/-
**Mathlib.Meta.FunProp.Context.increaseTransitionDepth** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Meta.FunProp.Context`。
形式化陈述：Mathlib.Meta.FunProp.Context → Mathlib.Meta.FunProp.Context
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase depth
-/
def Context.increaseTransitionDepth (ctx : Context) : Context :=
  {ctx with transitionDepth := ctx.transitionDepth + 1}

/-- Monad to run `fun_prop` tactic in. -/
/-
**Mathlib.Meta.FunProp.FunPropM** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Meta.FunPro
p`。
形式化陈述：FunPropM
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monad to run `fun_prop` tactic in.
-/
abbrev FunPropM := ReaderT FunProp.Context <| StateT FunProp.State MetaM

set_option linter.style.docString.empty false in
/-- Result of `funProp`, it is a proof of function property `P f` -/
/-
**Mathlib.Meta.FunProp.Result** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.FunProp`
。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Result of `funProp`, it is a proof of function property `P f`
-/
structure Result where
  /-- -/
  proof : Expr

/-- Default names to unfold -/
/-
**Mathlib.Meta.FunProp.defaultUnfoldPred** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta
.FunProp`。
形式化陈述：defaultUnfoldPred : Name -> Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Default names to unfold
-/
def defaultUnfoldPred : Name → Bool :=
  defaultNamesToUnfold.contains

/-- Get predicate on names indicating whether they should be unfolded. -/
/-
**Mathlib.Meta.FunProp.unfoldNamePred** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Fu
nProp`。
形式化陈述：unfoldNamePred : FunPropM (Name -> Bool)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get predicate on names indicating whether they should be unfolded.
-/
def unfoldNamePred : FunPropM (Name → Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

/-- Increase heartbeat, throws error when `maxSteps` was reached -/
/-
**Mathlib.Meta.FunProp.increaseSteps** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Fun
Prop`。
形式化陈述：increaseSteps : FunPropM Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase heartbeat, throws error when `maxSteps` was reached
-/
def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

/-- Increase transition depth. Return `none` if maximum transition depth has been reached. -/
/-
**Mathlib.Meta.FunProp.withIncreasedTransitionDepth** 是 Mathlib 中的一个定义，位于命名空间 `M
athlib.Meta.FunProp`。
形式化陈述：withIncreasedTransitionDepth {α} (go : FunPropM (Option α)) : FunPropM (Op
tion α)
参数：go : FunPropM (Option α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase transition depth. Return `none` if maximum transition depth has been re
ached.
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

/-- Log error message that will displayed to the user at the end.

Messages are logged only when `transitionDepth = 0` i.e. when `fun_prop` is **not** trying to infer
function property like continuity from another property like differentiability.
The main reason is that if the user forgets to add a continuity theorem for function `foo` then
`fun_prop` should report that there is a continuity theorem for `foo` missing. If we would log
messages `transitionDepth > 0` then user will see messages saying that there is a missing theorem
for differentiability, smoothness, ... for `foo`. -/
/-
**Mathlib.Meta.FunProp.logError** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunProp`
。
形式化陈述：logError (msg : String) : FunPropM Unit
参数：msg : String。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Log error message that will displayed to the user at the end.

Messages are logged only when `transitionDepth = 0` i.e. when `fun_prop` is **no
t** trying to infer
function property like continuity from another property like differentiability.
The main reason is that if the user forgets to add a continuity theorem for func
tion `foo` then
`fun_prop` should report that there is a continuity theorem for `foo` missing. I
f we would log
messages `transitionDepth > 0` then user will see messages saying that there is 
a missing theorem
for differentiability, smoothness, ... for `foo`.
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

