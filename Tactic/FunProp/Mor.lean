/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public import Mathlib.Init
public meta import Lean.Meta.CoeAttr
public import Lean.Meta.CoeAttr

/-!
## `funProp` Meta programming functions like in Lean.Expr.* but for working with bundled morphisms.

Function application in normal lean expression looks like `.app f x` but when we work with bundled
morphism `f` it looks like `.app (.app coe f) x` where `f`. In mathlib `coe` is usually
`DFunLike.coe` but it can be any coercion that is registered with the `coe` attribute.

The main difference when working with expression involving morphisms is that the notion the head of
expression changes. For example in:
```
  coe (f a) b
```
the head of expression is considered to be `f` and not `coe`.
-/

public meta section

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

/-- An abbreviation of `∀ x, p x`. It is used by `fun_prop` to represent Pi types as function
applications and should not occur in any place other than the implementation of `fun_prop`. -/
/-
**Mathlib.Meta.FunProp.Forall** 是 Mathlib 中的一个缩写定义，位于命名空间 `Mathlib.Meta.FunProp`
。
形式化陈述：Forall {α : Sort*} (p : α -> Sort*)
参数：p : α -> Sort*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation of `∀ x, p x`. It is used by `fun_prop` to represent Pi types as
 function
applications and should not occur in any place other than the implementation of 
`fun_prop`.
-/
abbrev Forall {α : Sort*} (p : α → Sort*) := ∀ x, p x

namespace Mor

/-- Is `name` a coercion from some function space to functions? -/
/-
**Mathlib.Meta.FunProp.Mor.isCoeFunName** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
FunProp.Mor`。
形式化陈述：isCoeFunName (name : Name) : CoreM Bool
参数：name : Name。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Is `name` a coercion from some function space to functions?
-/
def isCoeFunName (name : Name) : CoreM Bool := do
  let some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun

/-- Is `e` a coercion from some function space to functions? -/
/-
**Mathlib.Meta.FunProp.Mor.isCoeFun** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunP
rop.Mor`。
形式化陈述：isCoeFun (e : Expr) : MetaM Bool
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Is `e` a coercion from some function space to functions?
-/
def isCoeFun (e : Expr) : MetaM Bool := do
  let some (name, _) := e.getAppFn.const? | return false
  let some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs

/-- Morphism application -/
/-
**Mathlib.Meta.FunProp.Mor.App** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Meta.FunProp
.Mor`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphism application
-/
structure App where
  /-- morphism coercion -/
  coe : Expr
  /-- bundled morphism -/
  fn  : Expr
  /-- morphism argument -/
  arg : Expr

/-- Is `e` morphism application? -/
/-
**Mathlib.Meta.FunProp.Mor.isMorApp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunP
rop.Mor`。
形式化陈述：isMorApp? (e : Expr) : MetaM (Option App)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Is `e` morphism application?
-/
def isMorApp? (e : Expr) : MetaM (Option App) := do

  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return some { coe := coe, fn := f, arg := x }
  else
    return none

/--
Weak normal head form of an expression involving morphism applications. Additionally, `pred`
can specify which when to unfold definitions.

For example calling this on `coe (f a) b` will put `f` in weak normal head form instead of `coe`.
-/
/-
**Mathlib.Meta.FunProp.Mor.whnfPred** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Meta.F
unProp.Mor`。
形式化陈述：Expr → (Expr → MetaM Bool) → MetaM Expr
参数：Expr → MetaM Bool。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weak normal head form of an expression involving morphism applications. Addition
ally, `pred`
can specify which when to unfold definitions.

For example calling this on `coe (f a) b` will put `f` in weak normal head form 
instead of `coe`.
-/
partial def whnfPred (e : Expr) (pred : Expr → MetaM Bool) :
    MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e

    if let some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred
      if (← getConfig).zeta then
        return (coe.app f).app x
      else
        return ← mapLetTelescope f fun _ f' => pure ((coe.app f').app x)

    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfPred e pred
        | none   => return e
    else
      return e

/--
Weak normal head form of an expression involving morphism applications.

For example calling this on `coe (f a) b` will put `f` in weak normal head form instead of `coe`.
-/
/-
**Mathlib.Meta.FunProp.Mor.whnf** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunProp.
Mor`。
形式化陈述：whnf (e : Expr) : MetaM Expr
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weak normal head form of an expression involving morphism applications.

For example calling this on `coe (f a) b` will put `f` in weak normal head form 
instead of `coe`.
-/
def whnf (e : Expr) : MetaM Expr :=
  whnfPred e (fun _ => return false)


/-- Argument of morphism application that stores corresponding coercion if necessary -/
/-
**Mathlib.Meta.FunProp.Mor.Arg** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Meta.FunProp.M
or`。
形式化陈述：Arg where /-- argument of type `α` -/ expr : Expr /-- coercion `F → α → β`
 -/ coe : Option Expr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Argument of morphism application that stores corresponding coercion if necessary
-/
structure Arg where
  /-- argument of type `α` -/
  expr : Expr
  /-- coercion `F → α → β` -/
  coe : Option Expr := none
  deriving Inhabited

/-- Morphism application -/
/-
**Mathlib.Meta.FunProp.Mor.app** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunProp.M
or`。
形式化陈述：app (f : Expr) (arg : Arg) : Expr
参数：f : Expr；arg : Arg。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphism application
-/
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | none => f.app arg.expr
  | some coe => (coe.app f).app arg.expr


/-- Given `e = f a₁ a₂ ... aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundled morphism.

`∀ x, p x` is represented as `Forall p`. -/
/-
**Mathlib.Meta.FunProp.Mor.withApp** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunPr
op.Mor`。
形式化陈述：{α : Type} → Expr → (Expr → Array Mathlib.Meta.FunProp.Mor.Arg → MetaM α) 
→ MetaM α
参数：Expr → Array Mathlib.Meta.FunProp.Mor.Arg → MetaM α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `e = f a₁ a₂ ... aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundle
d morphism.

`∀ x, p x` is represented as `Forall p`.
-/
partial def withApp {α} (e : Expr) (k : Expr → Array Arg → MetaM α) : MetaM α :=
  go e #[]
where
  /-- -/
  go : Expr → Array Arg →  MetaM α
    | .mdata _ b, as => go b as
    | .app (.app c f) x, as => do
      if ← isCoeFun c then
        go f (as.push { coe := c, expr := x})
      else
        go (.app c f) (as.push { expr := x})
    | .app (.proj n i f) x, as => do
      -- convert proj back to function application
      let env ← getEnv
      let info := getStructureInfo? env n |>.get!
      let projFn := getProjFnForField? env n (info.fieldNames[i]!) |>.get!
      let .app c f ← mkAppM projFn #[f] | panic! "bug in Mor.withApp"

      go (.app (.app c f) x) as
    | .app f a, as => go f (as.push { expr := a })
    | .forallE x t b bi, _ => do
      go (← mkAppM ``Forall #[.lam x t b bi]) #[]
    | f, as => k f as.reverse


/--
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, return `f`.
Otherwise return the input expression.
-/
/-
**Mathlib.Meta.FunProp.Mor.getAppFn** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunP
rop.Mor`。
形式化陈述：getAppFn (e : Expr) : MetaM Expr
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, ret
urn `f`.
Otherwise return the input expression.
-/
def getAppFn (e : Expr) : MetaM Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
/-
**Mathlib.Meta.FunProp.Mor.getAppArgs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Fu
nProp.Mor`。
形式化陈述：getAppArgs (e : Expr) : MetaM (Array Arg)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphi
sm.
-/
def getAppArgs (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs

/-- `mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism. -/
/-
**Mathlib.Meta.FunProp.Mor.mkAppN** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.FunPro
p.Mor`。
形式化陈述：mkAppN (f : Expr) (xs : Array Arg) : Expr
参数：f : Expr；xs : Array Arg。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism.
-/
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

end Mor

end Meta.FunProp

end Mathlib

