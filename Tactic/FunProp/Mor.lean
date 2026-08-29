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

/--
Definition of `Forall` / `Forall` 的定义

English:
abbreviation Forall
  signature: {α : Sort*} (p : α -> Sort*)
  body: forall x, p x

中文:
缩写 任意
  签名: {α : 类型层*} (p : α -> 类型层*)
  定义体: forall x, p x
-/
abbrev Forall {α : Sort*} (p : α -> Sort*) := forall x, p x

namespace Mor

/--
Definition of `isCoeFunName` / `isCoeFunName` 的定义

English:
definition isCoeFunName
  signature: (name : Name)
  body: do
  let some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun

中文:
定义 isCoeFunName
  签名: (name : Name)
  定义体: do
  let some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun
-/
def isCoeFunName (name : Name) : CoreM Bool := do
  let some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun

/--
Definition of `isCoeFun` / `isCoeFun` 的定义

English:
definition isCoeFun
  signature: (e : Expr)
  body: do
  let some (name, _) := e.getAppFn.const? | return false
  let some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs

中文:
定义 isCoeFun
  签名: (e : Expr)
  定义体: do
  let some (name, _) := e.getAppFn.const? | return false
  let some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs
-/
def isCoeFun (e : Expr) : MetaM Bool := do
  let some (name, _) := e.getAppFn.const? | return false
  let some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs

/--
Definition of `App` / `App` 的定义

English:
structure App
  parameters: where
  axioms and operations (3):
    - coe : Expr
    - fn : Expr
    - arg : Expr

中文:
结构 App
  参数: where
  公理与运算 (3 个):
    - coe : Expr
    - fn : Expr
    - arg : Expr
-/
structure App where
  /-- morphism coercion -/
  coe : Expr
  /-- bundled morphism -/
  fn : Expr
  /-- morphism argument -/
  arg : Expr

/--
Definition of `isMorApp?` / `isMorApp?` 的定义

English:
definition isMorApp?
  signature: (e : Expr)
  body: do

  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return some { coe := coe, fn := f, arg := x }
  else
    return none

中文:
定义 isMorApp?
  签名: (e : Expr)
  定义体: do

  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return some { coe := coe, fn := f, arg := x }
  else
    return none
-/
def isMorApp? (e : Expr) : MetaM (Option App) := do

  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return some { coe := coe, fn := f, arg := x }
  else
    return none

/--
Definition of `whnfPred` / `whnfPred` 的定义

English:
definition whnfPred
  signature: (e : Expr) (pred : Expr -> MetaM Bool)
  body: do
  whnfEasyCases e fun e => do
    let e ← whnfCore e

    if let some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred
      if (← getConfig).zeta then
        return (coe.app f).app x
      else
        return ← mapLetTelescope f fun _ f' => pure ((coe.app f').app x)

    if (← pred e)

中文:
定义 whnfPred
  签名: (e : Expr) (pred : Expr -> MetaM 布尔值)
  定义体: do
  whnfEasyCases e fun e => do
    let e ← whnfCore e

    if let some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred
      if (← getConfig).zeta then
        return (coe.app f).app x
      else
        return ← mapLetTelescope f fun _ f' => pure ((coe.app f').app x)

    if (← pred e)
-/
partial def whnfPred (e : Expr) (pred : Expr -> MetaM Bool) :
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
        | none => return e
    else
      return e

/--
Definition of `whnf` / `whnf` 的定义

English:
definition whnf
  signature: (e : Expr)
  body: whnfPred e (fun _ => return false)

中文:
定义 whnf
  签名: (e : Expr)
  定义体: whnfPred e (fun _ => return false)

Depends on / 依赖: return, whnfPred
-/
def whnf (e : Expr) : MetaM Expr :=
  whnfPred e (fun _ => return false)


/--
Definition of `Arg` / `Arg` 的定义

English:
structure Arg
  parameters: where
  axioms and operations (2):
    - expr : Expr
    - coe : Option Expr  [default: none]

中文:
结构 Arg
  参数: where
  公理与运算 (2 个):
    - expr : Expr
    - coe : 选项类型 Expr  [默认: none]
-/
structure Arg where
  /-- argument of type `α` -/
  expr : Expr
  /-- coercion `F → α → β` -/
  coe : Option Expr := none
  deriving Inhabited

/--
Definition of `app` / `app` 的定义

English:
definition app
  signature: (f : Expr) (arg : Arg)
  body: match arg.coe with
  | none => f.app arg.expr
  | some coe => (coe.app f).app arg.expr

中文:
定义 app
  签名: (f : Expr) (arg : Arg)
  定义体: match arg.coe with
  | none => f.app arg.expr
  | some coe => (coe.app f).app arg.expr

Depends on / 依赖: arg.coe, arg.expr, coe.app, f.app
-/
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | none => f.app arg.expr
  | some coe => (coe.app f).app arg.expr


/--
Definition of `withApp` / `withApp` 的定义

English:
definition withApp
  signature: {α} (e : Expr) (k : Expr -> Array Arg -> MetaM α)
  body: go e #[]

中文:
定义 withApp
  签名: {α} (e : Expr) (k : Expr -> 数组 Arg -> MetaM α)
  定义体: go e #[]
-/
partial def withApp {α} (e : Expr) (k : Expr -> Array Arg -> MetaM α) : MetaM α :=
  go e #[]
where
  /-- -/
  go : Expr -> Array Arg -> MetaM α
    | .mdata _ b, as => go b as
    | .app (.app c f) x, as => do
      if ← isCoeFun c then
        go f (as.push { coe := c, expr := x})
      else
        go (.app c f) (as.push { expr := x})
    | .app (.proj n i f) x, as => do
      -- convert proj back to function application
      let env ← getEnv
.get! let info := getStructureInfo? env n
.get! let projFn := getProjFnForField? env n (info.fieldNames[i]!)
      let .app c f ← mkAppM projFn #[f] | panic! "bug in Mor.withApp"

      go (.app (.app c f) x) as
    | .app f a, as => go f (as.push { expr := a })
    | .forallE x t b bi, _ => do
      go (← mkAppM ``Forall #[.lam x t b bi]) #[]
    | f, as => k f as.reverse


/--
Definition of `getAppFn` / `getAppFn` 的定义

English:
definition getAppFn
  signature: (e : Expr)
  body: match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

中文:
定义 getAppFn
  签名: (e : Expr)
  定义体: match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

Depends on / 依赖: getAppFn, isCoeFun, return
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

/--
Definition of `getAppArgs` / `getAppArgs` 的定义

English:
definition getAppArgs
  signature: (e : Expr)
  body: withApp e fun _ xs => return xs

中文:
定义 getAppArgs
  签名: (e : Expr)
  定义体: withApp e fun _ xs => return xs

Depends on / 依赖: return, withApp
-/
def getAppArgs (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs

/--
Definition of `mkAppN` / `mkAppN` 的定义

English:
definition mkAppN
  signature: (f : Expr) (xs : Array Arg)
  body: xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

中文:
定义 mkAppN
  签名: (f : Expr) (xs : 数组 Arg)
  定义体: xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

Depends on / 依赖: coe.app, f.app, xs.foldl
-/
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, some coe⟩ => (coe.app f).app x)

end Mor

end Meta.FunProp

end Mathlib
