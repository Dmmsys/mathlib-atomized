/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Exception
public meta import Batteries.Lean.NameMapAttribute

/-!
# `@[notation_class]` attribute for `@[simps]`

This declares the `@[notation_class]` attribute, which is used to give smarter default projections
for `@[simps]`.

We put this in a separate file so that we can already tag some declarations with this attribute
in the file where we declare `@[simps]`. For further documentation, see `Tactic.Simps.Basic`.
-/

public meta section

/-- The `@[notation_class]` attribute specifies that this is a notation class,
and this notation should be used instead of projections by `@[simps]`.
  * This is only important if the projection is written differently using notation, e.g.
    `+` uses `HAdd.hAdd`, not `Add.add` and `0` uses `OfNat.ofNat` not `Zero.zero`.
    We also add it to non-heterogeneous notation classes, like `Neg`, but it doesn't do much for any
    class that extends `Neg`.
  * `@[notation_class* <projName> Simps.findCoercionArgs]` is used to configure the
    `SetLike` and `DFunLike` coercions.
  * The first name argument is the projection name we use as the key to search for this class
    (default: name of first projection of the class).
  * The second argument is the name of a declaration that has type
    `findArgType` which is defined to be `Name → Name → Array Expr → MetaM (Array (Option Expr))`.
    This declaration specifies how to generate the arguments of the notation class from the
    arguments of classes that use the projection. -/
syntax (name := notation_class) "notation_class" "*"? (ppSpace ident)? (ppSpace ident)? : attr

open Lean Meta Elab Term

namespace Simps

/--
Definition of `findArgType` / `findArgType` 的定义

English:
definition findArgType
  signature: : Type
  body: Name -> Name -> Array Expr -> MetaM (Array (Option Expr))

中文:
定义 findArgType
  签名: : Type
  定义体: Name -> Name -> Array Expr -> MetaM (Array (Option Expr))
-/
@[expose] def findArgType : Type := Name -> Name -> Array Expr -> MetaM (Array (Option Expr))

/--
Definition of `defaultfindArgs` / `defaultfindArgs` 的定义

English:
definition defaultfindArgs
  signature: : findArgType
  body: fun _ className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  if arity == args.size then
    return args.map some
  else if h : args.size = 1 then
    return .replicate arity args[0]
  else
   

中文:
定义 defaultfindArgs
  签名: : findArgType
  定义体: fun _ className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  if arity == args.size then
    return args.map some
  else if h : args.size = 1 then
    return .replicate arity args[0]
  else
   

Depends on / 依赖: className
-/
def defaultfindArgs : findArgType := fun _ className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  if arity == args.size then
    return args.map some
  else if h : args.size = 1 then
    return .replicate arity args[0]
  else
    throwError "initialize_simps_projections cannot automatically find arguments for class \
      {className}"

/--
Definition of `copyFirst` / `copyFirst` 的定义

English:
definition copyFirst
  signature: : findArgType
  body: fun _ _ args => return (args.push <| args[0]?.getD default).map some

中文:
定义 copyFirst
  签名: : findArgType
  定义体: fun _ _ args => return (args.push <| args[0]?.getD default).map some

Depends on / 依赖: args.push, return
-/
def copyFirst : findArgType := fun _ _ args => return (args.push <| args[0]?.getD default).map some

/--
Definition of `copySecond` / `copySecond` 的定义

English:
definition copySecond
  signature: : findArgType
  body: fun _ _ args => return (args.push <| args[1]?.getD default).map some

中文:
定义 copySecond
  签名: : findArgType
  定义体: fun _ _ args => return (args.push <| args[1]?.getD default).map some

Depends on / 依赖: args.push, return
-/
def copySecond : findArgType := fun _ _ args => return (args.push <| args[1]?.getD default).map some

/--
Definition of `nsmulArgs` / `nsmulArgs` 的定义

English:
definition nsmulArgs
  signature: : findArgType
  body: fun _ _ args =>
.map some return #[Expr.const `Nat [], args[0]?.getD default] ++ args

中文:
定义 nsmulArgs
  签名: : findArgType
  定义体: fun _ _ args =>
.map some return #[Expr.const `Nat [], args[0]?.getD default] ++ args
-/
def nsmulArgs : findArgType := fun _ _ args =>
.map some return #[Expr.const `Nat [], args[0]?.getD default] ++ args

/--
Definition of `zsmulArgs` / `zsmulArgs` 的定义

English:
definition zsmulArgs
  signature: : findArgType
  body: fun _ _ args =>
.map some return #[Expr.const `Int [], args[0]?.getD default] ++ args

中文:
定义 zsmulArgs
  签名: : findArgType
  定义体: fun _ _ args =>
.map some return #[Expr.const `Int [], args[0]?.getD default] ++ args
-/
def zsmulArgs : findArgType := fun _ _ args =>
.map some return #[Expr.const `Int [], args[0]?.getD default] ++ args

/--
Definition of `findZeroArgs` / `findZeroArgs` 的定义

English:
definition findZeroArgs
  signature: : findArgType
  body: fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 0]

中文:
定义 findZeroArgs
  签名: : findArgType
  定义体: fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 0]
-/
def findZeroArgs : findArgType := fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 0]

/--
Definition of `findOneArgs` / `findOneArgs` 的定义

English:
definition findOneArgs
  signature: : findArgType
  body: fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 1]

中文:
定义 findOneArgs
  签名: : findArgType
  定义体: fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 1]
-/
def findOneArgs : findArgType := fun _ _ args =>
  return #[some <| args[0]?.getD default, some <| mkRawNatLit 1]

/--
Definition of `findCoercionArgs` / `findCoercionArgs` 的定义

English:
definition findCoercionArgs
  signature: : findArgType
  body: fun str className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  let eStr := mkAppN (← mkConstWithLevelParams str) args
  let classArgs := .replicate (arity - 1) none
  return #[some eStr] ++ cl

中文:
定义 findCoercionArgs
  签名: : findArgType
  定义体: fun str className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  let eStr := mkAppN (← mkConstWithLevelParams str) args
  let classArgs := .replicate (arity - 1) none
  return #[some eStr] ++ cl

Depends on / 依赖: className
-/
def findCoercionArgs : findArgType := fun str className args => do
  let some classExpr := (← getEnv).find? className | throwError "no such class {className}"
  let arity := classExpr.type.getNumHeadForalls
  let eStr := mkAppN (← mkConstWithLevelParams str) args
  let classArgs := .replicate (arity - 1) none
  return #[some eStr] ++ classArgs

/--
Definition of `AutomaticProjectionData` / `AutomaticProjectionData` 的定义

English:
structure AutomaticProjectionData
  parameters: where
  axioms and operations (3):
    - className : Name
    - isNotation : = true
    - findArgs : Name  [default: `Simps.defaultfindArgs]

中文:
结构 AutomaticProjectionData
  参数: where
  公理与运算 (3 个):
    - className : Name
    - isNotation : = true
    - findArgs : Name  [默认: `Simps.defaultfindArgs]
-/
structure AutomaticProjectionData where
  /-- `className` is the name of the class we are looking for. -/
  className : Name
  /-- `isNotation` is a Boolean that specifies whether this is notation
  (false for the coercions `DFunLike` and `SetLike`). If this is set to true, we add the current
  class as hypothesis during type-class synthesis. -/
  isNotation := true
  /-- The method to find the arguments of the class. -/
  findArgs : Name := `Simps.defaultfindArgs
deriving Inhabited

/-- `@[notation_class]` attribute. Note: this is *not* a `NameMapAttribute` because we key on the
argument of the attribute, not the declaration name. -/
initialize notationClassAttr : NameMapExtension AutomaticProjectionData ← do
  let ext ← registerNameMapExtension AutomaticProjectionData
  registerBuiltinAttribute {
    name := `notation_class
    descr := "An attribute specifying that this is a notation class. Used by @[simps]."
    add := fun src stx _kind => do
      unless isStructure (← getEnv) src do
        throwError "@[notation_class] attribute can only be added to classes."
      match stx with
      | `(attr|notation_class $[*%$coercion]? $[$projName?]? $[$findArgs?]?) => do
        let projName ← match projName? with
          | none => pure (getStructureFields (← getEnv) src)[0]!
          | some projName => pure projName.getId
        let findArgs := if findArgs?.isSome then findArgs?.get!.getId else `Simps.defaultfindArgs
        match (← getEnv).find? findArgs with
        | none => throwError "no such declaration {findArgs}"
        | some declInfo =>
unless ← MetaM.run' isDefEq declInfo.type (mkConst ``findArgType) do
            throwError "declaration {findArgs} has wrong type"
        ext.add projName ⟨src, coercion.isNone, findArgs⟩
      | _ => throwUnsupportedSyntax }
  return ext

end Simps
