/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public import Lean.Meta.AppBuilder
public import Lean.Meta.Coe

/-!
# Additions to `Lean.Meta.Basic`

Likely these already exist somewhere. Pointers welcome.
-/

@[expose] public section

/--
Definition of `Lean.Meta.preservingMCtx` / `Lean.Meta.preservingMCtx` 的定义

English:
definition Lean.Meta.preservingMCtx
  signature: {α : Type} (x : MetaM α)
  body: do
  let mctx ← getMCtx
  try x finally setMCtx mctx

中文:
定义 Lean.Meta.preservingMCtx
  签名: {α : 类型} (x : MetaM α)
  定义体: do
  let mctx ← getMCtx
  try x finally setMCtx mctx
-/
def Lean.Meta.preservingMCtx {α : Type} (x : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  try x finally setMCtx mctx

open Lean Meta

/--
Definition of `Lean.Meta.forallMetaTelescopeReducingUntilDefEq` / `Lean.Meta.forallMetaTelescopeReducingUntilDefEq` 的定义

English:
definition Lean.Meta.forallMetaTelescopeReducingUntilDefEq
  body: do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDef

中文:
定义 Lean.Meta.对任意MetaTelescopeReducingUntilDefEq
  定义体: do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDef

Depends on / 依赖: MetavarKind, MetavarKind.natural, natural
-/
def Lean.Meta.forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do
      throwError m!"Failed to find {← ppExpr t} as the type of a parameter of {← ppExpr e}."
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

/-- `pureIsDefEq e₁ e₂` is short for `withNewMCtxDepth <| isDefEq e₁ e₂`.
Determines whether two expressions are definitionally equal to each other
when metavariables are not assignable. -/
@[inline]
/--
Definition of `Lean.Meta.pureIsDefEq` / `Lean.Meta.pureIsDefEq` 的定义

English:
definition Lean.Meta.pureIsDefEq
  signature: (e₁ e₂ : Expr)
  body: withNewMCtxDepth isDefEq e₁ e₂

中文:
定义 Lean.Meta.pureIsDefEq
  签名: (e₁ e₂ : Expr)
  定义体: withNewMCtxDepth isDefEq e₁ e₂

Depends on / 依赖: isDefEq, withNewMCtxDepth
-/
def Lean.Meta.pureIsDefEq (e₁ e₂ : Expr) : MetaM Bool :=
withNewMCtxDepth isDefEq e₁ e₂

/--
Definition of `Lean.Meta.mkRel` / `Lean.Meta.mkRel` 的定义

English:
definition Lean.Meta.mkRel
  signature: (n : Name) (lhs rhs : Expr)
  body: if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]

中文:
定义 Lean.Meta.mkRel
  签名: (n : Name) (lhs rhs : Expr)
  定义体: if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]

Depends on / 依赖: mkApp2, mkAppM, return
-/
def Lean.Meta.mkRel (n : Name) (lhs rhs : Expr) : MetaM Expr :=
  if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]

/--
Definition of `Lean.Meta.withEnsuringLocalInstance` / `Lean.Meta.withEnsuringLocalInstance` 的定义

English:
definition Lean.Meta.withEnsuringLocalInstance
  signature: {α : Type} (inst : MVarId) (k : MetaM (Expr × α))
  body: do
  let instE := mkMVar inst
  match ← trySynthInstance (← inferType instE) with
  | .some e =>
    unless ← isDefEq instE e do
      throwError "failed to assign synthesized type class instance {indentExpr e}\n\
        to{indentExpr instE}"
    k
  | _ =>
    withLetDecl `inst (← inferType instE)

中文:
定义 Lean.Meta.withEnsuringLocalInstance
  签名: {α : 类型} (inst : MVarId) (k : MetaM (Expr × α))
  定义体: do
  let instE := mkMVar inst
  match ← trySynthInstance (← inferType instE) with
  | .some e =>
    unless ← isDefEq instE e do
      throwError "failed to assign synthesized type class instance {indentExpr e}\n\
        to{indentExpr instE}"
    k
  | _ =>
    withLetDecl `inst (← inferType instE)
-/
def Lean.Meta.withEnsuringLocalInstance {α : Type} (inst : MVarId) (k : MetaM (Expr × α)) :
    MetaM (Expr × α) := do
  let instE := mkMVar inst
  match ← trySynthInstance (← inferType instE) with
  | .some e =>
    unless ← isDefEq instE e do
      throwError "failed to assign synthesized type class instance {indentExpr e}\n\
        to{indentExpr instE}"
    k
  | _ =>
    withLetDecl `inst (← inferType instE) instE fun inst' => do
      let (e, v) ← k
      let e' := (← e.abstractM #[inst']).instantiate1 instE
      return (e', v)

/--
Definition of `Lean.Meta.ensureHasType` / `Lean.Meta.ensureHasType` 的定义

English:
definition Lean.Meta.ensureHasType
  signature: (e expectedType : Expr)
  body: do
  let ty ← inferType e
  if ← withNewMCtxDepth (isDefEq ty expectedType) then return e else
(← coerceSimple? e expectedType).toOption.getDM
      throwError "Expected{indentD e}\nto have type{indentD ty}\n or to be coercible to it"

中文:
定义 Lean.Meta.ensureHasType
  签名: (e expectedType : Expr)
  定义体: do
  let ty ← inferType e
  if ← withNewMCtxDepth (isDefEq ty expectedType) then return e else
(← coerceSimple? e expectedType).toOption.getDM
      throwError "Expected{indentD e}\nto have type{indentD ty}\n or to be coercible to it"
-/
def Lean.Meta.ensureHasType (e expectedType : Expr) : MetaM Expr := do
  let ty ← inferType e
  if ← withNewMCtxDepth (isDefEq ty expectedType) then return e else
(← coerceSimple? e expectedType).toOption.getDM
      throwError "Expected{indentD e}\nto have type{indentD ty}\n or to be coercible to it"

/--
Definition of `Lean.Meta.ensureIsFunction` / `Lean.Meta.ensureIsFunction` 的定义

English:
definition Lean.Meta.ensureIsFunction
  signature: (e : Expr)
  body: do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isForall then return e else (← coerceToFunction? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a function, or to be coercible to \
      a function"

中文:
定义 Lean.Meta.ensureIsFunction
  签名: (e : Expr)
  定义体: do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isForall then return e else (← coerceToFunction? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a function, or to be coercible to \
      a function"
-/
def Lean.Meta.ensureIsFunction (e : Expr) : MetaM Expr := do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isForall then return e else (← coerceToFunction? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a function, or to be coercible to \
      a function"

/--
Definition of `Lean.Meta.ensureIsSort` / `Lean.Meta.ensureIsSort` 的定义

English:
definition Lean.Meta.ensureIsSort
  signature: (e : Expr)
  body: do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isSort then return e else (← coerceToSort? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a Sort, or to be coercible to \
      a Sort"

中文:
定义 Lean.Meta.ensureIsSort
  签名: (e : Expr)
  定义体: do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isSort then return e else (← coerceToSort? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a Sort, or to be coercible to \
      a Sort"
-/
def Lean.Meta.ensureIsSort (e : Expr) : MetaM Expr := do
let ty ← whnf ← instantiateMVars ← inferType e
if ty.isSort then return e else (← coerceToSort? e).getDM
    throwError "Expected{indentD e}\nof type{indentD ty}\nto be a Sort, or to be coercible to \
      a Sort"
