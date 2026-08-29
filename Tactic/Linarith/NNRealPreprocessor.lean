/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.Rify
public import Mathlib.Data.NNReal.Basic -- shake: keep (tactic dependency)

/-!
# NNReal linarith preprocessing

This file contains a `linarith` preprocessor for converting (in)equalities in `ℝ≥0` to `ℝ`.

By overriding the behaviour of the placeholder preprocessor `nnrealToReal` (which does nothing
unless this file is imported) `linarith` can still be used without importing `NNReal`.
-/

public meta section

namespace Mathlib.Tactic.Linarith

open Lean Meta

/--
Definition of `isNNRealProp` / `isNNRealProp` 的定义

English:
definition isNNRealProp
  signature: (e : Expr)
  body: succeeds do
  let (_, _, .const ``NNReal _, _, _) ← e.ineqOrNotIneq? | failure

中文:
定义 isNN实数Prop
  签名: (e : Expr)
  定义体: succeeds do
  let (_, _, .const ``NNReal _, _, _) ← e.ineqOrNotIneq? | failure
-/
partial def isNNRealProp (e : Expr) : MetaM Bool := succeeds do
  let (_, _, .const ``NNReal _, _, _) ← e.ineqOrNotIneq? | failure

/--
Definition of `getNNRealToRealArg?` / `getNNRealToRealArg?` 的定义

English:
definition getNNRealToRealArg?
  signature: (e : Expr)
  body: match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

@[deprecated (since := "2026-05-27")] alias isNNRealtoReal := getNNRealToRealArg?

中文:
定义 getNN实数To实数Arg?
  签名: (e : Expr)
  定义体: match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

@[deprecated (since := "2026-05-27")] alias isNNRealtoReal := getNNRealToRealArg?

Depends on / 依赖: NNReal, NNReal.toReal, toReal
-/
def getNNRealToRealArg? (e : Expr) : Option Expr :=
  match e with
  | .app (.const ``NNReal.toReal _) n => some n
  | _ => none

@[deprecated (since := "2026-05-27")] alias isNNRealtoReal := getNNRealToRealArg?

/--
Definition of `getNNRealCoes` / `getNNRealCoes` 的定义

English:
definition getNNRealCoes
  signature: (e : Expr)
  body: match getNNRealToRealArg? e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNReal

中文:
定义 getNN实数Coes
  签名: (e : Expr)
  定义体: match getNNRealToRealArg? e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNReal
-/
partial def getNNRealCoes (e : Expr) : List Expr :=
  match getNNRealToRealArg? e with
  | some x => [x]
  | none => match e.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HMul.hMul, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HSub.hSub, #[_, _, _, _, a, b]) => getNNRealCoes a ++ getNNRealCoes b
    | (``HDiv.hDiv, #[_, _, _, _, a, _]) => getNNRealCoes a
    | (``Neg.neg, #[_, _, a]) => getNNRealCoes a
    | _ => []

/--
Definition of `mkToRealNonnegProof?` / `mkToRealNonnegProof?` 的定义

English:
definition mkToRealNonnegProof?
  signature: (e : Expr)
  body: try commitIfNoEx (mkAppM ``NNReal.coe_nonneg #[e])
  catch e => do
    trace[linarith] "Got exception when using `coe_nonneg` {e.toMessageData}"
    return none

@[deprecated (since := "2026-05-27")] alias mk_toReal_nonneg_prf := mkToRealNonnegProof?

中文:
定义 mkTo实数NonnegProof?
  签名: (e : Expr)
  定义体: try commitIfNoEx (mkAppM ``NNReal.coe_nonneg #[e])
  catch e => do
    trace[linarith] "Got exception when using `coe_nonneg` {e.toMessageData}"
    return none

@[deprecated (since := "2026-05-27")] alias mk_toReal_nonneg_prf := mkToRealNonnegProof?

Depends on / 依赖: NNReal, NNReal.coe_nonneg, coe_nonneg, commitIfNoEx, e.toMessageData, exception, mkAppM, return, toMessageData
-/
def mkToRealNonnegProof? (e : Expr) : MetaM (Option Expr) :=
  try commitIfNoEx (mkAppM ``NNReal.coe_nonneg #[e])
  catch e => do
    trace[linarith] "Got exception when using `coe_nonneg` {e.toMessageData}"
    return none

@[deprecated (since := "2026-05-27")] alias mk_toReal_nonneg_prf := mkToRealNonnegProof?

initialize nnrealToRealTransform.set fun l => do
  let l ← l.mapM fun e => do
    let t ← whnfR (← instantiateMVars (← inferType e))
    if ← isNNRealProp t then
      return (← Rify.rifyProof e t).1
    else
      return e
let atoms : List Expr ← withNewMCtxDepth AtomM.run .reducible do
    for e in l do
      let (_, _, a, b) ← (← inferType e).ineq?
discard (getNNRealCoes a).mapM AtomM.addAtom
discard (getNNRealCoes b).mapM AtomM.addAtom
    return (← get).atoms.toList
  let nonnegProofs : List Expr ← atoms.filterMapM mkToRealNonnegProof?
  return nonnegProofs ++ l

end Mathlib.Tactic.Linarith
