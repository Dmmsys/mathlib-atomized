/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
public meta import Mathlib.Tactic.Ring
public meta import Mathlib.Util.Qq

/-!
# Reification support for the determinant tactic

This file contains the meta-level parser, `refiyBirdDet`, used by
`normalizeBirdDet` to turn `BirdDet.birdDet` calls into the context used by the
certificate-chain evaluator.

## Main definitions

- `reifyBirdDet`: Parse a call to `BirdDet.birdDet`.

-/

public meta section

open Lean Meta Qq
open Mathlib.Tactic.Ring

namespace Mathlib.Tactic.Determinant

/--
Definition of `commSemiringOfCommRing` / `commSemiringOfCommRing` 的定义

English:
abbreviation commSemiringOfCommRing
  signature: {u : Level} {α : Q(Type u)}
  body: q(CommRing.toCommSemiring (α := $α) (s := $rα))

中文:
缩写 commSemiringOfCommRing
  签名: {u : Level} {α : Q(类型u)}
  定义体: q(CommRing.toCommSemiring (α := $α) (s := $rα))

Depends on / 依赖: CommRing, CommRing.toCommSemiring, toCommSemiring
-/
abbrev commSemiringOfCommRing {u : Level} {α : Q(Type u)}
    (rα : Q(CommRing $α)) : Q(CommSemiring $α) :=
  q(CommRing.toCommSemiring (α := $α) (s := $rα))

/--
Definition of `arrayLiteral?` / `arrayLiteral?` 的定义

English:
definition arrayLiteral?
  signature: (e : Expr)
  body: do
  if let some elems ← getArrayLit? e then return some elems
  let e ← whnf e
  match_expr e with
  | Array.mk _ xs => getListLit? xs
  | _ => return none

中文:
定义 arrayLiteral?
  签名: (e : Expr)
  定义体: do
  if let some elems ← getArrayLit? e then return some elems
  let e ← whnf e
  match_expr e with
  | Array.mk _ xs => getListLit? xs
  | _ => return none
-/
def arrayLiteral? (e : Expr) : MetaM (Option (Array Expr)) := do
  if let some elems ← getArrayLit? e then return some elems
  let e ← whnf e
  match_expr e with
  | Array.mk _ xs => getListLit? xs
  | _ => return none

/--
Definition of `Ctx` / `Ctx` 的定义

English:
structure Ctx
  parameters: {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α))
  axioms and operations (6):
    - cα : Common.Cache (commSemiringOfCommRing rα)
    - rc : Common.RingCompute RatCoeff (commSemiringOfCommRing rα)
    - dimension : Nat
    - dimensionLit : Q(Nat)
    - arrayExpr : Q(Array $α)
    - arrayEntries : Array Q($α)

中文:
结构 Ctx
  参数: {u : Level} {α : Q(类型u)} (rα : Q(交换环 $α))
  公理与运算 (6 个):
    - cα : Common.Cache (commSemiringOfCommRing rα)
    - rc : Common.RingCompute RatCoeff (commSemiringOfCommRing rα)
    - dimension : 自然数
    - dimensionLit : Q(自然数)
    - arrayExpr : Q(数组 $α)
    - arrayEntries : 数组 Q($α)
-/
structure Ctx {u : Level} {α : Q(Type u)} (rα : Q(CommRing $α)) where
  /-- `Ring` evaluation cache for the scalar ring. -/
  cα : Common.Cache (commSemiringOfCommRing rα)
  /-- Proof-producing ring arithmetic. -/
  rc : Common.RingCompute RatCoeff (commSemiringOfCommRing rα)
  /-- The dimension of the reified matrix -/
  dimension : Nat
  /-- The quoted dimension expression from the reified determinant call. -/
  dimensionLit : Q(Nat)
  /-- The array of matrix entries as an Expr -/
  arrayExpr : Q(Array $α)
  /-- An array of matrix entry `Expr`s` -/
  arrayEntries : Array Q($α)

/--
Definition of `ReifiedBirdDet` / `ReifiedBirdDet` 的定义

English:
structure ReifiedBirdDet
  parameters: where
  axioms and operations (4):
    - {u : Level}
    - {α : Q(Type u)}
    - rα : Q(CommRing $α)
    - ctx : Ctx rα

中文:
结构 ReifiedBirdDet
  参数: where
  公理与运算 (4 个):
    - {u : Level}
    - {α : Q(类型u)}
    - rα : Q(交换环 $α)
    - ctx : Ctx rα
-/
structure ReifiedBirdDet where
  /-- The universe level associated with the `birdDet` call -/
  {u : Level}
  /-- The type of a matrix entry -/
  {α : Q(Type u)}
  /-- The `CommRing` instance for matrix entries -/
  rα : Q(CommRing $α)
  /-- The evaluator context for the parsed determinant expression. -/
  ctx : Ctx rα

/--
Definition of `reifyBirdDet` / `reifyBirdDet` 的定义

English:
definition reifyBirdDet
  signature: (e : Expr)
  body: do
  let e ← instantiateMVars e
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let_expr BirdDet.birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some rα ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type {q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionLit ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected the dimension to have type `Nat`, got {dimensionExpr}"
  let some dimension ← getNatValue? dimensionLit
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionLit}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type {q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, \
      expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type {α}"
    return entry
  let sα := commSemiringOfCommRing rα
  let cα : Common.Cache sα := {
    rα := some rα
    dsα := none
    czα := none
  }
  return {
    rα
    ctx := {
      cα
      rc := ringCompute cα
      dimension
      dimensionLit
      arrayExpr
      arrayEntries
    }
  }

中文:
定义 reifyBirdDet
  签名: (e : Expr)
  定义体: do
  let e ← instantiateMVars e
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let_expr BirdDet.birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some rα ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type {q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionLit ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected the dimension to have type `Nat`, got {dimensionExpr}"
  let some dimension ← getNatValue? dimensionLit
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionLit}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type {q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, \
      expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type {α}"
    return entry
  let sα := commSemiringOfCommRing rα
  let cα : Common.Cache sα := {
    rα := some rα
    dsα := none
    czα := none
  }
  return {
    rα
    ctx := {
      cα
      rc := ringCompute cα
      dimension
      dimensionLit
      arrayExpr
      arrayEntries
    }
  }
-/
def reifyBirdDet (e : Expr) : MetaM ReifiedBirdDet := do
  let e ← instantiateMVars e
  let ⟨_, α, _⟩ ← inferTypeQ' e
  let_expr BirdDet.birdDet _ birdRingInst dimensionExpr arrayExpr := e
    | throwError "expected an application of `birdDet, got {e}"
  let some rα ← checkTypeQ birdRingInst q(CommRing $α)
    | throwError "expected `birdDet` ring instance to have type {q(CommRing $α)}"
  let dimensionExpr ← whnf dimensionExpr
  let some dimensionLit ← checkTypeQ dimensionExpr q(Nat)
    | throwError "expected the dimension to have type `Nat`, got {dimensionExpr}"
  let some dimension ← getNatValue? dimensionLit
    | throwError "expected the dimension to be a `Nat` literal, got {dimensionLit}"
  let some arrayExpr ← checkTypeQ arrayExpr q(Array $α)
    | throwError "expected the array to have type {q(Array $α)}"
  let some arrayEntries ← arrayLiteral? arrayExpr
    | throwError "expected an array literal matrix, got {arrayExpr}"
  unless arrayEntries.size == dimension * dimension do
    throwError "matrix size mismatch: array has {arrayEntries.size} entries, \
      expected {dimension * dimension}"
  let arrayEntries ← arrayEntries.mapM fun entry => do
    let some entry ← checkTypeQ entry α
      | throwError "expected array entry to have type {α}"
    return entry
  let sα := commSemiringOfCommRing rα
  let cα : Common.Cache sα := {
    rα := some rα
    dsα := none
    czα := none
  }
  return {
    rα
    ctx := {
      cα
      rc := ringCompute cα
      dimension
      dimensionLit
      arrayExpr
      arrayEntries
    }
  }

end Mathlib.Tactic.Determinant

end
