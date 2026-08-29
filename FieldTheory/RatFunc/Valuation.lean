/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Valuations on F(t)

This file defines the valuation at infinity on the field of rational functions `F(t)`.

## Main definitions

- `RatFunc.inftyValuation` : The place at infinity on `F(t)` is the nonarchimedean
  valuation on `F(t)` with uniformizer `1/t`.
- `RatFunc.CompletionAtInfty` : The completion `F((t⁻¹))` of `F(t)` with respect to the
  valuation at infinity.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

@[expose] public section


public noncomputable section

namespace RatFunc

variable (F K : Type*) [Field F] [Field K]

/-! ### The place at infinity on F(t) -/

section InftyValuation

open Multiplicative WithZero Polynomial

variable [DecidableEq (RatFunc F)]

/--
Definition of `inftyValuationDef` / `inftyValuationDef` 的定义

English:
definition inftyValuationDef
  signature: (r : RatFunc F)
  body: if r = 0 then 0 else exp r.intDegree

中文:
定义 inftyValuationDef
  签名: (r : RatFunc F)
  定义体: if r = 0 then 0 else exp r.intDegree

Depends on / 依赖: intDegree, r.intDegree
-/
def inftyValuationDef (r : RatFunc F) : Intᵐ⁰ :=
  if r = 0 then 0 else exp r.intDegree

/--
theorem `InftyValuation.map_zero'` / 定理 `InftyValuation.map_zero'`

English:
theorem InftyValuation.map_zero'
  statement: inftyValuationDef F 0 = 0
  proof: if_pos rfl

中文:
定理 InftyValuation.map_zero'
  结论: inftyValuationDef F 0 = 0
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
  if_pos rfl

/--
theorem `InftyValuation.map_one'` / 定理 `InftyValuation.map_one'`

English:
theorem InftyValuation.map_one'
  statement: inftyValuationDef F 1 = 1
  proof: (if_neg one_ne_zero).trans by simp

中文:
定理 InftyValuation.map_one'
  结论: inftyValuationDef F 1 = 1
  证明: (if_neg one_ne_zero).trans by simp

Depends on / 依赖: if_neg, one_ne_zero
-/
theorem InftyValuation.map_one' : inftyValuationDef F 1 = 1 :=
(if_neg one_ne_zero).trans by simp

/--
theorem `InftyValuation.map_mul'` / 定理 `InftyValuation.map_mul'`

English:
theorem InftyValuation.map_mul'
  given: (x y : RatFunc F)
  proof: by
  rw [inftyValuationDef]; rw [inftyValuationDef]; rw [inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]

中文:
定理 InftyValuation.map_mul'
  条件: (x y : RatFunc F)
  证明: by
  rw [inftyValuationDef]; rw [inftyValuationDef]; rw [inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]

Depends on / 依赖: Eq.refl, RatFunc, RatFunc.intDegree_mul, if_pos, inftyValuationDef, intDegree_mul, mul_zero, zero_mul
-/
theorem InftyValuation.map_mul' (x y : RatFunc F) :
    inftyValuationDef F (x * y) = inftyValuationDef F x * inftyValuationDef F y := by
  rw [inftyValuationDef]; rw [inftyValuationDef]; rw [inftyValuationDef]
  by_cases hx : x = 0
  · rw [hx, zero_mul, if_pos (Eq.refl _), zero_mul]
  · by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos (Eq.refl _), mul_zero]
    · simp_all [RatFunc.intDegree_mul]

/--
theorem `InftyValuation.map_add_le_max'` / 定理 `InftyValuation.map_add_le_max'`

English:
theorem InftyValuation.map_add_le_max'
  given: (x y : RatFunc F)
  proof: by
  unfold inftyValuationDef
  have := @RatFunc.intDegree_add_le F
  aesop

@[simp]

中文:
定理 InftyValuation.map_add_le_max'
  条件: (x y : RatFunc F)
  证明: by
  unfold inftyValuationDef
  have := @RatFunc.intDegree_add_le F
  aesop

@[simp]

Depends on / 依赖: RatFunc, RatFunc.intDegree_add_le, inftyValuationDef, intDegree_add_le
-/
theorem InftyValuation.map_add_le_max' (x y : RatFunc F) :
    inftyValuationDef F (x + y) <= max (inftyValuationDef F x) (inftyValuationDef F y) := by
  unfold inftyValuationDef
  have := @RatFunc.intDegree_add_le F
  aesop

@[simp]
/--
theorem `inftyValuation_of_nonzero` / 定理 `inftyValuation_of_nonzero`

English:
theorem inftyValuation_of_nonzero
  given: {x : RatFunc F} (hx : x != 0)
  proof: by
  rw [inftyValuationDef]; rw [if_neg hx]

中文:
定理 inftyValuation_of_nonzero
  条件: {x : RatFunc F} (hx : x != 0)
  证明: by
  rw [inftyValuationDef]; rw [if_neg hx]

Depends on / 依赖: if_neg, inftyValuationDef
-/
theorem inftyValuation_of_nonzero {x : RatFunc F} (hx : x != 0) :
    inftyValuationDef F x = exp x.intDegree := by
  rw [inftyValuationDef]; rw [if_neg hx]

/--
Definition of `inftyValuation` / `inftyValuation` 的定义

English:
definition inftyValuation
  signature: : Valuation (RatFunc F) Intᵐ⁰ where
  body: inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F

中文:
定义 inftyValuation
  签名: : Valuation (RatFunc F) 整数ᵐ⁰ where
  定义体: inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F

Depends on / 依赖: inftyValuationDef
-/
def inftyValuation : Valuation (RatFunc F) Intᵐ⁰ where
  toFun := inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F

/--
theorem `inftyValuation_apply` / 定理 `inftyValuation_apply`

English:
theorem inftyValuation_apply
  given: {x : RatFunc F}
  statement: inftyValuation F x = inftyValuationDef F x
  proof: rfl

@[simp]

中文:
定理 inftyValuation_apply
  条件: {x : RatFunc F}
  结论: inftyValuation F x = inftyValuationDef F x
  证明: rfl

@[simp]
-/
theorem inftyValuation_apply {x : RatFunc F} : inftyValuation F x = inftyValuationDef F x :=
  rfl

@[simp]
/--
theorem `inftyValuation.C` / 定理 `inftyValuation.C`

English:
theorem inftyValuation.C
  given: {k : F} (hk : k != 0)
  proof: by
  simp [inftyValuation_apply, hk]

@[simp]

中文:
定理 inftyValuation.C
  条件: {k : F} (hk : k != 0)
  证明: by
  simp [inftyValuation_apply, hk]

@[simp]

Depends on / 依赖: inftyValuation_apply
-/
theorem inftyValuation.C {k : F} (hk : k != 0) :
    inftyValuation F (RatFunc.C k) = 1 := by
  simp [inftyValuation_apply, hk]

@[simp]
/--
theorem `inftyValuation.X` / 定理 `inftyValuation.X`

English:
theorem inftyValuation.X
  statement: inftyValuation F RatFunc.X = exp 1
  proof: by
  simp [inftyValuation_apply, inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]

中文:
定理 inftyValuation.X
  结论: inftyValuation F RatFunc.X = exp 1
  证明: by
  simp [inftyValuation_apply, inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]

Depends on / 依赖: RatFunc, RatFunc.X_ne_zero, RatFunc.intDegree_X, X_ne_zero, if_neg, inftyValuationDef, inftyValuation_apply, intDegree_X
-/
theorem inftyValuation.X : inftyValuation F RatFunc.X = exp 1 := by
  simp [inftyValuation_apply, inftyValuationDef, if_neg RatFunc.X_ne_zero, RatFunc.intDegree_X]

/--
lemma `inftyValuation.X_zpow` / 引理 `inftyValuation.X_zpow`

English:
lemma inftyValuation.X_zpow
  given: (m : Int)
  statement: inftyValuation F (RatFunc.X ^ m) = exp m
  proof: by simp

中文:
引理 inftyValuation.X_zpow
  条件: (m : 整数)
  结论: inftyValuation F (RatFunc.X ^ m) = exp m
  证明: by simp
-/
lemma inftyValuation.X_zpow (m : Int) : inftyValuation F (RatFunc.X ^ m) = exp m := by simp

/--
theorem `inftyValuation.X_inv` / 定理 `inftyValuation.X_inv`

English:
theorem inftyValuation.X_inv
  statement: inftyValuation F (1 / RatFunc.X) = exp (-1)
  proof: by
  rw [one_div]; rw [← zpow_neg_one]; rw [inftyValuation.X_zpow]

中文:
定理 inftyValuation.X_inv
  结论: inftyValuation F (1 / RatFunc.X) = exp (-1)
  证明: by
  rw [one_div]; rw [← zpow_neg_one]; rw [inftyValuation.X_zpow]

Depends on / 依赖: X_zpow, inftyValuation, inftyValuation.X_zpow, one_div, zpow_neg_one
-/
theorem inftyValuation.X_inv : inftyValuation F (1 / RatFunc.X) = exp (-1) := by
  rw [one_div]; rw [← zpow_neg_one]; rw [inftyValuation.X_zpow]

-- Dropped attribute `@[simp]` due to issue described here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60synthInstance.2EmaxHeartbeats.60.20error.20but.20only.20in.20.60simpNF.60
/--
theorem `inftyValuation.polynomial` / 定理 `inftyValuation.polynomial`

English:
theorem inftyValuation.polynomial
  given: {p : F[X]} (hp : p != 0)
  proof: by
  rw [inftyValuationDef]; rw [if_neg (by simpa)]; rw [RatFunc.intDegree_polynomial]

中文:
定理 inftyValuation.polynomial
  条件: {p : F[X]} (hp : p != 0)
  证明: by
  rw [inftyValuationDef]; rw [if_neg (by simpa)]; rw [RatFunc.intDegree_polynomial]

Depends on / 依赖: RatFunc, RatFunc.intDegree_polynomial, if_neg, inftyValuationDef, intDegree_polynomial
-/
theorem inftyValuation.polynomial {p : F[X]} (hp : p != 0) :
    inftyValuationDef F (algebraMap F[X] (RatFunc F) p) = exp (p.natDegree : Int) := by
  rw [inftyValuationDef]; rw [if_neg (by simpa)]; rw [RatFunc.intDegree_polynomial]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valuation.IsNontrivial (inftyValuation F)
  body: ⟨RatFunc.X, by simp⟩

中文:
实例 :
  签名: Valuation.IsNontrivial (inftyValuation F)
  定义体: ⟨RatFunc.X, by simp⟩

Depends on / 依赖: RatFunc, RatFunc.X
-/
instance : Valuation.IsNontrivial (inftyValuation F) := ⟨RatFunc.X, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valuation.IsTrivialOn F (inftyValuation F)
  body: ⟨fun _ hx => by simp [inftyValuation.C _ hx]⟩

中文:
实例 :
  签名: Valuation.IsTrivialOn F (inftyValuation F)
  定义体: ⟨fun _ hx => by simp [inftyValuation.C _ hx]⟩

Depends on / 依赖: inftyValuation, inftyValuation.C
-/
instance : Valuation.IsTrivialOn F (inftyValuation F) :=
  ⟨fun _ hx => by simp [inftyValuation.C _ hx]⟩

/-- The valued field `F(t)` with the valuation at infinity. -/
@[instance_reducible]
/--
Definition of `inftyValued` / `inftyValued` 的定义

English:
definition inftyValued
  signature: : Valued (RatFunc F) Intᵐ⁰
  body: Valued.mk' inftyValuation F

中文:
定义 inftyValued
  签名: : Valued (RatFunc F) 整数ᵐ⁰
  定义体: Valued.mk' inftyValuation F

Depends on / 依赖: Valued, Valued.mk, inftyValuation
-/
def inftyValued : Valued (RatFunc F) Intᵐ⁰ :=
Valued.mk' inftyValuation F

/--
theorem `inftyValued.def` / 定理 `inftyValued.def`

English:
theorem inftyValued.def
  given: {x : RatFunc F}
  proof: rfl

中文:
定理 inftyValued.def
  条件: {x : RatFunc F}
  证明: rfl
-/
theorem inftyValued.def {x : RatFunc F} :
    (inftyValued F).v x = inftyValuationDef F x :=
  rfl

namespace CompletionAtInfty

/- We temporarily disable the existing valued instance coming from the ideal `X` to avoid diamonds
with the uniform space structure coming from the valuation at infinity. -/
attribute [-instance] RatFunc.valuedRatFunc

/- Locally add the uniform space structure coming from the valuation at infinity. This instance
is scoped in the `CompletionAtInfty` namescape in case it is needed in the future. -/
/-- The uniform space structure on `RatFunc F` coming from the valuation at infinity. -/
scoped instance : UniformSpace (RatFunc F) := (inftyValued F).toUniformSpace

/--
Definition of `_root_.RatFunc.CompletionAtInfty` / `_root_.RatFunc.CompletionAtInfty` 的定义

English:
definition _root_.RatFunc.CompletionAtInfty
  body: UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

中文:
定义 _root_.RatFunc.CompletionAtInfty
  定义体: UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

Depends on / 依赖: Completion, RatFunc, UniformSpace, UniformSpace.Completion
-/
def _root_.RatFunc.CompletionAtInfty := UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valued (CompletionAtInfty F) Intᵐ⁰
  body: inferInstanceAs Valued (UniformSpace.Completion (RatFunc F)) Intᵐ⁰

中文:
实例 :
  签名: Valued (CompletionAtInfty F) 整数ᵐ⁰
  定义体: inferInstanceAs Valued (UniformSpace.Completion (RatFunc F)) Intᵐ⁰

Depends on / 依赖: Completion, RatFunc, UniformSpace, UniformSpace.Completion, Valued
-/
instance : Valued (CompletionAtInfty F) Intᵐ⁰ :=
inferInstanceAs Valued (UniformSpace.Completion (RatFunc F)) Intᵐ⁰

end CompletionAtInfty

/--
theorem `valuedCompletionAtInfty.def` / 定理 `valuedCompletionAtInfty.def`

English:
theorem valuedCompletionAtInfty.def
  given: {x : CompletionAtInfty F}
  proof: rfl

中文:
定理 valuedCompletionAtInfty.def
  条件: {x : CompletionAtInfty F}
  证明: rfl
-/
theorem valuedCompletionAtInfty.def {x : CompletionAtInfty F} :
  Valued.v x = (inftyValued F).extensionValuation x := rfl

end InftyValuation

end RatFunc
