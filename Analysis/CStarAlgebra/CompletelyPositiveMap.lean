/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-! # Completely positive maps

A linear map `φ : A₁ →ₗ[ℂ] A₂` (where `A₁` and `A₂` are C⋆-algebras) is called
*completely positive (CP)* if `CStarMatrix.map (Fin k) (Fin k) φ` (i.e. applying `φ` to all
entries of a k × k matrix) is also positive for every `k : ℕ`.

This file defines completely positive maps and develops their basic API.

## Main results

+ `NonUnitalStarAlgHomClass.instCompletelyPositiveMapClass`: Non-unital star algebra
  homomorphisms are completely positive.

## Notation

+ `A₁ →CP A₂` denotes the type of CP maps from `A₁` to `A₂`. This notation is scoped to
  `CStarAlgebra`.

## Implementation notes

The morphism class `CompletelyPositiveMapClass` is designed to be part of the order hierarchy,
and only includes the order property; linearity is not mentioned at all. It is therefore meant
to be used in conjunction with `LinearMapClass`. This is meant to avoid mixing order and algebra
as much as possible.
-/

@[expose] public section

open scoped CStarAlgebra

/--
Definition of `CompletelyPositiveMap` / `CompletelyPositiveMap` 的定义

English:
structure CompletelyPositiveMap
  parameters: (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
  extends: A₁ ->ₗ[Complex] A₂
  axioms and operations (1):
    - map_cstarMatrix_nonneg'((k : Nat) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 <= M)) : 0 <= M.map toLinearMap

中文:
结构 余mpletelyPositive映射
  参数: (A₁ : 类型) (A₂ : 类型) [非幺CStar代数 A₁]
  继承: A₁ ->ₗ[复形] A₂
  公理与运算 (1 个):
    - map_cstarMatrix_nonneg'((k : 自然数) (M : CStarMatrix (有限集 k) (有限集 k) A₁) (hM : 0 <= M)) : 0 <= M.map toLinearMap
-/
structure CompletelyPositiveMap (A₁ : Type*) (A₂ : Type*) [NonUnitalCStarAlgebra A₁]
    [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
    [StarOrderedRing A₂] extends A₁ ->ₗ[Complex] A₂ where
  map_cstarMatrix_nonneg' (k : Nat) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 <= M) :
      0 <= M.map toLinearMap

/--
Definition of `CompletelyPositiveMapClass` / `CompletelyPositiveMapClass` 的定义

English:
class CompletelyPositiveMapClass
  parameters: (F : Type*) (A₁ : Type*) (A₂ : Type*)
  axioms and operations (1):
    - map_cstarMatrix_nonneg'((φ : F) (k : Nat) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 <= M)) : 0 <= M.map φ

中文:
类 余mpletelyPositive映射类
  参数: (F : 类型) (A₁ : 类型) (A₂ : 类型)
  公理与运算 (1 个):
    - map_cstarMatrix_nonneg'((φ : F) (k : 自然数) (M : CStarMatrix (有限集 k) (有限集 k) A₁) (hM : 0 <= M)) : 0 <= M.map φ
-/
class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] where
  map_cstarMatrix_nonneg' (φ : F) (k : Nat) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 <= M) :
    0 <= M.map φ

/-- Notation for a `CompletelyPositiveMap`. -/
scoped[CStarAlgebra] notation:25 A₁ " ->CP " A₂:0 => CompletelyPositiveMap A₁ A₂

namespace CompletelyPositiveMapClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂] [FunLike F A₁ A₂] [LinearMapClass F Complex A₁ A₂]

/-- Reinterpret an element of a type of completely positive maps as a completely positive linear
  map. -/
@[coe]
/--
Definition of `toCompletelyPositiveLinearMap` / `toCompletelyPositiveLinearMap` 的定义

English:
definition toCompletelyPositiveLinearMap
  signature: [CompletelyPositiveMapClass F A₁ A₂] (f : F)
  body: { (f : A₁ ->ₗ[Complex] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' f }

中文:
定义 toCompletelyPositiveLinearMap
  签名: [余mpletelyPositive映射类 F A₁ A₂] (f : F)
  定义体: { (f : A₁ ->ₗ[Complex] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' f }

Depends on / 依赖: CompletelyPositiveMapClass, CompletelyPositiveMapClass.map_cstarMatrix_nonneg, map_cstarMatrix_nonneg
-/
def toCompletelyPositiveLinearMap [CompletelyPositiveMapClass F A₁ A₂] (f : F) : A₁ ->CP A₂ :=
  { (f : A₁ ->ₗ[Complex] A₂) with
    map_cstarMatrix_nonneg' := CompletelyPositiveMapClass.map_cstarMatrix_nonneg' f }

/--
Instance `instCoeToCompletelyPositiveMap` / 实例 `instCoeToCompletelyPositiveMap`

English:
instance instCoeToCompletelyPositiveMap
  signature: [CompletelyPositiveMapClass F A₁ A₂]
  body: toCompletelyPositiveLinearMap f

中文:
实例 instCoeToCompletelyPositiveMap
  签名: [余mpletelyPositive映射类 F A₁ A₂]
  定义体: toCompletelyPositiveLinearMap f

Depends on / 依赖: toCompletelyPositiveLinearMap
-/
instance instCoeToCompletelyPositiveMap [CompletelyPositiveMapClass F A₁ A₂] :
    CoeHead F (A₁ ->CP A₂) where
  coe f := toCompletelyPositiveLinearMap f

set_option backward.isDefEq.respectTransparency false in
open CStarMatrix in
/--
lemma `_root_.OrderHomClass.of_map_cstarMatrix_nonneg` / 引理 `_root_.OrderHomClass.of_map_cstarMatrix_nonneg`

English:
lemma _root_.OrderHomClass.of_map_cstarMatrix_nonneg
  proof: .of_addMonoidHom by
  intro φ a ha
simpa using! map_nonneg (toOneByOne (Fin 1) Complex A₂).symm
h φ 1 _ map_nonneg (toOneByOne (Fin 1) Complex A₁) ha

中文:
引理 _root_.序态射类.of_map_cstarMatrix_nonneg
  证明: .of_addMonoidHom by
  intro φ a ha
simpa using! map_nonneg (toOneByOne (Fin 1) Complex A₂).symm
h φ 1 _ map_nonneg (toOneByOne (Fin 1) Complex A₁) ha

Depends on / 依赖: map_nonneg, of_addMonoidHom, toOneByOne
-/
lemma _root_.OrderHomClass.of_map_cstarMatrix_nonneg
    (h : forall (φ : F) (k : Nat) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 <= M -> 0 <= M.map φ) :
OrderHomClass F A₁ A₂ := .of_addMonoidHom by
  intro φ a ha
simpa using! map_nonneg (toOneByOne (Fin 1) Complex A₂).symm
h φ 1 _ map_nonneg (toOneByOne (Fin 1) Complex A₁) ha

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompletelyPositiveMapClass
  signature: F A₁ A₂] : OrderHomClass F A₁ A₂
  body: .of_map_cstarMatrix_nonneg CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

中文:
实例 [余mpletelyPositive映射类
  签名: F A₁ A₂] : 序态射类 F A₁ A₂
  定义体: .of_map_cstarMatrix_nonneg CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

Depends on / 依赖: CompletelyPositiveMapClass, CompletelyPositiveMapClass.map_cstarMatrix_nonneg, map_cstarMatrix_nonneg, of_map_cstarMatrix_nonneg
-/
instance [CompletelyPositiveMapClass F A₁ A₂] : OrderHomClass F A₁ A₂ :=
  .of_map_cstarMatrix_nonneg CompletelyPositiveMapClass.map_cstarMatrix_nonneg'

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

variable {A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A₁ ->CP A₂) A₁ A₂
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

中文:
实例 :
  签名: 函数状 (A₁ ->CP A₂) A₁ A₂
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

Depends on / 依赖: f.toFun
-/
instance : FunLike (A₁ ->CP A₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearMapClass (A₁ ->CP A₂) Complex A₁ A₂
  body: map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

中文:
实例 :
  签名: 线性映射类 (A₁ ->CP A₂) 复形 A₁ A₂
  定义体: map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

Depends on / 依赖: f.toLinearMap, map_add, toLinearMap
-/
instance : LinearMapClass (A₁ ->CP A₂) Complex A₁ A₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smulₛₗ f.toLinearMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompletelyPositiveMapClass (A₁ ->CP A₂) A₁ A₂
  body: f.map_cstarMatrix_nonneg'

中文:
实例 :
  签名: 余mpletelyPositive映射类 (A₁ ->CP A₂) A₁ A₂
  定义体: f.map_cstarMatrix_nonneg'

Depends on / 依赖: f.map_cstarMatrix_nonneg, map_cstarMatrix_nonneg
-/
instance : CompletelyPositiveMapClass (A₁ ->CP A₂) A₁ A₂ where
  map_cstarMatrix_nonneg' f := f.map_cstarMatrix_nonneg'

open CStarMatrix in
/--
lemma `map_cstarMatrix_nonneg` / 引理 `map_cstarMatrix_nonneg`

English:
lemma map_cstarMatrix_nonneg
  statement: {n : Type*} [Fintype n] (φ : A₁ ->CP A₂) (M : CStarMatrix n n A₁)
  proof: by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 <= (reindexₐ Complex A₁ e M).mapₗ (φ : A₁ ->ₗ[Complex] A₂) := by
    simp only [mapₗ, LinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
    exact CompletelyPositiveMapClass.map_cstarMatrix_

中文:
引理 map_cstarMatrix_nonneg
  结论: {n : 类型} [有限类型 n] (φ : A₁ ->CP A₂) (M : CStarMatrix n n A₁)
  证明: by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 <= (reindexₐ Complex A₁ e M).mapₗ (φ : A₁ ->ₗ[Complex] A₂) := by
    simp only [mapₗ, LinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
    exact CompletelyPositiveMapClass.map_cstarMatrix_

Depends on / 依赖: AddHom, AddHom.coe_mk, CompletelyPositiveMapClass, CompletelyPositiveMapClass.map_cstarMatrix_nonneg, Fintype, Fintype.card, Fintype.equivFinOfCardEq, LinearMap, LinearMap.coe_coe, LinearMap.coe_mk, coe_coe, coe_mk, equivFinOfCardEq, map_cstarMatrix_nonneg, map_nonneg
-/
lemma map_cstarMatrix_nonneg {n : Type*} [Fintype n] (φ : A₁ ->CP A₂) (M : CStarMatrix n n A₁)
    (hM : 0 <= M) : 0 <= M.map φ := by
  let k := Fintype.card n
  let e := Fintype.equivFinOfCardEq (rfl : Fintype.card n = k)
  have hmain : 0 <= (reindexₐ Complex A₁ e M).mapₗ (φ : A₁ ->ₗ[Complex] A₂) := by
    simp only [mapₗ, LinearMap.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
    exact CompletelyPositiveMapClass.map_cstarMatrix_nonneg' _ k _ (map_nonneg _ hM)
  rw [← mapₗ_reindexₐ] at hmain
  simpa [reindexₐ_symm] using map_nonneg (reindexₐ Complex A₂ e).symm hmain

end CompletelyPositiveMap

namespace NonUnitalStarAlgHomClass

variable {F A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂]
  [NonUnitalAlgHomClass F Complex A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix CFC in
/--
Instance `instCompletelyPositiveMapClass` / 实例 `instCompletelyPositiveMapClass`

English:
instance instCompletelyPositiveMapClass
  signature: : CompletelyPositiveMapClass F A₁ A₂ where
  body: by
    change 0 <= (mapₙₐ (φ : A₁ ->⋆ₙₐ[Complex] A₂)) M
    exact map_nonneg _ hM

中文:
实例 instCompletelyPositiveMapClass
  签名: : 余mpletelyPositive映射类 F A₁ A₂ where
  定义体: by
    change 0 <= (mapₙₐ (φ : A₁ ->⋆ₙₐ[Complex] A₂)) M
    exact map_nonneg _ hM

Depends on / 依赖: map_nonneg
-/
instance instCompletelyPositiveMapClass : CompletelyPositiveMapClass F A₁ A₂ where
  map_cstarMatrix_nonneg' φ k M hM := by
    change 0 <= (mapₙₐ (φ : A₁ ->⋆ₙₐ[Complex] A₂)) M
    exact map_nonneg _ hM

end NonUnitalStarAlgHomClass
