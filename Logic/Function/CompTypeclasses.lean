/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Init

/-!
# Propositional typeclasses on several maps

This file contains typeclasses that are used in the definition of
equivariant maps in the spirit what was initially developed
by Frédéric Dupuis and Heather Macbeth for linear maps.

* `CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `CompTriple.IsId φ`, which expresses that `φ = id`

TODO :
* align with RingHomCompTriple

-/

public section

section CompTriple

/--
Definition of `CompTriple` / `CompTriple` 的定义

English:
class CompTriple
  parameters: {M N P : Type*} (φ : M -> N) (ψ : N -> P) (χ : outParam (M -> P))
  axioms and operations (1):
    - comp_eq : ψ.comp φ = χ

中文:
类 余mpTriple
  参数: {M N P : 类型} (φ : M -> N) (ψ : N -> P) (χ : outParam (M -> P))
  公理与运算 (1 个):
    - comp_eq : ψ.comp φ = χ
-/
class CompTriple {M N P : Type*} (φ : M -> N) (ψ : N -> P) (χ : outParam (M -> P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

/--
Definition of `IsId` / `IsId` 的定义

English:
class IsId
  parameters: {M : Type*} (σ : M -> M)
  axioms and operations (1):
    - eq_id : σ = id

中文:
类 是Id
  参数: {M : 类型} (σ : M -> M)
  公理与运算 (1 个):
    - eq_id : σ = id
-/
class IsId {M : Type*} (σ : M -> M) : Prop where
  eq_id : σ = id

instance {M : Type*} : IsId (@id M) where
  eq_id := rfl

/--
Instance `instComp_id` / 实例 `instComp_id`

English:
instance instComp_id
  signature: {N P : Type*} {φ : N -> N} [IsId φ] {ψ : N -> P}
  body: by simp only [IsId.eq_id, Function.comp_id]

中文:
实例 instComp_id
  签名: {N P : 类型} {φ : N -> N} [是Id φ] {ψ : N -> P}
  定义体: by simp only [IsId.eq_id, Function.comp_id]

Depends on / 依赖: Function, Function.comp_id, IsId.eq_id, comp_id, eq_id
-/
instance instComp_id {N P : Type*} {φ : N -> N} [IsId φ] {ψ : N -> P} :
    CompTriple φ ψ ψ where
  comp_eq := by simp only [IsId.eq_id, Function.comp_id]

/--
Instance `instId_comp` / 实例 `instId_comp`

English:
instance instId_comp
  signature: {M N : Type*} {φ : M -> N} {ψ : N -> N} [IsId ψ]
  body: by simp only [IsId.eq_id, Function.id_comp]

中文:
实例 instId_comp
  签名: {M N : 类型} {φ : M -> N} {ψ : N -> N} [是Id ψ]
  定义体: by simp only [IsId.eq_id, Function.id_comp]

Depends on / 依赖: Function, Function.id_comp, IsId.eq_id, eq_id, id_comp
-/
instance instId_comp {M N : Type*} {φ : M -> N} {ψ : N -> N} [IsId ψ] :
    CompTriple φ ψ φ where
  comp_eq := by simp only [IsId.eq_id, Function.id_comp]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {M N P : Type*}
  proof: rfl

中文:
定理 comp
  结论: {M N P : 类型}
  证明: rfl
-/
theorem comp {M N P : Type*}
    {φ : M -> N} {ψ : N -> P} :
    CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl

/--
lemma `comp_inv` / 引理 `comp_inv`

English:
lemma comp_inv
  statement: {M N : Type*} {φ : M -> N} {ψ : N -> M}
  proof: by simp only [IsId.eq_id, h.id]

中文:
引理 comp_inv
  结论: {M N : 类型} {φ : M -> N} {ψ : N -> M}
  证明: by simp only [IsId.eq_id, h.id]

Depends on / 依赖: IsId.eq_id, eq_id, h.id
-/
lemma comp_inv {M N : Type*} {φ : M -> N} {ψ : N -> M}
    (h : Function.RightInverse φ ψ) {χ : M -> M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, h.id]

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  statement: {M N P : Type*}
  proof: by
  rw [← h.comp_eq]; rw [Function.comp_apply]

中文:
引理 comp_apply
  结论: {M N P : 类型}
  证明: by
  rw [← h.comp_eq]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, comp_eq, h.comp_eq
-/
lemma comp_apply {M N P : Type*}
    {φ : M -> N} {ψ : N -> P} {χ : M -> P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq]; rw [Function.comp_apply]

end CompTriple

end CompTriple
