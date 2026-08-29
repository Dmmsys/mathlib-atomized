/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Logic.Function.CompTypeclasses
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Propositional typeclasses on several monoid homs

This file contains typeclasses used in the definition of equivariant maps,
in the spirit what was initially developed by Frédéric Dupuis and Heather Macbeth for linear maps.
However, we do not expect that all maps should be guessed automatically,
as it happens for linear maps.

If `φ`, `ψ`… are monoid homs and `M`, `N`… are monoids, we add two instances:
* `MonoidHom.CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `MonoidHom.IsId φ`, which expresses that `φ = id`

Some basic lemmas are proved:
* `MonoidHom.CompTriple.comp` asserts `MonoidHom.CompTriple φ ψ (ψ.comp φ)`
* `MonoidHom.CompTriple.id_comp` asserts `MonoidHom.CompTriple φ ψ ψ`
  in the presence of `MonoidHom.IsId φ`
* its variant `MonoidHom.CompTriple.comp_id`

TODO :
* align with RingHomCompTriple
* probably rename MonoidHom.CompTriple as MonoidHomCompTriple
  (or, on the opposite, rename RingHomCompTriple as RingHom.CompTriple)
* does one need AddHom.CompTriple ?

-/

public section

section MonoidHomCompTriple

namespace MonoidHom

/--
Definition of `CompTriple` / `CompTriple` 的定义

English:
class CompTriple
  parameters: {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
  axioms and operations (1):
    - comp_eq : ψ.comp φ = χ

中文:
类 CompTriple
  参数: {M N P : 类型} [Monoid M] [Monoid N] [Monoid P]
  公理与运算 (1 个):
    - comp_eq : ψ.comp φ = χ
-/
class CompTriple {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (φ : M ->* N) (ψ : N ->* P) (χ : outParam (M ->* P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

/--
Definition of `IsId` / `IsId` 的定义

English:
class IsId
  parameters: (σ : M ->* M)
  axioms and operations (1):
    - eq_id : σ = MonoidHom.id M

中文:
类 IsId
  参数: (σ : M ->* M)
  公理与运算 (1 个):
    - eq_id : σ = MonoidHom.id M
-/
class IsId (σ : M ->* M) : Prop where
  eq_id : σ = MonoidHom.id M

/--
Instance `instIsId` / 实例 `instIsId`

English:
instance instIsId
  signature: {M : Type*} [Monoid M]
  body: rfl

中文:
实例 instIsId
  签名: {M : 类型} [Monoid M]
  定义体: rfl
-/
instance instIsId {M : Type*} [Monoid M] : IsId (MonoidHom.id M) where
  eq_id := rfl

instance {σ : M ->* M} [h : _root_.CompTriple.IsId σ] : IsId σ where
  eq_id := by ext; exact congr_fun h.eq_id _

/--
Instance `instComp_id` / 实例 `instComp_id`

English:
instance instComp_id
  signature: {N P : Type*} [Monoid N] [Monoid P]
  body: by simp only [IsId.eq_id, MonoidHom.comp_id]

中文:
实例 instComp_id
  签名: {N P : 类型} [Monoid N] [Monoid P]
  定义体: by simp only [IsId.eq_id, MonoidHom.comp_id]

Depends on / 依赖: IsId.eq_id, MonoidHom, MonoidHom.comp_id, comp_id, eq_id
-/
instance instComp_id {N P : Type*} [Monoid N] [Monoid P]
    {φ : N ->* N} [IsId φ] {ψ : N ->* P} :
    CompTriple φ ψ ψ where
  comp_eq := by simp only [IsId.eq_id, MonoidHom.comp_id]

/--
Instance `instId_comp` / 实例 `instId_comp`

English:
instance instId_comp
  signature: {M N : Type*} [Monoid M] [Monoid N]
  body: by simp only [IsId.eq_id, MonoidHom.id_comp]

中文:
实例 instId_comp
  签名: {M N : 类型} [Monoid M] [Monoid N]
  定义体: by simp only [IsId.eq_id, MonoidHom.id_comp]

Depends on / 依赖: IsId.eq_id, MonoidHom, MonoidHom.id_comp, eq_id, id_comp
-/
instance instId_comp {M N : Type*} [Monoid M] [Monoid N]
    {φ : M ->* N} {ψ : N ->* N} [IsId ψ] :
    CompTriple φ ψ φ where
  comp_eq := by simp only [IsId.eq_id, MonoidHom.id_comp]

/--
lemma `comp_inv` / 引理 `comp_inv`

English:
lemma comp_inv
  statement: {φ : M ->* N} {ψ : N ->* M} (h : Function.RightInverse φ ψ)
  proof: by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]

中文:
引理 comp_inv
  结论: {φ : M ->* N} {ψ : N ->* M} (h : Function.RightInverse φ ψ)
  证明: by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]

Depends on / 依赖: DFunLike, DFunLike.coe_fn_eq, IsId.eq_id, coe_comp, coe_fn_eq, coe_id, eq_id, h.id
-/
lemma comp_inv {φ : M ->* N} {ψ : N ->* M} (h : Function.RightInverse φ ψ)
    {χ : M ->* M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_id]

/--
Instance `instRootCompTriple` / 实例 `instRootCompTriple`

English:
instance instRootCompTriple
  signature: {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} [κ : CompTriple φ ψ χ]
  body: by rw [← MonoidHom.coe_comp, κ.comp_eq]

中文:
实例 instRootCompTriple
  签名: {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} [κ : CompTriple φ ψ χ]
  定义体: by rw [← MonoidHom.coe_comp, κ.comp_eq]

Depends on / 依赖: MonoidHom, MonoidHom.coe_comp, coe_comp, comp_eq
-/
instance instRootCompTriple {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} [κ : CompTriple φ ψ χ] :
    _root_.CompTriple φ ψ χ where
  comp_eq := by rw [← MonoidHom.coe_comp, κ.comp_eq]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {φ : M ->* N} {ψ : N ->* P}
  proof: rfl

中文:
定理 comp
  条件: {φ : M ->* N} {ψ : N ->* P}
  证明: rfl
-/
theorem comp {φ : M ->* N} {ψ : N ->* P} :
    CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  proof: by
  rw [← h.comp_eq]; rw [MonoidHom.comp_apply]

中文:
引理 comp_apply
  证明: by
  rw [← h.comp_eq]; rw [MonoidHom.comp_apply]

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, comp_apply, comp_eq, h.comp_eq
-/
lemma comp_apply
    {φ : M ->* N} {ψ : N ->* P} {χ : M ->* P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq]; rw [MonoidHom.comp_apply]

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {Q : Type*} [Monoid Q]
  proof: by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

中文:
定理 comp_assoc
  结论: {Q : 类型} [Monoid Q]
  证明: by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

Depends on / 依赖: MonoidHom, MonoidHom.comp_assoc, comp_assoc, comp_eq
-/
theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M ->* N} {φ₂ : N ->* P} {φ₁₂ : M ->* P}
    (κ : CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P ->* Q} {φ₂₃ : N ->* Q} (κ' : CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M ->* Q} :
    CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

end MonoidHom.CompTriple

end MonoidHomCompTriple
