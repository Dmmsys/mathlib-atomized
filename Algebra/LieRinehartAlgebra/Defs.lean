/-
Copyright (c) 2025 Sven Holtrop and Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Holtrop, Leonid Ryvkin
-/
module

public import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie-Rinehart algebras

This file defines Lie-Rinehart algebras and their morphisms. It also shows that the derivations of
a commutative algebra over a commutative Ring form such a Lie-Rinehart algebra.
Lie-Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

* [Rinehart, G. S., Differential forms on general commutative algebras. Zbl 0113.26204
  Trans. Am. Math. Soc. 108, 195-222 (1963).][rinehart_1963]

-/

@[expose] public section

/--
Definition of `LieRinehartRing` / `LieRinehartRing` 的定义

English:
class LieRinehartRing
  parameters: (A L : Type*) [CommRing A] [LieRing L]
  axioms and operations (3):
    - lie_smul_eq_mul'((a b : A) (x : L)) : ⁅a • x, b⁆ = a * ⁅x, b⁆
    - leibniz_mul_right'((x : L) (a b : A)) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
    - leibniz_smul_right'((x y : L) (a : A)) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

中文:
类 LieRinehartRing
  参数: (A L : 类型) [CommRing A] [LieRing L]
  公理与运算 (3 个):
    - lie_smul_eq_mul'((a b : A) (x : L)) : ⁅a • x, b⁆ = a * ⁅x, b⁆
    - leibniz_mul_right'((x : L) (a b : A)) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
    - leibniz_smul_right'((x y : L) (a : A)) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y
-/
class LieRinehartRing (A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] : Prop where
  lie_smul_eq_mul' (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆
  leibniz_mul_right' (x : L) (a b : A) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
  leibniz_smul_right' (x y : L) (a : A) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

/--
Definition of `LieRinehartAlgebra` / `LieRinehartAlgebra` 的定义

English:
class LieRinehartAlgebra
  parameters: (R A L : Type*) [CommRing A] [LieRing L]
  (no additional axioms)

中文:
类 LieRinehartAlgebra
  参数: (R A L : 类型) [CommRing A] [LieRing L]
  (无附加公理)
-/
class LieRinehartAlgebra (R A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [CommRing R] [Algebra R A] [LieAlgebra R L] : Prop extends
    IsScalarTower R A L, LieModule R L A

variable {R A₁ L₁ A₂ L₂ A₃ L₃ : Type*} [CommRing R]
  [CommRing A₁] [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁]
  [CommRing A₂] [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂]
  [CommRing A₃] [LieRing L₃] [Module A₃ L₃] [LieRingModule L₃ A₃]
  [Algebra R A₁] [LieAlgebra R L₁] [Algebra R A₂] [LieAlgebra R L₂]
  [Algebra R A₃] [LieAlgebra R L₃]
  {σ₁₂ : A₁ ->ₐ[R] A₂} {σ₂₃ : A₂ ->ₐ[R] A₃}

/--
lemma `LieRinehartRing.lie_smul_eq_mul` / 引理 `LieRinehartRing.lie_smul_eq_mul`

English:
lemma LieRinehartRing.lie_smul_eq_mul
  given: [LieRinehartRing A₁ L₁] (a b : A₁) (x : L₁)
  proof: LieRinehartRing.lie_smul_eq_mul' a b x

中文:
引理 LieRinehartRing.lie_smul_eq_mul
  条件: [LieRinehartRing A₁ L₁] (a b : A₁) (x : L₁)
  证明: LieRinehartRing.lie_smul_eq_mul' a b x
-/
@[simp] lemma LieRinehartRing.lie_smul_eq_mul [LieRinehartRing A₁ L₁] (a b : A₁) (x : L₁) :
  ⁅a • x, b⁆ = a * ⁅x, b⁆ := LieRinehartRing.lie_smul_eq_mul' a b x

/--
lemma `LieRinehartRing.leibniz_mul_right` / 引理 `LieRinehartRing.leibniz_mul_right`

English:
lemma LieRinehartRing.leibniz_mul_right
  given: [LieRinehartRing A₁ L₁] (x : L₁) (a b : A₁)
  proof: LieRinehartRing.leibniz_mul_right' x a b

中文:
引理 LieRinehartRing.leibniz_mul_right
  条件: [LieRinehartRing A₁ L₁] (x : L₁) (a b : A₁)
  证明: LieRinehartRing.leibniz_mul_right' x a b
-/
@[simp] lemma LieRinehartRing.leibniz_mul_right [LieRinehartRing A₁ L₁] (x : L₁) (a b : A₁) :
  ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b := LieRinehartRing.leibniz_mul_right' x a b

/--
lemma `LieRinehartRing.leibniz_smul_right` / 引理 `LieRinehartRing.leibniz_smul_right`

English:
lemma LieRinehartRing.leibniz_smul_right
  given: [LieRinehartRing A₁ L₁] (x y : L₁) (a : A₁)
  proof: LieRinehartRing.leibniz_smul_right' x y a

中文:
引理 LieRinehartRing.leibniz_smul_right
  条件: [LieRinehartRing A₁ L₁] (x y : L₁) (a : A₁)
  证明: LieRinehartRing.leibniz_smul_right' x y a
-/
@[simp] lemma LieRinehartRing.leibniz_smul_right [LieRinehartRing A₁ L₁] (x y : L₁) (a : A₁) :
  ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y := LieRinehartRing.leibniz_smul_right' x y a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRinehartRing A₁ (Derivation R A₁ A₁)
  body: rfl
  leibniz_mul_right' _ _ _ := by simp; ring
  leibniz_smul_right' _ _ _ := by ext; simp [Derivation.commutator_apply]; ring

中文:
实例 :
  签名: LieRinehartRing A₁ (Derivation R A₁ A₁)
  定义体: rfl
  leibniz_mul_right' _ _ _ := by simp; ring
  leibniz_smul_right' _ _ _ := by ext; simp [Derivation.commutator_apply]; ring
-/
instance : LieRinehartRing A₁ (Derivation R A₁ A₁) where
  lie_smul_eq_mul' _ _ _ := rfl
  leibniz_mul_right' _ _ _ := by simp; ring
  leibniz_smul_right' _ _ _ := by ext; simp [Derivation.commutator_apply]; ring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRinehartAlgebra R A₁ (Derivation R A₁ A₁)

中文:
实例 :
  签名: LieRinehartAlgebra R A₁ (Derivation R A₁ A₁)
-/
instance : LieRinehartAlgebra R A₁ (Derivation R A₁ A₁) where

namespace LieRinehartAlgebra

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (σ : A₁ ->ₐ[R] A₂) (L₁ L₂ : Type*)
  extends: L₁ ->ₗ⁅R⁆ L₂
  axioms and operations (2):
    - map_smul_apply'((a : A₁) (x : L₁)) : toLieHom (a • x) = σ a • toLieHom x
    - apply_lie'((a : A₁) (x : L₁)) : σ ⁅x, a⁆ = ⁅toLieHom x, σ a⁆

中文:
结构 Hom
  参数: (σ : A₁ ->ₐ[R] A₂) (L₁ L₂ : 类型)
  继承: L₁ ->ₗ⁅R⁆ L₂
  公理与运算 (2 个):
    - map_smul_apply'((a : A₁) (x : L₁)) : toLieHom (a • x) = σ a • toLieHom x
    - apply_lie'((a : A₁) (x : L₁)) : σ ⁅x, a⁆ = ⁅toLieHom x, σ a⁆
-/
structure Hom (σ : A₁ ->ₐ[R] A₂) (L₁ L₂ : Type*)
    [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁] [LieAlgebra R L₁]
    [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂] [LieAlgebra R L₂]
    extends L₁ ->ₗ⁅R⁆ L₂ where
  map_smul_apply' (a : A₁) (x : L₁) : toLieHom (a • x) = σ a • toLieHom x
  apply_lie' (a : A₁) (x : L₁) : σ ⁅x, a⁆ = ⁅toLieHom x, σ a⁆

@[inherit_doc]
scoped notation:25 L " ->ₗ⁅" σ:25 "⁆ " L₂:0 => LieRinehartAlgebra.Hom σ L L₂

namespace Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (L₁ ->ₗ⁅σ₁₂⁆ L₂) (fun _ => L₁ -> L₂)
  body: ⟨fun f => f.toLieHom⟩

中文:
实例 :
  签名: CoeFun (L₁ ->ₗ⁅σ₁₂⁆ L₂) (fun _ => L₁ -> L₂)
  定义体: ⟨fun f => f.toLieHom⟩

Depends on / 依赖: f.toLieHom, toLieHom
-/
instance : CoeFun (L₁ ->ₗ⁅σ₁₂⁆ L₂) (fun _ => L₁ -> L₂) := ⟨fun f => f.toLieHom⟩

/--
lemma `map_smul_apply` / 引理 `map_smul_apply`

English:
lemma map_smul_apply
  given: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁)
  proof: f.map_smul_apply' a x

中文:
引理 map_smul_apply
  条件: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁)
  证明: f.map_smul_apply' a x

Depends on / 依赖: f.map_smul_apply, map_smul_apply
-/
lemma map_smul_apply (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    f (a • x) = σ₁₂ a • f x :=
  f.map_smul_apply' a x

/--
lemma `apply_lie` / 引理 `apply_lie`

English:
lemma apply_lie
  given: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁)
  proof: f.apply_lie' a x

中文:
引理 apply_lie
  条件: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁)
  证明: f.apply_lie' a x

Depends on / 依赖: apply_lie, f.apply_lie
-/
lemma apply_lie (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    σ₁₂ ⁅x, a⁆ = ⁅f x, σ₁₂ a⁆ :=
  f.apply_lie' a x

/--
Definition of `toLinearMap'` / `toLinearMap'` 的定义

English:
definition toLinearMap'
  signature: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂)
  body: f
  map_add' := f.map_add'
  map_smul' := f.map_smul_apply

中文:
定义 toLinearMap'
  签名: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂)
  定义体: f
  map_add' := f.map_add'
  map_smul' := f.map_smul_apply
-/
def toLinearMap' (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) : L₁ ->ₛₗ[σ₁₂.toRingHom] L₂ where
  toFun := f
  map_add' := f.map_add'
  map_smul' := f.map_smul_apply

/--
lemma `toLinearMap'_apply` / 引理 `toLinearMap'_apply`

English:
lemma toLinearMap'_apply
  given: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (x : L₁)
  statement: f.toLinearMap' x = f x
  proof: rfl

中文:
引理 toLinearMap'_apply
  条件: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (x : L₁)
  结论: f.toLinearMap' x = f x
  证明: rfl
-/
@[simp] lemma toLinearMap'_apply (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (x : L₁) : f.toLinearMap' x = f x := rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (g : L₂ ->ₗ⁅σ₂₃⁆ L₃)
  body: g.toLieHom.comp f.toLieHom
  map_smul_apply' _ _ := by simp [Hom.map_smul_apply]
  apply_lie' _ _ := by simp [f.apply_lie, g.apply_lie]

中文:
定义 comp
  签名: (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (g : L₂ ->ₗ⁅σ₂₃⁆ L₃)
  定义体: g.toLieHom.comp f.toLieHom
  map_smul_apply' _ _ := by simp [Hom.map_smul_apply]
  apply_lie' _ _ := by simp [f.apply_lie, g.apply_lie]
-/
protected def comp (f : L₁ ->ₗ⁅σ₁₂⁆ L₂) (g : L₂ ->ₗ⁅σ₂₃⁆ L₃) : L₁ ->ₗ⁅σ₂₃.comp σ₁₂⁆ L₃ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_smul_apply' _ _ := by simp [Hom.map_smul_apply]
  apply_lie' _ _ := by simp [f.apply_lie, g.apply_lie]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : L₁ ->ₗ⁅AlgHom.id R A₁⁆ L₁ where
  body: LieHom.id
  map_smul_apply' _ _ := by simp
  apply_lie' _ _ := by simp

中文:
定义 id
  签名: : L₁ ->ₗ⁅AlgHom.id R A₁⁆ L₁ where
  定义体: LieHom.id
  map_smul_apply' _ _ := by simp
  apply_lie' _ _ := by simp
-/
protected def id : L₁ ->ₗ⁅AlgHom.id R A₁⁆ L₁ where
  __ := LieHom.id
  map_smul_apply' _ _ := by simp
  apply_lie' _ _ := by simp

end Hom

variable [LieRinehartRing A₁ L₁] [LieRinehartAlgebra R A₁ L₁]

variable (R A₁ L₁) in
/--
Definition of `anchor` / `anchor` 的定义

English:
definition anchor
  signature: : L₁ ->ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where
  body: .mk' (LieModule.toEnd R L₁ A₁ x) fun a b => by
    simp [mul_comm b]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp [Derivation.commutator_apply]
  map_smul_apply' _ _ := by ext; simp
  apply_lie' _ _ := by simp

中文:
定义 anchor
  签名: : L₁ ->ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where
  定义体: .mk' (LieModule.toEnd R L₁ A₁ x) fun a b => by
    simp [mul_comm b]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp [Derivation.commutator_apply]
  map_smul_apply' _ _ := by ext; simp
  apply_lie' _ _ := by simp

Depends on / 依赖: Derivation, Derivation.commutator_apply, LieModule, LieModule.toEnd, apply_lie, commutator_apply, map_add, map_lie, map_smul, map_smul_apply, mul_comm
-/
def anchor : L₁ ->ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where
  toFun x := .mk' (LieModule.toEnd R L₁ A₁ x) fun a b => by
    simp [mul_comm b]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp [Derivation.commutator_apply]
  map_smul_apply' _ _ := by ext; simp
  apply_lie' _ _ := by simp

/--
lemma `anchor_derivation` / 引理 `anchor_derivation`

English:
lemma anchor_derivation
  statement: anchor R A₁ (Derivation R A₁ A₁) = Hom.id
  proof: rfl

中文:
引理 anchor_derivation
  结论: anchor R A₁ (Derivation R A₁ A₁) = Hom.id
  证明: rfl
-/
@[simp] lemma anchor_derivation : anchor R A₁ (Derivation R A₁ A₁) = Hom.id := rfl

/--
lemma `anchor_apply` / 引理 `anchor_apply`

English:
lemma anchor_apply
  given: (l : L₁) (a : A₁)
  proof: rfl

中文:
引理 anchor_apply
  条件: (l : L₁) (a : A₁)
  证明: rfl
-/
@[simp] lemma anchor_apply (l : L₁) (a : A₁) :
  (LieRinehartAlgebra.anchor R A₁ L₁ l) a = ⁅l, a⁆ := rfl

end LieRinehartAlgebra
