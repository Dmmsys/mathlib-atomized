/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic.Common

/-!
# Lemmas about the divisibility relation in product (semi)groups
-/

public section

variable {ι G₁ G₂ : Type*} {G : ι -> Type*} [Semigroup G₁] [Semigroup G₂] [forall i, Semigroup (G i)]

/--
theorem `prod_dvd_iff` / 定理 `prod_dvd_iff`

English:
theorem prod_dvd_iff
  given: {x y : G₁ × G₂}
  proof: by
  cases x; cases y
  simp only [dvd_def, Prod.exists, Prod.mk_mul_mk, Prod.mk.injEq,
    exists_and_left, exists_and_right]

@[simp]

中文:
定理 prod_dvd_iff
  条件: {x y : G₁ × G₂}
  证明: by
  cases x; cases y
  simp only [dvd_def, Prod.exists, Prod.mk_mul_mk, Prod.mk.injEq,
    exists_and_left, exists_and_right]

@[simp]

Depends on / 依赖: Prod.exists, Prod.mk.injEq, Prod.mk_mul_mk, dvd_def, exists_and_left, exists_and_right, mk_mul_mk
-/
theorem prod_dvd_iff {x y : G₁ × G₂} :
    x ∣ y ↔ x.1 ∣ y.1 ∧ x.2 ∣ y.2 := by
  cases x; cases y
  simp only [dvd_def, Prod.exists, Prod.mk_mul_mk, Prod.mk.injEq,
    exists_and_left, exists_and_right]

@[simp]
/--
theorem `Prod.mk_dvd_mk` / 定理 `Prod.mk_dvd_mk`

English:
theorem Prod.mk_dvd_mk
  given: {x₁ y₁ : G₁} {x₂ y₂ : G₂}
  proof: prod_dvd_iff

中文:
定理 积类型.mk_dvd_mk
  条件: {x₁ y₁ : G₁} {x₂ y₂ : G₂}
  证明: prod_dvd_iff

Depends on / 依赖: prod_dvd_iff
-/
theorem Prod.mk_dvd_mk {x₁ y₁ : G₁} {x₂ y₂ : G₂} :
    (x₁, x₂) ∣ (y₁, y₂) ↔ x₁ ∣ y₁ ∧ x₂ ∣ y₂ :=
  prod_dvd_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecompositionMonoid
  signature: G₁] [DecompositionMonoid G₂] : DecompositionMonoid (G₁ × G₂) where
  body: by
    simp_rw [prod_dvd_iff] at h ⊢
    obtain ⟨a₁, a₁', h₁, h₁', eq₁⟩ := DecompositionMonoid.primal a.1 h.1
    obtain ⟨a₂, a₂', h₂, h₂', eq₂⟩ := DecompositionMonoid.primal a.2 h.2
    -- aesop works here
    exact ⟨(a₁, a₂), (a₁', a₂'), ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩, Prod.ext eq₁ eq₂⟩

中文:
实例 [分解幺半群
  签名: G₁] [分解幺半群 G₂] : 分解幺半群 (G₁ × G₂) where
  定义体: by
    simp_rw [prod_dvd_iff] at h ⊢
    obtain ⟨a₁, a₁', h₁, h₁', eq₁⟩ := DecompositionMonoid.primal a.1 h.1
    obtain ⟨a₂, a₂', h₂, h₂', eq₂⟩ := DecompositionMonoid.primal a.2 h.2
    -- aesop works here
    exact ⟨(a₁, a₂), (a₁', a₂'), ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩, Prod.ext eq₁ eq₂⟩

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, primal, prod_dvd_iff, simp_rw
-/
instance [DecompositionMonoid G₁] [DecompositionMonoid G₂] : DecompositionMonoid (G₁ × G₂) where
  primal a b c h := by
    simp_rw [prod_dvd_iff] at h ⊢
    obtain ⟨a₁, a₁', h₁, h₁', eq₁⟩ := DecompositionMonoid.primal a.1 h.1
    obtain ⟨a₂, a₂', h₂, h₂', eq₂⟩ := DecompositionMonoid.primal a.2 h.2
    -- aesop works here
    exact ⟨(a₁, a₂), (a₁', a₂'), ⟨h₁, h₂⟩, ⟨h₁', h₂'⟩, Prod.ext eq₁ eq₂⟩

/--
theorem `pi_dvd_iff` / 定理 `pi_dvd_iff`

English:
theorem pi_dvd_iff
  given: {x y : forall i, G i}
  statement: x ∣ y ↔ forall i, x i ∣ y i
  proof: by
  simp_rw [dvd_def, funext_iff, Classical.skolem]; rfl

中文:
定理 pi_dvd_iff
  条件: {x y : 对任意 i, G i}
  结论: x ∣ y ↔ 对任意 i, x i ∣ y i
  证明: by
  simp_rw [dvd_def, funext_iff, Classical.skolem]; rfl

Depends on / 依赖: Classical, Classical.skolem, dvd_def, funext_iff, simp_rw, skolem
-/
theorem pi_dvd_iff {x y : forall i, G i} : x ∣ y ↔ forall i, x i ∣ y i := by
  simp_rw [dvd_def, funext_iff, Classical.skolem]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, DecompositionMonoid (G i)] : DecompositionMonoid (forall i, G i) where
  body: by
    simp_rw [pi_dvd_iff] at h ⊢
    choose a₁ a₂ h₁ h₂ eq using fun i => DecompositionMonoid.primal _ (h i)
    exact ⟨a₁, a₂, h₁, h₂, funext eq⟩

中文:
实例 [对任意
  签名: i, 分解幺半群 (G i)] : 分解幺半群 (对任意 i, G i) where
  定义体: by
    simp_rw [pi_dvd_iff] at h ⊢
    choose a₁ a₂ h₁ h₂ eq using fun i => DecompositionMonoid.primal _ (h i)
    exact ⟨a₁, a₂, h₁, h₂, funext eq⟩

Depends on / 依赖: DecompositionMonoid, DecompositionMonoid.primal, pi_dvd_iff, primal, simp_rw
-/
instance [forall i, DecompositionMonoid (G i)] : DecompositionMonoid (forall i, G i) where
  primal a b c h := by
    simp_rw [pi_dvd_iff] at h ⊢
    choose a₁ a₂ h₁ h₂ eq using fun i => DecompositionMonoid.primal _ (h i)
    exact ⟨a₁, a₂, h₁, h₂, funext eq⟩
