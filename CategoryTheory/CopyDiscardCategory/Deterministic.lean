/-
Copyright (c) 2025 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic

/-!
# Deterministic Morphisms in Copy-Discard Categories

Morphisms that preserve the copy operation perfectly.

A morphism `f : X → Y` is deterministic if copying then applying `f` to both copies equals applying
`f` then copying: `f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ f)`.

In probabilistic settings, these are morphisms without randomness. In cartesian categories, all
morphisms are deterministic.

## Main definitions

* `Deterministic` - Type class for morphisms that preserve copying

## Main results

* Identity morphisms are deterministic
* Composition of deterministic morphisms is deterministic

## Tags

deterministic, copy-discard category, comonoid morphism
-/

public section

universe v u

namespace CategoryTheory

open MonoidalCategory ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [CopyDiscardCategory.{v} C]

/-- A morphism is deterministic if it preserves the comonoid structure.

In probabilistic contexts, these are morphisms without randomness. -/
/-
**CategoryTheory.Deterministic** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：Deterministic {X Y : C} (f : X ⟶ Y)
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is deterministic if it preserves the comonoid structure.

In probabilistic contexts, these are morphisms without randomness.
-/
abbrev Deterministic {X Y : C} (f : X ⟶ Y) := IsComonHom f

namespace Deterministic

variable {X Y Z : C}

/-- Deterministic morphisms commute with copying. -/
/-
**CategoryTheory.Deterministic.copy_natural** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Deterministic`。
形式化陈述：copy_natural (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f otimesₘ 
f)
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsComonHom.hom_comul`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C} 
  {inst_2 : CategoryTheor…

--- 原说明 ---
Deterministic morphisms commute with copying.
-/
lemma copy_natural (f : X ⟶ Y) [Deterministic f] : f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) :=
  IsComonHom.hom_comul f

/-- Deterministic morphisms commute with discarding. -/
/-
**CategoryTheory.Deterministic.discard_natural** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Deterministic`。
形式化陈述：discard_natural (f : X ⟶ Y) [Deterministic f] : f ≫ ε[Y] = ε[X]
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsComonHom.hom_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}
   {inst_2 : CategoryTheor…

--- 原说明 ---
Deterministic morphisms commute with discarding.
-/
lemma discard_natural (f : X ⟶ Y) [Deterministic f] : f ≫ ε[Y] = ε[X] :=
  IsComonHom.hom_counit f

end Deterministic

end CategoryTheory

