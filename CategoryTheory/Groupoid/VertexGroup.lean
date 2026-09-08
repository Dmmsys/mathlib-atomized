/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Combinatorics.Quiver.Path

/-!
# Vertex group

This file defines the vertex group (*aka* isotropy group) of a groupoid at a vertex.

## Implementation notes

* The instance is defined "manually", instead of relying on `CategoryTheory.Aut.group` or
  using `CategoryTheory.inv`.
* The multiplication order therefore matches the categorical one: `x * y = x ≫ y`.
* The inverse is directly defined in terms of the groupoidal inverse: `x ⁻¹ = Groupoid.inv x`.

## Tags

isotropy, vertex group, groupoid
-/

@[expose] public section


namespace CategoryTheory

namespace Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- The vertex group at `c`. -/
@[simps mul one inv]
/-
**CategoryTheory.Groupoid.vertexGroup** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Groupoid`。
形式化陈述：vertexGroup (c : C) : Group (c ⟶ c) where mul
参数：c : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Groupoid.inv_comp`：∀ {obj : Type u} [self : CategoryTheor
y.Groupoid obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (C
ategoryTheory.Groupoid…

--- 原说明 ---
The vertex group at `c`.
-/
instance vertexGroup (c : C) : Group (c ⟶ c) where
  mul := fun x y : c ⟶ c => x ≫ y
  mul_assoc := Category.assoc
  one := 𝟙 c
  one_mul := Category.id_comp
  mul_one := Category.comp_id
  inv := Groupoid.inv
  inv_mul_cancel := inv_comp

/-- The inverse in the group is equal to the inverse given by `CategoryTheory.inv`. -/
/-
**CategoryTheory.Groupoid.vertexGroup.inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Groupoid.vertexGroup`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Groupoid C] (c : C) (γ : c ⟶ c), γ⁻¹
 = CategoryTheory.inv γ
参数：c : C；γ : c ⟶ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Groupoid.inv_eq_inv`：∀ {C : Type u} [inst : CategoryTheor
y.Groupoid C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Groupoid.inv f = CategoryT
heory.inv f

--- 原说明 ---
The inverse in the group is equal to the inverse given by `CategoryTheory.inv`.
-/
theorem vertexGroup.inv_eq_inv (c : C) (γ : c ⟶ c) : γ⁻¹ = CategoryTheory.inv γ :=
  Groupoid.inv_eq_inv γ

/-- An arrow in the groupoid defines, by conjugation, an isomorphism of groups between
its endpoints.
-/
@[simps]
/-
**CategoryTheory.Groupoid.vertexGroupIsomOfMap** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Groupoid`。
形式化陈述：vertexGroupIsomOfMap {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) where toFu
n γ
参数：f : c ⟶ d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow in the groupoid defines, by conjugation, an isomorphism of groups betwe
en
its endpoints.
-/
def vertexGroupIsomOfMap {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) where
  toFun γ := inv f ≫ γ ≫ f
  invFun δ := f ≫ δ ≫ inv f
  left_inv γ := by
    simp_rw [Category.assoc, comp_inv, Category.comp_id, ← Category.assoc, comp_inv,
      Category.id_comp]
  right_inv δ := by
    simp_rw [Category.assoc, inv_comp, ← Category.assoc, inv_comp, Category.id_comp,
      Category.comp_id]
  map_mul' γ₁ γ₂ := by
    simp only [vertexGroup_mul, inv_eq_inv, Category.assoc, IsIso.hom_inv_id_assoc]

/-- A path in the groupoid defines an isomorphism between its endpoints.
-/
/-
**CategoryTheory.Groupoid.vertexGroupIsomOfPath** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Groupoid`。
形式化陈述：vertexGroupIsomOfPath {c d : C} (p : Quiver.Path c d) : (c ⟶ c) ≃* (d ⟶ d)
参数：p : Quiver.Path c d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertexGroupIsomOfPath {c d : C} (p : Quiver.Path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
  vertexGroupIsomOfMap (composePath p)

/-- A functor defines a morphism of vertex groups. -/
@[simps]
/-
**CategoryTheory.Groupoid._root_.CategoryTheory.Functor.mapVertexGroup** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Groupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor defines a morphism of vertex groups.
-/
def _root_.CategoryTheory.Functor.mapVertexGroup {D : Type v} [Groupoid D] (φ : C ⥤ D) (c : C) :
    (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) where
  toFun := φ.map
  map_one' := φ.map_id c
  map_mul' := φ.map_comp

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias CategoryTheory.Functor.mapVertexGroup := CategoryTheory.Functor.mapVertexGroup

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")]
alias CategoryTheory.Functor.mapVertexGroup_apply := CategoryTheory.Functor.mapVertexGroup_apply

end Groupoid

end CategoryTheory

