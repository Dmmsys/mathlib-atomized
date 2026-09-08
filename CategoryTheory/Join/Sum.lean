/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Join.Basic
public import Mathlib.CategoryTheory.Sums.Basic

/-!
# Embedding of `C ⊕ D` into `C ⋆ D`

This file constructs a canonical functor `Join.fromSum` from `C ⊕ D` to `C ⋆ D` and gives
its characterization in terms of the canonical inclusions.
We also provide `Faithful` and `EssSurj` instances on this functor.

-/

@[expose] public section

namespace CategoryTheory.Join

variable (C D : Type*) [Category* C] [Category* D]

/-- The canonical functor from the sum to the join.
It sends `inl c` to `left c` and `inr d` to `right d`. -/
@[simps! obj] -- Maps get characterized w.r.t. the inclusions below
/-
**CategoryTheory.Join.fromSum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Join`。
形式化陈述：fromSum : C oplus D ⥤ C ⋆ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor from the sum to the join.
It sends `inl c` to `left c` and `inr d` to `right d`.
-/
def fromSum : C ⊕ D ⥤ C ⋆ D := (inclLeft C D).sum' <| inclRight C D

variable {C} in
@[simp]
/-
**CategoryTheory.Join.fromSum_map_inl** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Join`。
形式化陈述：fromSum_map_inl {c c' : C} (f : c ⟶ c') : (fromSum C D).map ((Sum.inl_ C D
).map f) = (inclLeft C D).map f
参数：f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSum_map_inl {c c' : C} (f : c ⟶ c') :
    (fromSum C D).map ((Sum.inl_ C D).map f) = (inclLeft C D).map f :=
  rfl

variable {D} in
@[simp]
/-
**CategoryTheory.Join.fromSum_map_inr** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Join`。
形式化陈述：fromSum_map_inr {d d' : D} (f : d ⟶ d') : (fromSum C D).map ((Sum.inr_ C D
).map f) = (inclRight C D).map f
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSum_map_inr {d d' : D} (f : d ⟶ d') :
    (fromSum C D).map ((Sum.inr_ C D).map f) = (inclRight C D).map f :=
  rfl

/-- Characterization of `fromSum` with respect to the left inclusion. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Join.inlCompFromSum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.J
oin`。
形式化陈述：inlCompFromSum : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of `fromSum` with respect to the left inclusion.
-/
def inlCompFromSum : Sum.inl_ C D ⋙ fromSum C D ≅ inclLeft C D := Functor.inlCompSum' _ _

/-- Characterization of `fromSum` with respect to the right inclusion. -/
@[simps! hom_app inv_app]
/-
**CategoryTheory.Join.inrCompFromSum** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.J
oin`。
形式化陈述：inrCompFromSum : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of `fromSum` with respect to the right inclusion.
-/
def inrCompFromSum : Sum.inr_ C D ⋙ fromSum C D ≅ inclRight C D := Functor.inrCompSum' _ _
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromSum C D).EssSurj where
  mem_essImage
    | left c => Functor.obj_mem_essImage _ (Sum.inl c)
    | right d => Functor.obj_mem_essImage _ (Sum.inr d)
/-
**CategoryTheory.Join.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Join`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromSum C D).Faithful where
  map_injective {x y} h h' heq := by
    cases h <;> cases h'
    all_goals
      simp only [fromSum_map_inl, fromSum_map_inr] at heq
      simp [Functor.map_injective _ heq]

end CategoryTheory.Join

