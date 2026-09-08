/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
## Locally directed gluing

We say that a diagram of sets is "locally directed" if for any `V, W ⊆ U` in the diagram,
`V ∩ W` is a union of elements in the diagram. Equivalently, for every `x ∈ U` in the diagram,
the set of elements containing `x` is directed (and hence the name).

This is the condition needed to show that a colimit (in `TopCat`) of open embeddings is the
gluing of the open sets. See `Mathlib/AlgebraicGeometry/Gluing.lean` for an actual application.
-/

public section

namespace CategoryTheory

open Limits

variable {J : Type*} [Category* J]

/--
We say that a functor `F` to `Type*` is locally directed if for every `x ∈ F.obj k`, the
set of `F.obj` containing `x` is (co)directed.
That is, for each diagram
```
      x ∈ Fₖ
    ↗       ↖
xᵢ ∈ Fᵢ    xⱼ ∈ Fⱼ
```
there exists
```
xᵢ ∈ Fᵢ    xⱼ ∈ Fⱼ
    ↖       ↗
      xₗ ∈ Fₗ
```
that commutes with it.
-/
/-
**CategoryTheory.Functor.IsLocallyDirected** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{J : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} J] → CategoryT
heory.Functor J (Type u_2) → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor `F` to `Type*` is locally directed if for every `x ∈ F.obj
 k`, the
set of `F.obj` containing `x` is (co)directed.
That is, for each diagram
```
      x ∈ Fₖ
    ↗       ↖
xᵢ ∈ Fᵢ    xⱼ ∈ Fⱼ
```
there exists
```
xᵢ ∈ Fᵢ    xⱼ ∈ Fⱼ
    ↖       ↗
      xₗ ∈ Fₗ
```
that commutes with it.
-/
class Functor.IsLocallyDirected (F : J ⥤ Type*) : Prop where
  cond (F) : ∀ {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j),
    F.map fi xi = F.map fj xj → ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : _),
      F.map fli x = xi ∧ F.map flj x = xj

alias Functor.exists_map_eq_of_isLocallyDirected := Functor.IsLocallyDirected.cond
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Discrete J ⥤ Type*) : F.IsLocallyDirected := by
  constructor
  rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩
  simpa using fun x ↦ ⟨i, 𝟙 _, 𝟙 _, x, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : WidePushoutShape J ⥤ Type*) [∀ i, Mono (F.map (.init i))] :
    F.IsLocallyDirected := by
  constructor
  rintro i j k (_ | i) (_ | j)
  · simpa using fun x ↦ ⟨_, 𝟙 _, 𝟙 _, x, by simp⟩
  · simp only [WidePushoutShape.hom_id, Functor.map_id, id_apply, forall_comm, forall_eq]
    exact fun x ↦ ⟨_, .init _, 𝟙 _, x, by simp⟩
  · simp only [WidePushoutShape.hom_id, Functor.map_id, id_apply, forall_eq']
    exact fun x ↦ ⟨_, 𝟙 _, .init _, x, by simp⟩
  · simp only [((CategoryTheory.mono_iff_injective (F.map (.init i))).mp inferInstance).eq_iff,
      forall_eq']
    exact fun x ↦ ⟨_, 𝟙 _, 𝟙 _, x, by simp⟩

end CategoryTheory

