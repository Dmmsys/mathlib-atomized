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
Definition of `Functor.IsLocallyDirected` / `Functor.IsLocallyDirected` 的定义

English:
class Functor.IsLocallyDirected
  parameters: (F : J ⥤ Type*)
  axioms and operations (1):
    - cond((F)) : forall {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j), F.map fi xi = F.map fj xj -> exists (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : _), F.map fli x = xi ∧ F.map flj x = xj

中文:
类 函子.是LocallyDirected
  参数: (F : J ⥤ 类型)
  公理与运算 (1 个):
    - cond((F)) : 对任意 {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j), F.map fi xi = F.map fj xj -> 存在 (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : _), F.map fli x = xi ∧ F.map flj x = xj

Depends on / 依赖: Functor, Functor.IsLocallyDirected.cond, IsLocallyDirected
-/
class Functor.IsLocallyDirected (F : J ⥤ Type*) : Prop where
  cond (F) : forall {i j k} (fi : i ⟶ k) (fj : j ⟶ k) (xi : F.obj i) (xj : F.obj j),
    F.map fi xi = F.map fj xj -> exists (l : J) (fli : l ⟶ i) (flj : l ⟶ j) (x : _),
      F.map fli x = xi ∧ F.map flj x = xj

alias Functor.exists_map_eq_of_isLocallyDirected := Functor.IsLocallyDirected.cond

instance (F : Discrete J ⥤ Type*) : F.IsLocallyDirected := by
  constructor
  rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩
  simpa using fun x => ⟨i, 𝟙 _, 𝟙 _, x, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
instance (F : WidePushoutShape J ⥤ Type*) [forall i, Mono (F.map (.init i))] :
    F.IsLocallyDirected := by
  constructor
  rintro i j k (_ | i) (_ | j)
  · simpa using fun x => ⟨_, 𝟙 _, 𝟙 _, x, by simp⟩
  · simp only [WidePushoutShape.hom_id, Functor.map_id, id_apply, forall_comm, forall_eq]
    exact fun x => ⟨_, .init _, 𝟙 _, x, by simp⟩
  · simp only [WidePushoutShape.hom_id, Functor.map_id, id_apply, forall_eq']
    exact fun x => ⟨_, 𝟙 _, .init _, x, by simp⟩
  · simp only [((CategoryTheory.mono_iff_injective (F.map (.init i))).mp inferInstance).eq_iff,
      forall_eq']
    exact fun x => ⟨_, 𝟙 _, 𝟙 _, x, by simp⟩

end CategoryTheory
