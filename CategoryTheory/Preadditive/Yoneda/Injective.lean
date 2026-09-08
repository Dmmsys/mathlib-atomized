/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
An object is injective iff the preadditive yoneda functor on it preserves epimorphisms.
-/

public section


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Injective

/-
**CategoryTheory.Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda
_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Injective`。
形式化陈述：injective_iff_preservesEpimorphisms_preadditiveYoneda_obj (J : C) : Inject
ive J ↔ (preadditiveYoneda.obj J).PreservesEpimorphisms
参数：J : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.injective_iff_preservesEpimorphisms_yoneda_obj`
：injective_iff_preservesEpimorphisms_yoneda_obj (J : C) : Injective J ↔ (yoneda.
obj J).PreservesEpimorphisms
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects`：p
reservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E) [Preserves
Epimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesE…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `AddCommGrpCat.forget_commGrp_preserves_epi`：(CategoryTheory.forget AddCo
mmGrpCat).PreservesEpimorphisms
-/
theorem injective_iff_preservesEpimorphisms_preadditiveYoneda_obj (J : C) :
    Injective J ↔ (preadditiveYoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine
    ⟨fun h : (preadditiveYoneda.obj J ⋙ (forget AddCommGrpCat)).PreservesEpimorphisms => ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYoneda.obj J) (forget _)
  · intro
    exact (inferInstance : (preadditiveYoneda.obj J ⋙ forget _).PreservesEpimorphisms)
/-
**CategoryTheory.Injective.injective_iff_preservesEpimorphisms_preadditive_yoned
a_obj'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Injective`。
形式化陈述：injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C) : Inje
ctive J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms
参数：J : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Injective.injective_iff_preservesEpimorphisms_yoneda_obj`
：injective_iff_preservesEpimorphisms_yoneda_obj (J : C) : Injective J ↔ (yoneda.
obj J).PreservesEpimorphisms
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_of_preserves_of_reflects`：p
reservesEpimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E) [Preserves
Epimorphisms (F ⋙ G)] [ReflectsEpimorphisms G] : PreservesE…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {E : Type u₃} [ins…
-/
theorem injective_iff_preservesEpimorphisms_preadditive_yoneda_obj' (J : C) :
    Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms := by
  rw [injective_iff_preservesEpimorphisms_yoneda_obj]
  refine ⟨fun h : (preadditiveYonedaObj J ⋙ (forget <| ModuleCat (End J))).PreservesEpimorphisms =>
    ?_, ?_⟩
  · exact
      Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveYonedaObj J) (forget _)
  · intro
    exact (inferInstance : (preadditiveYonedaObj J ⋙ forget _).PreservesEpimorphisms)

end Injective

end Preadditive

end CategoryTheory

