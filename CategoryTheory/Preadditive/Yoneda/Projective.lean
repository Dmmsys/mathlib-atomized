/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
An object is projective iff the preadditive coyoneda functor on it preserves epimorphisms.
-/

public section


universe v u

open Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

namespace Projective

/-
**CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyo
neda_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Projective`。
形式化陈述：projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj (P : C) : Pro
jective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_
obj`：projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) : Projective P ↔ 
(coyoneda.obj (op P)).PreservesEpimorphisms
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
theorem projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj (P : C) :
    Projective P ↔ (preadditiveCoyoneda.obj (op P)).PreservesEpimorphisms := by
  rw [projective_iff_preservesEpimorphisms_coyoneda_obj]
  refine ⟨fun h : (preadditiveCoyoneda.obj (op P) ⋙
      forget AddCommGrpCat).PreservesEpimorphisms => ?_, ?_⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyoneda.obj (op P))
        (forget _)
  · intro
    exact (inferInstance : (preadditiveCoyoneda.obj (op P) ⋙ forget _).PreservesEpimorphisms)
/-
**CategoryTheory.Projective.projective_iff_preservesEpimorphisms_preadditiveCoyo
nedaObj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Projective`。
形式化陈述：projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj (P : C) : Proj
ective P ↔ (preadditiveCoyonedaObj P).PreservesEpimorphisms
参数：P : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Projective.projective_iff_preservesEpimorphisms_coyoneda_
obj`：projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) : Projective P ↔ 
(coyoneda.obj (op P)).PreservesEpimorphisms
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
theorem projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj (P : C) :
    Projective P ↔ (preadditiveCoyonedaObj P).PreservesEpimorphisms := by
  rw [projective_iff_preservesEpimorphisms_coyoneda_obj]
  refine ⟨fun h : (preadditiveCoyonedaObj P ⋙ forget _).PreservesEpimorphisms => ?_, ?_⟩
  · exact Functor.preservesEpimorphisms_of_preserves_of_reflects (preadditiveCoyonedaObj P)
        (forget _)
  · intro
    exact (inferInstance : (preadditiveCoyonedaObj P ⋙ forget _).PreservesEpimorphisms)

end Projective

end Preadditive

end CategoryTheory

