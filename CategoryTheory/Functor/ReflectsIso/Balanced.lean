/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Balanced categories and functors reflecting isomorphisms

If a category is `C`, and a functor out of `C` reflects epimorphisms and monomorphisms,
then the functor reflects isomorphisms.
Furthermore, categories that admit a functor that `ReflectsIsomorphisms`, `PreservesEpimorphisms`
and `PreservesMonomorphisms` are balanced.

-/

public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category* C]
  {D : Type*} [Category* D]

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
    [Balanced C] (F : C ⥤ D) [ReflectsMonomorphisms F] [ReflectsEpimorphisms F] :
    F.ReflectsIsomorphisms where
  reflects f hf := by
    have : Epi f := epi_of_epi_map F inferInstance
    have : Mono f := mono_of_mono_map F inferInstance
    exact isIso_of_mono_of_epi f
/-
**CategoryTheory.Functor.balanced_of_preserves** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) [F.ReflectsIsomorphisms]   [F.PreservesEpimorphisms] [F.PreservesMonomorp
hisms] [CategoryTheory.Balanced D], CategoryTheory.Balanced C
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
-/
lemma Functor.balanced_of_preserves (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms] [Balanced D] :
    Balanced C where
  isIso_of_mono_of_epi f _ _ := by
    rw [← isIso_iff_of_reflects_iso (F := F)]
    exact isIso_of_mono_of_epi _

end CategoryTheory

