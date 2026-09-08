/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Localization

/-!
# The category of sheaves of modules as a localization of presheaves of modules

Similarly as the category of sheaves with values in a category identify to
a localization of the category of presheaves with respect to those morphisms
which become isomorphisms after sheafification
(see the file `Mathlib/CategoryTheory/Sites/Localization.lean`), we show that
the sheafification functor from presheaves of modules to sheaves of modules
is a localization functor.

-/

public section

universe v u v' u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace PresheafOfModules

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]

open MorphismProperty in
/-
**PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms** 是 M
athlib 中的一个引理，位于命名空间 `PresheafOfModules`。
形式化陈述：inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms : J.W.inverseImage 
(toPresheaf R₀) = (isomorphisms _).inverseImage (sheafification α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_eq_inverseImage_isomorphisms`：W_eq
_inverseImage_isomorphisms : J.W = (MorphismProperty.isomorphisms _).inverseImag
e (presheafToSheaf J A)
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpC
atToSheaf_1`：∀ {C : Type u'} [inst : CategoryTheory.Category.{v', u'} C] {J : Ca
tegoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
lemma inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms :
    J.W.inverseImage (toPresheaf R₀) = (isomorphisms _).inverseImage (sheafification α) := by
  rw [J.W_eq_inverseImage_isomorphisms]
  ext P Q f
  simp only [inverseImage_iff, isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (sheafificationCompToSheaf.{v} α)).app (Arrow.mk f))
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (sheafification.{v} α).IsLocalization (J.W.inverseImage (toPresheaf R₀)) := by
  rw [inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α]
  exact (sheafificationAdjunction.{v} α).isLocalization

end PresheafOfModules

