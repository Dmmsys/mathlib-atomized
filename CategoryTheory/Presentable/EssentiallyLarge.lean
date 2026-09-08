/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation

/-!
# Accessible categories are essentially large

If a category `C` satisfies `HasCardinalFilteredGenerator C κ` for `κ : Cardinal.{w}`
(e.g. it is locally `κ`-presentable or `κ`-accessible),
then `C` is equivalent to a `w`-large category, i.e. a category whose type
of objects is in `Type (w + 1)` and whose types of morphisms are in `Type w`.

-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

namespace ObjectProperty.IsCardinalFilteredGenerator

variable [LocallySmall.{w} C] {P : ObjectProperty C} [ObjectProperty.EssentiallySmall.{w} P]
    (hP : P.IsCardinalFilteredGenerator κ)

include hP in
/-
**CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.essentiallyLarge_top
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCardinalFilteredGene
rator`。
形式化陈述：essentiallyLarge_top : ObjectProperty.EssentiallySmall.{w + 1} (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instEssentiallySmallFullSubcategoryOfLocal
lySmallOfEssentiallySmall_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, 
u} C] (P : CategoryTheory.ObjectProperty C)   [CategoryTheory.LocallySmall.{w, v
, u} C] […
· 使用定理 `CategoryTheory.ObjectProperty.instSmallOfObjOfSmall`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (X : ι → C) [Small.{w, u_1}
 ι],   CategoryTheory.ObjectProperty.Smal…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallFunctorOfLocallySmall`：∀ (C : Type u) [inst : Ca
tegoryTheory.Category.{v, u} C] [Small.{w, u} C] [CategoryTheory.LocallySmall.{w
, v, u} C]   {D : Type u'} [inst_3 …
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.exists_colimit
sOfShape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : Category
Theory.ObjectProperty C} {κ : Cardinal.{w}}   [inst_1 : Fact κ.IsRegul…
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
-/
lemma essentiallyLarge_top :
    ObjectProperty.EssentiallySmall.{w + 1} (C := C) ⊤ := by
  let e := equivSmallModel.{w} P.FullSubcategory
  let ι := Σ (J : Type w) (_ : SmallCategory J),
    { F : J ⥤ _ // HasColimit (F ⋙ e.inverse ⋙ P.ι) }
  let φ : ι → C := fun ⟨j, _, F, hF⟩ ↦ colimit (F ⋙ e.inverse ⋙ P.ι)
  refine ⟨ObjectProperty.ofObj φ, inferInstance, fun X _ ↦ ?_⟩
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  let G : J ⥤ P.FullSubcategory := P.lift p.diag p.prop_diag_obj
  let iso : (G ⋙ e.functor) ⋙ e.inverse ⋙ P.ι ≅ p.diag :=
    Functor.associator _ _ _ ≪≫
    G.isoWhiskerLeft ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.unitIso.symm P.ι) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor _) _
  have : HasColimit p.diag := ⟨_, p.isColimit⟩
  have := hasColimit_of_iso iso
  let i : ι := ⟨J, inferInstance, G ⋙ e.functor, inferInstance⟩
  exact ⟨_, ⟨i⟩, ⟨((IsColimit.precomposeHomEquiv iso _).2
    (p.isColimit)).coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

end ObjectProperty.IsCardinalFilteredGenerator

variable (C κ) in
/-
**CategoryTheory.HasCardinalFilteredGenerator.exists_equivalence** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.HasCardinalFilteredGenerator`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}
) [inst_1 : Fact κ.IsRegular]   [CategoryTheory.HasCardinalFilteredGenerator C κ
], ∃ J x, Nonempty (C ≌ J)
参数：C : Type u；κ : Cardinal.{w}；C ≌ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.exists_equivalence_iff_of_locallySmall`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.LocallySmall.{w', 
v_1, u_1} C],   (∃ J x, Nonempty (C ≌ J)) ↔…
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.toLocallySmall`：∀ {C : Type 
u} {hC : CategoryTheory.Category.{v, u} C} (κ : Cardinal.{w}) {hκ : Fact κ.IsReg
ular}   [self : CategoryTheory.HasCardinalFilter…
· 使用定理 `CategoryTheory.HasCardinalFilteredGenerator.exists_generator`：∀ (C : Typ
e u) [hC : CategoryTheory.Category.{v, u} C] (κ : Cardinal.{w}) [hκ : Fact κ.IsR
egular]   [self : CategoryTheory.HasCardinalFilter…
· 使用引理 `CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator.essentiallyLar
ge_top`：essentiallyLarge_top : ObjectProperty.EssentiallySmall.{w + 1} (C
-/
lemma HasCardinalFilteredGenerator.exists_equivalence
    [HasCardinalFilteredGenerator C κ] :
    ∃ (J : Type (w + 1)) (_ : Category.{w} J), Nonempty (C ≌ J) := by
  rw [exists_equivalence_iff_of_locallySmall]
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  exact hP.essentiallyLarge_top

end CategoryTheory

