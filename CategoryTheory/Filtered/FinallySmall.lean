/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Finally small filtered categories

In this file, we show that if `C` is a filtered finally small category
that is locally small, there exists a final functor `D ⥤ C` from
a small filtered category. The dual result is also obtained.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace FinallySmall

attribute [local instance] IsFiltered.nonempty

open IsFiltered

variable [IsFiltered C] [LocallySmall.{w} C] [FinallySmall.{w} C]

/-
**CategoryTheory.FinallySmall.exists_of_isFiltered** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.FinallySmall`。
形式化陈述：exists_of_isFiltered : exists (D : Type w) (_ : SmallCategory D) (_ : IsFi
ltered D) (F : D ⥤ C), F.Final
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.instNonemptyStructuredArrow`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.ObjectProperty.strictMap_obj`：strictMap_obj (P : ObjectPr
operty C) (F : C ⥤ D) {X : C} (hX : P X) : P.strictMap F (F.obj X)
· 使用定理 `trivial`：True
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.IsFiltered.coeq_condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.IsFilteredOrEmpty C] {
j j' : C}   (f f' : j ⟶ j') {Z : C} …
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.final_of_comp_full_faithful'`：final_of_comp_full_
faithful' [Full G] [Faithful G] [Final (F ⋙ G)] : Final G
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.IsFiltered.of_equivalence`：of_equivalence (h : C ≌ D) : I
sFiltered D
· 使用定理 `CategoryTheory.Functor.final_of_isRightAdjoint`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.finallySmall_of_final_of_finallySmall`：finallySmall_of_fi
nal_of_finallySmall [FinallySmall.{w} K] (F : K ⥤ J) [Final F] : FinallySmall.{w
} J
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
lemma exists_of_isFiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Final := by
  /- First, under the assumption `Category.{w}` (instead of `LocallySmall.{w}`),
  we get most of the conclusion but instead of `D : Type w`,
  we only get a `w`-small `D : Type u`. -/
  have (C₀ : Type u) [Category.{w} C₀] [IsFiltered C₀] [FinallySmall.{w} C₀] :
      ∃ (D : Type u) (_ : Small.{w} D) (_ : Category.{w} D) (_ : IsFiltered D) (F : D ⥤ C₀),
        F.Final := by
    /- For `D`, we can choose the full subcategory of `C₀` which is the strict image
    of the final functor `fromFinalModel.{w} C₀ : FinalModel.{w} C₀ ⥤ C₀`,
    where `FinalModel.{w} C₀` is a `w`-small category. -/
    let P : ObjectProperty C₀ := ObjectProperty.strictMap ⊤ (fromFinalModel.{w} C₀)
    have hP (X : C₀) : ∃ (Y : C₀) (hY : P Y), Nonempty (X ⟶ Y) := by
      let f : StructuredArrow X (fromFinalModel.{w} C₀) := Classical.arbitrary _
      exact ⟨_, ObjectProperty.strictMap_obj _ _ (X := f.right) (by tauto), ⟨f.hom⟩⟩
    have : IsFiltered P.FullSubcategory :=
      { nonempty := by
          obtain ⟨X, hX, _⟩ := hP (Classical.arbitrary C₀)
          exact ⟨X, hX⟩
        cocone_objs := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩
          obtain ⟨Z, hZ, ⟨f⟩⟩ := hP (max X Y)
          exact ⟨⟨Z, hZ⟩, ObjectProperty.homMk (leftToMax X Y ≫ f),
            ObjectProperty.homMk (rightToMax X Y ≫ f), by tauto⟩
        cocone_maps := by
          rintro ⟨X, hX⟩ ⟨Y, hY⟩ ⟨f₁ : X ⟶ Y⟩ ⟨f₂ : X ⟶ Y⟩
          obtain ⟨Z, hZ, ⟨g⟩⟩ := hP (coeq f₁ f₂)
          exact ⟨⟨Z, hZ⟩, ObjectProperty.homMk (coeqHom f₁ f₂ ≫ g),
            ObjectProperty.hom_ext _ (coeq_condition_assoc _ _ _) ⟩ }
    let G : FinalModel.{w} C₀ ⥤ P.FullSubcategory :=
      { obj X := ⟨(fromFinalModel.{w} C₀).obj X, by tauto⟩
        map f := ObjectProperty.homMk ((fromFinalModel.{w} C₀).map f) }
    have : (G ⋙ P.ι).Final := inferInstanceAs (fromFinalModel.{w} C₀).Final
    exact ⟨P.FullSubcategory, small_of_surjective (f := G.obj)
      (by rintro ⟨_, Y, _, rfl⟩; exact ⟨Y, rfl⟩), inferInstance, inferInstance, P.ι,
      Functor.final_of_comp_full_faithful' G P.ι ⟩
  /- We get the conclusion under the assumption `Category.{w}`
  (instead of `LocallySmall.{w}`). -/
  have (C₀ : Type u) [Category.{w} C₀] (_ : IsFiltered C₀) (_ : FinallySmall.{w} C₀) :
      ∃ (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C₀), F.Final := by
    obtain ⟨D, _, _, _, F, _⟩ := this C₀
    let e := equivSmallModel.{w} D
    exact ⟨_, _, of_equivalence e, e.inverse ⋙ F, inferInstance⟩
  /- To get the conclusion for the given category `C`, it suffices to apply
  the previous result to the category `ShrinkHoms C`. -/
  let e := ShrinkHoms.equivalence.{w} C
  obtain ⟨D, _, _, F, _⟩ := this (ShrinkHoms C)
    (of_equivalence e) (finallySmall_of_final_of_finallySmall e.functor)
  exact ⟨D, inferInstance, inferInstance, F ⋙ e.inverse, inferInstance⟩

/-- If `C` is a locally small filtered finally small category,
this is a small filtered category, equipped with a final functor to `C`
(see `fromFilteredFinalModel`). -/
/-
**CategoryTheory.FinallySmall.FilteredFinalModel** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.FinallySmall`。
形式化陈述：FilteredFinalModel : Type w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FinallySmall.exists_of_isFiltered`：exists_of_isFiltered :
 exists (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Fin
al

--- 原说明 ---
If `C` is a locally small filtered finally small category,
this is a small filtered category, equipped with a final functor to `C`
(see `fromFilteredFinalModel`).
-/
def FilteredFinalModel : Type w := (exists_of_isFiltered.{w} C).choose
/-
**CategoryTheory.FinallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Finally
Small`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Category (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose
/-
**CategoryTheory.FinallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Finally
Small`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiltered (FilteredFinalModel.{w} C) :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small filtered finally small category,
this is a final functor from a small filtered category. -/
/-
**CategoryTheory.FinallySmall.fromFilteredFinalModel** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.FinallySmall`。
形式化陈述：fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FinallySmall.exists_of_isFiltered`：exists_of_isFiltered :
 exists (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Fin
al

--- 原说明 ---
If `C` is a locally small filtered finally small category,
this is a final functor from a small filtered category.
-/
noncomputable def fromFilteredFinalModel : FilteredFinalModel.{w} C ⥤ C :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose
/-
**CategoryTheory.FinallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Finally
Small`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromFilteredFinalModel.{w} C).Final :=
  (exists_of_isFiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

open Limits in
/-
**CategoryTheory.FinallySmall.preservesColimitsOfShape_of_isFiltered** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.FinallySmall`。
形式化陈述：preservesColimitsOfShape_of_isFiltered {D E : Type*} [Category* D] [Catego
ry* E] (F : D ⥤ E) [PreservesFilteredColimitsOfSize.{w, w} F] : PreservesColimit
sOfShape C F
参数：F : D ⥤ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Final.preservesColimitsOfShape_of_final`：preserve
sColimitsOfShape_of_final {B : Type u₄} [Category.{v₄} B] (H : E ⥤ B) [Preserves
ColimitsOfShape C H] : PreservesColimitsOfShape D H …
· 使用定理 `CategoryTheory.FinallySmall.instFinalFilteredFinalModelFromFilteredFinal
Model`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Catego
ryTheory.IsFiltered C]   [inst_2 : CategoryTheory.LocallySmall.{w, …
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.FinallySmall.instIsFilteredFilteredFinalModel`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.IsFilter
ed C]   [inst_2 : CategoryTheory.LocallySmall.{w, …
-/
lemma preservesColimitsOfShape_of_isFiltered
    {D E : Type*} [Category* D] [Category* E]
    (F : D ⥤ E) [PreservesFilteredColimitsOfSize.{w, w} F] :
    PreservesColimitsOfShape C F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (FinallySmall.fromFilteredFinalModel.{w} C) _

end FinallySmall

namespace InitiallySmall

variable [IsCofiltered C] [LocallySmall.{w} C] [InitiallySmall.{w} C]

/-
**CategoryTheory.InitiallySmall.exists_of_isCofiltered** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.InitiallySmall`。
形式化陈述：exists_of_isCofiltered : exists (D : Type w) (_ : SmallCategory D) (_ : Is
Cofiltered D) (F : D ⥤ C), F.Initial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.FinallySmall.exists_of_isFiltered`：exists_of_isFiltered :
 exists (D : Type w) (_ : SmallCategory D) (_ : IsFiltered D) (F : D ⥤ C), F.Fin
al
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.instFinallySmallOppositeOfInitiallySmall`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J],   C
ategoryTheory.FinallySmall Jᵒᵖ
· 使用定理 `CategoryTheory.Functor.instInitialOppositeLeftOpOfFinal`：∀ {C : Type u_1
} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
lemma exists_of_isCofiltered :
    ∃ (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C), F.Initial := by
  obtain ⟨D, _, _, F, _⟩ := FinallySmall.exists_of_isFiltered.{w} Cᵒᵖ
  exact ⟨Dᵒᵖ, inferInstance, inferInstance, F.leftOp, inferInstance⟩

/-- If `C` is a locally small cofiltered initially small category,
this is a small cofiltered category, equipped with an initial functor to `C`
(see `fromCofilteredInitialModel`). -/
/-
**CategoryTheory.InitiallySmall.CofilteredInitialModel** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.InitiallySmall`。
形式化陈述：CofilteredInitialModel : Type w
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InitiallySmall.exists_of_isCofiltered`：exists_of_isCofilt
ered : exists (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C
), F.Initial

--- 原说明 ---
If `C` is a locally small cofiltered initially small category,
this is a small cofiltered category, equipped with an initial functor to `C`
(see `fromCofilteredInitialModel`).
-/
def CofilteredInitialModel : Type w := (exists_of_isCofiltered.{w} C).choose
/-
**CategoryTheory.InitiallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Initi
allySmall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Category (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose
/-
**CategoryTheory.InitiallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Initi
allySmall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCofiltered (CofilteredInitialModel.{w} C) :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose

/-- If `C` is a locally small cofiltered initially small category,
this is an initial functor from a small cofiltered category. -/
/-
**CategoryTheory.InitiallySmall.fromCofilteredInitialModel** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.InitiallySmall`。
形式化陈述：fromCofilteredInitialModel : CofilteredInitialModel.{w} C ⥤ C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InitiallySmall.exists_of_isCofiltered`：exists_of_isCofilt
ered : exists (D : Type w) (_ : SmallCategory D) (_ : IsCofiltered D) (F : D ⥤ C
), F.Initial

--- 原说明 ---
If `C` is a locally small cofiltered initially small category,
this is an initial functor from a small cofiltered category.
-/
noncomputable def fromCofilteredInitialModel : CofilteredInitialModel.{w} C ⥤ C :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose
/-
**CategoryTheory.InitiallySmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Initi
allySmall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromCofilteredInitialModel.{w} C).Initial :=
  (exists_of_isCofiltered.{w} C).choose_spec.choose_spec.choose_spec.choose_spec

end InitiallySmall

end CategoryTheory

