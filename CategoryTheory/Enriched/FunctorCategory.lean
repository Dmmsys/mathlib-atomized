/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Functor categories are enriched

If `C` is a `V`-enriched ordinary category, then `J ⥤ C` is also
both a `V`-enriched ordinary category and a `J ⥤ V`-enriched
ordinary category, provided `C` has suitable limits.

We first define the `V`-enriched structure on `J ⥤ C` by saying
that if `F₁` and `F₂` are in `J ⥤ C`, then `enrichedHom V F₁ F₂ : V`
is a suitable limit involving `F₁.obj j ⟶[V] F₂.obj j` for all `j : C`.
The `J ⥤ V` object of morphisms `functorEnrichedHom V F₁ F₂ : J ⥤ V`
is defined by sending `j : J` to the previously defined `enrichedHom`
for the "restriction" of `F₁` and `F₂` to the category `Under j`.
The definition `isLimitConeFunctorEnrichedHom` shows that
`enriched V F₁ F₂` is the limit of the functor `functorEnrichedHom V F₁ F₂`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Enriched.FunctorCategory

open Category MonoidalCategory Limits CategoryTheory.Functor

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {C : Type u₂} [Category.{v₂} C] {J : Type u₃} [Category.{v₃} J]
  {K : Type u₄} [Category.{v₄} K] [EnrichedOrdinaryCategory V C]

variable (F₁ F₂ F₃ F₄ : J ⥤ C)

/-- Given two functors `F₁` and `F₂` from a category `J` to a `V`-enriched
ordinary category `C`, this is the diagram `Jᵒᵖ ⥤ J ⥤ V` whose end shall be
the `V`-morphisms in `J ⥤ V` from `F₁` to `F₂`. -/
@[simps!]
/-
**CategoryTheory.Enriched.FunctorCategory.diagram** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Enriched.FunctorCategory`。
形式化陈述：diagram : Jᵒᵖ ⥤ J ⥤ V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two functors `F₁` and `F₂` from a category `J` to a `V`-enriched
ordinary category `C`, this is the diagram `Jᵒᵖ ⥤ J ⥤ V` whose end shall be
the `V`-morphisms in `J ⥤ V` from `F₁` to `F₂`.
-/
def diagram : Jᵒᵖ ⥤ J ⥤ V := F₁.op ⋙ eHomFunctor V C ⋙ (whiskeringLeft J C V).obj F₂

/-- The condition that the end `diagram V F₁ F₂` exists, see `enrichedHom`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.HasEnrichedHom** 是 Mathlib 中的一个缩写定义，位于
命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：HasEnrichedHom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that the end `diagram V F₁ F₂` exists, see `enrichedHom`.
-/
abbrev HasEnrichedHom := HasEnd (diagram V F₁ F₂)

section

variable [HasEnrichedHom V F₁ F₂]

/-- The `V`-enriched hom from `F₁` to `F₂` when `F₁` and `F₂` are functors `J ⥤ C`
and `C` is a `V`-enriched category. -/
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedHom** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedHom : V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `V`-enriched hom from `F₁` to `F₂` when `F₁` and `F₂` are functors `J ⥤ C`
and `C` is a `V`-enriched category.
-/
noncomputable abbrev enrichedHom : V := end_ (diagram V F₁ F₂)

/-- The projection `enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j` in the category `V`
for any `j : J` when `F₁` and `F₂` are functors `J ⥤ C` and `C` is a `V`-enriched category. -/
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedHom** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedHom : V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j` in the category `V
`
for any `j : J` when `F₁` and `F₂` are functors `J ⥤ C` and `C` is a `V`-enriche
d category.
-/
noncomputable abbrev enrichedHomπ (j : J) : enrichedHom V F₁ F₂ ⟶ F₁.obj j ⟶[V] F₂.obj j :=
  end_.π _ j

@[reassoc]
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedHom_condition** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedHom_condition {i j : J} (f : i ⟶ j) : enrichedHomπ V F₁ F₂ i ≫ eHo
mWhiskerLeft V (F₁.obj i) (F₂.map f) = enrichedHomπ V F₁ F₂ j ≫ eHomWhiskerRight
 V (F₁.map f) (F₂.obj j)
参数：f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.condition`：∀ {J : Type u} [inst : CategoryThe
ory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
C]   (F : CategoryTheory.F…
-/
lemma enrichedHom_condition {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ eHomWhiskerLeft V (F₁.obj i) (F₂.map f) =
    enrichedHomπ V F₁ F₂ j ≫ eHomWhiskerRight V (F₁.map f) (F₂.obj j) :=
  end_.condition (diagram V F₁ F₂) f

@[reassoc]
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedHom_condition'** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedHom_condition' {i j : J} (f : i ⟶ j) : enrichedHomπ V F₁ F₂ i ≫ (ρ
_ _).inv ≫ _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _ = enrichedHomπ V F₁ F₂ j
 ≫ (fun_ _).inv ≫ (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _
参数：f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.condition`：∀ {J : Type u} [inst : CategoryThe
ory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} 
C]   (F : CategoryTheory.F…
-/
lemma enrichedHom_condition' {i j : J} (f : i ⟶ j) :
    enrichedHomπ V F₁ F₂ i ≫ (ρ_ _).inv ≫
      _ ◁ (eHomEquiv V) (F₂.map f) ≫ eComp V _ _ _ =
    enrichedHomπ V F₁ F₂ j ≫ (λ_ _).inv ≫
      (eHomEquiv V) (F₁.map f) ▷ _ ≫ eComp V _ _ _ :=
  end_.condition (diagram V F₁ F₂) f

variable {F₁ F₂}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary category,
this is the bijection `(F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂)`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Enriched.FunctorCategory`。
形式化陈述：homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where toFun τ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary ca
tegory,
this is the bijection `(F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂)`.
-/
noncomputable def homEquiv : (F₁ ⟶ F₂) ≃ (𝟙_ V ⟶ enrichedHom V F₁ F₂) where
  toFun τ := end_.lift (fun j ↦ eHomEquiv V (τ.app j)) (fun i j f ↦ by
    trans eHomEquiv V (τ.app i ≫ F₂.map f)
    · dsimp
      simp only [eHomEquiv_comp, tensorHom_def_assoc, MonoidalCategory.whiskerRight_id,
        ← unitors_equal, assoc, Iso.inv_hom_id_assoc, eHomWhiskerLeft]
    · dsimp
      simp only [← NatTrans.naturality, eHomEquiv_comp, tensorHom_def', id_whiskerLeft,
        assoc, Iso.inv_hom_id_assoc, eHomWhiskerRight])
  invFun g :=
    { app := fun j ↦ (eHomEquiv V).symm (g ≫ end_.π _ j)
      naturality := fun i j f ↦ (eHomEquiv V).injective (by
        simp only [eHomEquiv_comp, Equiv.apply_symm_apply, Iso.cancel_iso_inv_left]
        conv_rhs =>
          rw [tensorHom_def_assoc, MonoidalCategory.whiskerRight_id_assoc, assoc,
            enrichedHom_condition' V F₁ F₂ f]
        conv_lhs =>
          rw [tensorHom_def'_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
            id_whiskerLeft_assoc, id_whiskerLeft_assoc, Iso.inv_hom_id_assoc, unitors_equal]) }
  left_inv τ := by aesop
  right_inv g := by aesop

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.homEquiv_apply_** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Enriched.FunctorCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_apply_π (τ : F₁ ⟶ F₂) (j : J) :
    homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.app j) := by
  simp [homEquiv]

end

section

variable [HasEnrichedHom V F₁ F₁]

/-- The identity for the `V`-enrichment of the category `J ⥤ C`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedId** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity for the `V`-enrichment of the category `J ⥤ C`.
-/
noncomputable def enrichedId : 𝟙_ V ⟶ enrichedHom V F₁ F₁ := homEquiv _ (𝟙 F₁)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedId_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Enriched.FunctorCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedId_π (j : J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j) := by
  simp [enrichedId]

@[simp]
/-
**CategoryTheory.Enriched.FunctorCategory.homEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_id : homEquiv V (𝟙 F₁) = enrichedId V F₁ := rfl

end

section

variable [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₁ F₃]

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition for the `V`-enrichment of the category `J ⥤ C`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedComp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedComp : enrichedHom V F₁ F₂ otimes enrichedHom V F₂ F₃ ⟶ enrichedHo
m V F₁ F₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition for the `V`-enrichment of the category `J ⥤ C`.
-/
noncomputable def enrichedComp : enrichedHom V F₁ F₂ ⊗ enrichedHom V F₂ F₃ ⟶ enrichedHom V F₁ F₃ :=
  end_.lift (fun j ↦ (end_.π _ j ⊗ₘ end_.π _ j) ≫ eComp V _ _ _) (fun i j f ↦ by
    dsimp
    trans (end_.π (diagram V F₁ F₂) i ⊗ₘ end_.π (diagram V F₂ F₃) j) ≫
      (ρ_ _).inv ▷ _ ≫ (_ ◁ (eHomEquiv V (F₂.map f))) ▷ _ ≫ eComp V _ (F₂.obj i) _ ▷ _ ≫
        eComp V _ (F₂.obj j) _
    · have := end_.condition (diagram V F₂ F₃) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs => rw [assoc, tensorHom_def_assoc]
      conv_rhs =>
        rw [tensorHom_def_assoc, whisker_assoc_assoc, e_assoc,
          triangle_assoc_comp_right_inv_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
          assoc, assoc, ← this, MonoidalCategory.whiskerLeft_comp_assoc,
          MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc,
          ← e_assoc, whiskerLeft_rightUnitor_inv_assoc, associator_inv_naturality_right_assoc,
          Iso.hom_inv_id_assoc, whisker_exchange_assoc, MonoidalCategory.whiskerRight_id_assoc,
          Iso.inv_hom_id_assoc]
    · have := end_.condition (diagram V F₁ F₂) f
      dsimp [eHomWhiskerLeft, eHomWhiskerRight] at this ⊢
      conv_lhs =>
        rw [tensorHom_def'_assoc, ← comp_whiskerRight_assoc,
          ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
          assoc, assoc, this, comp_whiskerRight_assoc, comp_whiskerRight_assoc,
          comp_whiskerRight_assoc, leftUnitor_inv_whiskerRight_assoc,
          ← associator_inv_naturality_left_assoc, ← e_assoc',
          Iso.inv_hom_id_assoc, ← whisker_exchange_assoc, id_whiskerLeft_assoc,
          Iso.inv_hom_id_assoc]
      conv_rhs => rw [assoc, tensorHom_def'_assoc])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedComp_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Enriched.FunctorCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma enrichedComp_π (j : J) :
    enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j =
      (end_.π (diagram V F₁ F₂) j ⊗ₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ _ _ := by
  simp [enrichedComp]

variable {F₁ F₂ F₃}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Enriched.FunctorCategory.homEquiv_comp** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : (homEquiv V) (f ≫ g) = (fun_ (
𝟙_ V)).inv ≫ ((homEquiv V) f otimesₘ (homEquiv V) g) ≫ enrichedComp V F₁ F₂ F₃
参数：f : F₁ ⟶ F₂；g : F₂ ⟶ F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.homEquiv_apply_π`：homEquiv_apply
_π (τ : F₁ ⟶ F₂) (j : J) : homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.
app j)
· 使用引理 `CategoryTheory.eHomEquiv_comp`：eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g
 : Y ⟶ Z) : eHomEquiv V (f ≫ g) = (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEqui
v V g) ≫ eComp V X …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_comp (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (homEquiv V) (f ≫ g) = (λ_ (𝟙_ V)).inv ≫ ((homEquiv V) f ⊗ₘ (homEquiv V) g) ≫
    enrichedComp V F₁ F₂ F₃ := by
  ext j
  simp only [homEquiv_apply_π, NatTrans.comp_app, eHomEquiv_comp, assoc,
    enrichedComp_π, Functor.op_obj, tensorHom_comp_tensorHom_assoc]

end

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.enriched_id_comp** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enriched_id_comp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] : (fun_
 (enrichedHom V F₁ F₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F₂ ≫ enrichedCo
mp V F₁ F₁ F₂ = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedId_π`：enrichedId_π (j : 
J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j)
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.e_id_comp`：e_id_comp (X Y : C) : (fun_ (X ⟶[V] Y)).inv ≫ 
eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma enriched_id_comp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] :
    (λ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F₂ ≫
      enrichedComp V F₁ F₁ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def, assoc,
    ← comp_whiskerRight_assoc, enrichedId_π, ← whisker_exchange_assoc,
    id_whiskerLeft, assoc, assoc, Iso.inv_hom_id_assoc]
  dsimp
  rw [e_id_comp, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.enriched_comp_id** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enriched_comp_id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] : (ρ_ (
enrichedHom V F₁ F₂)).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ ≫ enrichedComp
 V F₁ F₂ F₂ = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedId_π`：enrichedId_π (j : 
J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j)
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.e_comp_id`：e_comp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ _ 
◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma enriched_comp_id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] :
    (ρ_ (enrichedHom V F₁ F₂)).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ ≫
      enrichedComp V F₁ F₂ F₂ = 𝟙 _ := by
  ext j
  rw [assoc, assoc, enrichedComp_π, id_comp, tensorHom_def', assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, enrichedId_π,
    whisker_exchange_assoc, MonoidalCategory.whiskerRight_id, assoc, assoc,
    Iso.inv_hom_id_assoc]
  dsimp
  rw [e_comp_id, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Enriched.FunctorCategory.enriched_assoc** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enriched_assoc [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnric
hedHom V F₁ F₄] [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] [HasEnrichedHo
m V F₃ F₄] : (α_ (enrichedHom V F₁ F₂) (enrichedHom V F₂ F₃) (enrichedHom V F₃ F
₄)).inv ≫ enrichedComp V F₁ F₂ F₃ ▷ enrichedHom V F₃ F₄ ≫ enrichedComp V F₁ F₃ F
₄ = enrichedHom V F₁ F₂ ◁ enrichedComp V F₂ F₃ F₄ ≫ enrichedComp V F₁ F₂ F₄
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def_assoc`：∀ {C : Type u} {𝒞 :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X
₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {X₁ Y₁ X₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g :…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Monoi
dalCategory C]   {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
-/
lemma enriched_assoc [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄]
    [HasEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] [HasEnrichedHom V F₃ F₄] :
    (α_ (enrichedHom V F₁ F₂) (enrichedHom V F₂ F₃) (enrichedHom V F₃ F₄)).inv ≫
      enrichedComp V F₁ F₂ F₃ ▷ enrichedHom V F₃ F₄ ≫ enrichedComp V F₁ F₃ F₄ =
      enrichedHom V F₁ F₂ ◁ enrichedComp V F₂ F₃ F₄ ≫ enrichedComp V F₁ F₂ F₄ := by
  ext j
  conv_lhs =>
    rw [assoc, assoc, enrichedComp_π,
      tensorHom_def_assoc, ← comp_whiskerRight_assoc, enrichedComp_π,
      comp_whiskerRight_assoc, ← whisker_exchange_assoc,
      ← whisker_exchange_assoc, ← tensorHom_def'_assoc, ← associator_inv_naturality_assoc]
  conv_rhs =>
    rw [assoc, enrichedComp_π, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      enrichedComp_π, MonoidalCategory.whiskerLeft_comp_assoc, whisker_exchange_assoc,
      whisker_exchange_assoc, ← tensorHom_def_assoc]
  dsimp
  rw [e_assoc]

variable (J C)

/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `V`-enriched ordinary category. -/
@[instance_reducible]
/-
**CategoryTheory.Enriched.FunctorCategory.enrichedOrdinaryCategory** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：enrichedOrdinaryCategory [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] 
: EnrichedOrdinaryCategory V (J ⥤ C) where Hom F₁ F₂
参数：F₁ F₂ : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `V`-enriched ordinary category.
-/
noncomputable def enrichedOrdinaryCategory [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory V (J ⥤ C) where
  Hom F₁ F₂ := enrichedHom V F₁ F₂
  id F := enrichedId V F
  comp F₁ F₂ F₃ := enrichedComp V F₁ F₂ F₃
  assoc _ _ _ _ := enriched_assoc _ _ _ _ _
  homEquiv := homEquiv V
  homEquiv_id _ := homEquiv_id V _
  homEquiv_comp f g := homEquiv_comp V f g

variable {J C}

section

variable (G : K ⥤ J) [HasEnrichedHom V F₁ F₂]

variable {F₁ F₂} in
/-- If `F₁` and `F₂` are functors `J ⥤ C`, `G : K ⥤ J`, and
`F₁'` and `F₂'` are functors `K ⥤ C` that are respectively
isomorphic to `G ⋙ F₁` and `G ⋙ F₂`, then this is the
induced morphism `enrichedHom V F₁ F₂ ⟶ enrichedHom V F₁' F₂'` in `V`
when `C` is a category enriched in `V`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.precompEnrichedHom'** 是 Mathlib 中的一个缩写
定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：precompEnrichedHom' {F₁' F₂' : K ⥤ C} [HasEnrichedHom V F₁' F₂'] (e₁ : G ⋙
 F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂') : enrichedHom V F₁ F₂ ⟶ enrichedHom V F₁' F₂'
参数：e₁ : G ⋙ F₁ ≅ F₁'；e₂ : G ⋙ F₂ ≅ F₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F₁` and `F₂` are functors `J ⥤ C`, `G : K ⥤ J`, and
`F₁'` and `F₂'` are functors `K ⥤ C` that are respectively
isomorphic to `G ⋙ F₁` and `G ⋙ F₂`, then this is the
induced morphism `enrichedHom V F₁ F₂ ⟶ enrichedHom V F₁' F₂'` in `V`
when `C` is a category enriched in `V`.
-/
noncomputable abbrev precompEnrichedHom' {F₁' F₂' : K ⥤ C}
    [HasEnrichedHom V F₁' F₂'] (e₁ : G ⋙ F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂') :
    enrichedHom V F₁ F₂ ⟶ enrichedHom V F₁' F₂' :=
  end_.lift (fun x ↦ enrichedHomπ V F₁ F₂ (G.obj x) ≫
    (eHomWhiskerRight _ (e₁.inv.app x) _ ≫ eHomWhiskerLeft _ _ (e₂.hom.app x)))
    (fun i j f ↦ by
      dsimp
      rw [assoc, assoc, assoc, assoc, ← eHomWhiskerLeft_comp,
        ← eHom_whisker_exchange, ← e₂.hom.naturality f,
        eHomWhiskerLeft_comp_assoc]
      dsimp
      rw [enrichedHom_condition_assoc, eHom_whisker_exchange,
        eHom_whisker_exchange, ← eHomWhiskerRight_comp_assoc,
        ← eHomWhiskerRight_comp_assoc, NatTrans.naturality]
      dsimp)

/-- If `F₁` and `F₂` are functors `J ⥤ C`, and `G : K ⥤ J`,
then this is the induced morphism
`enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂)` in `V`
when `C` is a category enriched in `V`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.precompEnrichedHom** 是 Mathlib 中的一个缩写定
义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：precompEnrichedHom [HasEnrichedHom V (G ⋙ F₁) (G ⋙ F₂)] : enrichedHom V F₁
 F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂)
参数：G ⋙ F₁；G ⋙ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F₁` and `F₂` are functors `J ⥤ C`, and `G : K ⥤ J`,
then this is the induced morphism
`enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂)` in `V`
when `C` is a category enriched in `V`.
-/
noncomputable abbrev precompEnrichedHom
    [HasEnrichedHom V (G ⋙ F₁) (G ⋙ F₂)] :
    enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂) :=
  precompEnrichedHom' V G (Iso.refl _) (Iso.refl _)

end


section

/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a category enriched in `V`,
this condition allows the definition of `functorEnrichedHom V F₁ F₂ : J ⥤ V`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.HasFunctorEnrichedHom** 是 Mathlib 中的一个
缩写定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：HasFunctorEnrichedHom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a category enriched in `V`
,
this condition allows the definition of `functorEnrichedHom V F₁ F₂ : J ⥤ V`.
-/
abbrev HasFunctorEnrichedHom :=
  ∀ (j : J), HasEnrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)

variable [HasFunctorEnrichedHom V F₁ F₂]
/-
**CategoryTheory.Enriched.FunctorCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Enriched.FunctorCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {j j' : J} (f : j ⟶ j') :
    HasEnrichedHom V (Under.map f ⋙ Under.forget j ⋙ F₁)
      (Under.map f ⋙ Under.forget j ⋙ F₂) :=
  inferInstanceAs (HasEnrichedHom V (Under.forget j' ⋙ F₁) (Under.forget j' ⋙ F₂))

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a category enriched in `V`,
this is the enriched hom functor from `F₁` to `F₂` in `J ⥤ V`. -/
@[simps!]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnrichedHom** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnrichedHom : J ⥤ V where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a category enriched in `V`
,
this is the enriched hom functor from `F₁` to `F₂` in `J ⥤ V`.
-/
noncomputable def functorEnrichedHom : J ⥤ V where
  obj j := enrichedHom V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
  map f := precompEnrichedHom' V (Under.map f) (Iso.refl _) (Iso.refl _)
  map_id X := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
      eHomWhiskerLeft_id, comp_id, id_comp]
    congr 1
    simp [Under.map, Comma.mapLeft]
    rfl
  map_comp f g := by
    ext j
    -- this was produced by `simp?`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, end_.lift_π,
      Under.map_obj_right, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
      eHomWhiskerLeft_id, comp_id, assoc]
    congr 1
    simp [Under.map, Comma.mapLeft]

variable [HasEnrichedHom V F₁ F₂]

set_option backward.isDefEq.respectTransparency false in
/-- The (limit) cone expressing that the limit of `functorEnrichedHom V F₁ F₂`
is `enrichedHom V F₁ F₂`. -/
@[simps]
/-
**CategoryTheory.Enriched.FunctorCategory.coneFunctorEnrichedHom** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：coneFunctorEnrichedHom : Cone (functorEnrichedHom V F₁ F₂) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (limit) cone expressing that the limit of `functorEnrichedHom V F₁ F₂`
is `enrichedHom V F₁ F₂`.
-/
noncomputable def coneFunctorEnrichedHom : Cone (functorEnrichedHom V F₁ F₂) where
  pt := enrichedHom V F₁ F₂
  π := { app := fun j ↦ precompEnrichedHom V F₁ F₂ (Under.forget j) }

namespace isLimitConeFunctorEnrichedHom

variable {V F₁ F₂} (s : Cone (functorEnrichedHom V F₁ F₂))

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom.lift** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory.isLimitConeFunct
orEnrichedHom`。
形式化陈述：lift : s.pt ⟶ enrichedHom V F₁ F₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom
`.
-/
noncomputable def lift : s.pt ⟶ enrichedHom V F₁ F₂ :=
  end_.lift (fun j ↦ s.π.app j ≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))) (fun j j' f ↦ by
    dsimp
    rw [← s.w f, assoc, assoc, assoc]
    -- this was produced by `simp?`
    simp only [functorEnrichedHom_obj, functorEnrichedHom_map, end_.lift_π_assoc, diagram_obj_obj,
      Functor.comp_obj, Under.forget_obj, Under.mk_right, Under.map_obj_right, Iso.refl_inv,
      NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom, eHomWhiskerLeft_id, comp_id]
    have := enrichedHom_condition V (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₂)
      (Under.homMk f : Under.mk (𝟙 j) ⟶ Under.mk f)
    dsimp at this
    rw [this]
    congr 3
    simp [Under.map, Comma.mapLeft]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom.fac** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory.isLimitConeFuncto
rEnrichedHom`。
形式化陈述：fac (j : J) : lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app 
j
参数：j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.lift_π`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.eHomWhiskerRight_id`：eHomWhiskerRight_id (X Y : C) : eHom
WhiskerRight V (𝟙 X) Y = 𝟙 _
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma fac (j : J) : lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app j := by
  dsimp [coneFunctorEnrichedHom]
  ext k
  have := s.w k.hom
  dsimp at this
  -- this was produced by `simp? [lift, ← this]`
  simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, lift, functorEnrichedHom_obj,
    assoc, end_.lift_π, Iso.refl_inv, NatTrans.id_app, eHomWhiskerRight_id, Iso.refl_hom,
    eHomWhiskerLeft_id, comp_id, ← this, Under.map_obj_right, Under.mk_right]
  congr
  simp [Under.map, Comma.mapLeft]
  rfl

end isLimitConeFunctorEnrichedHom

set_option backward.isDefEq.respectTransparency false in
open isLimitConeFunctorEnrichedHom in
/-- The limit of `functorEnrichedHom V F₁ F₂` is `enrichedHom V F₁ F₂`. -/
/-
**CategoryTheory.Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：isLimitConeFunctorEnrichedHom : IsLimit (coneFunctorEnrichedHom V F₁ F₂) w
here lift
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom.fa
c`：fac (j : J) : lift s ≫ (coneFunctorEnrichedHom V F₁ F₂).π.app j = s.π.app j

--- 原说明 ---
The limit of `functorEnrichedHom V F₁ F₂` is `enrichedHom V F₁ F₂`.
-/
noncomputable def isLimitConeFunctorEnrichedHom :
    IsLimit (coneFunctorEnrichedHom V F₁ F₂) where
  lift := lift
  fac := fac
  uniq s m hm := by
    dsimp
    ext j
    simpa using ((hm j).trans (fac s j).symm) =≫ enrichedHomπ V _ _ (Under.mk (𝟙 j))

end

set_option backward.isDefEq.respectTransparency false in
/-- The identity for the `J ⥤ V`-enrichment of the category `J ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnrichedId** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnrichedId [HasFunctorEnrichedHom V F₁ F₁] : 𝟙_ (J ⥤ V) ⟶ functorEn
richedHom V F₁ F₁ where app j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity for the `J ⥤ V`-enrichment of the category `J ⥤ C`.
-/
noncomputable def functorEnrichedId [HasFunctorEnrichedHom V F₁ F₁] :
    𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₁ where
  app j := enrichedId V _

set_option backward.isDefEq.respectTransparency false in
/-- The composition for the `J ⥤ V`-enrichment of the category `J ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnrichedComp** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnrichedComp [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom
 V F₂ F₃] [HasFunctorEnrichedHom V F₁ F₃] : functorEnrichedHom V F₁ F₂ otimes fu
nctorEnrichedHom V F₂ F₃ ⟶ functorEnrichedHom V F₁ F₃ where app j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition for the `J ⥤ V`-enrichment of the category `J ⥤ C`.
-/
noncomputable def functorEnrichedComp [HasFunctorEnrichedHom V F₁ F₂]
    [HasFunctorEnrichedHom V F₂ F₃] [HasFunctorEnrichedHom V F₁ F₃] :
    functorEnrichedHom V F₁ F₂ ⊗ functorEnrichedHom V F₂ F₃ ⟶ functorEnrichedHom V F₁ F₃ where
  app j := enrichedComp V _ _ _
  naturality j j' f := by
    dsimp
    ext k
    dsimp
    rw [assoc, assoc, enrichedComp_π]
    dsimp
    rw [tensorHom_comp_tensorHom_assoc]
    simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnriched_id_comp** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnriched_id_comp [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnriche
dHom V F₁ F₁] : (fun_ (functorEnrichedHom V F₁ F₂)).inv ≫ functorEnrichedId V F₁
 ▷ functorEnrichedHom V F₁ F₂ ≫ functorEnrichedComp V F₁ F₁ F₂ = 𝟙 (functorEnric
hedHom V F₁ F₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enriched_id_comp`：enriched_id_co
mp [HasEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₂] : (fun_ (enrichedHom V F₁ F
₂)).inv ≫ enrichedId V F₁ ▷ enrichedHom V F₁ F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorEnriched_id_comp [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₁ F₁] :
    (λ_ (functorEnrichedHom V F₁ F₂)).inv ≫
      functorEnrichedId V F₁ ▷ functorEnrichedHom V F₁ F₂ ≫
        functorEnrichedComp V F₁ F₁ F₂ = 𝟙 (functorEnrichedHom V F₁ F₂) := by cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnriched_comp_id** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnriched_comp_id [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnriche
dHom V F₂ F₂] : (ρ_ (functorEnrichedHom V F₁ F₂)).inv ≫ functorEnrichedHom V F₁ 
F₂ ◁ functorEnrichedId V F₂ ≫ functorEnrichedComp V F₁ F₂ F₂ = 𝟙 (functorEnriche
dHom V F₁ F₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enriched_comp_id`：enriched_comp_
id [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₂ F₂] : (ρ_ (enrichedHom V F₁ F₂)
).inv ≫ enrichedHom V F₁ F₂ ◁ enrichedId V F₂ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorEnriched_comp_id [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₂] :
    (ρ_ (functorEnrichedHom V F₁ F₂)).inv ≫
      functorEnrichedHom V F₁ F₂ ◁ functorEnrichedId V F₂ ≫
        functorEnrichedComp V F₁ F₂ F₂ = 𝟙 (functorEnrichedHom V F₁ F₂) := by cat_disch

@[reassoc]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnriched_assoc** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnriched_assoc [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedH
om V F₂ F₃] [HasFunctorEnrichedHom V F₃ F₄] [HasFunctorEnrichedHom V F₁ F₃] [Has
FunctorEnrichedHom V F₂ F₄] [HasFunctorEnrichedHom V F₁ F₄] : (α_ _ _ _).inv ≫ f
unctorEnrichedComp V F₁ F₂ F₃ ▷ functorEnrichedHom V F₃ F₄ ≫ functorEnrichedComp
 V F₁ F₃ F₄ = functorEnrichedHom V F₁ F₂ ◁ functorEnrichedComp V F₂ F₃ F₄ ≫ func
torEnrichedComp V F₁ F₂ F₄
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enriched_assoc`：enriched_assoc [
HasEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₄] [HasEn
richedHom V F₂ F₃] [HasEnrichedHom V F₂ F₄] …
-/
lemma functorEnriched_assoc [HasFunctorEnrichedHom V F₁ F₂] [HasFunctorEnrichedHom V F₂ F₃]
    [HasFunctorEnrichedHom V F₃ F₄] [HasFunctorEnrichedHom V F₁ F₃]
    [HasFunctorEnrichedHom V F₂ F₄] [HasFunctorEnrichedHom V F₁ F₄] :
    (α_ _ _ _).inv ≫ functorEnrichedComp V F₁ F₂ F₃ ▷ functorEnrichedHom V F₃ F₄ ≫
      functorEnrichedComp V F₁ F₃ F₄ =
        functorEnrichedHom V F₁ F₂ ◁ functorEnrichedComp V F₂ F₃ F₄ ≫
          functorEnrichedComp V F₁ F₂ F₄ := by
  ext j
  dsimp
  rw [enriched_assoc]

variable (J C) in
/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category. -/
@[instance_reducible]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnrichedCategory** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnrichedCategory [forall (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom V F
₁ F₂] : EnrichedCategory (J ⥤ V) (J ⥤ C) where Hom F₁ F₂
参数：F₁ F₂ : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category.
-/
noncomputable def functorEnrichedCategory
    [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom V F₁ F₂] :
    EnrichedCategory (J ⥤ V) (J ⥤ C) where
  Hom F₁ F₂ := functorEnrichedHom V F₁ F₂
  id F := functorEnrichedId V F
  comp F₁ F₂ F₃ := functorEnrichedComp V F₁ F₂ F₃
  assoc F₁ F₂ F₃ F₄ := functorEnriched_assoc V F₁ F₂ F₃ F₄

variable {F₁ F₂} in
/-- Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary category,
this is the bijection `(F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂)`. -/
@[simps! apply_app]
/-
**CategoryTheory.Enriched.FunctorCategory.functorHomEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorHomEquiv [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂] :
 (F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Given functors `F₁` and `F₂` in `J ⥤ C`, where `C` is a `V`-enriched ordinary ca
tegory,
this is the bijection `(F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂)`.
-/
noncomputable def functorHomEquiv [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂] :
    (F₁ ⟶ F₂) ≃ (𝟙_ (J ⥤ V) ⟶ functorEnrichedHom V F₁ F₂) :=
  (homEquiv V).trans (isLimitConeFunctorEnrichedHom V F₁ F₂).homEquiv

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Enriched.FunctorCategory.functorHomEquiv_id** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorHomEquiv_id [HasFunctorEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₁
] : (functorHomEquiv V) (𝟙 F₁) = functorEnrichedId V F₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.lift_π`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.eHomWhiskerRight_id`：eHomWhiskerRight_id (X Y : C) : eHom
WhiskerRight V (𝟙 X) Y = 𝟙 _
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedId_π`：enrichedId_π (j : 
J) : enrichedId V F₁ ≫ end_.π _ j = eId V (F₁.obj j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorHomEquiv_id [HasFunctorEnrichedHom V F₁ F₁] [HasEnrichedHom V F₁ F₁] :
    (functorHomEquiv V) (𝟙 F₁) = functorEnrichedId V F₁ := by cat_disch

set_option backward.isDefEq.respectTransparency false in
variable {F₁ F₂ F₃} in
/-
**CategoryTheory.Enriched.FunctorCategory.functorHomEquiv_comp** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorHomEquiv_comp [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ 
F₂] [HasFunctorEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₃] [HasFunctorEnriched
Hom V F₁ F₃] [HasEnrichedHom V F₁ F₃] (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : (functorHomE
quiv V) (f ≫ g) = (fun_ (𝟙_ (J ⥤ V))).inv ≫ ((functorHomEquiv V) f otimesₘ (func
torHomEquiv V) g) ≫ functorEnrichedComp V F₁ F₂ F₃
参数：f : F₁ ⟶ F₂；g : F₂ ⟶ F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.homEquiv_comp`：homEquiv_comp (f 
: F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : (homEquiv V) (f ≫ g) = (fun_ (𝟙_ V)).inv ≫ ((homEquiv
 V) f otimesₘ (homEquiv V) g) ≫ enrichedCom…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.lift_π`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.eHomWhiskerRight_id`：eHomWhiskerRight_id (X Y : C) : eHom
WhiskerRight V (𝟙 X) Y = 𝟙 _
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.homEquiv_apply_π`：homEquiv_apply
_π (τ : F₁ ⟶ F₂) (j : J) : homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.
app j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma functorHomEquiv_comp [HasFunctorEnrichedHom V F₁ F₂] [HasEnrichedHom V F₁ F₂]
    [HasFunctorEnrichedHom V F₂ F₃] [HasEnrichedHom V F₂ F₃]
    [HasFunctorEnrichedHom V F₁ F₃] [HasEnrichedHom V F₁ F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    (functorHomEquiv V) (f ≫ g) = (λ_ (𝟙_ (J ⥤ V))).inv ≫
      ((functorHomEquiv V) f ⊗ₘ (functorHomEquiv V) g) ≫ functorEnrichedComp V F₁ F₂ F₃ := by
  ext j
  dsimp
  ext k
  rw [homEquiv_comp, assoc, assoc, assoc, assoc, assoc, end_.lift_π, enrichedComp_π]
  simp [tensorHom_comp_tensorHom_assoc]

attribute [local instance] functorEnrichedCategory

variable (J C) in
/-- If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category. -/
@[instance_reducible]
/-
**CategoryTheory.Enriched.FunctorCategory.functorEnrichedOrdinaryCategory** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Enriched.FunctorCategory`。
形式化陈述：functorEnrichedOrdinaryCategory [forall (F₁ F₂ : J ⥤ C), HasFunctorEnriche
dHom V F₁ F₂] [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] : EnrichedOrdinar
yCategory (J ⥤ V) (J ⥤ C) where homEquiv
参数：F₁ F₂ : J ⥤ C；F₁ F₂ : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a `V`-enriched ordinary category, and `C` has suitable limits,
then `J ⥤ C` is also a `J ⥤ V`-enriched ordinary category.
-/
noncomputable def functorEnrichedOrdinaryCategory
    [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom V F₁ F₂]
    [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom V F₁ F₂] :
    EnrichedOrdinaryCategory (J ⥤ V) (J ⥤ C) where
  homEquiv := functorHomEquiv V
  homEquiv_id F := functorHomEquiv_id V F
  homEquiv_comp f g := functorHomEquiv_comp V f g

end CategoryTheory.Enriched.FunctorCategory

