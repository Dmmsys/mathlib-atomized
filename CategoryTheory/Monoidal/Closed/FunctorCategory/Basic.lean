/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Enriched.FunctorCategory

/-!
# Functor categories are monoidal closed

Let `C` be a monoidal closed category. Let `J` be a category. In this file,
we obtain that the category `J ⥤ C` is monoidal closed if `C` has suitable
limits.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits MonoidalCategory

namespace MonoidalClosed

namespace FunctorCategory

open Enriched.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
  {J : Type u₂} [Category.{v₂} J]
  [∀ (F₁ F₂ : J ⥤ C), HasFunctorEnrichedHom C F₁ F₂]

attribute [local simp] enrichedCategorySelf_hom

section

variable {F₁ F₂ F₂' F₃ F₃' : J ⥤ C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃)` when `F₁`, `F₂`
and `F₃` are functors `J ⥤ C`, and `C` is monoidal closed. -/
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.homEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：homEquiv : (F₁ otimes F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where t
oFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃)` when `F₁`, `F
₂`
and `F₃` are functors `J ⥤ C`, and `C` is monoidal closed.
-/
noncomputable def homEquiv : (F₁ ⊗ F₂ ⟶ F₃) ≃ (F₂ ⟶ functorEnrichedHom C F₁ F₃) where
  toFun f :=
    { app j := end_.lift (fun k ↦ F₂.map k.hom ≫ curry (f.app k.right))
        (fun k₁ k₂ φ ↦ by
          dsimp
          simp only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Category.assoc,
            enrichedOrdinaryCategorySelf_eHomWhiskerRight]
          rw [← curry_natural_left_assoc, ← curry_natural_left_assoc,
            ← curry_natural_right, curry_pre_app, Category.assoc,
            ← f.naturality φ.right, Monoidal.tensorObj_map, tensorHom_def_assoc,
            ← Under.w φ, Functor.map_comp, MonoidalCategory.whiskerLeft_comp_assoc,
            whisker_exchange_assoc]) }
  invFun g :=
    { app j := uncurry (g.app j ≫ enrichedHomπ C _ _ (Under.mk (𝟙 j)))
      naturality j j' φ := by
        dsimp
        rw [← uncurry_natural_right, tensorHom_def'_assoc, ← uncurry_pre_app,
          ← uncurry_natural_left, Category.assoc, Category.assoc,
          NatTrans.naturality_assoc, functorEnrichedHom_map,
          end_.lift_π_assoc, enrichedOrdinaryCategorySelf_eHomWhiskerRight]
        dsimp
        rw [pre_id, NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
          Functor.map_id, Category.comp_id, Category.comp_id]
        congr 2
        rw [← enrichedOrdinaryCategorySelf_eHomWhiskerRight,
          ← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        let α : Under.mk (𝟙 j) ⟶ (Under.map φ).obj (Under.mk (𝟙 j')) := Under.homMk φ
        exact (enrichedHom_condition C (Under.forget j ⋙ F₁) (Under.forget j ⋙ F₃) α).symm }
  left_inv f := by cat_disch
  right_inv g := by
    ext j
    dsimp
    ext k
    -- this following list was obtained by
    -- `simp? [enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Under.map, Comma.mapLeft]`
    simp only [diagram_obj_obj, Functor.comp_obj, Under.forget_obj, enrichedCategorySelf_hom,
      curry_uncurry, NatTrans.naturality_assoc, functorEnrichedHom_obj, functorEnrichedHom_map,
      Under.map, Comma.mapLeft, Functor.const_obj_obj, Functor.id_obj, Discrete.natTrans_app,
      StructuredArrow.left_eq_id, end_.lift_π, Under.mk_right, Under.mk_hom, Iso.refl_inv,
      NatTrans.id_app, enrichedOrdinaryCategorySelf_eHomWhiskerRight, pre_id, Iso.refl_hom,
      enrichedOrdinaryCategorySelf_eHomWhiskerLeft, Functor.map_id, Category.comp_id]
    congr
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.homEquiv_naturality_two_symm** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom
 C F₁ F₃) : homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g
参数：f₂ : F₂ ⟶ F₂'；g : F₂' ⟶ functorEnrichedHom C F₁ F₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma homEquiv_naturality_two_symm (f₂ : F₂ ⟶ F₂') (g : F₂' ⟶ functorEnrichedHom C F₁ F₃) :
    homEquiv.symm (f₂ ≫ g) = F₁ ◁ f₂ ≫ homEquiv.symm g := by
  dsimp [homEquiv]
  ext j
  simp [← uncurry_natural_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.homEquiv_naturality_three** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：homEquiv_naturality_three [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
 (f : F₁ otimes F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') : homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ 
_).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫ functorEnrichedComp C F₁ F₃ F₃'
参数：F₁ F₂ : J ⥤ C；f : F₁ otimes F₂ ⟶ F₃；f₃ : F₃ ⟶ F₃'。
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.lift_π`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.enrichedComp_π`：enrichedComp_π (
j : J) : enrichedComp V F₁ F₂ F₃ ≫ end_.π _ j = (end_.π (diagram V F₁ F₂) j otim
esₘ end_.π (diagram V F₂ F₃) j) ≫ eComp V _ …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {X Y : C}   (f : X ⟶ Y) {Z : C}   (h :…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Limits.end_.lift_π_assoc`：∀ {J : Type u} [inst : Category
Theory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F : CategoryTheory.F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用引理 `CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRi
ght`：enrichedOrdinaryCategorySelf_eHomWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y 
: C) : eHomWhiskerRight C f Y = (pre f).app Y
· 使用引理 `CategoryTheory.MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLe
ft`：enrichedOrdinaryCategorySelf_eHomWhiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y
₂) : eHomWhiskerLeft C X g = (ihom X).map g
· 使用定理 `CategoryTheory.MonoidalClosed.pre_id`：pre_id (A : C) [Closed A] : pre (𝟙
 A) = 𝟙 _
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Enriched.FunctorCategory.homEquiv_apply_π`：homEquiv_apply
_π (τ : F₁ ⟶ F₂) (j : J) : homEquiv V τ ≫ enrichedHomπ V _ _ j = eHomEquiv V (τ.
app j)
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_right`：curry_natural_right (
f : A otimes X ⟶ Y) (g : Y ⟶ Y') : curry (f ≫ g) = curry f ≫ (ihom _).map g
-/
lemma homEquiv_naturality_three [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
    (f : F₁ ⊗ F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') :
    homEquiv (f ≫ f₃) = homEquiv f ≫ (ρ_ _).inv ≫ _ ◁ functorHomEquiv _ f₃ ≫
      functorEnrichedComp C F₁ F₃ F₃' := by
  dsimp [homEquiv]
  ext j
  dsimp
  ext k
  rw [Category.assoc, Category.assoc, Category.assoc, end_.lift_π, enrichedComp_π,
    tensorHom_def, Category.assoc, whisker_exchange_assoc, whiskerRight_id_assoc,
    Iso.inv_hom_id_assoc, end_.lift_π_assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, end_.lift_π,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight,
    enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
  dsimp
  rw [pre_id, NatTrans.id_app, Functor.map_id, Category.comp_id,
    Category.comp_id, homEquiv_apply_π, curry_natural_right]
  congr 2
  symm
  apply enrichedOrdinaryCategorySelf_eHomWhiskerLeft

end

variable [∀ (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂]
attribute [local instance] Enriched.FunctorCategory.functorEnrichedOrdinaryCategory

/-- When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint. -/
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.adj** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：adj (F : J ⥤ C) : MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F
⟩
参数：F : J ⥤ C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MonoidalClosed.FunctorCategory.homEquiv_naturality_three`
：homEquiv_naturality_three [forall (F₁ F₂ : J ⥤ C), HasEnrichedHom C F₁ F₂] (f :
 F₁ otimes F₂ ⟶ F₃) (f₃ : F₃ ⟶ F₃') : homEquiv (f ≫ f₃) = hom…

--- 原说明 ---
When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint.
-/
noncomputable def adj (F : J ⥤ C) :
    MonoidalCategory.tensorLeft F ⊣ (eHomFunctor _ _).obj ⟨F⟩ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ ↦ homEquiv
      homEquiv_naturality_left_symm := homEquiv_naturality_two_symm
      homEquiv_naturality_right := homEquiv_naturality_three }

/-- When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint. -/
@[instance_reducible]
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.closed** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：closed (F : J ⥤ C) : Closed F where rightAdj
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `C` is monoidal closed and has suitable limits,
then for any `F : J ⥤ C`, `tensorLeft F` has a right adjoint.
-/
noncomputable def closed (F : J ⥤ C) : Closed F where
  rightAdj := (eHomFunctor _ _).obj ⟨F⟩
  adj := adj F

/-- If `C` is monoidal closed and has suitable limits, the functor
category `J ⥤ C` is monoidal closed. -/
/-
**CategoryTheory.MonoidalClosed.FunctorCategory.monoidalClosed** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.MonoidalClosed.FunctorCategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.Monoidal
Closed C] →         {J : Type u₂} →           [inst_3 : CategoryTheory.Category.
{v₂, u₂} J] →             [∀ (F₁ F₂ : CategoryTheory.Functor J C),              
     CategoryTheory.Enriched.FunctorCategory.HasFunctorEnrichedHom C F₁ F₂] →   
            [∀ (F₁ F₂ : CategoryTheory.Functor J C), CategoryTheory.Enriched.Fun
ctorCategory.HasEnrichedHom C F₁ F₂] →                 CategoryTheory.MonoidalCl
osed (CategoryTheory.Functor J C)
参数：F₁ F₂ : CategoryTheory.Functor J C；F₁ F₂ : CategoryTheory.Functor J C；Categor
yTheory.Functor J C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is monoidal closed and has suitable limits, the functor
category `J ⥤ C` is monoidal closed.
-/
noncomputable scoped instance monoidalClosed : MonoidalClosed (J ⥤ C) where
  closed := closed

end FunctorCategory

end MonoidalClosed

end CategoryTheory

