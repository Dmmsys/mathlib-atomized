/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Descent data when we have pullbacks

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
a family of maps `f i : X i ⟶ S` in the category `C`, chosen pullbacks `sq`
and threefold wide pullbacks `sq₃` for these morphisms, we define a
category `F.DescentData' sq sq₃` of objects over the `X i`
equipped with a descent data relative to the morphisms `f i : X i ⟶ S`, where
the data and compatibilities are expressed using the chosen pullbacks.

-/

@[expose] public section

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

section

variable {obj obj' : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj' j))

/-- Variant of `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` when we have
chosen pullbacks. -/
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` when we have
chosen pullbacks.
-/
noncomputable def pullHom' ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj' i₂) :=
  pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_eq_pullHom** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_eq_pullHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (p : Y ⟶ (sq i₁ i₂).pullback)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁ := by cat_disch)
    (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂ := by cat_disch) :
  pullHom' hom q f₁ f₂ hf₁ hf₂ =
    pullHom (hom i₁ i₂) p f₁ f₂ := by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> cat_disch
  rfl

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ =
      pullHom (hom i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom_pullHom'** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom_pullHom' ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hq : g ≫ q = q' := by cat_disch)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    pullHom (pullHom' hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ =
      pullHom' hom q' gf₁ gf₂ := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p, pullHom'_eq_pullHom _ _ _ _ (g ≫ p)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst])
    rfl (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl (by cat_disch)]
  simp

end

section

variable {obj : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

@[simp]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_p** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_p₁_p₂ (i₁ i₂ : ι) :
    pullHom' hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (by simp) (by simp) = hom i₁ i₂ := by
  simp [pullHom'_eq_pullHom hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (𝟙 _)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_self'** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_self' (hom_self : ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' hom q g g hg hg = 𝟙 _ := by
  simp [← pullHom_pullHom' hom g (f i) q (𝟙 (X i)) (𝟙 (X i)) g g hg, hom_self, pullHom]

set_option backward.isDefEq.respectTransparency false in
variable {sq₃} in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.comp_pullHom''** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_pullHom'' (hom_comp : ∀ (i₁ i₂ i₃ : ι),
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom' hom q f₁ f₂ ≫ pullHom' hom q f₂ f₃ = pullHom' hom q f₁ f₃ := by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pullHom_pullHom'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _,
    ← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ _ _,
    ← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ _ _]
  dsimp [pullHom]
  simp [← Functor.map_comp_assoc, hom_comp]

end

end DescentData'

open DescentData' in
/-- Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, a family of
morphisms `f i : X i ⟶ S`, chosen pullbacks `sq i j` of `f i` and `f j` for all `i` and `j`,
and chosen threefold wide pullbacks `sq₃`, this structure contains a description
of objects over the `X i` equipped with a descent data relative to the morphisms `f i`,
where the (iso)morphisms are compatibilities are considered over the chosen pullbacks. -/
/-
**CategoryTheory.Pseudofunctor.DescentData'** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Pseudofunctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) CategoryTheory.Cat →   
    {ι : Type t} →         {S : C} →           {X : ι → C} →             {f : (i
 : ι) → X i ⟶ S} →               (sq : (i j : ι) → CategoryTheory.Limits.ChosenP
ullback (f i) (f j)) →                 ((i₁ i₂ i₃ : ι) → CategoryTheory.Limits.C
hosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)) →                   Type (max (
max t u') v')
参数：CategoryTheory.LocallyDiscrete Cᵒᵖ；i : ι；sq : (i j : ι) → CategoryTheory.Limi
ts.ChosenPullback (f i) (f j)；(i₁ i₂ i₃ : ι) → CategoryTheory.Limits.ChosenPullb
ack₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃)；max (max t u') v'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, a family of
morphisms `f i : X i ⟶ S`, chosen pullbacks `sq i j` of `f i` and `f j` for all 
`i` and `j`,
and chosen threefold wide pullbacks `sq₃`, this structure contains a description
of objects over the `X i` equipped with a descent data relative to the morphisms
 `f i`,
where the (iso)morphisms are compatibilities are considered over the chosen pull
backs.
-/
structure DescentData' where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pulling back to the chosen pullbacks. It follows
  from the conditions `pullHom'_hom_self` and `pullHom'_hom_comp` that these morphisms
  are isomorphisms. -/
  hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
  pullHom'_hom_self : ∀ i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
  pullHom'_hom_comp (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentData'

attribute [reassoc] pullHom'_hom_comp

variable {F sq sq₃}

@[simp]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_self** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_self (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' D.hom q g g hg hg = 𝟙 _ :=
  pullHom'_self' _ D.pullHom'_hom_self _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Pseudofunctor.DescentData.comp_pullHom'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_pullHom' (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) (hf₃ : f₃ ≫ f i₃ = q := by cat_disch) :
    pullHom' D.hom q f₁ f₂ hf₁ hf₂ ≫ pullHom' D.hom q f₂ f₃ hf₂ hf₃ =
      pullHom' D.hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom'' _ D.pullHom'_hom_comp _ _ _ _ hf₁ hf₂ hf₃
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (D : F.DescentData' sq sq₃)
    {Y : C} (q : Y ⟶ S) (i₁ i₂ : ι) (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (pullHom' D.hom q f₁ f₂ hf₁ hf₂) :=
  ⟨pullHom' D.hom q f₂ f₁ hf₂ hf₁, by simp, by simp⟩
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_eq_hom** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_eq_hom (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    pullHom' D.hom _ _ _ (by simp) = D.hom i₁ i₂ := by
  simp
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    IsIso (D.hom i₁ i₂) := by
  simpa using (inferInstance : IsIso (pullHom' D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂))

/-- The type of morphisms in the category `F.DescentData' sq sq₃`. -/
@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentData.Hom** 是 Mathlib 中的一个结构，位于命名空间 `Catego
ryTheory.Pseudofunctor.DescentData`。
形式化陈述：Hom (D₁ D₂ : F.DescentData f) where /-- The morphisms between the `obj` fi
elds of descent data. -/ hom (i : ι) : D₁.obj i ⟶ D₂.obj i comm ⦃Y : C⦄ (q : Y ⟶
 S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ 
≫ f i₂ = q) : (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ = D₁.h
om q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂)
参数：D₁ D₂ : F.DescentData f；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `F.DescentData' sq sq₃`.
-/
structure Hom (D₁ D₂ : F.DescentData' sq sq₃) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom i₁ i₂ =
    D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (F.DescentData' sq sq₃) where
  Hom := Hom

@[simps id_hom comp_hom]
/-
**CategoryTheory.Pseudofunctor.DescentData.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (F.DescentData' sq sq₃) where
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

attribute [reassoc] comp_hom

@[ext]
/-
**CategoryTheory.Pseudofunctor.DescentData.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Pseudofunctor.DescentData`。
形式化陈述：hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂} (h : forall i, φ.hom i 
= φ'.hom i) : φ = φ'
参数：h : forall i, φ.hom i = φ'.hom i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pseudofunctor.DescentData.Hom.ext`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C}   {F : CategoryTheory.Pseudofunctor (Category
Theory.LocallyDiscrete Cᵒᵖ) CategoryTh…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
    (h : ∀ i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Pseudofunctor.DescentData.comm** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm {D₁ D₂ : F.DescentData' sq sq₃} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫ pullHom' D₂.hom q f₁ f₂ hf₁ hf₂ =
      pullHom' D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  obtain ⟨p, _, _⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [← pullHom_pullHom' D₂.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂,
    ← pullHom_pullHom' D₁.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂,
    pullHom'_p₁_p₂, pullHom'_p₁_p₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc, φ.comm, Functor.map_comp_assoc, mapComp'_inv_naturality]
  simp only [Category.assoc]

/-- Constructor for isomorphisms in the category `F.DescentData' sq sq₃`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Pseudofunctor.DescentData`。
形式化陈述：isoMk {D₁ D₂ : F.DescentData f} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i) 
(comm : forall ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (
hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q), (F.map f₁.op.toLoc).toFunctor.map (e
 i₁).hom ≫ D₂.hom q f₁ f₂ = D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (
e i₂).hom
参数：e : forall (i : ι), D₁.obj i ≅ D₂.obj i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category `F.DescentData' sq sq₃`.
-/
def isoMk {D₁ D₂ : F.DescentData' sq sq₃} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ (i₁ i₂ : ι), (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom i₁ i₂ =
      D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_mono ((F.map _).toFunctor.map (e i₂).hom), Category.assoc,
      Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
      ← cancel_epi ((F.map _).toFunctor.map (e i₁).hom),
      Iso.map_hom_inv_id_assoc, comm i₁ i₂]

/-- The functor `toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f`, on objects. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.descentData** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f`, on
 objects.
-/
noncomputable def descentData (D : F.DescentData' sq sq₃) : F.DescentData f where
  obj := D.obj
  hom _ _ _ _ _ _ _ _ := pullHom' D.hom _ _ _
  pullHom_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    pullHom_pullHom' _ _ _ _ _ _ _ _

variable (sq sq₃) in
/-- The functor `fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃`, on objects. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.ofDescentData** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃`, 
on objects.
-/
def ofDescentData (D : F.DescentData f) : F.DescentData' sq sq₃ where
  obj := D.obj
  hom i₁ i₂ := D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
  pullHom'_hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    have : p ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% h₁]
    rw [pullHom'_eq_pullHom _ _ _ _ p, D.pullHom_hom _ _ (f i), D.hom_self (f i) (𝟙 _)]
    all_goals cat_disch
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂,
      pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃,
      pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃,
      D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p, D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p,
      D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p, D.hom_comp]
    all_goals cat_disch

set_option backward.defeqAttrib.useBackward true in
variable (sq sq₃) in
@[simp]
/-
**CategoryTheory.Pseudofunctor.DescentData.pullHom'_ofDescentData_hom** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullHom'_ofDescentData_hom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    pullHom' (ofDescentData sq sq₃ D).hom q f₁ f₂ hf₁ hf₂ = D.hom q f₁ f₂ hf₁ hf₂ := by
  obtain ⟨p, h₁, h₂⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]
  dsimp
  rw [D.pullHom_hom _ _ _ (by rw [← (sq i₁ i₂).hp₁, reassoc_of% h₁, hf₁]) _ _
    (by simp) (by simp) _ _ h₁ h₂]

variable (F sq sq₃)

/-- The functor `F.DescentData' sq sq₃ ⥤ F.DescentData f`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.toDescentDataFunctor** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.DescentData' sq sq₃ ⥤ F.DescentData f`.
-/
noncomputable def toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f where
  obj D := D.descentData
  map φ :=
    { hom := φ.hom
      comm := comm φ }

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] DescentData.Hom.comm in
/-- The functor `F.DescentData f ⥤ F.DescentData' sq sq₃`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.fromDescentDataFunctor** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.DescentData f ⥤ F.DescentData' sq sq₃`.
-/
noncomputable def fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃ where
  obj D := .ofDescentData _ _ D
  map φ := { hom := φ.hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `F.DescentData' sq sq₃ ≌ F.DescentData f`. -/
@[simps]
/-
**CategoryTheory.Pseudofunctor.DescentData.descentDataEquivalence** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Pseudofunctor.DescentData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `F.DescentData' sq sq₃ ≌ F.DescentData f`.
-/
noncomputable def descentDataEquivalence : F.DescentData' sq sq₃ ≌ F.DescentData f where
  functor := toDescentDataFunctor _ _ _
  inverse := fromDescentDataFunctor _ _ _
  unitIso := NatIso.ofComponents (fun D ↦ isoMk (fun _ ↦ Iso.refl _))
  counitIso := NatIso.ofComponents (fun D ↦ DescentData.isoMk (fun _ ↦ Iso.refl _))

end DescentData'

end Pseudofunctor

end CategoryTheory

