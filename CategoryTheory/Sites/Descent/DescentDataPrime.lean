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
  {ι : Type t} {S : C} {X : ι -> C} {f : forall i, X i ⟶ S}
  (sq : forall i j, ChosenPullback (f i) (f j))
  (sq₃ : forall (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

section

variable {obj obj' : forall (i : ι), F.obj (.mk (op (X i)))}
  (hom : forall (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj' j))

/--
Definition of `pullHom'` / `pullHom'` 的定义

English:
definition pullHom'
  signature: ⦃Y
  body: pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂

@[reassoc]

中文:
定义 pullHom'
  签名: ⦃Y
  定义体: pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂

@[reassoc]

Depends on / 依赖: F.map, cat_disch, isPullback, isPullback.lift, op.toLoc, pullHom, toFunctor, toFunctor.obj
-/
noncomputable def pullHom' ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj' i₂) :=
  pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂

@[reassoc]
/--
lemma `pullHom'_eq_pullHom` / 引理 `pullHom'_eq_pullHom`

English:
lemma pullHom'_eq_pullHom
  given: ⦃Y
  statement: C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
  proof: by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> cat_disch
  rfl

@[reassoc]

中文:
引理 pullHom'_eq_pullHom
  条件: ⦃Y
  结论: C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
  证明: by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> cat_disch
  rfl

@[reassoc]
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
/--
lemma `pullHom'₁₂_eq_pullHom_of_chosenPullback₃` / 引理 `pullHom'₁₂_eq_pullHom_of_chosenPullback₃`

English:
lemma pullHom'₁₂_eq_pullHom_of_chosenPullback₃
  given: (i₁ i₂ i₃ : ι)
  proof: pullHom'_eq_pullHom _ _ _ ..

@[reassoc]

中文:
引理 pullHom'₁₂_eq_pullHom_of_chosenPullback₃
  条件: (i₁ i₂ i₃ : ι)
  证明: pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
-/
lemma pullHom'₁₂_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ =
      pullHom (hom i₁ i₂) (sq₃ i₁ i₂ i₃).p₁₂ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
/--
lemma `pullHom'₁₃_eq_pullHom_of_chosenPullback₃` / 引理 `pullHom'₁₃_eq_pullHom_of_chosenPullback₃`

English:
lemma pullHom'₁₃_eq_pullHom_of_chosenPullback₃
  given: (i₁ i₂ i₃ : ι)
  proof: pullHom'_eq_pullHom _ _ _ ..

@[reassoc]

中文:
引理 pullHom'₁₃_eq_pullHom_of_chosenPullback₃
  条件: (i₁ i₂ i₃ : ι)
  证明: pullHom'_eq_pullHom _ _ _ ..

@[reassoc]

Depends on / 依赖: Set.univ
-/
lemma pullHom'₁₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₁ i₃) (sq₃ i₁ i₂ i₃).p₁₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

@[reassoc]
/--
lemma `pullHom'₂₃_eq_pullHom_of_chosenPullback₃` / 引理 `pullHom'₂₃_eq_pullHom_of_chosenPullback₃`

English:
lemma pullHom'₂₃_eq_pullHom_of_chosenPullback₃
  given: (i₁ i₂ i₃ : ι)
  proof: pullHom'_eq_pullHom _ _ _ ..

中文:
引理 pullHom'₂₃_eq_pullHom_of_chosenPullback₃
  条件: (i₁ i₂ i₃ : ι)
  证明: pullHom'_eq_pullHom _ _ _ ..
-/
lemma pullHom'₂₃_eq_pullHom_of_chosenPullback₃ (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom (hom i₂ i₃) (sq₃ i₁ i₂ i₃).p₂₃ _ _ :=
  pullHom'_eq_pullHom _ _ _ ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pullHom_pullHom'` / 引理 `pullHom_pullHom'`

English:
lemma pullHom_pullHom'
  given: ⦃Y Y'
  statement: C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
  proof: by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [pullHom'_eq_pullHom _ _ _ _ (g ≫ p)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc]; rw [← op_comp]; rw [IsPullback.lift_fst])
    rfl (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl (by cat_disch)]
  simp

中文:
引理 pullHom_pullHom'
  条件: ⦃Y Y'
  结论: C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
  证明: by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [pullHom'_eq_pullHom _ _ _ _ (g ≫ p)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc]; rw [← op_comp]; rw [IsPullback.lift_fst])
    rfl (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl (by cat_disch)]
  simp

Depends on / 依赖: Category, Category.assoc, F.mapComp, Functor, Functor.map_comp, _eq_pullHom, _hom_whiskerRight_app, cat_disch, isPullback, isPullback.lift, mapComp, map_comp, pullHom
-/
lemma pullHom_pullHom' ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂)
    (hq : g ≫ q = q' := by cat_disch)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    pullHom (pullHom' hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ =
      pullHom' hom q' gf₁ gf₂ := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [pullHom'_eq_pullHom _ _ _ _ (g ≫ p)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc]; rw [← op_comp]; rw [IsPullback.lift_fst])
    rfl (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl (by cat_disch)]
  simp

end

section

variable {obj : forall (i : ι), F.obj (.mk (op (X i)))}
  (hom : forall (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

@[simp]
/--
lemma `pullHom'_p₁_p₂` / 引理 `pullHom'_p₁_p₂`

English:
lemma pullHom'_p₁_p₂
  given: (i₁ i₂ : ι)
  proof: by
  simp [pullHom'_eq_pullHom hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (𝟙 _)]

中文:
引理 pullHom'_p₁_p₂
  条件: (i₁ i₂ : ι)
  证明: by
  simp [pullHom'_eq_pullHom hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (𝟙 _)]
-/
lemma pullHom'_p₁_p₂ (i₁ i₂ : ι) :
    pullHom' hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (by simp) (by simp) = hom i₁ i₂ := by
  simp [pullHom'_eq_pullHom hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ (𝟙 _)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullHom'_self'` / 引理 `pullHom'_self'`

English:
lemma pullHom'_self'
  statement: (hom_self : forall i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
  proof: by
  simp [← pullHom_pullHom' hom g (f i) q (𝟙 (X i)) (𝟙 (X i)) g g hg, hom_self, pullHom]

中文:
引理 pullHom'_self'
  结论: (hom_self : 对任意 i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
  证明: by
  simp [← pullHom_pullHom' hom g (f i) q (𝟙 (X i)) (𝟙 (X i)) g g hg, hom_self, pullHom]
-/
lemma pullHom'_self' (hom_self : forall i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' hom q g g hg hg = 𝟙 _ := by
  simp [← pullHom_pullHom' hom g (f i) q (𝟙 (X i)) (𝟙 (X i)) g g hg, hom_self, pullHom]

set_option backward.isDefEq.respectTransparency false in
variable {sq₃} in
@[reassoc]
/--
lemma `comp_pullHom''` / 引理 `comp_pullHom''`

English:
lemma comp_pullHom''
  statement: (hom_comp : forall (i₁ i₂ i₃ : ι),
  proof: by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pullHom_pullHom'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ _ _]
  dsimp [pullHom]
  simp [← Functor.map_comp_assoc, hom_comp]

中文:
引理 comp_pullHom''
  结论: (hom_comp : 对任意 (i₁ i₂ i₃ : ι),
  证明: by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pullHom_pullHom'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ _ _]
  dsimp [pullHom]
  simp [← Functor.map_comp_assoc, hom_comp]

Depends on / 依赖: Functor, Functor.map_comp_assoc, _assoc, exists_lift, hom_comp, map_comp_assoc, pullHom, pullHom_pullHom
-/
lemma comp_pullHom'' (hom_comp : forall (i₁ i₂ i₃ : ι),
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    pullHom' hom q f₁ f₂ ≫ pullHom' hom q f₂ f₃ = pullHom' hom q f₁ f₃ := by
  obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
  rw [← pullHom_pullHom'_assoc hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ _ _]; rw [← pullHom_pullHom' hom φ (sq₃ i₁ i₂ i₃).p _ (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ _ _]
  dsimp [pullHom]
  simp [← Functor.map_comp_assoc, hom_comp]

end

end DescentData'

open DescentData' in
/--
Definition of `DescentData'` / `DescentData'` 的定义

English:
structure DescentData'
  parameters: where
  axioms and operations (4):
    - obj((i : ι)) : F.obj (.mk (op (X i)))
    - hom : forall (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶ (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
    - pullHom'_hom_self : forall i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
    - pullHom'_hom_comp((i₁ i₂ i₃ : ι)) : pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫ pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ = pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

中文:
结构 下降数据'
  参数: where
  公理与运算 (4 个):
    - obj((i : ι)) : F.obj (.mk (op (X i)))
    - hom : 对任意 (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶ (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
    - pullHom'_hom_self : 对任意 i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
    - pullHom'_hom_comp((i₁ i₂ i₃ : ι)) : pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫ pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ = pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃
-/
structure DescentData' where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pulling back to the chosen pullbacks. It follows
  from the conditions `pullHom'_hom_self` and `pullHom'_hom_comp` that these morphisms
  are isomorphisms. -/
  hom : forall (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
  pullHom'_hom_self : forall i, pullHom' hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _
  pullHom'_hom_comp (i₁ i₂ i₃ : ι) :
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
    pullHom' hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃

namespace DescentData'

attribute [reassoc] pullHom'_hom_comp

variable {F sq sq₃}

@[simp]
/--
lemma `pullHom'_self` / 引理 `pullHom'_self`

English:
lemma pullHom'_self
  statement: (D : F.DescentData' sq sq₃)
  proof: pullHom'_self' _ D.pullHom'_hom_self _ _

@[reassoc (attr := simp)]

中文:
引理 pullHom'_self
  结论: (D : F.下降数据' sq sq₃)
  证明: pullHom'_self' _ D.pullHom'_hom_self _ _

@[reassoc (attr := simp)]
-/
lemma pullHom'_self (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q := by cat_disch) :
    pullHom' D.hom q g g hg hg = 𝟙 _ :=
  pullHom'_self' _ D.pullHom'_hom_self _ _

@[reassoc (attr := simp)]
/--
lemma `comp_pullHom'` / 引理 `comp_pullHom'`

English:
lemma comp_pullHom'
  statement: (D : F.DescentData' sq sq₃)
  proof: comp_pullHom'' _ D.pullHom'_hom_comp _ _ _ _ hf₁ hf₂ hf₃

中文:
引理 comp_pullHom'
  结论: (D : F.下降数据' sq sq₃)
  证明: comp_pullHom'' _ D.pullHom'_hom_comp _ _ _ _ hf₁ hf₂ hf₃

Depends on / 依赖: D.hom, D.pullHom, _hom_comp, cat_disch, comp_pullHom, pullHom
-/
lemma comp_pullHom' (D : F.DescentData' sq sq₃)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) (hf₃ : f₃ ≫ f i₃ = q := by cat_disch) :
    pullHom' D.hom q f₁ f₂ hf₁ hf₂ ≫ pullHom' D.hom q f₂ f₃ hf₂ hf₃ =
      pullHom' D.hom q f₁ f₃ hf₁ hf₃ :=
  comp_pullHom'' _ D.pullHom'_hom_comp _ _ _ _ hf₁ hf₂ hf₃

instance (D : F.DescentData' sq sq₃)
    {Y : C} (q : Y ⟶ S) (i₁ i₂ : ι) (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (pullHom' D.hom q f₁ f₂ hf₁ hf₂) :=
  ⟨pullHom' D.hom q f₂ f₁ hf₂ hf₁, by simp, by simp⟩

/--
lemma `pullHom'_eq_hom` / 引理 `pullHom'_eq_hom`

English:
lemma pullHom'_eq_hom
  given: (D : F.DescentData' sq sq₃) (i₁ i₂ : ι)
  proof: by
  simp

中文:
引理 pullHom'_eq_hom
  条件: (D : F.下降数据' sq sq₃) (i₁ i₂ : ι)
  证明: by
  simp
-/
lemma pullHom'_eq_hom (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    pullHom' D.hom _ _ _ (by simp) = D.hom i₁ i₂ := by
  simp

instance (D : F.DescentData' sq sq₃) (i₁ i₂ : ι) :
    IsIso (D.hom i₁ i₂) := by
  simpa using (inferInstance : IsIso (pullHom' D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂))

/-- The type of morphisms in the category `F.DescentData' sq sq₃`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (D₁ D₂ : F.DescentData' sq sq₃)
  axioms and operations (2):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm((i₁ i₂ : ι)) : (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom i₁ i₂ = D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (hom i₂)  [default: by cat_disch]

中文:
结构 态射
  参数: (D₁ D₂ : F.下降数据' sq sq₃)
  公理与运算 (2 个):
    - hom((i : ι)) : D₁.obj i ⟶ D₂.obj i
    - comm((i₁ i₂ : ι)) : (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom i₁ i₂ = D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (hom i₂)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (D₁ D₂ : F.DescentData' sq sq₃) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm (i₁ i₂ : ι) :
    (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom i₁ i₂ =
    D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (F.DescentData' sq sq₃)
  body: Hom

@[simps id_hom comp_hom]

中文:
实例 :
  签名: 箭图 (F.下降数据' sq sq₃)
  定义体: Hom

@[simps id_hom comp_hom]
-/
instance : Quiver (F.DescentData' sq sq₃) where
  Hom := Hom

@[simps id_hom comp_hom]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (F.DescentData' sq sq₃)
  body: { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

中文:
实例 :
  签名: 范畴 (F.下降数据' sq sq₃)
  定义体: { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }
-/
instance : Category (F.DescentData' sq sq₃) where
  id _ := { hom _ := 𝟙 _ }
  comp f g := { hom i := f.hom i ≫ g.hom i }

attribute [reassoc] comp_hom

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
  proof: Hom.ext (funext h)

中文:
引理 hom_ext
  结论: {D₁ D₂ : F.下降数据' sq sq₃} {f g : D₁ ⟶ D₂}
  证明: Hom.ext (funext h)

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {D₁ D₂ : F.DescentData' sq sq₃} {f g : D₁ ⟶ D₂}
    (h : forall i, f.hom i = g.hom i) : f = g :=
  Hom.ext (funext h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `comm` / 引理 `comm`

English:
lemma comm
  statement: {D₁ D₂ : F.DescentData' sq sq₃} (φ : D₁ ⟶ D₂)
  proof: by
  obtain ⟨p, _, _⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [← pullHom_pullHom' D₂.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [← pullHom_pullHom' D₁.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [pullHom'_p₁_p₂]; rw [pullHom'_p₁_p₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]; rw [φ.comm]; rw [Functor.map_comp_assoc]; rw [mapComp'_inv_naturality]
  simp only [Category.assoc]

中文:
引理 comm
  结论: {D₁ D₂ : F.下降数据' sq sq₃} (φ : D₁ ⟶ D₂)
  证明: by
  obtain ⟨p, _, _⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [← pullHom_pullHom' D₂.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [← pullHom_pullHom' D₁.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [pullHom'_p₁_p₂]; rw [pullHom'_p₁_p₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]; rw [φ.comm]; rw [Functor.map_comp_assoc]; rw [mapComp'_inv_naturality]
  simp only [Category.assoc]

Depends on / 依赖: F.map, cat_disch, exists_lift, isPullback, isPullback.exists_lift, op.toLoc, pullHom, pullHom_pullHom, toFunctor, toFunctor.map
-/
lemma comm {D₁ D₂ : F.DescentData' sq sq₃} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫ pullHom' D₂.hom q f₁ f₂ hf₁ hf₂ =
      pullHom' D₁.hom q f₁ f₂ hf₁ hf₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  obtain ⟨p, _, _⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [← pullHom_pullHom' D₂.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [← pullHom_pullHom' D₁.hom p (sq i₁ i₂).p q (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ f₁ f₂]; rw [pullHom'_p₁_p₂]; rw [pullHom'_p₁_p₂]
  dsimp only [pullHom]
  rw [NatTrans.naturality_assoc]
  dsimp
  rw [← Functor.map_comp_assoc]; rw [φ.comm]; rw [Functor.map_comp_assoc]; rw [mapComp'_inv_naturality]
  simp only [Category.assoc]

/-- Constructor for isomorphisms in the category `F.DescentData' sq sq₃`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {D₁ D₂ : F.DescentData' sq sq₃} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
  body: (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_mono ((F.map _).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map _).toFunctor.map (e i₁).hom)]; rw [Iso.map_hom_inv_id_assoc]; rw [comm i₁ i₂]

中文:
定义 isoMk
  签名: {D₁ D₂ : F.下降数据' sq sq₃} (e : 对任意 (i : ι), D₁.obj i ≅ D₂.obj i)
  定义体: (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_mono ((F.map _).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map _).toFunctor.map (e i₁).hom)]; rw [Iso.map_hom_inv_id_assoc]; rw [comm i₁ i₂]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, F.map, Iso.map_hom_inv_id_assoc, Iso.map_inv_hom_id, cancel_epi, cancel_mono, cat_disch, comp_id, hom.comm, hom.hom, inv.comm, inv.hom, map_hom_inv_id_assoc, map_inv_hom_id, toFunctor, toFunctor.map
-/
def isoMk {D₁ D₂ : F.DescentData' sq sq₃} (e : forall (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : forall (i₁ i₂ : ι), (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom i₁ i₂ =
      D₁.hom i₁ i₂ ≫ (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) :
    D₁ ≅ D₂ where
  hom.hom i := (e i).hom
  hom.comm := comm
  inv.hom i := (e i).inv
  inv.comm i₁ i₂ := by
    rw [← cancel_mono ((F.map _).toFunctor.map (e i₂).hom)]; rw [Category.assoc]; rw [Category.assoc]; rw [Iso.map_inv_hom_id]; rw [Category.comp_id]; rw [← cancel_epi ((F.map _).toFunctor.map (e i₁).hom)]; rw [Iso.map_hom_inv_id_assoc]; rw [comm i₁ i₂]

/-- The functor `toDescentDataFunctor : F.DescentData' sq sq₃ ⥤ F.DescentData f`, on objects. -/
@[simps]
/--
Definition of `descentData` / `descentData` 的定义

English:
definition descentData
  signature: (D : F.DescentData' sq sq₃)
  body: D.obj
  hom _ _ _ _ _ _ _ _ := pullHom' D.hom _ _ _
  pullHom_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    pullHom_pullHom' _ _ _ _ _ _ _ _

中文:
定义 descentData
  签名: (D : F.下降数据' sq sq₃)
  定义体: D.obj
  hom _ _ _ _ _ _ _ _ := pullHom' D.hom _ _ _
  pullHom_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    pullHom_pullHom' _ _ _ _ _ _ _ _

Depends on / 依赖: D.obj
-/
noncomputable def descentData (D : F.DescentData' sq sq₃) : F.DescentData f where
  obj := D.obj
  hom _ _ _ _ _ _ _ _ := pullHom' D.hom _ _ _
  pullHom_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    pullHom_pullHom' _ _ _ _ _ _ _ _

variable (sq sq₃) in
/-- The functor `fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃`, on objects. -/
@[simps]
/--
Definition of `ofDescentData` / `ofDescentData` 的定义

English:
definition ofDescentData
  signature: (D : F.DescentData f)
  body: D.obj
  hom i₁ i₂ := D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
  pullHom'_hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    have : p ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% h₁]
    rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [D.pullHom_hom _ _ (f i)]; rw [D.hom_self (f i) (𝟙 _)]
    all_goals cat_disch
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.hom_comp]
    all_goals cat_disch

中文:
定义 ofDescentData
  签名: (D : F.下降数据 f)
  定义体: D.obj
  hom i₁ i₂ := D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
  pullHom'_hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    have : p ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% h₁]
    rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [D.pullHom_hom _ _ (f i)]; rw [D.hom_self (f i) (𝟙 _)]
    all_goals cat_disch
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.hom_comp]
    all_goals cat_disch

Depends on / 依赖: D.obj
-/
def ofDescentData (D : F.DescentData f) : F.DescentData' sq sq₃ where
  obj := D.obj
  hom i₁ i₂ := D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂
  pullHom'_hom_self i := by
    obtain ⟨p, h₁, h₂⟩ := (sq i i).isPullback.exists_lift (𝟙 _) (𝟙 _) (by simp)
    have : p ≫ (sq i i).p = f i := by rw [← (sq i i).hp₁, reassoc_of% h₁]
    rw [pullHom'_eq_pullHom _ _ _ _ p]; rw [D.pullHom_hom _ _ (f i)]; rw [D.hom_self (f i) (𝟙 _)]
    all_goals cat_disch
  pullHom'_hom_comp i₁ i₂ i₃ := by
    rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₂]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₂₃]; rw [pullHom'_eq_pullHom _ _ _ _ (sq₃ i₁ i₂ i₃).p₁₃]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.pullHom_hom _ _ (sq₃ i₁ i₂ i₃).p]; rw [D.hom_comp]
    all_goals cat_disch

set_option backward.defeqAttrib.useBackward true in
variable (sq sq₃) in
@[simp]
/--
lemma `pullHom'_ofDescentData_hom` / 引理 `pullHom'_ofDescentData_hom`

English:
lemma pullHom'_ofDescentData_hom
  statement: (D : F.DescentData f)
  proof: by
  obtain ⟨p, h₁, h₂⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]
  dsimp
  rw [D.pullHom_hom _ _ _ (by rw [← (sq i₁ i₂).hp₁]; rw [reassoc_of% h₁]; rw [hf₁]) _ _
    (by simp) (by simp) _ _ h₁ h₂]

中文:
引理 pullHom'_ofDescentData_hom
  结论: (D : F.下降数据 f)
  证明: by
  obtain ⟨p, h₁, h₂⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]
  dsimp
  rw [D.pullHom_hom _ _ _ (by rw [← (sq i₁ i₂).hp₁]; rw [reassoc_of% h₁]; rw [hf₁]) _ _
    (by simp) (by simp) _ _ h₁ h₂]
-/
lemma pullHom'_ofDescentData_hom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    pullHom' (ofDescentData sq sq₃ D).hom q f₁ f₂ hf₁ hf₂ = D.hom q f₁ f₂ hf₁ hf₂ := by
  obtain ⟨p, h₁, h₂⟩ := (sq i₁ i₂).isPullback.exists_lift f₁ f₂ (by cat_disch)
  rw [pullHom'_eq_pullHom _ _ _ _ p]
  dsimp
  rw [D.pullHom_hom _ _ _ (by rw [← (sq i₁ i₂).hp₁]; rw [reassoc_of% h₁]; rw [hf₁]) _ _
    (by simp) (by simp) _ _ h₁ h₂]

variable (F sq sq₃)

/-- The functor `F.DescentData' sq sq₃ ⥤ F.DescentData f`. -/
@[simps]
/--
Definition of `toDescentDataFunctor` / `toDescentDataFunctor` 的定义

English:
definition toDescentDataFunctor
  signature: : F.DescentData' sq sq₃ ⥤ F.DescentData f where
  body: D.descentData
  map φ :=
    { hom := φ.hom
      comm := comm φ }

中文:
定义 toDescentDataFunctor
  签名: : F.下降数据' sq sq₃ ⥤ F.下降数据 f where
  定义体: D.descentData
  map φ :=
    { hom := φ.hom
      comm := comm φ }

Depends on / 依赖: D.descentData, descentData
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
/--
Definition of `fromDescentDataFunctor` / `fromDescentDataFunctor` 的定义

English:
definition fromDescentDataFunctor
  signature: : F.DescentData f ⥤ F.DescentData' sq sq₃ where
  body: .ofDescentData _ _ D
  map φ := { hom := φ.hom }

中文:
定义 fromDescentDataFunctor
  签名: : F.下降数据 f ⥤ F.下降数据' sq sq₃ where
  定义体: .ofDescentData _ _ D
  map φ := { hom := φ.hom }

Depends on / 依赖: ofDescentData
-/
noncomputable def fromDescentDataFunctor : F.DescentData f ⥤ F.DescentData' sq sq₃ where
  obj D := .ofDescentData _ _ D
  map φ := { hom := φ.hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `F.DescentData' sq sq₃ ≌ F.DescentData f`. -/
@[simps]
/--
Definition of `descentDataEquivalence` / `descentDataEquivalence` 的定义

English:
definition descentDataEquivalence
  signature: : F.DescentData' sq sq₃ ≌ F.DescentData f where
  body: toDescentDataFunctor _ _ _
  inverse := fromDescentDataFunctor _ _ _
  unitIso := NatIso.ofComponents (fun D => isoMk (fun _ => Iso.refl _))
  counitIso := NatIso.ofComponents (fun D => DescentData.isoMk (fun _ => Iso.refl _))

中文:
定义 descentDataEquivalence
  签名: : F.下降数据' sq sq₃ ≌ F.下降数据 f where
  定义体: toDescentDataFunctor _ _ _
  inverse := fromDescentDataFunctor _ _ _
  unitIso := NatIso.ofComponents (fun D => isoMk (fun _ => Iso.refl _))
  counitIso := NatIso.ofComponents (fun D => DescentData.isoMk (fun _ => Iso.refl _))

Depends on / 依赖: toDescentDataFunctor
-/
noncomputable def descentDataEquivalence : F.DescentData' sq sq₃ ≌ F.DescentData f where
  functor := toDescentDataFunctor _ _ _
  inverse := fromDescentDataFunctor _ _ _
  unitIso := NatIso.ofComponents (fun D => isoMk (fun _ => Iso.refl _))
  counitIso := NatIso.ofComponents (fun D => DescentData.isoMk (fun _ => Iso.refl _))

end DescentData'

end Pseudofunctor

end CategoryTheory
