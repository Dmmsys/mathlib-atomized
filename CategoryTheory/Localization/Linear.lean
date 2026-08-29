/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Center.Localization
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Localization of linear categories

If `L : C ⥤ D` is an additive localization functor between preadditive categories,
and `C` is `R`-linear, we show that `D` can also be equipped with an `R`-linear
structure such that `L` is an `R`-linear functor.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Localization

variable (R : Type w) [Ring R] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [L.Additive] [Linear R C]

/-- If `L : C ⥤ D` is a localization functor and `C` is `R`-linear, then `D` is
`R`-linear if we already know that `D` is preadditive and `L` is additive. -/
@[instance_reducible]
/--
Definition of `linear` / `linear` 的定义

English:
definition linear
  signature: : Linear R D
  body: Linear.ofRingMorphism
  ((CatCenter.localizationRingHom L W).comp (Linear.toCatCenter R C))

中文:
定义 linear
  签名: : 线性 R D
  定义体: Linear.ofRingMorphism
  ((CatCenter.localizationRingHom L W).comp (Linear.toCatCenter R C))

Depends on / 依赖: Linear, Linear.ofRingMorphism, ofRingMorphism
-/
noncomputable def linear : Linear R D := Linear.ofRingMorphism
  ((CatCenter.localizationRingHom L W).comp (Linear.toCatCenter R C))

/--
lemma `functor_linear` / 引理 `functor_linear`

English:
lemma functor_linear
  proof: linear R L W
    Functor.Linear R L := by
  let := linear R L W
  constructor
  intro X Y f r
  change L.map (r • f) = ((Linear.toCatCenter R C r).localization L W).app (L.obj X) ≫ L.map f
  simp [← L.map_comp]

中文:
引理 functor_linear
  证明: linear R L W
    Functor.Linear R L := by
  let := linear R L W
  constructor
  intro X Y f r
  change L.map (r • f) = ((Linear.toCatCenter R C r).localization L W).app (L.obj X) ≫ L.map f
  simp [← L.map_comp]

Depends on / 依赖: linear
-/
lemma functor_linear :
    letI := linear R L W
    Functor.Linear R L := by
  let := linear R L W
  constructor
  intro X Y f r
  change L.map (r • f) = ((Linear.toCatCenter R C r).localization L W).app (L.obj X) ≫ L.map f
  simp [← L.map_comp]

section

variable [Preadditive W.Localization] [W.Q.Additive]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R W.Localization
  body: Localization.linear R W.Q W

中文:
实例 :
  签名: 线性 R W.Localization
  定义体: Localization.linear R W.Q W

Depends on / 依赖: Localization, Localization.linear, linear
-/
noncomputable instance : Linear R W.Localization := Localization.linear R W.Q W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Linear R W.Q
  body: Localization.functor_linear R W.Q W

中文:
实例 :
  签名: 函子.线性 R W.Q
  定义体: Localization.functor_linear R W.Q W

Depends on / 依赖: Localization, Localization.functor_linear, functor_linear
-/
noncomputable instance : Functor.Linear R W.Q := Localization.functor_linear R W.Q W

end

section

variable [W.HasLocalization] [Preadditive W.Localization'] [W.Q'.Additive]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R W.Localization'
  body: Localization.linear R W.Q' W

中文:
实例 :
  签名: 线性 R W.Localization'
  定义体: Localization.linear R W.Q' W

Depends on / 依赖: Localization, Localization.linear, linear
-/
noncomputable instance : Linear R W.Localization' := Localization.linear R W.Q' W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Linear R W.Q'
  body: Localization.functor_linear R W.Q' W

中文:
实例 :
  签名: 函子.线性 R W.Q'
  定义体: Localization.functor_linear R W.Q' W

Depends on / 依赖: Localization, Localization.functor_linear, functor_linear
-/
noncomputable instance : Functor.Linear R W.Q' := Localization.functor_linear R W.Q' W

end

section

variable {E : Type*} [Category* E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [Preadditive E]
  (R : Type*) [Ring R]
  [Linear R C] [Linear R D] [Linear R E] [L.Linear R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `functor_linear_iff` / 引理 `functor_linear_iff`

English:
lemma functor_linear_iff
  given: (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G]
  proof: by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso _ (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this]; rw 

中文:
引理 functor_linear_iff
  条件: (F : C ⥤ E) (G : D ⥤ E) [提升 L W F G]
  证明: by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso _ (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this]; rw 

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.comp_map, Functor.linear_iff, Functor.linear_of_iso, Functor.map_id, G.map_comp, L.map_id, L.map_smul, L.objObjPreimageIso, Lifting, Lifting.iso, Linear, Linear.comp_smul, Linear.smul_comp, Localization, Localization.essSurj, comp_map, comp_smul
-/
lemma functor_linear_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G] :
    F.Linear R ↔ G.Linear R := by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso _ (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this]; rw [G.map_comp]; rw [G.map_comp]; rw [← L.map_id]; rw [← L.map_smul]; rw [← Functor.comp_map]; rw [(L ⋙ G).map_smul]; rw [Functor.map_id]; rw [Linear.smul_comp]; rw [Linear.comp_smul]
    dsimp
    rw [Category.id_comp]; rw [← G.map_comp]; rw [e.inv_hom_id]; rw [G.map_id]
  · intro
    exact Functor.linear_of_iso _ (Lifting.iso L W F G)

end

end Localization

end CategoryTheory
