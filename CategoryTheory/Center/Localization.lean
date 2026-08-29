/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Localization of the center of a category

Given a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`,
we define a localization map `CatCenter C → CatCenter D` for the centers
of these categories. In case `L` is an additive functor between preadditive
categories, we promote this to a ring morphism `CatCenter C →+* CatCenter D`.

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (r s : CatCenter C) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace CatCenter

/--
Definition of `localization` / `localization` 的定义

English:
definition localization
  signature: : CatCenter D
  body: Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)

@[simp]

中文:
定义 localization
  签名: : CatCenter D
  定义体: Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, Localization, Localization.liftNatTrans, liftNatTrans, whiskerRight
-/
noncomputable def localization : CatCenter D :=
  Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)

@[simp]
/--
lemma `localization_app` / 引理 `localization_app`

English:
lemma localization_app
  given: (X : C)
  proof: by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, Functor.whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

include W

中文:
引理 localization_app
  条件: (X : C)
  证明: by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, Functor.whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

include W

Depends on / 依赖: Functor, Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.whiskerRight_app, Iso.hom_inv_id_app_assoc, Localization, Localization.liftNatTrans_app, NatTrans, NatTrans.naturality, comp_map, hom_inv_id_app_assoc, id_map, id_obj, liftNatTrans_app, localization, naturality, whiskerRight_app
-/
lemma localization_app (X : C) :
    (r.localization L W).app (L.obj X) = L.map (r.app X) := by
  dsimp [localization]
  simp only [Localization.liftNatTrans_app, Functor.id_obj, Functor.whiskerRight_app,
    NatTrans.naturality, Functor.comp_map, Functor.id_map, Iso.hom_inv_id_app_assoc]

include W

/--
lemma `ext_of_localization` / 引理 `ext_of_localization`

English:
lemma ext_of_localization
  statement: (r s : CatCenter D)
  proof: Localization.natTrans_ext L W h

中文:
引理 ext_of_localization
  结论: (r s : CatCenter D)
  证明: Localization.natTrans_ext L W h

Depends on / 依赖: Localization, Localization.natTrans_ext, natTrans_ext
-/
lemma ext_of_localization (r s : CatCenter D)
    (h : forall (X : C), r.app (L.obj X) = s.app (L.obj X)) : r = s :=
  Localization.natTrans_ext L W h

/--
lemma `localization_one` / 引理 `localization_one`

English:
lemma localization_one
  proof: ext_of_localization L W _ _ (fun X => by simp)

中文:
引理 localization_one
  证明: ext_of_localization L W _ _ (fun X => by simp)

Depends on / 依赖: ext_of_localization
-/
lemma localization_one :
    (1 : CatCenter C).localization L W = 1 :=
  ext_of_localization L W _ _ (fun X => by simp)

/--
lemma `localization_mul` / 引理 `localization_mul`

English:
lemma localization_mul
  proof: ext_of_localization L W _ _ (fun X => by simp)

中文:
引理 localization_mul
  证明: ext_of_localization L W _ _ (fun X => by simp)

Depends on / 依赖: ext_of_localization
-/
lemma localization_mul :
    (r * s).localization L W = r.localization L W * s.localization L W :=
  ext_of_localization L W _ _ (fun X => by simp)

section Preadditive

variable [Preadditive C] [Preadditive D] [L.Additive]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `localization_zero` / 引理 `localization_zero`

English:
lemma localization_zero
  proof: ext_of_localization L W _ _ (fun X => by simp)

中文:
引理 localization_zero
  证明: ext_of_localization L W _ _ (fun X => by simp)

Depends on / 依赖: ext_of_localization
-/
lemma localization_zero :
    (0 : CatCenter C).localization L W = 0 :=
  ext_of_localization L W _ _ (fun X => by simp)

/--
lemma `localization_add` / 引理 `localization_add`

English:
lemma localization_add
  proof: ext_of_localization L W _ _ (by simp)

中文:
引理 localization_add
  证明: ext_of_localization L W _ _ (by simp)

Depends on / 依赖: ext_of_localization
-/
lemma localization_add :
    (r + s).localization L W = r.localization L W + s.localization L W :=
  ext_of_localization L W _ _ (by simp)

/--
Definition of `localizationRingHom` / `localizationRingHom` 的定义

English:
definition localizationRingHom
  signature: : CatCenter C ->+* CatCenter D where
  body: r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

中文:
定义 localizationRingHom
  签名: : CatCenter C ->+* CatCenter D where
  定义体: r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

Depends on / 依赖: localization, r.localization
-/
noncomputable def localizationRingHom : CatCenter C ->+* CatCenter D where
  toFun r := r.localization L W
  map_zero' := localization_zero L W
  map_one' := localization_one L W
  map_add' _ _ := localization_add _ _ _ _
  map_mul' _ _ := localization_mul _ _ _ _

end Preadditive

end CatCenter

end CategoryTheory
