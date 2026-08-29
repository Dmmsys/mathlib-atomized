/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# (Co)limits on the (strict) Grothendieck Construction

* Shows that if a functor `G : Grothendieck F ⥤ H`, with `F : C ⥤ Cat`, has a colimit, and every
  fiber of `G` has a colimit, then so does the fiberwise colimit functor `C ⥤ H`.
* Vice versa, if each fiber of `G` has a colimit and the fiberwise colimit functor has a colimit,
  then `G` has a colimit.
* Shows that colimits of functors on the Grothendieck construction are colimits of
  "fibered colimits", i.e. of applying the colimit to each fiber of the functor.
* Derives `HasColimitsOfShape (Grothendieck F) H` with `F : C ⥤ Cat` from the presence of colimits
  on each fiber shape `F.obj X` and on the base category `C`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open CategoryTheory.Functor

namespace Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {F : C ⥤ Cat}
variable {H : Type u₂} [Category.{v₂} H]
variable (G : Grothendieck F ⥤ H)


noncomputable section

variable [forall {X Y : C} (f : X ⟶ Y), HasColimit ((F.map f).toFunctor ⋙ Grothendieck.ι F Y ⋙ G)]

@[local instance]
/--
lemma `hasColimit_ι_comp` / 引理 `hasColimit_ι_comp`

English:
lemma hasColimit_ι_comp
  statement: forall X, HasColimit (Grothendieck.ι F X ⋙ G)
  proof: fun X => hasColimit_of_iso (F := (F.map (𝟙 _)).toFunctor ⋙ Grothendieck.ι F X ⋙ G)
    (leftUnitor (Grothendieck.ι F X ⋙ G)).symm ≪≫
    (isoWhiskerRight (eqToIso congr($((F.map_id X).symm).toFunctor)) (Grothendieck.ι F X ⋙ G))

中文:
引理 hasColimit_ι_comp
  结论: 对任意 X, 有余极限 (Grothendieck.ι F X ⋙ G)
  证明: fun X => hasColimit_of_iso (F := (F.map (𝟙 _)).toFunctor ⋙ Grothendieck.ι F X ⋙ G)
    (leftUnitor (Grothendieck.ι F X ⋙ G)).symm ≪≫
    (isoWhiskerRight (eqToIso congr($((F.map_id X).symm).toFunctor)) (Grothendieck.ι F X ⋙ G))

Depends on / 依赖: F.map, F.map_id, Grothendieck, eqToIso, hasColimit_of_iso, isoWhiskerRight, leftUnitor, map_id, toFunctor
-/
lemma hasColimit_ι_comp : forall X, HasColimit (Grothendieck.ι F X ⋙ G) :=
fun X => hasColimit_of_iso (F := (F.map (𝟙 _)).toFunctor ⋙ Grothendieck.ι F X ⋙ G)
    (leftUnitor (Grothendieck.ι F X ⋙ G)).symm ≪≫
    (isoWhiskerRight (eqToIso congr($((F.map_id X).symm).toFunctor)) (Grothendieck.ι F X ⋙ G))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A functor taking a colimit on each fiber of a functor `G : Grothendieck F ⥤ H`. -/
@[simps]
/--
Definition of `fiberwiseColimit` / `fiberwiseColimit` 的定义

English:
definition fiberwiseColimit
  signature: : C ⥤ H where
  body: colimit (Grothendieck.ι F X ⋙ G)
  map {X Y} f := colimMap (whiskerRight (Grothendieck.ιNatTrans f) G ≫
    (associator _ _ _).hom) ≫ colimit.pre (Grothendieck.ι F Y ⋙ G) (F.map f).toFunctor
  map_id X := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj, ι_colimMap_assoc,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F X ⋙ G)
      (j := (F.map (𝟙 X)).toFunctor.obj d) (by simp)]
    rw [← eqToHom_map G (by simp)]; rw [Grothendieck.eqToHom_eq]
    rfl
  map_comp {X Y Z} f g := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, ι_colimMap_assoc, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, Category.comp_id, colimit.ι_pre, Category.assoc,
      colimit.ι_pre_assoc]
    rw [← Category.assoc]; rw [← G.map_comp]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F Z ⋙ G)
      (j := (F.map (f ≫ g)).toFunctor.obj d) (by simp)]
    rw [← Category.assoc]; rw [← eqToHom_map G (by simp)]; rw [← G.map_comp]; rw [Grothendieck.eqToHom_eq]
    congr 2
    fapply Grothendieck.ext
    · simp only [eqToHom_refl, Category.assoc, Grothendieck.comp_base,
        Category.comp_id]
    · simp only [Grothendieck.ι_obj, eqToHom_refl,
        Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber, Functor.map_id]
      conv_rhs => enter [2, 1]; rw [eqToHom_map (F.map (𝟙 Z)).toFunctor]
      conv_rhs => rw [eqToHom_trans, eqToHom_trans]

中文:
定义 fiberwiseColimit
  签名: : C ⥤ H where
  定义体: colimit (Grothendieck.ι F X ⋙ G)
  map {X Y} f := colimMap (whiskerRight (Grothendieck.ιNatTrans f) G ≫
    (associator _ _ _).hom) ≫ colimit.pre (Grothendieck.ι F Y ⋙ G) (F.map f).toFunctor
  map_id X := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj, ι_colimMap_assoc,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F X ⋙ G)
      (j := (F.map (𝟙 X)).toFunctor.obj d) (by simp)]
    rw [← eqToHom_map G (by simp)]; rw [Grothendieck.eqToHom_eq]
    rfl
  map_comp {X Y Z} f g := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, ι_colimMap_assoc, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, Category.comp_id, colimit.ι_pre, Category.assoc,
      colimit.ι_pre_assoc]
    rw [← Category.assoc]; rw [← G.map_comp]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F Z ⋙ G)
      (j := (F.map (f ≫ g)).toFunctor.obj d) (by simp)]
    rw [← Category.assoc]; rw [← eqToHom_map G (by simp)]; rw [← G.map_comp]; rw [Grothendieck.eqToHom_eq]
    congr 2
    fapply Grothendieck.ext
    · simp only [eqToHom_refl, Category.assoc, Grothendieck.comp_base,
        Category.comp_id]
    · simp only [Grothendieck.ι_obj, eqToHom_refl,
        Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber, Functor.map_id]
      conv_rhs => enter [2, 1]; rw [eqToHom_map (F.map (𝟙 Z)).toFunctor]
      conv_rhs => rw [eqToHom_trans, eqToHom_trans]

Depends on / 依赖: Grothendieck, colimit
-/
def fiberwiseColimit : C ⥤ H where
  obj X := colimit (Grothendieck.ι F X ⋙ G)
  map {X Y} f := colimMap (whiskerRight (Grothendieck.ιNatTrans f) G ≫
    (associator _ _ _).hom) ≫ colimit.pre (Grothendieck.ι F Y ⋙ G) (F.map f).toFunctor
  map_id X := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, Grothendieck.ι_obj, ι_colimMap_assoc,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F X ⋙ G)
      (j := (F.map (𝟙 X)).toFunctor.obj d) (by simp)]
    rw [← eqToHom_map G (by simp)]; rw [Grothendieck.eqToHom_eq]
    rfl
  map_comp {X Y Z} f g := by
    ext d
    simp only [Functor.comp_obj, Grothendieck.ιNatTrans, ι_colimMap_assoc, NatTrans.comp_app,
      whiskerRight_app, Functor.associator_hom_app, Category.comp_id, colimit.ι_pre, Category.assoc,
      colimit.ι_pre_assoc]
    rw [← Category.assoc]; rw [← G.map_comp]
    conv_rhs => rw [← colimit.eqToHom_comp_ι (Grothendieck.ι F Z ⋙ G)
      (j := (F.map (f ≫ g)).toFunctor.obj d) (by simp)]
    rw [← Category.assoc]; rw [← eqToHom_map G (by simp)]; rw [← G.map_comp]; rw [Grothendieck.eqToHom_eq]
    congr 2
    fapply Grothendieck.ext
    · simp only [eqToHom_refl, Category.assoc, Grothendieck.comp_base,
        Category.comp_id]
    · simp only [Grothendieck.ι_obj, eqToHom_refl,
        Grothendieck.comp_base, Category.comp_id, Grothendieck.comp_fiber, Functor.map_id]
      conv_rhs => enter [2, 1]; rw [eqToHom_map (F.map (𝟙 Z)).toFunctor]
      conv_rhs => rw [eqToHom_trans, eqToHom_trans]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: find a good way to fix the linter; simp cannot be combined with the subsequent apply
set_option linter.flexible false in
variable (H) (F) in
/-- Similar to `colimit` and `colim`, taking fiberwise colimits is a functor
`(Grothendieck F ⥤ H) ⥤ (C ⥤ H)` between functor categories. -/
@[simps]
/--
Definition of `fiberwiseColim` / `fiberwiseColim` 的定义

English:
definition fiberwiseColim
  signature: [forall c, HasColimitsOfShape (F.obj c) H]
  body: fiberwiseColimit G
  map α :=
    { app := fun c => colim.map (whiskerLeft _ α)
      naturality := fun c₁ c₂ f => by apply colimit.hom_ext; simp }
  map_id G := by ext; simp; apply Functor.map_id colim
  map_comp α β := by ext; simp; apply Functor.map_comp colim

中文:
定义 fiberwiseColim
  签名: [对任意 c, 有形状余极限 (F.obj c) H]
  定义体: fiberwiseColimit G
  map α :=
    { app := fun c => colim.map (whiskerLeft _ α)
      naturality := fun c₁ c₂ f => by apply colimit.hom_ext; simp }
  map_id G := by ext; simp; apply Functor.map_id colim
  map_comp α β := by ext; simp; apply Functor.map_comp colim

Depends on / 依赖: fiberwiseColimit
-/
def fiberwiseColim [forall c, HasColimitsOfShape (F.obj c) H] : (Grothendieck F ⥤ H) ⥤ (C ⥤ H) where
  obj G := fiberwiseColimit G
  map α :=
    { app := fun c => colim.map (whiskerLeft _ α)
      naturality := fun c₁ c₂ f => by apply colimit.hom_ext; simp }
  map_id G := by ext; simp; apply Functor.map_id colim
  map_comp α β := by ext; simp; apply Functor.map_comp colim

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every functor `G : Grothendieck F ⥤ H` induces a natural transformation from `G` to the
composition of the forgetful functor on `Grothendieck F` with the fiberwise colimit on `G`. -/
@[simps]
/--
Definition of `natTransIntoForgetCompFiberwiseColimit` / `natTransIntoForgetCompFiberwiseColimit` 的定义

English:
definition natTransIntoForgetCompFiberwiseColimit
  signature: :
  body: colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber
  naturality _ _ f := by
    simp only [Functor.comp_obj, Grothendieck.forget_obj, fiberwiseColimit_obj, Functor.comp_map,
      Grothendieck.forget_map, fiberwiseColimit_map, ι_colimMap_assoc, Grothendieck.ι_obj,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    rw [← colimit.w (Grothendieck.ι F _ ⋙ G) f.fiber]
    simp only [← Category.assoc, Functor.comp_obj, Functor.comp_map, ← G.map_comp]
    congr 2
    apply Grothendieck.ext <;> simp

中文:
定义 natTrans整数oForgetCompFiberwiseColimit
  签名: :
  定义体: colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber
  naturality _ _ f := by
    simp only [Functor.comp_obj, Grothendieck.forget_obj, fiberwiseColimit_obj, Functor.comp_map,
      Grothendieck.forget_map, fiberwiseColimit_map, ι_colimMap_assoc, Grothendieck.ι_obj,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    rw [← colimit.w (Grothendieck.ι F _ ⋙ G) f.fiber]
    simp only [← Category.assoc, Functor.comp_obj, Functor.comp_map, ← G.map_comp]
    congr 2
    apply Grothendieck.ext <;> simp

Depends on / 依赖: Grothendieck, X.base, X.fiber, colimit
-/
def natTransIntoForgetCompFiberwiseColimit :
    G ⟶ Grothendieck.forget F ⋙ fiberwiseColimit G where
  app X := colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber
  naturality _ _ f := by
    simp only [Functor.comp_obj, Grothendieck.forget_obj, fiberwiseColimit_obj, Functor.comp_map,
      Grothendieck.forget_map, fiberwiseColimit_map, ι_colimMap_assoc, Grothendieck.ι_obj,
      NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, Category.comp_id,
      colimit.ι_pre]
    rw [← colimit.w (Grothendieck.ι F _ ⋙ G) f.fiber]
    simp only [← Category.assoc, Functor.comp_obj, Functor.comp_map, ← G.map_comp]
    congr 2
    apply Grothendieck.ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {G} in
/-- A cocone on a functor `G : Grothendieck F ⥤ H` induces a cocone on the fiberwise colimit
on `G`. -/
@[simps]
/--
Definition of `coconeFiberwiseColimitOfCocone` / `coconeFiberwiseColimitOfCocone` 的定义

English:
definition coconeFiberwiseColimitOfCocone
  signature: (c : Cocone G)
  body: c.pt
  ι := { app := fun X => colimit.desc _ (c.whisker (Grothendieck.ι F X)),
         naturality := fun _ _ f => by dsimp; ext; simp }

中文:
定义 coconeFiberwiseColimitOfCocone
  签名: (c : 余锥 G)
  定义体: c.pt
  ι := { app := fun X => colimit.desc _ (c.whisker (Grothendieck.ι F X)),
         naturality := fun _ _ f => by dsimp; ext; simp }

Depends on / 依赖: c.pt
-/
def coconeFiberwiseColimitOfCocone (c : Cocone G) : Cocone (fiberwiseColimit G) where
  pt := c.pt
  ι := { app := fun X => colimit.desc _ (c.whisker (Grothendieck.ι F X)),
         naturality := fun _ _ f => by dsimp; ext; simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {G} in
/--
Definition of `isColimitCoconeFiberwiseColimitOfCocone` / `isColimitCoconeFiberwiseColimitOfCocone` 的定义

English:
definition isColimitCoconeFiberwiseColimitOfCocone
  signature: {c : Cocone G} (hc : IsColimit c)
  body: hc.desc Cocone.mk s.pt natTransIntoForgetCompFiberwiseColimit G ≫
    whiskerLeft (Grothendieck.forget F) s.ι
  fac s c := by dsimp; ext; simp
  uniq s m hm := hc.hom_ext fun X => by
    have := hm X.base
    simp only [Functor.const_obj_obj, IsColimit.fac, NatTrans.comp_app, Functor.comp_obj,
      Grothendieck.forget_obj, natTransIntoForgetCompFiberwiseColimit_app,
      whiskerLeft_app]
    simp only [coconeFiberwiseColimitOfCocone_pt, coconeFiberwiseColimitOfCocone_ι_app] at this
    simp [← this]

中文:
定义 isColimitCoconeFiberwiseColimitOfCocone
  签名: {c : 余锥 G} (hc : 是余极限 c)
  定义体: hc.desc Cocone.mk s.pt natTransIntoForgetCompFiberwiseColimit G ≫
    whiskerLeft (Grothendieck.forget F) s.ι
  fac s c := by dsimp; ext; simp
  uniq s m hm := hc.hom_ext fun X => by
    have := hm X.base
    simp only [Functor.const_obj_obj, IsColimit.fac, NatTrans.comp_app, Functor.comp_obj,
      Grothendieck.forget_obj, natTransIntoForgetCompFiberwiseColimit_app,
      whiskerLeft_app]
    simp only [coconeFiberwiseColimitOfCocone_pt, coconeFiberwiseColimitOfCocone_ι_app] at this
    simp [← this]

Depends on / 依赖: Cocone, Cocone.mk, hc.desc, natTransIntoForgetCompFiberwiseColimit, s.pt
-/
def isColimitCoconeFiberwiseColimitOfCocone {c : Cocone G} (hc : IsColimit c) :
    IsColimit (coconeFiberwiseColimitOfCocone c) where
desc s := hc.desc Cocone.mk s.pt natTransIntoForgetCompFiberwiseColimit G ≫
    whiskerLeft (Grothendieck.forget F) s.ι
  fac s c := by dsimp; ext; simp
  uniq s m hm := hc.hom_ext fun X => by
    have := hm X.base
    simp only [Functor.const_obj_obj, IsColimit.fac, NatTrans.comp_app, Functor.comp_obj,
      Grothendieck.forget_obj, natTransIntoForgetCompFiberwiseColimit_app,
      whiskerLeft_app]
    simp only [coconeFiberwiseColimitOfCocone_pt, coconeFiberwiseColimitOfCocone_ι_app] at this
    simp [← this]

/--
lemma `hasColimit_fiberwiseColimit` / 引理 `hasColimit_fiberwiseColimit`

English:
lemma hasColimit_fiberwiseColimit
  given: [HasColimit G]
  statement: HasColimit (fiberwiseColimit G) where
  proof: ⟨⟨_, isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _)⟩⟩

中文:
引理 hasColimit_fiberwiseColimit
  条件: [有余极限 G]
  结论: 有余极限 (fiberwiseColimit G) where
  证明: ⟨⟨_, isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _)⟩⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitCoconeFiberwiseColimitOfCocone
-/
lemma hasColimit_fiberwiseColimit [HasColimit G] : HasColimit (fiberwiseColimit G) where
  exists_colimit := ⟨⟨_, isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _)⟩⟩

variable {G}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a functor `G : Grothendieck F ⥤ H`, every cocone over `fiberwiseColimit G` induces a
cocone over `G` itself. -/
@[simps]
/--
Definition of `coconeOfCoconeFiberwiseColimit` / `coconeOfCoconeFiberwiseColimit` 的定义

English:
definition coconeOfCoconeFiberwiseColimit
  signature: (c : Cocone (fiberwiseColimit G))
  body: c.pt
  ι := { app := fun X => colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫ c.ι.app X.base
         naturality := fun {X Y} ⟨f, g⟩ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc]; rw [← c.w f]; rw [← Category.assoc]
          simp only [fiberwiseColimit_obj, fiberwiseColimit_map, ι_colimMap_assoc,
            Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app, whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
          rw [← colimit.w _ g]; rw [← Category.assoc]; rw [Functor.comp_map]; rw [← G.map_comp]
          congr <;> simp }

中文:
定义 coconeOfCoconeFiberwiseColimit
  签名: (c : 余锥 (fiberwiseColimit G))
  定义体: c.pt
  ι := { app := fun X => colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫ c.ι.app X.base
         naturality := fun {X Y} ⟨f, g⟩ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc]; rw [← c.w f]; rw [← Category.assoc]
          simp only [fiberwiseColimit_obj, fiberwiseColimit_map, ι_colimMap_assoc,
            Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app, whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
          rw [← colimit.w _ g]; rw [← Category.assoc]; rw [Functor.comp_map]; rw [← G.map_comp]
          congr <;> simp }

Depends on / 依赖: c.pt
-/
def coconeOfCoconeFiberwiseColimit (c : Cocone (fiberwiseColimit G)) : Cocone G where
  pt := c.pt
  ι := { app := fun X => colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫ c.ι.app X.base
         naturality := fun {X Y} ⟨f, g⟩ => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc]; rw [← c.w f]; rw [← Category.assoc]
          simp only [fiberwiseColimit_obj, fiberwiseColimit_map, ι_colimMap_assoc,
            Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app, whiskerRight_app,
            Functor.associator_hom_app, Category.comp_id, colimit.ι_pre]
          rw [← colimit.w _ g]; rw [← Category.assoc]; rw [Functor.comp_map]; rw [← G.map_comp]
          congr <;> simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCoconeOfFiberwiseCocone` / `isColimitCoconeOfFiberwiseCocone` 的定义

English:
definition isColimitCoconeOfFiberwiseCocone
  signature: {c : Cocone (fiberwiseColimit G)} (hc : IsColimit c)
  body: hc.desc Cocone.mk s.pt
    { app := fun X => colimit.desc (Grothendieck.ι F X ⋙ G) (s.whisker _) }
uniq s m hm := hc.hom_ext fun X => by
    simp only [fiberwiseColimit_obj, IsColimit.fac]
    simp only [coconeOfCoconeFiberwiseColimit_pt, Functor.const_obj_obj,
      coconeOfCoconeFiberwiseColimit_ι_app, Category.assoc] at hm
    ext d
    simp [hm ⟨X, d⟩]

中文:
定义 isColimitCoconeOfFiberwiseCocone
  签名: {c : 余锥 (fiberwiseColimit G)} (hc : 是余极限 c)
  定义体: hc.desc Cocone.mk s.pt
    { app := fun X => colimit.desc (Grothendieck.ι F X ⋙ G) (s.whisker _) }
uniq s m hm := hc.hom_ext fun X => by
    simp only [fiberwiseColimit_obj, IsColimit.fac]
    simp only [coconeOfCoconeFiberwiseColimit_pt, Functor.const_obj_obj,
      coconeOfCoconeFiberwiseColimit_ι_app, Category.assoc] at hm
    ext d
    simp [hm ⟨X, d⟩]

Depends on / 依赖: Cocone, Cocone.mk, hc.desc, s.pt
-/
def isColimitCoconeOfFiberwiseCocone {c : Cocone (fiberwiseColimit G)} (hc : IsColimit c) :
    IsColimit (coconeOfCoconeFiberwiseColimit c) where
desc s := hc.desc Cocone.mk s.pt
    { app := fun X => colimit.desc (Grothendieck.ι F X ⋙ G) (s.whisker _) }
uniq s m hm := hc.hom_ext fun X => by
    simp only [fiberwiseColimit_obj, IsColimit.fac]
    simp only [coconeOfCoconeFiberwiseColimit_pt, Functor.const_obj_obj,
      coconeOfCoconeFiberwiseColimit_ι_app, Category.assoc] at hm
    ext d
    simp [hm ⟨X, d⟩]

variable [HasColimit (fiberwiseColimit G)]

variable (G)

/-- We can infer that a functor `G : Grothendieck F ⥤ H`, with `F : C ⥤ Cat`, has a colimit from
the fact that each of its fibers has a colimit and that these fiberwise colimits, as a functor
`C ⥤ H` have a colimit. -/
@[local instance]
/--
lemma `hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit` / 引理 `hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit`

English:
lemma hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit
  statement: HasColimit G where
  proof: ⟨⟨_, isColimitCoconeOfFiberwiseCocone (colimit.isColimit _)⟩⟩

中文:
引理 hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit
  结论: 有余极限 G where
  证明: ⟨⟨_, isColimitCoconeOfFiberwiseCocone (colimit.isColimit _)⟩⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitCoconeOfFiberwiseCocone
-/
lemma hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit : HasColimit G where
  exists_colimit := ⟨⟨_, isColimitCoconeOfFiberwiseCocone (colimit.isColimit _)⟩⟩

/--
Definition of `colimitFiberwiseColimitIso` / `colimitFiberwiseColimitIso` 的定义

English:
definition colimitFiberwiseColimitIso
  signature: : colimit (fiberwiseColimit G) ≅ colimit G
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit (fiberwiseColimit G))
    (isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _))

中文:
定义 colimitFiberwiseColimitIso
  签名: : colimit (fiberwiseColimit G) ≅ colimit G
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit (fiberwiseColimit G))
    (isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _))

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, fiberwiseColimit, isColimit, isColimitCoconeFiberwiseColimitOfCocone
-/
def colimitFiberwiseColimitIso : colimit (fiberwiseColimit G) ≅ colimit G :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (fiberwiseColimit G))
    (isColimitCoconeFiberwiseColimitOfCocone (colimit.isColimit _))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitFiberwiseColimitIso_hom` / 引理 `ι_colimitFiberwiseColimitIso_hom`

English:
lemma ι_colimitFiberwiseColimitIso_hom
  given: (X : C) (d : F.obj X)
  proof: by
  simp [colimitFiberwiseColimitIso]

中文:
引理 ι_colimitFiberwiseColimitIso_hom
  条件: (X : C) (d : F.obj X)
  证明: by
  simp [colimitFiberwiseColimitIso]

Depends on / 依赖: colimitFiberwiseColimitIso
-/
lemma ι_colimitFiberwiseColimitIso_hom (X : C) (d : F.obj X) :
    colimit.ι (Grothendieck.ι F X ⋙ G) d ≫ colimit.ι (fiberwiseColimit G) X ≫
      (colimitFiberwiseColimitIso G).hom = colimit.ι G ⟨X, d⟩ := by
  simp [colimitFiberwiseColimitIso]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitFiberwiseColimitIso_inv` / 引理 `ι_colimitFiberwiseColimitIso_inv`

English:
lemma ι_colimitFiberwiseColimitIso_inv
  given: (X : Grothendieck F)
  proof: by
  rw [Iso.comp_inv_eq]
  simp

中文:
引理 ι_colimitFiberwiseColimitIso_inv
  条件: (X : Grothendieck F)
  证明: by
  rw [Iso.comp_inv_eq]
  simp

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma ι_colimitFiberwiseColimitIso_inv (X : Grothendieck F) :
    colimit.ι G X ≫ (colimitFiberwiseColimitIso G).inv =
    colimit.ι (Grothendieck.ι F X.base ⋙ G) X.fiber ≫
      colimit.ι (fiberwiseColimit G) X.base := by
  rw [Iso.comp_inv_eq]
  simp

end

@[instance]
/--
theorem `hasColimitsOfShape_grothendieck` / 定理 `hasColimitsOfShape_grothendieck`

English:
theorem hasColimitsOfShape_grothendieck
  statement: [forall X, HasColimitsOfShape (F.obj X) H]
  proof: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

noncomputable section FiberwiseColim

中文:
定理 hasColimitsOfShape_grothendieck
  结论: [对任意 X, 有形状余极限 (F.obj X) H]
  证明: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

noncomputable section FiberwiseColim

Depends on / 依赖: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit
-/
theorem hasColimitsOfShape_grothendieck [forall X, HasColimitsOfShape (F.obj X) H]
    [HasColimitsOfShape C H] : HasColimitsOfShape (Grothendieck F) H where
  has_colimit _ := hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

noncomputable section FiberwiseColim

variable [forall (c : C), HasColimitsOfShape (↑(F.obj c)) H] [HasColimitsOfShape C H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `colimitFiberwiseColimitIso` induces an isomorphism of functors `(J ⥤ C) ⥤ C`
between `fiberwiseColim F H ⋙ colim` and `colim`. -/
@[simps!]
/--
Definition of `fiberwiseColimCompColimIso` / `fiberwiseColimCompColimIso` 的定义

English:
definition fiberwiseColimCompColimIso
  signature: : fiberwiseColim F H ⋙ colim ≅ colim
  body: NatIso.ofComponents (fun G => colimitFiberwiseColimitIso G)
    fun _ => by (iterate 2 apply colimit.hom_ext; intro); simp

中文:
定义 fiberwiseColimCompColimIso
  签名: : fiberwiseColim F H ⋙ colim ≅ colim
  定义体: NatIso.ofComponents (fun G => colimitFiberwiseColimitIso G)
    fun _ => by (iterate 2 apply colimit.hom_ext; intro); simp

Depends on / 依赖: NatIso, NatIso.ofComponents, colimit, colimit.hom_ext, colimitFiberwiseColimitIso, hom_ext, iterate, ofComponents
-/
def fiberwiseColimCompColimIso : fiberwiseColim F H ⋙ colim ≅ colim :=
  NatIso.ofComponents (fun G => colimitFiberwiseColimitIso G)
    fun _ => by (iterate 2 apply colimit.hom_ext; intro); simp

/-- Composing `fiberwiseColim F H` with the evaluation functor `(evaluation C H).obj c` is
naturally isomorphic to precomposing the Grothendieck inclusion `Grothendieck.ι` to `colim`. -/
@[simps!]
/--
Definition of `fiberwiseColimCompEvaluationIso` / `fiberwiseColimCompEvaluationIso` 的定义

English:
definition fiberwiseColimCompEvaluationIso
  signature: (c : C)
  body: Iso.refl _

中文:
定义 fiberwiseColimCompEvaluationIso
  签名: (c : C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def fiberwiseColimCompEvaluationIso (c : C) :
    fiberwiseColim F H ⋙ (evaluation C H).obj c ≅
      (whiskeringLeft _ _ _).obj (Grothendieck.ι F c) ⋙ colim :=
  Iso.refl _

end FiberwiseColim

end Limits

end CategoryTheory
