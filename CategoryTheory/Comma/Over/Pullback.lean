/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Monad.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Adjunctions related to the over category

In a category with pullbacks, for any morphism `f : X ⟶ Y`, the functor
`Over.map f : Over X ⥤ Over Y` has a right adjoint `Over.pullback f`.

In a category with binary products, for any object `X` the functor
`Over.forget X : Over X ⥤ C` has a right adjoint `Over.star X`.

## Main declarations

- `Over.pullback f : Over Y ⥤ Over X` is the functor induced by a morphism `f : X ⟶ Y`.
- `Over.mapPullbackAdj` is the adjunction `Over.map f ⊣ Over.pullback f`.
- `star : C ⥤ Over X` is the functor induced by an object `X`.
- `forgetAdjStar` is the adjunction `forget X ⊣ star X`.

## TODO
Show `star X` itself has a right adjoint provided `C` is Cartesian closed and has pullbacks.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X Y : C)
variable {D : Type u₂} [Category.{v₂} D]


namespace Over

open Limits

attribute [local instance] hasPullback_of_right_iso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤ Over X`,
by pulling back a morphism along `f`. -/
@[simps! +simpRhs obj_left obj_hom map_left, implicit_reducible]
/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
  body: Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

中文:
定义 pullback
  签名: {X Y : C} (f : X ⟶ Y) [有PullbacksAlong f]
  定义体: Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

Depends on / 依赖: Over.mk, g.hom, pullback, pullback.snd
-/
def pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
/--
Definition of `mapPullbackAdj` / `mapPullbackAdj` 的定义

English:
definition mapPullbackAdj
  signature: {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) by
            simp [← Over.w v, pullback.condition]
          left_inv := by cat_disch
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

中文:
定义 mapPullbackAdj
  签名: {X Y : C} (f : X ⟶ Y) [有PullbacksAlong f]
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) by
            simp [← Over.w v, pullback.condition]
          left_inv := by cat_disch
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Over.homMk, Over.w, cat_disch, condition, homEquiv, invFun, left_inv, mkOfHomEquiv, pullback, pullback.condition, pullback.fst, pullback.lift, right_inv, u.left, v.left, x.hom
-/
def mapPullbackAdj {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) by
            simp [← Over.w v, pullback.condition]
          left_inv := by cat_disch
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : (Over.map f).IsLeftAdjoint :=
  (Over.mapPullbackAdj f).isLeftAdjoint

instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] : (Over.pullback f).IsRightAdjoint :=
  (Over.mapPullbackAdj f).isRightAdjoint

set_option backward.isDefEq.respectTransparency false in
/--
Instance `faithful_pullback` / 实例 `faithful_pullback`

English:
instance faithful_pullback
  signature: {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
  body: by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by
    simp only [Functor.comp_obj, Functor.id_obj, mapPullbackAdj_counit_app]; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

中文:
实例 faithful_pullback
  签名: {X Y : C} (f : X ⟶ Y) [有PullbacksAlong f]
  定义体: by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by
    simp only [Functor.comp_obj, Functor.id_obj, mapPullbackAdj_counit_app]; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

Depends on / 依赖: Functor, Functor.comp_obj, Functor.id_obj, comp_obj, counit, counit.app, faithful_R_of_epi_counit_app, id_obj, infer_instance, mapPullbackAdj, mapPullbackAdj_counit_app
-/
instance faithful_pullback {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [forall Z (g : Z ⟶ Y), Epi (pullback.fst g f)] : (pullback f).Faithful := by
  have (Z : Over Y) : Epi ((mapPullbackAdj f).counit.app Z) := by
    simp only [Functor.comp_obj, Functor.id_obj, mapPullbackAdj_counit_app]; infer_instance
  exact (mapPullbackAdj f).faithful_R_of_epi_counit_app

/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: {X : C}
  body: conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

中文:
定义 pullbackId
  签名: {X : C}
  定义体: conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

Depends on / 依赖: Adjunction, Adjunction.id, Over.mapId, conjugateIsoEquiv, mapPullbackAdj
-/
def pullbackId {X : C} : pullback (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g]
  body: conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

中文:
定义 pullbackComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [有PullbacksAlong f] [有PullbacksAlong g]
  定义体: conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

Depends on / 依赖: Over.mapComp, conjugateIsoEquiv, mapComp, mapPullbackAdj
-/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullbacksAlong f] [HasPullbacksAlong g] :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

/--
Instance `pullbackIsRightAdjoint` / 实例 `pullbackIsRightAdjoint`

English:
instance pullbackIsRightAdjoint
  signature: {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
  body: ⟨_, ⟨mapPullbackAdj f⟩⟩

中文:
实例 pullbackIsRightAdjoint
  签名: {X Y : C} (f : X ⟶ Y) [有PullbacksAlong f]
  定义体: ⟨_, ⟨mapPullbackAdj f⟩⟩

Depends on / 依赖: mapPullbackAdj
-/
instance pullbackIsRightAdjoint {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    (pullback f).IsRightAdjoint :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open pullback in
/-- If `F` is a left adjoint and its source category has pullbacks, then so is
`post F : Over Y ⥤ Over (G Y)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(Y ⟶ F X) ↦ (G Y ⟶ X ×_{G F X} G Y ⟶ X)`. -/
@[simps!]
/--
Definition of `postAdjunctionLeft` / `postAdjunctionLeft` 的定义

English:
definition postAdjunctionLeft
  signature: [HasPullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
  body: ((mapPullbackAdj (a.unit.app X)).comp (postAdjunctionRight a)).ofNatIsoLeft
    NatIso.ofComponents fun Y => isoMk (.refl _)

中文:
定义 postAdjunctionLeft
  签名: [有Pullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
  定义体: ((mapPullbackAdj (a.unit.app X)).comp (postAdjunctionRight a)).ofNatIsoLeft
    NatIso.ofComponents fun Y => isoMk (.refl _)

Depends on / 依赖: NatIso, NatIso.ofComponents, a.unit.app, mapPullbackAdj, ofComponents, ofNatIsoLeft, postAdjunctionRight
-/
def postAdjunctionLeft [HasPullbacks C] {X : C} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⊣ post G ⋙ pullback (a.unit.app X) :=
((mapPullbackAdj (a.unit.app X)).comp (postAdjunctionRight a)).ofNatIsoLeft
    NatIso.ofComponents fun Y => isoMk (.refl _)

/--
Instance `isLeftAdjoint_post` / 实例 `isLeftAdjoint_post`

English:
instance isLeftAdjoint_post
  signature: [HasPullbacks C] {F : C ⥤ D} [F.IsLeftAdjoint]
  body: let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

中文:
实例 isLeftAdjoint_post
  签名: [有Pullbacks C] {F : C ⥤ D} [F.是左伴随]
  定义体: let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

Depends on / 依赖: IsLeftAdjoint
-/
instance isLeftAdjoint_post [HasPullbacks C] {F : C ⥤ D} [F.IsLeftAdjoint] :
    (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

open Limits

set_option backward.defeqAttrib.useBackward true in
/-- The category over any object `X` factors through the category over the terminal object `T`. -/
@[simps!]
/--
Definition of `forgetMapTerminal` / `forgetMapTerminal` 的定义

English:
definition forgetMapTerminal
  signature: {T : C} (hT : IsTerminal T)
  body: NatIso.ofComponents fun X => .refl _

中文:
定义 forgetMapTerminal
  签名: {T : C} (hT : 是终止 T)
  定义体: NatIso.ofComponents fun X => .refl _

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def forgetMapTerminal {T : C} (hT : IsTerminal T) :
    forget X ≅ map (hT.from X) ⋙ (equivalenceOfIsTerminal hT).functor :=
  NatIso.ofComponents fun X => .refl _

section HasBinaryProducts
variable [HasBinaryProducts C]

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
/--
Definition of `star` / `star` 的定义

English:
definition star
  signature: : C ⥤ Over X
  body: cofree _ ⋙ coalgebraToOver X

中文:
定义 star
  签名: : C ⥤ Over X
  定义体: cofree _ ⋙ coalgebraToOver X

Depends on / 依赖: coalgebraToOver, cofree
-/
def star : C ⥤ Over X := cofree _ ⋙ coalgebraToOver X

/--
Definition of `forgetAdjStar` / `forgetAdjStar` 的定义

English:
definition forgetAdjStar
  signature: : forget X ⊣ star X
  body: (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

中文:
定义 forgetAdjStar
  签名: : forget X ⊣ star X
  定义体: (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

Depends on / 依赖: coalgebraEquivOver, symm.toAdjunction.comp, toAdjunction
-/
def forgetAdjStar : forget X ⊣ star X := (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `forgetAdjStar_counit_app` / 引理 `forgetAdjStar_counit_app`

English:
lemma forgetAdjStar_counit_app
  given: (X Y : C)
  statement: (Over.forgetAdjStar X).counit.app Y = prod.snd
  proof: by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

中文:
引理 forgetAdjStar_counit_app
  条件: (X Y : C)
  结论: (Over.forgetAdjStar X).counit.app Y = 乘积.snd
  证明: by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

Depends on / 依赖: CategoryTheory, CategoryTheory.coalgebraEquivOver, Over.forgetAdjStar, coalgebraEquivOver, forgetAdjStar
-/
lemma forgetAdjStar_counit_app (X Y : C) : (Over.forgetAdjStar X).counit.app Y = prod.snd := by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `forgetAdjStar_unit_app_left` / 引理 `forgetAdjStar_unit_app_left`

English:
lemma forgetAdjStar_unit_app_left
  given: (X : C) (Y : Over X)
  proof: by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

中文:
引理 forgetAdjStar_unit_app_left
  条件: (X : C) (Y : Over X)
  证明: by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

Depends on / 依赖: CategoryTheory, CategoryTheory.coalgebraEquivOver, Over.forgetAdjStar, coalgebraEquivOver, forgetAdjStar
-/
lemma forgetAdjStar_unit_app_left (X : C) (Y : Over X) :
    ((Over.forgetAdjStar X).unit.app Y).left = prod.lift Y.hom (𝟙 _) := by
  simp [Over.forgetAdjStar, CategoryTheory.coalgebraEquivOver]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (star X).IsRightAdjoint
  body: ⟨_, ⟨forgetAdjStar X⟩⟩

中文:
实例 :
  签名: (star X).是右伴随
  定义体: ⟨_, ⟨forgetAdjStar X⟩⟩

Depends on / 依赖: forgetAdjStar
-/
instance : (star X).IsRightAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget X).IsLeftAdjoint
  body: ⟨_, ⟨forgetAdjStar X⟩⟩

中文:
实例 :
  签名: (forget X).是左伴随
  定义体: ⟨_, ⟨forgetAdjStar X⟩⟩

Depends on / 依赖: forgetAdjStar
-/
instance : (forget X).IsLeftAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lifting to over `Y` and pulling back along `X ⟶ Y` is the same as lifting to over `X`. -/
@[simps!]
/--
Definition of `starPullbackIsoStar` / `starPullbackIsoStar` 的定义

English:
definition starPullbackIsoStar
  signature: [HasPullbacks C] {X Y : C} (f : X ⟶ Y)
  body: NatIso.ofComponents
    (fun Z =>
      Over.isoMk
      (pullback.congrHom (by simp) rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackProdFstIsoProd _ _)
    (by simp))

中文:
定义 starPullbackIsoStar
  签名: [有Pullbacks C] {X Y : C} (f : X ⟶ Y)
  定义体: NatIso.ofComponents
    (fun Z =>
      Over.isoMk
      (pullback.congrHom (by simp) rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackProdFstIsoProd _ _)
    (by simp))

Depends on / 依赖: NatIso, NatIso.ofComponents, Over.isoMk, congrHom, ofComponents, pullback, pullback.congrHom, pullbackProdFstIsoProd, pullbackSymmetry
-/
noncomputable def starPullbackIsoStar [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    star Y ⋙ pullback f ≅ star X :=
  NatIso.ofComponents
    (fun Z =>
      Over.isoMk
      (pullback.congrHom (by simp) rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackProdFstIsoProd _ _)
    (by simp))

end HasBinaryProducts
end Over

namespace Under

attribute [local instance] hasPushout_of_right_iso

set_option backward.isDefEq.respectTransparency false in
/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
/--
Definition of `pushout` / `pushout` 的定义

English:
definition pushout
  signature: {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
  body: Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

中文:
定义 pushout
  签名: {X Y : C} (f : X ⟶ Y) [有PushoutsAlong f]
  定义体: Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

Depends on / 依赖: Under.mk, pushout, pushout.inr, x.hom
-/
def pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    Under X ⥤ Under Y where
  obj x := Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

set_option backward.isDefEq.respectTransparency false in
/-- `Under.pushout f` is left adjoint to `Under.map f`. -/
@[simps! unit_app counit_app]
/--
Definition of `mapPushoutAdj` / `mapPushoutAdj` 的定义

English:
definition mapPushoutAdj
  signature: {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
  body: Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [map_obj_right, pushout_obj, mk_right, mk_hom]
        rw [← assoc]; rw [← assoc]; rw [pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by cat_disch
    }
  }

中文:
定义 mapPushoutAdj
  签名: {X Y : C} (f : X ⟶ Y) [有PushoutsAlong f]
  定义体: Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [map_obj_right, pushout_obj, mk_right, mk_hom]
        rw [← assoc]; rw [← assoc]; rw [pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by cat_disch
    }
  }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Under.homMk, Under.w, cat_disch, condition, homEquiv, invFun, left_inv, map_obj_hom, map_obj_right, mkOfHomEquiv, mk_hom, mk_right, pushout, pushout.condition, pushout.desc, pushout.inl, pushout_obj, right_inv
-/
def mapPushoutAdj {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    pushout f ⊣ map f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [map_obj_right, pushout_obj, mk_right, mk_hom]
        rw [← assoc]; rw [← assoc]; rw [pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by cat_disch
    }
  }

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in -- simp followed by infer_instance
/--
Instance `faithful_pushout` / 实例 `faithful_pushout`

English:
instance faithful_pushout
  signature: {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
  body: by
  have (Z : Under X) : Mono ((mapPushoutAdj f).unit.app Z) := by simp; infer_instance
  exact (mapPushoutAdj f).faithful_L_of_mono_unit_app

中文:
实例 faithful_pushout
  签名: {X Y : C} (f : X ⟶ Y) [有PushoutsAlong f]
  定义体: by
  have (Z : Under X) : Mono ((mapPushoutAdj f).unit.app Z) := by simp; infer_instance
  exact (mapPushoutAdj f).faithful_L_of_mono_unit_app

Depends on / 依赖: faithful_L_of_mono_unit_app, infer_instance, mapPushoutAdj, unit.app
-/
instance faithful_pushout {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
    [forall Z (g : X ⟶ Z), Mono (pushout.inl g f)] : (pushout f).Faithful := by
  have (Z : Under X) : Mono ((mapPushoutAdj f).unit.app Z) := by simp; infer_instance
  exact (mapPushoutAdj f).faithful_L_of_mono_unit_app

/--
Definition of `pushoutId` / `pushoutId` 的定义

English:
definition pushoutId
  signature: {X : C}
  body: (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _))).symm
    (Under.mapId X).symm

中文:
定义 pushoutId
  签名: {X : C}
  定义体: (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _))).symm
    (Under.mapId X).symm

Depends on / 依赖: Adjunction, Adjunction.id, Under.mapId, conjugateIsoEquiv, mapPushoutAdj
-/
def pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _))).symm
    (Under.mapId X).symm

/--
Definition of `pushoutComp` / `pushoutComp` 的定义

English:
definition pushoutComp
  signature: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _)).symm
    (mapComp f g).symm

中文:
定义 pushoutComp
  签名: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _)).symm
    (mapComp f g).symm

Depends on / 依赖: conjugateIsoEquiv, mapComp, mapPushoutAdj
-/
def pushoutComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasPushoutsAlong f] [HasPushoutsAlong g] :
    pushout (f ≫ g) ≅ pushout f ⋙ pushout g :=
  (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _)).symm
    (mapComp f g).symm

/--
Instance `pushoutIsLeftAdjoint` / 实例 `pushoutIsLeftAdjoint`

English:
instance pushoutIsLeftAdjoint
  signature: {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f]
  body: ⟨_, ⟨mapPushoutAdj f⟩⟩

中文:
实例 pushoutIsLeftAdjoint
  签名: {X Y : C} (f : X ⟶ Y) [有PushoutsAlong f]
  定义体: ⟨_, ⟨mapPushoutAdj f⟩⟩

Depends on / 依赖: mapPushoutAdj
-/
instance pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) [HasPushoutsAlong f] :
    (pushout f).IsLeftAdjoint :=
  ⟨_, ⟨mapPushoutAdj f⟩⟩

set_option backward.isDefEq.respectTransparency false in
open pushout in
/-- If `G` is a right adjoint and its source category has pushouts, then so is
`post G : Under Y ⥤ Under (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(G Y ⟶ X) ↦ (Y ⟶ Y ⨿_{F G Y} F X ⟶ F X)`. -/
@[simps!]
/--
Definition of `postAdjunctionRight` / `postAdjunctionRight` 的定义

English:
definition postAdjunctionRight
  signature: [HasPushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
  body: ((postAdjunctionLeft a).comp (mapPushoutAdj (a.counit.app Y))).ofNatIsoRight
    NatIso.ofComponents fun Y => isoMk (.refl _)

中文:
定义 postAdjunctionRight
  签名: [有Pushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
  定义体: ((postAdjunctionLeft a).comp (mapPushoutAdj (a.counit.app Y))).ofNatIsoRight
    NatIso.ofComponents fun Y => isoMk (.refl _)

Depends on / 依赖: NatIso, NatIso.ofComponents, a.counit.app, counit, mapPushoutAdj, ofComponents, ofNatIsoRight, postAdjunctionLeft
-/
def postAdjunctionRight [HasPushouts D] {Y : D} {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    post F ⋙ pushout (a.counit.app Y) ⊣ post G :=
((postAdjunctionLeft a).comp (mapPushoutAdj (a.counit.app Y))).ofNatIsoRight
    NatIso.ofComponents fun Y => isoMk (.refl _)

open pushout in
/--
Instance `isRightAdjoint_post` / 实例 `isRightAdjoint_post`

English:
instance isRightAdjoint_post
  signature: [HasPushouts D] {Y : D} {G : D ⥤ C} [G.IsRightAdjoint]
  body: let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

中文:
实例 isRightAdjoint_post
  签名: [有Pushouts D] {Y : D} {G : D ⥤ C} [G.是右伴随]
  定义体: let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

Depends on / 依赖: IsRightAdjoint
-/
instance isRightAdjoint_post [HasPushouts D] {Y : D} {G : D ⥤ C} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

/-- The category under any object `X` factors through the category under the initial object `I`. -/
@[simps!]
/--
Definition of `forgetMapInitial` / `forgetMapInitial` 的定义

English:
definition forgetMapInitial
  signature: {I : C} (hI : IsInitial I)
  body: NatIso.ofComponents fun X => .refl _

中文:
定义 forgetMapInitial
  签名: {I : C} (hI : IsInitial I)
  定义体: NatIso.ofComponents fun X => .refl _

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
noncomputable def forgetMapInitial {I : C} (hI : IsInitial I) :
    forget X ≅ map (hI.to X) ⋙ (equivalenceOfIsInitial hI).functor :=
  NatIso.ofComponents fun X => .refl _

section HasBinaryCoproducts
variable [HasBinaryCoproducts C]

/-- The functor from `C` to `Under X` which sends `Y : C` to `in₁ : X ⟶ X ⨿ Y`. -/
@[simps! obj_left obj_hom]
/--
Definition of `costar` / `costar` 的定义

English:
definition costar
  signature: : C ⥤ Under X
  body: Monad.free _ ⋙ algebraToUnder X

中文:
定义 costar
  签名: : C ⥤ Under X
  定义体: Monad.free _ ⋙ algebraToUnder X

Depends on / 依赖: Monad.free, algebraToUnder
-/
def costar : C ⥤ Under X := Monad.free _ ⋙ algebraToUnder X

/--
Definition of `costarAdjForget` / `costarAdjForget` 的定义

English:
definition costarAdjForget
  signature: : costar X ⊣ forget X
  body: (Monad.adj _).comp (algebraEquivUnder X).toAdjunction

中文:
定义 costarAdjForget
  签名: : costar X ⊣ forget X
  定义体: (Monad.adj _).comp (algebraEquivUnder X).toAdjunction

Depends on / 依赖: Monad.adj, algebraEquivUnder, toAdjunction
-/
def costarAdjForget : costar X ⊣ forget X := (Monad.adj _).comp (algebraEquivUnder X).toAdjunction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (costar X).IsLeftAdjoint
  body: ⟨_, ⟨costarAdjForget X⟩⟩

中文:
实例 :
  签名: (costar X).是左伴随
  定义体: ⟨_, ⟨costarAdjForget X⟩⟩

Depends on / 依赖: costarAdjForget
-/
instance : (costar X).IsLeftAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget X).IsRightAdjoint
  body: ⟨_, ⟨costarAdjForget X⟩⟩

中文:
实例 :
  签名: (forget X).是右伴随
  定义体: ⟨_, ⟨costarAdjForget X⟩⟩

Depends on / 依赖: costarAdjForget
-/
instance : (forget X).IsRightAdjoint := ⟨_, ⟨costarAdjForget X⟩⟩

end HasBinaryCoproducts
end Under

end CategoryTheory
