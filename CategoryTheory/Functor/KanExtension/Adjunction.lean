/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-! # The Kan extension functor

Given a functor `L : C ⥤ D`, we define the left Kan extension functor
`L.lan : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
left Kan extension along `L`. This is defined if all `F` have such
a left Kan extension. It is shown that `L.lan` is the left adjoint to
the functor `(D ⥤ H) ⥤ (C ⥤ H)` given by the precomposition
with `L` (see `Functor.lanAdjunction`).

Similarly, we define the right Kan extension functor
`L.ran : (C ⥤ H) ⥤ (D ⥤ H)` which sends a functor `F : C ⥤ H` to its
right Kan extension along `L`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) {H : Type*} [Category* H]

section lan

section

variable [forall (F : C ⥤ H), HasLeftKanExtension L F]

/--
Definition of `lan` / `lan` 的定义

English:
definition lan
  signature: : (C ⥤ H) ⥤ (D ⥤ H) where
  body: leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

中文:
定义 lan
  签名: : (C ⥤ H) ⥤ (D ⥤ H) where
  定义体: leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

Depends on / 依赖: leftKanExtension
-/
noncomputable def lan : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := leftKanExtension L F
  map {F₁ F₂} φ := descOfIsLeftKanExtension _ (leftKanExtensionUnit L F₁) _
    (φ ≫ leftKanExtensionUnit L F₂)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `lanUnit` / `lanUnit` 的定义

English:
definition lanUnit
  signature: : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  body: leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]

中文:
定义 lanUnit
  签名: : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  定义体: leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]

Depends on / 依赖: leftKanExtensionUnit
-/
noncomputable def lanUnit : (𝟭 (C ⥤ H)) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L where
  app F := leftKanExtensionUnit L F
  naturality {F₁ F₂} φ := by ext; simp [lan]

instance (F : C ⥤ H) : (L.lan.obj F).IsLeftKanExtension (L.lanUnit.app F) := by
  dsimp [lan, lanUnit]
  infer_instance

end

/--
Definition of `isPointwiseLeftKanExtensionLeftKanExtensionUnit` / `isPointwiseLeftKanExtensionLeftKanExtensionUnit` 的定义

English:
definition isPointwiseLeftKanExtensionLeftKanExtensionUnit
  body: isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (leftKanExtensionUnit L F)

中文:
定义 isPointwiseLeftKanExtensionLeftKanExtensionUnit
  定义体: isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (leftKanExtensionUnit L F)

Depends on / 依赖: isPointwiseLeftKanExtensionOfIsLeftKanExtension, leftKanExtensionUnit
-/
noncomputable def isPointwiseLeftKanExtensionLeftKanExtensionUnit
    (F : C ⥤ H) [HasPointwiseLeftKanExtension L F] :
    (LeftExtension.mk _ (L.leftKanExtensionUnit F)).IsPointwiseLeftKanExtension :=
  isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := F) _ (leftKanExtensionUnit L F)

section

open CostructuredArrow

variable (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]

/--
Definition of `leftKanExtensionObjIsoColimit` / `leftKanExtensionObjIsoColimit` 的定义

English:
definition leftKanExtensionObjIsoColimit
  signature: [HasLeftKanExtension L F] (X : D)
  body: LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X)

中文:
定义 leftKanExtensionObjIsoColimit
  签名: [HasLeftKanExtension L F] (X : D)
  定义体: LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X)

Depends on / 依赖: IsPointwiseLeftKanExtensionAt, LeftExtension, LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit, isPointwiseLeftKanExtensionLeftKanExtensionUnit, isoColimit
-/
noncomputable def leftKanExtensionObjIsoColimit [HasLeftKanExtension L F] (X : D) :
    (L.leftKanExtension F).obj X ≅ colimit (proj L X ⋙ F) :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.isoColimit (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_leftKanExtensionObjIsoColimit_inv` / 引理 `ι_leftKanExtensionObjIsoColimit_inv`

English:
lemma ι_leftKanExtensionObjIsoColimit_inv
  statement: [HasLeftKanExtension L F] (X : D)
  proof: by
  simp [leftKanExtensionObjIsoColimit]

@[reassoc (attr := simp)]

中文:
引理 ι_leftKanExtensionObjIsoColimit_inv
  结论: [HasLeftKanExtension L F] (X : D)
  证明: by
  simp [leftKanExtensionObjIsoColimit]

@[reassoc (attr := simp)]

Depends on / 依赖: leftKanExtensionObjIsoColimit
-/
lemma ι_leftKanExtensionObjIsoColimit_inv [HasLeftKanExtension L F] (X : D)
    (f : CostructuredArrow L X) :
    colimit.ι _ f ≫ (L.leftKanExtensionObjIsoColimit F X).inv =
    (L.leftKanExtensionUnit F).app f.left ≫ (L.leftKanExtension F).map f.hom := by
  simp [leftKanExtensionObjIsoColimit]

@[reassoc (attr := simp)]
/--
lemma `ι_leftKanExtensionObjIsoColimit_hom` / 引理 `ι_leftKanExtensionObjIsoColimit_hom`

English:
lemma ι_leftKanExtensionObjIsoColimit_hom
  given: (X : D) (f : CostructuredArrow L X)
  proof: LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

中文:
引理 ι_leftKanExtensionObjIsoColimit_hom
  条件: (X : D) (f : CostructuredArrow L X)
  证明: LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

Depends on / 依赖: IsPointwiseLeftKanExtensionAt, LeftExtension, LeftExtension.IsPointwiseLeftKanExtensionAt, isPointwiseLeftKanExtensionLeftKanExtensionUnit
-/
lemma ι_leftKanExtensionObjIsoColimit_hom (X : D) (f : CostructuredArrow L X) :
    (L.leftKanExtensionUnit F).app f.left ≫ (L.leftKanExtension F).map f.hom ≫
      (L.leftKanExtensionObjIsoColimit F X).hom =
    colimit.ι (proj L X ⋙ F) f :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

/--
lemma `leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom` / 引理 `leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom`

English:
lemma leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom
  statement: (X : D)
  proof: LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

中文:
引理 leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom
  结论: (X : D)
  证明: LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

Depends on / 依赖: IsPointwiseLeftKanExtensionAt, LeftExtension, LeftExtension.IsPointwiseLeftKanExtensionAt, isPointwiseLeftKanExtensionLeftKanExtensionUnit
-/
lemma leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom (X : D)
    (f : CostructuredArrow L X) :
    (leftKanExtensionUnit L F).app f.left ≫ (leftKanExtension L F).map f.hom ≫
       (L.leftKanExtensionObjIsoColimit F X).hom =
    colimit.ι (proj L X ⋙ F) f :=
  LeftExtension.IsPointwiseLeftKanExtensionAt.ι_isoColimit_hom (F := F)
    (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F X) f

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom` / 引理 `leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom`

English:
lemma leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
  given: (X : C)
  proof: by
  simpa using leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom L F
    (L.obj X) (CostructuredArrow.mk (𝟙 _))

中文:
引理 leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom
  条件: (X : C)
  证明: by
  simpa using leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom L F
    (L.obj X) (CostructuredArrow.mk (𝟙 _))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, L.obj, leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom
-/
lemma leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom (X : C) :
    (L.leftKanExtensionUnit F).app X ≫ (L.leftKanExtensionObjIsoColimit F (L.obj X)).hom =
    colimit.ι (proj L (L.obj X) ⋙ F) (CostructuredArrow.mk (𝟙 _)) := by
  simpa using leftKanExtensionUnit_leftKanExtension_map_leftKanExtensionObjIsoColimit_hom L F
    (L.obj X) (CostructuredArrow.mk (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[instance]
/--
theorem `hasColimit_map_comp_ι_comp_grothendieckProj` / 定理 `hasColimit_map_comp_ι_comp_grothendieckProj`

English:
theorem hasColimit_map_comp_ι_comp_grothendieckProj
  given: {X Y : D} (f : X ⟶ Y)
  proof: hasColimit_of_iso (isoWhiskerRight (mapCompιCompGrothendieckProj L f) F)

中文:
定理 hasColimit_map_comp_ι_comp_grothendieckProj
  条件: {X Y : D} (f : X ⟶ Y)
  证明: hasColimit_of_iso (isoWhiskerRight (mapCompιCompGrothendieckProj L f) F)

Depends on / 依赖: hasColimit_of_iso, isoWhiskerRight
-/
theorem hasColimit_map_comp_ι_comp_grothendieckProj {X Y : D} (f : X ⟶ Y) :
    HasColimit (((functor L).map f).toFunctor ⋙ Grothendieck.ι (functor L) Y ⋙
      grothendieckProj L ⋙ F) :=
  hasColimit_of_iso (isoWhiskerRight (mapCompιCompGrothendieckProj L f) F)

set_option backward.isDefEq.respectTransparency false in
/-- The left Kan extension of `F : C ⥤ H` along a functor `L : C ⥤ D` is isomorphic to the
fiberwise colimit of the projection functor on the Grothendieck construction of the costructured
arrow category composed with `F`. -/
@[simps!]
/--
Definition of `leftKanExtensionIsoFiberwiseColimit` / `leftKanExtensionIsoFiberwiseColimit` 的定义

English:
definition leftKanExtensionIsoFiberwiseColimit
  signature: [HasLeftKanExtension L F]
  body: letI : forall X, HasColimit (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F) :=
fun X => hasColimit_of_iso Iso.symm
        isoWhiskerRight (eqToIso congr($((functor L).map_id X).toFunctor)) _ ≪≫
        Functor.leftUnitor (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F)
Iso.symm NatIs

中文:
定义 leftKanExtensionIsoFiberwiseColimit
  签名: [HasLeftKanExtension L F]
  定义体: letI : forall X, HasColimit (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F) :=
fun X => hasColimit_of_iso Iso.symm
        isoWhiskerRight (eqToIso congr($((functor L).map_id X).toFunctor)) _ ≪≫
        Functor.leftUnitor (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F)
Iso.symm NatIs

Depends on / 依赖: Functor, Functor.leftUnitor, Grothendieck, HasColimit, HasColimit.isoOfNatIso, Iso.symm, NatIso, NatIso.ofComponents, colimit, colimit.hom_ext, eqToIso, functor, grothendieckProj, hasColimit_of_iso, hom_ext, isoOfNatIso, isoWhiskerRight, leftKanExtensionObjIsoColimit, leftUnitor, map_id
-/
noncomputable def leftKanExtensionIsoFiberwiseColimit [HasLeftKanExtension L F] :
    leftKanExtension L F ≅ fiberwiseColimit (grothendieckProj L ⋙ F) :=
  letI : forall X, HasColimit (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F) :=
fun X => hasColimit_of_iso Iso.symm
        isoWhiskerRight (eqToIso congr($((functor L).map_id X).toFunctor)) _ ≪≫
        Functor.leftUnitor (Grothendieck.ι (functor L) X ⋙ grothendieckProj L ⋙ F)
Iso.symm NatIso.ofComponents
    (fun X => HasColimit.isoOfNatIso (isoWhiskerRight (ιCompGrothendieckProj L X) F) ≪≫
      (leftKanExtensionObjIsoColimit L F X).symm)
    fun f => colimit.hom_ext (by simp)

end

section HasLeftKanExtension

variable [forall (F : C ⥤ H), HasLeftKanExtension L F]

set_option backward.isDefEq.respectTransparency false in
variable (H) in
/--
Definition of `lanAdjunction` / `lanAdjunction` 的定义

English:
definition lanAdjunction
  signature: : L.lan ⊣ (whiskeringLeft C D H).obj L
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _ (L.lanUnit.app F₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
      

中文:
定义 lanAdjunction
  签名: : L.lan ⊣ (whiskeringLeft C D H).obj L
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _ (L.lanUnit.app F₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
      

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, L.lanUnit.app, L.lanUnit.naturality, NatTrans, NatTrans.comp_app, comp_app, congr_app, descOfIsLeftKanExtension_fac_app, homEquiv, homEquivOfIsLeftKanExtension, homEquiv_naturality_left_symm, homEquiv_naturality_right, hom_ext_of_isLeftKanExtension, lanUnit, mkOfHomEquiv, naturality
-/
noncomputable def lanAdjunction : L.lan ⊣ (whiskeringLeft C D H).obj L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G => homEquivOfIsLeftKanExtension _ (L.lanUnit.app F) G
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} f α =>
        hom_ext_of_isLeftKanExtension _ (L.lanUnit.app F₁) _ _ (by
          ext X
          dsimp [homEquivOfIsLeftKanExtension]
          rw [descOfIsLeftKanExtension_fac_app]; rw [NatTrans.comp_app]; rw [← assoc]
          have h := congr_app (L.lanUnit.naturality f) X
          dsimp at h ⊢
          rw [← h]; rw [assoc]; rw [descOfIsLeftKanExtension_fac_app])
      homEquiv_naturality_right := fun {F G₁ G₂} β f => by
        dsimp [homEquivOfIsLeftKanExtension]
        rw [assoc] }

set_option backward.isDefEq.respectTransparency false in
variable (H) in
@[simp]
/--
lemma `lanAdjunction_unit` / 引理 `lanAdjunction_unit`

English:
lemma lanAdjunction_unit
  statement: (L.lanAdjunction H).unit = L.lanUnit
  proof: by
  ext F : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp

中文:
引理 lanAdjunction_unit
  结论: (L.lanAdjunction H).unit = L.lanUnit
  证明: by
  ext F : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp

Depends on / 依赖: homEquivOfIsLeftKanExtension, lanAdjunction
-/
lemma lanAdjunction_unit : (L.lanAdjunction H).unit = L.lanUnit := by
  ext F : 2
  dsimp [lanAdjunction, homEquivOfIsLeftKanExtension]
  simp

/--
lemma `lanAdjunction_counit_app` / 引理 `lanAdjunction_counit_app`

English:
lemma lanAdjunction_counit_app
  given: (G : D ⥤ H)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 lanAdjunction_counit_app
  条件: (G : D ⥤ H)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma lanAdjunction_counit_app (G : D ⥤ H) :
    (L.lanAdjunction H).counit.app G =
      descOfIsLeftKanExtension (L.lan.obj (L ⋙ G)) (L.lanUnit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `lanUnit_app_whiskerLeft_lanAdjunction_counit_app` / 引理 `lanUnit_app_whiskerLeft_lanAdjunction_counit_app`

English:
lemma lanUnit_app_whiskerLeft_lanAdjunction_counit_app
  given: (G : D ⥤ H)
  proof: by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]

中文:
引理 lanUnit_app_whiskerLeft_lanAdjunction_counit_app
  条件: (G : D ⥤ H)
  证明: by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]

Depends on / 依赖: lanAdjunction_counit_app
-/
lemma lanUnit_app_whiskerLeft_lanAdjunction_counit_app (G : D ⥤ H) :
    L.lanUnit.app (L ⋙ G) ≫ whiskerLeft L ((L.lanAdjunction H).counit.app G) = 𝟙 (L ⋙ G) := by
  simp [lanAdjunction_counit_app]

@[reassoc (attr := simp)]
/--
lemma `lanUnit_app_app_lanAdjunction_counit_app_app` / 引理 `lanUnit_app_app_lanAdjunction_counit_app_app`

English:
lemma lanUnit_app_app_lanAdjunction_counit_app_app
  given: (G : D ⥤ H) (X : C)
  proof: congr_app (L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

中文:
引理 lanUnit_app_app_lanAdjunction_counit_app_app
  条件: (G : D ⥤ H) (X : C)
  证明: congr_app (L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

Depends on / 依赖: L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app, congr_app, lanUnit_app_whiskerLeft_lanAdjunction_counit_app
-/
lemma lanUnit_app_app_lanAdjunction_counit_app_app (G : D ⥤ H) (X : C) :
    (L.lanUnit.app (L ⋙ G)).app X ≫ ((L.lanAdjunction H).counit.app G).app (L.obj X) = 𝟙 _ :=
  congr_app (L.lanUnit_app_whiskerLeft_lanAdjunction_counit_app G) X

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_lanAdjunction_counit_app_iff` / 引理 `isIso_lanAdjunction_counit_app_iff`

English:
lemma isIso_lanAdjunction_counit_app_iff
  given: (G : D ⥤ H)
  proof: (isLeftKanExtension_iff_isIso _ (L.lanUnit.app (L ⋙ G)) _ (by simp)).symm

中文:
引理 isIso_lanAdjunction_counit_app_iff
  条件: (G : D ⥤ H)
  证明: (isLeftKanExtension_iff_isIso _ (L.lanUnit.app (L ⋙ G)) _ (by simp)).symm

Depends on / 依赖: L.lanUnit.app, isLeftKanExtension_iff_isIso, lanUnit
-/
lemma isIso_lanAdjunction_counit_app_iff (G : D ⥤ H) :
    IsIso ((L.lanAdjunction H).counit.app G) ↔ G.IsLeftKanExtension (𝟙 (L ⋙ G)) :=
  (isLeftKanExtension_iff_isIso _ (L.lanUnit.app (L ⋙ G)) _ (by simp)).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_lanAdjunction_homEquiv_symm_iff` / 引理 `isIso_lanAdjunction_homEquiv_symm_iff`

English:
lemma isIso_lanAdjunction_homEquiv_symm_iff
  given: {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙ G)
  proof: (isLeftKanExtension_iff_isIso ((((L.lanAdjunction H).homEquiv _ _).symm α))
    (L.lanUnit.app F) α (by simp [lanAdjunction])).symm

中文:
引理 isIso_lanAdjunction_homEquiv_symm_iff
  条件: {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙ G)
  证明: (isLeftKanExtension_iff_isIso ((((L.lanAdjunction H).homEquiv _ _).symm α))
    (L.lanUnit.app F) α (by simp [lanAdjunction])).symm

Depends on / 依赖: L.lanAdjunction, L.lanUnit.app, homEquiv, isLeftKanExtension_iff_isIso, lanAdjunction, lanUnit
-/
lemma isIso_lanAdjunction_homEquiv_symm_iff {F : C ⥤ H} {G : D ⥤ H} (α : F ⟶ L ⋙ G) :
    IsIso (((L.lanAdjunction H).homEquiv _ _).symm α) ↔ G.IsLeftKanExtension α :=
  (isLeftKanExtension_iff_isIso ((((L.lanAdjunction H).homEquiv _ _).symm α))
    (L.lanUnit.app F) α (by simp [lanAdjunction])).symm

/-- Composing the left Kan extension of `L : C ⥤ D` with `colim` on shapes `D` is isomorphic
to `colim` on shapes `C`. -/
@[simps!]
/--
Definition of `lanCompColimIso` / `lanCompColimIso` 的定义

English:
definition lanCompColimIso
  signature: [HasColimitsOfShape C H] [HasColimitsOfShape D H]
  body: Iso.symm NatIso.ofComponents
    (fun G => (colimitIsoOfIsLeftKanExtension _ (L.lanUnit.app G)).symm)
    (fun f => colimit.hom_ext (fun i => by
      dsimp
      rw [ι_colimMap_assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_inv]; rw [ι_colimitIsoOfIsLeftKanExtension_inv_assoc]; rw [ι_colimMap]; rw [←

中文:
定义 lanCompColimIso
  签名: [HasColimitsOfShape C H] [HasColimitsOfShape D H]
  定义体: Iso.symm NatIso.ofComponents
    (fun G => (colimitIsoOfIsLeftKanExtension _ (L.lanUnit.app G)).symm)
    (fun f => colimit.hom_ext (fun i => by
      dsimp
      rw [ι_colimMap_assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_inv]; rw [ι_colimitIsoOfIsLeftKanExtension_inv_assoc]; rw [ι_colimMap]; rw [←
-/
noncomputable def lanCompColimIso [HasColimitsOfShape C H] [HasColimitsOfShape D H] :
    L.lan ⋙ colim ≅ colim (C := H) :=
Iso.symm NatIso.ofComponents
    (fun G => (colimitIsoOfIsLeftKanExtension _ (L.lanUnit.app G)).symm)
    (fun f => colimit.hom_ext (fun i => by
      dsimp
      rw [ι_colimMap_assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_inv]; rw [ι_colimitIsoOfIsLeftKanExtension_inv_assoc]; rw [ι_colimMap]; rw [← assoc]; rw [← assoc]
      congr 1
      exact congr_app (L.lanUnit.naturality f) i))

end HasLeftKanExtension

section HasPointwiseLeftKanExtension

variable (G : C ⥤ H) [L.HasPointwiseLeftKanExtension G]

variable [HasColimitsOfShape D H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit (CostructuredArrow.grothendieckProj L ⋙ G)
  body: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

中文:
实例 :
  签名: HasColimit (CostructuredArrow.grothendieckProj L ⋙ G)
  定义体: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

Depends on / 依赖: hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit
-/
instance : HasColimit (CostructuredArrow.grothendieckProj L ⋙ G) :=
  hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit _

variable [HasColimitsOfShape C H]

/--
Definition of `colimitIsoColimitGrothendieck` / `colimitIsoColimitGrothendieck` 的定义

English:
definition colimitIsoColimitGrothendieck
  signature: :
  body: calc
  colimit G
    ≅ colimit (leftKanExtension L G) :=
        (colimitIsoOfIsLeftKanExtension _ (L.leftKanExtensionUnit G)).symm
  _ ≅ colimit (fiberwiseColimit (CostructuredArrow.grothendieckProj L ⋙ G)) :=
        HasColimit.isoOfNatIso (leftKanExtensionIsoFiberwiseColimit L G)
  _ ≅ colimit (C

中文:
定义 colimitIsoColimitGrothendieck
  签名: :
  定义体: calc
  colimit G
    ≅ colimit (leftKanExtension L G) :=
        (colimitIsoOfIsLeftKanExtension _ (L.leftKanExtensionUnit G)).symm
  _ ≅ colimit (fiberwiseColimit (CostructuredArrow.grothendieckProj L ⋙ G)) :=
        HasColimit.isoOfNatIso (leftKanExtensionIsoFiberwiseColimit L G)
  _ ≅ colimit (C
-/
noncomputable def colimitIsoColimitGrothendieck :
    colimit G ≅ colimit (CostructuredArrow.grothendieckProj L ⋙ G) := calc
  colimit G
    ≅ colimit (leftKanExtension L G) :=
        (colimitIsoOfIsLeftKanExtension _ (L.leftKanExtensionUnit G)).symm
  _ ≅ colimit (fiberwiseColimit (CostructuredArrow.grothendieckProj L ⋙ G)) :=
        HasColimit.isoOfNatIso (leftKanExtensionIsoFiberwiseColimit L G)
  _ ≅ colimit (CostructuredArrow.grothendieckProj L ⋙ G) :=
        colimitFiberwiseColimitIso _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitIsoColimitGrothendieck_inv` / 引理 `ι_colimitIsoColimitGrothendieck_inv`

English:
lemma ι_colimitIsoColimitGrothendieck_inv
  given: (X : Grothendieck (CostructuredArrow.functor L))
  proof: by
  simp [colimitIsoColimitGrothendieck]

中文:
引理 ι_colimitIsoColimitGrothendieck_inv
  条件: (X : Grothendieck (CostructuredArrow.functor L))
  证明: by
  simp [colimitIsoColimitGrothendieck]

Depends on / 依赖: colimitIsoColimitGrothendieck
-/
lemma ι_colimitIsoColimitGrothendieck_inv (X : Grothendieck (CostructuredArrow.functor L)) :
    colimit.ι (CostructuredArrow.grothendieckProj L ⋙ G) X ≫
      (colimitIsoColimitGrothendieck L G).inv =
    colimit.ι G ((CostructuredArrow.proj L X.base).obj X.fiber) := by
  simp [colimitIsoColimitGrothendieck]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitIsoColimitGrothendieck_hom` / 引理 `ι_colimitIsoColimitGrothendieck_hom`

English:
lemma ι_colimitIsoColimitGrothendieck_hom
  given: (X : C)
  proof: by
  rw [← Iso.eq_comp_inv]
  exact (ι_colimitIsoColimitGrothendieck_inv L G ⟨L.obj X, .mk (𝟙 _)⟩).symm

中文:
引理 ι_colimitIsoColimitGrothendieck_hom
  条件: (X : C)
  证明: by
  rw [← Iso.eq_comp_inv]
  exact (ι_colimitIsoColimitGrothendieck_inv L G ⟨L.obj X, .mk (𝟙 _)⟩).symm

Depends on / 依赖: Iso.eq_comp_inv, L.obj, eq_comp_inv
-/
lemma ι_colimitIsoColimitGrothendieck_hom (X : C) :
    colimit.ι G X ≫ (colimitIsoColimitGrothendieck L G).hom =
    colimit.ι (CostructuredArrow.grothendieckProj L ⋙ G) ⟨L.obj X, .mk (𝟙 _)⟩ := by
  rw [← Iso.eq_comp_inv]
  exact (ι_colimitIsoColimitGrothendieck_inv L G ⟨L.obj X, .mk (𝟙 _)⟩).symm

end HasPointwiseLeftKanExtension


section

variable [Full L] [Faithful L]

instance (F : C ⥤ H) (X : C) [HasPointwiseLeftKanExtension L F]
    [forall (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanUnit.app F).app X) :=
  (isPointwiseLeftKanExtensionLeftKanExtensionUnit L F (L.obj X)).isIso_hom_app

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [forall (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso (L.lanUnit.app F) :=
  NatIso.isIso_of_isIso_app _

/--
Instance `coreflective` / 实例 `coreflective`

English:
instance coreflective
  signature: [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F]
  body: by
  apply NatIso.isIso_of_isIso_app _

中文:
实例 coreflective
  签名: [对任意 (F : C ⥤ H), HasPointwiseLeftKanExtension L F]
  定义体: by
  apply NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance coreflective [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanUnit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _

instance (F : C ⥤ H) [HasPointwiseLeftKanExtension L F]
    [forall (F : C ⥤ H), HasLeftKanExtension L F] :
    IsIso ((L.lanAdjunction H).unit.app F) := by
  rw [lanAdjunction_unit]
  infer_instance

/--
Instance `coreflective'` / 实例 `coreflective'`

English:
instance coreflective'
  signature: [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F]
  body: by
  apply NatIso.isIso_of_isIso_app _

中文:
实例 coreflective'
  签名: [对任意 (F : C ⥤ H), HasPointwiseLeftKanExtension L F]
  定义体: by
  apply NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance coreflective' [forall (F : C ⥤ H), HasPointwiseLeftKanExtension L F] :
    IsIso (L.lanAdjunction H).unit := by
  apply NatIso.isIso_of_isIso_app _

end

end lan

section ran

section

variable [forall (F : C ⥤ H), HasRightKanExtension L F]

/--
Definition of `ran` / `ran` 的定义

English:
definition ran
  signature: : (C ⥤ H) ⥤ (D ⥤ H) where
  body: rightKanExtension L F
  map {F₁ F₂} φ := liftOfIsRightKanExtension _ (rightKanExtensionCounit L F₂) _
    (rightKanExtensionCounit L F₁ ≫ φ)

中文:
定义 ran
  签名: : (C ⥤ H) ⥤ (D ⥤ H) where
  定义体: rightKanExtension L F
  map {F₁ F₂} φ := liftOfIsRightKanExtension _ (rightKanExtensionCounit L F₂) _
    (rightKanExtensionCounit L F₁ ≫ φ)

Depends on / 依赖: rightKanExtension
-/
noncomputable def ran : (C ⥤ H) ⥤ (D ⥤ H) where
  obj F := rightKanExtension L F
  map {F₁ F₂} φ := liftOfIsRightKanExtension _ (rightKanExtensionCounit L F₂) _
    (rightKanExtensionCounit L F₁ ≫ φ)

/--
Definition of `ranCounit` / `ranCounit` 的定义

English:
definition ranCounit
  signature: : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where
  body: rightKanExtensionCounit L F
  naturality {F₁ F₂} φ := by ext; simp [ran]

中文:
定义 ranCounit
  签名: : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where
  定义体: rightKanExtensionCounit L F
  naturality {F₁ F₂} φ := by ext; simp [ran]

Depends on / 依赖: rightKanExtensionCounit
-/
noncomputable def ranCounit : L.ran ⋙ (whiskeringLeft C D H).obj L ⟶ (𝟭 (C ⥤ H)) where
  app F := rightKanExtensionCounit L F
  naturality {F₁ F₂} φ := by ext; simp [ran]

instance (F : C ⥤ H) : (L.ran.obj F).IsRightKanExtension (L.ranCounit.app F) := by
  dsimp [ran, ranCounit]
  infer_instance

/--
Definition of `isPointwiseRightKanExtensionRanCounit` / `isPointwiseRightKanExtensionRanCounit` 的定义

English:
definition isPointwiseRightKanExtensionRanCounit
  body: isPointwiseRightKanExtensionOfIsRightKanExtension (F := F) _ (L.ranCounit.app F)

中文:
定义 isPointwiseRightKanExtensionRanCounit
  定义体: isPointwiseRightKanExtensionOfIsRightKanExtension (F := F) _ (L.ranCounit.app F)

Depends on / 依赖: L.ranCounit.app, isPointwiseRightKanExtensionOfIsRightKanExtension, ranCounit
-/
noncomputable def isPointwiseRightKanExtensionRanCounit
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] :
    (RightExtension.mk _ (L.ranCounit.app F)).IsPointwiseRightKanExtension :=
  isPointwiseRightKanExtensionOfIsRightKanExtension (F := F) _ (L.ranCounit.app F)

/--
Definition of `ranObjObjIsoLimit` / `ranObjObjIsoLimit` 的定义

English:
definition ranObjObjIsoLimit
  signature: (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D)
  body: RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X)

中文:
定义 ranObjObjIsoLimit
  签名: (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D)
  定义体: RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X)

Depends on / 依赖: IsPointwiseRightKanExtensionAt, RightExtension, RightExtension.IsPointwiseRightKanExtensionAt.isoLimit, isPointwiseRightKanExtensionRanCounit, isoLimit
-/
noncomputable def ranObjObjIsoLimit (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) :
    (L.ran.obj F).obj X ≅ limit (StructuredArrow.proj X L ⋙ F) :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ranObjObjIsoLimit_hom_π` / 引理 `ranObjObjIsoLimit_hom_π`

English:
lemma ranObjObjIsoLimit_hom_π
  proof: by
  simp [ranObjObjIsoLimit, ran, ranCounit]

@[reassoc (attr := simp)]

中文:
引理 ranObjObjIsoLimit_hom_π
  证明: by
  simp [ranObjObjIsoLimit, ran, ranCounit]

@[reassoc (attr := simp)]

Depends on / 依赖: ranCounit, ranObjObjIsoLimit
-/
lemma ranObjObjIsoLimit_hom_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).hom ≫ limit.π _ f =
    (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right := by
  simp [ranObjObjIsoLimit, ran, ranCounit]

@[reassoc (attr := simp)]
/--
lemma `ranObjObjIsoLimit_inv_π` / 引理 `ranObjObjIsoLimit_inv_π`

English:
lemma ranObjObjIsoLimit_inv_π
  proof: RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X) f

中文:
引理 ranObjObjIsoLimit_inv_π
  证明: RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X) f

Depends on / 依赖: IsPointwiseRightKanExtensionAt, RightExtension, RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_, isPointwiseRightKanExtensionRanCounit
-/
lemma ranObjObjIsoLimit_inv_π
    (F : C ⥤ H) [HasPointwiseRightKanExtension L F] (X : D) (f : StructuredArrow X L) :
    (L.ranObjObjIsoLimit F X).inv ≫ (L.ran.obj F).map f.hom ≫ (L.ranCounit.app F).app f.right =
    limit.π _ f :=
  RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_inv_π (F := F)
    (isPointwiseRightKanExtensionRanCounit L F X) f

set_option backward.isDefEq.respectTransparency false in
variable (H) in
/--
Definition of `ranAdjunction` / `ranAdjunction` 的定义

English:
definition ranAdjunction
  signature: : (whiskeringLeft C D H).obj L ⊣ L.ran
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        (homEquivOfIsRightKanExtension (α := L.ranCounit.app G) _ F).symm
      homEquiv_naturality_right := fun {F G₁ G₂} β f =>
        hom_ext_of_isRightKanExtension _ (L.ranCounit.app G₂) _ _ (by
        ext X
        dsimp [homEquivOfIsRightK

中文:
定义 ranAdjunction
  签名: : (whiskeringLeft C D H).obj L ⊣ L.ran
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        (homEquivOfIsRightKanExtension (α := L.ranCounit.app G) _ F).symm
      homEquiv_naturality_right := fun {F G₁ G₂} β f =>
        hom_ext_of_isRightKanExtension _ (L.ranCounit.app G₂) _ _ (by
        ext X
        dsimp [homEquivOfIsRightK

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, L.ranCounit.app, L.ranCounit.naturality, NatTrans, NatTrans.comp_app, comp_app, congr_app, homEquiv, homEquivOfIsRightKanExtension, homEquiv_naturality_left_symm, homEquiv_naturality_right, hom_ext_of_isRightKanExtension, liftOfIsRightKanExtension_fac_app, liftOfIsRightKanExtension_fac_app_assoc, mkOfHomEquiv, naturality, ranCounit
-/
noncomputable def ranAdjunction : (whiskeringLeft C D H).obj L ⊣ L.ran :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        (homEquivOfIsRightKanExtension (α := L.ranCounit.app G) _ F).symm
      homEquiv_naturality_right := fun {F G₁ G₂} β f =>
        hom_ext_of_isRightKanExtension _ (L.ranCounit.app G₂) _ _ (by
        ext X
        dsimp [homEquivOfIsRightKanExtension]
        rw [liftOfIsRightKanExtension_fac_app]; rw [NatTrans.comp_app]; rw [assoc]
        have h := congr_app (L.ranCounit.naturality f) X
        dsimp at h ⊢
        rw [h]; rw [liftOfIsRightKanExtension_fac_app_assoc])
      homEquiv_naturality_left_symm := fun {F₁ F₂ G} β f => by
        dsimp [homEquivOfIsRightKanExtension]
        rw [assoc] }

set_option backward.isDefEq.respectTransparency false in
variable (H) in
@[simp]
/--
lemma `ranAdjunction_counit` / 引理 `ranAdjunction_counit`

English:
lemma ranAdjunction_counit
  statement: (L.ranAdjunction H).counit = L.ranCounit
  proof: by
  ext F : 2
  dsimp [ranAdjunction, homEquivOfIsRightKanExtension]
  simp

中文:
引理 ranAdjunction_counit
  结论: (L.ranAdjunction H).counit = L.ranCounit
  证明: by
  ext F : 2
  dsimp [ranAdjunction, homEquivOfIsRightKanExtension]
  simp

Depends on / 依赖: homEquivOfIsRightKanExtension, ranAdjunction
-/
lemma ranAdjunction_counit : (L.ranAdjunction H).counit = L.ranCounit := by
  ext F : 2
  dsimp [ranAdjunction, homEquivOfIsRightKanExtension]
  simp

/--
lemma `ranAdjunction_unit_app` / 引理 `ranAdjunction_unit_app`

English:
lemma ranAdjunction_unit_app
  given: (G : D ⥤ H)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ranAdjunction_unit_app
  条件: (G : D ⥤ H)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ranAdjunction_unit_app (G : D ⥤ H) :
    (L.ranAdjunction H).unit.app G =
      liftOfIsRightKanExtension (L.ran.obj (L ⋙ G)) (L.ranCounit.app (L ⋙ G)) G (𝟙 (L ⋙ G)) :=
  rfl

@[reassoc (attr := simp)]
/--
lemma `ranCounit_app_whiskerLeft_ranAdjunction_unit_app` / 引理 `ranCounit_app_whiskerLeft_ranAdjunction_unit_app`

English:
lemma ranCounit_app_whiskerLeft_ranAdjunction_unit_app
  given: (G : D ⥤ H)
  proof: by
  simp [ranAdjunction_unit_app]

@[reassoc (attr := simp)]

中文:
引理 ranCounit_app_whiskerLeft_ranAdjunction_unit_app
  条件: (G : D ⥤ H)
  证明: by
  simp [ranAdjunction_unit_app]

@[reassoc (attr := simp)]

Depends on / 依赖: ranAdjunction_unit_app
-/
lemma ranCounit_app_whiskerLeft_ranAdjunction_unit_app (G : D ⥤ H) :
    whiskerLeft L ((L.ranAdjunction H).unit.app G) ≫ L.ranCounit.app (L ⋙ G) = 𝟙 (L ⋙ G) := by
  simp [ranAdjunction_unit_app]

@[reassoc (attr := simp)]
/--
lemma `ranCounit_app_app_ranAdjunction_unit_app_app` / 引理 `ranCounit_app_app_ranAdjunction_unit_app_app`

English:
lemma ranCounit_app_app_ranAdjunction_unit_app_app
  given: (G : D ⥤ H) (X : C)
  proof: congr_app (L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app G) X

中文:
引理 ranCounit_app_app_ranAdjunction_unit_app_app
  条件: (G : D ⥤ H) (X : C)
  证明: congr_app (L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app G) X

Depends on / 依赖: L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app, congr_app, ranCounit_app_whiskerLeft_ranAdjunction_unit_app
-/
lemma ranCounit_app_app_ranAdjunction_unit_app_app (G : D ⥤ H) (X : C) :
    ((L.ranAdjunction H).unit.app G).app (L.obj X) ≫ (L.ranCounit.app (L ⋙ G)).app X = 𝟙 _ :=
  congr_app (L.ranCounit_app_whiskerLeft_ranAdjunction_unit_app G) X

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_ranAdjunction_unit_app_iff` / 引理 `isIso_ranAdjunction_unit_app_iff`

English:
lemma isIso_ranAdjunction_unit_app_iff
  given: (G : D ⥤ H)
  proof: (isRightKanExtension_iff_isIso _ (L.ranCounit.app (L ⋙ G)) _ (by simp)).symm

中文:
引理 isIso_ranAdjunction_unit_app_iff
  条件: (G : D ⥤ H)
  证明: (isRightKanExtension_iff_isIso _ (L.ranCounit.app (L ⋙ G)) _ (by simp)).symm

Depends on / 依赖: L.ranCounit.app, isRightKanExtension_iff_isIso, ranCounit
-/
lemma isIso_ranAdjunction_unit_app_iff (G : D ⥤ H) :
    IsIso ((L.ranAdjunction H).unit.app G) ↔ G.IsRightKanExtension (𝟙 (L ⋙ G)) :=
  (isRightKanExtension_iff_isIso _ (L.ranCounit.app (L ⋙ G)) _ (by simp)).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_ranAdjunction_homEquiv_iff` / 引理 `isIso_ranAdjunction_homEquiv_iff`

English:
lemma isIso_ranAdjunction_homEquiv_iff
  given: {F : C ⥤ H} {G : D ⥤ H} (α : L ⋙ G ⟶ F)
  proof: (isRightKanExtension_iff_isIso ((((L.ranAdjunction H).homEquiv _ _) α))
    (L.ranCounit.app F) α (by simp [ranAdjunction])).symm

中文:
引理 isIso_ranAdjunction_homEquiv_iff
  条件: {F : C ⥤ H} {G : D ⥤ H} (α : L ⋙ G ⟶ F)
  证明: (isRightKanExtension_iff_isIso ((((L.ranAdjunction H).homEquiv _ _) α))
    (L.ranCounit.app F) α (by simp [ranAdjunction])).symm

Depends on / 依赖: L.ranAdjunction, L.ranCounit.app, homEquiv, isRightKanExtension_iff_isIso, ranAdjunction, ranCounit
-/
lemma isIso_ranAdjunction_homEquiv_iff {F : C ⥤ H} {G : D ⥤ H} (α : L ⋙ G ⟶ F) :
    IsIso (((L.ranAdjunction H).homEquiv _ _) α) ↔ G.IsRightKanExtension α :=
  (isRightKanExtension_iff_isIso ((((L.ranAdjunction H).homEquiv _ _) α))
    (L.ranCounit.app F) α (by simp [ranAdjunction])).symm

/-- Composing the right Kan extension of `L : C ⥤ D` with `lim` on shapes `D` is isomorphic
to `lim` on shapes `C`. -/
@[simps!]
/--
Definition of `ranCompLimIso` / `ranCompLimIso` 的定义

English:
definition ranCompLimIso
  signature: (L : C ⥤ D) [forall (G : C ⥤ H), L.HasRightKanExtension G]
  body: NatIso.ofComponents
    (fun G => limitIsoOfIsRightKanExtension _ (L.ranCounit.app G))
    (fun f => limit.hom_ext (fun i => by
      dsimp
      rw [assoc]; rw [assoc]; rw [limMap_π]; rw [limitIsoOfIsRightKanExtension_hom_π_assoc]; rw [limitIsoOfIsRightKanExtension_hom_π]; rw [limMap_π_assoc]
     

中文:
定义 ranCompLimIso
  签名: (L : C ⥤ D) [对任意 (G : C ⥤ H), L.HasRightKanExtension G]
  定义体: NatIso.ofComponents
    (fun G => limitIsoOfIsRightKanExtension _ (L.ranCounit.app G))
    (fun f => limit.hom_ext (fun i => by
      dsimp
      rw [assoc]; rw [assoc]; rw [limMap_π]; rw [limitIsoOfIsRightKanExtension_hom_π_assoc]; rw [limitIsoOfIsRightKanExtension_hom_π]; rw [limMap_π_assoc]
     
-/
noncomputable def ranCompLimIso (L : C ⥤ D) [forall (G : C ⥤ H), L.HasRightKanExtension G]
    [HasLimitsOfShape C H] [HasLimitsOfShape D H] : L.ran ⋙ lim ≅ lim (C := H) :=
  NatIso.ofComponents
    (fun G => limitIsoOfIsRightKanExtension _ (L.ranCounit.app G))
    (fun f => limit.hom_ext (fun i => by
      dsimp
      rw [assoc]; rw [assoc]; rw [limMap_π]; rw [limitIsoOfIsRightKanExtension_hom_π_assoc]; rw [limitIsoOfIsRightKanExtension_hom_π]; rw [limMap_π_assoc]
      congr 1
      exact congr_app (L.ranCounit.naturality f) i))

end

section

variable [Full L] [Faithful L]

instance (F : C ⥤ H) (X : C) [HasPointwiseRightKanExtension L F]
    [forall (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranCounit.app F).app X) :=
  (isPointwiseRightKanExtensionRanCounit L F (L.obj X)).isIso_hom_app

instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [forall (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso (L.ranCounit.app F) :=
  NatIso.isIso_of_isIso_app _

/--
Instance `reflective` / 实例 `reflective`

English:
instance reflective
  signature: [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F]
  body: by
  apply NatIso.isIso_of_isIso_app _

中文:
实例 reflective
  签名: [对任意 (F : C ⥤ H), HasPointwiseRightKanExtension L F]
  定义体: by
  apply NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance reflective [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranCounit (H := H)) := by
  apply NatIso.isIso_of_isIso_app _

instance (F : C ⥤ H) [HasPointwiseRightKanExtension L F]
    [forall (F : C ⥤ H), HasRightKanExtension L F] :
    IsIso ((L.ranAdjunction H).counit.app F) := by
  rw [ranAdjunction_counit]
  infer_instance

/--
Instance `reflective'` / 实例 `reflective'`

English:
instance reflective'
  signature: [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F]
  body: by
  apply NatIso.isIso_of_isIso_app _

中文:
实例 reflective'
  签名: [对任意 (F : C ⥤ H), HasPointwiseRightKanExtension L F]
  定义体: by
  apply NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance reflective' [forall (F : C ⥤ H), HasPointwiseRightKanExtension L F] :
    IsIso (L.ranAdjunction H).counit := by
  apply NatIso.isIso_of_isIso_app _

end

end ran

end Functor

end CategoryTheory
