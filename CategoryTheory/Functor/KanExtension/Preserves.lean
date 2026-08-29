/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preservation of Kan extensions

Given functors `F : A ⥤ B`, `L : B ⥤ C`, and `G : B ⥤ D`,
we introduce a typeclass `G.PreservesLeftKanExtension F L` which encodes the fact that
the left Kan extension of `F` along `L` is preserved by the functor `G`.

When the Kan extension is pointwise, it suffices that `G` preserves (co)limits of the relevant
diagrams.

We introduce the dual typeclass `G.PreservesRightKanExtension`.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  (G : B ⥤ D) (F : A ⥤ B) (L : A ⥤ C)

noncomputable section

section LeftKanExtension

/--
Definition of `PreservesLeftKanExtension` / `PreservesLeftKanExtension` 的定义

English:
class PreservesLeftKanExtension
  parameters: where
  axioms and operations (1):
    - preserves : forall (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],

中文:
类 保持LeftKanExtension
  参数: where
  公理与运算 (1 个):
    - preserves : 对任意 (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [是LeftKanExtension F' α],
-/
class PreservesLeftKanExtension where
  preserves : forall (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α],
IsLeftKanExtension (F' ⋙ G) whiskerRight α G ≫ (Functor.associator _ _ _).hom

/--
lemma `PreservesLeftKanExtension.mk'` / 引理 `PreservesLeftKanExtension.mk'`

English:
lemma PreservesLeftKanExtension.mk'
  proof: ⟨⟨Limits.IsInitial.equivOfIso
(LeftExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

中文:
引理 保持LeftKanExtension.mk'
  证明: ⟨⟨Limits.IsInitial.equivOfIso
(LeftExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

Depends on / 依赖: IsInitial, LeftExtension, LeftExtension.postcompose, Limits, Limits.IsInitial.equivOfIso, equivOfIso, h.nonempty_isUniversal.some, nonempty_isUniversal, preserves
-/
lemma PreservesLeftKanExtension.mk'
    (preserves : forall {E : LeftExtension L F}, E.IsUniversal ->
      Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L where
  preserves _ _ h :=
    ⟨⟨Limits.IsInitial.equivOfIso
(LeftExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

/--
lemma `PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension` / 引理 `PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension`

English:
lemma PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension
  proof: .mk fun F'' α' h =>
    isLeftKanExtension_of_iso
      (isoWhiskerRight (leftKanExtensionUnique F' α F'' α') G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (whiskerRight α' G ≫ (Functor.associator _ _ _).hom)
      (by ext x; simp [← G.map_comp])

中文:
引理 保持LeftKanExtension.mk_of_preserves_isLeftKanExtension
  证明: .mk fun F'' α' h =>
    isLeftKanExtension_of_iso
      (isoWhiskerRight (leftKanExtensionUnique F' α F'' α') G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (whiskerRight α' G ≫ (Functor.associator _ _ _).hom)
      (by ext x; simp [← G.map_comp])

Depends on / 依赖: Functor, Functor.associator, G.map_comp, associator, isLeftKanExtension_of_iso, isoWhiskerRight, leftKanExtensionUnique, map_comp, whiskerRight
-/
lemma PreservesLeftKanExtension.mk_of_preserves_isLeftKanExtension
    (F' : C ⥤ B) (α : F ⟶ L ⋙ F') [IsLeftKanExtension F' α]
    (h : IsLeftKanExtension (F' ⋙ G) <| whiskerRight α G ≫ (Functor.associator _ _ _).hom) :
    G.PreservesLeftKanExtension F L :=
  .mk fun F'' α' h =>
    isLeftKanExtension_of_iso
      (isoWhiskerRight (leftKanExtensionUnique F' α F'' α') G)
      (whiskerRight α G ≫ (Functor.associator _ _ _).hom)
      (whiskerRight α' G ≫ (Functor.associator _ _ _).hom)
      (by ext x; simp [← G.map_comp])

/--
lemma `PreservesLeftKanExtension.mk_of_preserves_isUniversal` / 引理 `PreservesLeftKanExtension.mk_of_preserves_isUniversal`

English:
lemma PreservesLeftKanExtension.mk_of_preserves_isUniversal
  statement: (E : LeftExtension L F)
  proof: .mk' G F L fun hE' =>
    ⟨Limits.IsInitial.equivOfIso
      (LeftExtension.postcompose₂ L F G|>.mapIso <| Limits.IsInitial.uniqueUpToIso hE hE') h.some⟩

中文:
引理 保持LeftKanExtension.mk_of_preserves_isUniversal
  结论: (E : LeftExtension L F)
  证明: .mk' G F L fun hE' =>
    ⟨Limits.IsInitial.equivOfIso
      (LeftExtension.postcompose₂ L F G|>.mapIso <| Limits.IsInitial.uniqueUpToIso hE hE') h.some⟩

Depends on / 依赖: IsInitial, LeftExtension, LeftExtension.postcompose, Limits, Limits.IsInitial.equivOfIso, Limits.IsInitial.uniqueUpToIso, equivOfIso, h.some, mapIso, uniqueUpToIso
-/
lemma PreservesLeftKanExtension.mk_of_preserves_isUniversal (E : LeftExtension L F)
    (hE : E.IsUniversal) (h : Nonempty (LeftExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesLeftKanExtension F L :=
  .mk' G F L fun hE' =>
    ⟨Limits.IsInitial.equivOfIso
      (LeftExtension.postcompose₂ L F G|>.mapIso <| Limits.IsInitial.uniqueUpToIso hE hE') h.some⟩

attribute [instance] PreservesLeftKanExtension.preserves

/--
Definition of `PreservesPointwiseLeftKanExtensionAt` / `PreservesPointwiseLeftKanExtensionAt` 的定义

English:
class PreservesPointwiseLeftKanExtensionAt
  parameters: (c : C)
  axioms and operations (1):
    - preserves : forall (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c -> Nonempty ((LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c)

中文:
类 保持PointwiseLeftKanExtensionAt
  参数: (c : C)
  公理与运算 (1 个):
    - preserves : 对任意 (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c -> 非空 ((LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c)
-/
class PreservesPointwiseLeftKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : forall (E : LeftExtension L F), E.IsPointwiseLeftKanExtensionAt c ->
    Nonempty ((LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c)

/--
Definition of `PreservesPointwiseLeftKanExtension` / `PreservesPointwiseLeftKanExtension` 的定义

English:
abbreviation PreservesPointwiseLeftKanExtension
  body: forall c : C, PreservesPointwiseLeftKanExtensionAt G F L c

中文:
缩写 PreservesPointwiseLeftKanExtension
  定义体: forall c : C, PreservesPointwiseLeftKanExtensionAt G F L c

Depends on / 依赖: PreservesPointwiseLeftKanExtensionAt
-/
abbrev PreservesPointwiseLeftKanExtension := forall c : C, PreservesPointwiseLeftKanExtensionAt G F L c

variable {F L} in
/--
Definition of `LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose` / `LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose` 的定义

English:
definition LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose
  signature: {c : C}
  body: .obj E LeftExtension.postcompose₂ L F G
.some PreservesPointwiseLeftKanExtensionAt.preserves E hE

中文:
定义 LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose
  签名: {c : C}
  定义体: .obj E LeftExtension.postcompose₂ L F G
.some PreservesPointwiseLeftKanExtensionAt.preserves E hE

Depends on / 依赖: Hom.id, LeftExtension, LeftExtension.postcompose
-/
def LeftExtension.IsPointwiseLeftKanExtensionAt.postcompose {c : C}
    [PreservesPointwiseLeftKanExtensionAt G F L c]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtensionAt c) :
.IsPointwiseLeftKanExtensionAt c := .obj E LeftExtension.postcompose₂ L F G
.some PreservesPointwiseLeftKanExtensionAt.preserves E hE

variable {F L} in
/--
Definition of `LeftExtension.IsPointwiseLeftKanExtension.postcompose` / `LeftExtension.IsPointwiseLeftKanExtension.postcompose` 的定义

English:
definition LeftExtension.IsPointwiseLeftKanExtension.postcompose
  body: fun c => .obj E LeftExtension.postcompose₂ L F G
  (hE c).postcompose G

中文:
定义 LeftExtension.IsPointwiseLeftKanExtension.postcompose
  定义体: fun c => .obj E LeftExtension.postcompose₂ L F G
  (hE c).postcompose G

Depends on / 依赖: LeftExtension, LeftExtension.postcompose
-/
def LeftExtension.IsPointwiseLeftKanExtension.postcompose
    [PreservesPointwiseLeftKanExtension G F L]
    {E : LeftExtension L F} (hE : E.IsPointwiseLeftKanExtension) :
.IsPointwiseLeftKanExtension := fun c => .obj E LeftExtension.postcompose₂ L F G
  (hE c).postcompose G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cocone at a point of the whiskering right by `G` of an extension is isomorphic to the
action of `G` on the cocone at that point for the original extension. -/
@[simps!]
/--
Definition of `LeftExtension.coconeAtWhiskerRightIso` / `LeftExtension.coconeAtWhiskerRightIso` 的定义

English:
definition LeftExtension.coconeAtWhiskerRightIso
  signature: (E : LeftExtension L F) (c : C)
  body: Limits.Cocone.ext (Iso.refl _)

中文:
定义 LeftExtension.coconeAtWhiskerRightIso
  签名: (E : LeftExtension L F) (c : C)
  定义体: Limits.Cocone.ext (Iso.refl _)

Depends on / 依赖: Cocone, Iso.refl, Limits, Limits.Cocone.ext
-/
def LeftExtension.coconeAtWhiskerRightIso (E : LeftExtension L F) (c : C) :
    (LeftExtension.postcompose₂ L F G |>.obj E).coconeAt c ≅ G.mapCocone (E.coconeAt c) :=
  Limits.Cocone.ext (Iso.refl _)

/--
lemma `PreservesPointwiseLeftKanExtensionAt.mk'` / 引理 `PreservesPointwiseLeftKanExtensionAt.mk'`

English:
lemma PreservesPointwiseLeftKanExtensionAt.mk'
  statement: (c : C) {E : LeftExtension L F}
  proof: ⟨Limits.IsColimit.ofIsoColimit hGE
      (E.coconeAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cocone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coconeAtWhiskerRightIso G F L c).symm⟩

中文:
引理 保持PointwiseLeftKanExtensionAt.mk'
  结论: (c : C) {E : LeftExtension L F}
  证明: ⟨Limits.IsColimit.ofIsoColimit hGE
      (E.coconeAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cocone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coconeAtWhiskerRightIso G F L c).symm⟩

Depends on / 依赖: Cocone, E.coconeAtWhiskerRightIso, IsColimit, Limits, Limits.Cocone.functoriality, Limits.IsColimit.ofIsoColimit, coconeAtWhiskerRightIso, functoriality, hE.uniqueUpToIso, mapIso, ofIsoColimit, uniqueUpToIso
-/
lemma PreservesPointwiseLeftKanExtensionAt.mk' (c : C) {E : LeftExtension L F}
    (hE : E.IsPointwiseLeftKanExtensionAt c)
    (hGE : (LeftExtension.postcompose₂ L F G |>.obj E).IsPointwiseLeftKanExtensionAt c) :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E' hE' :=
⟨Limits.IsColimit.ofIsoColimit hGE
      (E.coconeAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cocone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coconeAtWhiskerRightIso G F L c).symm⟩

/--
Instance `hasLeftKanExtension_of_preserves` / 实例 `hasLeftKanExtension_of_preserves`

English:
instance hasLeftKanExtension_of_preserves
  signature: [L.HasLeftKanExtension F]
  body: @HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.leftKanExtension F).IsLeftKanExtension L.leftKanExtensionUnit F := by
      infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)

中文:
实例 hasLeftKanExtension_of_preserves
  签名: [L.有LeftKanExtension F]
  定义体: @HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.leftKanExtension F).IsLeftKanExtension L.leftKanExtensionUnit F := by
      infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)

Depends on / 依赖: HasLeftKanExtension, HasLeftKanExtension.mk, IsLeftKanExtension, L.leftKanExtension, L.leftKanExtensionUnit, PreservesLeftKanExtension, PreservesLeftKanExtension.preserves, infer_instance, leftKanExtension, leftKanExtensionUnit, preserves
-/
instance hasLeftKanExtension_of_preserves [L.HasLeftKanExtension F]
    [PreservesLeftKanExtension G F L] : L.HasLeftKanExtension (F ⋙ G) :=
@HasLeftKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.leftKanExtension F).IsLeftKanExtension L.leftKanExtensionUnit F := by
      infer_instance
    PreservesLeftKanExtension.preserves (L.leftKanExtension F) (L.leftKanExtensionUnit F)

/--
Instance `hasPointwiseLeftKanExtension_of_preserves` / 实例 `hasPointwiseLeftKanExtension_of_preserves`

English:
instance hasPointwiseLeftKanExtension_of_preserves
  signature: [L.HasPointwiseLeftKanExtension F]
  body: (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
.postcompose G).hasPointwiseLeftKanExtension L F

中文:
实例 hasPointwiseLeftKanExtension_of_preserves
  签名: [L.HasPointwiseLeftKanExtension F]
  定义体: (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
.postcompose G).hasPointwiseLeftKanExtension L F

Depends on / 依赖: hasPointwiseLeftKanExtension, pointwiseLeftKanExtensionIsPointwiseLeftKanExtension, postcompose
-/
instance hasPointwiseLeftKanExtension_of_preserves [L.HasPointwiseLeftKanExtension F]
    [PreservesPointwiseLeftKanExtension G F L] : L.HasPointwiseLeftKanExtension (F ⋙ G) :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
.postcompose G).hasPointwiseLeftKanExtension L F

/--
Definition of `leftKanExtensionCompIsoOfPreserves` / `leftKanExtensionCompIsoOfPreserves` 的定义

English:
definition leftKanExtensionCompIsoOfPreserves
  signature: [PreservesLeftKanExtension G F L]
  body: leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

中文:
定义 leftKanExtensionCompIsoOfPreserves
  签名: [保持LeftKanExtension G F L]
  定义体: leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

Depends on / 依赖: Functor, Functor.associator, L.leftKanExtension, L.leftKanExtensionUnit, associator, leftKanExtension, leftKanExtensionUnique, leftKanExtensionUnit, whiskerRight
-/
def leftKanExtensionCompIsoOfPreserves [PreservesLeftKanExtension G F L]
    [L.HasLeftKanExtension F] :
    L.leftKanExtension F ⋙ G ≅ L.leftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.leftKanExtension F ⋙ G)
    (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.leftKanExtension <| F ⋙ G)
    (L.leftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesLeftKanExtension G F L] [L.HasLeftKanExtension F]

@[reassoc (attr := simp)]
/--
lemma `leftKanExtensionCompIsoOfPreserves_hom_fac` / 引理 `leftKanExtensionCompIsoOfPreserves_hom_fac`

English:
lemma leftKanExtensionCompIsoOfPreserves_hom_fac
  proof: by
  simpa [leftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.leftKanExtensionUnit (F ⋙ G))

中文:
引理 leftKanExtensionCompIsoOfPreserves_hom_fac
  证明: by
  simpa [leftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.leftKanExtensionUnit (F ⋙ G))

Depends on / 依赖: Functor, Functor.associator, L.leftKanExtensionUnit, associator, descOfIsLeftKanExtension_fac, leftKanExtensionCompIsoOfPreserves, leftKanExtensionUnit, whiskerRight
-/
lemma leftKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.leftKanExtensionUnit <| F ⋙ G) := by
  simpa [leftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.leftKanExtensionUnit (F ⋙ G))

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `leftKanExtensionCompIsoOfPreserves_hom_fac_app` / 引理 `leftKanExtensionCompIsoOfPreserves_hom_fac_app`

English:
lemma leftKanExtensionCompIsoOfPreserves_hom_fac_app
  given: (a : A)
  proof: by
  simpa [-leftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

中文:
引理 leftKanExtensionCompIsoOfPreserves_hom_fac_app
  条件: (a : A)
  证明: by
  simpa [-leftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

Depends on / 依赖: Hom.id, NatTrans, NatTrans.congr_app, congr_app, leftKanExtensionCompIsoOfPreserves_hom_fac
-/
lemma leftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    G.map ((L.leftKanExtensionUnit F).app a) ≫
      (G.leftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.leftKanExtensionUnit (F ⋙ G)).app a := by
  simpa [-leftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/--
lemma `leftKanExtensionCompIsoOfPreserves_inv_fac` / 引理 `leftKanExtensionCompIsoOfPreserves_inv_fac`

English:
lemma leftKanExtensionCompIsoOfPreserves_inv_fac
  proof: by
  simp [leftKanExtensionCompIsoOfPreserves]

中文:
引理 leftKanExtensionCompIsoOfPreserves_inv_fac
  证明: by
  simp [leftKanExtensionCompIsoOfPreserves]

Depends on / 依赖: leftKanExtensionCompIsoOfPreserves
-/
lemma leftKanExtensionCompIsoOfPreserves_inv_fac :
    (L.leftKanExtensionUnit <| F ⋙ G) ≫
      whiskerLeft L (leftKanExtensionCompIsoOfPreserves G F L).inv =
    whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom := by
  simp [leftKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `leftKanExtensionCompIsoOfPreserves_inv_fac_app` / 引理 `leftKanExtensionCompIsoOfPreserves_inv_fac_app`

English:
lemma leftKanExtensionCompIsoOfPreserves_inv_fac_app
  given: (a : A)
  proof: by
  simpa [-leftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

中文:
引理 leftKanExtensionCompIsoOfPreserves_inv_fac_app
  条件: (a : A)
  证明: by
  simpa [-leftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, leftKanExtensionCompIsoOfPreserves_inv_fac
-/
lemma leftKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (L.leftKanExtensionUnit (F ⋙ G)).app a ≫
      (G.leftKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) =
    G.map ((L.leftKanExtensionUnit F).app a) := by
  simpa [-leftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (leftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/--
Instance `preservesPointwiseLeftKanExtensionAtOfPreservesColimit` / 实例 `preservesPointwiseLeftKanExtensionAtOfPreservesColimit`

English:
instance preservesPointwiseLeftKanExtensionAtOfPreservesColimit
  signature: (c : C)
  body: ⟨Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (E.coconeAtWhiskerRightIso G _ _ c).symm⟩

中文:
实例 preservesPointwiseLeftKanExtensionAtOfPreservesColimit
  签名: (c : C)
  定义体: ⟨Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (E.coconeAtWhiskerRightIso G _ _ c).symm⟩

Depends on / 依赖: E.coconeAtWhiskerRightIso, IsColimit, Limits, Limits.IsColimit.ofIsoColimit, Limits.PreservesColimit.preserves, PreservesColimit, coconeAtWhiskerRightIso, ofIsoColimit, preserves
-/
instance preservesPointwiseLeftKanExtensionAtOfPreservesColimit (c : C)
    [Limits.PreservesColimit (CostructuredArrow.proj L c ⋙ F) G] :
    G.PreservesPointwiseLeftKanExtensionAt F L c where
  preserves E p :=
    ⟨Limits.IsColimit.ofIsoColimit
      (Limits.PreservesColimit.preserves p).some
      (E.coconeAtWhiskerRightIso G _ _ c).symm⟩

/--
Instance `preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise` / 实例 `preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise`

English:
instance preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
  body: (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso (LeftExtension.postcompose₂ObjMkIso G α) <|
      (isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α).postcompose G).isLeftKanExtension

中文:
实例 preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
  定义体: (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso (LeftExtension.postcompose₂ObjMkIso G α) <|
      (isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α).postcompose G).isLeftKanExtension

Depends on / 依赖: LeftExtension, LeftExtension.isPointwiseLeftKanExtensionEquivOfIso, LeftExtension.postcompose, isLeftKanExtension, isPointwiseLeftKanExtensionEquivOfIso, isPointwiseLeftKanExtensionOfIsLeftKanExtension, postcompose
-/
instance preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseLeftKanExtension L F] [G.PreservesPointwiseLeftKanExtension F L] :
    G.PreservesLeftKanExtension F L where
  preserves F' α _ :=
    (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso (LeftExtension.postcompose₂ObjMkIso G α) <|
      (isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α).postcompose G).isLeftKanExtension

/--
Definition of `pointwiseLeftKanExtensionCompIsoOfPreserves` / `pointwiseLeftKanExtensionCompIsoOfPreserves` 的定义

English:
definition pointwiseLeftKanExtensionCompIsoOfPreserves
  body: leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

中文:
定义 pointwiseLeftKanExtensionCompIsoOfPreserves
  定义体: leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

Depends on / 依赖: Functor, Functor.associator, L.pointwiseLeftKanExtension, L.pointwiseLeftKanExtensionUnit, associator, leftKanExtensionUnique, pointwiseLeftKanExtension, pointwiseLeftKanExtensionUnit, whiskerRight
-/
def pointwiseLeftKanExtensionCompIsoOfPreserves
    [PreservesPointwiseLeftKanExtension G F L]
    [L.HasPointwiseLeftKanExtension F] :
    L.pointwiseLeftKanExtension F ⋙ G ≅ L.pointwiseLeftKanExtension (F ⋙ G) :=
  leftKanExtensionUnique
    (L.pointwiseLeftKanExtension F ⋙ G)
    (whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
    (L.pointwiseLeftKanExtension <| F ⋙ G)
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

section

variable [PreservesPointwiseLeftKanExtension G F L] [L.HasPointwiseLeftKanExtension F]

@[reassoc (attr := simp)]
/--
lemma `pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac` / 引理 `pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac`

English:
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac
  proof: by
  simpa [pointwiseLeftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

中文:
引理 pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac
  证明: by
  simpa [pointwiseLeftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

Depends on / 依赖: Functor, Functor.associator, IsEmpty, L.pointwiseLeftKanExtensionUnit, associator, descOfIsLeftKanExtension_fac, infer_instance, pointwiseLeftKanExtensionCompIsoOfPreserves, pointwiseLeftKanExtensionUnit, whiskerRight
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreserves G F L).hom =
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G) := by
  simpa [pointwiseLeftKanExtensionCompIsoOfPreserves] using
    descOfIsLeftKanExtension_fac
      (α := whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      (β := L.pointwiseLeftKanExtensionUnit <| F ⋙ G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app` / 引理 `pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app`

English:
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app
  given: (a : A)
  proof: by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

中文:
引理 pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app
  条件: (a : A)
  证明: by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

Depends on / 依赖: IsEmpty, NatTrans, NatTrans.congr_app, congr_app, infer_instance, pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    G.map ((L.pointwiseLeftKanExtensionUnit F).app a) ≫
      (G.pointwiseLeftKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) =
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G).app a := by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/--
lemma `pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac` / 引理 `pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac`

English:
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac
  proof: by
  simp [pointwiseLeftKanExtensionCompIsoOfPreserves]

中文:
引理 pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac
  证明: by
  simp [pointwiseLeftKanExtensionCompIsoOfPreserves]

Depends on / 依赖: pointwiseLeftKanExtensionCompIsoOfPreserves
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac :
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G) ≫
      whiskerLeft L (pointwiseLeftKanExtensionCompIsoOfPreserves G F L).inv =
    whiskerRight (L.pointwiseLeftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom := by
  simp [pointwiseLeftKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app` / 引理 `pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app`

English:
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app
  given: (a : A)
  proof: by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

中文:
引理 pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app
  条件: (a : A)
  证明: by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac
-/
lemma pointwiseLeftKanExtensionCompIsoOfPreserves_fac_app (a : A) :
    (L.pointwiseLeftKanExtensionUnit <| F ⋙ G).app a ≫
      (G.pointwiseLeftKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) =
    G.map (L.pointwiseLeftKanExtensionUnit F |>.app a) := by
  simpa [-pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseLeftKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/--
Definition of `PreservesLeftKanExtensions` / `PreservesLeftKanExtensions` 的定义

English:
abbreviation PreservesLeftKanExtensions
  body: forall (F : A ⥤ B), G.PreservesLeftKanExtension F L

中文:
缩写 PreservesLeftKanExtensions
  定义体: forall (F : A ⥤ B), G.PreservesLeftKanExtension F L

Depends on / 依赖: G.PreservesLeftKanExtension, PreservesLeftKanExtension
-/
abbrev PreservesLeftKanExtensions := forall (F : A ⥤ B), G.PreservesLeftKanExtension F L

/--
Definition of `PreservesPointwiseLeftKanExtensions` / `PreservesPointwiseLeftKanExtensions` 的定义

English:
abbreviation PreservesPointwiseLeftKanExtensions
  body: forall (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

中文:
缩写 PreservesPointwiseLeftKanExtensions
  定义体: forall (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

Depends on / 依赖: G.PreservesPointwiseLeftKanExtension, PreservesPointwiseLeftKanExtension
-/
abbrev PreservesPointwiseLeftKanExtensions :=
  forall (F : A ⥤ B), G.PreservesPointwiseLeftKanExtension F L

set_option backward.defeqAttrib.useBackward true in
/-- Commuting a functor that preserves left Kan extensions with the `lan` functor. -/
@[simps!]
/--
Definition of `lanCompIsoOfPreserves` / `lanCompIsoOfPreserves` 的定义

English:
definition lanCompIsoOfPreserves
  signature: [G.PreservesLeftKanExtensions L]
  body: NatIso.ofComponents (fun F => leftKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isLeftKanExtension (L.leftKanExtension F ⋙ G)
        (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      dsimp [lan]
      ext
      simp [← G.map_comp_assoc])

中文:
定义 lanCompIsoOfPreserves
  签名: [G.PreservesLeftKanExtensions L]
  定义体: NatIso.ofComponents (fun F => leftKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isLeftKanExtension (L.leftKanExtension F ⋙ G)
        (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      dsimp [lan]
      ext
      simp [← G.map_comp_assoc])

Depends on / 依赖: Functor, Functor.associator, G.map_comp_assoc, L.leftKanExtension, L.leftKanExtensionUnit, NatIso, NatIso.ofComponents, associator, hom_ext_of_isLeftKanExtension, leftKanExtension, leftKanExtensionCompIsoOfPreserves, leftKanExtensionUnit, map_comp_assoc, ofComponents, whiskerRight
-/
def lanCompIsoOfPreserves [G.PreservesLeftKanExtensions L]
    [forall F : A ⥤ B, HasLeftKanExtension L F]
    [forall F : A ⥤ D, HasLeftKanExtension L F] :
    L.lan ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.lan :=
  NatIso.ofComponents (fun F => leftKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isLeftKanExtension (L.leftKanExtension F ⋙ G)
        (whiskerRight (L.leftKanExtensionUnit F) G ≫ (Functor.associator _ _ _).hom)
      dsimp [lan]
      ext
      simp [← G.map_comp_assoc])

end LeftKanExtension

section RightKanExtension

/--
Definition of `PreservesRightKanExtension` / `PreservesRightKanExtension` 的定义

English:
class PreservesRightKanExtension
  parameters: where
  axioms and operations (1):
    - preserves : forall (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α],

中文:
类 保持RightKanExtension
  参数: where
  公理与运算 (1 个):
    - preserves : 对任意 (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [是RightKanExtension F' α],
-/
class PreservesRightKanExtension where
  preserves : forall (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α],
IsRightKanExtension (F' ⋙ G) (Functor.associator _ _ _).inv ≫ whiskerRight α G

/--
lemma `PreservesRightKanExtension.mk'` / 引理 `PreservesRightKanExtension.mk'`

English:
lemma PreservesRightKanExtension.mk'
  proof: ⟨⟨Limits.IsTerminal.equivOfIso
(RightExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

中文:
引理 保持RightKanExtension.mk'
  证明: ⟨⟨Limits.IsTerminal.equivOfIso
(RightExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.equivOfIso, RightExtension, RightExtension.postcompose, equivOfIso, h.nonempty_isUniversal.some, nonempty_isUniversal, preserves
-/
lemma PreservesRightKanExtension.mk'
    (preserves : forall {E : RightExtension L F}, E.IsUniversal ->
      Nonempty (RightExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesRightKanExtension F L where
  preserves _ _ h :=
    ⟨⟨Limits.IsTerminal.equivOfIso
(RightExtension.postcompose₂ObjMkIso _ _) (preserves h.nonempty_isUniversal.some).some⟩⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `PreservesRightKanExtension.mk_of_preserves_isRightKanExtension` / 引理 `PreservesRightKanExtension.mk_of_preserves_isRightKanExtension`

English:
lemma PreservesRightKanExtension.mk_of_preserves_isRightKanExtension
  proof: .mk fun F'' α' h =>
    isRightKanExtension_of_iso
      (isoWhiskerRight (rightKanExtensionUnique F' α F'' α') G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α' G)
      (by ext x; simp [← G.map_comp])

中文:
引理 保持RightKanExtension.mk_of_preserves_isRightKanExtension
  证明: .mk fun F'' α' h =>
    isRightKanExtension_of_iso
      (isoWhiskerRight (rightKanExtensionUnique F' α F'' α') G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α' G)
      (by ext x; simp [← G.map_comp])

Depends on / 依赖: Functor, Functor.associator, G.map_comp, associator, isRightKanExtension_of_iso, isoWhiskerRight, map_comp, rightKanExtensionUnique, whiskerRight
-/
lemma PreservesRightKanExtension.mk_of_preserves_isRightKanExtension
    (F' : C ⥤ B) (α : L ⋙ F' ⟶ F) [IsRightKanExtension F' α]
    (h : IsRightKanExtension (F' ⋙ G) <| (Functor.associator _ _ _).inv ≫ whiskerRight α G) :
    G.PreservesRightKanExtension F L :=
  .mk fun F'' α' h =>
    isRightKanExtension_of_iso
      (isoWhiskerRight (rightKanExtensionUnique F' α F'' α') G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α G)
      ((Functor.associator _ _ _).inv ≫ whiskerRight α' G)
      (by ext x; simp [← G.map_comp])

/--
lemma `PreservesRightKanExtension.mk_of_preserves_isUniversal` / 引理 `PreservesRightKanExtension.mk_of_preserves_isUniversal`

English:
lemma PreservesRightKanExtension.mk_of_preserves_isUniversal
  statement: (E : RightExtension L F)
  proof: .mk' G F L fun hE' =>
    ⟨Limits.IsTerminal.equivOfIso
      (RightExtension.postcompose₂ L F G |>.mapIso
 Limits.IsTerminal.uniqueUpToIso hE hE') h.some⟩

中文:
引理 保持RightKanExtension.mk_of_preserves_isUniversal
  结论: (E : RightExtension L F)
  证明: .mk' G F L fun hE' =>
    ⟨Limits.IsTerminal.equivOfIso
      (RightExtension.postcompose₂ L F G |>.mapIso
 Limits.IsTerminal.uniqueUpToIso hE hE') h.some⟩

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.equivOfIso, Limits.IsTerminal.uniqueUpToIso, RightExtension, RightExtension.postcompose, equivOfIso, h.some, mapIso, uniqueUpToIso
-/
lemma PreservesRightKanExtension.mk_of_preserves_isUniversal (E : RightExtension L F)
    (hE : E.IsUniversal) (h : Nonempty (RightExtension.postcompose₂ L F G |>.obj E).IsUniversal) :
    G.PreservesRightKanExtension F L :=
  .mk' G F L fun hE' =>
    ⟨Limits.IsTerminal.equivOfIso
      (RightExtension.postcompose₂ L F G |>.mapIso
 Limits.IsTerminal.uniqueUpToIso hE hE') h.some⟩

attribute [instance] PreservesRightKanExtension.preserves

/--
Definition of `PreservesPointwiseRightKanExtensionAt` / `PreservesPointwiseRightKanExtensionAt` 的定义

English:
class PreservesPointwiseRightKanExtensionAt
  parameters: (c : C)
  axioms and operations (1):
    - preserves : forall (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c -> Nonempty ((RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c)

中文:
类 保持PointwiseRightKanExtensionAt
  参数: (c : C)
  公理与运算 (1 个):
    - preserves : 对任意 (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c -> 非空 ((RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c)
-/
class PreservesPointwiseRightKanExtensionAt (c : C) where
  /-- `G` preserves every pointwise extensions of `F` along `L` at `c`. -/
  preserves : forall (E : RightExtension L F), E.IsPointwiseRightKanExtensionAt c ->
    Nonempty ((RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c)

/--
Definition of `PreservesPointwiseRightKanExtension` / `PreservesPointwiseRightKanExtension` 的定义

English:
abbreviation PreservesPointwiseRightKanExtension
  body: forall c : C, PreservesPointwiseRightKanExtensionAt G F L c

中文:
缩写 PreservesPointwiseRightKanExtension
  定义体: forall c : C, PreservesPointwiseRightKanExtensionAt G F L c

Depends on / 依赖: PreservesPointwiseRightKanExtensionAt
-/
abbrev PreservesPointwiseRightKanExtension := forall c : C, PreservesPointwiseRightKanExtensionAt G F L c

variable {F L} in
/--
Definition of `RightExtension.IsPointwiseRightKanExtensionAt.postcompose` / `RightExtension.IsPointwiseRightKanExtensionAt.postcompose` 的定义

English:
definition RightExtension.IsPointwiseRightKanExtensionAt.postcompose
  signature: {c : C}
  body: .obj E RightExtension.postcompose₂ L F G
.some PreservesPointwiseRightKanExtensionAt.preserves E hE

中文:
定义 RightExtension.IsPointwiseRightKanExtensionAt.postcompose
  签名: {c : C}
  定义体: .obj E RightExtension.postcompose₂ L F G
.some PreservesPointwiseRightKanExtensionAt.preserves E hE

Depends on / 依赖: RightExtension, RightExtension.postcompose
-/
def RightExtension.IsPointwiseRightKanExtensionAt.postcompose {c : C}
    [PreservesPointwiseRightKanExtensionAt G F L c]
    {E : RightExtension L F} (hE : E.IsPointwiseRightKanExtensionAt c) :
.IsPointwiseRightKanExtensionAt c := .obj E RightExtension.postcompose₂ L F G
.some PreservesPointwiseRightKanExtensionAt.preserves E hE

variable {F L} in
/--
Definition of `RightExtension.IsPointwiseRightKanExtension.postcompose` / `RightExtension.IsPointwiseRightKanExtension.postcompose` 的定义

English:
definition RightExtension.IsPointwiseRightKanExtension.postcompose
  body: fun c => .obj E RightExtension.postcompose₂ L F G
  (hE c).postcompose G

中文:
定义 RightExtension.IsPointwiseRightKanExtension.postcompose
  定义体: fun c => .obj E RightExtension.postcompose₂ L F G
  (hE c).postcompose G

Depends on / 依赖: RightExtension, RightExtension.postcompose
-/
def RightExtension.IsPointwiseRightKanExtension.postcompose
    [PreservesPointwiseRightKanExtension G F L]
    {E : RightExtension L F} (hE : E.IsPointwiseRightKanExtension) :
.IsPointwiseRightKanExtension := fun c => .obj E RightExtension.postcompose₂ L F G
  (hE c).postcompose G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cone at a point of the whiskering right by `G` of an extension is isomorphic to the
action of `G` on the cone at that point for the original extension. -/
@[simps!]
/--
Definition of `RightExtension.coneAtWhiskerRightIso` / `RightExtension.coneAtWhiskerRightIso` 的定义

English:
definition RightExtension.coneAtWhiskerRightIso
  signature: (E : RightExtension L F) (c : C)
  body: Limits.Cone.ext (Iso.refl _)

中文:
定义 RightExtension.coneAtWhiskerRightIso
  签名: (E : RightExtension L F) (c : C)
  定义体: Limits.Cone.ext (Iso.refl _)

Depends on / 依赖: Iso.refl, Limits, Limits.Cone.ext
-/
def RightExtension.coneAtWhiskerRightIso (E : RightExtension L F) (c : C) :
    (RightExtension.postcompose₂ L F G |>.obj E).coneAt c ≅ G.mapCone (E.coneAt c) :=
  Limits.Cone.ext (Iso.refl _)

/--
lemma `PreservesPointwiseRightKanExtensionAt.mk'` / 引理 `PreservesPointwiseRightKanExtensionAt.mk'`

English:
lemma PreservesPointwiseRightKanExtensionAt.mk'
  statement: (c : C) {E : RightExtension L F}
  proof: ⟨Limits.IsLimit.ofIsoLimit hGE
      (E.coneAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coneAtWhiskerRightIso G F L c).symm⟩

中文:
引理 保持PointwiseRightKanExtensionAt.mk'
  结论: (c : C) {E : RightExtension L F}
  证明: ⟨Limits.IsLimit.ofIsoLimit hGE
      (E.coneAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coneAtWhiskerRightIso G F L c).symm⟩

Depends on / 依赖: E.coneAtWhiskerRightIso, IsLimit, Limits, Limits.Cone.functoriality, Limits.IsLimit.ofIsoLimit, coneAtWhiskerRightIso, functoriality, hE.uniqueUpToIso, mapIso, ofIsoLimit, uniqueUpToIso
-/
lemma PreservesPointwiseRightKanExtensionAt.mk' (c : C) {E : RightExtension L F}
    (hE : E.IsPointwiseRightKanExtensionAt c)
    (hGE : (RightExtension.postcompose₂ L F G |>.obj E).IsPointwiseRightKanExtensionAt c) :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E' hE' :=
⟨Limits.IsLimit.ofIsoLimit hGE
      (E.coneAtWhiskerRightIso G F L c) ≪≫
        (Limits.Cone.functoriality _ _).mapIso (hE.uniqueUpToIso hE') ≪≫
        (E'.coneAtWhiskerRightIso G F L c).symm⟩

/--
Instance `hasRightKanExtension_of_preserves` / 实例 `hasRightKanExtension_of_preserves`

English:
instance hasRightKanExtension_of_preserves
  signature: [L.HasRightKanExtension F]
  body: @HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.rightKanExtension F).IsRightKanExtension L.rightKanExtensionCounit F := by
      infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)

中文:
实例 hasRightKanExtension_of_preserves
  签名: [L.HasRightKanExtension F]
  定义体: @HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.rightKanExtension F).IsRightKanExtension L.rightKanExtensionCounit F := by
      infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)

Depends on / 依赖: HasRightKanExtension, HasRightKanExtension.mk, IsRightKanExtension, L.rightKanExtension, L.rightKanExtensionCounit, PreservesRightKanExtension, PreservesRightKanExtension.preserves, infer_instance, preserves, rightKanExtension, rightKanExtensionCounit
-/
instance hasRightKanExtension_of_preserves [L.HasRightKanExtension F]
    [PreservesRightKanExtension G F L] : L.HasRightKanExtension (F ⋙ G) :=
@HasRightKanExtension.mk _ _ _ _ _ _ _ _ _ _
letI : (L.rightKanExtension F).IsRightKanExtension L.rightKanExtensionCounit F := by
      infer_instance
    PreservesRightKanExtension.preserves (L.rightKanExtension F) (L.rightKanExtensionCounit F)

/--
Instance `hasPointwiseRightKanExtension_of_preserves` / 实例 `hasPointwiseRightKanExtension_of_preserves`

English:
instance hasPointwiseRightKanExtension_of_preserves
  signature: [L.HasPointwiseRightKanExtension F]
  body: (pointwiseRightKanExtensionIsPointwiseRightKanExtension
.postcompose G).hasPointwiseRightKanExtension L F

中文:
实例 hasPointwiseRightKanExtension_of_preserves
  签名: [L.HasPointwiseRightKanExtension F]
  定义体: (pointwiseRightKanExtensionIsPointwiseRightKanExtension
.postcompose G).hasPointwiseRightKanExtension L F

Depends on / 依赖: hasPointwiseRightKanExtension, pointwiseRightKanExtensionIsPointwiseRightKanExtension, postcompose
-/
instance hasPointwiseRightKanExtension_of_preserves [L.HasPointwiseRightKanExtension F]
    [PreservesPointwiseRightKanExtension G F L] : L.HasPointwiseRightKanExtension (F ⋙ G) :=
  (pointwiseRightKanExtensionIsPointwiseRightKanExtension
.postcompose G).hasPointwiseRightKanExtension L F

/--
Definition of `rightKanExtensionCompIsoOfPreserves` / `rightKanExtensionCompIsoOfPreserves` 的定义

English:
definition rightKanExtensionCompIsoOfPreserves
  signature: [PreservesRightKanExtension G F L]
  body: rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

中文:
定义 rightKanExtensionCompIsoOfPreserves
  签名: [保持RightKanExtension G F L]
  定义体: rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

Depends on / 依赖: Functor, Functor.associator, L.rightKanExtension, L.rightKanExtensionCounit, associator, rightKanExtension, rightKanExtensionCounit, rightKanExtensionUnique, whiskerRight
-/
def rightKanExtensionCompIsoOfPreserves [PreservesRightKanExtension G F L]
    [L.HasRightKanExtension F] :
    L.rightKanExtension F ⋙ G ≅ L.rightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.rightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G)
    (L.rightKanExtension <| F ⋙ G)
    (L.rightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesRightKanExtension G F L] [L.HasRightKanExtension F]

@[reassoc (attr := simp)]
/--
lemma `rightKanExtensionCompIsoOfPreserves_hom_fac` / 引理 `rightKanExtensionCompIsoOfPreserves_hom_fac`

English:
lemma rightKanExtensionCompIsoOfPreserves_hom_fac
  proof: by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]

中文:
引理 rightKanExtensionCompIsoOfPreserves_hom_fac
  证明: by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]

Depends on / 依赖: rightKanExtensionCompIsoOfPreserves
-/
lemma rightKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerLeft L (rightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.rightKanExtensionCounit <| F ⋙ G) =
    (Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G := by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
/--
lemma `rightKanExtensionCompIsoOfPreserves_hom_fac_app` / 引理 `rightKanExtensionCompIsoOfPreserves_hom_fac_app`

English:
lemma rightKanExtensionCompIsoOfPreserves_hom_fac_app
  given: (a : A)
  proof: by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]

中文:
引理 rightKanExtensionCompIsoOfPreserves_hom_fac_app
  条件: (a : A)
  证明: by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]

Depends on / 依赖: rightKanExtensionCompIsoOfPreserves
-/
lemma rightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    (G.rightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.rightKanExtensionCounit (F ⋙ G)).app a =
    G.map (L.rightKanExtensionCounit F |>.app a) := by
  simp [rightKanExtensionCompIsoOfPreserves]

@[reassoc (attr := simp)]
/--
lemma `rightKanExtensionCompIsoOfPreserves_inv_fac` / 引理 `rightKanExtensionCompIsoOfPreserves_inv_fac`

English:
lemma rightKanExtensionCompIsoOfPreserves_inv_fac
  proof: by
  simp [rightKanExtensionCompIsoOfPreserves]

中文:
引理 rightKanExtensionCompIsoOfPreserves_inv_fac
  证明: by
  simp [rightKanExtensionCompIsoOfPreserves]

Depends on / 依赖: rightKanExtensionCompIsoOfPreserves
-/
lemma rightKanExtensionCompIsoOfPreserves_inv_fac :
    whiskerLeft L (rightKanExtensionCompIsoOfPreserves G F L).inv ≫
      ((Functor.associator _ _ _).inv ≫ whiskerRight (L.rightKanExtensionCounit F) G) =
    (L.rightKanExtensionCounit <| F ⋙ G) := by
  simp [rightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `rightKanExtensionCompIsoOfPreserves_inv_fac_app` / 引理 `rightKanExtensionCompIsoOfPreserves_inv_fac_app`

English:
lemma rightKanExtensionCompIsoOfPreserves_inv_fac_app
  given: (a : A)
  proof: by
  simpa [-rightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (rightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

中文:
引理 rightKanExtensionCompIsoOfPreserves_inv_fac_app
  条件: (a : A)
  证明: by
  simpa [-rightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (rightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, rightKanExtensionCompIsoOfPreserves_inv_fac
-/
lemma rightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (G.rightKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) ≫
      G.map (L.rightKanExtensionCounit F |>.app a) =
    (L.rightKanExtensionCounit (F ⋙ G)).app a := by
  simpa [-rightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (rightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/--
Instance `preservesPointwiseRightKanExtensionAtOfPreservesLimit` / 实例 `preservesPointwiseRightKanExtensionAtOfPreservesLimit`

English:
instance preservesPointwiseRightKanExtensionAtOfPreservesLimit
  signature: (c : C)
  body: ⟨Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (E.coneAtWhiskerRightIso G _ _ c).symm⟩

中文:
实例 preservesPointwiseRightKanExtensionAtOfPreservesLimit
  签名: (c : C)
  定义体: ⟨Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (E.coneAtWhiskerRightIso G _ _ c).symm⟩

Depends on / 依赖: E.coneAtWhiskerRightIso, IsLimit, Limits, Limits.IsLimit.ofIsoLimit, Limits.PreservesLimit.preserves, PreservesLimit, coneAtWhiskerRightIso, ofIsoLimit, preserves
-/
instance preservesPointwiseRightKanExtensionAtOfPreservesLimit (c : C)
    [Limits.PreservesLimit (StructuredArrow.proj c L ⋙ F) G] :
    G.PreservesPointwiseRightKanExtensionAt F L c where
  preserves E p :=
    ⟨Limits.IsLimit.ofIsoLimit
      (Limits.PreservesLimit.preserves p).some
      (E.coneAtWhiskerRightIso G _ _ c).symm⟩

/--
Instance `preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise` / 实例 `preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise`

English:
instance preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
  body: (RightExtension.isPointwiseRightKanExtensionEquivOfIso
(RightExtension.postcompose₂ObjMkIso G α)
        (isPointwiseRightKanExtensionOfIsRightKanExtension F' α).postcompose G).isRightKanExtension

中文:
实例 preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
  定义体: (RightExtension.isPointwiseRightKanExtensionEquivOfIso
(RightExtension.postcompose₂ObjMkIso G α)
        (isPointwiseRightKanExtensionOfIsRightKanExtension F' α).postcompose G).isRightKanExtension

Depends on / 依赖: RightExtension, RightExtension.isPointwiseRightKanExtensionEquivOfIso, RightExtension.postcompose, isPointwiseRightKanExtensionEquivOfIso, isPointwiseRightKanExtensionOfIsRightKanExtension, isRightKanExtension, postcompose
-/
instance preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    [HasPointwiseRightKanExtension L F] [G.PreservesPointwiseRightKanExtension F L] :
    G.PreservesRightKanExtension F L where
  preserves F' α _ :=
    (RightExtension.isPointwiseRightKanExtensionEquivOfIso
(RightExtension.postcompose₂ObjMkIso G α)
        (isPointwiseRightKanExtensionOfIsRightKanExtension F' α).postcompose G).isRightKanExtension

/--
Definition of `pointwiseRightKanExtensionCompIsoOfPreserves` / `pointwiseRightKanExtensionCompIsoOfPreserves` 的定义

English:
definition pointwiseRightKanExtensionCompIsoOfPreserves
  body: rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

中文:
定义 pointwiseRightKanExtensionCompIsoOfPreserves
  定义体: rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

Depends on / 依赖: Functor, Functor.associator, L.pointwiseRightKanExtension, L.pointwiseRightKanExtensionCounit, associator, pointwiseRightKanExtension, pointwiseRightKanExtensionCounit, rightKanExtensionUnique, whiskerRight
-/
def pointwiseRightKanExtensionCompIsoOfPreserves
    [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F] :
    L.pointwiseRightKanExtension F ⋙ G ≅ L.pointwiseRightKanExtension (F ⋙ G) :=
  rightKanExtensionUnique
    (L.pointwiseRightKanExtension F ⋙ G)
    ((Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G)
    (L.pointwiseRightKanExtension <| F ⋙ G)
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G)

section

variable [PreservesPointwiseRightKanExtension G F L]
    [L.HasPointwiseRightKanExtension F]

@[reassoc (attr := simp)]
/--
lemma `pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac` / 引理 `pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac`

English:
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac
  proof: by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

中文:
引理 pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac
  证明: by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

Depends on / 依赖: pointwiseRightKanExtensionCompIsoOfPreserves
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac :
    whiskerLeft L (pointwiseRightKanExtensionCompIsoOfPreserves G F L).hom ≫
      (L.pointwiseRightKanExtensionCounit <| F ⋙ G) =
    (Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G := by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app` / 引理 `pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app`

English:
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app
  given: (a : A)
  proof: by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

中文:
引理 pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app
  条件: (a : A)
  证明: by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac_app (a : A) :
    (G.pointwiseRightKanExtensionCompIsoOfPreserves F L).hom.app (L.obj a) ≫
      (L.pointwiseRightKanExtensionCounit <| F ⋙ G).app a =
    G.map (L.pointwiseRightKanExtensionCounit F |>.app a) := by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_hom_fac G F L) a

@[reassoc (attr := simp)]
/--
lemma `pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac` / 引理 `pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac`

English:
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac
  proof: by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

中文:
引理 pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac
  证明: by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

Depends on / 依赖: pointwiseRightKanExtensionCompIsoOfPreserves
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac :
    whiskerLeft L (pointwiseRightKanExtensionCompIsoOfPreserves G F L).inv ≫
      (Functor.associator _ _ _).inv ≫ whiskerRight (L.pointwiseRightKanExtensionCounit F) G =
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G) := by
  simp [pointwiseRightKanExtensionCompIsoOfPreserves]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app` / 引理 `pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app`

English:
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app
  given: (a : A)
  proof: by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

中文:
引理 pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app
  条件: (a : A)
  证明: by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac
-/
lemma pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac_app (a : A) :
    (G.pointwiseRightKanExtensionCompIsoOfPreserves F L).inv.app (L.obj a) ≫
      G.map (L.pointwiseRightKanExtensionCounit F |>.app a) =
    (L.pointwiseRightKanExtensionCounit <| F ⋙ G).app a := by
  simpa [-pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac] using
    NatTrans.congr_app (pointwiseRightKanExtensionCompIsoOfPreserves_inv_fac G F L) a

end

/--
Definition of `PreservesRightKanExtensions` / `PreservesRightKanExtensions` 的定义

English:
abbreviation PreservesRightKanExtensions
  body: forall (F : A ⥤ B), G.PreservesRightKanExtension F L

中文:
缩写 PreservesRightKanExtensions
  定义体: forall (F : A ⥤ B), G.PreservesRightKanExtension F L

Depends on / 依赖: G.PreservesRightKanExtension, PreservesRightKanExtension
-/
abbrev PreservesRightKanExtensions := forall (F : A ⥤ B), G.PreservesRightKanExtension F L

/--
Definition of `PreservesPointwiseRightKanExtensions` / `PreservesPointwiseRightKanExtensions` 的定义

English:
abbreviation PreservesPointwiseRightKanExtensions
  body: forall (F : A ⥤ B), G.PreservesPointwiseRightKanExtension F L

中文:
缩写 PreservesPointwiseRightKanExtensions
  定义体: forall (F : A ⥤ B), G.PreservesPointwiseRightKanExtension F L

Depends on / 依赖: G.PreservesPointwiseRightKanExtension, PreservesPointwiseRightKanExtension
-/
abbrev PreservesPointwiseRightKanExtensions :=
  forall (F : A ⥤ B), G.PreservesPointwiseRightKanExtension F L

set_option backward.defeqAttrib.useBackward true in
/-- Commuting a functor that preserves right Kan extensions with the `ran` functor. -/
@[simps!]
/--
Definition of `ranCompIsoOfPreserves` / `ranCompIsoOfPreserves` 的定义

English:
definition ranCompIsoOfPreserves
  signature: [G.PreservesRightKanExtensions L]
  body: NatIso.ofComponents (fun F => rightKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isRightKanExtension
        (L.rightKanExtension <| F' ⋙ G)
        (L.rightKanExtensionCounit <| F' ⋙ G)
      dsimp [ran]
      ext
      simp only [comp_obj, Category.assoc, rightKanExtensionCompIsoOfPreserves_hom_fac,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp,
        liftOfIsRightKanExtension_fac, rightKanExtensionCompIsoOfPreserves_hom_fac_assoc,
        ← G.map_comp]
      simp)

中文:
定义 ranCompIsoOfPreserves
  签名: [G.PreservesRightKanExtensions L]
  定义体: NatIso.ofComponents (fun F => rightKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isRightKanExtension
        (L.rightKanExtension <| F' ⋙ G)
        (L.rightKanExtensionCounit <| F' ⋙ G)
      dsimp [ran]
      ext
      simp only [comp_obj, Category.assoc, rightKanExtensionCompIsoOfPreserves_hom_fac,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp,
        liftOfIsRightKanExtension_fac, rightKanExtensionCompIsoOfPreserves_hom_fac_assoc,
        ← G.map_comp]
      simp)

Depends on / 依赖: Category, Category.assoc, Category.id_comp, G.map_comp, L.rightKanExtension, L.rightKanExtensionCounit, NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app, associator_inv_app, comp_app, comp_obj, hom_ext_of_isRightKanExtension, id_comp, liftOfIsRightKanExtension_fac, map_comp, ofComponents, rightKanExtension, rightKanExtensionCompIsoOfPreserves
-/
def ranCompIsoOfPreserves [G.PreservesRightKanExtensions L]
    [forall F : A ⥤ B, HasRightKanExtension L F] [forall F : A ⥤ D, HasRightKanExtension L F] :
    L.ran ⋙ (whiskeringRight _ _ _).obj G ≅ (whiskeringRight _ _ _).obj G ⋙ L.ran :=
  NatIso.ofComponents (fun F => rightKanExtensionCompIsoOfPreserves _ _ _)
    (fun {F F'} η => by
      apply hom_ext_of_isRightKanExtension
        (L.rightKanExtension <| F' ⋙ G)
        (L.rightKanExtensionCounit <| F' ⋙ G)
      dsimp [ran]
      ext
      simp only [comp_obj, Category.assoc, rightKanExtensionCompIsoOfPreserves_hom_fac,
        NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app, Category.id_comp,
        liftOfIsRightKanExtension_fac, rightKanExtensionCompIsoOfPreserves_hom_fac_assoc,
        ← G.map_comp]
      simp)

end RightKanExtension

end

end CategoryTheory.Functor
