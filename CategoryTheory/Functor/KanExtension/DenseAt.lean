/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Canonical colimits, or functors that are dense at an object

Given a functor `F : C ⥤ D` and `Y : D`, we say that `F` is dense at `Y` (`F.DenseAt Y`),
if `Y` identifies to the colimit of all `F.obj X` for `X : C`
and `f : F.obj X ⟶ Y`, i.e. `Y` identifies to the colimit of
the obvious functor `CostructuredArrow F Y ⥤ D`. In some references,
it is also said that `Y` is a canonical colimit relatively to `F`.
While `F.DenseAt Y` contains data, we also introduce the
corresponding property `isDenseAt F` of objects of `D`.

## TODO

* formalize dense subcategories
* show the presheaves of types are canonical colimits relatively
  to the Yoneda embedding

## References
* https://ncatlab.org/nlab/show/dense+functor

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (F : C ⥤ D)

namespace Functor

/--
Definition of `DenseAt` / `DenseAt` 的定义

English:
abbreviation DenseAt
  signature: (Y : D)
  body: (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

中文:
缩写 DenseAt
  签名: (Y : D)
  定义体: (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

Depends on / 依赖: F.rightUnitor.inv, Functor, Functor.LeftExtension.mk, IsPointwiseLeftKanExtensionAt, LeftExtension, rightUnitor
-/
abbrev DenseAt (Y : D) : Type max u₁ u₂ v₂ :=
  (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).IsPointwiseLeftKanExtensionAt Y

/--
Definition of `denseAtEquiv` / `denseAtEquiv` 的定义

English:
definition denseAtEquiv
  signature: (Y : D)
  body: .refl _

中文:
定义 denseAtEquiv
  签名: (Y : D)
  定义体: .refl _
-/
def denseAtEquiv (Y : D) :
    F.DenseAt Y ≃ IsColimit ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y) :=
  .refl _

variable {F} {Y : D} (hY : F.DenseAt Y)

/--
Definition of `DenseAt.ofIso` / `DenseAt.ofIso` 的定义

English:
definition DenseAt.ofIso
  signature: {Y' : D} (e : Y ≅ Y')
  body: LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

中文:
定义 DenseAt.ofIso
  签名: {Y' : D} (e : Y ≅ Y')
  定义体: LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

Depends on / 依赖: LeftExtension, LeftExtension.isPointwiseLeftKanExtensionAtOfIso, isPointwiseLeftKanExtensionAtOfIso
-/
def DenseAt.ofIso {Y' : D} (e : Y ≅ Y') : F.DenseAt Y' :=
  LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ hY e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `DenseAt.ofNatIso` / `DenseAt.ofNatIso` 的定义

English:
definition DenseAt.ofNatIso
  signature: {G : C ⥤ D} (e : F ≅ G)
  body: (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

中文:
定义 DenseAt.of自然数Iso
  签名: {G : C ⥤ D} (e : F ≅ G)
  定义体: (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

Depends on / 依赖: Cocone, Cocone.ext, CostructuredArrow, CostructuredArrow.mapNatIso, Functor, Functor.associator, Functor.isoWhiskerLeft, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, associator, e.symm, equivOfNatIsoOfIso, hY.whiskerEquivalence, isoWhiskerLeft, mapNatIso, whiskerEquivalence
-/
def DenseAt.ofNatIso {G : C ⥤ D} (e : F ≅ G) : G.DenseAt Y :=
  (IsColimit.equivOfNatIsoOfIso
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerLeft _ e) _ _
      (by exact Cocone.ext (Iso.refl _)))
    (hY.whiskerEquivalence (CostructuredArrow.mapNatIso e.symm))

/--
Definition of `DenseAt.precompEquivOfFinal` / `DenseAt.precompEquivOfFinal` 的定义

English:
definition DenseAt.precompEquivOfFinal
  body: Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

中文:
定义 DenseAt.precompEquivOfFinal
  定义体: Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.pre, F.rightUnitor.inv, Functor, Functor.Final.isColimitWhiskerEquiv, LeftExtension, LeftExtension.mk, coconeAt, isColimitWhiskerEquiv, rightUnitor
-/
noncomputable def DenseAt.precompEquivOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y ≃ F.DenseAt Y :=
  Functor.Final.isColimitWhiskerEquiv (CostructuredArrow.pre G F Y)
    ((LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt Y)

/--
Definition of `DenseAt.precompOfFinal` / `DenseAt.precompOfFinal` 的定义

English:
definition DenseAt.precompOfFinal
  body: (DenseAt.precompEquivOfFinal G).symm hY

中文:
定义 DenseAt.precompOfFinal
  定义体: (DenseAt.precompEquivOfFinal G).symm hY

Depends on / 依赖: DenseAt, DenseAt.precompEquivOfFinal, precompEquivOfFinal
-/
noncomputable def DenseAt.precompOfFinal
    {C' : Type*} [Category* C'] (G : C' ⥤ C) [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).DenseAt Y :=
  (DenseAt.precompEquivOfFinal G).symm hY

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `DenseAt.postcompEquivalence` / `DenseAt.postcompEquivalence` 的定义

English:
definition DenseAt.postcompEquivalence
  body: IsColimit.ofWhiskerEquivalence (CostructuredArrow.post F G Y).asEquivalence
    (IsColimit.ofIsoColimit ((isColimitOfPreserves G hY)) (Cocone.ext (Iso.refl _)))

中文:
定义 DenseAt.postcompEquivalence
  定义体: IsColimit.ofWhiskerEquivalence (CostructuredArrow.post F G Y).asEquivalence
    (IsColimit.ofIsoColimit ((isColimitOfPreserves G hY)) (Cocone.ext (Iso.refl _)))

Depends on / 依赖: Cocone, Cocone.ext, CostructuredArrow, CostructuredArrow.post, IsColimit, IsColimit.ofIsoColimit, IsColimit.ofWhiskerEquivalence, Iso.refl, asEquivalence, isColimitOfPreserves, ofIsoColimit, ofWhiskerEquivalence
-/
noncomputable def DenseAt.postcompEquivalence
    {D' : Type*} [Category* D'] (G : D ⥤ D') [G.IsEquivalence] :
    (F ⋙ G).DenseAt (G.obj Y) :=
  IsColimit.ofWhiskerEquivalence (CostructuredArrow.post F G Y).asEquivalence
    (IsColimit.ofIsoColimit ((isColimitOfPreserves G hY)) (Cocone.ext (Iso.refl _)))

/--
lemma `DenseAt.hasPointwiseLeftKanExtensionAt` / 引理 `DenseAt.hasPointwiseLeftKanExtensionAt`

English:
lemma DenseAt.hasPointwiseLeftKanExtensionAt
  given: (hf : F.DenseAt Y)
  proof: ⟨_, hf⟩

中文:
引理 DenseAt.hasPointwiseLeftKanExtensionAt
  条件: (hf : F.DenseAt Y)
  证明: ⟨_, hf⟩
-/
lemma DenseAt.hasPointwiseLeftKanExtensionAt (hf : F.DenseAt Y) :
    F.HasPointwiseLeftKanExtensionAt F Y :=
  ⟨_, hf⟩

variable (F) in
/--
Definition of `isDenseAt` / `isDenseAt` 的定义

English:
definition isDenseAt
  signature: : ObjectProperty D
  body: fun Y => Nonempty (F.DenseAt Y)

中文:
定义 isDenseAt
  签名: : ObjectProperty D
  定义体: fun Y => Nonempty (F.DenseAt Y)

Depends on / 依赖: DenseAt, F.DenseAt, Nonempty
-/
def isDenseAt : ObjectProperty D :=
  fun Y => Nonempty (F.DenseAt Y)

/--
lemma `isDenseAt_eq_isPointwiseLeftKanExtensionAt` / 引理 `isDenseAt_eq_isPointwiseLeftKanExtensionAt`

English:
lemma isDenseAt_eq_isPointwiseLeftKanExtensionAt
  proof: rfl

中文:
引理 isDenseAt_eq_isPointwiseLeftKanExtensionAt
  证明: rfl
-/
lemma isDenseAt_eq_isPointwiseLeftKanExtensionAt :
    F.isDenseAt =
      (Functor.LeftExtension.mk (𝟭 D) F.rightUnitor.inv).isPointwiseLeftKanExtensionAt :=
  rfl

/--
lemma `isDenseAt_iff` / 引理 `isDenseAt_iff`

English:
lemma isDenseAt_iff
  given: {X : D}
  proof: .rfl

中文:
引理 isDenseAt_iff
  条件: {X : D}
  证明: .rfl
-/
lemma isDenseAt_iff {X : D} :
    F.isDenseAt X ↔ Nonempty (IsColimit <| (LeftExtension.mk (𝟭 D) F.rightUnitor.inv).coconeAt X) :=
  .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.isDenseAt.IsClosedUnderIsomorphisms
  body: by
  rw [isDenseAt_eq_isPointwiseLeftKanExtensionAt]
  infer_instance

中文:
实例 :
  签名: F.isDenseAt.在同构下封闭
  定义体: by
  rw [isDenseAt_eq_isPointwiseLeftKanExtensionAt]
  infer_instance

Depends on / 依赖: infer_instance, isDenseAt_eq_isPointwiseLeftKanExtensionAt
-/
instance : F.isDenseAt.IsClosedUnderIsomorphisms := by
  rw [isDenseAt_eq_isPointwiseLeftKanExtensionAt]
  infer_instance

/--
lemma `congr_isDenseAt` / 引理 `congr_isDenseAt`

English:
lemma congr_isDenseAt
  given: {G : C ⥤ D} (e : F ≅ G)
  proof: by
  ext X
  exact ⟨fun ⟨h⟩ => ⟨h.ofNatIso e⟩, fun ⟨h⟩ => ⟨h.ofNatIso e.symm⟩⟩

中文:
引理 congr_isDenseAt
  条件: {G : C ⥤ D} (e : F ≅ G)
  证明: by
  ext X
  exact ⟨fun ⟨h⟩ => ⟨h.ofNatIso e⟩, fun ⟨h⟩ => ⟨h.ofNatIso e.symm⟩⟩

Depends on / 依赖: e.symm, h.ofNatIso, ofNatIso
-/
lemma congr_isDenseAt {G : C ⥤ D} (e : F ≅ G) :
    F.isDenseAt = G.isDenseAt := by
  ext X
  exact ⟨fun ⟨h⟩ => ⟨h.ofNatIso e⟩, fun ⟨h⟩ => ⟨h.ofNatIso e.symm⟩⟩

/--
lemma `IsDenseAt.iff_of_final` / 引理 `IsDenseAt.iff_of_final`

English:
lemma IsDenseAt.iff_of_final
  statement: {C' : Type*} [Category* C'] (G : C' ⥤ C)
  proof: (DenseAt.precompEquivOfFinal G).nonempty_congr

中文:
引理 IsDenseAt.iff_of_final
  结论: {C' : 类型} [范畴* C'] (G : C' ⥤ C)
  证明: (DenseAt.precompEquivOfFinal G).nonempty_congr

Depends on / 依赖: DenseAt, DenseAt.precompEquivOfFinal, nonempty_congr, precompEquivOfFinal
-/
lemma IsDenseAt.iff_of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] :
    (G ⋙ F).isDenseAt Y ↔ F.isDenseAt Y :=
  (DenseAt.precompEquivOfFinal G).nonempty_congr

/--
lemma `IsDenseAt.of_final` / 引理 `IsDenseAt.of_final`

English:
lemma IsDenseAt.of_final
  statement: {C' : Type*} [Category* C'] (G : C' ⥤ C)
  proof: (iff_of_final G).mpr hY

中文:
引理 IsDenseAt.of_final
  结论: {C' : 类型} [范畴* C'] (G : C' ⥤ C)
  证明: (iff_of_final G).mpr hY

Depends on / 依赖: iff_of_final
-/
lemma IsDenseAt.of_final {C' : Type*} [Category* C'] (G : C' ⥤ C)
    [(CostructuredArrow.pre G F Y).Final] (hY : F.isDenseAt Y) :
    (G ⋙ F).isDenseAt Y :=
  (iff_of_final G).mpr hY

end Functor

end CategoryTheory
