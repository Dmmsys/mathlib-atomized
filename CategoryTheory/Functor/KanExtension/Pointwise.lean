/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is a colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

A dual API for pointwise right Kan extension is also formalized.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type*} [Category* C] [Category* D] [Category* D'] [Category* H]
  (L : C ⥤ D) (L' : C ⥤ D') (F : C ⥤ H)

/--
Definition of `HasPointwiseLeftKanExtensionAt` / `HasPointwiseLeftKanExtensionAt` 的定义

English:
abbreviation HasPointwiseLeftKanExtensionAt
  signature: (Y : D)
  body: HasColimit (CostructuredArrow.proj L Y ⋙ F)

中文:
缩写 HasPointwiseLeftKanExtensionAt
  签名: (Y : D)
  定义体: HasColimit (CostructuredArrow.proj L Y ⋙ F)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, HasColimit
-/
abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

/--
Definition of `HasPointwiseLeftKanExtension` / `HasPointwiseLeftKanExtension` 的定义

English:
abbreviation HasPointwiseLeftKanExtension
  body: forall (Y : D), HasPointwiseLeftKanExtensionAt L F Y

中文:
缩写 HasPointwiseLeftKanExtension
  定义体: forall (Y : D), HasPointwiseLeftKanExtensionAt L F Y

Depends on / 依赖: HasPointwiseLeftKanExtensionAt
-/
abbrev HasPointwiseLeftKanExtension := forall (Y : D), HasPointwiseLeftKanExtensionAt L F Y

/--
Definition of `HasPointwiseRightKanExtensionAt` / `HasPointwiseRightKanExtensionAt` 的定义

English:
abbreviation HasPointwiseRightKanExtensionAt
  signature: (Y : D)
  body: HasLimit (StructuredArrow.proj Y L ⋙ F)

中文:
缩写 HasPointwiseRightKanExtensionAt
  签名: (Y : D)
  定义体: HasLimit (StructuredArrow.proj Y L ⋙ F)

Depends on / 依赖: HasLimit, StructuredArrow, StructuredArrow.proj
-/
abbrev HasPointwiseRightKanExtensionAt (Y : D) :=
  HasLimit (StructuredArrow.proj Y L ⋙ F)

/--
Definition of `HasPointwiseRightKanExtension` / `HasPointwiseRightKanExtension` 的定义

English:
abbreviation HasPointwiseRightKanExtension
  body: forall (Y : D), HasPointwiseRightKanExtensionAt L F Y

中文:
缩写 HasPointwiseRightKanExtension
  定义体: forall (Y : D), HasPointwiseRightKanExtensionAt L F Y

Depends on / 依赖: HasPointwiseRightKanExtensionAt
-/
abbrev HasPointwiseRightKanExtension := forall (Y : D), HasPointwiseRightKanExtensionAt L F Y

/--
lemma `hasPointwiseLeftKanExtensionAt_iff_of_iso` / 引理 `hasPointwiseLeftKanExtensionAt_iff_of_iso`

English:
lemma hasPointwiseLeftKanExtensionAt_iff_of_iso
  given: {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂)
  proof: by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ Cost

中文:
引理 hasPointwiseLeftKanExtensionAt_iff_of_iso
  条件: {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂)
  证明: by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ Cost

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapIso, CostructuredArrow.proj, HasColimit, HasPointwiseLeftKanExtensionAt, e.symm, functor, infer_instance, mapIso, revert
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseLeftKanExtensionAt L F Y₁ ↔
      HasPointwiseLeftKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance

/--
lemma `hasPointwiseRightKanExtensionAt_iff_of_iso` / 引理 `hasPointwiseRightKanExtensionAt_iff_of_iso`

English:
lemma hasPointwiseRightKanExtensionAt_iff_of_iso
  given: {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂)
  proof: by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ Struct

中文:
引理 hasPointwiseRightKanExtensionAt_iff_of_iso
  条件: {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂)
  证明: by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ Struct

Depends on / 依赖: HasLimit, HasPointwiseRightKanExtensionAt, StructuredArrow, StructuredArrow.mapIso, StructuredArrow.proj, e.symm, functor, infer_instance, mapIso, revert
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseRightKanExtensionAt L F Y₁ ↔
      HasPointwiseRightKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices forall ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ StructuredArrow.proj Y₁ L ⋙ F)
  infer_instance

variable {L} in
/--
lemma `hasPointwiseLeftKanExtensionAt_iff_of_natIso_left` / 引理 `hasPointwiseLeftKanExtensionAt_iff_of_natIso_left`

English:
lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso_left
  given: {L' : C ⥤ D} (e : L ≅ L') (Y : D)
  proof: by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLe

中文:
引理 hasPointwiseLeftKanExtensionAt_iff_of_natIso_left
  条件: {L' : C ⥤ D} (e : L ≅ L') (Y : D)
  证明: by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLe
-/
private lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso_left {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y := by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimit_of_iso e'

variable {L} in
/--
lemma `hasPointwiseRightKanExtensionAt_iff_of_natIso_left` / 引理 `hasPointwiseRightKanExtensionAt_iff_of_natIso_left`

English:
lemma hasPointwiseRightKanExtensionAt_iff_of_natIso_left
  given: {L' : C ⥤ D} (e : L ≅ L') (Y : D)
  proof: by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRigh

中文:
引理 hasPointwiseRightKanExtensionAt_iff_of_natIso_left
  条件: {L' : C ⥤ D} (e : L ≅ L') (Y : D)
  证明: by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRigh
-/
private lemma hasPointwiseRightKanExtensionAt_iff_of_natIso_left {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y := by
  revert L L' e
  suffices forall ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRightIso _ e.symm
  let e' : StructuredArrow.proj Y L' ⋙ F ≅
    Φ.functor ⋙ StructuredArrow.proj Y L ⋙ F := Iso.refl _
  exact hasLimit_of_iso e'.symm

/--
lemma `hasPointwiseLeftKanExtensionAt_of_equivalence` / 引理 `hasPointwiseLeftKanExtensionAt_of_equivalence`

English:
lemma hasPointwiseLeftKanExtensionAt_of_equivalence
  proof: by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inf

中文:
引理 hasPointwiseLeftKanExtensionAt_of_equivalence
  证明: by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inf

Depends on / 依赖: CostructuredArrow, CostructuredArrow.post, CostructuredArrow.proj, E.functor, E.functor.obj, HasColimit, HasPointwiseLeftKanExtensionAt, asEquivalence, e.symm, functor, hasColimit_of_equivalence_comp, hasPointwiseLeftKanExtensionAt_iff_of_iso, hasPointwiseLeftKanExtensionAt_iff_of_natIso_left
-/
lemma hasPointwiseLeftKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseLeftKanExtensionAt L F Y] :
    HasPointwiseLeftKanExtensionAt L' F Y' := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : HasPointwiseLeftKanExtensionAt L F Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)

/--
lemma `hasPointwiseLeftKanExtensionAt_iff_of_equivalence` / 引理 `hasPointwiseLeftKanExtensionAt_iff_of_equivalence`

English:
lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
  proof: by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnit

中文:
引理 hasPointwiseLeftKanExtensionAt_iff_of_equivalence
  证明: by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnit

Depends on / 依赖: E.inverse.mapIso, E.symm, E.unitIso.symm, E.unitIso.symm.app, Functor, Functor.associator, L.rightUnitor, associator, e.symm, eL.symm, hasPointwiseLeftKanExtensionAt_of_equivalence, inverse, isoWhiskerLeft, isoWhiskerRight, mapIso, rightUnitor, unitIso
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

/--
lemma `hasPointwiseRightKanExtensionAt_of_equivalence` / 引理 `hasPointwiseRightKanExtensionAt_of_equivalence`

English:
lemma hasPointwiseRightKanExtensionAt_of_equivalence
  proof: by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferIn

中文:
引理 hasPointwiseRightKanExtensionAt_of_equivalence
  证明: by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferIn

Depends on / 依赖: E.functor, E.functor.obj, HasLimit, HasPointwiseRightKanExtensionAt, StructuredArrow, StructuredArrow.post, StructuredArrow.proj, asEquivalence, e.symm, functor, hasLimit_of_equivalence_comp, hasPointwiseRightKanExtensionAt_iff_of_iso, hasPointwiseRightKanExtensionAt_iff_of_natIso_left
-/
lemma hasPointwiseRightKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseRightKanExtensionAt L F Y] :
    HasPointwiseRightKanExtensionAt L' F Y' := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso_left F eL]; rw [hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferInstance : HasPointwiseRightKanExtensionAt L F Y)
  exact hasLimit_of_equivalence_comp (asEquivalence Φ)

/--
lemma `hasPointwiseRightKanExtensionAt_iff_of_equivalence` / 引理 `hasPointwiseRightKanExtensionAt_iff_of_equivalence`

English:
lemma hasPointwiseRightKanExtensionAt_iff_of_equivalence
  proof: by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUn

中文:
引理 hasPointwiseRightKanExtensionAt_iff_of_equivalence
  证明: by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUn

Depends on / 依赖: E.inverse.mapIso, E.symm, E.unitIso.symm, E.unitIso.symm.app, Functor, Functor.associator, L.rightUnitor, associator, e.symm, eL.symm, hasPointwiseRightKanExtensionAt_of_equivalence, inverse, isoWhiskerLeft, isoWhiskerRight, mapIso, rightUnitor, unitIso
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `HasPointwiseLeftKanExtensionAt.of_natIso` / 引理 `HasPointwiseLeftKanExtensionAt.of_natIso`

English:
lemma HasPointwiseLeftKanExtensionAt.of_natIso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
  proof: by
  rw [hasPointwiseLeftKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : CostructuredArrow.proj L Y ⋙ F' ≅ CostructuredArrow.proj L Y ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseLeftKanExtensionAt]; rw [hasColimit_iff_of_iso e]
  infer_instance

中文:
引理 HasPointwiseLeftKanExtensionAt.of_natIso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
  证明: by
  rw [hasPointwiseLeftKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : CostructuredArrow.proj L Y ⋙ F' ≅ CostructuredArrow.proj L Y ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseLeftKanExtensionAt]; rw [hasColimit_iff_of_iso e]
  infer_instance

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, HasPointwiseLeftKanExtensionAt, NatIso, NatIso.ofComponents, hasColimit_iff_of_iso, hasPointwiseLeftKanExtensionAt_iff_of_natIso_left, infer_instance, ofComponents
-/
lemma HasPointwiseLeftKanExtensionAt.of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
    [L.HasPointwiseLeftKanExtensionAt F Y] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseLeftKanExtensionAt F' Y := by
  rw [hasPointwiseLeftKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : CostructuredArrow.proj L Y ⋙ F' ≅ CostructuredArrow.proj L Y ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseLeftKanExtensionAt]; rw [hasColimit_iff_of_iso e]
  infer_instance

/--
lemma `hasPointwiseLeftKanExtensionAt_iff_of_natIso` / 引理 `hasPointwiseLeftKanExtensionAt_iff_of_natIso`

English:
lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
  proof: ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

中文:
引理 hasPointwiseLeftKanExtensionAt_iff_of_natIso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
  证明: ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

Depends on / 依赖: of_natIso
-/
lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
    (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L.HasPointwiseLeftKanExtensionAt F Y ↔ L'.HasPointwiseLeftKanExtensionAt F' Y :=
  ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `HasPointwiseRightKanExtensionAt.of_natIso` / 引理 `HasPointwiseRightKanExtensionAt.of_natIso`

English:
lemma HasPointwiseRightKanExtensionAt.of_natIso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
  proof: by
  rw [hasPointwiseRightKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : StructuredArrow.proj Y L ⋙ F' ≅ StructuredArrow.proj Y L ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseRightKanExtensionAt]; rw [hasLimit_iff_of_iso e]
  infer_instance

中文:
引理 HasPointwiseRightKanExtensionAt.of_natIso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
  证明: by
  rw [hasPointwiseRightKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : StructuredArrow.proj Y L ⋙ F' ≅ StructuredArrow.proj Y L ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseRightKanExtensionAt]; rw [hasLimit_iff_of_iso e]
  infer_instance

Depends on / 依赖: HasPointwiseRightKanExtensionAt, NatIso, NatIso.ofComponents, StructuredArrow, StructuredArrow.proj, hasLimit_iff_of_iso, hasPointwiseRightKanExtensionAt_iff_of_natIso_left, infer_instance, ofComponents
-/
lemma HasPointwiseRightKanExtensionAt.of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} (Y : D)
    [L.HasPointwiseRightKanExtensionAt F Y] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseRightKanExtensionAt F' Y := by
  rw [hasPointwiseRightKanExtensionAt_iff_of_natIso_left _ e₁.symm]
  let e : StructuredArrow.proj Y L ⋙ F' ≅ StructuredArrow.proj Y L ⋙ F :=
    NatIso.ofComponents fun X => (e₂.app _).symm
  rw [HasPointwiseRightKanExtensionAt]; rw [hasLimit_iff_of_iso e]
  infer_instance

/--
lemma `hasPointwiseRightKanExtensionAt_iff_of_natIso` / 引理 `hasPointwiseRightKanExtensionAt_iff_of_natIso`

English:
lemma hasPointwiseRightKanExtensionAt_iff_of_natIso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
  proof: ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

中文:
引理 hasPointwiseRightKanExtensionAt_iff_of_natIso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
  证明: ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

Depends on / 依赖: of_natIso
-/
lemma hasPointwiseRightKanExtensionAt_iff_of_natIso {L L' : C ⥤ D} {F F' : C ⥤ H} {Y : D}
    (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L.HasPointwiseRightKanExtensionAt F Y ↔ L'.HasPointwiseRightKanExtensionAt F' Y :=
  ⟨fun _ => .of_natIso Y e₁ e₂, fun _ => .of_natIso Y e₁.symm e₂.symm⟩

/--
lemma `HasPointwiseLeftKanExtension.of_iso` / 引理 `HasPointwiseLeftKanExtension.of_iso`

English:
lemma HasPointwiseLeftKanExtension.of_iso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H}
  proof: fun _ => .of_natIso _ e₁ e₂

中文:
引理 HasPointwiseLeftKanExtension.of_iso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H}
  证明: fun _ => .of_natIso _ e₁ e₂

Depends on / 依赖: of_natIso
-/
lemma HasPointwiseLeftKanExtension.of_iso {L L' : C ⥤ D} {F F' : C ⥤ H}
    [L.HasPointwiseLeftKanExtension F] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseLeftKanExtension F' :=
  fun _ => .of_natIso _ e₁ e₂

/--
lemma `HasPointwiseRightKanExtension.of_iso` / 引理 `HasPointwiseRightKanExtension.of_iso`

English:
lemma HasPointwiseRightKanExtension.of_iso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H}
  proof: fun _ => .of_natIso _ e₁ e₂

中文:
引理 HasPointwiseRightKanExtension.of_iso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H}
  证明: fun _ => .of_natIso _ e₁ e₂

Depends on / 依赖: of_natIso
-/
lemma HasPointwiseRightKanExtension.of_iso {L L' : C ⥤ D} {F F' : C ⥤ H}
    [L.HasPointwiseRightKanExtension F] (e₁ : L ≅ L') (e₂ : F ≅ F') :
    L'.HasPointwiseRightKanExtension F' :=
  fun _ => .of_natIso _ e₁ e₂

/--
lemma `hasPointwiseLeftKanExtension_iff_of_iso` / 引理 `hasPointwiseLeftKanExtension_iff_of_iso`

English:
lemma hasPointwiseLeftKanExtension_iff_of_iso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
  proof: ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

中文:
引理 hasPointwiseLeftKanExtension_iff_of_iso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
  证明: ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

Depends on / 依赖: of_iso
-/
lemma hasPointwiseLeftKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
    (e₂ : F ≅ F') :
    L.HasPointwiseLeftKanExtension F ↔ L'.HasPointwiseLeftKanExtension F' :=
  ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

/--
lemma `hasPointwiseRightKanExtension_iff_of_iso` / 引理 `hasPointwiseRightKanExtension_iff_of_iso`

English:
lemma hasPointwiseRightKanExtension_iff_of_iso
  statement: {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
  proof: ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

中文:
引理 hasPointwiseRightKanExtension_iff_of_iso
  结论: {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
  证明: ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

Depends on / 依赖: of_iso
-/
lemma hasPointwiseRightKanExtension_iff_of_iso {L L' : C ⥤ D} {F F' : C ⥤ H} (e₁ : L ≅ L')
    (e₂ : F ≅ F') :
    L.HasPointwiseRightKanExtension F ↔ L'.HasPointwiseRightKanExtension F' :=
  ⟨fun _ => .of_iso e₁ e₂, fun _ => .of_iso e₁.symm e₂.symm⟩

namespace LeftExtension

variable {F L}
variable (E : LeftExtension L F)

set_option backward.defeqAttrib.useBackward true in
/-- The cocone for `CostructuredArrow.proj L Y ⋙ F` attached to `E : LeftExtension L F`.
The point of this cocone is `E.right.obj Y` -/
@[simps]
/--
Definition of `coconeAt` / `coconeAt` 的定义

English:
definition coconeAt
  signature: (Y : D)
  body: E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

中文:
定义 coconeAt
  签名: (Y : D)
  定义体: E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

Depends on / 依赖: E.right.obj
-/
def coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (L F) in
/-- The cocones for `CostructuredArrow.proj L Y ⋙ F`, as a functor from `LeftExtension L F`. -/
@[simps]
/--
Definition of `coconeAtFunctor` / `coconeAtFunctor` 的定义

English:
definition coconeAtFunctor
  signature: (Y : D)
  body: E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp)

中文:
定义 coconeAtFunctor
  签名: (Y : D)
  定义体: E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp)

Depends on / 依赖: E.coconeAt, coconeAt
-/
def coconeAtFunctor (Y : D) :
    LeftExtension L F ⥤ Cocone (CostructuredArrow.proj L Y ⋙ F) where
  obj E := E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp)

/--
Definition of `IsPointwiseLeftKanExtensionAt` / `IsPointwiseLeftKanExtensionAt` 的定义

English:
definition IsPointwiseLeftKanExtensionAt
  signature: (Y : D)
  body: IsColimit (E.coconeAt Y)

中文:
定义 IsPointwiseLeftKanExtensionAt
  签名: (Y : D)
  定义体: IsColimit (E.coconeAt Y)

Depends on / 依赖: E.coconeAt, IsColimit, coconeAt
-/
def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

instance (Y : D) : Subsingleton (E.IsPointwiseLeftKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsColimit _))

variable {E} in
/--
lemma `IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt` / 引理 `IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt`

English:
lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
  proof: ⟨_, h⟩

中文:
引理 IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
  证明: ⟨_, h⟩
-/
lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
    HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsPointwiseLeftKanExtensionAt.isIso_hom_app` / 引理 `IsPointwiseLeftKanExtensionAt.isIso_hom_app`

English:
lemma IsPointwiseLeftKanExtensionAt.isIso_hom_app
  proof: by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

中文:
引理 IsPointwiseLeftKanExtensionAt.isIso_hom_app
  证明: by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mkIdTerminal, h.isIso_, mkIdTerminal
-/
lemma IsPointwiseLeftKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseLeftKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseLeftKanExtensionAtOfIso'` / `isPointwiseLeftKanExtensionAtOfIso'` 的定义

English:
definition isPointwiseLeftKanExtensionAtOfIso'
  body: IsColimit.ofIsoColimit (hY.whiskerEquivalence (CostructuredArrow.mapIso e.symm))
    (Cocone.ext (E.right.mapIso e))

中文:
定义 isPointwiseLeftKanExtensionAtOfIso'
  定义体: IsColimit.ofIsoColimit (hY.whiskerEquivalence (CostructuredArrow.mapIso e.symm))
    (Cocone.ext (E.right.mapIso e))

Depends on / 依赖: Cocone, Cocone.ext, CostructuredArrow, CostructuredArrow.mapIso, E.right.mapIso, IsColimit, IsColimit.ofIsoColimit, e.symm, hY.whiskerEquivalence, mapIso, ofIsoColimit, whiskerEquivalence
-/
def isPointwiseLeftKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseLeftKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y' :=
  IsColimit.ofIsoColimit (hY.whiskerEquivalence (CostructuredArrow.mapIso e.symm))
    (Cocone.ext (E.right.mapIso e))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isPointwiseLeftKanExtensionAtEquivOfIso'` / `isPointwiseLeftKanExtensionAtEquivOfIso'` 的定义

English:
definition isPointwiseLeftKanExtensionAtEquivOfIso'
  signature: {Y Y' : D} (e : Y ≅ Y')
  body: E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

中文:
定义 isPointwiseLeftKanExtensionAtEquivOfIso'
  签名: {Y Y' : D} (e : Y ≅ Y')
  定义体: E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

Depends on / 依赖: E.isPointwiseLeftKanExtensionAtOfIso, isPointwiseLeftKanExtensionAtOfIso
-/
def isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where
  toFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseLeftKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
include h in
/--
lemma `hom_ext'` / 引理 `hom_ext'`

English:
lemma hom_ext'
  statement: {T : H} {f g : E.right.obj Y ⟶ T}
  proof: h.hom_ext (fun j => by simpa using hfg j.hom)

中文:
引理 hom_ext'
  结论: {T : H} {f g : E.right.obj Y ⟶ T}
  证明: h.hom_ext (fun j => by simpa using hfg j.hom)

Depends on / 依赖: h.hom_ext, hom_ext, j.hom
-/
lemma hom_ext' {T : H} {f g : E.right.obj Y ⟶ T}
    (hfg : forall ⦃X : C⦄ (φ : L.obj X ⟶ Y),
      E.hom.app X ≫ E.right.map φ ≫ f = E.hom.app X ≫ E.right.map φ ≫ g) : f = g :=
  h.hom_ext (fun j => by simpa using hfg j.hom)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `comp_homEquiv_symm` / 引理 `comp_homEquiv_symm`

English:
lemma comp_homEquiv_symm
  statement: {Z : H}
  proof: by
  simpa using h.ι_app_homEquiv_symm φ g

中文:
引理 comp_homEquiv_symm
  结论: {Z : H}
  证明: by
  simpa using h.ι_app_homEquiv_symm φ g
-/
lemma comp_homEquiv_symm {Z : H}
    (φ : CostructuredArrow.proj L Y ⋙ F ⟶ (Functor.const _).obj Z)
    (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.homEquiv.symm φ = φ.app g := by
  simpa using h.ι_app_homEquiv_symm φ g

variable [HasColimit (CostructuredArrow.proj L Y ⋙ F)]

/--
Definition of `isoColimit` / `isoColimit` 的定义

English:
definition isoColimit
  signature: :
  body: h.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]

中文:
定义 isoColimit
  签名: :
  定义体: h.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, cat_disch, coconePointUniqueUpToIso, cokernel, cokernel.desc, colimit, colimit.isColimit, h.coconePointUniqueUpToIso, isColimit, reassoc_of
-/
noncomputable def isoColimit :
    E.right.obj Y ≅ colimit (CostructuredArrow.proj L Y ⋙ F) :=
  h.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
/--
lemma `ι_isoColimit_inv` / 引理 `ι_isoColimit_inv`

English:
lemma ι_isoColimit_inv
  given: (g : CostructuredArrow L Y)
  proof: IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

中文:
引理 ι_isoColimit_inv
  条件: (g : CostructuredArrow L Y)
  证明: IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, comp_coconePointUniqueUpToIso_inv
-/
lemma ι_isoColimit_inv (g : CostructuredArrow L Y) :
    colimit.ι _ g ≫ h.isoColimit.inv = E.hom.app g.left ≫ E.right.map g.hom :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `ι_isoColimit_hom` / 引理 `ι_isoColimit_hom`

English:
lemma ι_isoColimit_hom
  given: (g : CostructuredArrow L Y)
  proof: by
  simpa using! h.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) g

中文:
引理 ι_isoColimit_hom
  条件: (g : CostructuredArrow L Y)
  证明: by
  simpa using! h.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) g

Depends on / 依赖: colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, h.comp_coconePointUniqueUpToIso_hom, isColimit
-/
lemma ι_isoColimit_hom (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.isoColimit.hom =
      colimit.ι (CostructuredArrow.proj L Y ⋙ F) g := by
  simpa using! h.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) g

end IsPointwiseLeftKanExtensionAt

/--
Definition of `isPointwiseLeftKanExtensionAt` / `isPointwiseLeftKanExtensionAt` 的定义

English:
definition isPointwiseLeftKanExtensionAt
  signature: : ObjectProperty D
  body: fun Y => Nonempty (E.IsPointwiseLeftKanExtensionAt Y)

中文:
定义 isPointwiseLeftKanExtensionAt
  签名: : ObjectProperty D
  定义体: fun Y => Nonempty (E.IsPointwiseLeftKanExtensionAt Y)

Depends on / 依赖: E.IsPointwiseLeftKanExtensionAt, IsPointwiseLeftKanExtensionAt, Nonempty
-/
def isPointwiseLeftKanExtensionAt : ObjectProperty D :=
  fun Y => Nonempty (E.IsPointwiseLeftKanExtensionAt Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: E.isPointwiseLeftKanExtensionAt.IsClosedUnderIsomorphisms
  body: ⟨E.isPointwiseLeftKanExtensionAtOfIso' h.some e⟩

中文:
实例 :
  签名: E.isPointwiseLeftKanExtensionAt.在同构下封闭
  定义体: ⟨E.isPointwiseLeftKanExtensionAtOfIso' h.some e⟩

Depends on / 依赖: E.isPointwiseLeftKanExtensionAtOfIso, h.some, isPointwiseLeftKanExtensionAtOfIso
-/
instance : E.isPointwiseLeftKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseLeftKanExtensionAtOfIso' h.some e⟩

/--
Definition of `IsPointwiseLeftKanExtension` / `IsPointwiseLeftKanExtension` 的定义

English:
abbreviation IsPointwiseLeftKanExtension
  body: forall (Y : D), E.IsPointwiseLeftKanExtensionAt Y

中文:
缩写 IsPointwiseLeftKanExtension
  定义体: forall (Y : D), E.IsPointwiseLeftKanExtensionAt Y

Depends on / 依赖: E.IsPointwiseLeftKanExtensionAt, IsPointwiseLeftKanExtensionAt
-/
abbrev IsPointwiseLeftKanExtension := forall (Y : D), E.IsPointwiseLeftKanExtensionAt Y

variable {E E'}

/--
Definition of `isPointwiseLeftKanExtensionAtEquivOfIso` / `isPointwiseLeftKanExtensionAtEquivOfIso` 的定义

English:
definition isPointwiseLeftKanExtensionAtEquivOfIso
  signature: (e : E ≅ E') (Y : D)
  body: IsColimit.equivIsoColimit ((coconeAtFunctor L F Y).mapIso e)

中文:
定义 isPointwiseLeftKanExtensionAtEquivOfIso
  签名: (e : E ≅ E') (Y : D)
  定义体: IsColimit.equivIsoColimit ((coconeAtFunctor L F Y).mapIso e)

Depends on / 依赖: IsColimit, IsColimit.equivIsoColimit, coconeAtFunctor, equivIsoColimit, mapIso
-/
def isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y :=
  IsColimit.equivIsoColimit ((coconeAtFunctor L F Y).mapIso e)

/--
Definition of `isPointwiseLeftKanExtensionEquivOfIso` / `isPointwiseLeftKanExtensionEquivOfIso` 的定义

English:
definition isPointwiseLeftKanExtensionEquivOfIso
  signature: (e : E ≅ E')
  body: fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

中文:
定义 isPointwiseLeftKanExtensionEquivOfIso
  签名: (e : E ≅ E')
  定义体: fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

Depends on / 依赖: isPointwiseLeftKanExtensionAtEquivOfIso
-/
def isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseLeftKanExtension ≃ E'.IsPointwiseLeftKanExtension where
  toFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseLeftKanExtension)
include h

/--
lemma `IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension` / 引理 `IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension`

English:
lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension
  proof: fun Y => (h Y).hasPointwiseLeftKanExtensionAt

中文:
引理 IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension
  证明: fun Y => (h Y).hasPointwiseLeftKanExtensionAt

Depends on / 依赖: hasPointwiseLeftKanExtensionAt
-/
lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsPointwiseLeftKanExtension.homFrom` / `IsPointwiseLeftKanExtension.homFrom` 的定义

English:
definition IsPointwiseLeftKanExtension.homFrom
  signature: (G : LeftExtension L F)
  body: StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
 

中文:
定义 IsPointwiseLeftKanExtension.homFrom
  签名: (G : LeftExtension L F)
  定义体: StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
 

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, CostructuredArrow.mk, L.obj, LeftExtension, LeftExtension.coconeAt, StructuredArrow, StructuredArrow.homMk, coconeAt, fac_assoc, hom_ext, naturality
-/
def IsPointwiseLeftKanExtension.homFrom (G : LeftExtension L F) : E ⟶ G :=
  StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsPointwiseLeftKanExtension.hom_ext` / 引理 `IsPointwiseLeftKanExtension.hom_ext`

English:
lemma IsPointwiseLeftKanExtension.hom_ext
  proof: by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁]; rw [reassoc_of% eq₂]

中文:
引理 IsPointwiseLeftKanExtension.hom_ext
  证明: by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁]; rw [reassoc_of% eq₂]

Depends on / 依赖: NatTrans, NatTrans.naturality, StructuredArrow, StructuredArrow.w, X.left, congr_app, hom_ext, naturality, reassoc_of
-/
lemma IsPointwiseLeftKanExtension.hom_ext
    {G : LeftExtension L F} {f₁ f₂ : E ⟶ G} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁]; rw [reassoc_of% eq₂]

/--
Definition of `IsPointwiseLeftKanExtension.isUniversal` / `IsPointwiseLeftKanExtension.isUniversal` 的定义

English:
definition IsPointwiseLeftKanExtension.isUniversal
  signature: : E.IsUniversal
  body: IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)

中文:
定义 IsPointwiseLeftKanExtension.isUniversal
  签名: : E.是泛
  定义体: IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)

Depends on / 依赖: IsInitial, IsInitial.ofUniqueHom, h.homFrom, h.hom_ext, homFrom, hom_ext, ofUniqueHom
-/
def IsPointwiseLeftKanExtension.isUniversal : E.IsUniversal :=
  IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)

/--
lemma `IsPointwiseLeftKanExtension.isLeftKanExtension` / 引理 `IsPointwiseLeftKanExtension.isLeftKanExtension`

English:
lemma IsPointwiseLeftKanExtension.isLeftKanExtension
  proof: ⟨h.isUniversal⟩

中文:
引理 IsPointwiseLeftKanExtension.isLeftKanExtension
  证明: ⟨h.isUniversal⟩

Depends on / 依赖: h.isUniversal, isUniversal
-/
lemma IsPointwiseLeftKanExtension.isLeftKanExtension :
    E.right.IsLeftKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩

/--
lemma `IsPointwiseLeftKanExtension.hasLeftKanExtension` / 引理 `IsPointwiseLeftKanExtension.hasLeftKanExtension`

English:
lemma IsPointwiseLeftKanExtension.hasLeftKanExtension
  proof: have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom

中文:
引理 IsPointwiseLeftKanExtension.hasLeftKanExtension
  证明: have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom

Depends on / 依赖: E.hom, E.right, HasLeftKanExtension, HasLeftKanExtension.mk, h.isLeftKanExtension, isLeftKanExtension
-/
lemma IsPointwiseLeftKanExtension.hasLeftKanExtension :
    HasLeftKanExtension L F :=
  have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom

/--
lemma `IsPointwiseLeftKanExtension.isIso_hom` / 引理 `IsPointwiseLeftKanExtension.isIso_hom`

English:
lemma IsPointwiseLeftKanExtension.isIso_hom
  given: [L.Full] [L.Faithful]
  proof: have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

中文:
引理 IsPointwiseLeftKanExtension.isIso_hom
  条件: [L.满] [L.忠实]
  证明: have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

Depends on / 依赖: L.obj, NatIso, NatIso.isIso_of_isIso_app, isIso_hom_app, isIso_of_isIso_app
-/
lemma IsPointwiseLeftKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end LeftExtension

namespace RightExtension

variable {F L}
variable (E E' : RightExtension L F)

set_option backward.defeqAttrib.useBackward true in
/-- The cone for `StructuredArrow.proj Y L ⋙ F` attached to `E : RightExtension L F`.
The point of this cone is `E.left.obj Y` -/
@[simps]
/--
Definition of `coneAt` / `coneAt` 的定义

English:
definition coneAt
  signature: (Y : D)
  body: E.left.obj Y
  π :=
    { app := fun g => E.left.map g.hom ≫ E.hom.app g.right
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [assoc]; rw [id_comp]; rw [← StructuredArrow.w φ]; rw [Functor.map_comp]; rw [assoc]
        congr 1
        apply E.hom.naturality }

中文:
定义 coneAt
  签名: (Y : D)
  定义体: E.left.obj Y
  π :=
    { app := fun g => E.left.map g.hom ≫ E.hom.app g.right
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [assoc]; rw [id_comp]; rw [← StructuredArrow.w φ]; rw [Functor.map_comp]; rw [assoc]
        congr 1
        apply E.hom.naturality }

Depends on / 依赖: E.left.obj
-/
def coneAt (Y : D) : Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := E.left.obj Y
  π :=
    { app := fun g => E.left.map g.hom ≫ E.hom.app g.right
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [assoc]; rw [id_comp]; rw [← StructuredArrow.w φ]; rw [Functor.map_comp]; rw [assoc]
        congr 1
        apply E.hom.naturality }

set_option backward.defeqAttrib.useBackward true in
variable (L F) in
/-- The cones for `StructuredArrow.proj Y L ⋙ F`, as a functor from `RightExtension L F`. -/
@[simps]
/--
Definition of `coneAtFunctor` / `coneAtFunctor` 的定义

English:
definition coneAtFunctor
  signature: (Y : D)
  body: E.coneAt Y
  map {E E'} φ := ConeMorphism.mk (φ.left.app Y) (fun G => by
    dsimp
    rw [← CostructuredArrow.w φ]
    simp)

中文:
定义 coneAtFunctor
  签名: (Y : D)
  定义体: E.coneAt Y
  map {E E'} φ := ConeMorphism.mk (φ.left.app Y) (fun G => by
    dsimp
    rw [← CostructuredArrow.w φ]
    simp)

Depends on / 依赖: E.coneAt, coneAt
-/
def coneAtFunctor (Y : D) :
    RightExtension L F ⥤ Cone (StructuredArrow.proj Y L ⋙ F) where
  obj E := E.coneAt Y
  map {E E'} φ := ConeMorphism.mk (φ.left.app Y) (fun G => by
    dsimp
    rw [← CostructuredArrow.w φ]
    simp)

/--
Definition of `IsPointwiseRightKanExtensionAt` / `IsPointwiseRightKanExtensionAt` 的定义

English:
definition IsPointwiseRightKanExtensionAt
  signature: (Y : D)
  body: IsLimit (E.coneAt Y)

中文:
定义 IsPointwiseRightKanExtensionAt
  签名: (Y : D)
  定义体: IsLimit (E.coneAt Y)

Depends on / 依赖: E.coneAt, IsLimit, coneAt
-/
def IsPointwiseRightKanExtensionAt (Y : D) := IsLimit (E.coneAt Y)

instance (Y : D) : Subsingleton (E.IsPointwiseRightKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsLimit _))

variable {E} in
/--
lemma `IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt` / 引理 `IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt`

English:
lemma IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
  proof: ⟨_, h⟩

中文:
引理 IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
  证明: ⟨_, h⟩
-/
lemma IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
    {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y) :
    HasPointwiseRightKanExtensionAt L F Y := ⟨_, h⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsPointwiseRightKanExtensionAt.isIso_hom_app` / 引理 `IsPointwiseRightKanExtensionAt.isIso_hom_app`

English:
lemma IsPointwiseRightKanExtensionAt.isIso_hom_app
  proof: by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

中文:
引理 IsPointwiseRightKanExtensionAt.isIso_hom_app
  证明: by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

Depends on / 依赖: StructuredArrow, StructuredArrow.mkIdInitial, h.isIso_, mkIdInitial
-/
lemma IsPointwiseRightKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseRightKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isPointwiseRightKanExtensionAtOfIso'` / `isPointwiseRightKanExtensionAtOfIso'` 的定义

English:
definition isPointwiseRightKanExtensionAtOfIso'
  body: IsLimit.ofIsoLimit (hY.whiskerEquivalence (StructuredArrow.mapIso e.symm))
    (Cone.ext (E.left.mapIso e))

中文:
定义 isPointwiseRightKanExtensionAtOfIso'
  定义体: IsLimit.ofIsoLimit (hY.whiskerEquivalence (StructuredArrow.mapIso e.symm))
    (Cone.ext (E.left.mapIso e))

Depends on / 依赖: Cone.ext, E.left.mapIso, IsLimit, IsLimit.ofIsoLimit, StructuredArrow, StructuredArrow.mapIso, e.symm, hY.whiskerEquivalence, mapIso, ofIsoLimit, whiskerEquivalence
-/
def isPointwiseRightKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseRightKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y' :=
  IsLimit.ofIsoLimit (hY.whiskerEquivalence (StructuredArrow.mapIso e.symm))
    (Cone.ext (E.left.mapIso e))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isPointwiseRightKanExtensionAtEquivOfIso'` / `isPointwiseRightKanExtensionAtEquivOfIso'` 的定义

English:
definition isPointwiseRightKanExtensionAtEquivOfIso'
  signature: {Y Y' : D} (e : Y ≅ Y')
  body: E.isPointwiseRightKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseRightKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

中文:
定义 isPointwiseRightKanExtensionAtEquivOfIso'
  签名: {Y Y' : D} (e : Y ≅ Y')
  定义体: E.isPointwiseRightKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseRightKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

Depends on / 依赖: E.isPointwiseRightKanExtensionAtOfIso, isPointwiseRightKanExtensionAtOfIso
-/
def isPointwiseRightKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y ≃ E.IsPointwiseRightKanExtensionAt Y' where
  toFun h := E.isPointwiseRightKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseRightKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseRightKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y)

include h in
/--
lemma `hom_ext'` / 引理 `hom_ext'`

English:
lemma hom_ext'
  statement: {T : H} {f g : T ⟶ E.left.obj Y}
  proof: h.hom_ext (fun j => hfg j.hom)

中文:
引理 hom_ext'
  结论: {T : H} {f g : T ⟶ E.left.obj Y}
  证明: h.hom_ext (fun j => hfg j.hom)

Depends on / 依赖: h.hom_ext, hom_ext, j.hom
-/
lemma hom_ext' {T : H} {f g : T ⟶ E.left.obj Y}
    (hfg : forall ⦃X : C⦄ (φ : Y ⟶ L.obj X),
      f ≫ E.left.map φ ≫ E.hom.app X = g ≫ E.left.map φ ≫ E.hom.app X) : f = g :=
  h.hom_ext (fun j => hfg j.hom)

variable [HasLimit (StructuredArrow.proj Y L ⋙ F)]

/--
Definition of `isoLimit` / `isoLimit` 的定义

English:
definition isoLimit
  signature: :
  body: h.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]

中文:
定义 isoLimit
  签名: :
  定义体: h.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: conePointUniqueUpToIso, h.conePointUniqueUpToIso, isLimit, limit.isLimit
-/
noncomputable def isoLimit :
    E.left.obj Y ≅ limit (StructuredArrow.proj Y L ⋙ F) :=
  h.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
/--
lemma `isoLimit_hom_π` / 引理 `isoLimit_hom_π`

English:
lemma isoLimit_hom_π
  given: (g : StructuredArrow Y L)
  proof: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]

中文:
引理 isoLimit_hom_π
  条件: (g : 结构化箭头 Y L)
  证明: IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, conePointUniqueUpToIso_hom_comp
-/
lemma isoLimit_hom_π (g : StructuredArrow Y L) :
    h.isoLimit.hom ≫ limit.π _ g = E.left.map g.hom ≫ E.hom.app g.right :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
/--
lemma `isoLimit_inv_π` / 引理 `isoLimit_inv_π`

English:
lemma isoLimit_inv_π
  given: (g : StructuredArrow Y L)
  proof: by
  simpa using! h.conePointUniqueUpToIso_inv_comp (limit.isLimit _) g

中文:
引理 isoLimit_inv_π
  条件: (g : 结构化箭头 Y L)
  证明: by
  simpa using! h.conePointUniqueUpToIso_inv_comp (limit.isLimit _) g

Depends on / 依赖: conePointUniqueUpToIso_inv_comp, h.conePointUniqueUpToIso_inv_comp, isLimit, limit.isLimit
-/
lemma isoLimit_inv_π (g : StructuredArrow Y L) :
    h.isoLimit.inv ≫ E.left.map g.hom ≫ E.hom.app g.right =
      limit.π (StructuredArrow.proj Y L ⋙ F) g := by
  simpa using! h.conePointUniqueUpToIso_inv_comp (limit.isLimit _) g

end IsPointwiseRightKanExtensionAt

/--
Definition of `isPointwiseRightKanExtensionAt` / `isPointwiseRightKanExtensionAt` 的定义

English:
definition isPointwiseRightKanExtensionAt
  signature: : ObjectProperty D
  body: fun Y => Nonempty (E.IsPointwiseRightKanExtensionAt Y)

中文:
定义 isPointwiseRightKanExtensionAt
  签名: : ObjectProperty D
  定义体: fun Y => Nonempty (E.IsPointwiseRightKanExtensionAt Y)

Depends on / 依赖: E.IsPointwiseRightKanExtensionAt, IsPointwiseRightKanExtensionAt, Nonempty
-/
def isPointwiseRightKanExtensionAt : ObjectProperty D :=
  fun Y => Nonempty (E.IsPointwiseRightKanExtensionAt Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: E.isPointwiseRightKanExtensionAt.IsClosedUnderIsomorphisms
  body: ⟨E.isPointwiseRightKanExtensionAtOfIso' h.some e⟩

中文:
实例 :
  签名: E.isPointwiseRightKanExtensionAt.在同构下封闭
  定义体: ⟨E.isPointwiseRightKanExtensionAtOfIso' h.some e⟩

Depends on / 依赖: E.isPointwiseRightKanExtensionAtOfIso, h.some, isPointwiseRightKanExtensionAtOfIso
-/
instance : E.isPointwiseRightKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseRightKanExtensionAtOfIso' h.some e⟩

/--
Definition of `IsPointwiseRightKanExtension` / `IsPointwiseRightKanExtension` 的定义

English:
abbreviation IsPointwiseRightKanExtension
  body: forall (Y : D), E.IsPointwiseRightKanExtensionAt Y

中文:
缩写 IsPointwiseRightKanExtension
  定义体: forall (Y : D), E.IsPointwiseRightKanExtensionAt Y

Depends on / 依赖: E.IsPointwiseRightKanExtensionAt, IsPointwiseRightKanExtensionAt
-/
abbrev IsPointwiseRightKanExtension := forall (Y : D), E.IsPointwiseRightKanExtensionAt Y

variable {E E'}

/--
Definition of `isPointwiseRightKanExtensionAtEquivOfIso` / `isPointwiseRightKanExtensionAtEquivOfIso` 的定义

English:
definition isPointwiseRightKanExtensionAtEquivOfIso
  signature: (e : E ≅ E') (Y : D)
  body: IsLimit.equivIsoLimit ((coneAtFunctor L F Y).mapIso e)

中文:
定义 isPointwiseRightKanExtensionAtEquivOfIso
  签名: (e : E ≅ E') (Y : D)
  定义体: IsLimit.equivIsoLimit ((coneAtFunctor L F Y).mapIso e)

Depends on / 依赖: IsLimit, IsLimit.equivIsoLimit, coneAtFunctor, equivIsoLimit, mapIso
-/
def isPointwiseRightKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseRightKanExtensionAt Y ≃ E'.IsPointwiseRightKanExtensionAt Y :=
  IsLimit.equivIsoLimit ((coneAtFunctor L F Y).mapIso e)

/--
Definition of `isPointwiseRightKanExtensionEquivOfIso` / `isPointwiseRightKanExtensionEquivOfIso` 的定义

English:
definition isPointwiseRightKanExtensionEquivOfIso
  signature: (e : E ≅ E')
  body: fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

中文:
定义 isPointwiseRightKanExtensionEquivOfIso
  签名: (e : E ≅ E')
  定义体: fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

Depends on / 依赖: isPointwiseRightKanExtensionAtEquivOfIso
-/
def isPointwiseRightKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseRightKanExtension ≃ E'.IsPointwiseRightKanExtension where
  toFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseRightKanExtension)
include h

/--
lemma `IsPointwiseRightKanExtension.hasPointwiseRightKanExtension` / 引理 `IsPointwiseRightKanExtension.hasPointwiseRightKanExtension`

English:
lemma IsPointwiseRightKanExtension.hasPointwiseRightKanExtension
  proof: fun Y => (h Y).hasPointwiseRightKanExtensionAt

中文:
引理 IsPointwiseRightKanExtension.hasPointwiseRightKanExtension
  证明: fun Y => (h Y).hasPointwiseRightKanExtensionAt

Depends on / 依赖: hasPointwiseRightKanExtensionAt
-/
lemma IsPointwiseRightKanExtension.hasPointwiseRightKanExtension :
    HasPointwiseRightKanExtension L F :=
  fun Y => (h Y).hasPointwiseRightKanExtensionAt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `IsPointwiseRightKanExtension.homTo` / `IsPointwiseRightKanExtension.homTo` 的定义

English:
definition IsPointwiseRightKanExtension.homTo
  signature: (G : RightExtension L F)
  body: CostructuredArrow.homMk
    { app := fun Y => (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₂).hom_ext (fun X => by
        rw [assoc]; rw [(h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
     

中文:
定义 IsPointwiseRightKanExtension.homTo
  签名: (G : RightExtension L F)
  定义体: CostructuredArrow.homMk
    { app := fun Y => (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₂).hom_ext (fun X => by
        rw [assoc]; rw [(h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
     

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, L.obj, RightExtension, RightExtension.coneAt, StructuredArrow, StructuredArrow.map, StructuredArrow.mk, coneAt, hom_ext, naturality
-/
def IsPointwiseRightKanExtension.homTo (G : RightExtension L F) : G ⟶ E :=
  CostructuredArrow.homMk
    { app := fun Y => (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₂).hom_ext (fun X => by
        rw [assoc]; rw [(h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (RightExtension.coneAt G _) (StructuredArrow.mk (𝟙 _)))

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsPointwiseRightKanExtension.hom_ext` / 引理 `IsPointwiseRightKanExtension.hom_ext`

English:
lemma IsPointwiseRightKanExtension.hom_ext
  proof: by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [← NatTrans.naturality_assoc, eq₁, eq₂]

中文:
引理 IsPointwiseRightKanExtension.hom_ext
  证明: by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [← NatTrans.naturality_assoc, eq₁, eq₂]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w, NatTrans, NatTrans.naturality_assoc, X.right, congr_app, hom_ext, naturality_assoc
-/
lemma IsPointwiseRightKanExtension.hom_ext
    {G : RightExtension L F} {f₁ f₂ : G ⟶ E} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [← NatTrans.naturality_assoc, eq₁, eq₂]

/--
Definition of `IsPointwiseRightKanExtension.isUniversal` / `IsPointwiseRightKanExtension.isUniversal` 的定义

English:
definition IsPointwiseRightKanExtension.isUniversal
  signature: : E.IsUniversal
  body: IsTerminal.ofUniqueHom h.homTo (fun _ _ => h.hom_ext)

中文:
定义 IsPointwiseRightKanExtension.isUniversal
  签名: : E.是泛
  定义体: IsTerminal.ofUniqueHom h.homTo (fun _ _ => h.hom_ext)

Depends on / 依赖: IsTerminal, IsTerminal.ofUniqueHom, h.homTo, h.hom_ext, hom_ext, ofUniqueHom
-/
def IsPointwiseRightKanExtension.isUniversal : E.IsUniversal :=
  IsTerminal.ofUniqueHom h.homTo (fun _ _ => h.hom_ext)

/--
lemma `IsPointwiseRightKanExtension.isRightKanExtension` / 引理 `IsPointwiseRightKanExtension.isRightKanExtension`

English:
lemma IsPointwiseRightKanExtension.isRightKanExtension
  proof: ⟨h.isUniversal⟩

中文:
引理 IsPointwiseRightKanExtension.isRightKanExtension
  证明: ⟨h.isUniversal⟩

Depends on / 依赖: h.isUniversal, isUniversal
-/
lemma IsPointwiseRightKanExtension.isRightKanExtension :
    E.left.IsRightKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩

/--
lemma `IsPointwiseRightKanExtension.hasRightKanExtension` / 引理 `IsPointwiseRightKanExtension.hasRightKanExtension`

English:
lemma IsPointwiseRightKanExtension.hasRightKanExtension
  proof: have := h.isRightKanExtension
  HasRightKanExtension.mk E.left E.hom

中文:
引理 IsPointwiseRightKanExtension.hasRightKanExtension
  证明: have := h.isRightKanExtension
  HasRightKanExtension.mk E.left E.hom

Depends on / 依赖: E.hom, E.left, HasRightKanExtension, HasRightKanExtension.mk, h.isRightKanExtension, isRightKanExtension
-/
lemma IsPointwiseRightKanExtension.hasRightKanExtension :
    HasRightKanExtension L F :=
  have := h.isRightKanExtension
  HasRightKanExtension.mk E.left E.hom

/--
lemma `IsPointwiseRightKanExtension.isIso_hom` / 引理 `IsPointwiseRightKanExtension.isIso_hom`

English:
lemma IsPointwiseRightKanExtension.isIso_hom
  given: [L.Full] [L.Faithful]
  proof: have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

中文:
引理 IsPointwiseRightKanExtension.isIso_hom
  条件: [L.满] [L.忠实]
  证明: have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

Depends on / 依赖: L.obj, NatIso, NatIso.isIso_of_isIso_app, isIso_hom_app, isIso_of_isIso_app
-/
lemma IsPointwiseRightKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end RightExtension

section

variable [HasPointwiseLeftKanExtension L F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed pointwise left Kan extension when `HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
/--
Definition of `pointwiseLeftKanExtension` / `pointwiseLeftKanExtension` 的定义

English:
definition pointwiseLeftKanExtension
  signature: : D ⥤ H where
  body: colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          na

中文:
定义 pointwiseLeftKanExtension
  签名: : D ⥤ H where
  定义体: colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          na

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, colimit
-/
noncomputable def pointwiseLeftKanExtension : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using colimit.w (CostructuredArrow.proj L Y₂ ⋙ F)
              ((CostructuredArrow.map f).map φ) })
  map_id Y := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp)

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the constructed pointwise left Kan extension when
`HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
/--
Definition of `pointwiseLeftKanExtensionUnit` / `pointwiseLeftKanExtensionUnit` 的定义

English:
definition pointwiseLeftKanExtensionUnit
  signature: : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  body: colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredA

中文:
定义 pointwiseLeftKanExtensionUnit
  签名: : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  定义体: colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredA

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, L.obj, colimit
-/
noncomputable def pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pointwiseLeftKanExtensionIsPointwiseLeftKanExtension` / `pointwiseLeftKanExtensionIsPointwiseLeftKanExtension` 的定义

English:
definition pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
  signature: :
  body: fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]; rw [← CostructuredArrow.eq_mk]))

中文:
定义 pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
  签名: :
  定义体: fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]; rw [← CostructuredArrow.eq_mk]))

Depends on / 依赖: Cocone, Cocone.ext, CostructuredArrow, CostructuredArrow.eq_mk, CostructuredArrow.map_mk, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, comp_id, eq_mk, id_comp, isColimit, map_mk, ofIsoColimit
-/
noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]; rw [← CostructuredArrow.eq_mk]))

/--
Definition of `pointwiseLeftKanExtensionIsUniversal` / `pointwiseLeftKanExtensionIsUniversal` 的定义

English:
definition pointwiseLeftKanExtensionIsUniversal
  signature: :
  body: (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal

中文:
定义 pointwiseLeftKanExtensionIsUniversal
  签名: :
  定义体: (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal

Depends on / 依赖: isUniversal, pointwiseLeftKanExtensionIsPointwiseLeftKanExtension
-/
noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsUniversal :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pointwiseLeftKanExtension L F).IsLeftKanExtension
  body: ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

中文:
实例 :
  签名: (pointwiseLeftKanExtension L F).是LeftKanExtension
  定义体: ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

Depends on / 依赖: pointwiseLeftKanExtensionIsUniversal
-/
instance : (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F) where
  nonempty_isUniversal := ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLeftKanExtension L F
  body: HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

中文:
实例 :
  签名: 有LeftKanExtension L F
  定义体: HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

Depends on / 依赖: HasLeftKanExtension, HasLeftKanExtension.mk, pointwiseLeftKanExtensionUnit
-/
instance : HasLeftKanExtension L F :=
  HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary cocone used in the lemma `pointwiseLeftKanExtension_desc_app` -/
@[simps]
/--
Definition of `costructuredArrowMapCocone` / `costructuredArrowMapCocone` 的定义

English:
definition costructuredArrowMapCocone
  signature: (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D)
  body: G.obj Y
  ι := {
    app := fun f => α.app f.left ≫ G.map f.hom
    naturality := by simp [← G.map_comp] }

中文:
定义 costructuredArrowMapCocone
  签名: (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D)
  定义体: G.obj Y
  ι := {
    app := fun f => α.app f.left ≫ G.map f.hom
    naturality := by simp [← G.map_comp] }

Depends on / 依赖: G.obj
-/
def costructuredArrowMapCocone (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := G.obj Y
  ι := {
    app := fun f => α.app f.left ≫ G.map f.hom
    naturality := by simp [← G.map_comp] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pointwiseLeftKanExtension_desc_app` / 引理 `pointwiseLeftKanExtension_desc_app`

English:
lemma pointwiseLeftKanExtension_desc_app
  given: (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D)
  proof: by G α
  let β : L.pointwiseLeftKanExtension F ⟶ G :=
    { app := fun Y => colimit.desc _ (costructuredArrowMapCocone L F G α Y) }
  have h : (pointwiseLeftKanExtension L F).descOfIsLeftKanExtension
      (pointwiseLeftKanExtensionUnit L F) G α = β := by
    apply hom_ext_of_isLeftKanExtension (α :

中文:
引理 pointwiseLeftKanExtension_desc_app
  条件: (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D)
  证明: by G α
  let β : L.pointwiseLeftKanExtension F ⟶ G :=
    { app := fun Y => colimit.desc _ (costructuredArrowMapCocone L F G α Y) }
  have h : (pointwiseLeftKanExtension L F).descOfIsLeftKanExtension
      (pointwiseLeftKanExtensionUnit L F) G α = β := by
    apply hom_ext_of_isLeftKanExtension (α :

Depends on / 依赖: L.pointwiseLeftKanExtension, NatTrans, NatTrans.congr_app, colimit, colimit.desc, congr_app, costructuredArrowMapCocone, descOfIsLeftKanExtension, hom_ext_of_isLeftKanExtension, pointwiseLeftKanExtension, pointwiseLeftKanExtensionUnit
-/
lemma pointwiseLeftKanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    ((pointwiseLeftKanExtension L F).descOfIsLeftKanExtension (pointwiseLeftKanExtensionUnit L F)
.app Y) = colimit.desc _ (costructuredArrowMapCocone L F G α Y) := by G α
  let β : L.pointwiseLeftKanExtension F ⟶ G :=
    { app := fun Y => colimit.desc _ (costructuredArrowMapCocone L F G α Y) }
  have h : (pointwiseLeftKanExtension L F).descOfIsLeftKanExtension
      (pointwiseLeftKanExtensionUnit L F) G α = β := by
    apply hom_ext_of_isLeftKanExtension (α := pointwiseLeftKanExtensionUnit L F)
    aesop
  exact NatTrans.congr_app h Y

variable {F L}

/--
Definition of `isPointwiseLeftKanExtensionOfIsLeftKanExtension` / `isPointwiseLeftKanExtensionOfIsLeftKanExtension` 的定义

English:
definition isPointwiseLeftKanExtensionOfIsLeftKanExtension
  signature: (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
  body: LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

中文:
定义 isPointwiseLeftKanExtensionOfIsLeftKanExtension
  签名: (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
  定义体: LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, LeftExtension, LeftExtension.isPointwiseLeftKanExtensionEquivOfIso, coconePointUniqueUpToIso, isPointwiseLeftKanExtensionEquivOfIso, isUniversalOfIsLeftKanExtension, pointwiseLeftKanExtensionIsPointwiseLeftKanExtension, pointwiseLeftKanExtensionIsUniversal
-/
noncomputable def isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

end

section

variable [HasPointwiseRightKanExtension L F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed pointwise right Kan extension
when `HasPointwiseRightKanExtension L F` holds. -/
@[simps]
/--
Definition of `pointwiseRightKanExtension` / `pointwiseRightKanExtension` 的定义

English:
definition pointwiseRightKanExtension
  signature: : D ⥤ H where
  body: limit (StructuredArrow.proj Y L ⋙ F)
  map {Y₁ Y₂} f := limit.lift (StructuredArrow.proj Y₂ L ⋙ F)
      (Cone.mk (limit (StructuredArrow.proj Y₁ L ⋙ F))
        { app := fun g => limit.π (StructuredArrow.proj Y₁ L ⋙ F)
            ((StructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ 

中文:
定义 pointwiseRightKanExtension
  签名: : D ⥤ H where
  定义体: limit (StructuredArrow.proj Y L ⋙ F)
  map {Y₁ Y₂} f := limit.lift (StructuredArrow.proj Y₂ L ⋙ F)
      (Cone.mk (limit (StructuredArrow.proj Y₁ L ⋙ F))
        { app := fun g => limit.π (StructuredArrow.proj Y₁ L ⋙ F)
            ((StructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ 

Depends on / 依赖: StructuredArrow, StructuredArrow.proj
-/
noncomputable def pointwiseRightKanExtension : D ⥤ H where
  obj Y := limit (StructuredArrow.proj Y L ⋙ F)
  map {Y₁ Y₂} f := limit.lift (StructuredArrow.proj Y₂ L ⋙ F)
      (Cone.mk (limit (StructuredArrow.proj Y₁ L ⋙ F))
        { app := fun g => limit.π (StructuredArrow.proj Y₁ L ⋙ F)
            ((StructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using (limit.w (StructuredArrow.proj Y₁ L ⋙ F)
              ((StructuredArrow.map f).map φ)).symm })
  map_id Y := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, id_comp]
    congr
    apply StructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, assoc]
    congr 1
    apply StructuredArrow.map_comp)

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the constructed pointwise right Kan extension when
`HasPointwiseRightKanExtension L F` holds. -/
@[simps]
/--
Definition of `pointwiseRightKanExtensionCounit` / `pointwiseRightKanExtensionCounit` 的定义

English:
definition pointwiseRightKanExtensionCounit
  signature: :
  body: limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
    (StructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseRightKanExtension_map, limit.lift_π, StructuredArrow.map_mk]
    rw [comp_id]
    let φ : StructuredArrow.mk (𝟙 (L.obj X₁)) ⟶ StructuredArrow.mk 

中文:
定义 pointwiseRightKanExtensionCounit
  签名: :
  定义体: limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
    (StructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseRightKanExtension_map, limit.lift_π, StructuredArrow.map_mk]
    rw [comp_id]
    let φ : StructuredArrow.mk (𝟙 (L.obj X₁)) ⟶ StructuredArrow.mk 

Depends on / 依赖: L.obj, StructuredArrow, StructuredArrow.proj
-/
noncomputable def pointwiseRightKanExtensionCounit :
    L ⋙ pointwiseRightKanExtension L F ⟶ F where
  app X := limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
    (StructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_map,
      pointwiseRightKanExtension_map, limit.lift_π, StructuredArrow.map_mk]
    rw [comp_id]
    let φ : StructuredArrow.mk (𝟙 (L.obj X₁)) ⟶ StructuredArrow.mk (L.map f) :=
      StructuredArrow.homMk f
    exact (limit.w (StructuredArrow.proj (L.obj X₁) L ⋙ F) φ).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pointwiseRightKanExtensionIsPointwiseRightKanExtension` / `pointwiseRightKanExtensionIsPointwiseRightKanExtension` 的定义

English:
definition pointwiseRightKanExtensionIsPointwiseRightKanExtension
  signature: :
  body: fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [limit.lift_π, StructuredArrow.map_mk, id_comp]
    congr
    rw [comp_id]; rw [← StructuredArrow.eq_mk]))

中文:
定义 pointwiseRightKanExtensionIsPointwiseRightKanExtension
  签名: :
  定义体: fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [limit.lift_π, StructuredArrow.map_mk, id_comp]
    congr
    rw [comp_id]; rw [← StructuredArrow.eq_mk]))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, Iso.refl, StructuredArrow, StructuredArrow.eq_mk, StructuredArrow.map_mk, comp_id, eq_mk, id_comp, isLimit, limit.isLimit, limit.lift_, map_mk, ofIsoLimit
-/
noncomputable def pointwiseRightKanExtensionIsPointwiseRightKanExtension :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsPointwiseRightKanExtension :=
  fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [limit.lift_π, StructuredArrow.map_mk, id_comp]
    congr
    rw [comp_id]; rw [← StructuredArrow.eq_mk]))

/--
Definition of `pointwiseRightKanExtensionIsUniversal` / `pointwiseRightKanExtensionIsUniversal` 的定义

English:
definition pointwiseRightKanExtensionIsUniversal
  signature: :
  body: (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).isUniversal

中文:
定义 pointwiseRightKanExtensionIsUniversal
  签名: :
  定义体: (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).isUniversal

Depends on / 依赖: isUniversal, pointwiseRightKanExtensionIsPointwiseRightKanExtension
-/
noncomputable def pointwiseRightKanExtensionIsUniversal :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsUniversal :=
  (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).isUniversal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (pointwiseRightKanExtension L F).IsRightKanExtension
  body: ⟨pointwiseRightKanExtensionIsUniversal L F⟩

中文:
实例 :
  签名: (pointwiseRightKanExtension L F).是RightKanExtension
  定义体: ⟨pointwiseRightKanExtensionIsUniversal L F⟩

Depends on / 依赖: pointwiseRightKanExtensionIsUniversal
-/
instance : (pointwiseRightKanExtension L F).IsRightKanExtension
    (pointwiseRightKanExtensionCounit L F) where
  nonempty_isUniversal := ⟨pointwiseRightKanExtensionIsUniversal L F⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRightKanExtension L F
  body: HasRightKanExtension.mk _ (pointwiseRightKanExtensionCounit L F)

中文:
实例 :
  签名: HasRightKanExtension L F
  定义体: HasRightKanExtension.mk _ (pointwiseRightKanExtensionCounit L F)

Depends on / 依赖: HasRightKanExtension, HasRightKanExtension.mk, pointwiseRightKanExtensionCounit
-/
instance : HasRightKanExtension L F :=
  HasRightKanExtension.mk _ (pointwiseRightKanExtensionCounit L F)

set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary cocone used in the lemma `pointwiseRightKanExtension_lift_app` -/
@[simps]
/--
Definition of `structuredArrowMapCone` / `structuredArrowMapCone` 的定义

English:
definition structuredArrowMapCone
  signature: (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D)
  body: G.obj Y
  π := {
    app := fun f => G.map f.hom ≫ α.app f.right
    naturality := by simp [← α.naturality, ← G.map_comp_assoc] }

中文:
定义 structuredArrowMapCone
  签名: (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D)
  定义体: G.obj Y
  π := {
    app := fun f => G.map f.hom ≫ α.app f.right
    naturality := by simp [← α.naturality, ← G.map_comp_assoc] }

Depends on / 依赖: G.obj, HasEqualizers, HasKernels, hasKernels_of_hasEqualizers
-/
def structuredArrowMapCone (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := G.obj Y
  π := {
    app := fun f => G.map f.hom ≫ α.app f.right
    naturality := by simp [← α.naturality, ← G.map_comp_assoc] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `pointwiseRightKanExtension_lift_app` / 引理 `pointwiseRightKanExtension_lift_app`

English:
lemma pointwiseRightKanExtension_lift_app
  given: (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D)
  proof: by
  let β : G ⟶ L.pointwiseRightKanExtension F :=
    { app := fun Y => limit.lift _ (structuredArrowMapCone L F G α Y) }
  have h : (pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α = β := by
    apply hom_ext_of_isRightKanExtension (α := p

中文:
引理 pointwiseRightKanExtension_lift_app
  条件: (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D)
  证明: by
  let β : G ⟶ L.pointwiseRightKanExtension F :=
    { app := fun Y => limit.lift _ (structuredArrowMapCone L F G α Y) }
  have h : (pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α = β := by
    apply hom_ext_of_isRightKanExtension (α := p

Depends on / 依赖: HasCoequalizers, L.pointwiseRightKanExtension, NatTrans, NatTrans.congr_app, congr_app, hasCokernels_of_hasCoequalizers, hom_ext_of_isRightKanExtension, liftOfIsRightKanExtension, limit.lift, pointwiseRightKanExtension, pointwiseRightKanExtensionCounit, structuredArrowMapCone
-/
lemma pointwiseRightKanExtension_lift_app (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    ((pointwiseRightKanExtension L F).liftOfIsRightKanExtension
.app Y) = (pointwiseRightKanExtensionCounit L F) G α
        limit.lift _ (structuredArrowMapCone L F G α Y) := by
  let β : G ⟶ L.pointwiseRightKanExtension F :=
    { app := fun Y => limit.lift _ (structuredArrowMapCone L F G α Y) }
  have h : (pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α = β := by
    apply hom_ext_of_isRightKanExtension (α := pointwiseRightKanExtensionCounit L F)
    aesop
  exact NatTrans.congr_app h Y

variable {F L}

/--
Definition of `isPointwiseRightKanExtensionOfIsRightKanExtension` / `isPointwiseRightKanExtensionOfIsRightKanExtension` 的定义

English:
definition isPointwiseRightKanExtensionOfIsRightKanExtension
  signature: (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
  body: RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (IsLimit.conePointUniqueUpToIso (pointwiseRightKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsRightKanExtension α))
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F)

中文:
定义 isPointwiseRightKanExtensionOfIsRightKanExtension
  签名: (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
  定义体: RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (IsLimit.conePointUniqueUpToIso (pointwiseRightKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsRightKanExtension α))
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, RightExtension, RightExtension.isPointwiseRightKanExtensionEquivOfIso, conePointUniqueUpToIso, isPointwiseRightKanExtensionEquivOfIso, isUniversalOfIsRightKanExtension, pointwiseRightKanExtensionIsPointwiseRightKanExtension, pointwiseRightKanExtensionIsUniversal
-/
noncomputable def isPointwiseRightKanExtensionOfIsRightKanExtension (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (IsLimit.conePointUniqueUpToIso (pointwiseRightKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsRightKanExtension α))
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F)

end

end Functor

end CategoryTheory
