/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Equivalences of sheaf categories

Given a site `(C, J)` and a category `D` which is equivalent to `C`, with `C` and `D` possibly large
and possibly in different universes, we transport the Grothendieck topology `J` on `C` to `D` and
prove that the sheaf categories are equivalent.

We also prove that sheafification and the property `HasSheafCompose` transport nicely over this
equivalence, and apply it to essentially small sites. We also provide instances for existence of
sufficiently small limits in the sheaf category on the essentially small site.

## Main definitions

* `CategoryTheory.Equivalence.sheafCongr` is the equivalence of sheaf categories.

* `CategoryTheory.Equivalence.transportAndSheafify` is the functor which takes a presheaf on `C`,
  transports it over the equivalence to `D`, sheafifies there and then transports back to `C`.

* `CategoryTheory.Equivalence.transportSheafificationAdjunction`: `transportAndSheafify` is
  left adjoint to the functor taking a sheaf to its underlying presheaf.

* `CategoryTheory.smallSheafify` is the functor which takes a presheaf on an essentially small site
  `(C, J)`, transports to a small model, sheafifies there and then transports back to `C`.

* `CategoryTheory.smallSheafificationAdjunction`: `smallSheafify` is left adjoint to the functor
  taking a sheaf to its underlying presheaf.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

open CategoryTheory.Functor Limits GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)
variable (A : Type u₃) [Category.{v₃} A]

namespace Equivalence

instance (priority := 900) [G.IsEquivalence] : IsCoverDense G J where
  is_cover U := by
    let e := (asEquivalence G).symm
    convert! J.top_mem U
    ext Y f
    simp only [Sieve.top_apply, iff_true]
    let g : e.inverse.obj _ ⟶ U := (e.unitInv.app Y) ≫ f
    have : (Sieve.coverByImage e.inverse U).arrows g := Presieve.in_coverByImage _ g
    replace := Sieve.downward_closed _ this (e.unit.app Y)
    simpa [g] using! this

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: e.functor.IsDenseSubsite J (e.inverse.inducedTopology J)
  body: by
  have : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext
    simp [mem_inducedTopology_iff_of_isCoverDense, mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_equivalence_eq_pullback]
  nth_rw 1 [this]
  infer_instance

中文:
实例 :
  签名: e.functor.是DenseSubsite J (e.inverse.inducedTopology J)
  定义体: by
  have : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext
    simp [mem_inducedTopology_iff_of_isCoverDense, mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_equivalence_eq_pullback]
  nth_rw 1 [this]
  infer_instance

Depends on / 依赖: Sieve.functorPushforward_equivalence_eq_pullback, e.functor.inducedTopology, e.inverse.inducedTopology, functor, functorPushforward_equivalence_eq_pullback, inducedTopology, infer_instance, inverse, mem_inducedTopology_iff_of_isCoverDense, nth_rw
-/
instance : e.functor.IsDenseSubsite J (e.inverse.inducedTopology J) := by
  have : J = e.functor.inducedTopology (e.inverse.inducedTopology J) := by
    ext
    simp [mem_inducedTopology_iff_of_isCoverDense, mem_inducedTopology_iff_of_isCoverDense,
      Sieve.functorPushforward_equivalence_eq_pullback]
  nth_rw 1 [this]
  infer_instance

/--
lemma `eq_inducedTopology_of_isDenseSubsite` / 引理 `eq_inducedTopology_of_isDenseSubsite`

English:
lemma eq_inducedTopology_of_isDenseSubsite
  given: [e.inverse.IsDenseSubsite K J]
  proof: by
  ext
  rw [mem_inducedTopology_iff_of_isCoverDense]
  exact (e.inverse.functorPushforward_mem_iff K J).symm

中文:
引理 eq_inducedTopology_of_isDenseSubsite
  条件: [e.inverse.是DenseSubsite K J]
  证明: by
  ext
  rw [mem_inducedTopology_iff_of_isCoverDense]
  exact (e.inverse.functorPushforward_mem_iff K J).symm

Depends on / 依赖: e.inverse.functorPushforward_mem_iff, functorPushforward_mem_iff, inverse, mem_inducedTopology_iff_of_isCoverDense
-/
lemma eq_inducedTopology_of_isDenseSubsite [e.inverse.IsDenseSubsite K J] :
    K = e.inverse.inducedTopology J := by
  ext
  rw [mem_inducedTopology_iff_of_isCoverDense]
  exact (e.inverse.functorPushforward_mem_iff K J).symm

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isDenseSubsite_functor_of_isCocontinuous` / 引理 `isDenseSubsite_functor_of_isCocontinuous`

English:
lemma isDenseSubsite_functor_of_isCocontinuous
  proof: by
    constructor
    · intro H
      refine J.superset_covering ?_ (e.functor.cover_lift J K H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion e.functor X).u_l_eq S]
    · intro H
      refine K.superset_covering ?_
        (e.inverse.cover_lift K J (J.pullback_stable (e.unitInv.app X) H))
      exact fun Y f (H : S _) => ⟨_, _, e.counitInv.app Y, H, by simp⟩

中文:
引理 isDenseSubsite_functor_of_isCocontinuous
  证明: by
    constructor
    · intro H
      refine J.superset_covering ?_ (e.functor.cover_lift J K H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion e.functor X).u_l_eq S]
    · intro H
      refine K.superset_covering ?_
        (e.inverse.cover_lift K J (J.pullback_stable (e.unitInv.app X) H))
      exact fun Y f (H : S _) => ⟨_, _, e.counitInv.app Y, H, by simp⟩

Depends on / 依赖: J.pullback_stable, J.superset_covering, K.superset_covering, Sieve.fullyFaithfulFunctorGaloisCoinsertion, counitInv, cover_lift, e.counitInv.app, e.functor, e.functor.cover_lift, e.inverse.cover_lift, e.unitInv.app, fullyFaithfulFunctorGaloisCoinsertion, functor, inverse, pullback_stable, superset_covering, u_l_eq, unitInv
-/
lemma isDenseSubsite_functor_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.functor.IsDenseSubsite J K where
  functorPushforward_mem_iff {X S} := by
    constructor
    · intro H
      refine J.superset_covering ?_ (e.functor.cover_lift J K H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion e.functor X).u_l_eq S]
    · intro H
      refine K.superset_covering ?_
        (e.inverse.cover_lift K J (J.pullback_stable (e.unitInv.app X) H))
      exact fun Y f (H : S _) => ⟨_, _, e.counitInv.app Y, H, by simp⟩

/--
lemma `isDenseSubsite_inverse_of_isCocontinuous` / 引理 `isDenseSubsite_inverse_of_isCocontinuous`

English:
lemma isDenseSubsite_inverse_of_isCocontinuous
  proof: have : e.symm.functor.IsCocontinuous K J := inferInstanceAs (e.inverse.IsCocontinuous _ _)
  have : e.symm.inverse.IsCocontinuous J K := inferInstanceAs (e.functor.IsCocontinuous _ _)
  isDenseSubsite_functor_of_isCocontinuous _ _ e.symm

中文:
引理 isDenseSubsite_inverse_of_isCocontinuous
  证明: have : e.symm.functor.IsCocontinuous K J := inferInstanceAs (e.inverse.IsCocontinuous _ _)
  have : e.symm.inverse.IsCocontinuous J K := inferInstanceAs (e.functor.IsCocontinuous _ _)
  isDenseSubsite_functor_of_isCocontinuous _ _ e.symm

Depends on / 依赖: IsCocontinuous, e.functor.IsCocontinuous, e.inverse.IsCocontinuous, e.symm, e.symm.functor.IsCocontinuous, e.symm.inverse.IsCocontinuous, functor, inverse, isDenseSubsite_functor_of_isCocontinuous
-/
lemma isDenseSubsite_inverse_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.inverse.IsDenseSubsite K J :=
  have : e.symm.functor.IsCocontinuous K J := inferInstanceAs (e.inverse.IsCocontinuous _ _)
  have : e.symm.inverse.IsCocontinuous J K := inferInstanceAs (e.functor.IsCocontinuous _ _)
  isDenseSubsite_functor_of_isCocontinuous _ _ e.symm

variable [e.inverse.IsDenseSubsite K J]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: e.functor.IsDenseSubsite J K
  body: by
  rw [e.eq_inducedTopology_of_isDenseSubsite J K]
  infer_instance

中文:
实例 :
  签名: e.functor.是DenseSubsite J K
  定义体: by
  rw [e.eq_inducedTopology_of_isDenseSubsite J K]
  infer_instance

Depends on / 依赖: e.eq_inducedTopology_of_isDenseSubsite, eq_inducedTopology_of_isDenseSubsite, infer_instance
-/
instance : e.functor.IsDenseSubsite J K := by
  rw [e.eq_inducedTopology_of_isDenseSubsite J K]
  infer_instance

/-- The functor in the equivalence of sheaf categories. -/
@[simps!]
/--
Definition of `sheafCongr.functor` / `sheafCongr.functor` 的定义

English:
definition sheafCongr.functor
  signature: : Sheaf J A ⥤ Sheaf K A
  body: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op)
    (e.inverse.op_comp_isSheaf _ _)

中文:
定义 sheafCongr.functor
  签名: : 层 J A ⥤ 层 K A
  定义体: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op)
    (e.inverse.op_comp_isSheaf _ _)

Depends on / 依赖: Functor, Functor.whiskeringLeft, ObjectProperty, ObjectProperty.lift, e.inverse.op, e.inverse.op_comp_isSheaf, inverse, op_comp_isSheaf, sheafToPresheaf, whiskeringLeft
-/
def sheafCongr.functor : Sheaf J A ⥤ Sheaf K A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op)
    (e.inverse.op_comp_isSheaf _ _)

/-- The inverse in the equivalence of sheaf categories. -/
@[simps!]
/--
Definition of `sheafCongr.inverse` / `sheafCongr.inverse` 的定义

English:
definition sheafCongr.inverse
  signature: : Sheaf K A ⥤ Sheaf J A
  body: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor.op)
    (e.functor.op_comp_isSheaf _ _)

中文:
定义 sheafCongr.inverse
  签名: : 层 K A ⥤ 层 J A
  定义体: ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor.op)
    (e.functor.op_comp_isSheaf _ _)

Depends on / 依赖: Functor, Functor.whiskeringLeft, ObjectProperty, ObjectProperty.lift, e.functor.op, e.functor.op_comp_isSheaf, functor, op_comp_isSheaf, sheafToPresheaf, whiskeringLeft
-/
def sheafCongr.inverse : Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj e.functor.op)
    (e.functor.op_comp_isSheaf _ _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit iso in the equivalence of sheaf categories. -/
@[simps!]
/--
Definition of `sheafCongr.unitIso` / `sheafCongr.unitIso` 的定义

English:
definition sheafCongr.unitIso
  signature: : 𝟭 (Sheaf J A) ≅ functor J K e A ⋙ inverse J K e A
  body: NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.unitIso F.obj))

中文:
定义 sheafCongr.unitIso
  签名: : 𝟭 (层 J A) ≅ functor J K e A ⋙ inverse J K e A
  定义体: NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.unitIso F.obj))

Depends on / 依赖: F.obj, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, e.op.unitIso, isoWhiskerRight, ofComponents, unitIso
-/
def sheafCongr.unitIso : 𝟭 (Sheaf J A) ≅ functor J K e A ⋙ inverse J K e A :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.unitIso F.obj))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The counit iso in the equivalence of sheaf categories. -/
@[simps!]
/--
Definition of `sheafCongr.counitIso` / `sheafCongr.counitIso` 的定义

English:
definition sheafCongr.counitIso
  signature: : inverse J K e A ⋙ functor J K e A ≅ 𝟭 (Sheaf _ A)
  body: NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.counitIso F.obj))

中文:
定义 sheafCongr.counitIso
  签名: : inverse J K e A ⋙ functor J K e A ≅ 𝟭 (层 _ A)
  定义体: NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.counitIso F.obj))

Depends on / 依赖: F.obj, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, counitIso, e.op.counitIso, isoWhiskerRight, ofComponents
-/
def sheafCongr.counitIso : inverse J K e A ⋙ functor J K e A ≅ 𝟭 (Sheaf _ A) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (isoWhiskerRight e.op.counitIso F.obj))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of sheaf categories. -/
@[simps]
/--
Definition of `sheafCongr` / `sheafCongr` 的定义

English:
definition sheafCongr
  signature: : Sheaf J A ≌ Sheaf K A where
  body: sheafCongr.functor J K e A
  inverse := sheafCongr.inverse J K e A
  unitIso := sheafCongr.unitIso J K e A
  counitIso := sheafCongr.counitIso J K e A
  functor_unitIso_comp X := by
    ext
    simp [← Functor.map_comp, ← op_comp]

中文:
定义 sheafCongr
  签名: : 层 J A ≌ 层 K A where
  定义体: sheafCongr.functor J K e A
  inverse := sheafCongr.inverse J K e A
  unitIso := sheafCongr.unitIso J K e A
  counitIso := sheafCongr.counitIso J K e A
  functor_unitIso_comp X := by
    ext
    simp [← Functor.map_comp, ← op_comp]

Depends on / 依赖: functor, sheafCongr, sheafCongr.functor
-/
def sheafCongr : Sheaf J A ≌ Sheaf K A where
  functor := sheafCongr.functor J K e A
  inverse := sheafCongr.inverse J K e A
  unitIso := sheafCongr.unitIso J K e A
  counitIso := sheafCongr.counitIso J K e A
  functor_unitIso_comp X := by
    ext
    simp [← Functor.map_comp, ← op_comp]

variable [HasSheafify K A]

/-- Transport a presheaf to the equivalent category and sheafify there. -/
noncomputable
/--
Definition of `transportAndSheafify` / `transportAndSheafify` 的定义

English:
definition transportAndSheafify
  signature: : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A
  body: e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J K A).inverse

中文:
定义 transportAndSheafify
  签名: : (Cᵒᵖ ⥤ A) ⥤ 层 J A
  定义体: e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J K A).inverse

Depends on / 依赖: congrLeft, e.op.congrLeft.functor, e.sheafCongr, functor, inverse, presheafToSheaf, sheafCongr
-/
def transportAndSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.op.congrLeft.functor ⋙ presheafToSheaf _ _ ⋙ (e.sheafCongr J K A).inverse

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An auxiliary definition for the sheafification adjunction. -/
noncomputable
/--
Definition of `transportIsoSheafToPresheaf` / `transportIsoSheafToPresheaf` 的定义

English:
definition transportIsoSheafToPresheaf
  signature: : (e.sheafCongr J K A).functor ⋙
  body: NatIso.ofComponents (fun F => isoWhiskerRight e.op.unitIso.symm F.obj)

中文:
定义 transportIsoSheafToPresheaf
  签名: : (e.sheafCongr J K A).functor ⋙
  定义体: NatIso.ofComponents (fun F => isoWhiskerRight e.op.unitIso.symm F.obj)

Depends on / 依赖: F.obj, NatIso, NatIso.ofComponents, e.op.unitIso.symm, isoWhiskerRight, ofComponents, unitIso
-/
def transportIsoSheafToPresheaf : (e.sheafCongr J K A).functor ⋙
    sheafToPresheaf K A ⋙ e.op.congrLeft.inverse ≅ sheafToPresheaf J A :=
  NatIso.ofComponents (fun F => isoWhiskerRight e.op.unitIso.symm F.obj)

/-- Transporting and sheafifying is left adjoint to taking the underlying presheaf. -/
noncomputable
/--
Definition of `transportSheafificationAdjunction` / `transportSheafificationAdjunction` 的定义

English:
definition transportSheafificationAdjunction
  signature: : transportAndSheafify J K e A ⊣ sheafToPresheaf J A
  body: ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (transportIsoSheafToPresheaf _ _ _ _)

中文:
定义 transportSheafificationAdjunction
  签名: : transportAndSheafify J K e A ⊣ sheafToPresheaf J A
  定义体: ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (transportIsoSheafToPresheaf _ _ _ _)

Depends on / 依赖: congrLeft, e.op.congrLeft.toAdjunction.comp, e.sheafCongr, ofNatIsoRight, sheafCongr, sheafificationAdjunction, symm.toAdjunction, toAdjunction, transportIsoSheafToPresheaf
-/
def transportSheafificationAdjunction : transportAndSheafify J K e A ⊣ sheafToPresheaf J A :=
  ((e.op.congrLeft.toAdjunction.comp (sheafificationAdjunction _ _)).comp
    (e.sheafCongr J K A).symm.toAdjunction).ofNatIsoRight
    (transportIsoSheafToPresheaf _ _ _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits transportAndSheafify J K e A
  body: comp_preservesLimitsOfShape _ _

include K e in

中文:
实例 :
  签名: 保持FiniteLimits transportAndSheafify J K e A
  定义体: comp_preservesLimitsOfShape _ _

include K e in

Depends on / 依赖: comp_preservesLimitsOfShape
-/
noncomputable instance : PreservesFiniteLimits transportAndSheafify J K e A where
  preservesFiniteLimits _ := comp_preservesLimitsOfShape _ _

include K e in
/--
theorem `hasSheafify` / 定理 `hasSheafify`

English:
theorem hasSheafify
  statement: HasSheafify J A
  proof: HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

中文:
定理 hasSheafify
  结论: 有Sheafify J A
  证明: HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

Depends on / 依赖: HasSheafify, HasSheafify.mk, transportSheafificationAdjunction
-/
theorem hasSheafify : HasSheafify J A :=
  HasSheafify.mk' J A (transportSheafificationAdjunction J K e A)

variable {A : Type*} [Category* A] {B : Type*} [Category* B] (F : A ⥤ B)
  [K.HasSheafCompose F]

include K e in
/--
theorem `hasSheafCompose` / 定理 `hasSheafCompose`

English:
theorem hasSheafCompose
  statement: J.HasSheafCompose F where
  proof: by
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

中文:
定理 hasSheafCompose
  结论: J.有SheafCompose F where
  证明: by
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

Depends on / 依赖: HasSheafCompose, HasSheafCompose.isSheaf, IsSheaf, Presheaf, Presheaf.IsSheaf, Presheaf.isSheaf_of_iso_iff, e.functor.op, e.functor.op_comp_isSheaf, e.inverse.op, e.inverse.op_comp_isSheaf, e.op.unitIso.symm, functor, inverse, isSheaf, isSheaf_of_iso_iff, isoWhiskerRight, op_comp_isSheaf, replace, unitIso
-/
theorem hasSheafCompose : J.HasSheafCompose F where
  isSheaf P hP := by
    have hP' : Presheaf.IsSheaf K (e.inverse.op ⋙ P ⋙ F) := by
      change Presheaf.IsSheaf K ((_ ⋙ _) ⋙ _)
      apply HasSheafCompose.isSheaf
      exact e.inverse.op_comp_isSheaf K J ⟨P, hP⟩
    replace hP' : Presheaf.IsSheaf J (e.functor.op ⋙ e.inverse.op ⋙ P ⋙ F) :=
      e.functor.op_comp_isSheaf _ _ ⟨_, hP'⟩
    exact (Presheaf.isSheaf_of_iso_iff ((isoWhiskerRight e.op.unitIso.symm (P ⋙ F)))).mp hP'

end Equivalence

variable (B : Type u₄) [Category.{v₄} B] (F : A ⥤ B)

section
variable [EssentiallySmall.{w} C]
variable [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A]
variable [((equivSmallModel C).inverse.inducedTopology J).HasSheafCompose F]

/-- Transport to a small model and sheafify there. -/
noncomputable
/--
Definition of `smallSheafify` / `smallSheafify` 的定义

English:
definition smallSheafify
  signature: : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A
  body: (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).inverse.inducedTopology J) A

中文:
定义 smallSheafify
  签名: : (Cᵒᵖ ⥤ A) ⥤ 层 J A
  定义体: (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).inverse.inducedTopology J) A

Depends on / 依赖: equivSmallModel, transportAndSheafify
-/
def smallSheafify : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A := (equivSmallModel C).transportAndSheafify J
  ((equivSmallModel C).inverse.inducedTopology J) A

/--
Transporting to a small model and sheafifying there is left adjoint to the underlying presheaf
functor
-/
noncomputable
/--
Definition of `smallSheafificationAdjunction` / `smallSheafificationAdjunction` 的定义

English:
definition smallSheafificationAdjunction
  signature: : smallSheafify J A ⊣ sheafToPresheaf J A
  body: (equivSmallModel C).transportSheafificationAdjunction J _ A

中文:
定义 smallSheafificationAdjunction
  签名: : smallSheafify J A ⊣ sheafToPresheaf J A
  定义体: (equivSmallModel C).transportSheafificationAdjunction J _ A

Depends on / 依赖: equivSmallModel, transportSheafificationAdjunction
-/
def smallSheafificationAdjunction : smallSheafify J A ⊣ sheafToPresheaf J A :=
  (equivSmallModel C).transportSheafificationAdjunction J _ A

/--
lemma `hasSheafifyEssentiallySmallSite` / 引理 `hasSheafifyEssentiallySmallSite`

English:
lemma hasSheafifyEssentiallySmallSite
  statement: HasSheafify J A
  proof: (equivSmallModel C).hasSheafify J ((equivSmallModel C).inverse.inducedTopology J) A

中文:
引理 hasSheafifyEssentiallySmallSite
  结论: 有Sheafify J A
  证明: (equivSmallModel C).hasSheafify J ((equivSmallModel C).inverse.inducedTopology J) A

Depends on / 依赖: equivSmallModel, hasSheafify, inducedTopology, inverse, inverse.inducedTopology
-/
lemma hasSheafifyEssentiallySmallSite : HasSheafify J A :=
  (equivSmallModel C).hasSheafify J ((equivSmallModel C).inverse.inducedTopology J) A

/--
Instance `hasSheafComposeEssentiallySmallSite` / 实例 `hasSheafComposeEssentiallySmallSite`

English:
instance hasSheafComposeEssentiallySmallSite
  signature: : HasSheafCompose J F
  body: (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).inverse.inducedTopology J) F

omit [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] in

中文:
实例 hasSheafComposeEssentiallySmallSite
  签名: : 有SheafCompose J F
  定义体: (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).inverse.inducedTopology J) F

omit [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] in

Depends on / 依赖: equivSmallModel, hasSheafCompose, inducedTopology, inverse, inverse.inducedTopology
-/
instance hasSheafComposeEssentiallySmallSite : HasSheafCompose J F :=
  (equivSmallModel C).hasSheafCompose J ((equivSmallModel C).inverse.inducedTopology J) F

omit [HasSheafify ((equivSmallModel C).inverse.inducedTopology J) A] in
/--
lemma `hasLimitsEssentiallySmallSite` / 引理 `hasLimitsEssentiallySmallSite`

English:
lemma hasLimitsEssentiallySmallSite
  proof: Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

中文:
引理 hasLimitsEssentiallySmallSite
  证明: Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

Depends on / 依赖: Adjunction, Adjunction.has_limits_of_equivalence, equivSmallModel, functor, has_limits_of_equivalence, inducedTopology, inverse, inverse.inducedTopology, sheafCongr
-/
lemma hasLimitsEssentiallySmallSite
    [HasLimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
HasLimitsOfSize.{max v₃ w, max v₃ w} Sheaf J A :=
  Adjunction.has_limits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

/--
Instance `hasColimitsEssentiallySmallSite` / 实例 `hasColimitsEssentiallySmallSite`

English:
instance hasColimitsEssentiallySmallSite
  body: Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

中文:
实例 hasColimitsEssentiallySmallSite
  定义体: Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

Depends on / 依赖: Adjunction, Adjunction.has_colimits_of_equivalence, equivSmallModel, functor, has_colimits_of_equivalence, inducedTopology, inverse, inverse.inducedTopology, sheafCongr
-/
instance hasColimitsEssentiallySmallSite
    [HasColimits <| Sheaf ((equivSmallModel C).inverse.inducedTopology J) A] :
HasColimitsOfSize.{max v₃ w, max v₃ w} Sheaf J A :=
  Adjunction.has_colimits_of_equivalence ((equivSmallModel C).sheafCongr J
    ((equivSmallModel C).inverse.inducedTopology J) A).functor

end

namespace GrothendieckTopology

variable {A}
variable [G.IsCoverDense J] [G.Full]

section
variable [Functor.IsContinuous G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]

open Localization

set_option backward.isDefEq.respectTransparency false in
/--
lemma `W_inverseImage_whiskeringLeft` / 引理 `W_inverseImage_whiskeringLeft`

English:
lemma W_inverseImage_whiskeringLeft
  proof: by
  ext P Q f
  have h₁ : K.W (A := A) =
    ObjectProperty.isLocal (· in Set.range (sheafToPresheaf J A ⋙
      ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op)).obj) := by
    rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [← ObjectProperty.isoClosure_isLocal]
    conv_rhs => rw [← ObjectProperty.isoClosure_isLocal]
    apply congr_arg
    ext P
    constructor
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨_, ⟨_, rfl⟩, ⟨e.trans ((sheafToPresheaf _ _).mapIso
        ((G.sheafPushforwardContinuous A K J).objObjPreimageIso R).symm)⟩⟩
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨G.op ⋙ R.obj, ⟨(G.sheafPushforwardContinuous A K J).obj R, rfl⟩, ⟨e⟩⟩
  have h₂ : forall (R : Sheaf J A),
    Function.Bijective (fun (g : G.op ⋙ Q ⟶ G.op ⋙ R.obj) => whiskerLeft G.op f ≫ g) ↔
      Function.Bijective (fun (g : Q ⟶ R.obj) => f ≫ g) := fun R => by
    rw [← Function.Bijective.of_comp_iff _
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G Q R.obj R.property)]
    exact Function.Bijective.of_comp_iff'
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P R.obj R.property)
        (fun g => f ≫ g)
  rw [h₁]; rw [J.W_eq_isLocal_range_sheafToPresheaf_obj]; rw [MorphismProperty.inverseImage_iff]
  constructor
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).1 (h _ ⟨R, rfl⟩)
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).2 (h _ ⟨R, rfl⟩)

中文:
引理 W_inverseImage_whiskeringLeft
  证明: by
  ext P Q f
  have h₁ : K.W (A := A) =
    ObjectProperty.isLocal (· in Set.range (sheafToPresheaf J A ⋙
      ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op)).obj) := by
    rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [← ObjectProperty.isoClosure_isLocal]
    conv_rhs => rw [← ObjectProperty.isoClosure_isLocal]
    apply congr_arg
    ext P
    constructor
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨_, ⟨_, rfl⟩, ⟨e.trans ((sheafToPresheaf _ _).mapIso
        ((G.sheafPushforwardContinuous A K J).objObjPreimageIso R).symm)⟩⟩
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨G.op ⋙ R.obj, ⟨(G.sheafPushforwardContinuous A K J).obj R, rfl⟩, ⟨e⟩⟩
  have h₂ : forall (R : Sheaf J A),
    Function.Bijective (fun (g : G.op ⋙ Q ⟶ G.op ⋙ R.obj) => whiskerLeft G.op f ≫ g) ↔
      Function.Bijective (fun (g : Q ⟶ R.obj) => f ≫ g) := fun R => by
    rw [← Function.Bijective.of_comp_iff _
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G Q R.obj R.property)]
    exact Function.Bijective.of_comp_iff'
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P R.obj R.property)
        (fun g => f ≫ g)
  rw [h₁]; rw [J.W_eq_isLocal_range_sheafToPresheaf_obj]; rw [MorphismProperty.inverseImage_iff]
  constructor
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).1 (h _ ⟨R, rfl⟩)
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).2 (h _ ⟨R, rfl⟩)

Depends on / 依赖: G.op, G.sheafPushforwardContinuous, ObjectProperty, ObjectProperty.isLocal, ObjectProperty.isoClosure_isLocal, Set.range, W_eq_isLocal_range_sheafToPresheaf_obj, congr_arg, conv_rhs, e.trans, isLocal, isoClosure_isLocal, mapIso, objObjPreimageIso, sheafPushforwardContinuous, sheafToPresheaf, whiskeringLeft
-/
lemma W_inverseImage_whiskeringLeft :
    K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op) = J.W := by
  ext P Q f
  have h₁ : K.W (A := A) =
    ObjectProperty.isLocal (· in Set.range (sheafToPresheaf J A ⋙
      ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op)).obj) := by
    rw [W_eq_isLocal_range_sheafToPresheaf_obj]; rw [← ObjectProperty.isoClosure_isLocal]
    conv_rhs => rw [← ObjectProperty.isoClosure_isLocal]
    apply congr_arg
    ext P
    constructor
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨_, ⟨_, rfl⟩, ⟨e.trans ((sheafToPresheaf _ _).mapIso
        ((G.sheafPushforwardContinuous A K J).objObjPreimageIso R).symm)⟩⟩
    · rintro ⟨_, ⟨R, rfl⟩, ⟨e⟩⟩
      exact ⟨G.op ⋙ R.obj, ⟨(G.sheafPushforwardContinuous A K J).obj R, rfl⟩, ⟨e⟩⟩
  have h₂ : forall (R : Sheaf J A),
    Function.Bijective (fun (g : G.op ⋙ Q ⟶ G.op ⋙ R.obj) => whiskerLeft G.op f ≫ g) ↔
      Function.Bijective (fun (g : Q ⟶ R.obj) => f ≫ g) := fun R => by
    rw [← Function.Bijective.of_comp_iff _
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G Q R.obj R.property)]
    exact Function.Bijective.of_comp_iff'
      (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense J G P R.obj R.property)
        (fun g => f ≫ g)
  rw [h₁]; rw [J.W_eq_isLocal_range_sheafToPresheaf_obj]; rw [MorphismProperty.inverseImage_iff]
  constructor
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).1 (h _ ⟨R, rfl⟩)
  · rintro h _ ⟨R, rfl⟩
    exact (h₂ R).2 (h _ ⟨R, rfl⟩)

/--
lemma `W_whiskerLeft_iff` / 引理 `W_whiskerLeft_iff`

English:
lemma W_whiskerLeft_iff
  given: {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q)
  proof: by
  rw [← W_inverseImage_whiskeringLeft J K G]
  rfl

中文:
引理 W_whiskerLeft_iff
  条件: {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q)
  证明: by
  rw [← W_inverseImage_whiskeringLeft J K G]
  rfl

Depends on / 依赖: W_inverseImage_whiskeringLeft
-/
lemma W_whiskerLeft_iff {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    K.W (whiskerLeft G.op f) ↔ J.W f := by
  rw [← W_inverseImage_whiskeringLeft J K G]
  rfl

end

/--
lemma `PreservesSheafification.transport` / 引理 `PreservesSheafification.transport`

English:
lemma PreservesSheafification.transport
  proof: by
    rw [← J.W_whiskerLeft_iff (G := G) (K := K)] at hf
    have := K.W_of_preservesSheafification F (whiskerLeft G.op f) hf
    rw [whiskerRight_left] at this
have := K.W.of_postcomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_inv _)
      K.W.of_precomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_hom _) this
    rwa [K.W_whiskerLeft_iff (G := G) (J := J) (f := whiskerRight f F)] at this

中文:
引理 保持层化.transport
  证明: by
    rw [← J.W_whiskerLeft_iff (G := G) (K := K)] at hf
    have := K.W_of_preservesSheafification F (whiskerLeft G.op f) hf
    rw [whiskerRight_left] at this
have := K.W.of_postcomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_inv _)
      K.W.of_precomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_hom _) this
    rwa [K.W_whiskerLeft_iff (G := G) (J := J) (f := whiskerRight f F)] at this

Depends on / 依赖: G.op, Iso.isIso_hom, Iso.isIso_inv, J.W_whiskerLeft_iff, K.W.of_postcomp, K.W.of_precomp, K.W_of_preservesSheafification, K.W_whiskerLeft_iff, MorphismProperty, MorphismProperty.isomorphisms, W_of_preservesSheafification, W_whiskerLeft_iff, isIso_hom, isIso_inv, isomorphisms, of_postcomp, of_precomp, whiskerLeft, whiskerRight, whiskerRight_left
-/
lemma PreservesSheafification.transport
    [Functor.IsContinuous G K J]
    [(G.sheafPushforwardContinuous B K J).EssSurj]
    [(G.sheafPushforwardContinuous A K J).EssSurj]
    [K.PreservesSheafification F] : J.PreservesSheafification F where
  le P Q f hf := by
    rw [← J.W_whiskerLeft_iff (G := G) (K := K)] at hf
    have := K.W_of_preservesSheafification F (whiskerLeft G.op f) hf
    rw [whiskerRight_left] at this
have := K.W.of_postcomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_inv _)
      K.W.of_precomp (W' := MorphismProperty.isomorphisms _) _ _ (Iso.isIso_hom _) this
    rwa [K.W_whiskerLeft_iff (G := G) (J := J) (f := whiskerRight f F)] at this

variable [Functor.IsContinuous G K J] [(G.sheafPushforwardContinuous A K J).EssSurj]
variable [G.IsCocontinuous K J] {FA : A -> A -> Type*} {CA : A -> Type*}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable [K.WEqualsLocallyBijective A]

/--
lemma `WEqualsLocallyBijective.transport` / 引理 `WEqualsLocallyBijective.transport`

English:
lemma WEqualsLocallyBijective.transport
  given: (hG : CoverPreserving K J G)
  proof: by
    rw [← W_whiskerLeft_iff J K G f]; rw [← Presheaf.isLocallyInjective_whisker_iff K J G f hG]; rw [← Presheaf.isLocallySurjective_whisker_iff K J G f hG]; rw [W_iff_isLocallyBijective]

中文:
引理 WEqualsLocallyBijective.transport
  条件: (hG : 余verPreserving K J G)
  证明: by
    rw [← W_whiskerLeft_iff J K G f]; rw [← Presheaf.isLocallyInjective_whisker_iff K J G f hG]; rw [← Presheaf.isLocallySurjective_whisker_iff K J G f hG]; rw [W_iff_isLocallyBijective]

Depends on / 依赖: Presheaf, Presheaf.isLocallyInjective_whisker_iff, Presheaf.isLocallySurjective_whisker_iff, W_iff_isLocallyBijective, W_whiskerLeft_iff, isLocallyInjective_whisker_iff, isLocallySurjective_whisker_iff
-/
lemma WEqualsLocallyBijective.transport (hG : CoverPreserving K J G) :
    J.WEqualsLocallyBijective A where
  iff f := by
    rw [← W_whiskerLeft_iff J K G f]; rw [← Presheaf.isLocallyInjective_whisker_iff K J G f hG]; rw [← Presheaf.isLocallySurjective_whisker_iff K J G f hG]; rw [W_iff_isLocallyBijective]

variable [EssentiallySmall.{w} C]
  [forall (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) A]

/--
lemma `WEqualsLocallyBijective.ofEssentiallySmall` / 引理 `WEqualsLocallyBijective.ofEssentiallySmall`

English:
lemma WEqualsLocallyBijective.ofEssentiallySmall
  proof: WEqualsLocallyBijective.transport J ((equivSmallModel C).inverse.inducedTopology J)
    (equivSmallModel C).inverse (IsDenseSubsite.coverPreserving _ _ _)

中文:
引理 WEqualsLocallyBijective.ofEssentiallySmall
  证明: WEqualsLocallyBijective.transport J ((equivSmallModel C).inverse.inducedTopology J)
    (equivSmallModel C).inverse (IsDenseSubsite.coverPreserving _ _ _)

Depends on / 依赖: IsDenseSubsite, IsDenseSubsite.coverPreserving, WEqualsLocallyBijective, WEqualsLocallyBijective.transport, coverPreserving, equivSmallModel, inducedTopology, inverse, inverse.inducedTopology, transport
-/
lemma WEqualsLocallyBijective.ofEssentiallySmall
    [((equivSmallModel C).inverse.inducedTopology J).WEqualsLocallyBijective A] :
    J.WEqualsLocallyBijective A :=
  WEqualsLocallyBijective.transport J ((equivSmallModel C).inverse.inducedTopology J)
    (equivSmallModel C).inverse (IsDenseSubsite.coverPreserving _ _ _)

variable [forall (X : Cᵒᵖ), HasLimitsOfShape (StructuredArrow X (equivSmallModel C).inverse.op) B]
variable [PreservesSheafification ((equivSmallModel C).inverse.inducedTopology J) F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesSheafification J F
  body: PreservesSheafification.transport (A := A) J
    ((equivSmallModel C).inverse.inducedTopology J) (equivSmallModel C).inverse B F

中文:
实例 :
  签名: 保持层化 J F
  定义体: PreservesSheafification.transport (A := A) J
    ((equivSmallModel C).inverse.inducedTopology J) (equivSmallModel C).inverse B F

Depends on / 依赖: PreservesSheafification, PreservesSheafification.transport, equivSmallModel, inducedTopology, inverse, inverse.inducedTopology, transport
-/
instance : PreservesSheafification J F :=
  PreservesSheafification.transport (A := A) J
    ((equivSmallModel C).inverse.inducedTopology J) (equivSmallModel C).inverse B F

end GrothendieckTopology

end CategoryTheory
