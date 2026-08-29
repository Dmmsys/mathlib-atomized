/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# Adjoints of fully faithful functors

A left adjoint is
* faithful, if and only if the unit is a monomorphism
* full, if and only if the unit is a split epimorphism
* fully faithful, if and only if the unit is an isomorphism

A right adjoint is
* faithful, if and only if the counit is an epimorphism
* full, if and only if the counit is a split monomorphism
* fully faithful, if and only if the counit is an isomorphism

This is Lemma 4.5.13 in Riehl's *Category Theory in Context* [riehl2017].
See also https://stacks.math.columbia.edu/tag/07RB for the statements about fully faithful functors.

In the file `Mathlib/CategoryTheory/Monad/Adjunction.lean`, we prove that in fact, if there exists
an isomorphism `L ⋙ R ≅ 𝟭 C`, then the unit is an isomorphism, and similarly for the counit.
See `CategoryTheory.Adjunction.isIso_unit_of_iso` and
`CategoryTheory.Adjunction.isIso_counit_of_iso`.
-/

@[expose] public section


open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

open Category CategoryTheory.Functor

open Opposite

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

attribute [local simp] homEquiv_unit homEquiv_counit

set_option backward.defeqAttrib.useBackward true in
/--
Instance `unit_mono_of_L_faithful` / 实例 `unit_mono_of_L_faithful`

English:
instance unit_mono_of_L_faithful
  signature: [L.Faithful] (X : C)
  body: L.map_injective (h.homEquiv Y (L.obj X)).injective by simpa using hfg

中文:
实例 unit_mono_of_L_faithful
  签名: [L.忠实] (X : C)
  定义体: L.map_injective (h.homEquiv Y (L.obj X)).injective by simpa using hfg

Depends on / 依赖: L.map_injective, L.obj, h.homEquiv, homEquiv, injective, map_injective
-/
instance unit_mono_of_L_faithful [L.Faithful] (X : C) : Mono (h.unit.app X) where
  right_cancellation {Y} f g hfg :=
L.map_injective (h.homEquiv Y (L.obj X)).injective by simpa using hfg

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unitSplitEpiOfLFull` / `unitSplitEpiOfLFull` 的定义

English:
definition unitSplitEpiOfLFull
  signature: [L.Full] (X : C)
  body: L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]

中文:
定义 unitSplitEpiOfLFull
  签名: [L.满] (X : C)
  定义体: L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]
-/
noncomputable def unitSplitEpiOfLFull [L.Full] (X : C) : SplitEpi (h.unit.app X) where
  section_ := L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]

/--
Instance `unit_isSplitEpi_of_L_full` / 实例 `unit_isSplitEpi_of_L_full`

English:
instance unit_isSplitEpi_of_L_full
  signature: [L.Full] (X : C)
  body: ⟨⟨h.unitSplitEpiOfLFull X⟩⟩

中文:
实例 unit_isSplitEpi_of_L_full
  签名: [L.满] (X : C)
  定义体: ⟨⟨h.unitSplitEpiOfLFull X⟩⟩

Depends on / 依赖: h.unitSplitEpiOfLFull, unitSplitEpiOfLFull
-/
instance unit_isSplitEpi_of_L_full [L.Full] (X : C) : IsSplitEpi (h.unit.app X) :=
  ⟨⟨h.unitSplitEpiOfLFull X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.Full]
  signature: [L.Faithful] (X : C)
  body: isIso_of_mono_of_isSplitEpi _

中文:
实例 [L.满]
  签名: [L.忠实] (X : C)
  定义体: isIso_of_mono_of_isSplitEpi _

Depends on / 依赖: isIso_of_mono_of_isSplitEpi
-/
instance [L.Full] [L.Faithful] (X : C) : IsIso (h.unit.app X) :=
  isIso_of_mono_of_isSplitEpi _

/--
Instance `unit_isIso_of_L_fully_faithful` / 实例 `unit_isIso_of_L_fully_faithful`

English:
instance unit_isIso_of_L_fully_faithful
  signature: [L.Full] [L.Faithful]
  body: NatIso.isIso_of_isIso_app _

中文:
实例 unit_isIso_of_L_fully_faithful
  签名: [L.满] [L.忠实]
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance unit_isIso_of_L_fully_faithful [L.Full] [L.Faithful] : IsIso (Adjunction.unit h) :=
  NatIso.isIso_of_isIso_app _

/--
Instance `counit_epi_of_R_faithful` / 实例 `counit_epi_of_R_faithful`

English:
instance counit_epi_of_R_faithful
  signature: [R.Faithful] (X : D)
  body: R.map_injective (h.homEquiv (R.obj X) Y).symm.injective by simpa using! hfg

中文:
实例 counit_epi_of_R_faithful
  签名: [R.忠实] (X : D)
  定义体: R.map_injective (h.homEquiv (R.obj X) Y).symm.injective by simpa using! hfg

Depends on / 依赖: R.map_injective, R.obj, h.homEquiv, homEquiv, injective, map_injective, symm.injective
-/
instance counit_epi_of_R_faithful [R.Faithful] (X : D) : Epi (h.counit.app X) where
  left_cancellation {Y} f g hfg :=
R.map_injective (h.homEquiv (R.obj X) Y).symm.injective by simpa using! hfg

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `counitSplitMonoOfRFull` / `counitSplitMonoOfRFull` 的定义

English:
definition counitSplitMonoOfRFull
  signature: [R.Full] (X : D)
  body: R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

中文:
定义 counitSplitMonoOfRFull
  签名: [R.满] (X : D)
  定义体: R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

Depends on / 依赖: R.obj, R.preimage, h.unit.app, preimage
-/
noncomputable def counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
  retraction := R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

/--
Instance `counit_isSplitMono_of_R_full` / 实例 `counit_isSplitMono_of_R_full`

English:
instance counit_isSplitMono_of_R_full
  signature: [R.Full] (X : D)
  body: ⟨⟨h.counitSplitMonoOfRFull X⟩⟩

中文:
实例 counit_isSplitMono_of_R_full
  签名: [R.满] (X : D)
  定义体: ⟨⟨h.counitSplitMonoOfRFull X⟩⟩

Depends on / 依赖: counitSplitMonoOfRFull, h.counitSplitMonoOfRFull
-/
instance counit_isSplitMono_of_R_full [R.Full] (X : D) : IsSplitMono (h.counit.app X) :=
  ⟨⟨h.counitSplitMonoOfRFull X⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.Full]
  signature: [R.Faithful] (X : D)
  body: isIso_of_epi_of_isSplitMono _

中文:
实例 [R.满]
  签名: [R.忠实] (X : D)
  定义体: isIso_of_epi_of_isSplitMono _

Depends on / 依赖: isIso_of_epi_of_isSplitMono
-/
instance [R.Full] [R.Faithful] (X : D) : IsIso (h.counit.app X) :=
  isIso_of_epi_of_isSplitMono _

/--
Instance `counit_isIso_of_R_fully_faithful` / 实例 `counit_isIso_of_R_fully_faithful`

English:
instance counit_isIso_of_R_fully_faithful
  signature: [R.Full] [R.Faithful]
  body: NatIso.isIso_of_isIso_app _

中文:
实例 counit_isIso_of_R_fully_faithful
  签名: [R.满] [R.忠实]
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance counit_isIso_of_R_fully_faithful [R.Full] [R.Faithful] : IsIso (Adjunction.counit h) :=
  NatIso.isIso_of_isIso_app _

/-- If the unit of an adjunction is an isomorphism, then its inverse on the image of L is given
by L whiskered with the counit. -/
@[simp]
/--
theorem `inv_map_unit` / 定理 `inv_map_unit`

English:
theorem inv_map_unit
  given: {X : C} [IsIso (h.unit.app X)]
  proof: IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)

中文:
定理 inv_map_unit
  条件: {X : C} [是同构 (h.unit.app X)]
  证明: IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, h.left_triangle_components, inv_eq_of_hom_inv_id, left_triangle_components
-/
theorem inv_map_unit {X : C} [IsIso (h.unit.app X)] :
    inv (L.map (h.unit.app X)) = h.counit.app (L.obj X) :=
  IsIso.inv_eq_of_hom_inv_id (h.left_triangle_components X)

/-- If the unit of an adjunction is an isomorphism, then one has an isomorphism `L ⋙ R ⋙ L ≅ L`. -/
@[simps!]
/--
Definition of `whiskerLeftLCounitIsoOfIsIsoUnit` / `whiskerLeftLCounitIsoOfIsIsoUnit` 的定义

English:
definition whiskerLeftLCounitIsoOfIsIsoUnit
  signature: [IsIso h.unit]
  body: (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _

中文:
定义 whiskerLeftLCounitIsoOfIsIsoUnit
  签名: [是同构 h.unit]
  定义体: (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _

Depends on / 依赖: Functor, Functor.leftUnitor, L.associator, associator, h.unit, isoWhiskerRight, leftUnitor
-/
noncomputable def whiskerLeftLCounitIsoOfIsIsoUnit [IsIso h.unit] : L ⋙ R ⋙ L ≅ L :=
  (L.associator R L).symm ≪≫ isoWhiskerRight (asIso h.unit).symm L ≪≫ Functor.leftUnitor _

/-- If the counit of an adjunction is an isomorphism, then its inverse on the image of R is given
by R whiskered with the unit. -/
@[simp]
/--
theorem `inv_counit_map` / 定理 `inv_counit_map`

English:
theorem inv_counit_map
  given: {X : D} [IsIso (h.counit.app X)]
  proof: IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)

中文:
定理 inv_counit_map
  条件: {X : D} [是同构 (h.counit.app X)]
  证明: IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)

Depends on / 依赖: IsIso.inv_eq_of_inv_hom_id, h.right_triangle_components, inv_eq_of_inv_hom_id, right_triangle_components
-/
theorem inv_counit_map {X : D} [IsIso (h.counit.app X)] :
    inv (R.map (h.counit.app X)) = h.unit.app (R.obj X) :=
  IsIso.inv_eq_of_inv_hom_id (h.right_triangle_components X)

/-- If the counit of an adjunction is an isomorphism, then one has an isomorphism
`(R ⋙ L ⋙ R) ≅ R`. -/
@[simps!]
/--
Definition of `whiskerLeftRUnitIsoOfIsIsoCounit` / `whiskerLeftRUnitIsoOfIsIsoCounit` 的定义

English:
definition whiskerLeftRUnitIsoOfIsIsoCounit
  signature: [IsIso h.counit]
  body: (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _

中文:
定义 whiskerLeftRUnitIsoOfIsIsoCounit
  签名: [是同构 h.counit]
  定义体: (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _

Depends on / 依赖: Functor, Functor.leftUnitor, R.associator, associator, counit, h.counit, isoWhiskerRight, leftUnitor
-/
noncomputable def whiskerLeftRUnitIsoOfIsIsoCounit [IsIso h.counit] : R ⋙ L ⋙ R ≅ R :=
  (R.associator L R).symm ≪≫ isoWhiskerRight (asIso h.counit) R ≪≫ Functor.leftUnitor _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `faithful_L_of_mono_unit_app` / 引理 `faithful_L_of_mono_unit_app`

English:
lemma faithful_L_of_mono_unit_app
  given: [forall X, Mono (h.unit.app X)]
  statement: L.Faithful where
  proof: by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg

中文:
引理 faithful_L_of_mono_unit_app
  条件: [对任意 X, 单态射 (h.unit.app X)]
  结论: L.忠实 where
  证明: by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg

Depends on / 依赖: L.obj, Mono.right_cancellation, h.homEquiv, h.unit.app, homEquiv, injective, right_cancellation, symm.injective
-/
lemma faithful_L_of_mono_unit_app [forall X, Mono (h.unit.app X)] : L.Faithful where
  map_injective {X Y f g} hfg := by
    apply Mono.right_cancellation (f := h.unit.app Y)
    apply (h.homEquiv X (L.obj Y)).symm.injective
    simpa using hfg

/--
lemma `full_L_of_isSplitEpi_unit_app` / 引理 `full_L_of_isSplitEpi_unit_app`

English:
lemma full_L_of_isSplitEpi_unit_app
  given: [forall X, IsSplitEpi (h.unit.app X)]
  statement: L.Full where
  proof: by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    suffices L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) by simp [this]
    rw [← comp_id (L.map (section_ (h.unit.app Y)))]
    simp only [Functor.id_obj, ← h.left_triangle_components Y,
      ← assoc, ← Functor.map_comp

中文:
引理 full_L_of_isSplitEpi_unit_app
  条件: [对任意 X, 是分裂满态射 (h.unit.app X)]
  结论: L.满 where
  证明: by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    suffices L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) by simp [this]
    rw [← comp_id (L.map (section_ (h.unit.app Y)))]
    simp only [Functor.id_obj, ← h.left_triangle_components Y,
      ← assoc, ← Functor.map_comp

Depends on / 依赖: Functor, Functor.id_obj, Functor.map_comp, Functor.map_id, IsSplitEpi, IsSplitEpi.id, L.map, L.obj, comp_id, counit, h.counit.app, h.homEquiv, h.left_triangle_components, h.unit.app, homEquiv, id_comp, id_obj, left_triangle_components, map_comp, map_id
-/
lemma full_L_of_isSplitEpi_unit_app [forall X, IsSplitEpi (h.unit.app X)] : L.Full where
  map_surjective {X Y} f := by
    use ((h.homEquiv X (L.obj Y)) f ≫ section_ (h.unit.app Y))
    suffices L.map (section_ (h.unit.app Y)) = h.counit.app (L.obj Y) by simp [this]
    rw [← comp_id (L.map (section_ (h.unit.app Y)))]
    simp only [Functor.id_obj, ← h.left_triangle_components Y,
      ← assoc, ← Functor.map_comp, IsSplitEpi.id, Functor.map_id, id_comp]

/--
Definition of `fullyFaithfulLOfIsIsoUnit` / `fullyFaithfulLOfIsIsoUnit` 的定义

English:
definition fullyFaithfulLOfIsIsoUnit
  signature: [IsIso h.unit]
  body: h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)

中文:
定义 fullyFaithfulLOfIsIsoUnit
  签名: [是同构 h.unit]
  定义体: h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)

Depends on / 依赖: L.obj, h.homEquiv, h.unit.app, homEquiv
-/
noncomputable def fullyFaithfulLOfIsIsoUnit [IsIso h.unit] : L.FullyFaithful where
  preimage {_ Y} f := h.homEquiv _ (L.obj Y) f ≫ inv (h.unit.app Y)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `faithful_R_of_epi_counit_app` / 引理 `faithful_R_of_epi_counit_app`

English:
lemma faithful_R_of_epi_counit_app
  given: [forall X, Epi (h.counit.app X)]
  statement: R.Faithful where
  proof: by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg

中文:
引理 faithful_R_of_epi_counit_app
  条件: [对任意 X, 满态射 (h.counit.app X)]
  结论: R.忠实 where
  证明: by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg

Depends on / 依赖: Epi.left_cancellation, R.obj, counit, h.counit.app, h.homEquiv, homEquiv, injective, left_cancellation
-/
lemma faithful_R_of_epi_counit_app [forall X, Epi (h.counit.app X)] : R.Faithful where
  map_injective {X Y f g} hfg := by
    apply Epi.left_cancellation (f := h.counit.app X)
    apply (h.homEquiv (R.obj X) Y).injective
    simpa using hfg

/--
lemma `full_R_of_isSplitMono_counit_app` / 引理 `full_R_of_isSplitMono_counit_app`

English:
lemma full_R_of_isSplitMono_counit_app
  given: [forall X, IsSplitMono (h.counit.app X)]
  statement: R.Full where
  proof: by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    suffices R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) by simp [this]
    rw [← id_comp (R.map (retraction (h.counit.app X)))]
    simp only [Functor.id_obj, ← h.right_triangle_components X,
      assoc, ← Fu

中文:
引理 full_R_of_isSplitMono_counit_app
  条件: [对任意 X, 是分裂单态射 (h.counit.app X)]
  结论: R.满 where
  证明: by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    suffices R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) by simp [this]
    rw [← id_comp (R.map (retraction (h.counit.app X)))]
    simp only [Functor.id_obj, ← h.right_triangle_components X,
      assoc, ← Fu

Depends on / 依赖: Functor, Functor.id_obj, Functor.map_comp, Functor.map_id, IsSplitMono, IsSplitMono.id, R.map, R.obj, comp_id, counit, h.counit.app, h.homEquiv, h.right_triangle_components, h.unit.app, homEquiv, id_comp, id_obj, map_comp, map_id, retraction
-/
lemma full_R_of_isSplitMono_counit_app [forall X, IsSplitMono (h.counit.app X)] : R.Full where
  map_surjective {X Y} f := by
    use (retraction (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f)
    suffices R.map (retraction (h.counit.app X)) = h.unit.app (R.obj X) by simp [this]
    rw [← id_comp (R.map (retraction (h.counit.app X)))]
    simp only [Functor.id_obj, ← h.right_triangle_components X,
      assoc, ← Functor.map_comp, IsSplitMono.id, Functor.map_id, comp_id]

/--
Definition of `fullyFaithfulROfIsIsoCounit` / `fullyFaithfulROfIsIsoCounit` 的定义

English:
definition fullyFaithfulROfIsIsoCounit
  signature: [IsIso h.counit]
  body: inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f

中文:
定义 fullyFaithfulROfIsIsoCounit
  签名: [是同构 h.counit]
  定义体: inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f

Depends on / 依赖: R.obj, counit, h.counit.app, h.homEquiv, homEquiv
-/
noncomputable def fullyFaithfulROfIsIsoCounit [IsIso h.counit] : R.FullyFaithful where
  preimage {X Y} f := inv (h.counit.app X) ≫ (h.homEquiv (R.obj X) Y).symm f

/--
Instance `whiskerLeft_counit_iso_of_L_fully_faithful` / 实例 `whiskerLeft_counit_iso_of_L_fully_faithful`

English:
instance whiskerLeft_counit_iso_of_L_fully_faithful
  signature: [L.Full] [L.Faithful]
  body: by
  have := ((Functor.associator ..).inv ≫ whiskerRight (inv h.unit) L) ≫= h.left_triangle
  simp only [assoc, ← whiskerRight_comp_assoc, IsIso.inv_hom_id, whiskerRight_id', id_comp,
    Iso.inv_hom_id_assoc] at this
  rw [this]
  infer_instance

中文:
实例 whiskerLeft_counit_iso_of_L_fully_faithful
  签名: [L.满] [L.忠实]
  定义体: by
  have := ((Functor.associator ..).inv ≫ whiskerRight (inv h.unit) L) ≫= h.left_triangle
  simp only [assoc, ← whiskerRight_comp_assoc, IsIso.inv_hom_id, whiskerRight_id', id_comp,
    Iso.inv_hom_id_assoc] at this
  rw [this]
  infer_instance

Depends on / 依赖: Functor, Functor.associator, IsIso.inv_hom_id, Iso.inv_hom_id_assoc, associator, h.left_triangle, h.unit, id_comp, infer_instance, inv_hom_id, inv_hom_id_assoc, left_triangle, whiskerRight, whiskerRight_comp_assoc, whiskerRight_id
-/
instance whiskerLeft_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerLeft L h.counit) := by
  have := ((Functor.associator ..).inv ≫ whiskerRight (inv h.unit) L) ≫= h.left_triangle
  simp only [assoc, ← whiskerRight_comp_assoc, IsIso.inv_hom_id, whiskerRight_id', id_comp,
    Iso.inv_hom_id_assoc] at this
  rw [this]
  infer_instance

/--
Instance `whiskerRight_counit_iso_of_L_fully_faithful` / 实例 `whiskerRight_counit_iso_of_L_fully_faithful`

English:
instance whiskerRight_counit_iso_of_L_fully_faithful
  signature: [L.Full] [L.Faithful]
  body: by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp]; rw [Iso.inv_comp_eq] at this
  rw [this]
  infer_instance

中文:
实例 whiskerRight_counit_iso_of_L_fully_faithful
  签名: [L.满] [L.忠实]
  定义体: by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp]; rw [Iso.inv_comp_eq] at this
  rw [this]
  infer_instance

Depends on / 依赖: IsIso.eq_inv_comp, Iso.inv_comp_eq, eq_inv_comp, h.right_triangle, infer_instance, inv_comp_eq, right_triangle
-/
instance whiskerRight_counit_iso_of_L_fully_faithful [L.Full] [L.Faithful] :
    IsIso (whiskerRight h.counit R) := by
  have := h.right_triangle
  rw [← IsIso.eq_inv_comp]; rw [Iso.inv_comp_eq] at this
  rw [this]
  infer_instance

/--
Instance `whiskerLeft_unit_iso_of_R_fully_faithful` / 实例 `whiskerLeft_unit_iso_of_R_fully_faithful`

English:
instance whiskerLeft_unit_iso_of_R_fully_faithful
  signature: [R.Full] [R.Faithful]
  body: by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

中文:
实例 whiskerLeft_unit_iso_of_R_fully_faithful
  签名: [R.满] [R.忠实]
  定义体: by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

Depends on / 依赖: IsIso.eq_comp_inv, eq_comp_inv, h.right_triangle, infer_instance, right_triangle
-/
instance whiskerLeft_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerLeft R h.unit) := by
  have := h.right_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

/--
Instance `whiskerRight_unit_iso_of_R_fully_faithful` / 实例 `whiskerRight_unit_iso_of_R_fully_faithful`

English:
instance whiskerRight_unit_iso_of_R_fully_faithful
  signature: [R.Full] [R.Faithful]
  body: by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

中文:
实例 whiskerRight_unit_iso_of_R_fully_faithful
  签名: [R.满] [R.忠实]
  定义体: by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

Depends on / 依赖: IsIso.eq_comp_inv, eq_comp_inv, h.left_triangle, infer_instance, left_triangle
-/
instance whiskerRight_unit_iso_of_R_fully_faithful [R.Full] [R.Faithful] :
    IsIso (whiskerRight h.unit L) := by
  have := h.left_triangle
  rw [← IsIso.eq_comp_inv] at this
  rw [this]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.Faithful]
  signature: [L.Full] {Y : C}
  body: isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)

中文:
实例 [L.忠实]
  签名: [L.满] {Y : C}
  定义体: isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)

Depends on / 依赖: h.left_triangle_components, isIso_of_hom_comp_eq_id, left_triangle_components
-/
instance [L.Faithful] [L.Full] {Y : C} : IsIso (h.counit.app (L.obj Y)) :=
  isIso_of_hom_comp_eq_id _ (h.left_triangle_components Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.Faithful]
  signature: [L.Full] {Y : D}
  body: isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)

中文:
实例 [L.忠实]
  签名: [L.满] {Y : D}
  定义体: isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)

Depends on / 依赖: h.right_triangle_components, isIso_of_hom_comp_eq_id, right_triangle_components
-/
instance [L.Faithful] [L.Full] {Y : D} : IsIso (R.map (h.counit.app Y)) :=
  isIso_of_hom_comp_eq_id _ (h.right_triangle_components Y)

/--
lemma `isIso_counit_app_iff_mem_essImage` / 引理 `isIso_counit_app_iff_mem_essImage`

English:
lemma isIso_counit_app_iff_mem_essImage
  given: [L.Faithful] [L.Full] {X : D}
  proof: by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

中文:
引理 isIso_counit_app_iff_mem_essImage
  条件: [L.忠实] [L.满] {X : D}
  证明: by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

Depends on / 依赖: NatTrans, NatTrans.isIso_app_iff_of_iso, R.obj, counit, h.counit.app, i.symm, infer_instance, isIso_app_iff_of_iso
-/
lemma isIso_counit_app_iff_mem_essImage [L.Faithful] [L.Full] {X : D} :
    IsIso (h.counit.app X) ↔ L.essImage X := by
  constructor
  · intro
    exact ⟨R.obj X, ⟨asIso (h.counit.app X)⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

/--
lemma `mem_essImage_of_counit_isIso` / 引理 `mem_essImage_of_counit_isIso`

English:
lemma mem_essImage_of_counit_isIso
  statement: (A : D)
  proof: ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩

中文:
引理 mem_essImage_of_counit_isIso
  结论: (A : D)
  证明: ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩

Depends on / 依赖: R.obj, counit, h.counit.app
-/
lemma mem_essImage_of_counit_isIso (A : D)
    [IsIso (h.counit.app A)] : L.essImage A :=
  ⟨R.obj A, ⟨asIso (h.counit.app A)⟩⟩

/--
lemma `isIso_counit_app_of_iso` / 引理 `isIso_counit_app_of_iso`

English:
lemma isIso_counit_app_of_iso
  given: [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y)
  proof: (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩

中文:
引理 isIso_counit_app_of_iso
  条件: [L.忠实] [L.满] {X : D} {Y : C} (e : X ≅ L.obj Y)
  证明: (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩

Depends on / 依赖: MonoidalCategory, MonoidalCategory.tensorHom_comp_tensorHom_assoc, comp_id, e.symm, id_comp, isIso_counit_app_iff_mem_essImage, tensorHom_comp_tensorHom_assoc, tensorHom_id
-/
lemma isIso_counit_app_of_iso [L.Faithful] [L.Full] {X : D} {Y : C} (e : X ≅ L.obj Y) :
    IsIso (h.counit.app X) :=
  (isIso_counit_app_iff_mem_essImage h).mpr ⟨Y, ⟨e.symm⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.Faithful]
  signature: [R.Full] {Y : D}
  body: isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)

中文:
实例 [R.忠实]
  签名: [R.满] {Y : D}
  定义体: isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)

Depends on / 依赖: h.right_triangle_components, isIso_of_comp_hom_eq_id, right_triangle_components
-/
instance [R.Faithful] [R.Full] {Y : D} : IsIso (h.unit.app (R.obj Y)) :=
  isIso_of_comp_hom_eq_id _ (h.right_triangle_components Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.Faithful]
  signature: [R.Full] {X : C}
  body: isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)

中文:
实例 [R.忠实]
  签名: [R.满] {X : C}
  定义体: isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)

Depends on / 依赖: h.left_triangle_components, isIso_of_comp_hom_eq_id, left_triangle_components
-/
instance [R.Faithful] [R.Full] {X : C} : IsIso (L.map (h.unit.app X)) :=
  isIso_of_comp_hom_eq_id _ (h.left_triangle_components X)

/--
lemma `isIso_unit_app_iff_mem_essImage` / 引理 `isIso_unit_app_iff_mem_essImage`

English:
lemma isIso_unit_app_iff_mem_essImage
  given: [R.Faithful] [R.Full] {Y : C}
  proof: by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

中文:
引理 isIso_unit_app_iff_mem_essImage
  条件: [R.忠实] [R.满] {Y : C}
  证明: by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

Depends on / 依赖: L.obj, MonoidalCategory, MonoidalCategory.curriedAssociatorNatIso, NatTrans, NatTrans.isIso_app_iff_of_iso, curriedAssociatorNatIso, h.unit.app, i.symm, infer_instance, isIso_app_iff_of_iso
-/
lemma isIso_unit_app_iff_mem_essImage [R.Faithful] [R.Full] {Y : C} :
    IsIso (h.unit.app Y) ↔ R.essImage Y := by
  constructor
  · intro
    exact ⟨L.obj Y, ⟨(asIso (h.unit.app Y)).symm⟩⟩
  · rintro ⟨_, ⟨i⟩⟩
    rw [NatTrans.isIso_app_iff_of_iso _ i.symm]
    infer_instance

/--
theorem `mem_essImage_of_unit_isIso` / 定理 `mem_essImage_of_unit_isIso`

English:
theorem mem_essImage_of_unit_isIso
  statement: (A : C)
  proof: ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩

中文:
定理 mem_essImage_of_unit_isIso
  结论: (A : C)
  证明: ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩

Depends on / 依赖: L.obj, h.unit.app
-/
theorem mem_essImage_of_unit_isIso (A : C)
    [IsIso (h.unit.app A)] : R.essImage A :=
  ⟨L.obj A, ⟨(asIso (h.unit.app A)).symm⟩⟩

/--
lemma `isIso_unit_app_of_iso` / 引理 `isIso_unit_app_of_iso`

English:
lemma isIso_unit_app_of_iso
  given: [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X)
  proof: (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩

中文:
引理 isIso_unit_app_of_iso
  条件: [R.忠实] [R.满] {X : D} {Y : C} (e : Y ≅ R.obj X)
  证明: (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩

Depends on / 依赖: e.symm, isIso_unit_app_iff_mem_essImage
-/
lemma isIso_unit_app_of_iso [R.Faithful] [R.Full] {X : D} {Y : C} (e : Y ≅ R.obj X) :
    IsIso (h.unit.app Y) :=
  (isIso_unit_app_iff_mem_essImage h).mpr ⟨X, ⟨e.symm⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.IsEquivalence]
  signature: : IsIso h.unit
  body: by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app

中文:
实例 [R.是等价]
  签名: : 是同构 h.unit
  定义体: by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, R.objObjPreimageIso, isIso_of_isIso_app, isIso_unit_app_of_iso, objObjPreimageIso
-/
instance [R.IsEquivalence] : IsIso h.unit := by
  have := fun Y => isIso_unit_app_of_iso h (R.objObjPreimageIso Y).symm
  apply NatIso.isIso_of_isIso_app

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsEquivalence]
  signature: : IsIso h.counit
  body: by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app

中文:
实例 [L.是等价]
  签名: : 是同构 h.counit
  定义体: by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: L.objObjPreimageIso, NatIso, NatIso.isIso_of_isIso_app, isIso_counit_app_of_iso, isIso_of_isIso_app, objObjPreimageIso
-/
instance [L.IsEquivalence] : IsIso h.counit := by
  have := fun X => isIso_counit_app_of_iso h (L.objObjPreimageIso X).symm
  apply NatIso.isIso_of_isIso_app

/--
lemma `isEquivalence_left_of_isEquivalence_right` / 引理 `isEquivalence_left_of_isEquivalence_right`

English:
lemma isEquivalence_left_of_isEquivalence_right
  given: (h : L ⊣ R) [R.IsEquivalence]
  statement: L.IsEquivalence
  proof: h.toEquivalence.isEquivalence_functor

中文:
引理 isEquivalence_left_of_isEquivalence_right
  条件: (h : L ⊣ R) [R.是等价]
  结论: L.是等价
  证明: h.toEquivalence.isEquivalence_functor

Depends on / 依赖: h.toEquivalence.isEquivalence_functor, isEquivalence_functor, toEquivalence
-/
lemma isEquivalence_left_of_isEquivalence_right (h : L ⊣ R) [R.IsEquivalence] : L.IsEquivalence :=
  h.toEquivalence.isEquivalence_functor

/--
lemma `isEquivalence_right_of_isEquivalence_left` / 引理 `isEquivalence_right_of_isEquivalence_left`

English:
lemma isEquivalence_right_of_isEquivalence_left
  given: (h : L ⊣ R) [L.IsEquivalence]
  statement: R.IsEquivalence
  proof: h.toEquivalence.isEquivalence_inverse

中文:
引理 isEquivalence_right_of_isEquivalence_left
  条件: (h : L ⊣ R) [L.是等价]
  结论: R.是等价
  证明: h.toEquivalence.isEquivalence_inverse

Depends on / 依赖: h.toEquivalence.isEquivalence_inverse, isEquivalence_inverse, toEquivalence
-/
lemma isEquivalence_right_of_isEquivalence_left (h : L ⊣ R) [L.IsEquivalence] : R.IsEquivalence :=
  h.toEquivalence.isEquivalence_inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [L.IsEquivalence]
  signature: : IsIso h.unit
  body: by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance

中文:
实例 [L.是等价]
  签名: : 是同构 h.unit
  定义体: by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance

Depends on / 依赖: h.isEquivalence_right_of_isEquivalence_left, infer_instance, isEquivalence_right_of_isEquivalence_left
-/
instance [L.IsEquivalence] : IsIso h.unit := by
  have := h.isEquivalence_right_of_isEquivalence_left
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [R.IsEquivalence]
  signature: : IsIso h.counit
  body: by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance

中文:
实例 [R.是等价]
  签名: : 是同构 h.counit
  定义体: by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance

Depends on / 依赖: h.isEquivalence_left_of_isEquivalence_right, infer_instance, isEquivalence_left_of_isEquivalence_right
-/
instance [R.IsEquivalence] : IsIso h.counit := by
  have := h.isEquivalence_left_of_isEquivalence_right
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
theorem `isIso_map_unit_of_isLeftAdjoint_comp` / 定理 `isIso_map_unit_of_isLeftAdjoint_comp`

English:
theorem isIso_map_unit_of_isLeftAdjoint_comp
  statement: {E : Type*} [Category* E]
  proof: by
  let FF := FullyFaithful.ofFullyFaithful R
  apply isIso_of_coyoneda_map_bijective
  intro Y
  convert!
    ((adj2.homEquiv (R.obj (L.obj X)) Y).trans <|
FF.homEquiv.symm.trans
          (h.homEquiv X (S.obj Y)).trans (adj2.homEquiv X Y).symm).bijective using 1
  ext x
  have := adj2.counit_natu

中文:
定理 isIso_map_unit_of_isLeftAdjoint_comp
  结论: {E : 类型} [范畴* E]
  证明: by
  let FF := FullyFaithful.ofFullyFaithful R
  apply isIso_of_coyoneda_map_bijective
  intro Y
  convert!
    ((adj2.homEquiv (R.obj (L.obj X)) Y).trans <|
FF.homEquiv.symm.trans
          (h.homEquiv X (S.obj Y)).trans (adj2.homEquiv X Y).symm).bijective using 1
  ext x
  have := adj2.counit_natu

Depends on / 依赖: Adjunction, Adjunction.homEquiv, FF.homEquiv.symm.trans, FullyFaithful, FullyFaithful.ofFullyFaithful, L.obj, R.obj, S.obj, adj2.counit_naturality, adj2.homEquiv, bijective, convert, counit_naturality, h.homEquiv, homEquiv, isIso_of_coyoneda_map_bijective, ofFullyFaithful
-/
theorem isIso_map_unit_of_isLeftAdjoint_comp {E : Type*} [Category* E]
    {T : C ⥤ E} {S : E ⥤ D} {X : C} (adj2 : T ⊣ S ⋙ R) [R.Faithful] [R.Full] :
    IsIso (T.map (h.unit.app X)) := by
  let FF := FullyFaithful.ofFullyFaithful R
  apply isIso_of_coyoneda_map_bijective
  intro Y
  convert!
    ((adj2.homEquiv (R.obj (L.obj X)) Y).trans <|
FF.homEquiv.symm.trans
          (h.homEquiv X (S.obj Y)).trans (adj2.homEquiv X Y).symm).bijective using 1
  ext x
  have := adj2.counit_naturality x
  simp_all [Adjunction.homEquiv]

end CategoryTheory.Adjunction
