/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Properties of morphisms satisfying fpqc descent

In this file we show some global properties satisfy fpqc descent.

- universally closed
  (`AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`)
- universally open
  (`AlgebraicGeometry.descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact`)
- universally injective
  (`AlgebraicGeometry.descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact`)
- being an isomorphism
  (`AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`)
- being an open immersion
  (`AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact`)
-/

public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact` / 实例 `Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact`

English:
instance Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact
  signature: :
  body: .of_le (Q := @Surjective) (le_of_inf_eq' (by grind))

中文:
实例 平坦.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact
  签名: :
  定义体: .of_le (Q := @Surjective) (le_of_inf_eq' (by grind))

Depends on / 依赖: Surjective, le_of_inf_eq, of_le
-/
instance Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Surjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  .of_le (Q := @Surjective) (le_of_inf_eq' (by grind))

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally closed satisfies fpqc descent. -/
@[stacks 02KS]
/--
Instance `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact` / 实例 `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`

English:
instance descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  signature: :
  body: by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

中文:
实例 descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  签名: :
  定义体: by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

Depends on / 依赖: IsLocalIso, IsLocalIso.le_of_isZariskiLocalAtSource, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact, Spec.map, descendsAlong_inf_quasiCompact, inf_comm, inf_le_inf, le_of_isZariskiLocalAtSource, le_rfl, pullback, pullback.fst, pullback.map, pullback.snd, universally_mk
-/
instance descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally open satisfies fpqc descent. -/
@[stacks 02KT]
/--
Instance `descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact` / 实例 `descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact`

English:
instance descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
  signature: :
  body: by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

中文:
实例 descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact
  签名: :
  定义体: by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

Depends on / 依赖: IsLocalIso, IsLocalIso.le_of_isZariskiLocalAtSource, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact, Spec.map, descendsAlong_inf_quasiCompact, inf_comm, inf_le_inf, le_of_isZariskiLocalAtSource, le_rfl, pullback, pullback.fst, pullback.map, pullback.snd, universally_mk
-/
instance descendsAlong_universallyOpen_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyOpen
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  refine fun {R} S Y φ g ⟨_, _⟩ hfst => ⟨universally_mk' _ _ fun {T} f _ s hs => ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← Scheme.image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- Universally injective satisfies fpqc descent. -/
@[stacks 02KW]
/--
Instance `descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact` / 实例 `descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact`

English:
instance descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact
  signature: :
  body: by
  rw [universallyInjective_eq_diagonal]
  infer_instance

中文:
实例 descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact
  签名: :
  定义体: by
  rw [universallyInjective_eq_diagonal]
  infer_instance

Depends on / 依赖: infer_instance, universallyInjective_eq_diagonal
-/
instance descendsAlong_universallyInjective_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyInjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [universallyInjective_eq_diagonal]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Being an isomorphism satisfies fpqc descent. -/
@[stacks 02L4]
/--
Instance `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact` / 实例 `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`

English:
instance descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
  signature: :
  body: by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h (hfst : IsIso _)
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : Surjective g :=
      of_pullback_fst_of_descendsAlong (P := @Surjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hopen' : UniversallyOpen g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyOpen) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : IsHomeomorph g.base := ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
    have : IsAffineHom g :=
      isAffineHom_of_isInducing g this.isInducing this.isClosedEmbedding.isClosed_range
    isAffine_of_isAffineHom g
  wlog hY : exists T, Y = Spec T generalizing Y
  · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    change isomorphisms Scheme _
    rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  refine of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f => Function.Bijective f) (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_bijective ?_ ?_ h hfst
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · simp_rw [← isIso_SpecMap_iff, implies_true]

中文:
实例 descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact
  签名: :
  定义体: by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h (hfst : IsIso _)
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : Surjective g :=
      of_pullback_fst_of_descendsAlong (P := @Surjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hopen' : UniversallyOpen g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyOpen) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : IsHomeomorph g.base := ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
    have : IsAffineHom g :=
      isAffineHom_of_isInducing g this.isInducing this.isClosedEmbedding.isClosed_range
    isAffine_of_isAffineHom g
  wlog hY : exists T, Y = Spec T generalizing Y
  · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    change isomorphisms Scheme _
    rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  refine of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f => Function.Bijective f) (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_bijective ?_ ?_ h hfst
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · simp_rw [← isIso_SpecMap_iff, implies_true]

Depends on / 依赖: IsAffine, IsLocalIso, IsLocalIso.le_of_isZariskiLocalAtSource, IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact, QuasiCompact, Spec.map, Surjecti, Surjective, UniversallyInjective, descendsAlong_inf_quasiCompact, inf_comm, inf_le_inf, le_of_isZariskiLocalAtSource, le_rfl, of_pullback_fst_of_descendsAlong
-/
instance descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact :
    (isomorphisms Scheme.{u}).DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h (hfst : IsIso _)
  have : IsAffine Y :=
    have : UniversallyInjective g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyInjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : Surjective g :=
      of_pullback_fst_of_descendsAlong (P := @Surjective) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have hopen' : UniversallyOpen g :=
      of_pullback_fst_of_descendsAlong (P := @UniversallyOpen) (f := Spec.map φ)
        (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩ inferInstance
    have : IsHomeomorph g.base := ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
    have : IsAffineHom g :=
      isAffineHom_of_isInducing g this.isInducing this.isClosedEmbedding.isClosed_range
    isAffine_of_isAffineHom g
  wlog hY : exists T, Y = Spec T generalizing Y
  · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
      pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    change isomorphisms Scheme _
    rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
  obtain ⟨T, rfl⟩ := hY
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  refine of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f => Function.Bijective f) (P' := @Surjective ⊓ @Flat)
      RingHom.FaithfullyFlat.codescendsAlong_bijective ?_ ?_ h hfst
  · intro _ _ f hf
    rwa [← flat_and_surjective_SpecMap_iff, and_comm]
  · simp_rw [← isIso_SpecMap_iff, implies_true]

set_option backward.isDefEq.respectTransparency.types false in
/-- Being an open immersion satisfies fpqc descent. -/
@[stacks 02L3]
/--
Instance `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'` / 实例 `descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`

English:
instance descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'
  signature: :
  body: by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hg
  have : UniversallyOpen g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f)
      hf inferInstance
  let U : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  let f' := pullback.snd f U.ι
  let g' : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simp [U])
  have : Surjective g' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, g', hy]⟩⟩
  have : IsIso (pullback.fst f' g') := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, inferInstance⟩
    have : IsOpenImmersion (pullback.fst f (g' ≫ U.ι)) := by
      rwa [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    have : IsOpenImmersion (pullback.fst f' g' ≫ pullback.fst f U.ι) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst]
      infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : IsIso g' := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f') ?_ this
    exact MorphismProperty.pullback_snd _ _ hf
  rw [← IsOpenImmersion.lift_fac U.ι g (by simp [U])]
  infer_instance

中文:
实例 descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'
  签名: :
  定义体: by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hg
  have : UniversallyOpen g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f)
      hf inferInstance
  let U : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  let f' := pullback.snd f U.ι
  let g' : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simp [U])
  have : Surjective g' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, g', hy]⟩⟩
  have : IsIso (pullback.fst f' g') := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, inferInstance⟩
    have : IsOpenImmersion (pullback.fst f (g' ≫ U.ι)) := by
      rwa [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    have : IsOpenImmersion (pullback.fst f' g' ≫ pullback.fst f U.ι) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst]
      infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : IsIso g' := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f') ?_ this
    exact MorphismProperty.pullback_snd _ _ hf
  rw [← IsOpenImmersion.lift_fac U.ι g (by simp [U])]
  infer_instance

Depends on / 依赖: DescendsAlong, DescendsAlong.mk, IsOpenImmersion, IsOpenImmersion.lift, MorphismProperty, MorphismProperty.of_pullback_fst_of_descendsAlong, QuasiCompact, Scheme, Scheme.Hom.comp_apply, Set.range, Surjective, UniversallyOpen, Z.Opens, comp_apply, g.base, g.isOpenMap.isOpen_range, injective, isOpenMap, isOpen_range, of_pullback_fst_of_descendsAlong
-/
instance descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact' :
    IsOpenImmersion.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hg
  have : UniversallyOpen g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f)
      hf inferInstance
  let U : Z.Opens := ⟨Set.range g.base, g.isOpenMap.isOpen_range⟩
  let f' := pullback.snd f U.ι
  let g' : Y ⟶ U := IsOpenImmersion.lift U.ι g (by simp [U])
  have : Surjective g' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by apply U.ι.injective; simp [← Scheme.Hom.comp_apply, g', hy]⟩⟩
  have : IsIso (pullback.fst f' g') := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨?_, inferInstance⟩
    have : IsOpenImmersion (pullback.fst f (g' ≫ U.ι)) := by
      rwa [AlgebraicGeometry.IsOpenImmersion.lift_fac]
    have : IsOpenImmersion (pullback.fst f' g' ≫ pullback.fst f U.ι) := by
      rw [← pullbackLeftPullbackSndIso_hom_fst]
      infer_instance
    exact .of_comp _ (pullback.fst _ _)
  have : IsIso g' := by
    apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := isomorphisms Scheme) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f') ?_ this
    exact MorphismProperty.pullback_snd _ _ hf
  rw [← IsOpenImmersion.lift_fac U.ι g (by simp [U])]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `HasRingHomProperty.descendsAlong_flat` / 引理 `HasRingHomProperty.descendsAlong_flat`

English:
lemma HasRingHomProperty.descendsAlong_flat
  statement: {P : MorphismProperty Scheme.{u}}
  proof: by
  refine HasRingHomProperty.descendsAlong _ _ _ _ ?_ ?_ h
  · rw [inf_comm]
    gcongr
    exact IsLocalIso.le_of_isZariskiLocalAtSource @Flat
  · intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂

中文:
引理 有RingHomProperty.descendsAlong_flat
  结论: {P : MorphismProperty 概形.{u}}
  证明: by
  refine HasRingHomProperty.descendsAlong _ _ _ _ ?_ ?_ h
  · rw [inf_comm]
    gcongr
    exact IsLocalIso.le_of_isZariskiLocalAtSource @Flat
  · intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂

Depends on / 依赖: FaithfullyFlat, HasRingHomProperty, HasRingHomProperty.Spec_iff, HasRingHomProperty.descendsAlong, IsLocalIso, IsLocalIso.le_of_isZariskiLocalAtSource, RingHom, RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, Spec.map, Spec_iff, descendsAlong, iff_flat_and_comap_surjective, inf_comm, le_of_isZariskiLocalAtSource, surjective
-/
lemma HasRingHomProperty.descendsAlong_flat {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}
    [HasRingHomProperty P Q] (h : RingHom.CodescendsAlong Q RingHom.FaithfullyFlat) :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine HasRingHomProperty.descendsAlong _ _ _ _ ?_ ?_ h
  · rw [inf_comm]
    gcongr
    exact IsLocalIso.le_of_isZariskiLocalAtSource @Flat
  · intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂

set_option backward.isDefEq.respectTransparency.types false in
/-- fpqc descent implies fppf descent -/
instance (P : MorphismProperty Scheme) [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x => have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [Flat f] [QuasiCompact f] :
    (Over.pullback f).Faithful :=
  MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
    (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y : Scheme} (f : X ⟶ Y) [Surjective f] [Flat f] [LocallyOfFinitePresentation f] :
    (Over.pullback f).Faithful :=
  MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong
    (P := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry
