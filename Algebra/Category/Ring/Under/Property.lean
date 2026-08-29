/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Properties of `P.Under ⊤ R` for `R : CommRingCat`

In this file we translate ring theoretic properties of a property of ring homomorphisms
`P` in properties of the category `P.Under ⊤ R`.

## Main results

- `CommRingCat.Under.hasFiniteLimits`: If `P` is stable under finite products and equalizers,
  `P.Under ⊤ R` has finite limits.
- `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout`: If `P` has stable equalizers,
  base change along arbitrary morphisms preserve finite limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

variable {Q : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop}

open MorphismProperty

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape` / 引理 `RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape`

English:
lemma RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape
  statement: (hQi : RespectsIso Q)
  proof: by
  refine .of_isClosedUnderLimitsOfShape fun (J : Type u) _ => ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i => eqToIso <| by simp) ≪≫
limit.isoLimitCo

中文:
引理 RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape
  结论: (hQi : RespectsIso Q)
  证明: by
  refine .of_isClosedUnderLimitsOfShape fun (J : Type u) _ => ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i => eqToIso <| by simp) ≪≫
limit.isoLimitCo

Depends on / 依赖: CommRingCat, CommRingCat.Under.piFan, CommRingCat.Under.piFanIsLimit, CommRingCat.mkUnder, Discrete, Discrete.natIso, HasLimit, HasLimit.isoOfNatIso, IsClosedUnderFiniteProducts, RespectsIso, eqToIso, isLimit, isoLimitCone, isoOfNatIso, limit.isoLimitCone, mkUnder, natIso, of_isClosedUnderLimitsOfShape, piFanIsLimit, pres.diag.obj
-/
lemma RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderFiniteProducts := by
  refine .of_isClosedUnderLimitsOfShape fun (J : Type u) _ => ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i => eqToIso <| by simp) ≪≫
limit.isoLimitCone ⟨CommRingCat.Under.piFan fun i => (pres.diag.obj ⟨i⟩),
CommRingCat.Under.piFanIsLimit fun i => (pres.diag.obj ⟨i⟩)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff]; rw [← Under.w e.inv]; rw [(toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQp _ fun i => hpres _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `RingHom.HasEqualizers.isClosedUnderLimitsOfShape` / 引理 `RingHom.HasEqualizers.isClosedUnderLimitsOfShape`

English:
lemma RingHom.HasEqualizers.isClosedUnderLimitsOfShape
  statement: (hQi : RespectsIso Q)
  proof: by
  refine ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (pres.diag.map .left))
          (CommRingCat.toAlgHom (pres.diag.map .right))) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.is

中文:
引理 RingHom.HasEqualizers.isClosedUnderLimitsOfShape
  结论: (hQi : RespectsIso Q)
  证明: by
  refine ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (pres.diag.map .left))
          (CommRingCat.toAlgHom (pres.diag.map .right))) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.is

Depends on / 依赖: AlgHom, AlgHom.equalizer, CommRingCat, CommRingCat.Under.equalizerFork, CommRingCat.Under.equalizerForkIsLimit, CommRingCat.mkUnder, CommRingCat.toAlgHom, HasLimit, HasLimit.isoOfNatIso, IsClosedUnderLimitsOfShape, WalkingParallelPair, diagramIsoParallelPair, equalizer, equalizerFork, equalizerForkIsLimit, isLimit, isoLimitCone, isoOfNatIso, limit.isoLimitCone, mkUnder
-/
lemma RingHom.HasEqualizers.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderLimitsOfShape WalkingParallelPair := by
  refine ⟨fun A ⟨pres, hpres⟩ => ?_⟩
  let e : A ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (pres.diag.map .left))
          (CommRingCat.toAlgHom (pres.diag.map .right))) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (diagramIsoParallelPair _) ≪≫ limit.isoLimitCone
        ⟨CommRingCat.Under.equalizerFork (pres.diag.map .left) (pres.diag.map .right),
          CommRingCat.Under.equalizerForkIsLimit
            (pres.diag.map .left) (pres.diag.map .right)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff]; rw [← Under.w e.inv]; rw [(toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQe _ _ (hpres .zero) (hpres .one)

/-- If `Q` is stable under finite products, the inclusion from the subcategory of `Under R` defined
by `Q` creates finite products. -/
@[instance_reducible]
/--
Definition of `RingHom.HasFiniteProducts.createsFiniteProductsForget` / `RingHom.HasFiniteProducts.createsFiniteProductsForget` 的定义

English:
definition RingHom.HasFiniteProducts.createsFiniteProductsForget
  body: by
  refine .mk' _ fun (J : Type u) _ => ?_
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  have := hQp.isClosedUnderLimitsOfShape hQi R
exact inferInstanceAs (toMorphismProperty Q).underObj.IsClosedUnderLimitsOfShape _

中文:
定义 RingHom.HasFiniteProducts.createsFiniteProductsForget
  定义体: by
  refine .mk' _ fun (J : Type u) _ => ?_
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  have := hQp.isClosedUnderLimitsOfShape hQi R
exact inferInstanceAs (toMorphismProperty Q).underObj.IsClosedUnderLimitsOfShape _

Depends on / 依赖: Comma.forgetCreatesLimitsOfShapeOfClosed, IsClosedUnderLimitsOfShape, allowSynthFailures, forgetCreatesLimitsOfShapeOfClosed, hQp.isClosedUnderLimitsOfShape, isClosedUnderLimitsOfShape, toMorphismProperty, underObj, underObj.IsClosedUnderLimitsOfShape
-/
noncomputable def RingHom.HasFiniteProducts.createsFiniteProductsForget
    (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  refine .mk' _ fun (J : Type u) _ => ?_
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  have := hQp.isClosedUnderLimitsOfShape hQi R
exact inferInstanceAs (toMorphismProperty Q).underObj.IsClosedUnderLimitsOfShape _

/--
lemma `RingHom.HasFiniteProducts.hasFiniteProducts` / 引理 `RingHom.HasFiniteProducts.hasFiniteProducts`

English:
lemma RingHom.HasFiniteProducts.hasFiniteProducts
  statement: (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q)
  proof: by
  refine ⟨fun n => ⟨fun D => ?_⟩⟩
  have := hQp.createsFiniteProductsForget hQi R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

中文:
引理 RingHom.HasFiniteProducts.hasFiniteProducts
  结论: (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q)
  证明: by
  refine ⟨fun n => ⟨fun D => ?_⟩⟩
  have := hQp.createsFiniteProductsForget hQi R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

Depends on / 依赖: CategoryTheory, CategoryTheory.hasLimit_of_created, Under.forget, createsFiniteProductsForget, forget, hQp.createsFiniteProductsForget, hasLimit_of_created
-/
lemma RingHom.HasFiniteProducts.hasFiniteProducts (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q)
    (R : CommRingCat.{u}) :
    Limits.HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n => ⟨fun D => ?_⟩⟩
  have := hQp.createsFiniteProductsForget hQi R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

/--
lemma `RingHom.HasFiniteProducts.preservesFiniteProducts_pushout` / 引理 `RingHom.HasFiniteProducts.preservesFiniteProducts_pushout`

English:
lemma RingHom.HasFiniteProducts.preservesFiniteProducts_pushout
  statement: (hQi : RingHom.RespectsIso Q)
  proof: by
  have := hQp.createsFiniteProductsForget hQi R
  refine ⟨fun n => ⟨fun {K} => ?_⟩⟩
  have : PreservesLimit K (Under.pushout (toMorphismProperty Q) ⊤ f ⋙
        Under.forget (toMorphismProperty Q) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instanc

中文:
引理 RingHom.HasFiniteProducts.preservesFiniteProducts_pushout
  结论: (hQi : RingHom.RespectsIso Q)
  证明: by
  have := hQp.createsFiniteProductsForget hQi R
  refine ⟨fun n => ⟨fun {K} => ?_⟩⟩
  have : PreservesLimit K (Under.pushout (toMorphismProperty Q) ⊤ f ⋙
        Under.forget (toMorphismProperty Q) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instanc

Depends on / 依赖: MorphismProperty, MorphismProperty.Under.forget, PreservesLimit, Under.forget, Under.pushout, Under.pushoutCompForgetIso, createsFiniteProductsForget, forget, hQp.createsFiniteProductsForget, infer_instance, preservesLimit_iff_of_natIso, preservesLimit_of_reflects_of_preserves, pushout, pushoutCompForgetIso, toMorphismProperty
-/
lemma RingHom.HasFiniteProducts.preservesFiniteProducts_pushout (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) [(toMorphismProperty Q).IsStableUnderCobaseChange]
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteProducts (Under.pushout (toMorphismProperty Q) ⊤ f) := by
  have := hQp.createsFiniteProductsForget hQi R
  refine ⟨fun n => ⟨fun {K} => ?_⟩⟩
  have : PreservesLimit K (Under.pushout (toMorphismProperty Q) ⊤ f ⋙
        Under.forget (toMorphismProperty Q) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (MorphismProperty.Under.forget _ ⊤ S)

/-- If `Q` is stable under equalizers, the inclusion from the subcategory of `Under R` defined
by `Q` creates equalizers. -/
@[instance_reducible]
/--
Definition of `RingHom.HasEqualizers.createsLimitsWalkingParallelPair` / `RingHom.HasEqualizers.createsLimitsWalkingParallelPair` 的定义

English:
definition RingHom.HasEqualizers.createsLimitsWalkingParallelPair
  signature: (hQi : RespectsIso Q)
  body: by
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  exact hQe.isClosedUnderLimitsOfShape hQi _

中文:
定义 RingHom.HasEqualizers.createsLimitsWalkingParallelPair
  签名: (hQi : RespectsIso Q)
  定义体: by
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  exact hQe.isClosedUnderLimitsOfShape hQi _

Depends on / 依赖: Comma.forgetCreatesLimitsOfShapeOfClosed, allowSynthFailures, forgetCreatesLimitsOfShapeOfClosed, hQe.isClosedUnderLimitsOfShape, isClosedUnderLimitsOfShape
-/
noncomputable def RingHom.HasEqualizers.createsLimitsWalkingParallelPair (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  exact hQe.isClosedUnderLimitsOfShape hQi _

/--
lemma `RingHom.HasEqualizers.hasEqualizers` / 引理 `RingHom.HasEqualizers.hasEqualizers`

English:
lemma RingHom.HasEqualizers.hasEqualizers
  statement: (hQi : RespectsIso Q) (hQe : HasEqualizers Q)
  proof: by
  refine ⟨fun D => ?_⟩
  have := hQe.createsLimitsWalkingParallelPair hQi R
  exact hasLimit_of_created D (Under.forget _ _ R)

中文:
引理 RingHom.HasEqualizers.hasEqualizers
  结论: (hQi : RespectsIso Q) (hQe : HasEqualizers Q)
  证明: by
  refine ⟨fun D => ?_⟩
  have := hQe.createsLimitsWalkingParallelPair hQi R
  exact hasLimit_of_created D (Under.forget _ _ R)

Depends on / 依赖: Under.forget, createsLimitsWalkingParallelPair, forget, hQe.createsLimitsWalkingParallelPair, hasLimit_of_created
-/
lemma RingHom.HasEqualizers.hasEqualizers (hQi : RespectsIso Q) (hQe : HasEqualizers Q)
    (R : CommRingCat.{u}) :
    Limits.HasEqualizers ((toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun D => ?_⟩
  have := hQe.createsLimitsWalkingParallelPair hQi R
  exact hasLimit_of_created D (Under.forget _ _ R)

namespace CommRingCat

/-- If `Q` is stable under finite products and equalizers, the inclusion from the subcategory of
`Under R` defined by `Q` creates finite limits. -/
@[instance_reducible]
/--
Definition of `Under.createsFiniteLimitsForget` / `Under.createsFiniteLimitsForget` 的定义

English:
definition Under.createsFiniteLimitsForget
  signature: (hQi : RingHom.RespectsIso Q)
  body: letI := hQp.createsFiniteProductsForget hQi
  letI := hQe.createsLimitsWalkingParallelPair hQi
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts _

中文:
定义 Under.createsFiniteLimitsForget
  签名: (hQi : RingHom.RespectsIso Q)
  定义体: letI := hQp.createsFiniteProductsForget hQi
  letI := hQe.createsLimitsWalkingParallelPair hQi
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts _

Depends on / 依赖: createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts, createsFiniteProductsForget, createsLimitsWalkingParallelPair, hQe.createsLimitsWalkingParallelPair, hQp.createsFiniteProductsForget
-/
noncomputable def Under.createsFiniteLimitsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
  letI := hQp.createsFiniteProductsForget hQi
  letI := hQe.createsLimitsWalkingParallelPair hQi
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts _

/--
lemma `Under.hasFiniteLimits` / 引理 `Under.hasFiniteLimits`

English:
lemma Under.hasFiniteLimits
  statement: (hQi : RingHom.RespectsIso Q)
  proof: have := hQp.hasFiniteProducts hQi
  have := hQe.hasEqualizers hQi
  hasFiniteLimits_of_hasEqualizers_and_finite_products

中文:
引理 Under.hasFiniteLimits
  结论: (hQi : RingHom.RespectsIso Q)
  证明: have := hQp.hasFiniteProducts hQi
  have := hQe.hasEqualizers hQi
  hasFiniteLimits_of_hasEqualizers_and_finite_products

Depends on / 依赖: hQe.hasEqualizers, hQp.hasFiniteProducts, hasEqualizers, hasFiniteLimits_of_hasEqualizers_and_finite_products, hasFiniteProducts
-/
lemma Under.hasFiniteLimits (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty Q).Under ⊤ R) :=
  have := hQp.hasFiniteProducts hQi
  have := hQe.hasEqualizers hQi
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end CommRingCat

variable (P : forall {R S : Type u} [CommRing R] [CommRing S], (R ->+* S) -> Prop)

open RingHom

variable {P}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective` / 引理 `CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective`

English:
lemma CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
  proof: by
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let ι : R.mkUnder (AlgHom.equalizer (toAlgHom f) (toAlgHom g)) ⟶ A :=
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder
  let h' := (R.tensorProd S).map ι
  have w' : h' ≫ (tensorProd

中文:
引理 CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
  证明: by
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let ι : R.mkUnder (AlgHom.equalizer (toAlgHom f) (toAlgHom g)) ⟶ A :=
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder
  let h' := (R.tensorProd S).map ι
  have w' : h' ≫ (tensorProd

Depends on / 依赖: AlgHom, AlgHom.equalizer, CommRingCat, CommRingCat.Under.equalizer_comp, Fork.of, IsLimit, R.mkUnder, R.tensorProd, Under.equalizerFork, Under.equalizerForkIsLimit, equalizer, equalizerFork, equalizerForkIsLimit, equalizer_comp, isLimitMap, mapCone, mkUnder, tensorProd, toAlgHom, toUnder
-/
lemma CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
    {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g : A ⟶ B} :
    PreservesLimit (parallelPair f g) (tensorProd R S) ↔
      Function.Bijective ((toAlgHom f).tensorEqualizer R S (toAlgHom g)) := by
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let ι : R.mkUnder (AlgHom.equalizer (toAlgHom f) (toAlgHom g)) ⟶ A :=
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder
  let h' := (R.tensorProd S).map ι
  have w' : h' ≫ (tensorProd R S).map f = h' ≫ (tensorProd R S).map g := by
    simpa using! congr((R.tensorProd S).map $(CommRingCat.Under.equalizer_comp f g))
  let e : IsLimit ((R.tensorProd S).mapCone c) ≃ IsLimit (Fork.ofι h' w') :=
    isLimitMapConeForkEquiv (tensorProd R S) (Under.equalizer_comp f g)
  rw [preservesLimit_iff_isLimit_mapCone hc]; rw [e.nonempty_congr]; rw [(Under.equalizerForkIsLimit _ _).nonempty_isLimit_iff_isIso_lift]
  have heq : (Under.equalizerForkIsLimit _ _).lift (Fork.ofι h' w') =
      (AlgHom.tensorEqualizer S S (toAlgHom f) (toAlgHom g)).toUnder ≫
        Under.homMk (CommRingCat.ofHom (.id _)) := by
    refine Fork.IsLimit.hom_ext (Under.equalizerForkIsLimit _ _) ?_
    rw [Fork.IsLimit.lift_ι]
    ext : 2
    dsimp
    ext x <;> rfl
  rw [heq]; rw [← isIso_iff_of_reflects_iso _ (CategoryTheory.Under.forget S)]; rw [ConcreteCategory.isIso_iff_bijective]
  rfl

/--
lemma `RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd` / 引理 `RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd`

English:
lemma RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
  proof: by
  rw [CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective]
  exact hPse _ _ hA hB

中文:
引理 RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
  证明: by
  rw [CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective]
  exact hPse _ _ hA hB

Depends on / 依赖: CommRingCat, CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective, preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
-/
lemma RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
    (hPse : HasStableEqualizers P) {R S : CommRingCat.{u}} [Algebra R S]
    {A B : Under R} (f g : A ⟶ B) (hA : P A.hom.hom) (hB : P B.hom.hom) :
    PreservesLimit (parallelPair f g) (CommRingCat.tensorProd R S) := by
  rw [CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective]
  exact hPse _ _ hA hB

/--
lemma `RingHom.HasStableEqualizers.preservesEqualizers_pushout` / 引理 `RingHom.HasStableEqualizers.preservesEqualizers_pushout`

English:
lemma RingHom.HasStableEqualizers.preservesEqualizers_pushout
  statement: (hPi : RespectsIso P)
  proof: by
  refine ⟨fun {K} => ?_⟩
  have := hPe.createsLimitsWalkingParallelPair hPi R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    rw [← CommRingCat.ofHom_hom f]; rw [← preservesLimit_iff_of_natIso _ (CommRingC

中文:
引理 RingHom.HasStableEqualizers.preservesEqualizers_pushout
  结论: (hPi : RespectsIso P)
  证明: by
  refine ⟨fun {K} => ?_⟩
  have := hPe.createsLimitsWalkingParallelPair hPi R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    rw [← CommRingCat.ofHom_hom f]; rw [← preservesLimit_iff_of_natIso _ (CommRingC

Depends on / 依赖: CategoryTheory, CategoryTheory.Under.pushout, CommRingCat, CommRingCat.ofHom_hom, CommRingCat.tensorProdIsoPushout, K.obj, PreservesLimit, Under.forget, algebraize, createsLimitsWalkingParallelPair, diagramIsoParallelPair, f.hom, forget, hPe.createsLimitsWalkingParallelPair, hPse.preservesLimit_parallelPair_tensorProd, ofHom_hom, preservesLimit_iff_of_iso_diagram, preservesLimit_iff_of_natIso, preservesLimit_parallelPair_tensorProd, pushout
-/
lemma RingHom.HasStableEqualizers.preservesEqualizers_pushout (hPi : RespectsIso P)
    (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (Under.pushout (toMorphismProperty P) ⊤ f) := by
  refine ⟨fun {K} => ?_⟩
  have := hPe.createsLimitsWalkingParallelPair hPi R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    rw [← CommRingCat.ofHom_hom f]; rw [← preservesLimit_iff_of_natIso _ (CommRingCat.tensorProdIsoPushout R S)]; rw [← preservesLimit_iff_of_iso_diagram _ (diagramIsoParallelPair _).symm]
    exact hPse.preservesLimit_parallelPair_tensorProd _ _ ((K.obj _).prop) ((K.obj _).prop)
  have : PreservesLimit K (Under.pushout (toMorphismProperty P) ⊤ f ⋙
        Under.forget (toMorphismProperty P) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (Under.forget _ ⊤ S)

/--
lemma `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout` / 引理 `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout`

English:
lemma RingHom.HasStableEqualizers.preservesFiniteLimits_pushout
  statement: (hPi : RingHom.RespectsIso P)
  proof: have := hPp.preservesFiniteProducts_pushout hPi f
  have := hPse.preservesEqualizers_pushout hPi hPe f
  have := CommRingCat.Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

中文:
引理 RingHom.HasStableEqualizers.preservesFiniteLimits_pushout
  结论: (hPi : RingHom.RespectsIso P)
  证明: have := hPp.preservesFiniteProducts_pushout hPi f
  have := hPse.preservesEqualizers_pushout hPi hPe f
  have := CommRingCat.Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

Depends on / 依赖: CommRingCat, CommRingCat.Under.hasFiniteLimits, hPp.preservesFiniteProducts_pushout, hPse.preservesEqualizers_pushout, hasFiniteLimits, preservesEqualizers_pushout, preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts, preservesFiniteProducts_pushout
-/
lemma RingHom.HasStableEqualizers.preservesFiniteLimits_pushout (hPi : RingHom.RespectsIso P)
    (hPp : HasFiniteProducts P) (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (Under.pushout (toMorphismProperty P) ⊤ f) :=
  have := hPp.preservesFiniteProducts_pushout hPi f
  have := hPse.preservesEqualizers_pushout hPi hPe f
  have := CommRingCat.Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
