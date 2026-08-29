/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

A particular example is the transfer of `Abelian` instances from a category `C` to `ShrinkHoms C`;
see `ShrinkHoms.abelian`. In this case, we also transfer the `Preadditive` structure.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D)
variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasKernels` / 定理 `hasKernels`

English:
theorem hasKernels
  given: [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
  statement: HasKernels C
  proof: { has_limit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

中文:
定理 hasKernels
  条件: [保持FiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
  结论: 有Kernels C
  证明: { has_limit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

Depends on / 依赖: F.map, F.obj, G.map, HasKernel, Limits, Limits.hasKernel_comp_mono, Limits.hasKernel_iso_comp, MulAction, NatIso, NatIso.naturality_1, hasKernel_comp_mono, hasKernel_iso_comp, has_limit, i.hom.app, i.inv.app, naturality_1
-/
theorem hasKernels [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C :=
  { has_limit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasCokernels` / 定理 `hasCokernels`

English:
theorem hasCokernels
  given: (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)
  statement: HasCokernels C
  proof: { has_colimit {X Y} f := by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCok

中文:
定理 hasCokernels
  条件: (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F)
  结论: 有余kernels C
  证明: { has_colimit {X Y} f := by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCok

Depends on / 依赖: F.map, G.map, HasCokernel, Limits, Limits.hasCokernel_comp_iso, Limits.hasCokernel_epi_comp, NatIso, NatIso.naturality_1, PreservesColimits, adj.leftAdjoint_preservesColimits, hasCokernel_comp_iso, hasCokernel_epi_comp, has_colimit, i.hom.app, i.inv.app, isPretransitive_of_isGalois, leftAdjoint_preservesColimits, naturality_1
-/
theorem hasCokernels (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C :=
  { has_colimit {X Y} f := by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (with `G` preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian. -/
@[stacks 03A3, instance_reducible]
/--
Definition of `abelianOfAdjunction` / `abelianOfAdjunction` 的定义

English:
definition abelianOfAdjunction
  signature: {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
  body: by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : forall {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    hav

中文:
定义 abelianOfAdjunction
  签名: {C : 类型u₁} [范畴.{v₁} C] [预加性 C] [有FiniteProducts C]
  定义体: by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : forall {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    hav

Depends on / 依赖: Abelian, Abelian.PreservesCoimageImageComparison.iso, Abelian.coimageImageComparison, Arrow.mk, F.map, Functor, Functor.mapArrowFunctor, G.map, PreservesCoimageImageComparison, PreservesColimits, adj.leftAdjoint_preservesColimits, arrowIso, coimageImageComparison, hasCokernels, hasKernels, leftAdjoint_preservesColimits, mapArrowFunctor, mapIso
-/
def abelianOfAdjunction {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : forall {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    have : PreservesColimits G := adj.leftAdjoint_preservesColimits
    let iso : Arrow.mk (G.map (Abelian.coimageImageComparison (F.map f))) ≅
        Arrow.mk (Abelian.coimageImageComparison f) :=
      Abelian.PreservesCoimageImageComparison.iso G (F.map f) ≪≫
        Abelian.coimageImageComparisonFunctor.mapIso arrowIso
    rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
@[instance_reducible]
/--
Definition of `abelianOfEquivalence` / `abelianOfEquivalence` 的定义

English:
definition abelianOfEquivalence
  signature: {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
  body: abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction

中文:
定义 abelianOfEquivalence
  签名: {C : 类型u₁} [范畴.{v₁} C] [预加性 C] [有FiniteProducts C]
  定义体: abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction

Depends on / 依赖: F.asEquivalence.symm.toAdjunction, F.asEquivalence.unitIso.symm, F.inv, abelianOfAdjunction, asEquivalence, toAdjunction, unitIso
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    [F.IsEquivalence] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction

namespace ShrinkHoms

universe w

variable {C : Type*} [Category* C] [LocallySmall.{w} C]

section Preadditive

variable [Preadditive C]

variable (C)

/--
Instance `preadditive` / 实例 `preadditive`

English:
instance preadditive
  signature: : Preadditive.{w} (ShrinkHoms C)
  body: .ofFullyFaithful (equivalence C).fullyFaithfulInverse

中文:
实例 preadditive
  签名: : 预加性.{w} (ShrinkHoms C)
  定义体: .ofFullyFaithful (equivalence C).fullyFaithfulInverse

Depends on / 依赖: equivalence, fullyFaithfulInverse, ofFullyFaithful
-/
instance preadditive : Preadditive.{w} (ShrinkHoms C) :=
  .ofFullyFaithful (equivalence C).fullyFaithfulInverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inverse C).Additive
  body: (equivalence C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

中文:
实例 :
  签名: (inverse C).加性
  定义体: (equivalence C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

Depends on / 依赖: additive_ofFullyFaithful, equivalence, fullyFaithfulFunctor, symm.fullyFaithfulFunctor.additive_ofFullyFaithful
-/
instance : (inverse C).Additive :=
  (equivalence C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor C).Additive
  body: (equivalence C).symm.additive_inverse_of_FullyFaithful

中文:
实例 :
  签名: (functor C).加性
  定义体: (equivalence C).symm.additive_inverse_of_FullyFaithful

Depends on / 依赖: additive_inverse_of_FullyFaithful, equivalence, symm.additive_inverse_of_FullyFaithful
-/
instance : (functor C).Additive :=
  (equivalence C).symm.additive_inverse_of_FullyFaithful

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: (J : Type*) [Category* J]
  body: Adjunction.hasLimitsOfShape_of_equivalence (inverse C)

中文:
实例 hasLimitsOfShape
  签名: (J : 类型) [范畴* J]
  定义体: Adjunction.hasLimitsOfShape_of_equivalence (inverse C)

Depends on / 依赖: Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, hasLimitsOfShape_of_equivalence, inverse
-/
instance hasLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, w} J (ShrinkHoms C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (inverse C)

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits C]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasFiniteLimits
  签名: [有有限极限 C]
  定义体: ⟨fun _ => inferInstance⟩

Depends on / 依赖: Action, Action.preservesColimitsOfShape_of_preserves, PreservesColimitsOfShape, SingleObj, preservesColimitsOfShape_of_preserves
-/
instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits.{w} (ShrinkHoms C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
/--
Instance `abelian` / 实例 `abelian`

English:
instance abelian
  signature: [Abelian C]
  body: abelianOfEquivalence (inverse C)

中文:
实例 abelian
  签名: [交换 C]
  定义体: abelianOfEquivalence (inverse C)

Depends on / 依赖: abelianOfEquivalence, inverse
-/
noncomputable instance abelian [Abelian C] :
    Abelian.{w} (ShrinkHoms C) := abelianOfEquivalence (inverse C)

end ShrinkHoms


namespace AsSmall

universe w v u

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

variable (C)

/--
Instance `preadditive` / 实例 `preadditive`

English:
instance preadditive
  signature: : Preadditive (AsSmall.{w} C)
  body: .ofFullyFaithful equiv.fullyFaithfulInverse

中文:
实例 preadditive
  签名: : 预加性 (AsSmall.{w} C)
  定义体: .ofFullyFaithful equiv.fullyFaithfulInverse

Depends on / 依赖: equiv.fullyFaithfulInverse, fullyFaithfulInverse, ofFullyFaithful
-/
instance preadditive : Preadditive (AsSmall.{w} C) :=
  .ofFullyFaithful equiv.fullyFaithfulInverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (down (C := C)).Additive
  body: equiv.symm.fullyFaithfulFunctor.additive_ofFullyFaithful

中文:
实例 :
  签名: (down (C := C)).加性
  定义体: equiv.symm.fullyFaithfulFunctor.additive_ofFullyFaithful

Depends on / 依赖: Additive
-/
instance : (down (C := C)).Additive :=
  equiv.symm.fullyFaithfulFunctor.additive_ofFullyFaithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (up (C := C)).Additive
  body: equiv.symm.additive_inverse_of_FullyFaithful

中文:
实例 :
  签名: (up (C := C)).加性
  定义体: equiv.symm.additive_inverse_of_FullyFaithful

Depends on / 依赖: Additive
-/
instance : (up (C := C)).Additive :=
  equiv.symm.additive_inverse_of_FullyFaithful

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: (J : Type*) [Category* J]
  body: Adjunction.hasLimitsOfShape_of_equivalence equiv.inverse

中文:
实例 hasLimitsOfShape
  签名: (J : 类型) [范畴* J]
  定义体: Adjunction.hasLimitsOfShape_of_equivalence equiv.inverse

Depends on / 依赖: Adjunction, Adjunction.hasLimitsOfShape_of_equivalence, equiv.inverse, hasLimitsOfShape_of_equivalence, inverse
-/
instance hasLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, max u v w} J (AsSmall.{w} C) :=
  Adjunction.hasLimitsOfShape_of_equivalence equiv.inverse

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits C]
  body: ⟨fun _ => inferInstance⟩

中文:
实例 hasFiniteLimits
  签名: [有有限极限 C]
  定义体: ⟨fun _ => inferInstance⟩
-/
instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits (AsSmall.{w} C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
/--
Instance `abelian` / 实例 `abelian`

English:
instance abelian
  signature: [Abelian C]
  body: abelianOfEquivalence equiv.inverse

中文:
实例 abelian
  签名: [交换 C]
  定义体: abelianOfEquivalence equiv.inverse

Depends on / 依赖: Finite, Finite.exists_type_univ_nonempty_mulEquiv, Limits, Limits.hasColimitsOfShape_of_equivalence, abelianOfEquivalence, e.toSingleObjEquiv.symm, equiv.inverse, exists_type_univ_nonempty_mulEquiv, hasColimitsOfShape_of_equivalence, inverse, toSingleObjEquiv
-/
noncomputable instance abelian [Abelian C] :
    Abelian (AsSmall.{w} C) := abelianOfEquivalence equiv.inverse

end AsSmall

end CategoryTheory
