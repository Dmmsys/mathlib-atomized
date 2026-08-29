/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Riccardo Brasca, Filippo A. E. Nuccio
-/
module

public import Mathlib.Condensed.Module
public import Mathlib.Condensed.Equivalence
/-!

# The explicit sheaf condition for condensed sets

We give the following three explicit descriptions of condensed objects:

* `Condensed.ofSheafStonean`: A finite-product-preserving presheaf on `Stonean`.

* `Condensed.ofSheafProfinite`: A finite-product-preserving presheaf on `Profinite`, satisfying
  `EqualizerCondition`.

* `Condensed.ofSheafCompHaus`: A finite-product-preserving presheaf on `CompHaus`, satisfying
  `EqualizerCondition`.

The property `EqualizerCondition` is defined in
`Mathlib/CategoryTheory/Sites/Coherent/RegularSheaves.lean` and it says that for any effective epi
`X ⟶ B` (in this case that is equivalent to being a continuous surjection), the presheaf `F`
exhibits `F(B)` as the equalizer of the two maps `F(X) ⇉ F(X ×_B X)`.

We also give variants for condensed objects in concrete categories whose forgetful functor
reflects finite limits (resp. products), where it is enough to check the sheaf condition after
postcomposing with the forgetful functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Functor Presheaf regularTopology

namespace Condensed

variable {A : Type*} [Category* A]

/--
Definition of `ofSheafStonean` / `ofSheafStonean` 的定义

English:
definition ofSheafStonean
  body: .functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_of_projective F]
      exact ⟨fun _ => inferInstance⟩ }

中文:
定义 ofSheafStonean
  定义体: .functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_of_projective F]
      exact ⟨fun _ => inferInstance⟩ }

Depends on / 依赖: StoneanCompHaus, StoneanCompHaus.equivalence, equivalence, functor, functor.obj, isSheaf_iff_preservesFiniteProducts_of_projective, property
-/
noncomputable def ofSheafStonean
    [forall X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F] :
    Condensed A :=
.functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_of_projective F]
      exact ⟨fun _ => inferInstance⟩ }

/--
Definition of `ofSheafForgetStonean` / `ofSheafForgetStonean` 的定义

English:
definition ofSheafForgetStonean
  body: .functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_projective_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_of_projective]
      exact ⟨fun _ => inferInstance⟩ }

中文:
定义 ofSheafForgetStonean
  定义体: .functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_projective_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_of_projective]
      exact ⟨fun _ => inferInstance⟩ }

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, StoneanCompHaus, StoneanCompHaus.equivalence, equivalence, forget, functor, functor.obj, isSheaf_coherent_of_projective_of_comp, isSheaf_iff_preservesFiniteProducts_of_projective, property
-/
noncomputable def ofSheafForgetStonean
    [forall X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
    {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteProducts (CategoryTheory.forget A)]
    (F : Stonean.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)] :
    Condensed A :=
.functor.obj { StoneanCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_projective_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_of_projective]
      exact ⟨fun _ => inferInstance⟩ }

/--
Definition of `ofSheafProfinite` / `ofSheafProfinite` 的定义

English:
definition ofSheafProfinite
  body: .functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

中文:
定义 ofSheafProfinite
  定义体: .functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

Depends on / 依赖: ProfiniteCompHaus, ProfiniteCompHaus.equivalence, equivalence, functor, functor.obj, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
noncomputable def ofSheafProfinite
    [forall X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A :=
.functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

/--
Definition of `ofSheafForgetProfinite` / `ofSheafForgetProfinite` 的定义

English:
definition ofSheafForgetProfinite
  body: .functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

中文:
定义 ofSheafForgetProfinite
  定义体: .functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, ProfiniteCompHaus, ProfiniteCompHaus.equivalence, equivalence, forget, functor, functor.obj, isSheaf_coherent_of_hasPullbacks_of_comp, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
noncomputable def ofSheafForgetProfinite
    [forall X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A]
    {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : Profinite.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) :
    Condensed A :=
.functor.obj { ProfiniteCompHaus.equivalence A
    obj := F
    property := by
      apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
      rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
      exact ⟨⟨fun _ => inferInstance⟩, hF⟩ }

/--
Definition of `ofSheafCompHaus` / `ofSheafCompHaus` 的定义

English:
definition ofSheafCompHaus
  body: F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

中文:
定义 ofSheafCompHaus
  定义体: F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩
-/
noncomputable def ofSheafCompHaus
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts F]
    (hF : EqualizerCondition F) : Condensed A where
  obj := F
  property := by
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

/--
Definition of `ofSheafForgetCompHaus` / `ofSheafForgetCompHaus` 的定义

English:
definition ofSheafForgetCompHaus
  body: F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

中文:
定义 ofSheafForgetCompHaus
  定义体: F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩
-/
noncomputable def ofSheafForgetCompHaus
    {FA : A -> A -> Type*} {CA : A -> Type*} [forall X Y, FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [ReflectsFiniteLimits (CategoryTheory.forget A)]
    (F : CompHaus.{u}ᵒᵖ ⥤ A) [PreservesFiniteProducts (F ⋙ CategoryTheory.forget A)]
    (hF : EqualizerCondition (F ⋙ CategoryTheory.forget A)) : Condensed A where
  obj := F
  property := by
    apply isSheaf_coherent_of_hasPullbacks_of_comp F (CategoryTheory.forget A)
    rw [isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
    exact ⟨⟨fun _ => inferInstance⟩, hF⟩

/--
theorem `equalizerCondition` / 定理 `equalizerCondition`

English:
theorem equalizerCondition
  given: (X : Condensed A)
  statement: EqualizerCondition X.obj
  proof: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

中文:
定理 equalizerCondition
  条件: (X : Condensed A)
  结论: EqualizerCondition X.obj
  证明: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

Depends on / 依赖: X.obj, X.property, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
theorem equalizerCondition (X : Condensed A) : EqualizerCondition X.obj :=
.2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

/-- A condensed object preserves finite products. -/
noncomputable instance (X : Condensed A) : PreservesFiniteProducts X.obj :=
.mp isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj
.1 X.property

/-- A condensed object regarded as a sheaf on `Profinite` preserves finite products. -/
noncomputable instance (X : Sheaf (coherentTopology Profinite.{u}) A) :
    PreservesFiniteProducts X.obj :=
.mp isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj
.1 X.property

/--
theorem `equalizerCondition_profinite` / 定理 `equalizerCondition_profinite`

English:
theorem equalizerCondition_profinite
  given: (X : Sheaf (coherentTopology Profinite.{u}) A)
  proof: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

中文:
定理 equalizerCondition_profinite
  条件: (X : 层 (coherentTopology Profinite.{u}) A)
  证明: .2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

Depends on / 依赖: X.obj, X.property, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
theorem equalizerCondition_profinite (X : Sheaf (coherentTopology Profinite.{u}) A) :
    EqualizerCondition X.obj :=
.2 .mp X.property isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X.obj

/-- A condensed object regarded as a sheaf on `Stonean` preserves finite products. -/
noncomputable instance (X : Sheaf (coherentTopology Stonean.{u}) A) :
    PreservesFiniteProducts X.obj :=
.mp X.property isSheaf_iff_preservesFiniteProducts_of_projective X.obj

end Condensed

namespace CondensedSet

/--
Definition of `ofSheafStonean` / `ofSheafStonean` 的定义

English:
abbreviation ofSheafStonean
  signature: (F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1))
  body: Condensed.ofSheafStonean F

中文:
缩写 ofSheafStonean
  签名: (F : Stonean.{u}ᵒᵖ ⥤ 类型 (u + 1))
  定义体: Condensed.ofSheafStonean F

Depends on / 依赖: Condensed, Condensed.ofSheafStonean, ofSheafStonean
-/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] : CondensedSet :=
  Condensed.ofSheafStonean F

/--
Definition of `ofSheafProfinite` / `ofSheafProfinite` 的定义

English:
abbreviation ofSheafProfinite
  signature: (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
  body: Condensed.ofSheafProfinite F hF

中文:
缩写 ofSheafProfinite
  签名: (F : Profinite.{u}ᵒᵖ ⥤ 类型 (u + 1))
  定义体: Condensed.ofSheafProfinite F hF

Depends on / 依赖: Condensed, Condensed.ofSheafProfinite, ofSheafProfinite
-/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafProfinite F hF

/--
Definition of `ofSheafCompHaus` / `ofSheafCompHaus` 的定义

English:
abbreviation ofSheafCompHaus
  signature: (F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1))
  body: Condensed.ofSheafCompHaus F hF

中文:
缩写 ofSheafCompHaus
  签名: (F : CompHaus.{u}ᵒᵖ ⥤ 类型 (u + 1))
  定义体: Condensed.ofSheafCompHaus F hF

Depends on / 依赖: Condensed, Condensed.ofSheafCompHaus, ofSheafCompHaus
-/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedSet :=
  Condensed.ofSheafCompHaus F hF

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R]

/--
Definition of `ofSheafStonean` / `ofSheafStonean` 的定义

English:
abbreviation ofSheafStonean
  signature: (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
  body: haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafStonean F

中文:
缩写 ofSheafStonean
  签名: (F : Stonean.{u}ᵒᵖ ⥤ 模范畴.{u + 1} R)
  定义体: haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafStonean F

Depends on / 依赖: Condensed, Condensed.ofSheafStonean, HasLimitsOfSize, ModuleCat, hasLimitsOfSizeShrink, ofSheafStonean
-/
noncomputable abbrev ofSheafStonean (F : Stonean.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafStonean F

/--
Definition of `ofSheafProfinite` / `ofSheafProfinite` 的定义

English:
abbreviation ofSheafProfinite
  signature: (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
  body: haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafProfinite F hF

中文:
缩写 ofSheafProfinite
  签名: (F : Profinite.{u}ᵒᵖ ⥤ 模范畴.{u + 1} R)
  定义体: haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafProfinite F hF

Depends on / 依赖: Condensed, Condensed.ofSheafProfinite, HasLimitsOfSize, ModuleCat, hasLimitsOfSizeShrink, ofSheafProfinite
-/
noncomputable abbrev ofSheafProfinite (F : Profinite.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  haveI : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.ofSheafProfinite F hF

/--
Definition of `ofSheafCompHaus` / `ofSheafCompHaus` 的定义

English:
abbreviation ofSheafCompHaus
  signature: (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
  body: Condensed.ofSheafCompHaus F hF

中文:
缩写 ofSheafCompHaus
  签名: (F : CompHaus.{u}ᵒᵖ ⥤ 模范畴.{u + 1} R)
  定义体: Condensed.ofSheafCompHaus F hF

Depends on / 依赖: Condensed, Condensed.ofSheafCompHaus, ofSheafCompHaus
-/
noncomputable abbrev ofSheafCompHaus (F : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R)
    [PreservesFiniteProducts F] (hF : EqualizerCondition F) : CondensedMod R :=
  Condensed.ofSheafCompHaus F hF

end CondensedMod
