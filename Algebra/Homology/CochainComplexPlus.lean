/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Bounded below cochain complexes

In this file, we consider the full subcategory `CochainComplex.Plus C`
of `CochainComplex C ℤ` consisting of bounded below cochain complexes
in a category `C`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C]

/--
Definition of `plus` / `plus` 的定义

English:
definition plus
  signature: [HasZeroMorphisms C]
  body: fun K => exists (n : Int), K.IsStrictlyGE n

中文:
定义 plus
  签名: [HasZeroMorphisms C]
  定义体: fun K => exists (n : Int), K.IsStrictlyGE n
-/
protected def plus [HasZeroMorphisms C] : ObjectProperty (CochainComplex C Int) :=
  fun K => exists (n : Int), K.IsStrictlyGE n

/--
lemma `plus_iff` / 引理 `plus_iff`

English:
lemma plus_iff
  given: [HasZeroMorphisms C] (K : CochainComplex C Int)
  proof: Iff.rfl

中文:
引理 plus_iff
  条件: [HasZeroMorphisms C] (K : CochainComplex C 整数)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma plus_iff [HasZeroMorphisms C] (K : CochainComplex C Int) :
    CochainComplex.plus C K ↔ exists (n : Int), K.IsStrictlyGE n := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroMorphisms
  signature: C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  body: by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

中文:
实例 [HasZeroMorphisms
  签名: C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  定义体: by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

Depends on / 依赖: isStrictlyGE_of_iso
-/
instance [HasZeroMorphisms C] : (CochainComplex.plus C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ e ⟨n, _⟩
    exact ⟨n, isStrictlyGE_of_iso e n⟩

/--
Definition of `Plus` / `Plus` 的定义

English:
abbreviation Plus
  signature: [HasZeroMorphisms C]
  body: (CochainComplex.plus C).FullSubcategory

中文:
缩写 Plus
  签名: [HasZeroMorphisms C]
  定义体: (CochainComplex.plus C).FullSubcategory

Depends on / 依赖: CochainComplex, CochainComplex.plus, FullSubcategory
-/
abbrev Plus [HasZeroMorphisms C] :=
  (CochainComplex.plus C).FullSubcategory

namespace Plus

section

variable [HasZeroMorphisms C]

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : Plus C ⥤ CochainComplex C Int
  body: ObjectProperty.ι _

中文:
缩写 ι
  签名: : Plus C ⥤ CochainComplex C 整数
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev ι : Plus C ⥤ CochainComplex C Int := ObjectProperty.ι _

/--
Definition of `fullyFaithfulι` / `fullyFaithfulι` 的定义

English:
definition fullyFaithfulι
  signature: : (ι C).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
定义 fullyFaithfulι
  签名: : (ι C).FullyFaithful
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
def fullyFaithfulι : (ι C).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

instance (J : Type*) [SmallCategory J] [FinCategory J] [HasLimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : exists (n : Int), forall (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ union {0}) ⟨0, by grind⟩, fun j =>
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isLimitOfPreserves (HomologicalComplex.eval _ _ i) p.isLimit).hom_ext
      (fun j => (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_tgt _ _)

instance (J : Type*) [SmallCategory J] [FinCategory J] [HasColimitsOfShape J C] :
    (CochainComplex.plus C).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro K ⟨p⟩
    obtain ⟨n, hn⟩ : exists (n : Int), forall (j : J), (p.diag.obj j).IsStrictlyGE n := by
      choose n hn using p.prop_diag_obj
      exact ⟨Finset.min' (Finset.image n ⊤ union {0}) ⟨0, by grind⟩, fun j =>
        (p.diag.obj j).isStrictlyGE_of_ge _ _ (Finset.min'_le _ (n j) (by simp))⟩
    refine ⟨n, ?_⟩
    rw [isStrictlyGE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    exact (isColimitOfPreserves (HomologicalComplex.eval _ _ i) p.isColimit).hom_ext
      (fun j => (isZero_of_isStrictlyGE (p.diag.obj j) n i).eq_of_src _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteLimits
  signature: C] : HasFiniteLimits (Plus C) where
  body: by infer_instance

中文:
实例 [HasFiniteLimits
  签名: C] : HasFiniteLimits (Plus C) where
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance [HasFiniteLimits C] : HasFiniteLimits (Plus C) where
  out J _ _ := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFiniteColimits
  signature: C] : HasFiniteColimits (Plus C) where
  body: by infer_instance

中文:
实例 [HasFiniteColimits
  签名: C] : HasFiniteColimits (Plus C) where
  定义体: by infer_instance

Depends on / 依赖: HomotopyCategory, HomotopyCategory.subcategoryAcyclic, Shift.linear_of_localization, infer_instance, linear_of_localization, subcategoryAcyclic
-/
instance [HasFiniteColimits C] : HasFiniteColimits (Plus C) where
  out J _ _ := by infer_instance

variable {C} in
/--
lemma `mono_iff` / 引理 `mono_iff`

English:
lemma mono_iff
  given: [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y)
  proof: ⟨fun _ => inferInstanceAs (Mono ((ι C).map f)),
    fun _ => Functor.mono_of_mono_map (ι C) (by assumption)⟩

中文:
引理 mono_iff
  条件: [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y)
  证明: ⟨fun _ => inferInstanceAs (Mono ((ι C).map f)),
    fun _ => Functor.mono_of_mono_map (ι C) (by assumption)⟩

Depends on / 依赖: Functor, Functor.Linear, Functor.mono_of_mono_map, HomotopyCategory, HomotopyCategory.singleFunctor, Linear, mono_of_mono_map, singleFunctor
-/
lemma mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom :=
  ⟨fun _ => inferInstanceAs (Mono ((ι C).map f)),
    fun _ => Functor.mono_of_mono_map (ι C) (by assumption)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimitsOfShape
  signature: WalkingCospan C] {X Y
  body: by
  rwa [← mono_iff]

中文:
实例 [HasLimitsOfShape
  签名: WalkingCospan C] {X Y
  定义体: by
  rwa [← mono_iff]

Depends on / 依赖: mono_iff
-/
instance [HasLimitsOfShape WalkingCospan C] {X Y : Plus C} (f : X ⟶ Y) [Mono f] :
    Mono f.hom := by
  rwa [← mono_iff]

/--
Definition of `quasiIso` / `quasiIso` 的定义

English:
definition quasiIso
  signature: [CategoryWithHomology C]
  body: (HomologicalComplex.quasiIso C (ComplexShape.up Int)).inverseImage (ι C)

中文:
定义 quasiIso
  签名: [CategoryWithHomology C]
  定义体: (HomologicalComplex.quasiIso C (ComplexShape.up Int)).inverseImage (ι C)

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplex, HomologicalComplex.quasiIso, inverseImage, quasiIso
-/
def quasiIso [CategoryWithHomology C] : MorphismProperty (Plus C) :=
  (HomologicalComplex.quasiIso C (ComplexShape.up Int)).inverseImage (ι C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (quasiIso C).HasTwoOutOfThreeProperty
  body: by
  dsimp [quasiIso]
  infer_instance

中文:
实例 [CategoryWithHomology
  签名: C] : (quasiIso C).HasTwoOutOfThree命题erty
  定义体: by
  dsimp [quasiIso]
  infer_instance

Depends on / 依赖: infer_instance, quasiIso
-/
instance [CategoryWithHomology C] : (quasiIso C).HasTwoOutOfThreeProperty := by
  dsimp [quasiIso]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithHomology
  signature: C] : (quasiIso C).IsStableUnderRetracts
  body: by
  dsimp [quasiIso]
  infer_instance

中文:
实例 [CategoryWithHomology
  签名: C] : (quasiIso C).IsStableUnderRetracts
  定义体: by
  dsimp [quasiIso]
  infer_instance

Depends on / 依赖: infer_instance, quasiIso
-/
instance [CategoryWithHomology C] : (quasiIso C).IsStableUnderRetracts := by
  dsimp [quasiIso]
  infer_instance

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: C] : (CochainComplex.plus C).IsStableUnderShift Int where
  body: ⟨fun K ⟨k, hk⟩ => ⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩⟩

中文:
实例 [Preadditive
  签名: C] : (CochainComplex.plus C).IsStableUnderShift 整数 where
  定义体: ⟨fun K ⟨k, hk⟩ => ⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩⟩

Depends on / 依赖: K.isStrictlyGE_shift, isStrictlyGE_shift
-/
instance [Preadditive C] : (CochainComplex.plus C).IsStableUnderShift Int where
  isStableUnderShiftBy n :=
    ⟨fun K ⟨k, hk⟩ => ⟨k - n, K.isStrictlyGE_shift k n _ (by lia)⟩⟩

end Plus

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

section

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [F.PreservesZeroMorphisms]

set_option backward.defeqAttrib.useBackward true in
/-- The functor on categories of bounded below cochain complexes that
is induced by a functor (which preserves zero morphisms). -/
@[simps!]
/--
Definition of `mapCochainComplexPlus` / `mapCochainComplexPlus` 的定义

English:
definition mapCochainComplexPlus
  signature: : CochainComplex.Plus C ⥤ CochainComplex.Plus D
  body: ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

中文:
定义 mapCochainComplexPlus
  签名: : CochainComplex.Plus C ⥤ CochainComplex.Plus D
  定义体: ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

Depends on / 依赖: CochainComplex, CochainComplex.Plus, F.mapHomologicalComplex, ObjectProperty, ObjectProperty.lift, infer_instance, mapHomologicalComplex
-/
def mapCochainComplexPlus : CochainComplex.Plus C ⥤ CochainComplex.Plus D :=
  ObjectProperty.lift _ (CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _) (fun K => by
    obtain ⟨i, hi⟩ := K.2
    refine ⟨i, ?_⟩
    dsimp [CochainComplex.Plus.ι]
    infer_instance)

/-- The isomorphism between `F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D`
and `CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _` when `F : C ⥤ D`
is a functor which preserves zero morphisms -/
@[simps!]
/--
Definition of `mapCochainComplexPlusCompι` / `mapCochainComplexPlusCompι` 的定义

English:
definition mapCochainComplexPlusCompι
  signature: :
  body: Iso.refl _

中文:
定义 mapCochainComplexPlusCompι
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def mapCochainComplexPlusCompι :
    F.mapCochainComplexPlus ⋙ CochainComplex.Plus.ι D ≅
      CochainComplex.Plus.ι C ⋙ F.mapHomologicalComplex _ := Iso.refl _

end

end Functor

end CategoryTheory
