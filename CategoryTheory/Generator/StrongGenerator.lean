/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Strong generators

If `P : ObjectProperty C`, we say that `P` is a strong generator if it is a
generator (in the sense that `IsSeparating P` holds) such that for any
proper subobject `A ⊂ X`, there exists a morphism `G ⟶ X` which does not factor
through `A` from an object satisfying `P`.

The main result is the lemma `isStrongGenerator_iff_exists_extremalEpi` which
says that if `P` is `w`-small, `C` is locally `w`-small and
has coproducts of size `w`, then `P` is a strong generator iff any
object of `C` is the target of an extremal epimorphism from a coproduct of
objects satisfying `P`.

We also show that if any object in `C` is a colimit of objects in `S`,
then `S` is a strong generator.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits


namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

/--
Definition of `IsStrongGenerator` / `IsStrongGenerator` 的定义

English:
definition IsStrongGenerator
  signature: : Prop
  body: P.IsSeparating ∧ forall ⦃X : C⦄ (A : Subobject X),
    (forall (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) -> A = ⊤

中文:
定义 IsStrongGenerator
  签名: : 命题
  定义体: P.IsSeparating ∧ forall ⦃X : C⦄ (A : Subobject X),
    (forall (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) -> A = ⊤

Depends on / 依赖: Factors, IsSeparating, P.IsSeparating, Subobject, Subobject.Factors
-/
def IsStrongGenerator : Prop :=
  P.IsSeparating ∧ forall ⦃X : C⦄ (A : Subobject X),
    (forall (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) -> A = ⊤

variable {P}

/--
lemma `isStrongGenerator_iff` / 引理 `isStrongGenerator_iff`

English:
lemma isStrongGenerator_iff
  proof: by
  refine ⟨fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X Y i _ h => ?_⟩,
    fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X A hA => ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G hG g => ?_)
    rw [Subobject.mk_factors_iff]
    exact h G hG g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow 

中文:
引理 isStrongGenerator_iff
  证明: by
  refine ⟨fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X Y i _ h => ?_⟩,
    fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X A hA => ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G hG g => ?_)
    rw [Subobject.mk_factors_iff]
    exact h G hG g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow 

Depends on / 依赖: A.arrow, Subobject, Subobject.factorThru_arrow, Subobject.isIso_arrow_iff_eq_top, Subobject.isIso_iff_mk_eq_top, Subobject.mk_factors_iff, factorThru_arrow, isIso_arrow_iff_eq_top, isIso_iff_mk_eq_top, mk_factors_iff
-/
lemma isStrongGenerator_iff :
    P.IsStrongGenerator ↔ P.IsSeparating ∧
      forall ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i],
        (forall (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) => f ≫ i)) -> IsIso i := by
  refine ⟨fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X Y i _ h => ?_⟩,
    fun ⟨hS₁, hS₂⟩ => ⟨hS₁, fun X A hA => ?_⟩⟩
  · rw [Subobject.isIso_iff_mk_eq_top]
    refine hS₂ _ (fun G hG g => ?_)
    rw [Subobject.mk_factors_iff]
    exact h G hG g
  · rw [← Subobject.isIso_arrow_iff_eq_top]
    exact hS₂ A.arrow (fun G hG g => ⟨_, Subobject.factorThru_arrow _ _ (hA G hG g)⟩)

namespace IsStrongGenerator

section

variable (hP : P.IsStrongGenerator)

include hP

/--
lemma `isSeparating` / 引理 `isSeparating`

English:
lemma isSeparating
  statement: P.IsSeparating
  proof: hP.1

中文:
引理 isSeparating
  结论: P.IsSeparating
  证明: hP.1
-/
lemma isSeparating : P.IsSeparating := hP.1

/--
lemma `subobject_eq_top` / 引理 `subobject_eq_top`

English:
lemma subobject_eq_top
  statement: {X : C} {A : Subobject X}
  proof: hP.2 _ hA

中文:
引理 subobject_eq_top
  结论: {X : C} {A : Subobject X}
  证明: hP.2 _ hA
-/
lemma subobject_eq_top {X : C} {A : Subobject X}
    (hA : forall (G : C) (_ : P G) (f : G ⟶ X), Subobject.Factors A f) :
    A = ⊤ :=
  hP.2 _ hA

/--
lemma `isIso_of_mono` / 引理 `isIso_of_mono`

English:
lemma isIso_of_mono
  given: ⦃X Y
  statement: C⦄ (i : X ⟶ Y) [Mono i]
  proof: (isStrongGenerator_iff.1 hP).2 i hi

中文:
引理 isIso_of_mono
  条件: ⦃X Y
  结论: C⦄ (i : X ⟶ Y) [Mono i]
  证明: (isStrongGenerator_iff.1 hP).2 i hi

Depends on / 依赖: isStrongGenerator_iff
-/
lemma isIso_of_mono ⦃X Y : C⦄ (i : X ⟶ Y) [Mono i]
    (hi : forall (G : C) (_ : P G), Function.Surjective (fun (f : G ⟶ X) => f ≫ i)) : IsIso i :=
  (isStrongGenerator_iff.1 hP).2 i hi

/--
lemma `exists_of_subobject_ne_top` / 引理 `exists_of_subobject_ne_top`

English:
lemma exists_of_subobject_ne_top
  given: {X : C} {A : Subobject X} (hA : A != ⊤)
  proof: by
  by_contra!
  exact hA (hP.subobject_eq_top this)

中文:
引理 exists_of_subobject_ne_top
  条件: {X : C} {A : Subobject X} (hA : A != ⊤)
  证明: by
  by_contra!
  exact hA (hP.subobject_eq_top this)

Depends on / 依赖: hP.subobject_eq_top, subobject_eq_top
-/
lemma exists_of_subobject_ne_top {X : C} {A : Subobject X} (hA : A != ⊤) :
    exists (G : C) (_ : P G) (f : G ⟶ X), ¬ Subobject.Factors A f := by
  by_contra!
  exact hA (hP.subobject_eq_top this)

/--
lemma `exists_of_mono_not_isIso` / 引理 `exists_of_mono_not_isIso`

English:
lemma exists_of_mono_not_isIso
  given: {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i)
  proof: by
  by_contra!
  exact hi (hP.isIso_of_mono i this)

中文:
引理 exists_of_mono_not_isIso
  条件: {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i)
  证明: by
  by_contra!
  exact hi (hP.isIso_of_mono i this)

Depends on / 依赖: hP.isIso_of_mono, isIso_of_mono
-/
lemma exists_of_mono_not_isIso {X Y : C} (i : X ⟶ Y) [Mono i] (hi : ¬ IsIso i) :
    exists (G : C) (_ : P G) (g : G ⟶ Y), forall (f : G ⟶ X), f ≫ i != g := by
  by_contra!
  exact hi (hP.isIso_of_mono i this)

end

end IsStrongGenerator

namespace IsStrongGenerator

/--
lemma `mk_of_exists_extremalEpi` / 引理 `mk_of_exists_extremalEpi`

English:
lemma mk_of_exists_extremalEpi
  proof: by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X => ?_), fun X Y i _ hi => ?_⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, hs, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (hs j) (c.inj j ≫ p)

中文:
引理 mk_of_exists_extremalEpi
  证明: by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X => ?_), fun X Y i _ hi => ?_⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, hs, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (hs j) (c.inj j ≫ p)

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.IsColimit.hom_ext, ExtremalEpi, ExtremalEpi.isIso, IsColimit, IsSeparating, IsSeparating.mk_of_exists_epi, c.inj, hom_ext, isStrongGenerator_iff, mk_of_exists_epi, replace
-/
lemma mk_of_exists_extremalEpi
    (hS : forall (X : C), exists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsColimit c)
      (p : c.pt ⟶ X), ExtremalEpi p) :
    P.IsStrongGenerator := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_epi.{w} (fun X => ?_), fun X Y i _ hi => ?_⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS X
    exact ⟨ι, s, hs, c, hc, p, inferInstance⟩
  · obtain ⟨ι, s, hs, c, hc, p, _⟩ := hS Y
    replace hi (j : ι) := hi (s j) (hs j) (c.inj j ≫ p)
    choose φ hφ using hi
    exact ExtremalEpi.isIso p (Cofan.IsColimit.desc hc φ) _
      (Cofan.IsColimit.hom_ext hc _ _ (by simp [hφ]))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `extremalEpi_coproductFrom` / 引理 `extremalEpi_coproductFrom`

English:
lemma extremalEpi_coproductFrom
  proof: hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f => ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

中文:
引理 extremalEpi_coproductFrom
  证明: hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f => ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

Depends on / 依赖: epi_coproductFrom, hP.isSeparating.epi_coproductFrom, isSeparating
-/
lemma extremalEpi_coproductFrom
    (hP : IsStrongGenerator P) (X : C) [HasCoproduct (P.coproductFromFamily X)] :
    ExtremalEpi (P.coproductFrom X) where
  toEpi := hP.isSeparating.epi_coproductFrom X
  isIso p i fac _ := hP.isIso_of_mono _ (fun G hG f => ⟨P.ιCoproductFrom f hG ≫ p, by simp [fac]⟩)

end IsStrongGenerator

/--
lemma `isStrongGenerator_iff_exists_extremalEpi` / 引理 `isStrongGenerator_iff_exists_extremalEpi`

English:
lemma isStrongGenerator_iff_exists_extremalEpi
  proof: by
  refine ⟨fun hP X => ?_, fun hP => .mk_of_exists_extremalEpi hP⟩
  have := hasCoproductsOfShape_of_small.{w} C (CostructuredArrow P.ι X)
  have := (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm
  refine ⟨_, fun j => ((equiv

中文:
引理 isStrongGenerator_iff_exists_extremalEpi
  证明: by
  refine ⟨fun hP X => ?_, fun hP => .mk_of_exists_extremalEpi hP⟩
  have := hasCoproductsOfShape_of_small.{w} C (CostructuredArrow P.ι X)
  have := (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm
  refine ⟨_, fun j => ((equiv

Depends on / 依赖: CostructuredArrow, Discrete, Discrete.equivalence, P.coproductFromFamily, coproductFromFamily, coproductIsCoproduct, equivShrink, equivalence, hasCoproductsOfShape_of_small, mk_of_exists_extremalEpi, whiskerEquivalence
-/
lemma isStrongGenerator_iff_exists_extremalEpi
    [HasCoproducts.{w} C] [LocallySmall.{w} C] [ObjectProperty.Small.{w} P] :
    P.IsStrongGenerator ↔
      forall (X : C), exists (ι : Type w) (s : ι -> C) (_ : forall i, P (s i)) (c : Cofan s) (_ : IsColimit c)
        (p : c.pt ⟶ X), ExtremalEpi p := by
  refine ⟨fun hP X => ?_, fun hP => .mk_of_exists_extremalEpi hP⟩
  have := hasCoproductsOfShape_of_small.{w} C (CostructuredArrow P.ι X)
  have := (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm
  refine ⟨_, fun j => ((equivShrink.{w} (CostructuredArrow P.ι X)).symm j).left.1,
    fun j => ((equivShrink.{w} _).symm j).1.2, _,
    (coproductIsCoproduct (P.coproductFromFamily X)).whiskerEquivalence
    (Discrete.equivalence (equivShrink.{w} _)).symm, _, hP.extremalEpi_coproductFrom X⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsStrongGenerator.mk_of_exists_colimitsOfShape` / 引理 `IsStrongGenerator.mk_of_exists_colimitsOfShape`

English:
lemma IsStrongGenerator.mk_of_exists_colimitsOfShape
  proof: by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_colimitsOfShape hP, fun X Y i _ hi => ?_⟩
  suffices IsSplitEpi i by
    obtain ⟨r, fac⟩ := this
    exact ⟨r, by simp [← cancel_mono i, fac]⟩
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  choose φ hφ using fun j => hi _ (p.prop_diag_obj j) (p.ι.a

中文:
引理 IsStrongGenerator.mk_of_exists_colimitsOfShape
  证明: by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_colimitsOfShape hP, fun X Y i _ hi => ?_⟩
  suffices IsSplitEpi i by
    obtain ⟨r, fac⟩ := this
    exact ⟨r, by simp [← cancel_mono i, fac]⟩
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  choose φ hφ using fun j => hi _ (p.prop_diag_obj j) (p.ι.a

Depends on / 依赖: Cocone, Cocone.mk, IsSeparating, IsSeparating.mk_of_exists_colimitsOfShape, IsSplitEpi, cancel_mono, fac_assoc, hom_ext, isColimit, isStrongGenerator_iff, mk_of_exists_colimitsOfShape, naturality, p.diag, p.isColimit.desc, p.isColimit.fac_assoc, p.isColimit.hom_ext, p.prop_diag_obj, prop_diag_obj
-/
lemma IsStrongGenerator.mk_of_exists_colimitsOfShape
    (hP : forall (X : C), exists (J : Type w) (_ : Category.{w'} J), P.colimitsOfShape J X) :
    P.IsStrongGenerator := by
  rw [isStrongGenerator_iff]
  refine ⟨IsSeparating.mk_of_exists_colimitsOfShape hP, fun X Y i _ hi => ?_⟩
  suffices IsSplitEpi i by
    obtain ⟨r, fac⟩ := this
    exact ⟨r, by simp [← cancel_mono i, fac]⟩
  obtain ⟨J, _, ⟨p⟩⟩ := hP Y
  choose φ hφ using fun j => hi _ (p.prop_diag_obj j) (p.ι.app j)
  let c : Cocone p.diag := Cocone.mk _
    { app := φ
      naturality j₁ j₂ f := by simp [← cancel_mono i, hφ] }
  refine ⟨p.isColimit.desc c, p.isColimit.hom_ext (fun j => ?_)⟩
  dsimp at hφ ⊢
  rw [p.isColimit.fac_assoc]; rw [hφ]; rw [Category.comp_id]

end ObjectProperty

end CategoryTheory
