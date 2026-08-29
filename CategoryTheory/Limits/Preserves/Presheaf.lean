/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Elements

/-!
# Finite-limit-preserving presheaves

In this file we prove that if `C` is a small finitely cocomplete category and `A : Cᵒᵖ ⥤ Type u`
is a presheaf, then `CostructuredArrow yoneda A` is filtered (equivalently, the category of
elements of `A` is cofiltered) if and only if `A` preserves finite limits.

This is one of the keys steps of establishing the equivalence `Ind C ≌ (Cᵒᵖ ⥤ₗ Type u)` (here,
`Cᵒᵖ ⥤ₗ Type u` is the category of left exact functors) for a *small* finitely cocomplete category
`C`.

## Implementation notes

In the entire file, we are careful about details like functor associativity to ensure that we do
not end up in situations where we have morphisms like `colimit.ι F i ≫ f`, where the domain of `f`
is `colimit G` where `F` and `G` are definitionally equal but not syntactically equal. In these
situations, lemmas about `colimit.ι G i ≫ f` cannot be applied using `rw` and `simp`, forcing the
use of `erw`. In particular, for us this means that `HasColimit.isoOfNatIso (Iso.refl _)` is better
than `Iso.refl _` and that we should be very particular about functor associativity.

The theorem is also true for large categories and the proof given here generalizes to this case on
paper. However, our infrastructure for commuting finite limits of shape `J` and filtered colimits
of shape `K` is fundamentally not equipped to deal with the case where not all limits of shape `K`
exist. In fact, not even the definition `colimitLimitToLimitColimit` can be written down if not
all limits of shape `K` exist. Refactoring this to the level of generality we need would be a major
undertaking. Since the application to the category of Ind-objects only require the case where `C`
is small, we leave this as a TODO.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.3.13
* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1], Proposition 6.1.2
-/

@[expose] public section

open CategoryTheory Limits Functor

universe v u

namespace CategoryTheory.Limits

section LargeCategory

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : Cᵒᵖ ⥤ Type v)

/--
theorem `isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits` / 定理 `isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits`

English:
theorem isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
  proof: by
  suffices IsCofiltered A.Elements from
    IsFiltered.of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
  suffices HasFiniteLimits A.Elements from IsCofiltered.of_hasFiniteLimits A.Elements
  exact ⟨fun J _ _ => inferInstance⟩

中文:
定理 isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
  证明: by
  suffices IsCofiltered A.Elements from
    IsFiltered.of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
  suffices HasFiniteLimits A.Elements from IsCofiltered.of_hasFiniteLimits A.Elements
  exact ⟨fun J _ _ => inferInstance⟩

Depends on / 依赖: A.Elements, CategoryOfElements, CategoryOfElements.costructuredArrowYonedaEquivalence, Elements, HasFiniteLimits, IsCofiltered, IsCofiltered.of_hasFiniteLimits, IsFiltered, IsFiltered.of_equivalence, costructuredArrowYonedaEquivalence, of_equivalence, of_hasFiniteLimits
-/
theorem isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits
    [PreservesFiniteLimits A] : IsFiltered (CostructuredArrow yoneda A) := by
  suffices IsCofiltered A.Elements from
    IsFiltered.of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
  suffices HasFiniteLimits A.Elements from IsCofiltered.of_hasFiniteLimits A.Elements
  exact ⟨fun J _ _ => inferInstance⟩

end LargeCategory

variable {C : Type u} [SmallCategory C] [HasFiniteColimits C]

variable (A : Cᵒᵖ ⥤ Type u)

namespace PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux

variable {J : Type} [SmallCategory J] [FinCategory J] (K : J ⥤ Cᵒᵖ)

/--
Definition of `functorToInterchange` / `functorToInterchange` 的定义

English:
definition functorToInterchange
  signature: : J ⥤ CostructuredArrow yoneda A ⥤ Type u
  body: K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)

中文:
定义 functorTo整数erchange
  签名: : J ⥤ CostructuredArrow yoneda A ⥤ 类型u
  定义体: K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, coyoneda, whiskeringLeft
-/
def functorToInterchange : J ⥤ CostructuredArrow yoneda A ⥤ Type u :=
  K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)

/-- (Implementation) The definition of `functorToInterchange`. -/
@[simps!]
/--
Definition of `functorToInterchangeIso` / `functorToInterchangeIso` 的定义

English:
definition functorToInterchangeIso
  signature: : functorToInterchange A K ≅
  body: Iso.refl _

#adaptation_note

中文:
定义 functorTo整数erchangeIso
  签名: : functorTo整数erchange A K ≅
  定义体: Iso.refl _

#adaptation_note

Depends on / 依赖: Iso.refl
-/
def functorToInterchangeIso : functorToInterchange A K ≅
    K ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _) :=
  Iso.refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- (Implementation) One way to express the flipped version of our functor. We choose this
association because the type of `Presheaf.tautologicalCocone` is
`Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda)`, so this association will show up in the
proof. -/
@[simps! +dsimpLhs]
/--
Definition of `flipFunctorToInterchange` / `flipFunctorToInterchange` 的定义

English:
definition flipFunctorToInterchange
  signature: : (functorToInterchange A K).flip ≅
  body: Iso.refl _

中文:
定义 flipFunctorTo整数erchange
  签名: : (functorTo整数erchange A K).flip ≅
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def flipFunctorToInterchange : (functorToInterchange A K).flip ≅
    ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft J Cᵒᵖ (Type u)).obj K) :=
  Iso.refl _

/-- (Implementation) A natural isomorphism we will need to construct `iso`. -/
@[simps! -fullyApplied hom_app]
/--
Definition of `isoAux` / `isoAux` 的定义

English:
definition isoAux
  signature: :
  body: Iso.refl _

中文:
定义 isoAux
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def isoAux :
    (CostructuredArrow.proj yoneda A ⋙ yoneda ⋙ (evaluation Cᵒᵖ (Type u)).obj (limit K)) ≅
      ((coyoneda ⋙ (whiskeringLeft (CostructuredArrow yoneda A) C (Type u)).obj
        (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
  Iso.refl _

/--
Definition of `iso` / `iso` 的定义

English:
definition iso
  signature: [IsFiltered (CostructuredArrow yoneda A)]
  body: calc
  A.obj (limit K) ≅ (colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)).obj (limit K) :=
      (IsColimit.coconePointUniqueUpToIso
        (Presheaf.isColimitTautologicalCocone A) (colimit.isColimit _)).app _
  _ ≅ colimit (((CostructuredArrow.proj yoneda A) ⋙ yoneda) ⋙ (evaluation _ _).obj (limit K)) :=
      (colimitObjIsoColimitCompEvaluation _ _)
  _ ≅ colimit ((CostructuredArrow.proj yoneda A) ⋙ yoneda ⋙ (evaluation _ _).obj (limit K)) :=
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  _ ≅ colimit
      ((coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
        HasColimit.isoOfNatIso (isoAux A K)
  _ ≅ colimit (limit (K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)))) :=
        HasColimit.isoOfNatIso (preservesLimitIso _ _)
  _ ≅ colimit (limit (functorToInterchange A K)) :=
        HasColimit.isoOfNatIso (HasLimit.isoOfNatIso (functorToInterchangeIso A K).symm)
  _ ≅ limit (colimit (functorToInterchange A K).flip) := colimitLimitIso _
  _ ≅ limit (colimit
        ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj K)) :=
          HasLimit.isoOfNatIso (HasColimit.isoOfNatIso (flipFunctorToInterchange A K))
  _ ≅ limit (K ⋙ colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)) :=
        HasLimit.isoOfNatIso
          (colimitCompWhiskeringLeftIsoCompColimit (CostructuredArrow.proj yoneda A ⋙ yoneda) K)
  _ ≅ limit (K ⋙ A) := HasLimit.isoOfNatIso (isoWhiskerLeft _
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit _) (Presheaf.isColimitTautologicalCocone A)))

中文:
定义 iso
  签名: [是Filtered (CostructuredArrow yoneda A)]
  定义体: calc
  A.obj (limit K) ≅ (colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)).obj (limit K) :=
      (IsColimit.coconePointUniqueUpToIso
        (Presheaf.isColimitTautologicalCocone A) (colimit.isColimit _)).app _
  _ ≅ colimit (((CostructuredArrow.proj yoneda A) ⋙ yoneda) ⋙ (evaluation _ _).obj (limit K)) :=
      (colimitObjIsoColimitCompEvaluation _ _)
  _ ≅ colimit ((CostructuredArrow.proj yoneda A) ⋙ yoneda ⋙ (evaluation _ _).obj (limit K)) :=
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  _ ≅ colimit
      ((coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
        HasColimit.isoOfNatIso (isoAux A K)
  _ ≅ colimit (limit (K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)))) :=
        HasColimit.isoOfNatIso (preservesLimitIso _ _)
  _ ≅ colimit (limit (functorToInterchange A K)) :=
        HasColimit.isoOfNatIso (HasLimit.isoOfNatIso (functorToInterchangeIso A K).symm)
  _ ≅ limit (colimit (functorToInterchange A K).flip) := colimitLimitIso _
  _ ≅ limit (colimit
        ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj K)) :=
          HasLimit.isoOfNatIso (HasColimit.isoOfNatIso (flipFunctorToInterchange A K))
  _ ≅ limit (K ⋙ colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)) :=
        HasLimit.isoOfNatIso
          (colimitCompWhiskeringLeftIsoCompColimit (CostructuredArrow.proj yoneda A ⋙ yoneda) K)
  _ ≅ limit (K ⋙ A) := HasLimit.isoOfNatIso (isoWhiskerLeft _
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit _) (Presheaf.isColimitTautologicalCocone A)))
-/
noncomputable def iso [IsFiltered (CostructuredArrow yoneda A)] :
    A.obj (limit K) ≅ limit (K ⋙ A) := calc
  A.obj (limit K) ≅ (colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)).obj (limit K) :=
      (IsColimit.coconePointUniqueUpToIso
        (Presheaf.isColimitTautologicalCocone A) (colimit.isColimit _)).app _
  _ ≅ colimit (((CostructuredArrow.proj yoneda A) ⋙ yoneda) ⋙ (evaluation _ _).obj (limit K)) :=
      (colimitObjIsoColimitCompEvaluation _ _)
  _ ≅ colimit ((CostructuredArrow.proj yoneda A) ⋙ yoneda ⋙ (evaluation _ _).obj (limit K)) :=
      HasColimit.isoOfNatIso (Functor.associator _ _ _)
  _ ≅ colimit
      ((coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj yoneda A)).obj (limit K)) :=
        HasColimit.isoOfNatIso (isoAux A K)
  _ ≅ colimit (limit (K ⋙ (coyoneda ⋙ (whiskeringLeft _ _ _).obj (CostructuredArrow.proj _ _)))) :=
        HasColimit.isoOfNatIso (preservesLimitIso _ _)
  _ ≅ colimit (limit (functorToInterchange A K)) :=
        HasColimit.isoOfNatIso (HasLimit.isoOfNatIso (functorToInterchangeIso A K).symm)
  _ ≅ limit (colimit (functorToInterchange A K).flip) := colimitLimitIso _
  _ ≅ limit (colimit
        ((CostructuredArrow.proj yoneda A ⋙ yoneda) ⋙ (whiskeringLeft _ _ _).obj K)) :=
          HasLimit.isoOfNatIso (HasColimit.isoOfNatIso (flipFunctorToInterchange A K))
  _ ≅ limit (K ⋙ colimit (CostructuredArrow.proj yoneda A ⋙ yoneda)) :=
        HasLimit.isoOfNatIso
          (colimitCompWhiskeringLeftIsoCompColimit (CostructuredArrow.proj yoneda A ⋙ yoneda) K)
  _ ≅ limit (K ⋙ A) := HasLimit.isoOfNatIso (isoWhiskerLeft _
        (IsColimit.coconePointUniqueUpToIso
          (colimit.isColimit _) (Presheaf.isColimitTautologicalCocone A)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `iso_hom` / 定理 `iso_hom`

English:
theorem iso_hom
  given: [IsFiltered (CostructuredArrow yoneda A)]
  statement: (iso A K).hom = limit.post K A
  proof: by
  -- We will have to use `ι_colimitLimitIso_limit_π` eventually, so let's start by
  -- transforming the goal into something from a colimit to a limit so that we can apply
  -- `limit.hom_ext` and `colimit.hom_ext`.
  dsimp [iso, -Iso.app_hom]
  simp only [Category.assoc]
  rw [Eq.comm]; rw [← Iso.inv_comp_eq]; rw [← Iso.inv_comp_eq]
  refine limit.hom_ext (fun j => colimit.hom_ext (fun i => ?_))
  simp only [Category.assoc]
  -- `simp` is not too helpful here because we will need to apply `NatTrans.comp_app_assoc`
  -- backwards at certain points, so we rewrite the term manually.
  rw [HasLimit.isoOfNatIso_hom_π]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [limit.post_π]; rw [colimitObjIsoColimitCompEvaluation_ι_inv_assoc (CostructuredArrow.proj yoneda A ⋙ yoneda)]; rw [Iso.app_inv]; rw [← NatTrans.comp_app_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_inv]; rw [Presheaf.tautologicalCocone_ι_app]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [ι_colimitLimitIso_limit_π_assoc]; rw [isoAux_hom_app]; rw [← NatTrans.comp_app_assoc]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [HasLimit.isoOfNatIso_hom_π]; rw [preservesLimitIso_hom_π_assoc]; rw [Iso.symm_hom]; rw [← NatTrans.comp_app_assoc]; rw [HasColimit.isoOfNatIso_ι_hom]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [ι_colimitCompWhiskeringLeftIsoCompColimit_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [isoWhiskerLeft_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [← whiskerLeft_comp]; rw [colimit.comp_coconePointUniqueUpToIso_hom]
  have := i.hom.naturality (limit.π K j)
  dsimp only [yoneda_obj_obj, Functor.const_obj_obj] at this
  rw [← this]
  ext
  simp [flipFunctorToInterchange, functorToInterchangeIso, functorToInterchange]

中文:
定理 iso_hom
  条件: [是Filtered (CostructuredArrow yoneda A)]
  结论: (iso A K).hom = limit.post K A
  证明: by
  -- We will have to use `ι_colimitLimitIso_limit_π` eventually, so let's start by
  -- transforming the goal into something from a colimit to a limit so that we can apply
  -- `limit.hom_ext` and `colimit.hom_ext`.
  dsimp [iso, -Iso.app_hom]
  simp only [Category.assoc]
  rw [Eq.comm]; rw [← Iso.inv_comp_eq]; rw [← Iso.inv_comp_eq]
  refine limit.hom_ext (fun j => colimit.hom_ext (fun i => ?_))
  simp only [Category.assoc]
  -- `simp` is not too helpful here because we will need to apply `NatTrans.comp_app_assoc`
  -- backwards at certain points, so we rewrite the term manually.
  rw [HasLimit.isoOfNatIso_hom_π]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [limit.post_π]; rw [colimitObjIsoColimitCompEvaluation_ι_inv_assoc (CostructuredArrow.proj yoneda A ⋙ yoneda)]; rw [Iso.app_inv]; rw [← NatTrans.comp_app_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_inv]; rw [Presheaf.tautologicalCocone_ι_app]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [ι_colimitLimitIso_limit_π_assoc]; rw [isoAux_hom_app]; rw [← NatTrans.comp_app_assoc]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [HasLimit.isoOfNatIso_hom_π]; rw [preservesLimitIso_hom_π_assoc]; rw [Iso.symm_hom]; rw [← NatTrans.comp_app_assoc]; rw [HasColimit.isoOfNatIso_ι_hom]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [ι_colimitCompWhiskeringLeftIsoCompColimit_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [isoWhiskerLeft_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [← whiskerLeft_comp]; rw [colimit.comp_coconePointUniqueUpToIso_hom]
  have := i.hom.naturality (limit.π K j)
  dsimp only [yoneda_obj_obj, Functor.const_obj_obj] at this
  rw [← this]
  ext
  simp [flipFunctorToInterchange, functorToInterchangeIso, functorToInterchange]
-/
theorem iso_hom [IsFiltered (CostructuredArrow yoneda A)] : (iso A K).hom = limit.post K A := by
  -- We will have to use `ι_colimitLimitIso_limit_π` eventually, so let's start by
  -- transforming the goal into something from a colimit to a limit so that we can apply
  -- `limit.hom_ext` and `colimit.hom_ext`.
  dsimp [iso, -Iso.app_hom]
  simp only [Category.assoc]
  rw [Eq.comm]; rw [← Iso.inv_comp_eq]; rw [← Iso.inv_comp_eq]
  refine limit.hom_ext (fun j => colimit.hom_ext (fun i => ?_))
  simp only [Category.assoc]
  -- `simp` is not too helpful here because we will need to apply `NatTrans.comp_app_assoc`
  -- backwards at certain points, so we rewrite the term manually.
  rw [HasLimit.isoOfNatIso_hom_π]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [limit.post_π]; rw [colimitObjIsoColimitCompEvaluation_ι_inv_assoc (CostructuredArrow.proj yoneda A ⋙ yoneda)]; rw [Iso.app_inv]; rw [← NatTrans.comp_app_assoc]; rw [colimit.comp_coconePointUniqueUpToIso_inv]; rw [Presheaf.tautologicalCocone_ι_app]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasLimit.isoOfNatIso_hom_π_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [HasColimit.isoOfNatIso_ι_hom_assoc]; rw [ι_colimitLimitIso_limit_π_assoc]; rw [isoAux_hom_app]; rw [← NatTrans.comp_app_assoc]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [HasLimit.isoOfNatIso_hom_π]; rw [preservesLimitIso_hom_π_assoc]; rw [Iso.symm_hom]; rw [← NatTrans.comp_app_assoc]; rw [HasColimit.isoOfNatIso_ι_hom]; rw [← NatTrans.comp_app_assoc]; rw [Category.assoc]; rw [ι_colimitCompWhiskeringLeftIsoCompColimit_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [isoWhiskerLeft_hom]; rw [NatTrans.comp_app]; rw [Category.assoc]; rw [← NatTrans.comp_app]; rw [← whiskerLeft_comp]; rw [colimit.comp_coconePointUniqueUpToIso_hom]
  have := i.hom.naturality (limit.π K j)
  dsimp only [yoneda_obj_obj, Functor.const_obj_obj] at this
  rw [← this]
  ext
  simp [flipFunctorToInterchange, functorToInterchangeIso, functorToInterchange]

/--
theorem `isIso_post` / 定理 `isIso_post`

English:
theorem isIso_post
  given: [IsFiltered (CostructuredArrow yoneda A)]
  statement: IsIso (limit.post K A)
  proof: iso_hom A K ▸ inferInstance

中文:
定理 isIso_post
  条件: [是Filtered (CostructuredArrow yoneda A)]
  结论: 是同构 (limit.post K A)
  证明: iso_hom A K ▸ inferInstance

Depends on / 依赖: iso_hom
-/
theorem isIso_post [IsFiltered (CostructuredArrow yoneda A)] : IsIso (limit.post K A) :=
  iso_hom A K ▸ inferInstance

end PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux

attribute [local instance] PreservesFiniteLimitsOfIsFilteredCostructuredArrowYonedaAux.isIso_post

/--
lemma `preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda` / 引理 `preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda`

English:
lemma preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
  proof: ⟨fun {_} => preservesLimit_of_isIso_post _ _⟩

中文:
引理 preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
  证明: ⟨fun {_} => preservesLimit_of_isIso_post _ _⟩

Depends on / 依赖: preservesLimit_of_isIso_post
-/
lemma preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
    [IsFiltered (CostructuredArrow yoneda A)] : PreservesFiniteLimits A where
  preservesFiniteLimits _ _ _ := ⟨fun {_} => preservesLimit_of_isIso_post _ _⟩

/--
theorem `isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits` / 定理 `isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits`

English:
theorem isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits
  proof: ⟨fun _ => preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda A,
   fun _ => isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A⟩

中文:
定理 isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits
  证明: ⟨fun _ => preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda A,
   fun _ => isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A⟩

Depends on / 依赖: isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits, preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda
-/
theorem isFiltered_costructuredArrow_yoneda_iff_nonempty_preservesFiniteLimits :
    IsFiltered (CostructuredArrow yoneda A) ↔ PreservesFiniteLimits A :=
  ⟨fun _ => preservesFiniteLimits_of_isFiltered_costructuredArrow_yoneda A,
   fun _ => isFiltered_costructuredArrow_yoneda_of_preservesFiniteLimits A⟩

end CategoryTheory.Limits
