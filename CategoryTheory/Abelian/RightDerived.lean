/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Right-derived functors

We define the right-derived functors `F.rightDerived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

We first define a functor
`F.rightDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.up ℕ)` which is
`injectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`I : InjectiveResolution X`, then `F.rightDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `I.cocomplex`
(this isomorphism is `I.isoRightDerivedToHomotopyCategoryObj F`).

Then, the right-derived functors `F.rightDerived n : C ⥤ D` are obtained by composing
`F.rightDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_rightDerived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `NatTrans.rightDerived`: the natural transformation between right derived functors
  induced by a natural transformation.
* `Functor.toRightDerivedZero`: the natural transformation `F ⟶ F.rightDerived 0`,
  which is an isomorphism when `F` is left exact (i.e. preserves finite limits),
  see also `Functor.rightDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.rightDerived` (and `Functor.leftDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a right derived functor
  `F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`,
  and `F.rightDerived` shall be redefined using `F.rightDerivedFunctorPlus`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/--
Definition of `Functor.rightDerivedToHomotopyCategory` / `Functor.rightDerivedToHomotopyCategory` 的定义

English:
definition Functor.rightDerivedToHomotopyCategory
  signature: (F : C ⥤ D) [F.Additive]
  body: injectiveResolutions C ⋙ F.mapHomotopyCategory _

中文:
定义 函子.rightDerivedToHomotopyCategory
  签名: (F : C ⥤ D) [F.加性]
  定义体: injectiveResolutions C ⋙ F.mapHomotopyCategory _

Depends on / 依赖: F.mapHomotopyCategory, injectiveResolutions, mapHomotopyCategory
-/
noncomputable def Functor.rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.up Nat) :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _

/--
Definition of `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj` / `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj` 的定义

English:
definition InjectiveResolution.isoRightDerivedToHomotopyCategoryObj
  signature: {X : C}
  body: (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

中文:
定义 单射消解.isoRightDerivedToHomotopyCategoryObj
  签名: {X : C}
  定义体: (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

Depends on / 依赖: F.mapHomotopyCategory, F.mapHomotopyCategoryFactors, I.cocomplex, I.iso, IsLimit, Subsingleton, cocomplex, mapHomotopyCategory, mapHomotopyCategoryFactors, mapIso
-/
noncomputable def InjectiveResolution.isoRightDerivedToHomotopyCategoryObj {X : C}
    (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj I.cocomplex :=
  (F.mapHomotopyCategory _).mapIso I.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app I.cocomplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality` / 引理 `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality`

English:
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality
  proof: by
  dsimp [Functor.rightDerivedToHomotopyCategory, isoRightDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.up Nat)).hom.naturality]
  rfl

中文:
引理 单射消解.isoRightDerivedToHomotopyCategoryObj_hom_naturality
  证明: by
  dsimp [Functor.rightDerivedToHomotopyCategory, isoRightDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.up Nat)).hom.naturality]
  rfl

Depends on / 依赖: ComplexShape, ComplexShape.up, F.mapHomotopyCategoryFactors, Functor, Functor.map_comp, Functor.map_comp_assoc, Functor.rightDerivedToHomotopyCategory, hom.naturality, isoRightDerivedToHomotopyCategoryObj, iso_hom_naturality, mapHomotopyCategoryFactors, map_comp, map_comp_assoc, naturality, rightDerivedToHomotopyCategory
-/
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.map f ≫ (J.isoRightDerivedToHomotopyCategoryObj F).hom =
      (I.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
  dsimp [Functor.rightDerivedToHomotopyCategory, isoRightDerivedToHomotopyCategoryObj]
  rw [← Functor.map_comp_assoc]; rw [iso_hom_naturality f I J φ comm]; rw [Functor.map_comp]; rw [assoc]; rw [assoc]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.up Nat)).hom.naturality]
  rfl

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality` / 引理 `InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality`

English:
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality
  proof: by
    rw [← cancel_epi (I.isoRightDerivedToHomotopyCategoryObj F).hom]; rw [Iso.hom_inv_id_assoc]
    dsimp
    rw [← isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc f I J φ comm F]; rw [Iso.hom_inv_id]; rw [comp_id]

中文:
引理 单射消解.isoRightDerivedToHomotopyCategoryObj_inv_naturality
  证明: by
    rw [← cancel_epi (I.isoRightDerivedToHomotopyCategoryObj F).hom]; rw [Iso.hom_inv_id_assoc]
    dsimp
    rw [← isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc f I J φ comm F]; rw [Iso.hom_inv_id]; rw [comp_id]

Depends on / 依赖: I.isoRightDerivedToHomotopyCategoryObj, Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, isoRightDerivedToHomotopyCategoryObj, isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc
-/
lemma InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    (I.isoRightDerivedToHomotopyCategoryObj F).inv ≫ F.rightDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (J.isoRightDerivedToHomotopyCategoryObj F).inv := by
    rw [← cancel_epi (I.isoRightDerivedToHomotopyCategoryObj F).hom]; rw [Iso.hom_inv_id_assoc]
    dsimp
    rw [← isoRightDerivedToHomotopyCategoryObj_hom_naturality_assoc f I J φ comm F]; rw [Iso.hom_inv_id]; rw [comp_id]

/--
Definition of `Functor.rightDerived` / `Functor.rightDerived` 的定义

English:
definition Functor.rightDerived
  signature: (F : C ⥤ D) [F.Additive] (n : Nat)
  body: F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

中文:
定义 函子.rightDerived
  签名: (F : C ⥤ D) [F.加性] (n : 自然数)
  定义体: F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

Depends on / 依赖: F.rightDerivedToHomotopyCategory, HomotopyCategory, HomotopyCategory.homologyFunctor, homologyFunctor, rightDerivedToHomotopyCategory
-/
noncomputable def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : Nat) : C ⥤ D :=
  F.rightDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

/--
Definition of `InjectiveResolution.isoRightDerivedObj` / `InjectiveResolution.isoRightDerivedObj` 的定义

English:
definition InjectiveResolution.isoRightDerivedObj
  signature: {X : C} (I : InjectiveResolution X)
  body: (HomotopyCategory.homologyFunctor D _ n).mapIso
    (I.isoRightDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).app _

中文:
定义 单射消解.isoRightDerivedObj
  签名: {X : C} (I : 单射消解 X)
  定义体: (HomotopyCategory.homologyFunctor D _ n).mapIso
    (I.isoRightDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).app _

Depends on / 依赖: ComplexShape, ComplexShape.up, HomotopyCategory, HomotopyCategory.homologyFunctor, HomotopyCategory.homologyFunctorFactors, I.isoRightDerivedToHomotopyCategoryObj, homologyFunctor, homologyFunctorFactors, isoRightDerivedToHomotopyCategoryObj, mapIso
-/
noncomputable def InjectiveResolution.isoRightDerivedObj {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
    (I.isoRightDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `InjectiveResolution.isoRightDerivedObj_hom_naturality` / 引理 `InjectiveResolution.isoRightDerivedObj_hom_naturality`

English:
lemma InjectiveResolution.isoRightDerivedObj_hom_naturality
  proof: by
  dsimp [isoRightDerivedObj, Functor.rightDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f I J φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n)

中文:
引理 单射消解.isoRightDerivedObj_hom_naturality
  证明: by
  dsimp [isoRightDerivedObj, Functor.rightDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f I J φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n)

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.map_comp, Functor.map_comp_assoc, Functor.rightDerived, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, InjectiveResolution, InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality, hom.naturality, homologyFunctorFactors, isoRightDerivedObj, isoRightDerivedToHomotopyCategoryObj_hom_naturality, map_comp, map_comp_assoc, naturality, rightDerived
-/
lemma InjectiveResolution.isoRightDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObj F n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoRightDerivedObj, Functor.rightDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality f I J φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).hom.naturality]
  rfl

@[reassoc]
/--
lemma `InjectiveResolution.isoRightDerivedObj_inv_naturality` / 引理 `InjectiveResolution.isoRightDerivedObj_inv_naturality`

English:
lemma InjectiveResolution.isoRightDerivedObj_inv_naturality
  proof: by
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 单射消解.isoRightDerivedObj_inv_naturality
  证明: by
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: InjectiveResolution, InjectiveResolution.isoRightDerivedObj_hom_naturality, Iso.inv_hom_id, Iso.inv_hom_id_assoc, J.isoRightDerivedObj, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, isoRightDerivedObj, isoRightDerivedObj_hom_naturality
-/
lemma InjectiveResolution.isoRightDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (I.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (J.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (J.isoRightDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

/--
lemma `Functor.isZero_rightDerived_obj_injective_succ` / 引理 `Functor.isZero_rightDerived_obj_injective_succ`

English:
lemma Functor.isZero_rightDerived_obj_injective_succ
  proof: by
  refine IsZero.of_iso ?_ ((InjectiveResolution.self X).isoRightDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

中文:
引理 函子.isZero_rightDerived_obj_injective_succ
  证明: by
  refine IsZero.of_iso ?_ ((InjectiveResolution.self X).isoRightDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

Depends on / 依赖: F.map_isZero, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, InjectiveResolution, InjectiveResolution.self, IsZero, IsZero.of_iso, ShortComplex, ShortComplex.exact_of_isZero_X, exactAt_iff_isZero_homology, isZero_zero, isoRightDerivedObj, map_isZero, of_iso
-/
lemma Functor.isZero_rightDerived_obj_injective_succ
    (F : C ⥤ D) [F.Additive] (n : Nat) (X : C) [Injective X] :
    IsZero ((F.rightDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((InjectiveResolution.self X).isoRightDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Functor.rightDerived_map_eq` / 定理 `Functor.rightDerived_map_eq`

English:
theorem Functor.rightDerived_map_eq
  statement: (F : C ⥤ D) [F.Additive] (n : Nat) {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← cancel_mono (Q.isoRightDerivedObj F n).hom]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [CochainComplex.single₀_map_f_zer

中文:
定理 函子.rightDerived_map_eq
  结论: (F : C ⥤ D) [F.加性] (n : 自然数) {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← cancel_mono (Q.isoRightDerivedObj F n).hom]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [CochainComplex.single₀_map_f_zer

Depends on / 依赖: CochainComplex, CochainComplex.single, HomologicalComplex, HomologicalComplex.comp_f, InjectiveResolution, InjectiveResolution.isoRightDerivedObj_hom_naturality, Iso.inv_hom_id, Q.isoRightDerivedObj, cancel_mono, comp_f, comp_id, inv_hom_id, isoRightDerivedObj, isoRightDerivedObj_hom_naturality
-/
theorem Functor.rightDerived_map_eq (F : C ⥤ D) [F.Additive] (n : Nat) {X Y : C} (f : X ⟶ Y)
    {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : P.cocomplex ⟶ Q.cocomplex)
    (w : P.ι ≫ g = (CochainComplex.single₀ C).map f ≫ Q.ι) :
    (F.rightDerived n).map f =
      (P.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoRightDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoRightDerivedObj F n).hom]; rw [InjectiveResolution.isoRightDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [CochainComplex.single₀_map_f_zero]

/--
Definition of `NatTrans.rightDerivedToHomotopyCategory` / `NatTrans.rightDerivedToHomotopyCategory` 的定义

English:
definition NatTrans.rightDerivedToHomotopyCategory
  body: Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.up Nat))

中文:
定义 自然变换.rightDerivedToHomotopyCategory
  定义体: Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.up Nat))

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.whiskerLeft, NatTrans, NatTrans.mapHomotopyCategory, mapHomotopyCategory, whiskerLeft
-/
noncomputable def NatTrans.rightDerivedToHomotopyCategory
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.rightDerivedToHomotopyCategory ⟶ G.rightDerivedToHomotopyCategory :=
  Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.up Nat))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `InjectiveResolution.rightDerivedToHomotopyCategory_app_eq` / 引理 `InjectiveResolution.rightDerivedToHomotopyCategory_app_eq`

English:
lemma InjectiveResolution.rightDerivedToHomotopyCategory_app_eq
  proof: by
  rw [← cancel_mono (P.isoRightDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoRightDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.rightDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  ob

中文:
引理 单射消解.rightDerivedToHomotopyCategory_app_eq
  证明: by
  rw [← cancel_mono (P.isoRightDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoRightDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.rightDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  ob

Depends on / 依赖: Functor, Functor.mapHomotopyCategoryFactors, Functor.map_comp, HomotopyCategory, HomotopyCategory.quotient, Iso.inv_hom_id, NatTrans, NatTrans.mapHomologicalComplex_naturality, NatTrans.rightDerivedToHomotopyCategory, P.isoRightDerivedToHomotopyCategoryObj, cancel_mono, comp_id, id_comp, inv_hom_id, isoRightDerivedToHomotopyCategoryObj, mapHomologicalComplex_naturality, mapHomotopyCategoryFactors, map_comp, map_surjective, quotient
-/
lemma InjectiveResolution.rightDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X) :
    (NatTrans.rightDerivedToHomotopyCategory α).app X =
      (P.isoRightDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (P.isoRightDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoRightDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoRightDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.rightDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
/--
lemma `NatTrans.rightDerivedToHomotopyCategory_id` / 引理 `NatTrans.rightDerivedToHomotopyCategory_id`

English:
lemma NatTrans.rightDerivedToHomotopyCategory_id
  given: (F : C ⥤ D) [F.Additive]
  proof: rfl

@[simp, reassoc]

中文:
引理 自然变换.rightDerivedToHomotopyCategory_id
  条件: (F : C ⥤ D) [F.加性]
  证明: rfl

@[simp, reassoc]
-/
lemma NatTrans.rightDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `NatTrans.rightDerivedToHomotopyCategory_comp` / 引理 `NatTrans.rightDerivedToHomotopyCategory_comp`

English:
lemma NatTrans.rightDerivedToHomotopyCategory_comp
  statement: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

中文:
引理 自然变换.rightDerivedToHomotopyCategory_comp
  结论: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl
-/
lemma NatTrans.rightDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.rightDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.rightDerivedToHomotopyCategory α ≫
        NatTrans.rightDerivedToHomotopyCategory β := rfl

/--
Definition of `NatTrans.rightDerived` / `NatTrans.rightDerived` 的定义

English:
definition NatTrans.rightDerived
  body: Functor.whiskerRight (NatTrans.rightDerivedToHomotopyCategory α) _

@[simp]

中文:
定义 自然变换.rightDerived
  定义体: Functor.whiskerRight (NatTrans.rightDerivedToHomotopyCategory α) _

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, NatTrans, NatTrans.rightDerivedToHomotopyCategory, rightDerivedToHomotopyCategory, whiskerRight
-/
noncomputable def NatTrans.rightDerived
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : Nat) :
    F.rightDerived n ⟶ G.rightDerived n :=
  Functor.whiskerRight (NatTrans.rightDerivedToHomotopyCategory α) _

@[simp]
/--
theorem `NatTrans.rightDerived_id` / 定理 `NatTrans.rightDerived_id`

English:
theorem NatTrans.rightDerived_id
  given: (F : C ⥤ D) [F.Additive] (n : Nat)
  proof: by
  dsimp only [rightDerived]
  simp only [rightDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

中文:
定理 自然变换.rightDerived_id
  条件: (F : C ⥤ D) [F.加性] (n : 自然数)
  证明: by
  dsimp only [rightDerived]
  simp only [rightDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

Depends on / 依赖: Functor, Functor.whiskerRight_id, rightDerived, rightDerivedToHomotopyCategory_id, whiskerRight_id
-/
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : Nat) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) := by
  dsimp only [rightDerived]
  simp only [rightDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `NatTrans.rightDerived_comp` / 定理 `NatTrans.rightDerived_comp`

English:
theorem NatTrans.rightDerived_comp
  statement: {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  proof: by
  simp [NatTrans.rightDerived]

中文:
定理 自然变换.rightDerived_comp
  结论: {F G H : C ⥤ D} [F.加性] [G.加性] [H.加性]
  证明: by
  simp [NatTrans.rightDerived]

Depends on / 依赖: NatTrans, NatTrans.rightDerived, rightDerived
-/
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : Nat) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [NatTrans.rightDerived]

namespace InjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightDerived_app_eq` / 引理 `rightDerived_app_eq`

English:
lemma rightDerived_app_eq
  proof: by
  dsimp [NatTrans.rightDerived, isoRightDerivedObj]
  rw [InjectiveResolution.rightDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).hom.naturality_assoc
    ((NatTrans.mapHo

中文:
引理 rightDerived_app_eq
  证明: by
  dsimp [NatTrans.rightDerived, isoRightDerivedObj]
  rw [InjectiveResolution.rightDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).hom.naturality_assoc
    ((NatTrans.mapHo

Depends on / 依赖: ComplexShape, ComplexShape.up, Functor, Functor.comp_map, Functor.map_comp, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, InjectiveResolution, InjectiveResolution.rightDerivedToHomotopyCategory_app_eq, Iso.hom_inv_id_app_assoc, NatTrans, NatTrans.mapHomologicalComplex, NatTrans.rightDerived, P.cocomplex, cocomplex, comp_map, hom.naturality_assoc, hom_inv_id_app_assoc, homologyFunctorFactors, isoRightDerivedObj
-/
lemma rightDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : InjectiveResolution X)
    (n : Nat) : (NatTrans.rightDerived α n).app X =
      (P.isoRightDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.up Nat) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
        (P.isoRightDerivedObj G n).inv := by
  dsimp [NatTrans.rightDerived, isoRightDerivedObj]
  rw [InjectiveResolution.rightDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up Nat)).app P.cocomplex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toRightDerivedZero'` / `toRightDerivedZero'` 的定义

English:
definition toRightDerivedZero'
  signature: {X : C}
  body: HomologicalComplex.liftCycles _ (F.map (P.ι.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [HomologicalComplex.Hom.comm]; rw [HomologicalComplex.single_obj_d]; rw [zero_comp]; rw [F.map_zero])

中文:
定义 toRightDerivedZero'
  签名: {X : C}
  定义体: HomologicalComplex.liftCycles _ (F.map (P.ι.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [HomologicalComplex.Hom.comm]; rw [HomologicalComplex.single_obj_d]; rw [zero_comp]; rw [F.map_zero])

Depends on / 依赖: F.map, F.map_comp, F.map_zero, HomologicalComplex, HomologicalComplex.Hom.comm, HomologicalComplex.liftCycles, HomologicalComplex.single_obj_d, liftCycles, map_comp, map_zero, single_obj_d, zero_comp
-/
noncomputable def toRightDerivedZero' {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.obj X ⟶ ((F.mapHomologicalComplex _).obj P.cocomplex).cycles 0 :=
  HomologicalComplex.liftCycles _ (F.map (P.ι.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [HomologicalComplex.Hom.comm]; rw [HomologicalComplex.single_obj_d]; rw [zero_comp]; rw [F.map_zero])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toRightDerivedZero'_comp_iCycles` / 引理 `toRightDerivedZero'_comp_iCycles`

English:
lemma toRightDerivedZero'_comp_iCycles
  statement: {C} [Category* C] [Abelian C] {X : C}
  proof: by
  simp [toRightDerivedZero']

中文:
引理 toRightDerivedZero'_comp_iCycles
  结论: {C} [范畴* C] [交换 C] {X : C}
  证明: by
  simp [toRightDerivedZero']
-/
lemma toRightDerivedZero'_comp_iCycles {C} [Category* C] [Abelian C] {X : C}
    (P : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    P.toRightDerivedZero' F ≫
      HomologicalComplex.iCycles _ _ = F.map (P.ι.f 0) := by
  simp [toRightDerivedZero']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `toRightDerivedZero'_naturality` / 引理 `toRightDerivedZero'_naturality`

English:
lemma toRightDerivedZero'_naturality
  statement: {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [← cancel_mono (HomologicalComplex.iCycles _ _), assoc,
    toRightDerivedZero'_comp_iCycles,
    CochainComplex.single₀_obj_zero, HomologicalComplex.cyclesMap_i,
    Functor.mapHomologicalComplex_map_f, toRightDerivedZero'_comp_iCycles_assoc,
    ← F.map_comp, comm]

中文:
引理 toRightDerivedZero'_naturality
  结论: {C} [范畴* C] [交换 C] {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [← cancel_mono (HomologicalComplex.iCycles _ _), assoc,
    toRightDerivedZero'_comp_iCycles,
    CochainComplex.single₀_obj_zero, HomologicalComplex.cyclesMap_i,
    Functor.mapHomologicalComplex_map_f, toRightDerivedZero'_comp_iCycles_assoc,
    ← F.map_comp, comm]
-/
lemma toRightDerivedZero'_naturality {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y)
    (φ : P.cocomplex ⟶ Q.cocomplex) (comm : P.ι.f 0 ≫ φ.f 0 = f ≫ Q.ι.f 0)
    (F : C ⥤ D) [F.Additive] :
    F.map f ≫ Q.toRightDerivedZero' F =
      P.toRightDerivedZero' F ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map φ) 0 := by
  simp only [← cancel_mono (HomologicalComplex.iCycles _ _), assoc,
    toRightDerivedZero'_comp_iCycles,
    CochainComplex.single₀_obj_zero, HomologicalComplex.cyclesMap_i,
    Functor.mapHomologicalComplex_map_f, toRightDerivedZero'_comp_iCycles_assoc,
    ← F.map_comp, comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso ((InjectiveResolution.self X).toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  rw [CochainComplex.isIso_liftCycles_iff]
  refine ⟨ShortComplex.Splitting.exact ?_, inferInstance⟩
  exact
    { r := 𝟙 _
      s := 0
      s_g := (F.map_isZero (isZero_zero _)).eq_of_src _ _ }

end InjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Functor.toRightDerivedZero` / `Functor.toRightDerivedZero` 的定义

English:
definition Functor.toRightDerivedZero
  signature: (F : C ⥤ D) [F.Additive]
  body: (injectiveResolution X).toRightDerivedZero' F ≫
    (CochainComplex.isoHomologyπ₀ _).hom ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) 0).inv.app _
  naturality {X Y} f := by
    dsimp [rightDerived]
    rw [assoc]; rw [assoc]; rw [InjectiveResolution.toRightDerivedZero'_n

中文:
定义 函子.toRightDerivedZero
  签名: (F : C ⥤ D) [F.加性]
  定义体: (injectiveResolution X).toRightDerivedZero' F ≫
    (CochainComplex.isoHomologyπ₀ _).hom ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) 0).inv.app _
  naturality {X Y} f := by
    dsimp [rightDerived]
    rw [assoc]; rw [assoc]; rw [InjectiveResolution.toRightDerivedZero'_n

Depends on / 依赖: injectiveResolution, toRightDerivedZero
-/
noncomputable def Functor.toRightDerivedZero (F : C ⥤ D) [F.Additive] :
    F ⟶ F.rightDerived 0 where
  app X := (injectiveResolution X).toRightDerivedZero' F ≫
    (CochainComplex.isoHomologyπ₀ _).hom ≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up Nat) 0).inv.app _
  naturality {X Y} f := by
    dsimp [rightDerived]
    rw [assoc]; rw [assoc]; rw [InjectiveResolution.toRightDerivedZero'_naturality_assoc f
      (injectiveResolution X) (injectiveResolution Y)
      (InjectiveResolution.desc f _ _) (by simp)]; rw [← HomologicalComplex.homologyπ_naturality_assoc]
    erw [← NatTrans.naturality]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `InjectiveResolution.toRightDerivedZero_eq` / 引理 `InjectiveResolution.toRightDerivedZero_eq`

English:
lemma InjectiveResolution.toRightDerivedZero_eq
  proof: by
  dsimp [Functor.toRightDerivedZero, isoRightDerivedObj]
  have h₁ := InjectiveResolution.toRightDerivedZero'_naturality
    (𝟙 X) (injectiveResolution X) I (desc (𝟙 X) _ _) (by simp) F
  simp only [Functor.map_id, id_comp] at h₁
  have h₂ : (I.isoRightDerivedToHomotopyCategoryObj F).hom =
    (F

中文:
引理 单射消解.toRightDerivedZero_eq
  证明: by
  dsimp [Functor.toRightDerivedZero, isoRightDerivedObj]
  have h₁ := InjectiveResolution.toRightDerivedZero'_naturality
    (𝟙 X) (injectiveResolution X) I (desc (𝟙 X) _ _) (by simp) F
  simp only [Functor.map_id, id_comp] at h₁
  have h₂ : (I.isoRightDerivedToHomotopyCategoryObj F).hom =
    (F

Depends on / 依赖: F.mapHomologicalComplex, Functor, Functor.map_id, Functor.toRightDerivedZero, HomotopyCategory, HomotopyCategory.homologyFunctor, HomotopyCategory.quotient, I.isoRightDerivedToHomotopyCategoryObj, InjectiveResolution, InjectiveResolution.toRightDerivedZero, _naturality, cancel_mono, comp_id, homologyFunctor, id_comp, injectiveResolution, isoRightDerivedObj, isoRightDerivedToHomotopyCategoryObj, mapHomologicalComplex, map_id
-/
lemma InjectiveResolution.toRightDerivedZero_eq
    {X : C} (I : InjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.toRightDerivedZero.app X = I.toRightDerivedZero' F ≫
      (CochainComplex.isoHomologyπ₀ _).hom ≫ (I.isoRightDerivedObj F 0).inv := by
  dsimp [Functor.toRightDerivedZero, isoRightDerivedObj]
  have h₁ := InjectiveResolution.toRightDerivedZero'_naturality
    (𝟙 X) (injectiveResolution X) I (desc (𝟙 X) _ _) (by simp) F
  simp only [Functor.map_id, id_comp] at h₁
  have h₂ : (I.isoRightDerivedToHomotopyCategoryObj F).hom =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (desc (𝟙 X) _ _) :=
    comp_id _
  rw [← cancel_mono ((HomotopyCategory.homologyFunctor _ _ 0).map
      (I.isoRightDerivedToHomotopyCategoryObj F).hom)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [assoc]; rw [← Functor.map_comp]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [comp_id]; rw [reassoc_of% h₁]; rw [h₂]; rw [← HomologicalComplex.homologyπ_naturality_assoc]
  erw [← NatTrans.naturality]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
instance (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    IsIso (F.toRightDerivedZero.app X) := by
  rw [(InjectiveResolution.self X).toRightDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

set_option backward.isDefEq.respectTransparency.types false in
instance {X : C} (P : InjectiveResolution X) :
    IsIso (P.toRightDerivedZero' F) := by
  dsimp [InjectiveResolution.toRightDerivedZero']
  rw [CochainComplex.isIso_liftCycles_iff]; rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  exact ⟨KernelFork.mapIsLimit _ (P.isLimitKernelFork) F⟩

set_option backward.isDefEq.respectTransparency false in
instance (X : C) : IsIso (F.toRightDerivedZero.app X) := by
  dsimp [Functor.toRightDerivedZero]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso F.toRightDerivedZero
  body: NatIso.isIso_of_isIso_app _

中文:
实例 :
  签名: 是同构 F.toRightDerivedZero
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance : IsIso F.toRightDerivedZero :=
  NatIso.isIso_of_isIso_app _

namespace Functor

/-- The canonical isomorphism `F.rightDerived 0 ≅ F` when `F` is left exact
(i.e. preserves finite limits). -/
@[simps! inv]
/--
Definition of `rightDerivedZeroIsoSelf` / `rightDerivedZeroIsoSelf` 的定义

English:
definition rightDerivedZeroIsoSelf
  signature: : F.rightDerived 0 ≅ F
  body: (asIso F.toRightDerivedZero).symm

@[reassoc (attr := simp)]

中文:
定义 rightDerivedZeroIsoSelf
  签名: : F.rightDerived 0 ≅ F
  定义体: (asIso F.toRightDerivedZero).symm

@[reassoc (attr := simp)]

Depends on / 依赖: F.toRightDerivedZero, toRightDerivedZero
-/
noncomputable def rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F :=
  (asIso F.toRightDerivedZero).symm

@[reassoc (attr := simp)]
/--
lemma `rightDerivedZeroIsoSelf_hom_inv_id` / 引理 `rightDerivedZeroIsoSelf_hom_inv_id`

English:
lemma rightDerivedZeroIsoSelf_hom_inv_id
  proof: F.rightDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 rightDerivedZeroIsoSelf_hom_inv_id
  证明: F.rightDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: F.rightDerivedZeroIsoSelf.hom_inv_id, hom_inv_id, rightDerivedZeroIsoSelf
-/
lemma rightDerivedZeroIsoSelf_hom_inv_id :
    F.rightDerivedZeroIsoSelf.hom ≫ F.toRightDerivedZero = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `rightDerivedZeroIsoSelf_inv_hom_id` / 引理 `rightDerivedZeroIsoSelf_inv_hom_id`

English:
lemma rightDerivedZeroIsoSelf_inv_hom_id
  proof: F.rightDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 rightDerivedZeroIsoSelf_inv_hom_id
  证明: F.rightDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: F.rightDerivedZeroIsoSelf.inv_hom_id, inv_hom_id, rightDerivedZeroIsoSelf
-/
lemma rightDerivedZeroIsoSelf_inv_hom_id :
    F.toRightDerivedZero ≫ F.rightDerivedZeroIsoSelf.hom = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `rightDerivedZeroIsoSelf_hom_inv_id_app` / 引理 `rightDerivedZeroIsoSelf_hom_inv_id_app`

English:
lemma rightDerivedZeroIsoSelf_hom_inv_id_app
  given: (X : C)
  proof: F.rightDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
引理 rightDerivedZeroIsoSelf_hom_inv_id_app
  条件: (X : C)
  证明: F.rightDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: F.rightDerivedZeroIsoSelf.hom_inv_id_app, hom_inv_id_app, rightDerivedZeroIsoSelf
-/
lemma rightDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.rightDerivedZeroIsoSelf.hom.app X ≫ F.toRightDerivedZero.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
/--
lemma `rightDerivedZeroIsoSelf_inv_hom_id_app` / 引理 `rightDerivedZeroIsoSelf_inv_hom_id_app`

English:
lemma rightDerivedZeroIsoSelf_inv_hom_id_app
  given: (X : C)
  proof: F.rightDerivedZeroIsoSelf.inv_hom_id_app X

中文:
引理 rightDerivedZeroIsoSelf_inv_hom_id_app
  条件: (X : C)
  证明: F.rightDerivedZeroIsoSelf.inv_hom_id_app X

Depends on / 依赖: F.rightDerivedZeroIsoSelf.inv_hom_id_app, inv_hom_id_app, rightDerivedZeroIsoSelf
-/
lemma rightDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.toRightDerivedZero.app X ≫ F.rightDerivedZeroIsoSelf.hom.app X = 𝟙 _ :=
  F.rightDerivedZeroIsoSelf.inv_hom_id_app X

end Functor

end

end CategoryTheory
