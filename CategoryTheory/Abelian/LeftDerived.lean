/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Riccardo Brasca, Adam Topaz, Jujian Zhang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Left-derived functors

We define the left-derived functors `F.leftDerived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

We first define a functor
`F.leftDerivedToHomotopyCategory : C ⥤ HomotopyCategory D (ComplexShape.down ℕ)` which is
`projectiveResolutions C ⋙ F.mapHomotopyCategory _`. We show that if `X : C` and
`P : ProjectiveResolution X`, then `F.leftDerivedToHomotopyCategory.obj X` identifies
to the image in the homotopy category of the functor `F` applied objectwise to `P.complex`
(this isomorphism is `P.isoLeftDerivedToHomotopyCategoryObj F`).

Then, the left-derived functors `F.leftDerived n : C ⥤ D` are obtained by composing
`F.leftDerivedToHomotopyCategory` with the homology functors on the homotopy category.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `Functor.isZero_leftDerived_obj_projective_succ`: projective objects have no higher
  left derived functor.
* `NatTrans.leftDerived`: the natural transformation between left derived functors
  induced by a natural transformation.
* `Functor.fromLeftDerivedZero`: the natural transformation `F.leftDerived 0 ⟶ F`,
  which is an isomorphism when `F` is right exact (i.e. preserves finite colimits),
  see also `Functor.leftDerivedZeroIsoSelf`.

## TODO

* refactor `Functor.leftDerived` (and `Functor.rightDerived`) when the necessary
  material enters mathlib: derived categories, injective/projective derivability
  structures, existence of derived functors from derivability structures.
  Eventually, we shall get a left derived functor
  `F.leftDerivedFunctorMinus : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D`,
  and `F.leftDerived` shall be redefined using `F.leftDerivedFunctorMinus`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]

/--
Definition of `Functor.leftDerivedToHomotopyCategory` / `Functor.leftDerivedToHomotopyCategory` 的定义

English:
definition Functor.leftDerivedToHomotopyCategory
  signature: (F : C ⥤ D) [F.Additive]
  body: projectiveResolutions C ⋙ F.mapHomotopyCategory _

中文:
定义 Functor.leftDerivedToHomotopyCategory
  签名: (F : C ⥤ D) [F.Additive]
  定义体: projectiveResolutions C ⋙ F.mapHomotopyCategory _

Depends on / 依赖: F.mapHomotopyCategory, mapHomotopyCategory, projectiveResolutions
-/
noncomputable def Functor.leftDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    C ⥤ HomotopyCategory D (ComplexShape.down Nat) :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _

/--
Definition of `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj` / `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj` 的定义

English:
definition ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj
  signature: {X : C}
  body: (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

中文:
定义 ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj
  签名: {X : C}
  定义体: (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

Depends on / 依赖: F.mapHomotopyCategory, F.mapHomotopyCategoryFactors, P.complex, P.iso, complex, mapHomotopyCategory, mapHomotopyCategoryFactors, mapIso
-/
noncomputable def ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.obj X ≅
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).obj P.complex :=
  (F.mapHomotopyCategory _).mapIso P.iso ≪≫
    (F.mapHomotopyCategoryFactors _).app P.complex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality` / 引理 `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality`

English:
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
  proof: by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [assoc]; rw [← Functor.map_comp]; rw [iso_inv_naturality f P Q φ comm]; rw [Functor.map_comp]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down Nat)).inv.naturality_assoc]
  rfl

@[reassoc]

中文:
引理 ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
  证明: by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [assoc]; rw [← Functor.map_comp]; rw [iso_inv_naturality f P Q φ comm]; rw [Functor.map_comp]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down Nat)).inv.naturality_assoc]
  rfl

@[reassoc]

Depends on / 依赖: ComplexShape, ComplexShape.down, F.mapHomotopyCategoryFactors, Functor, Functor.leftDerivedToHomotopyCategory, Functor.map_comp, inv.naturality_assoc, isoLeftDerivedToHomotopyCategoryObj, iso_inv_naturality, leftDerivedToHomotopyCategory, mapHomotopyCategoryFactors, map_comp, naturality_assoc
-/
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    (P.isoLeftDerivedToHomotopyCategoryObj F).inv ≫ F.leftDerivedToHomotopyCategory.map f =
      (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ ≫
        (Q.isoLeftDerivedToHomotopyCategoryObj F).inv := by
  dsimp [Functor.leftDerivedToHomotopyCategory, isoLeftDerivedToHomotopyCategoryObj]
  rw [assoc]; rw [← Functor.map_comp]; rw [iso_inv_naturality f P Q φ comm]; rw [Functor.map_comp]
  erw [(F.mapHomotopyCategoryFactors (ComplexShape.down Nat)).inv.naturality_assoc]
  rfl

@[reassoc]
/--
lemma `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality` / 引理 `ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality`

English:
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
  proof: by
    dsimp
    rw [← cancel_epi (P.isoLeftDerivedToHomotopyCategoryObj F).inv]; rw [Iso.inv_hom_id_assoc]; rw [isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc f P Q φ comm F]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
  证明: by
    dsimp
    rw [← cancel_epi (P.isoLeftDerivedToHomotopyCategoryObj F).inv]; rw [Iso.inv_hom_id_assoc]; rw [isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc f P Q φ comm F]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, P.isoLeftDerivedToHomotopyCategoryObj, cancel_epi, comp_id, inv_hom_id, inv_hom_id_assoc, isoLeftDerivedToHomotopyCategoryObj, isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc
-/
lemma ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    F.leftDerivedToHomotopyCategory.map f ≫ (Q.isoLeftDerivedToHomotopyCategoryObj F).hom =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map φ := by
    dsimp
    rw [← cancel_epi (P.isoLeftDerivedToHomotopyCategoryObj F).inv]; rw [Iso.inv_hom_id_assoc]; rw [isoLeftDerivedToHomotopyCategoryObj_inv_naturality_assoc f P Q φ comm F]; rw [Iso.inv_hom_id]; rw [comp_id]

/--
Definition of `Functor.leftDerived` / `Functor.leftDerived` 的定义

English:
definition Functor.leftDerived
  signature: (F : C ⥤ D) [F.Additive] (n : Nat)
  body: F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

中文:
定义 Functor.leftDerived
  签名: (F : C ⥤ D) [F.Additive] (n : 自然数)
  定义体: F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

Depends on / 依赖: F.leftDerivedToHomotopyCategory, HomotopyCategory, HomotopyCategory.homologyFunctor, homologyFunctor, leftDerivedToHomotopyCategory
-/
noncomputable def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : Nat) : C ⥤ D :=
  F.leftDerivedToHomotopyCategory ⋙ HomotopyCategory.homologyFunctor D _ n

/--
Definition of `ProjectiveResolution.isoLeftDerivedObj` / `ProjectiveResolution.isoLeftDerivedObj` 的定义

English:
definition ProjectiveResolution.isoLeftDerivedObj
  signature: {X : C} (P : ProjectiveResolution X)
  body: (HomotopyCategory.homologyFunctor D _ n).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).app _

中文:
定义 ProjectiveResolution.isoLeftDerivedObj
  签名: {X : C} (P : ProjectiveResolution X)
  定义体: (HomotopyCategory.homologyFunctor D _ n).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).app _

Depends on / 依赖: ComplexShape, ComplexShape.down, HomotopyCategory, HomotopyCategory.homologyFunctor, HomotopyCategory.homologyFunctorFactors, P.isoLeftDerivedToHomotopyCategoryObj, homologyFunctor, homologyFunctorFactors, isoLeftDerivedToHomotopyCategoryObj, mapIso
-/
noncomputable def ProjectiveResolution.isoLeftDerivedObj {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (F.leftDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
    (P.isoLeftDerivedToHomotopyCategoryObj F) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).app _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `ProjectiveResolution.isoLeftDerivedObj_hom_naturality` / 引理 `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`

English:
lemma ProjectiveResolution.isoLeftDerivedObj_hom_naturality
  proof: by
  dsimp [isoLeftDerivedObj, Functor.leftDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n)

中文:
引理 ProjectiveResolution.isoLeftDerivedObj_hom_naturality
  证明: by
  dsimp [isoLeftDerivedObj, Functor.leftDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n)

Depends on / 依赖: ComplexShape, ComplexShape.down, Functor, Functor.leftDerived, Functor.map_comp, Functor.map_comp_assoc, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, ProjectiveResolution, ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality, hom.naturality, homologyFunctorFactors, isoLeftDerivedObj, isoLeftDerivedToHomotopyCategoryObj_hom_naturality, leftDerived, map_comp, map_comp_assoc, naturality
-/
lemma ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (F.leftDerived n).map f ≫ (Q.isoLeftDerivedObj F n).hom =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ := by
  dsimp [isoLeftDerivedObj, Functor.leftDerived]
  rw [assoc]; rw [← Functor.map_comp_assoc]; rw [ProjectiveResolution.isoLeftDerivedToHomotopyCategoryObj_hom_naturality f P Q φ comm F]; rw [Functor.map_comp]; rw [assoc]
  erw [(HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).hom.naturality]
  rfl

@[reassoc]
/--
lemma `ProjectiveResolution.isoLeftDerivedObj_inv_naturality` / 引理 `ProjectiveResolution.isoLeftDerivedObj_inv_naturality`

English:
lemma ProjectiveResolution.isoLeftDerivedObj_inv_naturality
  proof: by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 ProjectiveResolution.isoLeftDerivedObj_inv_naturality
  证明: by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, ProjectiveResolution, ProjectiveResolution.isoLeftDerivedObj_hom_naturality, Q.isoLeftDerivedObj, cancel_mono, comp_id, inv_hom_id, inv_hom_id_assoc, isoLeftDerivedObj, isoLeftDerivedObj_hom_naturality
-/
lemma ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] (n : Nat) :
    (P.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map f =
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map φ ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [assoc]; rw [assoc]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ comm F n]; rw [Iso.inv_hom_id_assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

/--
lemma `Functor.isZero_leftDerived_obj_projective_succ` / 引理 `Functor.isZero_leftDerived_obj_projective_succ`

English:
lemma Functor.isZero_leftDerived_obj_projective_succ
  proof: by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

中文:
引理 Functor.isZero_leftDerived_obj_projective_succ
  证明: by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

Depends on / 依赖: F.map_isZero, HomologicalComplex, HomologicalComplex.exactAt_iff_isZero_homology, IsZero, IsZero.of_iso, ProjectiveResolution, ProjectiveResolution.self, ShortComplex, ShortComplex.exact_of_isZero_X, exactAt_iff_isZero_homology, isZero_zero, isoLeftDerivedObj, map_isZero, of_iso
-/
lemma Functor.isZero_leftDerived_obj_projective_succ
    (F : C ⥤ D) [F.Additive] (n : Nat) (X : C) [Projective X] :
    IsZero ((F.leftDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero (by apply isZero_zero))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Functor.leftDerived_map_eq` / 定理 `Functor.leftDerived_map_eq`

English:
theorem Functor.leftDerived_map_eq
  statement: (F : C ⥤ D) [F.Additive] (n : Nat) {X Y : C} (f : X ⟶ Y)
  proof: by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [ChainComplex.single₀_map_f_zero]

中文:
定理 Functor.leftDerived_map_eq
  结论: (F : C ⥤ D) [F.Additive] (n : 自然数) {X Y : C} (f : X ⟶ Y)
  证明: by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [ChainComplex.single₀_map_f_zero]

Depends on / 依赖: ChainComplex, ChainComplex.single, HomologicalComplex, HomologicalComplex.comp_f, Iso.inv_hom_id, ProjectiveResolution, ProjectiveResolution.isoLeftDerivedObj_hom_naturality, Q.isoLeftDerivedObj, cancel_mono, comp_f, comp_id, inv_hom_id, isoLeftDerivedObj, isoLeftDerivedObj_hom_naturality
-/
theorem Functor.leftDerived_map_eq (F : C ⥤ D) [F.Additive] (n : Nat) {X Y : C} (f : X ⟶ Y)
    {P : ProjectiveResolution X} {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex)
    (w : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).map g ≫
          (Q.isoLeftDerivedObj F n).inv := by
  rw [← cancel_mono (Q.isoLeftDerivedObj F n).hom]; rw [ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q g _ F n]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rw [← HomologicalComplex.comp_f]; rw [w]; rw [HomologicalComplex.comp_f]; rw [ChainComplex.single₀_map_f_zero]

/--
Definition of `NatTrans.leftDerivedToHomotopyCategory` / `NatTrans.leftDerivedToHomotopyCategory` 的定义

English:
definition NatTrans.leftDerivedToHomotopyCategory
  body: Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down Nat))

中文:
定义 NatTrans.leftDerivedToHomotopyCategory
  定义体: Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down Nat))

Depends on / 依赖: ComplexShape, ComplexShape.down, Functor, Functor.whiskerLeft, NatTrans, NatTrans.mapHomotopyCategory, mapHomotopyCategory, whiskerLeft
-/
noncomputable def NatTrans.leftDerivedToHomotopyCategory
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    F.leftDerivedToHomotopyCategory ⟶ G.leftDerivedToHomotopyCategory :=
  Functor.whiskerLeft _ (NatTrans.mapHomotopyCategory α (ComplexShape.down Nat))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq` / 引理 `ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq`

English:
lemma ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
  proof: by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtai

中文:
引理 ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
  证明: by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtai

Depends on / 依赖: Functor, Functor.mapHomotopyCategoryFactors, Functor.map_comp, HomotopyCategory, HomotopyCategory.quotient, Iso.inv_hom_id, NatTrans, NatTrans.leftDerivedToHomotopyCategory, NatTrans.mapHomologicalComplex_naturality, P.isoLeftDerivedToHomotopyCategoryObj, cancel_mono, comp_id, id_comp, inv_hom_id, isoLeftDerivedToHomotopyCategoryObj, leftDerivedToHomotopyCategory, mapHomologicalComplex_naturality, mapHomotopyCategoryFactors, map_comp, map_surjective
-/
lemma ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X) :
    (NatTrans.leftDerivedToHomotopyCategory α).app X =
      (P.isoLeftDerivedToHomotopyCategoryObj F).hom ≫
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
          (P.isoLeftDerivedToHomotopyCategoryObj G).inv := by
  rw [← cancel_mono (P.isoLeftDerivedToHomotopyCategoryObj G).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  dsimp [isoLeftDerivedToHomotopyCategoryObj, Functor.mapHomotopyCategoryFactors,
    NatTrans.leftDerivedToHomotopyCategory]
  rw [assoc]
  erw [id_comp, comp_id]
  obtain ⟨β, hβ⟩ := (HomotopyCategory.quotient _ _).map_surjective (iso P).hom
  rw [← hβ]
  dsimp
  simp only [← Functor.map_comp, NatTrans.mapHomologicalComplex_naturality]
  rfl

@[simp]
/--
lemma `NatTrans.leftDerivedToHomotopyCategory_id` / 引理 `NatTrans.leftDerivedToHomotopyCategory_id`

English:
lemma NatTrans.leftDerivedToHomotopyCategory_id
  given: (F : C ⥤ D) [F.Additive]
  proof: rfl

@[simp, reassoc]

中文:
引理 NatTrans.leftDerivedToHomotopyCategory_id
  条件: (F : C ⥤ D) [F.Additive]
  证明: rfl

@[simp, reassoc]
-/
lemma NatTrans.leftDerivedToHomotopyCategory_id (F : C ⥤ D) [F.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `NatTrans.leftDerivedToHomotopyCategory_comp` / 引理 `NatTrans.leftDerivedToHomotopyCategory_comp`

English:
lemma NatTrans.leftDerivedToHomotopyCategory_comp
  statement: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  proof: rfl

中文:
引理 NatTrans.leftDerivedToHomotopyCategory_comp
  结论: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
  证明: rfl
-/
lemma NatTrans.leftDerivedToHomotopyCategory_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)
    [F.Additive] [G.Additive] [H.Additive] :
    NatTrans.leftDerivedToHomotopyCategory (α ≫ β) =
      NatTrans.leftDerivedToHomotopyCategory α ≫
        NatTrans.leftDerivedToHomotopyCategory β := rfl

/--
Definition of `NatTrans.leftDerived` / `NatTrans.leftDerived` 的定义

English:
definition NatTrans.leftDerived
  body: Functor.whiskerRight (NatTrans.leftDerivedToHomotopyCategory α) _

@[simp]

中文:
定义 NatTrans.leftDerived
  定义体: Functor.whiskerRight (NatTrans.leftDerivedToHomotopyCategory α) _

@[simp]

Depends on / 依赖: Functor, Functor.whiskerRight, NatTrans, NatTrans.leftDerivedToHomotopyCategory, leftDerivedToHomotopyCategory, whiskerRight
-/
noncomputable def NatTrans.leftDerived
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : Nat) :
    F.leftDerived n ⟶ G.leftDerived n :=
  Functor.whiskerRight (NatTrans.leftDerivedToHomotopyCategory α) _

@[simp]
/--
theorem `NatTrans.leftDerived_id` / 定理 `NatTrans.leftDerived_id`

English:
theorem NatTrans.leftDerived_id
  given: (F : C ⥤ D) [F.Additive] (n : Nat)
  proof: by
  dsimp only [leftDerived]
  simp only [leftDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

中文:
定理 NatTrans.leftDerived_id
  条件: (F : C ⥤ D) [F.Additive] (n : 自然数)
  证明: by
  dsimp only [leftDerived]
  simp only [leftDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

Depends on / 依赖: Functor, Functor.whiskerRight_id, leftDerived, leftDerivedToHomotopyCategory_id, whiskerRight_id
-/
theorem NatTrans.leftDerived_id (F : C ⥤ D) [F.Additive] (n : Nat) :
    NatTrans.leftDerived (𝟙 F) n = 𝟙 (F.leftDerived n) := by
  dsimp only [leftDerived]
  simp only [leftDerivedToHomotopyCategory_id, Functor.whiskerRight_id']
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp, reassoc]
/--
theorem `NatTrans.leftDerived_comp` / 定理 `NatTrans.leftDerived_comp`

English:
theorem NatTrans.leftDerived_comp
  statement: {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  proof: by
  simp [NatTrans.leftDerived]

中文:
定理 NatTrans.leftDerived_comp
  结论: {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
  证明: by
  simp [NatTrans.leftDerived]

Depends on / 依赖: NatTrans, NatTrans.leftDerived, leftDerived
-/
theorem NatTrans.leftDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : Nat) :
    NatTrans.leftDerived (α ≫ β) n = NatTrans.leftDerived α n ≫ NatTrans.leftDerived β n := by
  simp [NatTrans.leftDerived]

namespace ProjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftDerived_app_eq` / 引理 `leftDerived_app_eq`

English:
lemma leftDerived_app_eq
  proof: by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).hom.naturality_assoc
    ((NatTrans.mapHo

中文:
引理 leftDerived_app_eq
  证明: by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).hom.naturality_assoc
    ((NatTrans.mapHo

Depends on / 依赖: ComplexShape, ComplexShape.down, Functor, Functor.comp_map, Functor.map_comp, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, Iso.hom_inv_id_app_assoc, NatTrans, NatTrans.leftDerived, NatTrans.mapHomologicalComplex, P.complex, ProjectiveResolution, ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq, comp_map, complex, hom.naturality_assoc, hom_inv_id_app_assoc, homologyFunctorFactors, isoLeftDerivedObj
-/
lemma leftDerived_app_eq
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) {X : C} (P : ProjectiveResolution X)
    (n : Nat) : (NatTrans.leftDerived α n).app X =
      (P.isoLeftDerivedObj F n).hom ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down Nat) n).map
        ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
        (P.isoLeftDerivedObj G n).inv := by
  dsimp [NatTrans.leftDerived, isoLeftDerivedObj]
  rw [ProjectiveResolution.leftDerivedToHomotopyCategory_app_eq α P]; rw [Functor.map_comp]; rw [Functor.map_comp]; rw [assoc]
  erw [← (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) n).hom.naturality_assoc
    ((NatTrans.mapHomologicalComplex α (ComplexShape.down Nat)).app P.complex)]
  simp only [Functor.comp_map, Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromLeftDerivedZero'` / `fromLeftDerivedZero'` 的定义

English:
definition fromLeftDerivedZero'
  signature: {X : C}
  body: HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [complex_d_comp_π_f_zero]; rw [F.map_zero])

中文:
定义 fromLeftDerivedZero'
  签名: {X : C}
  定义体: HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [complex_d_comp_π_f_zero]; rw [F.map_zero])

Depends on / 依赖: F.map, F.map_comp, F.map_zero, HomologicalComplex, HomologicalComplex.descOpcycles, descOpcycles, map_comp, map_zero
-/
noncomputable def fromLeftDerivedZero' {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    ((F.mapHomologicalComplex _).obj P.complex).opcycles 0 ⟶ F.obj X :=
  HomologicalComplex.descOpcycles _ (F.map (P.π.f 0)) 1 (by simp) (by
    dsimp
    rw [← F.map_comp]; rw [complex_d_comp_π_f_zero]; rw [F.map_zero])

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `pOpcycles_comp_fromLeftDerivedZero'` / 引理 `pOpcycles_comp_fromLeftDerivedZero'`

English:
lemma pOpcycles_comp_fromLeftDerivedZero'
  statement: {C} [Category* C] [Abelian C] {X : C}
  proof: by
  simp [fromLeftDerivedZero']

中文:
引理 pOpcycles_comp_fromLeftDerivedZero'
  结论: {C} [Category* C] [Abelian C] {X : C}
  证明: by
  simp [fromLeftDerivedZero']

Depends on / 依赖: fromLeftDerivedZero
-/
lemma pOpcycles_comp_fromLeftDerivedZero' {C} [Category* C] [Abelian C] {X : C}
    (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.pOpcycles _ _ ≫ P.fromLeftDerivedZero' F = F.map (P.π.f 0) := by
  simp [fromLeftDerivedZero']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `fromLeftDerivedZero'_naturality` / 引理 `fromLeftDerivedZero'_naturality`

English:
lemma fromLeftDerivedZero'_naturality
  statement: {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
  proof: by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← F.map_comp, comm,
    HomologicalComplex.p_opcyclesMap_assoc, Functor.mapHomologicalComplex_map_f,
    pOpcycles_comp_fromLeftDerivedZero', pOpcycles_comp_fromLeftDerivedZero'_assoc]

中文:
引理 fromLeftDerivedZero'_naturality
  结论: {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
  证明: by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← F.map_comp, comm,
    HomologicalComplex.p_opcyclesMap_assoc, Functor.mapHomologicalComplex_map_f,
    pOpcycles_comp_fromLeftDerivedZero', pOpcycles_comp_fromLeftDerivedZero'_assoc]
-/
lemma fromLeftDerivedZero'_naturality {C} [Category* C] [Abelian C] {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f)
    (F : C ⥤ D) [F.Additive] :
    HomologicalComplex.opcyclesMap ((F.mapHomologicalComplex _).map φ) 0 ≫
        Q.fromLeftDerivedZero' F = P.fromLeftDerivedZero' F ≫ F.map f := by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _), ← F.map_comp, comm,
    HomologicalComplex.p_opcyclesMap_assoc, Functor.mapHomologicalComplex_map_f,
    pOpcycles_comp_fromLeftDerivedZero', pOpcycles_comp_fromLeftDerivedZero'_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso ((ProjectiveResolution.self X).fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff]
  refine ⟨ShortComplex.Splitting.exact ?_, inferInstance⟩
  exact
    { r := 0
      s := 𝟙 _
      f_r := (F.map_isZero (isZero_zero _)).eq_of_src _ _ }

end ProjectiveResolution

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Functor.fromLeftDerivedZero` / `Functor.fromLeftDerivedZero` 的定义

English:
definition Functor.fromLeftDerivedZero
  signature: (F : C ⥤ D) [F.Additive]
  body: (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) 0).hom.app _ ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫ (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    dsimp [leftDerived]
    rw [assoc]; rw [assoc]; rw [← ProjectiveResolution.fromLeftDerivedZero'_

中文:
定义 Functor.fromLeftDerivedZero
  签名: (F : C ⥤ D) [F.Additive]
  定义体: (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) 0).hom.app _ ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫ (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    dsimp [leftDerived]
    rw [assoc]; rw [assoc]; rw [← ProjectiveResolution.fromLeftDerivedZero'_

Depends on / 依赖: ComplexShape, ComplexShape.down, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, hom.app, homologyFunctorFactors
-/
noncomputable def Functor.fromLeftDerivedZero (F : C ⥤ D) [F.Additive] :
    F.leftDerived 0 ⟶ F where
  app X := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.down Nat) 0).hom.app _ ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫ (projectiveResolution X).fromLeftDerivedZero' F
  naturality {X Y} f := by
    dsimp [leftDerived]
    rw [assoc]; rw [assoc]; rw [← ProjectiveResolution.fromLeftDerivedZero'_naturality f
      (projectiveResolution X) (projectiveResolution Y)
      (ProjectiveResolution.lift f _ _) (by simp)]; rw [← HomologicalComplex.homologyι_naturality_assoc]
    erw [← NatTrans.naturality_assoc]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `ProjectiveResolution.fromLeftDerivedZero_eq` / 引理 `ProjectiveResolution.fromLeftDerivedZero_eq`

English:
lemma ProjectiveResolution.fromLeftDerivedZero_eq
  proof: by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ := ProjectiveResolution.fromLeftDerivedZero'_naturality
    (𝟙 X) P (projectiveResolution X) (lift (𝟙 X) _ _) (by simp) F
  have h₂ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategor

中文:
引理 ProjectiveResolution.fromLeftDerivedZero_eq
  证明: by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ := ProjectiveResolution.fromLeftDerivedZero'_naturality
    (𝟙 X) P (projectiveResolution X) (lift (𝟙 X) _ _) (by simp) F
  have h₂ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategor

Depends on / 依赖: F.mapHomologicalComplex, Functor, Functor.fromLeftDerivedZero, Functor.map_id, HomotopyCategory, HomotopyCategory.homologyFunctor, HomotopyCategory.quotient, P.isoLeftDerivedToHomotopyCategoryObj, ProjectiveResolution, ProjectiveResolution.fromLeftDerivedZero, _naturality, cancel_epi, comp_id, fromLeftDerivedZero, homologyFunctor, id_comp, isoLeftDerivedObj, isoLeftDerivedToHomotopyCategoryObj, mapHomologicalComplex, map_id
-/
lemma ProjectiveResolution.fromLeftDerivedZero_eq
    {X : C} (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] :
    F.fromLeftDerivedZero.app X = (P.isoLeftDerivedObj F 0).hom ≫
      (ChainComplex.isoHomologyι₀ _).hom ≫
        P.fromLeftDerivedZero' F := by
  dsimp [Functor.fromLeftDerivedZero, isoLeftDerivedObj]
  have h₁ := ProjectiveResolution.fromLeftDerivedZero'_naturality
    (𝟙 X) P (projectiveResolution X) (lift (𝟙 X) _ _) (by simp) F
  have h₂ : (P.isoLeftDerivedToHomotopyCategoryObj F).inv =
    (F.mapHomologicalComplex _ ⋙ HomotopyCategory.quotient _ _).map (lift (𝟙 X) _ _) :=
      id_comp _
  simp only [Functor.map_id, comp_id] at h₁
  rw [assoc]; rw [← cancel_epi ((HomotopyCategory.homologyFunctor _ _ 0).map
      (P.isoLeftDerivedToHomotopyCategoryObj F).inv)]; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id]; rw [Functor.map_id]; rw [id_comp]; rw [← h₁]; rw [h₂]; rw [← HomologicalComplex.homologyι_naturality_assoc]
  erw [← NatTrans.naturality_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
instance (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    IsIso (F.fromLeftDerivedZero.app X) := by
  rw [(ProjectiveResolution.self X).fromLeftDerivedZero_eq F]
  infer_instance

section

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency.types false in
instance {X : C} (P : ProjectiveResolution X) :
    IsIso (P.fromLeftDerivedZero' F) := by
  dsimp [ProjectiveResolution.fromLeftDerivedZero']
  rw [ChainComplex.isIso_descOpcycles_iff]; rw [ShortComplex.exact_and_epi_g_iff_g_is_cokernel]
  exact ⟨CokernelCofork.mapIsColimit _ (P.isColimitCokernelCofork) F⟩

set_option backward.isDefEq.respectTransparency false in
instance (X : C) : IsIso (F.fromLeftDerivedZero.app X) := by
  dsimp [Functor.fromLeftDerivedZero]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso F.fromLeftDerivedZero
  body: NatIso.isIso_of_isIso_app _

中文:
实例 :
  签名: IsIso F.fromLeftDerivedZero
  定义体: NatIso.isIso_of_isIso_app _

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, isIso_of_isIso_app
-/
instance : IsIso F.fromLeftDerivedZero :=
  NatIso.isIso_of_isIso_app _

namespace Functor

/-- The canonical isomorphism `F.leftDerived 0 ≅ F` when `F` is right exact
(i.e. preserves finite colimits). -/
@[simps! hom]
/--
Definition of `leftDerivedZeroIsoSelf` / `leftDerivedZeroIsoSelf` 的定义

English:
definition leftDerivedZeroIsoSelf
  signature: : F.leftDerived 0 ≅ F
  body: (asIso F.fromLeftDerivedZero)

@[reassoc (attr := simp)]

中文:
定义 leftDerivedZeroIsoSelf
  签名: : F.leftDerived 0 ≅ F
  定义体: (asIso F.fromLeftDerivedZero)

@[reassoc (attr := simp)]

Depends on / 依赖: F.fromLeftDerivedZero, fromLeftDerivedZero
-/
noncomputable def leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F :=
  (asIso F.fromLeftDerivedZero)

@[reassoc (attr := simp)]
/--
lemma `leftDerivedZeroIsoSelf_hom_inv_id` / 引理 `leftDerivedZeroIsoSelf_hom_inv_id`

English:
lemma leftDerivedZeroIsoSelf_hom_inv_id
  proof: F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 leftDerivedZeroIsoSelf_hom_inv_id
  证明: F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: F.leftDerivedZeroIsoSelf.hom_inv_id, hom_inv_id, leftDerivedZeroIsoSelf
-/
lemma leftDerivedZeroIsoSelf_hom_inv_id :
    F.fromLeftDerivedZero ≫ F.leftDerivedZeroIsoSelf.inv = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `leftDerivedZeroIsoSelf_inv_hom_id` / 引理 `leftDerivedZeroIsoSelf_inv_hom_id`

English:
lemma leftDerivedZeroIsoSelf_inv_hom_id
  proof: F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 leftDerivedZeroIsoSelf_inv_hom_id
  证明: F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: F.leftDerivedZeroIsoSelf.inv_hom_id, inv_hom_id, leftDerivedZeroIsoSelf
-/
lemma leftDerivedZeroIsoSelf_inv_hom_id :
    F.leftDerivedZeroIsoSelf.inv ≫ F.fromLeftDerivedZero = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `leftDerivedZeroIsoSelf_hom_inv_id_app` / 引理 `leftDerivedZeroIsoSelf_hom_inv_id_app`

English:
lemma leftDerivedZeroIsoSelf_hom_inv_id_app
  given: (X : C)
  proof: F.leftDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]

中文:
引理 leftDerivedZeroIsoSelf_hom_inv_id_app
  条件: (X : C)
  证明: F.leftDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]

Depends on / 依赖: F.leftDerivedZeroIsoSelf.hom_inv_id_app, hom_inv_id_app, leftDerivedZeroIsoSelf
-/
lemma leftDerivedZeroIsoSelf_hom_inv_id_app (X : C) :
    F.fromLeftDerivedZero.app X ≫ F.leftDerivedZeroIsoSelf.inv.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.hom_inv_id_app X

@[reassoc (attr := simp)]
/--
lemma `leftDerivedZeroIsoSelf_inv_hom_id_app` / 引理 `leftDerivedZeroIsoSelf_inv_hom_id_app`

English:
lemma leftDerivedZeroIsoSelf_inv_hom_id_app
  given: (X : C)
  proof: F.leftDerivedZeroIsoSelf.inv_hom_id_app X

中文:
引理 leftDerivedZeroIsoSelf_inv_hom_id_app
  条件: (X : C)
  证明: F.leftDerivedZeroIsoSelf.inv_hom_id_app X

Depends on / 依赖: F.leftDerivedZeroIsoSelf.inv_hom_id_app, inv_hom_id_app, leftDerivedZeroIsoSelf
-/
lemma leftDerivedZeroIsoSelf_inv_hom_id_app (X : C) :
    F.leftDerivedZeroIsoSelf.inv.app X ≫ F.fromLeftDerivedZero.app X = 𝟙 _ :=
  F.leftDerivedZeroIsoSelf.inv_hom_id_app X

end Functor

end

end CategoryTheory
