/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Mathlib/Algebra/Homology/Localization.lean` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the file
`HomotopyCategory.Acyclic`, it was shown that this class of quasiisomorphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`)
using the localization theorem for triangulated categories which was obtained
in the file `Mathlib/CategoryTheory/Localization/Triangulated.lean`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
  of cochain complexes (done), and compare the associated connecting homomorphism
  with the one defined in `Algebra.Homology.HomologySequence`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

@[expose] public noncomputable section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

/--
Definition of `HasDerivedCategory` / `HasDerivedCategory` 的定义

English:
abbreviation HasDerivedCategory
  body: MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up Int))

中文:
缩写 HasDerivedCategory
  定义体: MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up Int))

Depends on / 依赖: HasLocalization, MorphismProperty, MorphismProperty.HasLocalization
-/
abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up Int))

/-- The derived category obtained using the constructed localized category of cochain complexes
with respect to quasi-isomorphisms. This should be used only while proving statements
which do not involve the derived category. -/
@[instance_reducible]
/--
Definition of `HasDerivedCategory.standard` / `HasDerivedCategory.standard` 的定义

English:
definition HasDerivedCategory.standard
  signature: : HasDerivedCategory.{max u v} C
  body: MorphismProperty.HasLocalization.standard _

中文:
定义 HasDerivedCategory.standard
  签名: : HasDerivedCategory.{最大值 u v} C
  定义体: MorphismProperty.HasLocalization.standard _

Depends on / 依赖: HasLocalization, MorphismProperty, MorphismProperty.HasLocalization.standard, standard
-/
def HasDerivedCategory.standard : HasDerivedCategory.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w} C]

/--
Definition of `DerivedCategory` / `DerivedCategory` 的定义

English:
definition DerivedCategory
  signature: : Type (max u v)
  body: HomologicalComplexUpToQuasiIso C (ComplexShape.up Int)
deriving Category

中文:
定义 导出范畴
  签名: : 类型 (最大值 u v)
  定义体: HomologicalComplexUpToQuasiIso C (ComplexShape.up Int)
deriving Category

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplexUpToQuasiIso
-/
def DerivedCategory : Type (max u v) := HomologicalComplexUpToQuasiIso C (ComplexShape.up Int)
deriving Category

namespace DerivedCategory

variable {C}

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: : CochainComplex C Int ⥤ DerivedCategory C
  body: HomologicalComplexUpToQuasiIso.Q

中文:
定义 Q
  签名: : 上链复形 C 整数 ⥤ 导出范畴 C
  定义体: HomologicalComplexUpToQuasiIso.Q

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q
-/
def Q : CochainComplex C Int ⥤ DerivedCategory C := HomologicalComplexUpToQuasiIso.Q

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Q (C := C)).IsLocalization
  body: by
  dsimp only [Q, DerivedCategory]
  infer_instance

中文:
实例 :
  签名: (Q (C := C)).是Localization
  定义体: by
  dsimp only [Q, DerivedCategory]
  infer_instance

Depends on / 依赖: IsLocalization
-/
instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up Int)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance

instance {K L : CochainComplex C Int} (f : K ⟶ L) [QuasiIso f] :
    IsIso (Q.map f) :=
  Localization.inverts Q (HomologicalComplex.quasiIso C (ComplexShape.up Int)) _
    (inferInstanceAs (QuasiIso f))

/--
Definition of `Qh` / `Qh` 的定义

English:
definition Qh
  signature: : HomotopyCategory C (ComplexShape.up Int) ⥤ DerivedCategory C
  body: HomologicalComplexUpToQuasiIso.Qh

中文:
定义 Qh
  签名: : HomotopyCategory C (余mplexShape.up 整数) ⥤ 导出范畴 C
  定义体: HomologicalComplexUpToQuasiIso.Qh

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Qh
-/
def Qh : HomotopyCategory C (ComplexShape.up Int) ⥤ DerivedCategory C :=
  HomologicalComplexUpToQuasiIso.Qh

variable (C) in
/--
Definition of `quotientCompQhIso` / `quotientCompQhIso` 的定义

English:
definition quotientCompQhIso
  signature: : HomotopyCategory.quotient C (ComplexShape.up Int) ⋙ Qh ≅ Q
  body: HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up Int)

#adaptation_note /-- Prior to nightly-2026-05-07, the LHS of these statements was guarded with
`dsimp%`; it now reports `made no progress`, so we write the (already-reduced) form directly. -/
@[reassoc (attr := simp)]

中文:
定义 quotientCompQhIso
  签名: : HomotopyCategory.quotient C (余mplexShape.up 整数) ⋙ Qh ≅ Q
  定义体: HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up Int)

#adaptation_note /-- Prior to nightly-2026-05-07, the LHS of these statements was guarded with
`dsimp%`; it now reports `made no progress`, so we write the (already-reduced) form directly. -/
@[reassoc (attr := simp)]

Depends on / 依赖: ComplexShape, ComplexShape.up, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso, quotientCompQhIso
-/
def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up Int) ⋙ Qh ≅ Q :=
  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up Int)

#adaptation_note /-- Prior to nightly-2026-05-07, the LHS of these statements was guarded with
`dsimp%`; it now reports `made no progress`, so we write the (already-reduced) form directly. -/
@[reassoc (attr := simp)]
/--
lemma `quotientCompQhIso_hom_naturality` / 引理 `quotientCompQhIso_hom_naturality`

English:
lemma quotientCompQhIso_hom_naturality
  given: {K L : CochainComplex C Int} (f : K ⟶ L)
  proof: (quotientCompQhIso C).hom.naturality f

@[reassoc]

中文:
引理 quotientCompQhIso_hom_naturality
  条件: {K L : 上链复形 C 整数} (f : K ⟶ L)
  证明: (quotientCompQhIso C).hom.naturality f

@[reassoc]

Depends on / 依赖: hom.naturality, naturality, quotientCompQhIso
-/
lemma quotientCompQhIso_hom_naturality {K L : CochainComplex C Int} (f : K ⟶ L) :
    Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ (quotientCompQhIso C).hom.app L =
      (quotientCompQhIso C).hom.app K ≫ Q.map f :=
  (quotientCompQhIso C).hom.naturality f

@[reassoc]
/--
lemma `quotientCompQhIso_inv_naturality` / 引理 `quotientCompQhIso_inv_naturality`

English:
lemma quotientCompQhIso_inv_naturality
  given: {K L : CochainComplex C Int} (f : K ⟶ L)
  proof: (quotientCompQhIso C).inv.naturality f

中文:
引理 quotientCompQhIso_inv_naturality
  条件: {K L : 上链复形 C 整数} (f : K ⟶ L)
  证明: (quotientCompQhIso C).inv.naturality f

Depends on / 依赖: inv.naturality, naturality, quotientCompQhIso
-/
lemma quotientCompQhIso_inv_naturality {K L : CochainComplex C Int} (f : K ⟶ L) :
    Q.map f ≫ (quotientCompQhIso C).inv.app L =
      (quotientCompQhIso C).inv.app K ≫ Qh.map ((HomotopyCategory.quotient _ _).map f) :=
  (quotientCompQhIso C).inv.naturality f

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up Int))
  body: by
  dsimp [Qh, DerivedCategory]
  infer_instance

中文:
实例 :
  签名: Qh.是Localization (HomotopyCategory.quasiIso C (余mplexShape.up 整数))
  定义体: by
  dsimp [Qh, DerivedCategory]
  infer_instance

Depends on / 依赖: DerivedCategory, infer_instance
-/
instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up Int)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW
  body: by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

中文:
实例 :
  签名: Qh.是Localization (HomotopyCategory.subcategoryAcyclic C).trW
  定义体: by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, infer_instance, quasiIso_eq_trW_subcategoryAcyclic
-/
instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW := by
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (DerivedCategory C)
  body: Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: 预加性 (导出范畴 C)
  定义体: Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: HomotopyCategory, HomotopyCategory.subcategoryAcyclic, Localization, Localization.preadditive, preadditive, subcategoryAcyclic
-/
instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).Additive
  body: Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: (Qh (C := C)).加性
  定义体: Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: Additive
-/
instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Q (C := C)).Additive
  body: Functor.additive_of_iso (quotientCompQhIso C)

中文:
实例 :
  签名: (Q (C := C)).加性
  定义体: Functor.additive_of_iso (quotientCompQhIso C)

Depends on / 依赖: Additive
-/
instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject (DerivedCategory C)
  body: Q.hasZeroObject_of_additive

中文:
实例 :
  签名: 有ZeroObject (导出范畴 C)
  定义体: Q.hasZeroObject_of_additive

Depends on / 依赖: Q.hasZeroObject_of_additive, hasZeroObject_of_additive
-/
instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (DerivedCategory C) Int
  body: HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

中文:
实例 :
  签名: 有Shift (导出范畴 C) 整数
  定义体: HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

Depends on / 依赖: HasShift, HasShift.localized, HomotopyCategory, HomotopyCategory.subcategoryAcyclic, localized, subcategoryAcyclic
-/
instance : HasShift (DerivedCategory C) Int :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).CommShift Int
  body: Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

中文:
实例 :
  签名: (Qh (C := C)).交换Shift 整数
  定义体: Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

Depends on / 依赖: CommShift
-/
instance : (Qh (C := C)).CommShift Int :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Q (C := C)).CommShift Int
  body: Functor.CommShift.ofIso (quotientCompQhIso C) Int

中文:
实例 :
  签名: (Q (C := C)).交换Shift 整数
  定义体: Functor.CommShift.ofIso (quotientCompQhIso C) Int

Depends on / 依赖: CommShift
-/
instance : (Q (C := C)).CommShift Int :=
  Functor.CommShift.ofIso (quotientCompQhIso C) Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatTrans.CommShift (quotientCompQhIso C).hom Int
  body: Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) Int

中文:
实例 :
  签名: 自然变换.交换Shift (quotientCompQhIso C).hom 整数
  定义体: Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) Int

Depends on / 依赖: CommShift, Functor, Functor.CommShift.ofIso_compatibility, ofIso_compatibility, quotientCompQhIso
-/
instance : NatTrans.CommShift (quotientCompQhIso C).hom Int :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) Int

instance (n : Int) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pretriangulated (DerivedCategory C)
  body: Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: 预三角 (导出范畴 C)
  定义体: Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: HomotopyCategory, HomotopyCategory.subcategoryAcyclic, Localization, Triangulated, Triangulated.Localization.pretriangulated, pretriangulated, subcategoryAcyclic
-/
instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).IsTriangulated
  body: Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: (Qh (C := C)).是三角
  定义体: Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: IsTriangulated
-/
instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTriangulated (DerivedCategory C)
  body: Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: 是三角 (导出范畴 C)
  定义体: Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: HomotopyCategory, HomotopyCategory.subcategoryAcyclic, Localization, Triangulated, Triangulated.Localization.isTriangulated, isTriangulated, subcategoryAcyclic
-/
instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).mapArrow.EssSurj
  body: Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW

中文:
实例 :
  签名: (Qh (C := C)).mapArrow.本质满射
  定义体: Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW

Depends on / 依赖: EssSurj, mapArrow, mapArrow.EssSurj
-/
instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh : _ ⥤ DerivedCategory C).EssSurj
  body: Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

中文:
实例 :
  签名: (Qh : _ ⥤ 导出范畴 C).本质满射
  定义体: Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso, Localization, Localization.essSurj, essSurj, quasiIso
-/
instance : (Qh : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Q : _ ⥤ DerivedCategory C).EssSurj
  body: Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

中文:
实例 :
  签名: (Q : _ ⥤ 导出范畴 C).本质满射
  定义体: Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, Localization, Localization.essSurj, essSurj, quasiIso
-/
instance : (Q : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

/--
lemma `mem_distTriang_iff` / 引理 `mem_distTriang_iff`

English:
lemma mem_distTriang_iff
  given: (T : Triangle (DerivedCategory C))
  proof: by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

中文:
引理 mem_distTriang_iff
  条件: (T : Triangle (导出范畴 C))
  证明: by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Functor, Functor.mapTriangleCompIso, Functor.mapTriangleIso, HomotopyCategory, HomotopyCategory.quotient, Iso.refl, Qh.mapTriangle.mapIso, Qh.map_distinguished, isomorphic_distinguished, mapIso, mapTriangle, mapTriangleCompIso, mapTriangleIso, map_distinguished, quotient, quotientCompQhIso, symm.app
-/
lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T in distTriang (DerivedCategory C)) ↔ exists (X Y : CochainComplex C Int) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

section

open CochainComplex

variable {K L : CochainComplex C Int} (φ : K ⟶ L)

/--
lemma `mappingCone_triangle_distinguished` / 引理 `mappingCone_triangle_distinguished`

English:
lemma mappingCone_triangle_distinguished
  proof: by
  rw [mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

中文:
引理 mappingCone_triangle_distinguished
  证明: by
  rw [mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl, mem_distTriang_iff
-/
lemma mappingCone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle φ) in distTriang _ := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

/--
lemma `mappingCocone_triangle_distinguished` / 引理 `mappingCocone_triangle_distinguished`

English:
lemma mappingCocone_triangle_distinguished
  proof: by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

中文:
引理 mappingCocone_triangle_distinguished
  证明: by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

Depends on / 依赖: DerivedCategory, DerivedCategory.Q.mapTriangle.mapIso, DerivedCategory.Q.mapTriangleRotateIso.app, isomorphic_distinguished, mapIso, mapTriangle, mapTriangleRotateIso, mappingCocone, mappingCocone.rotateTriangleIso, mappingCone_triangle_distinguished, rotateTriangleIso, rotate_distinguished_triangle
-/
lemma mappingCocone_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle φ) in distTriang _ := by
  rw [rotate_distinguished_triangle]
  exact isomorphic_distinguished _ (mappingCone_triangle_distinguished φ) _
    (DerivedCategory.Q.mapTriangleRotateIso.app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso φ))

end

variable (C)

/--
Definition of `singleFunctors` / `singleFunctors` 的定义

English:
definition singleFunctors
  signature: : SingleFunctors C (DerivedCategory C) Int
  body: (HomotopyCategory.singleFunctors C).postcomp Qh

中文:
定义 singleFunctors
  签名: : SingleFunctors C (导出范畴 C) 整数
  定义体: (HomotopyCategory.singleFunctors C).postcomp Qh

Depends on / 依赖: HomotopyCategory, HomotopyCategory.singleFunctors, postcomp, singleFunctors
-/
def singleFunctors : SingleFunctors C (DerivedCategory C) Int :=
  (HomotopyCategory.singleFunctors C).postcomp Qh

/--
Definition of `singleFunctor` / `singleFunctor` 的定义

English:
abbreviation singleFunctor
  signature: (n : Int)
  body: (singleFunctors C).functor n

中文:
缩写 singleFunctor
  签名: (n : 整数)
  定义体: (singleFunctors C).functor n

Depends on / 依赖: functor, singleFunctors
-/
abbrev singleFunctor (n : Int) := (singleFunctors C).functor n

set_option backward.defeqAttrib.useBackward true in
instance (n : Int) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQhIso`.
/--
theorem `Qh_obj_singleFunctors_obj` / 定理 `Qh_obj_singleFunctors_obj`

English:
theorem Qh_obj_singleFunctors_obj
  given: (n : Int) (X : C)
  proof: rfl

中文:
定理 Qh_obj_singleFunctors_obj
  条件: (n : 整数) (X : C)
  证明: rfl
-/
@[simp] theorem Qh_obj_singleFunctors_obj (n : Int) (X : C) :
    Qh.obj (((HomotopyCategory.singleFunctors C).functor n).obj X) = (singleFunctor C n).obj X :=
  rfl

/--
theorem `Q_obj_single_obj` / 定理 `Q_obj_single_obj`

English:
theorem Q_obj_single_obj
  given: (n : Int) (X : C)
  proof: rfl

中文:
定理 Q_obj_single_obj
  条件: (n : 整数) (X : C)
  证明: rfl
-/
@[simp] theorem Q_obj_single_obj (n : Int) (X : C) :
    Q.obj ((HomologicalComplex.single C _ n).obj X) = (singleFunctor C n).obj X :=
  rfl

/--
Definition of `singleFunctorsPostcompQhIso` / `singleFunctorsPostcompQhIso` 的定义

English:
definition singleFunctorsPostcompQhIso
  signature: :
  body: Iso.refl _

中文:
定义 singleFunctorsPostcompQhIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def singleFunctorsPostcompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh :=
  Iso.refl _

/--
Definition of `singleFunctorsPostcompQIso` / `singleFunctorsPostcompQIso` 的定义

English:
definition singleFunctorsPostcompQIso
  signature: :
  body: (SingleFunctors.postcompFunctor C Int (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

中文:
定义 singleFunctorsPostcompQIso
  签名: :
  定义体: (SingleFunctors.postcompFunctor C Int (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

Depends on / 依赖: Additive, CochainComplex, CochainComplex.singleFunctors, DerivedCategory, HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.singleFunctorsPostcompQuotientIso, SingleFunctors, SingleFunctors.postcompFunctor, SingleFunctors.postcompIsoOfIso, mapIso, postcompFunctor, postcompIsoOfIso, postcompPostcompIso, quotient, quotientCompQhIso, singleFunctors, singleFunctorsPostcompQuotientIso
-/
def singleFunctorsPostcompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q :=
  (SingleFunctors.postcompFunctor C Int (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `singleFunctorsPostcompQIso_hom_hom` / 引理 `singleFunctorsPostcompQIso_hom_hom`

English:
lemma singleFunctorsPostcompQIso_hom_hom
  given: (n : Int)
  proof: by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]
  erw [Category.id_comp]
  rfl

中文:
引理 singleFunctorsPostcompQIso_hom_hom
  条件: (n : 整数)
  证明: by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]
  erw [Category.id_comp]
  rfl

Depends on / 依赖: Category, Category.id_comp, CategoryTheory, CategoryTheory.Functor.map_id, Functor, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso, HomotopyCategory, HomotopyCategory.singleFunctorsPostcompQuotientIso, id_comp, map_id, quotientCompQhIso, singleFunctorsPostcompQIso, singleFunctorsPostcompQuotientIso
-/
lemma singleFunctorsPostcompQIso_hom_hom (n : Int) :
    (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id]; rw [Category.id_comp]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `singleFunctorsPostcompQIso_inv_hom` / 引理 `singleFunctorsPostcompQIso_inv_hom`

English:
lemma singleFunctorsPostcompQIso_inv_hom
  given: (n : Int)
  proof: by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

中文:
引理 singleFunctorsPostcompQIso_inv_hom
  条件: (n : 整数)
  证明: by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

Depends on / 依赖: HomotopyCategory, HomotopyCategory.singleFunctorsPostcompQuotientIso, singleFunctorsPostcompQIso, singleFunctorsPostcompQuotientIso
-/
lemma singleFunctorsPostcompQIso_inv_hom (n : Int) :
    (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

/--
Definition of `singleFunctorIsoCompQ` / `singleFunctorIsoCompQ` 的定义

English:
definition singleFunctorIsoCompQ
  signature: (n : Int)
  body: Iso.refl _

中文:
定义 singleFunctorIsoCompQ
  签名: (n : 整数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def singleFunctorIsoCompQ (n : Int) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _

/--
lemma `isIso_Q_map_iff_quasiIso` / 引理 `isIso_Q_map_iff_quasiIso`

English:
lemma isIso_Q_map_iff_quasiIso
  given: {K L : CochainComplex C Int} (φ : K ⟶ L)
  proof: by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

中文:
引理 isIso_Q_map_iff_quasiIso
  条件: {K L : 上链复形 C 整数} (φ : K ⟶ L)
  证明: by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso, isIso_Q_map_iff_mem_quasiIso
-/
lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C Int} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

/--
lemma `Q_map_eq_of_homotopy` / 引理 `Q_map_eq_of_homotopy`

English:
lemma Q_map_eq_of_homotopy
  given: {K L : CochainComplex C Int} {f g : K ⟶ L} (h : Homotopy f g)
  proof: HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

中文:
引理 Q_map_eq_of_homotopy
  条件: {K L : 上链复形 C 整数} {f g : K ⟶ L} (h : 同伦 f g)
  证明: HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy, Q_map_eq_of_homotopy
-/
lemma Q_map_eq_of_homotopy {K L : CochainComplex C Int} {f g : K ⟶ L} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

end DerivedCategory
