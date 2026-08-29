/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The bounded below derived category

Let `C` be an abelian category. In this file, we show that
the bounded below derived category `DerivedCategory.Plus C` (defined
as a full subcategory of `DerivedCategory C`) is the localization
of the bounded below homotopy category `HomotopyCategory.Plus C`
with respect to quasi-isomorphisms.

-/

@[expose] public section

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category* C] [Abelian C]

namespace HomotopyCategory.Plus

variable (C)

/--
Definition of `subcategoryAcyclic` / `subcategoryAcyclic` 的定义

English:
abbreviation subcategoryAcyclic
  signature: :
  body: (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

中文:
缩写 subcategoryAcyclic
  签名: :
  定义体: (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.subcategoryAcyclic, inverseImage, subcategoryAcyclic
-/
abbrev subcategoryAcyclic :
    ObjectProperty (HomotopyCategory.Plus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quasiIso_eq_subcategoryAcyclic_trW` / 引理 `quasiIso_eq_subcategoryAcyclic_trW`

English:
lemma quasiIso_eq_subcategoryAcyclic_trW
  proof: by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Plus.ι C).map_distinguished _ mem)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]

中文:
引理 quasiIso_eq_subcategoryAcyclic_trW
  证明: by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Plus.ι C).map_distinguished _ mem)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]

Depends on / 依赖: CategoryTheory, CategoryTheory.Pretriangulated.distinguished_cocone_triangle, HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.subcategoryAcyclic, Pretriangulated, distinguished_cocone_triangle, map_distinguished, quasiIso_eq_trW_subcategoryAcyclic, subcategoryAcyclic, trW_iff_of_distinguished
-/
lemma quasiIso_eq_subcategoryAcyclic_trW :
    HomotopyCategory.Plus.quasiIso C = (subcategoryAcyclic C).trW := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    ((HomotopyCategory.Plus.ι C).map_distinguished _ mem)
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at this
  rwa [dsimp% (subcategoryAcyclic C).trW_iff_of_distinguished _ mem]

end HomotopyCategory.Plus

namespace DerivedCategory

open TStructure

variable [HasDerivedCategory C]

namespace Plus

/--
Definition of `Qh` / `Qh` 的定义

English:
definition Qh
  signature: : HomotopyCategory.Plus C ⥤ Plus C
  body: t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hK
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app K) n⟩)

中文:
定义 Qh
  签名: : HomotopyCategory.Plus C ⥤ Plus C
  定义体: t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hK
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app K) n⟩)

Depends on / 依赖: DerivedCategory, DerivedCategory.Qh, HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.plus_quotient_obj_iff, HomotopyCategory.quotient_obj_surjective, isGE_of_iso, plus_quotient_obj_iff, quotientCompQhIso, quotient_obj_surjective, symm.app, t.isGE_of_iso, t.plus.lift
-/
noncomputable def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨K, hK⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hK
    exact ⟨n, t.isGE_of_iso ((quotientCompQhIso C).symm.app K) n⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh : _ ⥤ Plus C).CommShift Int
  body: by
  dsimp only [Qh]
  infer_instance

中文:
实例 :
  签名: (Qh : _ ⥤ Plus C).CommShift 整数
  定义体: by
  dsimp only [Qh]
  infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance : (Qh : _ ⥤ Plus C).CommShift Int := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh : _ ⥤ Plus C).IsTriangulated
  body: by
  dsimp only [Qh]
  infer_instance

中文:
实例 :
  签名: (Qh : _ ⥤ Plus C).IsTriangulated
  定义体: by
  dsimp only [Qh]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Qh_map_bijective_of_isKInjective` / 引理 `Qh_map_bijective_of_isKInjective`

English:
lemma Qh_map_bijective_of_isKInjective
  statement: (K L : HomotopyCategory.Plus C)
  proof: by
  have := CochainComplex.IsKInjective.Qh_map_bijective K.1 L.1.as
  rw [← Function.Bijective.of_comp_iff _
    ((HomotopyCategory.Plus.fullyFaithfulι C).map_bijective _ _)] at this
  rwa [← Function.Bijective.of_comp_iff' (t.plus.fullyFaithfulι.map_bijective _ _)]

中文:
引理 Qh_map_bijective_of_isKInjective
  结论: (K L : HomotopyCategory.Plus C)
  证明: by
  have := CochainComplex.IsKInjective.Qh_map_bijective K.1 L.1.as
  rw [← Function.Bijective.of_comp_iff _
    ((HomotopyCategory.Plus.fullyFaithfulι C).map_bijective _ _)] at this
  rwa [← Function.Bijective.of_comp_iff' (t.plus.fullyFaithfulι.map_bijective _ _)]

Depends on / 依赖: Bijective, CochainComplex, CochainComplex.IsKInjective.Qh_map_bijective, Function, Function.Bijective.of_comp_iff, HomotopyCategory, HomotopyCategory.Plus.fullyFaithful, IsKInjective, Qh_map_bijective, map_bijective, of_comp_iff, t.plus.fullyFaithful
-/
lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) -> _) := by
  have := CochainComplex.IsKInjective.Qh_map_bijective K.1 L.1.as
  rw [← Function.Bijective.of_comp_iff _
    ((HomotopyCategory.Plus.fullyFaithfulι C).map_bijective _ _)] at this
  rwa [← Function.Bijective.of_comp_iff' (t.plus.fullyFaithfulι.map_bijective _ _)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.plus C).IsVerdierRightLocalizing
  body: by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hL
    obtain ⟨n, hn⟩ := hL
    obtain ⟨φ, rfl⟩ := (HomotopyCateg

中文:
实例 :
  签名: (HomotopyCategory.plus C).IsVerdierRightLocalizing
  定义体: by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hL
    obtain ⟨n, hn⟩ := hL
    obtain ⟨φ, rfl⟩ := (HomotopyCateg

Depends on / 依赖: CochainComplex, HomotopyCategory, HomotopyCategory.plus_quotient_obj_iff, HomotopyCategory.quotient, HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic, HomotopyCategory.quotient_obj_surjective, K.truncGE, map_surjective, plus_quotient_obj_iff, quotient, quotient_obj_mem_subcategoryAcyclic_iff_acyclic, quotient_obj_surjective, truncGE
-/
instance : (HomotopyCategory.plus C).IsVerdierRightLocalizing
    (HomotopyCategory.subcategoryAcyclic C) where
  fac {K L} φ hK hL := by
    obtain ⟨K : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L : CochainComplex _ _, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    simp only [HomotopyCategory.plus_quotient_obj_iff] at hL
    obtain ⟨n, hn⟩ := hL
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    refine ⟨(HomotopyCategory.quotient _ _).obj (K.truncGE n),
      (HomotopyCategory.quotient _ _).map (K.πTruncGE n),
      (HomotopyCategory.quotient _ _).map (CochainComplex.truncGEMap φ n ≫ inv (L.πTruncGE n)),
      ?_, ?_, by simp [← Functor.map_comp]⟩
    · simp only [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hK.truncGE _

variable (C)

/--
Definition of `QhCompιIsoιCompQh` / `QhCompιIsoιCompQh` 的定义

English:
definition QhCompιIsoιCompQh
  signature: :
  body: Iso.refl _

中文:
定义 QhCompιIsoιCompQh
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def QhCompιIsoιCompQh :
    Qh ⋙ Plus.ι ≅ HomotopyCategory.Plus.ι C ⋙ DerivedCategory.Qh := Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).EssSurj
  body: by
    intro ⟨X, n, K, e, h⟩
    refine ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up Int)).obj K, ?_⟩,
      ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
    simp only [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨n, h⟩

中文:
实例 :
  签名: (Qh (C := C)).EssSurj
  定义体: by
    intro ⟨X, n, K, e, h⟩
    refine ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up Int)).obj K, ?_⟩,
      ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
    simp only [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨n, h⟩

Depends on / 依赖: EssSurj
-/
instance : (Qh (C := C)).EssSurj where
  mem_essImage := by
    intro ⟨X, n, K, e, h⟩
    refine ⟨⟨(HomotopyCategory.quotient C (ComplexShape.up Int)).obj K, ?_⟩,
      ⟨Plus.ι.preimageIso ((quotientCompQhIso C).app _ ≪≫ e.symm)⟩⟩
    simp only [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨n, h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).trW
  body: ((HomotopyCategory.plus C).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic C)).isLocalization_of_isLocalizedFullyFaithful
      (QhCompιIsoιCompQh C).symm

中文:
实例 :
  签名: Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).trW
  定义体: ((HomotopyCategory.plus C).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic C)).isLocalization_of_isLocalizedFullyFaithful
      (QhCompιIsoιCompQh C).symm

Depends on / 依赖: HomotopyCategory, HomotopyCategory.plus, HomotopyCategory.subcategoryAcyclic, isLocalization_of_isLocalizedFullyFaithful, subcategoryAcyclic, triangulatedLocalizerMorphism
-/
instance : Qh.IsLocalization (HomotopyCategory.Plus.subcategoryAcyclic C).trW :=
  ((HomotopyCategory.plus C).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic C)).isLocalization_of_isLocalizedFullyFaithful
      (QhCompιIsoιCompQh C).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C)
  body: by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

中文:
实例 :
  签名: Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C)
  定义体: by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

Depends on / 依赖: HomotopyCategory, HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW, infer_instance, quasiIso_eq_subcategoryAcyclic_trW
-/
instance : Qh.IsLocalization (HomotopyCategory.Plus.quasiIso C) := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

/--
Definition of `singleFunctors` / `singleFunctors` 的定义

English:
definition singleFunctors
  signature: : SingleFunctors C (Plus C) Int
  body: SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

中文:
定义 singleFunctors
  签名: : SingleFunctors C (Plus C) 整数
  定义体: SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

Depends on / 依赖: DerivedCategory, DerivedCategory.singleFunctor, DerivedCategory.singleFunctors, Iso.refl, SingleFunctors, SingleFunctors.lift, singleFunctor, singleFunctors, t.plus.lift
-/
noncomputable def singleFunctors : SingleFunctors C (Plus C) Int :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n)
      (fun _ => ⟨n, inferInstance⟩))
      (fun _ => Iso.refl _)

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
noncomputable abbrev singleFunctor (n : Int) : C ⥤ Plus C := (singleFunctors C).functor n

/--
Definition of `singleFunctorιIso` / `singleFunctorιIso` 的定义

English:
definition singleFunctorιIso
  signature: (n : Int)
  body: Iso.refl _

中文:
定义 singleFunctorιIso
  签名: (n : 整数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def singleFunctorιIso (n : Int) :
    singleFunctor C n ⋙ Plus.ι ≅ DerivedCategory.singleFunctor C n :=
  Iso.refl _

instance (n : Int) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: (n : Int)
  body: Plus.ι ⋙ DerivedCategory.homologyFunctor C n
deriving Functor.IsHomological

中文:
定义 homologyFunctor
  签名: (n : 整数)
  定义体: Plus.ι ⋙ DerivedCategory.homologyFunctor C n
deriving Functor.IsHomological

Depends on / 依赖: DerivedCategory, DerivedCategory.homologyFunctor, homologyFunctor
-/
noncomputable def homologyFunctor (n : Int) : Plus C ⥤ C :=
  Plus.ι ⋙ DerivedCategory.homologyFunctor C n
deriving Functor.IsHomological

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Qh (C := C)).mapArrow.EssSurj
  body: Localization.essSurj_mapArrow _
    (HomotopyCategory.Plus.subcategoryAcyclic C).trW

中文:
实例 :
  签名: (Qh (C := C)).mapArrow.EssSurj
  定义体: Localization.essSurj_mapArrow _
    (HomotopyCategory.Plus.subcategoryAcyclic C).trW

Depends on / 依赖: EssSurj, mapArrow, mapArrow.EssSurj
-/
instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _
    (HomotopyCategory.Plus.subcategoryAcyclic C).trW

variable {C}

/--
Definition of `TStructure.t` / `TStructure.t` 的定义

English:
abbreviation TStructure.t
  signature: : TStructure (DerivedCategory.Plus C)
  body: (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

中文:
缩写 TStructure.t
  签名: : TStructure (DerivedCategory.Plus C)
  定义体: (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

Depends on / 依赖: DerivedCategory, DerivedCategory.TStructure.t, TStructure, plus.tStructure, tStructure
-/
noncomputable abbrev TStructure.t : TStructure (DerivedCategory.Plus C) :=
  (DerivedCategory.TStructure.t (C := C)).plus.tStructure DerivedCategory.TStructure.t

/--
Definition of `IsGE` / `IsGE` 的定义

English:
abbreviation IsGE
  signature: (X : Plus C) (n : Int)
  body: Plus.TStructure.t.IsGE X n

中文:
缩写 IsGE
  签名: (X : Plus C) (n : 整数)
  定义体: Plus.TStructure.t.IsGE X n

Depends on / 依赖: Plus.TStructure.t.IsGE, TStructure
-/
abbrev IsGE (X : Plus C) (n : Int) : Prop := Plus.TStructure.t.IsGE X n

/--
Definition of `IsLE` / `IsLE` 的定义

English:
abbreviation IsLE
  signature: (X : Plus C) (n : Int)
  body: Plus.TStructure.t.IsLE X n

中文:
缩写 IsLE
  签名: (X : Plus C) (n : 整数)
  定义体: Plus.TStructure.t.IsLE X n

Depends on / 依赖: Plus.TStructure.t.IsLE, TStructure
-/
abbrev IsLE (X : Plus C) (n : Int) : Prop := Plus.TStructure.t.IsLE X n

/--
lemma `isGE_ι_obj_iff` / 引理 `isGE_ι_obj_iff`

English:
lemma isGE_ι_obj_iff
  given: (X : Plus C) (n : Int)
  proof: by
  constructor
  all_goals exact fun h => ⟨h.1⟩

中文:
引理 isGE_ι_obj_iff
  条件: (X : Plus C) (n : 整数)
  证明: by
  constructor
  all_goals exact fun h => ⟨h.1⟩

Depends on / 依赖: all_goals
-/
lemma isGE_ι_obj_iff (X : Plus C) (n : Int) :
    (ι.obj X).IsGE n ↔ X.IsGE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

/--
lemma `isLE_ι_obj_iff` / 引理 `isLE_ι_obj_iff`

English:
lemma isLE_ι_obj_iff
  given: (X : Plus C) (n : Int)
  proof: by
  constructor
  all_goals exact fun h => ⟨h.1⟩

中文:
引理 isLE_ι_obj_iff
  条件: (X : Plus C) (n : 整数)
  证明: by
  constructor
  all_goals exact fun h => ⟨h.1⟩

Depends on / 依赖: all_goals
-/
lemma isLE_ι_obj_iff (X : Plus C) (n : Int) :
    (ι.obj X).IsLE n ↔ X.IsLE n := by
  constructor
  all_goals exact fun h => ⟨h.1⟩

instance (X : Plus C) (n : Int) [X.IsGE n] : (ι.obj X).IsGE n := by
  rw [isGE_ι_obj_iff]
  infer_instance

instance (X : Plus C) (n : Int) [X.IsLE n] : (ι.obj X).IsLE n := by
  rw [isLE_ι_obj_iff]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence Int
  body: inferInstanceAs ((ι ⋙ DerivedCategory.homologyFunctor C 0).ShiftSequence Int)

中文:
实例 :
  签名: (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence 整数
  定义体: inferInstanceAs ((ι ⋙ DerivedCategory.homologyFunctor C 0).ShiftSequence Int)

Depends on / 依赖: DerivedCategory, DerivedCategory.homologyFunctor, ShiftSequence, homologyFunctor
-/
noncomputable instance : (DerivedCategory.Plus.homologyFunctor C 0).ShiftSequence Int :=
  inferInstanceAs ((ι ⋙ DerivedCategory.homologyFunctor C 0).ShiftSequence Int)

instance (X : C) (n : Int) : ((singleFunctor C n).obj X).IsGE n := by
  rw [← isGE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsGE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

instance (X : C) (n : Int) : ((singleFunctor C n).obj X).IsLE n := by
  rw [← isLE_ι_obj_iff]
  change DerivedCategory.TStructure.t.IsLE ((DerivedCategory.singleFunctor C n).obj X) n
  infer_instance

/--
lemma `isZero_homology_of_isGE` / 引理 `isZero_homology_of_isGE`

English:
lemma isZero_homology_of_isGE
  proof: (ι.obj X).isZero_of_isGE n i hi

中文:
引理 isZero_homology_of_isGE
  证明: (ι.obj X).isZero_of_isGE n i hi

Depends on / 依赖: isZero_of_isGE
-/
lemma isZero_homology_of_isGE
    (X : Plus C) (n : Int) [X.IsGE n] (i : Int) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isGE n i hi

/--
lemma `isZero_homology_of_isLE` / 引理 `isZero_homology_of_isLE`

English:
lemma isZero_homology_of_isLE
  proof: (ι.obj X).isZero_of_isLE n i hi

中文:
引理 isZero_homology_of_isLE
  证明: (ι.obj X).isZero_of_isLE n i hi

Depends on / 依赖: isZero_of_isLE
-/
lemma isZero_homology_of_isLE
    (X : Plus C) (n : Int) [X.IsLE n] (i : Int) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj X) :=
  (ι.obj X).isZero_of_isLE n i hi

/--
lemma `isIso_iff` / 引理 `isIso_iff`

English:
lemma isIso_iff
  given: {X Y : Plus C} (f : X ⟶ Y)
  proof: by
  refine ⟨fun _ _ => inferInstance, fun _ => ?_⟩
  have : IsIso (ι.map f) := by rwa [DerivedCategory.isIso_iff]
  exact isIso_of_fully_faithful ι _

中文:
引理 isIso_iff
  条件: {X Y : Plus C} (f : X ⟶ Y)
  证明: by
  refine ⟨fun _ _ => inferInstance, fun _ => ?_⟩
  have : IsIso (ι.map f) := by rwa [DerivedCategory.isIso_iff]
  exact isIso_of_fully_faithful ι _

Depends on / 依赖: DerivedCategory, DerivedCategory.isIso_iff, isIso_iff, isIso_of_fully_faithful
-/
lemma isIso_iff {X Y : Plus C} (f : X ⟶ Y) :
    IsIso f ↔ forall (n : Int), IsIso ((homologyFunctor C n).map f) := by
  refine ⟨fun _ _ => inferInstance, fun _ => ?_⟩
  have : IsIso (ι.map f) := by rwa [DerivedCategory.isIso_iff]
  exact isIso_of_fully_faithful ι _

/--
Definition of `Q` / `Q` 的定义

English:
definition Q
  signature: : CochainComplex.Plus C ⥤ DerivedCategory.Plus C
  body: HomotopyCategory.Plus.quotient C ⋙ Qh

中文:
定义 Q
  签名: : CochainComplex.Plus C ⥤ DerivedCategory.Plus C
  定义体: HomotopyCategory.Plus.quotient C ⋙ Qh

Depends on / 依赖: HomotopyCategory, HomotopyCategory.Plus.quotient, quotient
-/
noncomputable def Q : CochainComplex.Plus C ⥤ DerivedCategory.Plus C :=
  HomotopyCategory.Plus.quotient C ⋙ Qh

-- TODO: show that `Q` is indeed a localization functor with respect to quasi-isomorphisms

end Plus

end DerivedCategory
