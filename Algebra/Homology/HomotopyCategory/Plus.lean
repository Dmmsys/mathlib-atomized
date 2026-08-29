/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

/-!
# The triangulated subcategory of bounded below cochain complexes up to homotopy

In this file, we introduce the triangulated full subcategory `HomotopyCategory.Plus C`
of `HomotopyCategory C (.up ℤ)` consisting of bounded below cochain complexes.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Pretriangulated HomotopicalAlgebra

variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (A : Type*) [Category* A] [Abelian A]

namespace CochainComplex

open HomologicalComplex

variable {C} [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `plus_cylinder` / 引理 `plus_cylinder`

English:
lemma plus_cylinder
  given: (K : CochainComplex C Int) (hK : CochainComplex.plus C K)
  proof: by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [cylinder]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up Int) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyGE

中文:
引理 plus_cylinder
  条件: (K : 上链复形 C 整数) (hK : 上链复形.plus C K)
  证明: by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [cylinder]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up Int) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyGE

Depends on / 依赖: CochainComplex, CochainComplex.isStrictlyGE_iff, ComplexShape, ComplexShape.up_Rel, HomologicalComplex, HomologicalComplex.eval, IsZero, IsZero.of_iso, K.isZero_of_isStrictlyGE, cylinder, homotopyCofiber, homotopyCofiber.isZero_X, isStrictlyGE_iff, isZero_X, isZero_of_isStrictlyGE, mapBiprod, of_iso, up_Rel
-/
lemma plus_cylinder (K : CochainComplex C Int) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (cylinder K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [cylinder]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj => ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up Int) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyGE n i
  · simp only [ComplexShape.up_Rel] at hj
    exact K.isZero_of_isStrictlyGE n _ (by lia)

/--
lemma `plus_pathObject` / 引理 `plus_pathObject`

English:
lemma plus_pathObject
  given: (K : CochainComplex C Int) (hK : CochainComplex.plus C K)
  proof: by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine pathObject.isZero_X _ _ (K.isZero_of_isStrictlyGE n i)
    (fun j hj => ?_)
  simp only [ComplexShape.up_Rel] at hj
  exact K.isZero_of_isStrictlyGE n j

中文:
引理 plus_pathObject
  条件: (K : 上链复形 C 整数) (hK : 上链复形.plus C K)
  证明: by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine pathObject.isZero_X _ _ (K.isZero_of_isStrictlyGE n i)
    (fun j hj => ?_)
  simp only [ComplexShape.up_Rel] at hj
  exact K.isZero_of_isStrictlyGE n j

Depends on / 依赖: CochainComplex, CochainComplex.isStrictlyGE_iff, ComplexShape, ComplexShape.up_Rel, K.isZero_of_isStrictlyGE, isStrictlyGE_iff, isZero_X, isZero_of_isStrictlyGE, pathObject, pathObject.isZero_X, up_Rel
-/
lemma plus_pathObject (K : CochainComplex C Int) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (pathObject K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine pathObject.isZero_X _ _ (K.isZero_of_isStrictlyGE n i)
    (fun j hj => ?_)
  simp only [ComplexShape.up_Rel] at hj
  exact K.isZero_of_isStrictlyGE n j

/--
lemma `isStrictlyGE_mappingCone` / 引理 `isStrictlyGE_mappingCone`

English:
lemma isStrictlyGE_mappingCone
  statement: {K L : CochainComplex C Int} (f : K ⟶ L)
  proof: by
  rw [isStrictlyGE_iff]
  intro i hi
  simp at hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _, L.isZero_of_isStrictlyGE n₂ _⟩

中文:
引理 isStrictlyGE_mappingCone
  结论: {K L : 上链复形 C 整数} (f : K ⟶ L)
  证明: by
  rw [isStrictlyGE_iff]
  intro i hi
  simp at hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _, L.isZero_of_isStrictlyGE n₂ _⟩

Depends on / 依赖: IsStrictlyGE, K.isZero_of_isStrictlyGE, L.isZero_of_isStrictlyGE, isStrictlyGE_iff, isZero_X_iff, isZero_of_isStrictlyGE, mappingCone, mappingCone.isZero_X_iff
-/
lemma isStrictlyGE_mappingCone {K L : CochainComplex C Int} (f : K ⟶ L)
    (n₁ n₂ n : Int) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (hn₁ : n < n₁ := by lia)
    (hn₂ : n <= n₂ := by lia) :
    (mappingCone f).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  simp at hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _, L.isZero_of_isStrictlyGE n₂ _⟩

/--
Definition of `Plus.precylinder` / `Plus.precylinder` 的定义

English:
abbreviation Plus.precylinder
  signature: (K : Plus C)
  body: K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

中文:
缩写 Plus.precylinder
  签名: (K : Plus C)
  定义体: K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

Depends on / 依赖: K.obj.plus_cylinder, K.obj.precylinder.toFullSubcategory, K.property, plus_cylinder, precylinder, property, toFullSubcategory
-/
noncomputable abbrev Plus.precylinder (K : Plus C) : Precylinder K :=
  K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

/--
Definition of `Plus.prepathObject` / `Plus.prepathObject` 的定义

English:
abbreviation Plus.prepathObject
  signature: (K : Plus C)
  body: K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

中文:
缩写 Plus.prepathObject
  签名: (K : Plus C)
  定义体: K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

Depends on / 依赖: K.obj.plus_pathObject, K.obj.prepathObject.toFullSubcategory, K.property, plus_pathObject, prepathObject, property, toFullSubcategory
-/
noncomputable abbrev Plus.prepathObject (K : Plus C) : PrepathObject K :=
  K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

end CochainComplex

namespace HomotopyCategory

/--
Definition of `plus` / `plus` 的定义

English:
definition plus
  signature: : ObjectProperty (HomotopyCategory C (.up Int))
  body: (CochainComplex.plus C).strictMap (quotient _ _)

中文:
定义 plus
  签名: : ObjectProperty (HomotopyCategory C (.up 整数))
  定义体: (CochainComplex.plus C).strictMap (quotient _ _)

Depends on / 依赖: CochainComplex, CochainComplex.plus, quotient, strictMap
-/
def plus : ObjectProperty (HomotopyCategory C (.up Int)) :=
  (CochainComplex.plus C).strictMap (quotient _ _)

variable {C} in
@[simp]
/--
lemma `plus_quotient_obj_iff` / 引理 `plus_quotient_obj_iff`

English:
lemma plus_quotient_obj_iff
  given: (K : CochainComplex C Int)
  proof: by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [plus, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

中文:
引理 plus_quotient_obj_iff
  条件: (K : 上链复形 C 整数)
  证明: by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [plus, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

Depends on / 依赖: ObjectProperty, ObjectProperty.strictMap_iff, Quotient, Quotient.as, congr_arg, strictMap_iff
-/
lemma plus_quotient_obj_iff (K : CochainComplex C Int) :
    plus C ((quotient _ _).obj K) ↔ CochainComplex.plus C K := by
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  simp only [plus, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : (plus C).ContainsZero where
  body: ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [plus_quotient_obj_iff]
      exact ⟨0, inferInstance⟩⟩

中文:
实例 [有ZeroObject
  签名: C] : (plus C).余ntainsZero where
  定义体: ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [plus_quotient_obj_iff]
      exact ⟨0, inferInstance⟩⟩

Depends on / 依赖: Functor, Functor.map_isZero, HomotopyCategory, HomotopyCategory.quotient, isZero_zero, map_isZero, plus_quotient_obj_iff, quotient
-/
instance [HasZeroObject C] : (plus C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [plus_quotient_obj_iff]
      exact ⟨0, inferInstance⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (plus C).IsStableUnderShift Int
  body: { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_quotient_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff]; rw [shift_quotient_obj]; rw [plus_quotient_obj_iff]
        exact ⟨q - n, K.isStrict

中文:
实例 :
  签名: (plus C).是StableUnderShift 整数
  定义体: { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_quotient_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff]; rw [shift_quotient_obj]; rw [plus_quotient_obj_iff]
        exact ⟨q - n, K.isStrict

Depends on / 依赖: CochainComplex, K.isStrictlyGE_shift, K.quotient_obj_surjective, ObjectProperty, ObjectProperty.prop_shift_iff, isStrictlyGE_shift, le_shift, plus_quotient_obj_iff, prop_shift_iff, quotient_obj_surjective, shift_quotient_obj
-/
instance : (plus C).IsStableUnderShift Int where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_quotient_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff]; rw [shift_quotient_obj]; rw [plus_quotient_obj_iff]
        exact ⟨q - n, K.isStrictlyGE_shift q n (q - n) (by lia)⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] [HasBinaryBiproducts C] :
  body: by
    obtain ⟨n₁, _⟩ : (CochainComplex.plus C) T.obj₁.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨n₂, _⟩ : (CochainComplex.plus C) T.obj₂.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
 

中文:
实例 [有ZeroObject
  签名: C] [有BinaryBiproducts C] :
  定义体: by
    obtain ⟨n₁, _⟩ : (CochainComplex.plus C) T.obj₁.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨n₂, _⟩ : (CochainComplex.plus C) T.obj₂.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
 

Depends on / 依赖: CochainComplex, CochainComplex.isStrictlyGE_mappingCone, CochainComplex.plus, Iso.refl, T.mor, T.obj, Triangle, isStrictlyGE_mappingCone, mapIso, map_surjective, mappingCone_triangleh_distinguished, plus_quotient_obj_iff, quotient
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (plus C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨n₁, _⟩ : (CochainComplex.plus C) T.obj₁.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨n₂, _⟩ : (CochainComplex.plus C) T.obj₂.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [plus_quotient_obj_iff]
      exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _
        (by simp) (by simp)⟩
    · simp [hf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] [HasBinaryBiproducts C] : (plus C).IsTriangulated where
  body: .of_isTriangulatedClosed₃

中文:
实例 [有ZeroObject
  签名: C] [有BinaryBiproducts C] : (plus C).是三角 where
  定义体: .of_isTriangulatedClosed₃
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] : (plus C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/--
Definition of `Plus` / `Plus` 的定义

English:
abbreviation Plus
  body: (plus C).FullSubcategory

中文:
缩写 Plus
  定义体: (plus C).FullSubcategory

Depends on / 依赖: FullSubcategory
-/
abbrev Plus := (plus C).FullSubcategory

namespace Plus

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : Plus C ⥤ HomotopyCategory C (.up Int)
  body: (plus C).ι

中文:
缩写 ι
  签名: : Plus C ⥤ HomotopyCategory C (.up 整数)
  定义体: (plus C).ι
-/
abbrev ι : Plus C ⥤ HomotopyCategory C (.up Int) := (plus C).ι

/--
Definition of `fullyFaithfulι` / `fullyFaithfulι` 的定义

English:
abbreviation fullyFaithfulι
  signature: : (ι C).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
缩写 fullyFaithfulι
  签名: : (ι C).满忠实
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

/--
Definition of `quasiIso` / `quasiIso` 的定义

English:
definition quasiIso
  signature: : MorphismProperty (Plus A)
  body: (HomotopyCategory.quasiIso A _).inverseImage (ι A)
deriving MorphismProperty.IsMultiplicative

中文:
定义 quasiIso
  签名: : MorphismProperty (Plus A)
  定义体: (HomotopyCategory.quasiIso A _).inverseImage (ι A)
deriving MorphismProperty.IsMultiplicative

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quasiIso, inverseImage, quasiIso
-/
def quasiIso : MorphismProperty (Plus A) :=
  (HomotopyCategory.quasiIso A _).inverseImage (ι A)
deriving MorphismProperty.IsMultiplicative

/--
lemma `quasiIso_iff` / 引理 `quasiIso_iff`

English:
lemma quasiIso_iff
  given: {K L : Plus A} (f : K ⟶ L)
  proof: Iff.rfl

中文:
引理 quasiIso_iff
  条件: {K L : Plus A} (f : K ⟶ L)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma quasiIso_iff {K L : Plus A} (f : K ⟶ L) :
    quasiIso A f ↔ (HomotopyCategory.quasiIso A _) f.hom := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso A).IsCompatibleWithShift Int
  body: by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso _ _) f.hom a]
    exact (HomotopyCategory.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

中文:
实例 :
  签名: (quasiIso A).是余mpatibleWithShift 整数
  定义体: by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso _ _) f.hom a]
    exact (HomotopyCategory.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

Depends on / 依赖: Arrow.isoOfNatIso, Arrow.mk, HomotopyCategory, HomotopyCategory.quasiIso, IsCompatibleWithShift, MorphismProperty, MorphismProperty.IsCompatibleWithShift.iff, arrow_mk_iso_iff, commShiftIso, f.hom, isoOfNatIso, quasiIso, quasiIso_iff
-/
instance : (quasiIso A).IsCompatibleWithShift Int where
  condition a := by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso _ _) f.hom a]
    exact (HomotopyCategory.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso A).RespectsIso
  body: by
  dsimp only [quasiIso]
  infer_instance

中文:
实例 :
  签名: (quasiIso A).RespectsIso
  定义体: by
  dsimp only [quasiIso]
  infer_instance

Depends on / 依赖: infer_instance, quasiIso
-/
instance : (quasiIso A).RespectsIso := by
  dsimp only [quasiIso]
  infer_instance

/-- The full and essentially surjective functor
`CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`. -/
@[simps!]
/--
Definition of `quotient` / `quotient` 的定义

English:
definition quotient
  signature: : CochainComplex.Plus C ⥤ Plus C
  body: ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up Int)) (by
      rintro ⟨K, h⟩
      simpa [plus_quotient_obj_iff])

中文:
定义 quotient
  签名: : 上链复形.Plus C ⥤ Plus C
  定义体: ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up Int)) (by
      rintro ⟨K, h⟩
      simpa [plus_quotient_obj_iff])

Depends on / 依赖: CochainComplex, CochainComplex.Plus, HomotopyCategory, HomotopyCategory.quotient, ObjectProperty, ObjectProperty.lift, plus_quotient_obj_iff, quotient
-/
def quotient : CochainComplex.Plus C ⥤ Plus C :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up Int)) (by
      rintro ⟨K, h⟩
      simpa [plus_quotient_obj_iff])

/--
Definition of `quotientCompιIso` / `quotientCompιIso` 的定义

English:
definition quotientCompιIso
  signature: :
  body: ObjectProperty.liftCompιIso ..

中文:
定义 quotientCompιIso
  签名: :
  定义体: ObjectProperty.liftCompιIso ..

Depends on / 依赖: ObjectProperty, ObjectProperty.liftComp
-/
def quotientCompιIso :
    quotient C ⋙ ι C ≅ CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up Int) :=
  ObjectProperty.liftCompιIso ..

variable {C} in
/--
lemma `quotient_obj_surjective` / 引理 `quotient_obj_surjective`

English:
lemma quotient_obj_surjective
  statement: Function.Surjective (quotient C).obj
  proof: fun K => by
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
    rw [← HomotopyCategory.plus_quotient_obj_iff]; rw [hL]
    exact K.property

中文:
引理 quotient_obj_surjective
  结论: 函数.满射 (quotient C).obj
  证明: fun K => by
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
    rw [← HomotopyCategory.plus_quotient_obj_iff]; rw [hL]
    exact K.property

Depends on / 依赖: HomotopyCategory, HomotopyCategory.plus_quotient_obj_iff, HomotopyCategory.quotient_obj_surjective, K.obj, K.property, plus_quotient_obj_iff, property, quotient_obj_surjective
-/
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj :=
  fun K => by
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
    rw [← HomotopyCategory.plus_quotient_obj_iff]; rw [hL]
    exact K.property

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient C).EssSurj
  body: by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩

中文:
实例 :
  签名: (quotient C).本质满射
  定义体: by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl, quotient_obj_surjective
-/
instance : (quotient C).EssSurj where
  mem_essImage K := by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quotient C).Full
  body: by dsimp [quotient]; infer_instance

中文:
实例 :
  签名: (quotient C).满
  定义体: by dsimp [quotient]; infer_instance

Depends on / 依赖: infer_instance, quotient
-/
instance : (quotient C).Full := by dsimp [quotient]; infer_instance

section

variable [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency.types false in
open HomologicalComplex in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf => by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← inverseImage_quotient_isomorphisms] using! hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjecti

中文:
实例 :
  定义体: Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf => by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← inverseImage_quotient_isomorphisms] using! hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjecti

Depends on / 依赖: Functor, Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders, HomotopyCategory, HomotopyCategory.Plus, K.precylinder, LeftHomotopy, ObjectProperty, ObjectProperty.homMk_surjective, Precylinder, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm, congr_map, cylinder, fullSubcategoryEquiv, homMk_surjective, homotopyOfEq, inverseImage_quotient_isomorphisms, isIso_iff_of_reflects_iso, isLocalization_of_essSurj_of_full_of_exists_cylinders, precylinder, replace
-/
instance :
    (quotient C).IsLocalization
      ((homotopyEquivalences C (.up Int)).inverseImage (CochainComplex.Plus.ι C)) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf => by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← inverseImage_quotient_isomorphisms] using! hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    replace hf := homotopyOfEq f₀ f₁ ((HomotopyCategory.Plus.ι _).congr_map hf)
    exact ⟨K.precylinder, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
      { h := cylinder.desc _ _ hf }, ⟨cylinder.homotopyEquiv _ (fun n => ⟨n - 1, by simp⟩), rfl⟩⟩)

/--
Definition of `singleFunctors` / `singleFunctors` 的定义

English:
definition singleFunctors
  signature: : SingleFunctors C (Plus C) Int
  body: SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (plus C).lift (singleFunctor C n)
    (fun X => by
      rw [← quotient_obj_singleFunctors_obj]; rw [plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩))
    (fun _ => Iso.refl _)

中文:
定义 singleFunctors
  签名: : SingleFunctors C (Plus C) 整数
  定义体: SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (plus C).lift (singleFunctor C n)
    (fun X => by
      rw [← quotient_obj_singleFunctors_obj]; rw [plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩))
    (fun _ => Iso.refl _)

Depends on / 依赖: HomotopyCategory, HomotopyCategory.singleFunctors, Iso.refl, SingleFunctors, SingleFunctors.lift, plus_quotient_obj_iff, quotient_obj_singleFunctors_obj, singleFunctor, singleFunctors
-/
noncomputable def singleFunctors : SingleFunctors C (Plus C) Int :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n => (plus C).lift (singleFunctor C n)
    (fun X => by
      rw [← quotient_obj_singleFunctors_obj]; rw [plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩))
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
noncomputable abbrev singleFunctor (n : Int) : C ⥤ Plus C :=
  (singleFunctors C).functor n

/--
Definition of `singleFunctorCompιIso` / `singleFunctorCompιIso` 的定义

English:
definition singleFunctorCompιIso
  signature: (n : Int)
  body: Iso.refl _

中文:
定义 singleFunctorCompιIso
  签名: (n : 整数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def singleFunctorCompιIso (n : Int) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
instance (n : Int) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end

end Plus

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C D}
variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapHomotopyCategoryPlus` / `mapHomotopyCategoryPlus` 的定义

English:
definition mapHomotopyCategoryPlus
  signature: : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D
  body: (HomotopyCategory.plus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up Int)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      dsimp
      simp only [HomotopyCategory.plus_quotient_obj_iff] at hX ⊢
      obtain ⟨n, _⟩ :

中文:
定义 mapHomotopyCategoryPlus
  签名: : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D
  定义体: (HomotopyCategory.plus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up Int)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      dsimp
      simp only [HomotopyCategory.plus_quotient_obj_iff] at hX ⊢
      obtain ⟨n, _⟩ :

Depends on / 依赖: CochainComplex, CochainComplex.IsStrictlyGE, ComplexShape, ComplexShape.up, F.mapHomologicalComplex, F.mapHomotopyCategory, HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.plus, HomotopyCategory.plus_quotient_obj_iff, HomotopyCategory.quotient_obj_surjective, IsStrictlyGE, mapHomologicalComplex, mapHomotopyCategory, plus_quotient_obj_iff, quotient_obj_surjective
-/
def mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D :=
  (HomotopyCategory.plus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up Int)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      dsimp
      simp only [HomotopyCategory.plus_quotient_obj_iff] at hX ⊢
      obtain ⟨n, _⟩ := hX
      exact ⟨n, inferInstanceAs (CochainComplex.IsStrictlyGE
        ((F.mapHomologicalComplex _).obj K) n)⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: inferInstanceAs (((HomotopyCategory.plus D).lift (HomotopyCategory.Plus.ι C ⋙
    F.mapHomotopyCategory (.up Int)) _).CommShift Int)

中文:
实例 :
  定义体: inferInstanceAs (((HomotopyCategory.plus D).lift (HomotopyCategory.Plus.ι C ⋙
    F.mapHomotopyCategory (.up Int)) _).CommShift Int)

Depends on / 依赖: CommShift, F.mapHomotopyCategory, HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.plus, mapHomotopyCategory
-/
noncomputable instance :
    F.mapHomotopyCategoryPlus.CommShift Int :=
  inferInstanceAs (((HomotopyCategory.plus D).lift (HomotopyCategory.Plus.ι C ⋙
    F.mapHomotopyCategory (.up Int)) _).CommShift Int)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] [HasBinaryBiproducts C] [HasZeroObject D] [HasBinaryBiproducts D] :
  body: by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

中文:
实例 [有ZeroObject
  签名: C] [有BinaryBiproducts C] [有ZeroObject D] [有BinaryBiproducts D] :
  定义体: by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

Depends on / 依赖: infer_instance, mapHomotopyCategoryPlus
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] [HasZeroObject D] [HasBinaryBiproducts D] :
    (F.mapHomotopyCategoryPlus).IsTriangulated := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Full
  signature: F] [Faithful F] : Full F.mapHomotopyCategoryPlus where
  body: ⟨ObjectProperty.homMk ((F.mapHomotopyCategory _).preimage f.hom), by
      ext
      exact (F.mapHomotopyCategory _).map_preimage f.hom⟩

中文:
实例 [满
  签名: F] [忠实 F] : 满 F.mapHomotopyCategoryPlus where
  定义体: ⟨ObjectProperty.homMk ((F.mapHomotopyCategory _).preimage f.hom), by
      ext
      exact (F.mapHomotopyCategory _).map_preimage f.hom⟩

Depends on / 依赖: F.mapHomotopyCategory, ObjectProperty, ObjectProperty.homMk, f.hom, mapHomotopyCategory, map_preimage, preimage
-/
instance [Full F] [Faithful F] : Full F.mapHomotopyCategoryPlus where
  map_surjective f :=
    ⟨ObjectProperty.homMk ((F.mapHomotopyCategory _).preimage f.hom), by
      ext
      exact (F.mapHomotopyCategory _).map_preimage f.hom⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Full
  signature: F] [Faithful F] : Faithful F.mapHomotopyCategoryPlus where
  body: by
    ext
    exact (F.mapHomotopyCategory _).map_injective ((ObjectProperty.ι _).congr_map h)

中文:
实例 [满
  签名: F] [忠实 F] : 忠实 F.mapHomotopyCategoryPlus where
  定义体: by
    ext
    exact (F.mapHomotopyCategory _).map_injective ((ObjectProperty.ι _).congr_map h)

Depends on / 依赖: F.mapHomotopyCategory, ObjectProperty, congr_map, mapHomotopyCategory, map_injective
-/
instance [Full F] [Faithful F] : Faithful F.mapHomotopyCategoryPlus where
  map_injective h := by
    ext
    exact (F.mapHomotopyCategory _).map_injective ((ObjectProperty.ι _).congr_map h)

/--
Definition of `mapHomotopyCategoryPlusCompIso` / `mapHomotopyCategoryPlusCompIso` 的定义

English:
definition mapHomotopyCategoryPlusCompIso
  signature: {E : Type*} [Category* E] [Preadditive E]
  body: ((HomotopyCategory.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (mapHomotopyCategoryCompIso e (.up Int)))

中文:
定义 mapHomotopyCategoryPlusCompIso
  签名: {E : 类型} [范畴* E] [预加性 E]
  定义体: ((HomotopyCategory.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (mapHomotopyCategoryCompIso e (.up Int)))

Depends on / 依赖: HomotopyCategory, HomotopyCategory.Plus, HomotopyCategory.plus, isoWhiskerLeft, mapHomotopyCategoryCompIso, preimageIso, whiskeringRight
-/
def mapHomotopyCategoryPlusCompIso {E : Type*} [Category* E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ≅ H.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (mapHomotopyCategoryCompIso e (.up Int)))

end Functor

end CategoryTheory
