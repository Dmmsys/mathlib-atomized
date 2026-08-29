/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Cylinders

We introduce a notion of cylinder for an object `A : C` in a model category.
It consists of an object `I`, a weak equivalence `π : I ⟶ A` equipped with two sections
`i₀` and `i₁`. This notion shall be important in the definition of "left homotopies"
in model categories.

## Implementation notes

The most important definition in this file is `Cylinder A`. This structure
extends another structure `Precylinder A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of cylinders are stated as typeclasses `Cylinder.IsGood`
and `Cylinder.IsVeryGood`.

The existence of very good cylinder objects in model categories is stated
in the lemma `Cylinder.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/cylinder+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/--
Definition of `Precylinder` / `Precylinder` 的定义

English:
structure Precylinder
  parameters: (A : C)
  axioms and operations (6):
    - I : C
    - i₀ : A ⟶ I
    - i₁ : A ⟶ I
    - π : I ⟶ A
    - i₀_π : i₀ ≫ π = 𝟙 A  [default: by cat_disch]
    - i₁_π : i₁ ≫ π = 𝟙 A  [default: by cat_disch]

中文:
结构 Precylinder
  参数: (A : C)
  公理与运算 (6 个):
    - I : C
    - i₀ : A ⟶ I
    - i₁ : A ⟶ I
    - π : I ⟶ A
    - i₀_π : i₀ ≫ π = 𝟙 A  [默认: by cat_disch]
    - i₁_π : i₁ ≫ π = 𝟙 A  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Precylinder (A : C) where
  /-- the underlying object of a (pre)cylinder -/
  I : C
  /-- the first "inclusion" in the (pre)cylinder -/
  i₀ : A ⟶ I
  /-- the second "inclusion" in the (pre)cylinder -/
  i₁ : A ⟶ I
  /-- the codiagonal of the (pre)cylinder -/
  π : I ⟶ A
  i₀_π : i₀ ≫ π = 𝟙 A := by cat_disch
  i₁_π : i₁ ≫ π = 𝟙 A := by cat_disch

namespace Precylinder

attribute [reassoc (attr := simp)] i₀_π i₁_π

variable {A : C} (P : Precylinder A)

/-- The precylinder object obtained by switching the two inclusions. -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : Precylinder A where
  body: P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π

中文:
定义 symm
  签名: : Precylinder A where
  定义体: P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π
-/
def symm : Precylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  π := P.π

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two precylinders. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (P' : Precylinder A) [HasPushout P.i₁ P'.i₀]
  body: pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)

中文:
定义 trans
  签名: (P' : Precylinder A) [HasPushout P.i₁ P'.i₀]
  定义体: pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)

Depends on / 依赖: pushout
-/
noncomputable def trans (P' : Precylinder A) [HasPushout P.i₁ P'.i₀] :
    Precylinder A where
  I := pushout P.i₁ P'.i₀
  i₀ := P.i₀ ≫ pushout.inl _ _
  i₁ := P'.i₁ ≫ pushout.inr _ _
  π := pushout.desc P.π P'.π (by simp)

section

variable [HasBinaryCoproduct A A]

/--
Definition of `i` / `i` 的定义

English:
definition i
  signature: : A ⨿ A ⟶ P.I
  body: coprod.desc P.i₀ P.i₁

中文:
定义 i
  签名: : A ⨿ A ⟶ P.I
  定义体: coprod.desc P.i₀ P.i₁

Depends on / 依赖: coprod, coprod.desc
-/
noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inl_i` / 引理 `inl_i`

English:
lemma inl_i
  statement: coprod.inl ≫ P.i = P.i₀
  proof: by simp [i]

中文:
引理 inl_i
  结论: coprod.inl ≫ P.i = P.i₀
  证明: by simp [i]
-/
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `inr_i` / 引理 `inr_i`

English:
lemma inr_i
  statement: coprod.inr ≫ P.i = P.i₁
  proof: by simp [i]

中文:
引理 inr_i
  结论: coprod.inr ≫ P.i = P.i₁
  证明: by simp [i]
-/
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

end

@[simp, reassoc]
/--
lemma `symm_i` / 引理 `symm_i`

English:
lemma symm_i
  given: [HasBinaryCoproducts C]
  statement: P.symm.i = (coprod.braiding A A).hom ≫ P.i
  proof: by cat_disch

中文:
引理 symm_i
  条件: [HasBinaryCoproducts C]
  结论: P.symm.i = (coprod.braiding A A).hom ≫ P.i
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma symm_i [HasBinaryCoproducts C] : P.symm.i = (coprod.braiding A A).hom ≫ P.i := by cat_disch

/-- The precylinder in a full subcategory of `C` induced by a precylinder
in the category `C`. -/
@[simps]
/--
Definition of `toFullSubcategory` / `toFullSubcategory` 的定义

English:
definition toFullSubcategory
  signature: {P : ObjectProperty C} {X : P.FullSubcategory} (Q : Precylinder X.obj)
  body: ⟨Q.I, hQ⟩
  i₀ := P.homMk Q.i₀
  i₁ := P.homMk Q.i₁
  π := P.homMk Q.π

中文:
定义 toFullSubcategory
  签名: {P : Object命题erty C} {X : P.FullSubcategory} (Q : Precylinder X.obj)
  定义体: ⟨Q.I, hQ⟩
  i₀ := P.homMk Q.i₀
  i₁ := P.homMk Q.i₁
  π := P.homMk Q.π
-/
def toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : Precylinder X.obj)
    (hQ : P Q.I) :
    Precylinder X where
  I := ⟨Q.I, hQ⟩
  i₀ := P.homMk Q.i₀
  i₁ := P.homMk Q.i₁
  π := P.homMk Q.π

/-- The image of a precylinder by a functor. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {X : C} (P : Precylinder X) {D : Type*} [Category* D] (F : C ⥤ D)
  body: F.obj P.I
  i₀ := F.map P.i₀
  i₁ := F.map P.i₁
  π := F.map P.π
  i₀_π := by simp [← F.map_comp]
  i₁_π := by simp [← F.map_comp]

中文:
定义 map
  签名: {X : C} (P : Precylinder X) {D : 类型} [Category* D] (F : C ⥤ D)
  定义体: F.obj P.I
  i₀ := F.map P.i₀
  i₁ := F.map P.i₁
  π := F.map P.π
  i₀_π := by simp [← F.map_comp]
  i₁_π := by simp [← F.map_comp]

Depends on / 依赖: F.obj
-/
def map {X : C} (P : Precylinder X) {D : Type*} [Category* D] (F : C ⥤ D) :
    Precylinder (F.obj X) where
  I := F.obj P.I
  i₀ := F.map P.i₀
  i₁ := F.map P.i₁
  π := F.map P.π
  i₀_π := by simp [← F.map_comp]
  i₁_π := by simp [← F.map_comp]

end Precylinder

/--
Definition of `Cylinder` / `Cylinder` 的定义

English:
structure Cylinder
  parameters: [CategoryWithWeakEquivalences C] (A : C)
  extends: Precylinder A
  axioms and operations (1):
    - weakEquivalence_π : WeakEquivalence π  [default: by infer_instance]

中文:
结构 Cylinder
  参数: [CategoryWithWeakEquivalences C] (A : C)
  继承: Precylinder A
  公理与运算 (1 个):
    - weakEquivalence_π : WeakEquivalence π  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure Cylinder [CategoryWithWeakEquivalences C] (A : C) extends Precylinder A where
  weakEquivalence_π : WeakEquivalence π := by infer_instance

namespace Cylinder

attribute [instance] weakEquivalence_π

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : Cylinder A)

set_option backward.defeqAttrib.useBackward true in
/-- The cylinder object obtained by switching the two inclusions. -/
@[simps!]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : Cylinder A where
  body: P.toPrecylinder.symm
  weakEquivalence_π := by dsimp; infer_instance

@[simp, reassoc]

中文:
定义 symm
  签名: : Cylinder A where
  定义体: P.toPrecylinder.symm
  weakEquivalence_π := by dsimp; infer_instance

@[simp, reassoc]

Depends on / 依赖: P.toPrecylinder.symm, toPrecylinder
-/
def symm : Cylinder A where
  __ := P.toPrecylinder.symm
  weakEquivalence_π := by dsimp; infer_instance

@[simp, reassoc]
/--
lemma `symm_i` / 引理 `symm_i`

English:
lemma symm_i
  given: [HasBinaryCoproducts C]
  proof: P.toPrecylinder.symm_i

中文:
引理 symm_i
  条件: [HasBinaryCoproducts C]
  证明: P.toPrecylinder.symm_i

Depends on / 依赖: P.toPrecylinder.symm_i, symm_i, toPrecylinder
-/
lemma symm_i [HasBinaryCoproducts C] :
    P.symm.i = (coprod.braiding A A).hom ≫ P.i :=
  P.toPrecylinder.symm_i

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence P.i₀
  body: weakEquivalence_of_postcomp_of_fac P.i₀_π

中文:
实例 :
  签名: WeakEquivalence P.i₀
  定义体: weakEquivalence_of_postcomp_of_fac P.i₀_π

Depends on / 依赖: weakEquivalence_of_postcomp_of_fac
-/
instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac P.i₀_π

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence P.i₁
  body: weakEquivalence_of_postcomp_of_fac P.i₁_π

中文:
实例 :
  签名: WeakEquivalence P.i₁
  定义体: weakEquivalence_of_postcomp_of_fac P.i₁_π

Depends on / 依赖: weakEquivalence_of_postcomp_of_fac
-/
instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac P.i₁_π

end

/--
Definition of `IsGood` / `IsGood` 的定义

English:
class IsGood
  parameters: [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  axioms and operations (1):
    - cofibration_i : Cofibration P.i  [default: by infer_instance]

中文:
类 IsGood
  参数: [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  公理与运算 (1 个):
    - cofibration_i : Cofibration P.i  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C] : Prop where
  cofibration_i : Cofibration P.i := by infer_instance

/--
Definition of `IsVeryGood` / `IsVeryGood` 的定义

English:
class IsVeryGood
  parameters: [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  extends: P.IsGood
  axioms and operations (1):
    - fibration_π : Fibration P.π  [default: by infer_instance]

中文:
类 IsVeryGood
  参数: [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  继承: P.IsGood
  公理与运算 (1 个):
    - fibration_π : Fibration P.π  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsVeryGood [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
    [CategoryWithFibrations C] : Prop extends P.IsGood where
  fibration_π : Fibration P.π := by infer_instance

attribute [instance] IsGood.cofibration_i IsVeryGood.fibration_π

section

variable [HasBinaryCoproduct A A] [CategoryWithCofibrations C]
  [HasInitial C] [(cofibrations C).IsStableUnderComposition]
  [(cofibrations C).IsStableUnderCobaseChange]
  [IsCofibrant A] [P.IsGood]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Cofibration P.i₀
  body: by
  rw [← P.inl_i]
  infer_instance

中文:
实例 :
  签名: Cofibration P.i₀
  定义体: by
  rw [← P.inl_i]
  infer_instance

Depends on / 依赖: P.inl_i, infer_instance, inl_i
-/
instance : Cofibration P.i₀ := by
  rw [← P.inl_i]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Cofibration P.i₁
  body: by
  rw [← P.inr_i]
  infer_instance

中文:
实例 :
  签名: Cofibration P.i₁
  定义体: by
  rw [← P.inr_i]
  infer_instance

Depends on / 依赖: P.inr_i, infer_instance, inr_i
-/
instance : Cofibration P.i₁ := by
  rw [← P.inr_i]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCofibrant P.I
  body: isCofibrant_of_cofibration P.i₀

中文:
实例 :
  签名: IsCofibrant P.I
  定义体: isCofibrant_of_cofibration P.i₀

Depends on / 依赖: isCofibrant_of_cofibration
-/
instance : IsCofibrant P.I :=
  isCofibrant_of_cofibration P.i₀

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryCoproducts
  signature: C] [CategoryWithCofibrations C] [P.IsGood]
  body: by
    have hi : cofibrations C P.i := by rw [← cofibration_iff]; infer_instance
    rw [P.symm_i]; rw [cofibration_iff]
    refine ((cofibrations C).arrow_mk_iso_iff ?_).2 hi
    exact Arrow.isoMk (coprod.braiding A A) (Iso.refl _)

中文:
实例 [HasBinaryCoproducts
  签名: C] [CategoryWithCofibrations C] [P.IsGood]
  定义体: by
    have hi : cofibrations C P.i := by rw [← cofibration_iff]; infer_instance
    rw [P.symm_i]; rw [cofibration_iff]
    refine ((cofibrations C).arrow_mk_iso_iff ?_).2 hi
    exact Arrow.isoMk (coprod.braiding A A) (Iso.refl _)

Depends on / 依赖: Arrow.isoMk, Iso.refl, P.symm_i, arrow_mk_iso_iff, braiding, cofibration_iff, cofibrations, coprod, coprod.braiding, infer_instance, symm_i
-/
instance [HasBinaryCoproducts C] [CategoryWithCofibrations C] [P.IsGood]
    [(cofibrations C).RespectsIso] : P.symm.IsGood where
  cofibration_i := by
    have hi : cofibrations C P.i := by rw [← cofibration_iff]; infer_instance
    rw [P.symm_i]; rw [cofibration_iff]
    refine ((cofibrations C).arrow_mk_iso_iff ?_).2 hi
    exact Arrow.isoMk (coprod.braiding A A) (Iso.refl _)

section

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [(fibrations C).IsStableUnderComposition]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryCoproduct
  signature: A A] [HasTerminal C] [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I
  body: isFibrant_of_fibration P.π

中文:
实例 [HasBinaryCoproduct
  签名: A A] [HasTerminal C] [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I
  定义体: isFibrant_of_fibration P.π

Depends on / 依赖: isFibrant_of_fibration
-/
instance [HasBinaryCoproduct A A] [HasTerminal C] [IsFibrant A] [P.IsVeryGood] : IsFibrant P.I :=
  isFibrant_of_fibration P.π

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).RespectsIso] [HasBinaryCoproducts C] [P.IsVeryGood] :
  body: by dsimp; infer_instance

中文:
实例 [(cofibrations
  签名: C).RespectsIso] [HasBinaryCoproducts C] [P.IsVeryGood] :
  定义体: by dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance [(cofibrations C).RespectsIso] [HasBinaryCoproducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  fibration_π := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : Cylinder A)

section

variable (h : MorphismProperty.MapFactorizationData (cofibrations C) (trivialFibrations C)
    (codiag A))

set_option backward.isDefEq.respectTransparency false in
/-- A cylinder object for `A` can be obtained from a factorization of the obvious
map `A ⨿ A ⟶ A` as a cofibration followed by a trivial fibration. -/
@[simps]
/--
Definition of `ofFactorizationData` / `ofFactorizationData` 的定义

English:
definition ofFactorizationData
  signature: : Cylinder A where
  body: h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

@[simp]

中文:
定义 ofFactorizationData
  签名: : Cylinder A where
  定义体: h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

@[simp]
-/
noncomputable def ofFactorizationData : Cylinder A where
  I := h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  π := h.p

@[simp]
/--
lemma `ofFactorizationData_i` / 引理 `ofFactorizationData_i`

English:
lemma ofFactorizationData_i
  statement: (ofFactorizationData h).i = h.i
  proof: by cat_disch

中文:
引理 ofFactorizationData_i
  结论: (ofFactorizationData h).i = h.i
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by cat_disch

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ofFactorizationData h).IsVeryGood
  body: by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance

中文:
实例 :
  签名: (ofFactorizationData h).IsVeryGood
  定义体: by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance

Depends on / 依赖: Cofibration, infer_instance
-/
instance : (ofFactorizationData h).IsVeryGood where
  cofibration_i := by simpa using inferInstanceAs (Cofibration h.i)
  fibration_π := by dsimp; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasTerminal
  signature: C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
  body: isFibrant_of_fibration (ofFactorizationData h).π

中文:
实例 [HasTerminal
  签名: C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
  定义体: isFibrant_of_fibration (ofFactorizationData h).π

Depends on / 依赖: isFibrant_of_fibration, ofFactorizationData
-/
instance [HasTerminal C] [IsFibrant A] [(fibrations C).IsStableUnderComposition] :
    IsFibrant (ofFactorizationData h).I :=
  isFibrant_of_fibration (ofFactorizationData h).π

end

variable (A) in
/--
lemma `exists_very_good` / 引理 `exists_very_good`

English:
lemma exists_very_good
  proof: ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

中文:
引理 exists_very_good
  证明: ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, factorizationData, ofFactorizationData
-/
lemma exists_very_good :
    exists (P : Cylinder A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (Cylinder A)
  body: ⟨(exists_very_good A).choose⟩

中文:
实例 :
  签名: Nonempty (Cylinder A)
  定义体: ⟨(exists_very_good A).choose⟩

Depends on / 依赖: exists_very_good
-/
instance : Nonempty (Cylinder A) := ⟨(exists_very_good A).choose⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two good cylinders. -/
@[simps!]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood]
  body: P.toPrecylinder.trans P'.toPrecylinder
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Precylinder.i₀_π]
      infer_instance
    dsimp
    a

中文:
定义 trans
  签名: [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood]
  定义体: P.toPrecylinder.trans P'.toPrecylinder
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Precylinder.i₀_π]
      infer_instance
    dsimp
    a

Depends on / 依赖: P.toPrecylinder.trans, toPrecylinder
-/
noncomputable def trans [IsCofibrant A] (P P' : Cylinder A) [P'.IsGood] :
    Cylinder A where
  __ := P.toPrecylinder.trans P'.toPrecylinder
  weakEquivalence_π := by
    have : WeakEquivalence ((P.i₀ ≫ pushout.inl P.i₁ P'.i₀) ≫
        pushout.desc P.π P'.π (by simp)) := by
      simp only [assoc, colimit.ι_desc, PushoutCocone.mk_ι_app,
        Precylinder.i₀_π]
      infer_instance
    dsimp
    apply weakEquivalence_of_precomp (P.i₀ ≫ pushout.inl _ _)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofibrant
  signature: A] (P P'
  body: by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i]; rw [ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condi

中文:
实例 [IsCofibrant
  签名: A] (P P'
  定义体: by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i]; rw [ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condi

Depends on / 依赖: Cofibration, IsPushout, IsPushout.of_hasPushout, P.trans, Precylinder, Precylinder.i, cofibration_iff, cofibrations, condition, coprod, coprod.desc, coprod.inl, coprod.map, of_hasPushout, pushout, pushout.condition, pushout.inl, pushout.inr
-/
instance [IsCofibrant A] (P P' : Cylinder A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  cofibration_i := by
    let ψ : P.I ⨿ A ⟶ (P.trans P').I := coprod.desc (pushout.inl _ _) (P'.i₁ ≫ pushout.inr _ _)
    rw [show (P.trans P').i = coprod.map P.i₀ (𝟙 A) ≫ ψ by simp [Precylinder.i]; rw [ψ]]
    have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = P'.i ≫ pushout.inr _ _ := by
      ext
      · simp [ψ, pushout.condition]
      · simp [ψ]
    have sq : IsPushout P.i₁ (coprod.inl ≫ P'.i) (coprod.inl ≫ ψ) (pushout.inr _ _) := by
      simpa [ψ] using IsPushout.of_hasPushout P.i₁ P'.i₀
    have : Cofibration ψ := by
      rw [cofibration_iff]
      exact (cofibrations C).of_isPushout
        (IsPushout.of_top sq fac (IsPushout.of_coprod_inl_with_id P.i₁ A).flip)
        (by rw [← cofibration_iff]; infer_instance)
    infer_instance

end Cylinder

end HomotopicalAlgebra
