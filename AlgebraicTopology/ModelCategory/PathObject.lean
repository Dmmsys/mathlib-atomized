/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Path objects

We introduce a notion of path object for an object `A : C` in a model category.
It consists of an object `P`, a weak equivalence `ι : A ⟶ P` equipped with two retractions
`p₀` and `p₁`. This notion shall be important in the definition of "right homotopies"
in model categories.

This file dualizes the definitions in the file
`Mathlib/AlgebraicTopology/ModelCategory/Cylinder.lean`.

## Implementation notes

The most important definition in this file is `PathObject A`. This structure
extends another structure `PrepathObject A` (which does not assume that `C`
has a notion of weak equivalences, which can be interesting in situations
where we have not yet obtained the model category axioms).

The good properties of path objects are stated as typeclasses `PathObject.IsGood`
and `PathObject.IsVeryGood`.

The existence of very good path objects in model categories is stated
in the lemma `PathObject.exists_very_good`.

## References
* [Daniel G. Quillen, Homotopical algebra][Quillen1967]
* https://ncatlab.org/nlab/show/path+space+object

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/--
Definition of `PrepathObject` / `PrepathObject` 的定义

English:
structure PrepathObject
  parameters: (A : C)
  axioms and operations (6):
    - P : C
    - p₀ : P ⟶ A
    - p₁ : P ⟶ A
    - ι : A ⟶ P
    - ι_p₀ : ι ≫ p₀ = 𝟙 A  [default: by aesop_cat]
    - ι_p₁ : ι ≫ p₁ = 𝟙 A  [default: by aesop_cat]

中文:
结构 PrepathObject
  参数: (A : C)
  公理与运算 (6 个):
    - P : C
    - p₀ : P ⟶ A
    - p₁ : P ⟶ A
    - ι : A ⟶ P
    - ι_p₀ : ι ≫ p₀ = 𝟙 A  [默认: by aesop_cat]
    - ι_p₁ : ι ≫ p₁ = 𝟙 A  [默认: by aesop_cat]

Depends on / 依赖: aesop_cat
-/
structure PrepathObject (A : C) where
  /-- the underlying object of a (pre)path object -/
  P : C
  /-- the first "projection" from the (pre)path object -/
  p₀ : P ⟶ A
  /-- the second "projection" from the (pre)path object -/
  p₁ : P ⟶ A
  /-- the diagonal of the (pre)path object -/
  ι : A ⟶ P
  ι_p₀ : ι ≫ p₀ = 𝟙 A := by aesop_cat
  ι_p₁ : ι ≫ p₁ = 𝟙 A := by aesop_cat

namespace PrepathObject

attribute [reassoc (attr := simp)] ι_p₀ ι_p₁

variable {A : C} (P : PrepathObject A)

/-- The pre-path object obtained by switching the two projections. -/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PrepathObject A where
  body: P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι

中文:
定义 symm
  签名: : PrepathObject A where
  定义体: P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι
-/
def symm : PrepathObject A where
  P := P.P
  p₀ := P.p₁
  p₁ := P.p₀
  ι := P.ι

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two pre-path objects. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀]
  body: pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)

中文:
定义 trans
  签名: (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀]
  定义体: pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)

Depends on / 依赖: pullback
-/
noncomputable def trans (P' : PrepathObject A) [HasPullback P.p₁ P'.p₀] :
    PrepathObject A where
  P := pullback P.p₁ P'.p₀
  p₀ := pullback.fst _ _ ≫ P.p₀
  p₁ := pullback.snd _ _ ≫ P'.p₁
  ι := pullback.lift P.ι P'.ι (by simp)

section

variable [HasBinaryProduct A A]

/--
Definition of `p` / `p` 的定义

English:
definition p
  signature: : P.P ⟶ A ⨯ A
  body: prod.lift P.p₀ P.p₁

中文:
定义 p
  签名: : P.P ⟶ A ⨯ A
  定义体: prod.lift P.p₀ P.p₁

Depends on / 依赖: prod.lift
-/
noncomputable def p : P.P ⟶ A ⨯ A := prod.lift P.p₀ P.p₁

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p_fst` / 引理 `p_fst`

English:
lemma p_fst
  statement: P.p ≫ prod.fst = P.p₀
  proof: by simp [p]

中文:
引理 p_fst
  结论: P.p ≫ prod.fst = P.p₀
  证明: by simp [p]
-/
lemma p_fst : P.p ≫ prod.fst = P.p₀ := by simp [p]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p_snd` / 引理 `p_snd`

English:
lemma p_snd
  statement: P.p ≫ prod.snd = P.p₁
  proof: by simp [p]

中文:
引理 p_snd
  结论: P.p ≫ prod.snd = P.p₁
  证明: by simp [p]
-/
lemma p_snd : P.p ≫ prod.snd = P.p₁ := by simp [p]

end

@[simp, reassoc]
/--
lemma `symm_p` / 引理 `symm_p`

English:
lemma symm_p
  given: [HasBinaryProducts C]
  proof: by aesop_cat

中文:
引理 symm_p
  条件: [HasBinaryProducts C]
  证明: by aesop_cat

Depends on / 依赖: aesop_cat
-/
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom := by aesop_cat

/-- The pre-path object in a full subcategory of `C` induced by a pre-path object
in the category `C`. -/
@[simps]
/--
Definition of `toFullSubcategory` / `toFullSubcategory` 的定义

English:
definition toFullSubcategory
  signature: {P : ObjectProperty C} {X : P.FullSubcategory} (Q : PrepathObject X.obj)
  body: ⟨Q.P, hQ⟩
  p₀ := P.homMk Q.p₀
  p₁ := P.homMk Q.p₁
  ι := P.homMk Q.ι

中文:
定义 toFullSubcategory
  签名: {P : Object命题erty C} {X : P.FullSubcategory} (Q : PrepathObject X.obj)
  定义体: ⟨Q.P, hQ⟩
  p₀ := P.homMk Q.p₀
  p₁ := P.homMk Q.p₁
  ι := P.homMk Q.ι
-/
def toFullSubcategory {P : ObjectProperty C} {X : P.FullSubcategory} (Q : PrepathObject X.obj)
    (hQ : P Q.P) :
    PrepathObject X where
  P := ⟨Q.P, hQ⟩
  p₀ := P.homMk Q.p₀
  p₁ := P.homMk Q.p₁
  ι := P.homMk Q.ι

/-- The image of a pre-path object by a functor. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {X : C} (P : PrepathObject X) {D : Type*} [Category* D] (F : C ⥤ D)
  body: F.obj P.P
  p₀ := F.map P.p₀
  p₁ := F.map P.p₁
  ι := F.map P.ι
  ι_p₀ := by simp [← F.map_comp]
  ι_p₁ := by simp [← F.map_comp]

中文:
定义 map
  签名: {X : C} (P : PrepathObject X) {D : 类型} [Category* D] (F : C ⥤ D)
  定义体: F.obj P.P
  p₀ := F.map P.p₀
  p₁ := F.map P.p₁
  ι := F.map P.ι
  ι_p₀ := by simp [← F.map_comp]
  ι_p₁ := by simp [← F.map_comp]

Depends on / 依赖: F.obj
-/
def map {X : C} (P : PrepathObject X) {D : Type*} [Category* D] (F : C ⥤ D) :
    PrepathObject (F.obj X) where
  P := F.obj P.P
  p₀ := F.map P.p₀
  p₁ := F.map P.p₁
  ι := F.map P.ι
  ι_p₀ := by simp [← F.map_comp]
  ι_p₁ := by simp [← F.map_comp]

end PrepathObject

/--
Definition of `PathObject` / `PathObject` 的定义

English:
structure PathObject
  parameters: [CategoryWithWeakEquivalences C] (A : C)
  extends: PrepathObject A
  axioms and operations (1):
    - weakEquivalence_ι : WeakEquivalence ι  [default: by infer_instance]

中文:
结构 PathObject
  参数: [CategoryWithWeakEquivalences C] (A : C)
  继承: PrepathObject A
  公理与运算 (1 个):
    - weakEquivalence_ι : WeakEquivalence ι  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure PathObject [CategoryWithWeakEquivalences C] (A : C) extends PrepathObject A where
  weakEquivalence_ι : WeakEquivalence ι := by infer_instance

namespace PathObject

attribute [instance] weakEquivalence_ι

section

variable {A : C} [CategoryWithWeakEquivalences C] (P : PathObject A)

set_option backward.defeqAttrib.useBackward true in
/-- The path object obtained by switching the two projections. -/
@[simps!]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : PathObject A where
  body: P.toPrepathObject.symm
  weakEquivalence_ι := by dsimp; infer_instance

@[simp, reassoc]

中文:
定义 symm
  签名: : PathObject A where
  定义体: P.toPrepathObject.symm
  weakEquivalence_ι := by dsimp; infer_instance

@[simp, reassoc]

Depends on / 依赖: P.toPrepathObject.symm, toPrepathObject
-/
def symm : PathObject A where
  __ := P.toPrepathObject.symm
  weakEquivalence_ι := by dsimp; infer_instance

@[simp, reassoc]
/--
lemma `symm_p` / 引理 `symm_p`

English:
lemma symm_p
  given: [HasBinaryProducts C]
  proof: P.toPrepathObject.symm_p

中文:
引理 symm_p
  条件: [HasBinaryProducts C]
  证明: P.toPrepathObject.symm_p

Depends on / 依赖: P.toPrepathObject.symm_p, symm_p, toPrepathObject
-/
lemma symm_p [HasBinaryProducts C] :
    P.symm.p = P.p ≫ (prod.braiding A A).hom :=
  P.toPrepathObject.symm_p

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence P.p₀
  body: weakEquivalence_of_precomp_of_fac P.ι_p₀

中文:
实例 :
  签名: WeakEquivalence P.p₀
  定义体: weakEquivalence_of_precomp_of_fac P.ι_p₀

Depends on / 依赖: weakEquivalence_of_precomp_of_fac
-/
instance : WeakEquivalence P.p₀ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₀

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WeakEquivalence P.p₁
  body: weakEquivalence_of_precomp_of_fac P.ι_p₁

中文:
实例 :
  签名: WeakEquivalence P.p₁
  定义体: weakEquivalence_of_precomp_of_fac P.ι_p₁

Depends on / 依赖: weakEquivalence_of_precomp_of_fac
-/
instance : WeakEquivalence P.p₁ :=
  weakEquivalence_of_precomp_of_fac P.ι_p₁

end

/--
Definition of `IsGood` / `IsGood` 的定义

English:
class IsGood
  parameters: [HasBinaryProduct A A] [CategoryWithFibrations C]
  axioms and operations (1):
    - fibration_p : Fibration P.p  [default: by infer_instance]

中文:
类 IsGood
  参数: [HasBinaryProduct A A] [CategoryWithFibrations C]
  公理与运算 (1 个):
    - fibration_p : Fibration P.p  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsGood [HasBinaryProduct A A] [CategoryWithFibrations C] : Prop where
  fibration_p : Fibration P.p := by infer_instance

/--
Definition of `IsVeryGood` / `IsVeryGood` 的定义

English:
class IsVeryGood
  parameters: [HasBinaryProduct A A] [CategoryWithFibrations C]
  extends: P.IsGood
  axioms and operations (1):
    - cofibration_ι : Cofibration P.ι  [default: by infer_instance]

中文:
类 IsVeryGood
  参数: [HasBinaryProduct A A] [CategoryWithFibrations C]
  继承: P.IsGood
  公理与运算 (1 个):
    - cofibration_ι : Cofibration P.ι  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsVeryGood [HasBinaryProduct A A] [CategoryWithFibrations C]
    [CategoryWithCofibrations C] : Prop extends P.IsGood where
  cofibration_ι : Cofibration P.ι := by infer_instance

attribute [instance] IsGood.fibration_p IsVeryGood.cofibration_ι

section

variable [HasBinaryProduct A A] [CategoryWithFibrations C]
  [HasTerminal C] [(fibrations C).IsStableUnderComposition]
  [(fibrations C).IsStableUnderBaseChange]
  [IsFibrant A] [P.IsGood]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fibration P.p₀
  body: by
  rw [← P.p_fst]
  infer_instance

中文:
实例 :
  签名: Fibration P.p₀
  定义体: by
  rw [← P.p_fst]
  infer_instance

Depends on / 依赖: P.p_fst, infer_instance, p_fst
-/
instance : Fibration P.p₀ := by
  rw [← P.p_fst]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fibration P.p₁
  body: by
  rw [← P.p_snd]
  infer_instance

中文:
实例 :
  签名: Fibration P.p₁
  定义体: by
  rw [← P.p_snd]
  infer_instance

Depends on / 依赖: P.p_snd, infer_instance, p_snd
-/
instance : Fibration P.p₁ := by
  rw [← P.p_snd]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsFibrant P.P
  body: isFibrant_of_fibration P.p₀

中文:
实例 :
  签名: IsFibrant P.P
  定义体: isFibrant_of_fibration P.p₀

Depends on / 依赖: isFibrant_of_fibration
-/
instance : IsFibrant P.P :=
  isFibrant_of_fibration P.p₀

end

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryProducts
  signature: C] [CategoryWithFibrations C] [P.IsGood]
  body: by
    have hp : fibrations C P.p := by rw [← fibration_iff]; infer_instance
    rw [P.symm_p]; rw [fibration_iff]
    refine ((fibrations C).arrow_mk_iso_iff ?_).2 hp
    exact Arrow.isoMk (Iso.refl _) (prod.braiding A A)

中文:
实例 [HasBinaryProducts
  签名: C] [CategoryWithFibrations C] [P.IsGood]
  定义体: by
    have hp : fibrations C P.p := by rw [← fibration_iff]; infer_instance
    rw [P.symm_p]; rw [fibration_iff]
    refine ((fibrations C).arrow_mk_iso_iff ?_).2 hp
    exact Arrow.isoMk (Iso.refl _) (prod.braiding A A)

Depends on / 依赖: Arrow.isoMk, Iso.refl, P.symm_p, arrow_mk_iso_iff, braiding, fibration_iff, fibrations, infer_instance, prod.braiding, symm_p
-/
instance [HasBinaryProducts C] [CategoryWithFibrations C] [P.IsGood]
    [(fibrations C).RespectsIso] : P.symm.IsGood where
  fibration_p := by
    have hp : fibrations C P.p := by rw [← fibration_iff]; infer_instance
    rw [P.symm_p]; rw [fibration_iff]
    refine ((fibrations C).arrow_mk_iso_iff ?_).2 hp
    exact Arrow.isoMk (Iso.refl _) (prod.braiding A A)

section

variable [CategoryWithFibrations C] [CategoryWithCofibrations C]
  [(cofibrations C).IsStableUnderComposition]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryProduct
  signature: A A] [HasInitial C] [IsCofibrant A] [P.IsVeryGood] : IsCofibrant P.P
  body: isCofibrant_of_cofibration P.ι

中文:
实例 [HasBinaryProduct
  签名: A A] [HasInitial C] [IsCofibrant A] [P.IsVeryGood] : IsCofibrant P.P
  定义体: isCofibrant_of_cofibration P.ι

Depends on / 依赖: isCofibrant_of_cofibration
-/
instance [HasBinaryProduct A A] [HasInitial C] [IsCofibrant A] [P.IsVeryGood] : IsCofibrant P.P :=
  isCofibrant_of_cofibration P.ι

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(fibrations
  signature: C).RespectsIso] [HasBinaryProducts C] [P.IsVeryGood] :
  body: by dsimp; infer_instance

中文:
实例 [(fibrations
  签名: C).RespectsIso] [HasBinaryProducts C] [P.IsVeryGood] :
  定义体: by dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance [(fibrations C).RespectsIso] [HasBinaryProducts C] [P.IsVeryGood] :
    P.symm.IsVeryGood where
  cofibration_ι := by dsimp; infer_instance

end

end

variable [ModelCategory C] {A : C} (P : PathObject A)

section

variable (h : MorphismProperty.MapFactorizationData
  (trivialCofibrations C) (fibrations C) (diag A))

set_option backward.isDefEq.respectTransparency false in
/-- A path object for `A` can be obtained from a factorization of the obvious
map `A ⟶ A ⨯ A` as a trivial cofibration followed by a fibration. -/
@[simps]
/--
Definition of `ofFactorizationData` / `ofFactorizationData` 的定义

English:
definition ofFactorizationData
  signature: : PathObject A where
  body: h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

@[simp]

中文:
定义 ofFactorizationData
  签名: : PathObject A where
  定义体: h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

@[simp]
-/
noncomputable def ofFactorizationData : PathObject A where
  P := h.Z
  p₀ := h.p ≫ prod.fst
  p₁ := h.p ≫ prod.snd
  ι := h.i

@[simp]
/--
lemma `ofFactorizationData_p` / 引理 `ofFactorizationData_p`

English:
lemma ofFactorizationData_p
  statement: (ofFactorizationData h).p = h.p
  proof: by aesop_cat

中文:
引理 ofFactorizationData_p
  结论: (ofFactorizationData h).p = h.p
  证明: by aesop_cat

Depends on / 依赖: aesop_cat
-/
lemma ofFactorizationData_p : (ofFactorizationData h).p = h.p := by aesop_cat

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ofFactorizationData h).IsVeryGood
  body: by simpa using inferInstanceAs (Fibration h.p)
  cofibration_ι := by dsimp; infer_instance

中文:
实例 :
  签名: (ofFactorizationData h).IsVeryGood
  定义体: by simpa using inferInstanceAs (Fibration h.p)
  cofibration_ι := by dsimp; infer_instance

Depends on / 依赖: Fibration, infer_instance
-/
instance : (ofFactorizationData h).IsVeryGood where
  fibration_p := by simpa using inferInstanceAs (Fibration h.p)
  cofibration_ι := by dsimp; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasInitial
  signature: C] [IsCofibrant A] [(cofibrations C).IsStableUnderComposition] :
  body: isCofibrant_of_cofibration (ofFactorizationData h).ι

中文:
实例 [HasInitial
  签名: C] [IsCofibrant A] [(cofibrations C).IsStableUnderComposition] :
  定义体: isCofibrant_of_cofibration (ofFactorizationData h).ι

Depends on / 依赖: isCofibrant_of_cofibration, ofFactorizationData
-/
instance [HasInitial C] [IsCofibrant A] [(cofibrations C).IsStableUnderComposition] :
    IsCofibrant (ofFactorizationData h).P :=
  isCofibrant_of_cofibration (ofFactorizationData h).ι

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
    exists (P : PathObject A), P.IsVeryGood :=
  ⟨ofFactorizationData (MorphismProperty.factorizationData _ _ _),
    inferInstance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (PathObject A)
  body: ⟨(exists_very_good A).choose⟩

中文:
实例 :
  签名: Nonempty (PathObject A)
  定义体: ⟨(exists_very_good A).choose⟩

Depends on / 依赖: exists_very_good
-/
instance : Nonempty (PathObject A) := ⟨(exists_very_good A).choose⟩

set_option backward.defeqAttrib.useBackward true in
/-- The gluing of two good path objects. -/
@[simps!]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: [IsFibrant A] (P P' : PathObject A) [P'.IsGood]
  body: P.toPrepathObject.trans P'.toPrepathObject
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫
        pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc]; rw [PrepathObject.ι_p₀]
      infer_instance
    dsimp
    apply weakEquivalence_of_po

中文:
定义 trans
  签名: [IsFibrant A] (P P' : PathObject A) [P'.IsGood]
  定义体: P.toPrepathObject.trans P'.toPrepathObject
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫
        pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc]; rw [PrepathObject.ι_p₀]
      infer_instance
    dsimp
    apply weakEquivalence_of_po

Depends on / 依赖: P.toPrepathObject.trans, toPrepathObject
-/
noncomputable def trans [IsFibrant A] (P P' : PathObject A) [P'.IsGood] :
    PathObject A where
  __ := P.toPrepathObject.trans P'.toPrepathObject
  weakEquivalence_ι := by
    have : WeakEquivalence (pullback.lift P.ι P'.ι (by simp) ≫
        pullback.fst P.p₁ P'.p₀ ≫ P.p₀) := by
      rw [pullback.lift_fst_assoc]; rw [PrepathObject.ι_p₀]
      infer_instance
    dsimp
    apply weakEquivalence_of_postcomp _ (pullback.fst P.p₁ P'.p₀ ≫ P.p₀)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFibrant
  signature: A] (P P'
  body: by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PrepathObject.p]; rw [ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condi

中文:
实例 [IsFibrant
  签名: A] (P P'
  定义体: by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PrepathObject.p]; rw [ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condi

Depends on / 依赖: Fibration, IsPullback, IsPullback.of_hasPullback, P.trans, PrepathObject, PrepathObject.p, condition, fibration_iff, fibrations, of_hasPullback, prod.fst, prod.lift, prod.map, pullback, pullback.condition, pullback.fst, pullback.snd
-/
instance [IsFibrant A] (P P' : PathObject A) [P.IsGood] [P'.IsGood] :
    (P.trans P').IsGood where
  fibration_p := by
    let ψ : (P.trans P').P ⟶ P.P ⨯ A := prod.lift (pullback.fst _ _) (pullback.snd _ _ ≫ P'.p₁)
    rw [show (P.trans P').p = ψ ≫ prod.map P.p₀ (𝟙 A) by simp [PrepathObject.p]; rw [ψ]]
    have fac : ψ ≫ prod.map P.p₁ (𝟙 A) = pullback.snd _ _ ≫ P'.p := by
      ext
      · simp [ψ, pullback.condition]
      · simp [ψ]
    have sq : IsPullback (ψ ≫ prod.fst) (pullback.snd P.p₁ P'.p₀) P.p₁ (P'.p ≫ prod.fst) := by
      simpa [ψ] using IsPullback.of_hasPullback P.p₁ P'.p₀
    have : Fibration ψ := by
      rw [fibration_iff]
      exact (fibrations C).of_isPullback
        (IsPullback.of_right sq fac (IsPullback.of_prod_fst_with_id P.p₁ A)).flip
          (by rw [← fibration_iff]; infer_instance)
    infer_instance

end PathObject

/-- The opposite of a pre-path object is a precylinder object. -/
@[simps]
/--
Definition of `PrepathObject.op` / `PrepathObject.op` 的定义

English:
definition PrepathObject.op
  signature: {A : C} (P : PrepathObject A)
  body: op P.P
  i₀ := P.p₀.op
  i₁ := P.p₁.op
  π := P.ι.op
  i₀_π := Quiver.Hom.unop_inj (by simp)
  i₁_π := Quiver.Hom.unop_inj (by simp)

中文:
定义 PrepathObject.op
  签名: {A : C} (P : PrepathObject A)
  定义体: op P.P
  i₀ := P.p₀.op
  i₁ := P.p₁.op
  π := P.ι.op
  i₀_π := Quiver.Hom.unop_inj (by simp)
  i₁_π := Quiver.Hom.unop_inj (by simp)
-/
protected def PrepathObject.op {A : C} (P : PrepathObject A) :
    Precylinder (op A) where
  I := op P.P
  i₀ := P.p₀.op
  i₁ := P.p₁.op
  π := P.ι.op
  i₀_π := Quiver.Hom.unop_inj (by simp)
  i₁_π := Quiver.Hom.unop_inj (by simp)

/-- The precylinder object obtained from a pre-path object in the opposite category. -/
@[simps]
/--
Definition of `PrepathObject.unop` / `PrepathObject.unop` 的定义

English:
definition PrepathObject.unop
  signature: {A : Cᵒᵖ} (P : PrepathObject A)
  body: P.P.unop
  i₀ := P.p₀.unop
  i₁ := P.p₁.unop
  π := P.ι.unop
  i₀_π := Quiver.Hom.op_inj (by simp)
  i₁_π := Quiver.Hom.op_inj (by simp)

中文:
定义 PrepathObject.unop
  签名: {A : Cᵒᵖ} (P : PrepathObject A)
  定义体: P.P.unop
  i₀ := P.p₀.unop
  i₁ := P.p₁.unop
  π := P.ι.unop
  i₀_π := Quiver.Hom.op_inj (by simp)
  i₁_π := Quiver.Hom.op_inj (by simp)
-/
protected def PrepathObject.unop {A : Cᵒᵖ} (P : PrepathObject A) :
    Precylinder A.unop where
  I := P.P.unop
  i₀ := P.p₀.unop
  i₁ := P.p₁.unop
  π := P.ι.unop
  i₀_π := Quiver.Hom.op_inj (by simp)
  i₁_π := Quiver.Hom.op_inj (by simp)

/-- The opposite of a precylinder object is a pre-path object. -/
@[simps]
/--
Definition of `Precylinder.op` / `Precylinder.op` 的定义

English:
definition Precylinder.op
  signature: {A : C} (P : Precylinder A)
  body: op P.I
  p₀ := P.i₀.op
  p₁ := P.i₁.op
  ι := P.π.op
  ι_p₀ := Quiver.Hom.unop_inj (by simp)
  ι_p₁ := Quiver.Hom.unop_inj (by simp)

中文:
定义 Precylinder.op
  签名: {A : C} (P : Precylinder A)
  定义体: op P.I
  p₀ := P.i₀.op
  p₁ := P.i₁.op
  ι := P.π.op
  ι_p₀ := Quiver.Hom.unop_inj (by simp)
  ι_p₁ := Quiver.Hom.unop_inj (by simp)
-/
protected def Precylinder.op {A : C} (P : Precylinder A) :
    PrepathObject (op A) where
  P := op P.I
  p₀ := P.i₀.op
  p₁ := P.i₁.op
  ι := P.π.op
  ι_p₀ := Quiver.Hom.unop_inj (by simp)
  ι_p₁ := Quiver.Hom.unop_inj (by simp)

/-- The pre-path object object obtained from a cylinder in the opposite category. -/
@[simps]
/--
Definition of `Precylinder.unop` / `Precylinder.unop` 的定义

English:
definition Precylinder.unop
  signature: {A : Cᵒᵖ} (P : Precylinder A)
  body: P.I.unop
  p₀ := P.i₀.unop
  p₁ := P.i₁.unop
  ι := P.π.unop
  ι_p₀ := Quiver.Hom.op_inj (by simp)
  ι_p₁ := Quiver.Hom.op_inj (by simp)

中文:
定义 Precylinder.unop
  签名: {A : Cᵒᵖ} (P : Precylinder A)
  定义体: P.I.unop
  p₀ := P.i₀.unop
  p₁ := P.i₁.unop
  ι := P.π.unop
  ι_p₀ := Quiver.Hom.op_inj (by simp)
  ι_p₁ := Quiver.Hom.op_inj (by simp)
-/
protected def Precylinder.unop {A : Cᵒᵖ} (P : Precylinder A) :
    PrepathObject A.unop where
  P := P.I.unop
  p₀ := P.i₀.unop
  p₁ := P.i₁.unop
  ι := P.π.unop
  ι_p₀ := Quiver.Hom.op_inj (by simp)
  ι_p₁ := Quiver.Hom.op_inj (by simp)

end HomotopicalAlgebra
