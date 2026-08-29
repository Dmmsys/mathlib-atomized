/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.LiftingProperties.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# The model category structure on Over categories

Let `C` be a model category. For any `S : C`, we define
a model category structure on the category `Over S`:
a morphism `X ⟶ Y` in `Over S` is a cofibration
(resp. a fibration, a weak equivalence) if the
underlying morphism `f.left : X.left ⟶ Y.left` is.
(Apart from the existence of (finite) limits
from `Mathlib.CategoryTheory.Limits.Constructions.Over.Basic`, the verification
of the axioms is straightforward.)

## TODO
* Proceed to the dual construction for `Under S`.

-/

@[expose] public section

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithCofibrations (Over S)
  body: (cofibrations C).over

中文:
实例 :
  签名: CategoryWithCofibrations (Over S)
  定义体: (cofibrations C).over

Depends on / 依赖: cofibrations
-/
instance : CategoryWithCofibrations (Over S) where
  cofibrations := (cofibrations C).over

/--
lemma `cofibrations_over_def` / 引理 `cofibrations_over_def`

English:
lemma cofibrations_over_def
  proof: rfl

中文:
引理 cofibrations_over_def
  证明: rfl
-/
lemma cofibrations_over_def :
    cofibrations (Over S) = (cofibrations C).over := rfl

/--
lemma `cofibrations_over_iff` / 引理 `cofibrations_over_iff`

English:
lemma cofibrations_over_iff
  given: {X Y : Over S} (f : X ⟶ Y)
  proof: by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

中文:
引理 cofibrations_over_iff
  条件: {X Y : Over S} (f : X ⟶ Y)
  证明: by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

Depends on / 依赖: MorphismProperty, MorphismProperty.over_iff, cofibration_iff, cofibrations_over_def, over_iff
-/
lemma cofibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.left := by
  simp only [cofibration_iff, cofibrations_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.left := by
  rwa [← cofibrations_over_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [cofibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

中文:
实例 [(cofibrations
  签名: C).IsStableUnderRetracts] :
  定义体: by
  rw [cofibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.over_eq_inverseImage, cofibrations_over_def, infer_instance, over_eq_inverseImage
-/
instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Over S)).IsStableUnderRetracts := by
  rw [cofibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithFibrations (Over S)
  body: (fibrations C).over

中文:
实例 :
  签名: CategoryWithFibrations (Over S)
  定义体: (fibrations C).over

Depends on / 依赖: fibrations
-/
instance : CategoryWithFibrations (Over S) where
  fibrations := (fibrations C).over

/--
lemma `fibrations_over_def` / 引理 `fibrations_over_def`

English:
lemma fibrations_over_def
  proof: rfl

中文:
引理 fibrations_over_def
  证明: rfl
-/
lemma fibrations_over_def :
    fibrations (Over S) = (fibrations C).over := rfl

/--
lemma `fibrations_over_iff` / 引理 `fibrations_over_iff`

English:
lemma fibrations_over_iff
  given: {X Y : Over S} (f : X ⟶ Y)
  proof: by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

中文:
引理 fibrations_over_iff
  条件: {X Y : Over S} (f : X ⟶ Y)
  证明: by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

Depends on / 依赖: MorphismProperty, MorphismProperty.over_iff, fibration_iff, fibrations_over_def, over_iff
-/
lemma fibrations_over_iff {X Y : Over S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.left := by
  simp only [fibration_iff, fibrations_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [Fibration f] : Fibration f.left := by
  rwa [← fibrations_over_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(fibrations
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [fibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

中文:
实例 [(fibrations
  签名: C).IsStableUnderRetracts] :
  定义体: by
  rw [fibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.over_eq_inverseImage, fibrations_over_def, infer_instance, over_eq_inverseImage
-/
instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Over S)).IsStableUnderRetracts := by
  rw [fibrations_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithWeakEquivalences (Over S)
  body: (weakEquivalences C).over

中文:
实例 :
  签名: CategoryWithWeakEquivalences (Over S)
  定义体: (weakEquivalences C).over

Depends on / 依赖: weakEquivalences
-/
instance : CategoryWithWeakEquivalences (Over S) where
  weakEquivalences := (weakEquivalences C).over

/--
lemma `weakEquivalences_over_def` / 引理 `weakEquivalences_over_def`

English:
lemma weakEquivalences_over_def
  proof: rfl

中文:
引理 weakEquivalences_over_def
  证明: rfl
-/
lemma weakEquivalences_over_def :
    weakEquivalences (Over S) = (weakEquivalences C).over := rfl

/--
lemma `weakEquivalences_over_iff` / 引理 `weakEquivalences_over_iff`

English:
lemma weakEquivalences_over_iff
  given: {X Y : Over S} (f : X ⟶ Y)
  proof: by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

中文:
引理 weakEquivalences_over_iff
  条件: {X Y : Over S} (f : X ⟶ Y)
  证明: by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

Depends on / 依赖: MorphismProperty, MorphismProperty.over_iff, over_iff, weakEquivalence_iff, weakEquivalences_over_def
-/
lemma weakEquivalences_over_iff {X Y : Over S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.left := by
  simp only [weakEquivalence_iff, weakEquivalences_over_def, MorphismProperty.over_iff]

instance {X Y : Over S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.left := by
  rwa [← weakEquivalences_over_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(weakEquivalences
  signature: C).IsStableUnderRetracts] :
  body: by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

中文:
实例 [(weakEquivalences
  签名: C).IsStableUnderRetracts] :
  定义体: by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.over_eq_inverseImage, infer_instance, over_eq_inverseImage, weakEquivalences_over_def
-/
instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Over S)).IsStableUnderRetracts := by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

end

/--
lemma `trivialCofibrations_over_eq` / 引理 `trivialCofibrations_over_eq`

English:
lemma trivialCofibrations_over_eq
  proof: rfl

中文:
引理 trivialCofibrations_over_eq
  证明: rfl
-/
lemma trivialCofibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Over S) = (trivialCofibrations C).over := rfl

/--
lemma `trivialFibrations_over_eq` / 引理 `trivialFibrations_over_eq`

English:
lemma trivialFibrations_over_eq
  proof: rfl

中文:
引理 trivialFibrations_over_eq
  证明: rfl
-/
lemma trivialFibrations_over_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Over S) = (trivialFibrations C).over := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CategoryWithWeakEquivalences
  signature: C]
  body: by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

中文:
实例 [CategoryWithWeakEquivalences
  签名: C]
  定义体: by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

Depends on / 依赖: MorphismProperty, MorphismProperty.over_eq_inverseImage, infer_instance, over_eq_inverseImage, weakEquivalences_over_def
-/
instance [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Over S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_over_def]; rw [MorphismProperty.over_eq_inverseImage]
  infer_instance

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(trivialCofibrations
  signature: C).HasFactorization (fibrations C)] :
  body: by
  rw [fibrations_over_def]; rw [trivialCofibrations_over_eq]
  infer_instance

中文:
实例 [(trivialCofibrations
  签名: C).HasFactorization (fibrations C)] :
  定义体: by
  rw [fibrations_over_def]; rw [trivialCofibrations_over_eq]
  infer_instance

Depends on / 依赖: fibrations_over_def, infer_instance, trivialCofibrations_over_eq
-/
instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Over S)).HasFactorization (fibrations (Over S)) := by
  rw [fibrations_over_def]; rw [trivialCofibrations_over_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(cofibrations
  signature: C).HasFactorization (trivialFibrations C)] :
  body: by
  rw [cofibrations_over_def]; rw [trivialFibrations_over_eq]
  infer_instance

中文:
实例 [(cofibrations
  签名: C).HasFactorization (trivialFibrations C)] :
  定义体: by
  rw [cofibrations_over_def]; rw [trivialFibrations_over_eq]
  infer_instance

Depends on / 依赖: cofibrations_over_def, infer_instance, trivialFibrations_over_eq
-/
instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Over S)).HasFactorization (trivialFibrations (Over S)) := by
  rw [cofibrations_over_def]; rw [trivialFibrations_over_eq]
  infer_instance

end

/--
Instance `ModelCategory.over` / 实例 `ModelCategory.over`

English:
instance ModelCategory.over
  signature: [ModelCategory C]
  body: .over _ _
  cm4b _ _ _ _ _ := .over _ _

中文:
实例 ModelCategory.over
  签名: [ModelCategory C]
  定义体: .over _ _
  cm4b _ _ _ _ _ := .over _ _
-/
instance ModelCategory.over [ModelCategory C] : ModelCategory (Over S) where
  cm4a _ _ _ _ _ := .over _ _
  cm4b _ _ _ _ _ := .over _ _

end HomotopicalAlgebra
