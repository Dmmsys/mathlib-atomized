/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

/--
Definition of `leftExactFunctor` / `leftExactFunctor` 的定义

English:
definition leftExactFunctor
  signature: : ObjectProperty (C ⥤ D)
  body: fun F => PreservesFiniteLimits F

中文:
定义 leftExactFunctor
  签名: : ObjectProperty (C ⥤ D)
  定义体: fun F => PreservesFiniteLimits F

Depends on / 依赖: PreservesFiniteLimits
-/
def leftExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F => PreservesFiniteLimits F

variable {C D} in
@[simp]
/--
lemma `leftExactFunctor_iff` / 引理 `leftExactFunctor_iff`

English:
lemma leftExactFunctor_iff
  given: (F : C ⥤ D)
  proof: Iff.rfl

中文:
引理 leftExactFunctor_iff
  条件: (F : C ⥤ D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma leftExactFunctor_iff (F : C ⥤ D) :
    leftExactFunctor C D F ↔ PreservesFiniteLimits F := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (leftExactFunctor C D).IsClosedUnderIsomorphisms
  body: by
    simp only [leftExactFunctor_iff] at h ⊢
    exact preservesFiniteLimits_of_natIso e

中文:
实例 :
  签名: (leftExactFunctor C D).在同构下封闭
  定义体: by
    simp only [leftExactFunctor_iff] at h ⊢
    exact preservesFiniteLimits_of_natIso e

Depends on / 依赖: leftExactFunctor_iff, preservesFiniteLimits_of_natIso
-/
instance : (leftExactFunctor C D).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [leftExactFunctor_iff] at h ⊢
    exact preservesFiniteLimits_of_natIso e

/--
Definition of `LeftExactFunctor` / `LeftExactFunctor` 的定义

English:
abbreviation LeftExactFunctor
  body: (leftExactFunctor C D).FullSubcategory

中文:
缩写 LeftExactFunctor
  定义体: (leftExactFunctor C D).FullSubcategory

Depends on / 依赖: FullSubcategory, leftExactFunctor
-/
abbrev LeftExactFunctor := (leftExactFunctor C D).FullSubcategory

/-- `C ⥤ₗ D` denotes left exact functors `C ⥤ D` -/
infixr:26 " ⥤ₗ " => LeftExactFunctor

/--
Definition of `LeftExactFunctor.forget` / `LeftExactFunctor.forget` 的定义

English:
abbreviation LeftExactFunctor.forget
  signature: : (C ⥤ₗ D) ⥤ C ⥤ D
  body: ObjectProperty.ι _

中文:
缩写 LeftExactFunctor.forget
  签名: : (C ⥤ₗ D) ⥤ C ⥤ D
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/--
Definition of `LeftExactFunctor.fullyFaithful` / `LeftExactFunctor.fullyFaithful` 的定义

English:
abbreviation LeftExactFunctor.fullyFaithful
  signature: : (LeftExactFunctor.forget C D).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
缩写 LeftExactFunctor.fullyFaithful
  签名: : (LeftExactFunctor.forget C D).满忠实
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
abbrev LeftExactFunctor.fullyFaithful : (LeftExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/--
Definition of `rightExactFunctor` / `rightExactFunctor` 的定义

English:
definition rightExactFunctor
  signature: : ObjectProperty (C ⥤ D)
  body: fun F => PreservesFiniteColimits F

中文:
定义 rightExactFunctor
  签名: : ObjectProperty (C ⥤ D)
  定义体: fun F => PreservesFiniteColimits F

Depends on / 依赖: PreservesFiniteColimits
-/
def rightExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F => PreservesFiniteColimits F

variable {C D} in
@[simp]
/--
lemma `rightExactFunctor_iff` / 引理 `rightExactFunctor_iff`

English:
lemma rightExactFunctor_iff
  given: (F : C ⥤ D)
  proof: Iff.rfl

中文:
引理 rightExactFunctor_iff
  条件: (F : C ⥤ D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma rightExactFunctor_iff (F : C ⥤ D) :
    rightExactFunctor C D F ↔ PreservesFiniteColimits F := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rightExactFunctor C D).IsClosedUnderIsomorphisms
  body: by
    simp only [rightExactFunctor_iff] at h ⊢
    exact preservesFiniteColimits_of_natIso e

中文:
实例 :
  签名: (rightExactFunctor C D).在同构下封闭
  定义体: by
    simp only [rightExactFunctor_iff] at h ⊢
    exact preservesFiniteColimits_of_natIso e

Depends on / 依赖: preservesFiniteColimits_of_natIso, rightExactFunctor_iff
-/
instance : (rightExactFunctor C D).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [rightExactFunctor_iff] at h ⊢
    exact preservesFiniteColimits_of_natIso e

/--
Definition of `RightExactFunctor` / `RightExactFunctor` 的定义

English:
abbreviation RightExactFunctor
  body: (rightExactFunctor C D).FullSubcategory

中文:
缩写 RightExactFunctor
  定义体: (rightExactFunctor C D).FullSubcategory

Depends on / 依赖: FullSubcategory, rightExactFunctor
-/
abbrev RightExactFunctor := (rightExactFunctor C D).FullSubcategory

/-- `C ⥤ᵣ D` denotes right exact functors `C ⥤ D` -/
infixr:26 " ⥤ᵣ " => RightExactFunctor

/--
Definition of `RightExactFunctor.forget` / `RightExactFunctor.forget` 的定义

English:
abbreviation RightExactFunctor.forget
  signature: : (C ⥤ᵣ D) ⥤ C ⥤ D
  body: ObjectProperty.ι _

中文:
缩写 RightExactFunctor.forget
  签名: : (C ⥤ᵣ D) ⥤ C ⥤ D
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/--
Definition of `RightExactFunctor.fullyFaithful` / `RightExactFunctor.fullyFaithful` 的定义

English:
abbreviation RightExactFunctor.fullyFaithful
  signature: : (RightExactFunctor.forget C D).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
缩写 RightExactFunctor.fullyFaithful
  签名: : (RightExactFunctor.forget C D).满忠实
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
abbrev RightExactFunctor.fullyFaithful : (RightExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/--
Definition of `exactFunctor` / `exactFunctor` 的定义

English:
definition exactFunctor
  signature: : ObjectProperty (C ⥤ D)
  body: leftExactFunctor C D ⊓ rightExactFunctor C D

中文:
定义 exactFunctor
  签名: : ObjectProperty (C ⥤ D)
  定义体: leftExactFunctor C D ⊓ rightExactFunctor C D

Depends on / 依赖: leftExactFunctor, rightExactFunctor
-/
def exactFunctor : ObjectProperty (C ⥤ D) :=
  leftExactFunctor C D ⊓ rightExactFunctor C D

variable {C D} in
@[simp]
/--
lemma `exactFunctor_iff` / 引理 `exactFunctor_iff`

English:
lemma exactFunctor_iff
  given: (F : C ⥤ D)
  proof: Iff.rfl

中文:
引理 exactFunctor_iff
  条件: (F : C ⥤ D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma exactFunctor_iff (F : C ⥤ D) :
    exactFunctor C D F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (exactFunctor C D).IsClosedUnderIsomorphisms
  body: by
  dsimp [exactFunctor]
  infer_instance

中文:
实例 :
  签名: (exactFunctor C D).在同构下封闭
  定义体: by
  dsimp [exactFunctor]
  infer_instance

Depends on / 依赖: exactFunctor, infer_instance
-/
instance : (exactFunctor C D).IsClosedUnderIsomorphisms := by
  dsimp [exactFunctor]
  infer_instance

/--
Definition of `ExactFunctor` / `ExactFunctor` 的定义

English:
abbreviation ExactFunctor
  body: (exactFunctor C D).FullSubcategory

中文:
缩写 ExactFunctor
  定义体: (exactFunctor C D).FullSubcategory

Depends on / 依赖: FullSubcategory, exactFunctor
-/
abbrev ExactFunctor := (exactFunctor C D).FullSubcategory

/-- `C ⥤ₑ D` denotes exact functors `C ⥤ D` -/
infixr:26 " ⥤ₑ " => ExactFunctor

/--
Definition of `ExactFunctor.forget` / `ExactFunctor.forget` 的定义

English:
abbreviation ExactFunctor.forget
  signature: : (C ⥤ₑ D) ⥤ C ⥤ D
  body: ObjectProperty.ι _

中文:
缩写 ExactFunctor.forget
  签名: : (C ⥤ₑ D) ⥤ C ⥤ D
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/--
lemma `exactFunctor_le_leftExactFunctor` / 引理 `exactFunctor_le_leftExactFunctor`

English:
lemma exactFunctor_le_leftExactFunctor
  proof: fun _ h => h.1

中文:
引理 exactFunctor_le_leftExactFunctor
  证明: fun _ h => h.1
-/
lemma exactFunctor_le_leftExactFunctor :
    exactFunctor C D <= leftExactFunctor C D :=
  fun _ h => h.1

/--
lemma `exactFunctor_le_rightExactFunctor` / 引理 `exactFunctor_le_rightExactFunctor`

English:
lemma exactFunctor_le_rightExactFunctor
  proof: fun _ h => h.2

中文:
引理 exactFunctor_le_rightExactFunctor
  证明: fun _ h => h.2
-/
lemma exactFunctor_le_rightExactFunctor :
    exactFunctor C D <= rightExactFunctor C D :=
  fun _ h => h.2

/--
Definition of `LeftExactFunctor.ofExact` / `LeftExactFunctor.ofExact` 的定义

English:
abbreviation LeftExactFunctor.ofExact
  signature: : (C ⥤ₑ D) ⥤ C ⥤ₗ D
  body: ObjectProperty.ιOfLE (exactFunctor_le_leftExactFunctor C D)

中文:
缩写 LeftExactFunctor.ofExact
  签名: : (C ⥤ₑ D) ⥤ C ⥤ₗ D
  定义体: ObjectProperty.ιOfLE (exactFunctor_le_leftExactFunctor C D)

Depends on / 依赖: ObjectProperty, exactFunctor_le_leftExactFunctor
-/
abbrev LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_leftExactFunctor C D)

/--
Definition of `RightExactFunctor.ofExact` / `RightExactFunctor.ofExact` 的定义

English:
abbreviation RightExactFunctor.ofExact
  signature: : (C ⥤ₑ D) ⥤ C ⥤ᵣ D
  body: ObjectProperty.ιOfLE (exactFunctor_le_rightExactFunctor C D)

中文:
缩写 RightExactFunctor.ofExact
  签名: : (C ⥤ₑ D) ⥤ C ⥤ᵣ D
  定义体: ObjectProperty.ιOfLE (exactFunctor_le_rightExactFunctor C D)

Depends on / 依赖: ObjectProperty, exactFunctor_le_rightExactFunctor
-/
abbrev RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_rightExactFunctor C D)

variable {C D}

@[simp]
/--
theorem `LeftExactFunctor.ofExact_obj` / 定理 `LeftExactFunctor.ofExact_obj`

English:
theorem LeftExactFunctor.ofExact_obj
  given: (F : C ⥤ₑ D)
  proof: rfl

@[simp]

中文:
定理 LeftExactFunctor.ofExact_obj
  条件: (F : C ⥤ₑ D)
  证明: rfl

@[simp]
-/
theorem LeftExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl

@[simp]
/--
theorem `RightExactFunctor.ofExact_obj` / 定理 `RightExactFunctor.ofExact_obj`

English:
theorem RightExactFunctor.ofExact_obj
  given: (F : C ⥤ₑ D)
  proof: rfl

@[simp]

中文:
定理 RightExactFunctor.ofExact_obj
  条件: (F : C ⥤ₑ D)
  证明: rfl

@[simp]
-/
theorem RightExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (RightExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl

@[simp]
/--
theorem `LeftExactFunctor.ofExact_map_hom` / 定理 `LeftExactFunctor.ofExact_map_hom`

English:
theorem LeftExactFunctor.ofExact_map_hom
  given: {F G : C ⥤ₑ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 LeftExactFunctor.ofExact_map_hom
  条件: {F G : C ⥤ₑ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem LeftExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((LeftExactFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/--
theorem `RightExactFunctor.ofExact_map_hom` / 定理 `RightExactFunctor.ofExact_map_hom`

English:
theorem RightExactFunctor.ofExact_map_hom
  given: {F G : C ⥤ₑ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 RightExactFunctor.ofExact_map_hom
  条件: {F G : C ⥤ₑ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem RightExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((RightExactFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

@[simp]
/--
theorem `LeftExactFunctor.forget_obj` / 定理 `LeftExactFunctor.forget_obj`

English:
theorem LeftExactFunctor.forget_obj
  given: (F : C ⥤ₗ D)
  statement: (LeftExactFunctor.forget C D).obj F = F.1
  proof: rfl

@[simp]

中文:
定理 LeftExactFunctor.forget_obj
  条件: (F : C ⥤ₗ D)
  结论: (LeftExactFunctor.forget C D).obj F = F.1
  证明: rfl

@[simp]
-/
theorem LeftExactFunctor.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/--
theorem `RightExactFunctor.forget_obj` / 定理 `RightExactFunctor.forget_obj`

English:
theorem RightExactFunctor.forget_obj
  given: (F : C ⥤ᵣ D)
  statement: (RightExactFunctor.forget C D).obj F = F.1
  proof: rfl

@[simp]

中文:
定理 RightExactFunctor.forget_obj
  条件: (F : C ⥤ᵣ D)
  结论: (RightExactFunctor.forget C D).obj F = F.1
  证明: rfl

@[simp]
-/
theorem RightExactFunctor.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/--
theorem `ExactFunctor.forget_obj` / 定理 `ExactFunctor.forget_obj`

English:
theorem ExactFunctor.forget_obj
  given: (F : C ⥤ₑ D)
  statement: (ExactFunctor.forget C D).obj F = F.1
  proof: rfl

@[simp]

中文:
定理 ExactFunctor.forget_obj
  条件: (F : C ⥤ₑ D)
  结论: (ExactFunctor.forget C D).obj F = F.1
  证明: rfl

@[simp]
-/
theorem ExactFunctor.forget_obj (F : C ⥤ₑ D) : (ExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
/--
theorem `LeftExactFunctor.forget_map` / 定理 `LeftExactFunctor.forget_map`

English:
theorem LeftExactFunctor.forget_map
  given: {F G : C ⥤ₗ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 LeftExactFunctor.forget_map
  条件: {F G : C ⥤ₗ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
/--
theorem `RightExactFunctor.forget_map` / 定理 `RightExactFunctor.forget_map`

English:
theorem RightExactFunctor.forget_map
  given: {F G : C ⥤ᵣ D} (α : F ⟶ G)
  proof: rfl

@[simp]

中文:
定理 RightExactFunctor.forget_map
  条件: {F G : C ⥤ᵣ D} (α : F ⟶ G)
  证明: rfl

@[simp]
-/
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
/--
theorem `ExactFunctor.forget_map` / 定理 `ExactFunctor.forget_map`

English:
theorem ExactFunctor.forget_map
  given: {F G : C ⥤ₑ D} (α : F ⟶ G)
  proof: rfl

中文:
定理 ExactFunctor.forget_map
  条件: {F G : C ⥤ₑ D} (α : F ⟶ G)
  证明: rfl
-/
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (ExactFunctor.forget C D).map α = α.hom :=
  rfl

/--
Definition of `LeftExactFunctor.of` / `LeftExactFunctor.of` 的定义

English:
definition LeftExactFunctor.of
  signature: (F : C ⥤ D) [PreservesFiniteLimits F]
  body: ⟨F, by simpa⟩

中文:
定义 LeftExactFunctor.of
  签名: (F : C ⥤ D) [保持FiniteLimits F]
  定义体: ⟨F, by simpa⟩
-/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, by simpa⟩

/--
Definition of `RightExactFunctor.of` / `RightExactFunctor.of` 的定义

English:
definition RightExactFunctor.of
  signature: (F : C ⥤ D) [PreservesFiniteColimits F]
  body: ⟨F, by simpa⟩

中文:
定义 RightExactFunctor.of
  签名: (F : C ⥤ D) [保持FiniteColimits F]
  定义体: ⟨F, by simpa⟩
-/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, by simpa⟩

/--
Definition of `ExactFunctor.of` / `ExactFunctor.of` 的定义

English:
definition ExactFunctor.of
  signature: (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  body: ⟨F, by simp only [exactFunctor_iff]; constructor <;> assumption⟩

@[simp]

中文:
定义 ExactFunctor.of
  签名: (F : C ⥤ D) [保持FiniteLimits F] [保持FiniteColimits F]
  定义体: ⟨F, by simp only [exactFunctor_iff]; constructor <;> assumption⟩

@[simp]

Depends on / 依赖: exactFunctor_iff
-/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, by simp only [exactFunctor_iff]; constructor <;> assumption⟩

@[simp]
/--
theorem `LeftExactFunctor.of_fst` / 定理 `LeftExactFunctor.of_fst`

English:
theorem LeftExactFunctor.of_fst
  given: (F : C ⥤ D) [PreservesFiniteLimits F]
  proof: rfl

@[simp]

中文:
定理 LeftExactFunctor.of_fst
  条件: (F : C ⥤ D) [保持FiniteLimits F]
  证明: rfl

@[simp]
-/
theorem LeftExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.of F).obj = F :=
  rfl

@[simp]
/--
theorem `RightExactFunctor.of_fst` / 定理 `RightExactFunctor.of_fst`

English:
theorem RightExactFunctor.of_fst
  given: (F : C ⥤ D) [PreservesFiniteColimits F]
  proof: rfl

@[simp]

中文:
定理 RightExactFunctor.of_fst
  条件: (F : C ⥤ D) [保持FiniteColimits F]
  证明: rfl

@[simp]
-/
theorem RightExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.of F).obj = F :=
  rfl

@[simp]
/--
theorem `ExactFunctor.of_fst` / 定理 `ExactFunctor.of_fst`

English:
theorem ExactFunctor.of_fst
  given: (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  proof: rfl

中文:
定理 ExactFunctor.of_fst
  条件: (F : C ⥤ D) [保持FiniteLimits F] [保持FiniteColimits F]
  证明: rfl
-/
theorem ExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj = F :=
  rfl

/--
theorem `LeftExactFunctor.forget_obj_of` / 定理 `LeftExactFunctor.forget_obj_of`

English:
theorem LeftExactFunctor.forget_obj_of
  given: (F : C ⥤ D) [PreservesFiniteLimits F]
  proof: rfl

中文:
定理 LeftExactFunctor.forget_obj_of
  条件: (F : C ⥤ D) [保持FiniteLimits F]
  证明: rfl
-/
theorem LeftExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F :=
  rfl

/--
theorem `RightExactFunctor.forget_obj_of` / 定理 `RightExactFunctor.forget_obj_of`

English:
theorem RightExactFunctor.forget_obj_of
  given: (F : C ⥤ D) [PreservesFiniteColimits F]
  proof: rfl

中文:
定理 RightExactFunctor.forget_obj_of
  条件: (F : C ⥤ D) [保持FiniteColimits F]
  证明: rfl
-/
theorem RightExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F :=
  rfl

/--
theorem `ExactFunctor.forget_obj_of` / 定理 `ExactFunctor.forget_obj_of`

English:
theorem ExactFunctor.forget_obj_of
  statement: (F : C ⥤ D) [PreservesFiniteLimits F]
  proof: rfl

中文:
定理 ExactFunctor.forget_obj_of
  结论: (F : C ⥤ D) [保持FiniteLimits F]
  证明: rfl
-/
theorem ExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F :=
  rfl

noncomputable instance (F : C ⥤ₗ D) : PreservesFiniteLimits F.obj :=
  F.property

noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2

variable {E : Type u₃} [Category.{v₃} E]

section

variable (C D E)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `LeftExactFunctor.whiskeringLeft` / `LeftExactFunctor.whiskeringLeft` 的定义

English:
definition LeftExactFunctor.whiskeringLeft
  signature: : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

中文:
定义 LeftExactFunctor.whiskeringLeft
  签名: : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringLeft, ObjectProperty, ObjectProperty.lift, forget, whiskeringLeft
-/
def LeftExactFunctor.whiskeringLeft : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `LeftExactFunctor.whiskeringRight` / `LeftExactFunctor.whiskeringRight` 的定义

English:
definition LeftExactFunctor.whiskeringRight
  signature: : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

中文:
定义 LeftExactFunctor.whiskeringRight
  签名: : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringRight, ObjectProperty, ObjectProperty.lift, forget, whiskeringRight
-/
def LeftExactFunctor.whiskeringRight : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `RightExactFunctor.whiskeringLeft` / `RightExactFunctor.whiskeringLeft` 的定义

English:
definition RightExactFunctor.whiskeringLeft
  signature: : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

中文:
定义 RightExactFunctor.whiskeringLeft
  签名: : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringLeft, ObjectProperty, ObjectProperty.lift, forget, whiskeringLeft
-/
def RightExactFunctor.whiskeringLeft : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `RightExactFunctor.whiskeringRight` / `RightExactFunctor.whiskeringRight` 的定义

English:
definition RightExactFunctor.whiskeringRight
  signature: : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

中文:
定义 RightExactFunctor.whiskeringRight
  签名: : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringRight, ObjectProperty, ObjectProperty.lift, forget, whiskeringRight
-/
def RightExactFunctor.whiskeringRight : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `ExactFunctor.whiskeringLeft` / `ExactFunctor.whiskeringLeft` 的定义

English:
definition ExactFunctor.whiskeringLeft
  signature: : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

中文:
定义 ExactFunctor.whiskeringLeft
  签名: : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringLeft, ObjectProperty, ObjectProperty.lift, forget, whiskeringLeft
-/
def ExactFunctor.whiskeringLeft : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
/--
Definition of `ExactFunctor.whiskeringRight` / `ExactFunctor.whiskeringRight` 的定义

English:
definition ExactFunctor.whiskeringRight
  signature: : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  body: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

中文:
定义 ExactFunctor.whiskeringRight
  签名: : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  定义体: ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

Depends on / 依赖: F.obj, Functor, Functor.whiskeringRight, ObjectProperty, ObjectProperty.lift, forget, whiskeringRight
-/
def ExactFunctor.whiskeringRight : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

end

end

end CategoryTheory
