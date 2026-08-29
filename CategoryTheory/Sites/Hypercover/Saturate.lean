/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Homotopy
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Saturation of a `0`-hypercover

Given a `0`-hypercover `E`, we define a `1`-hypercover `E.saturate`
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

variable {C : Type*} [Category* C] {A : Type*} [Category* A]

open Limits

/--
Definition of `Relation` / `Relation` 的定义

English:
structure Relation
  parameters: {S : C} (E : PreZeroHypercover S) (i j : E.I₀)
  axioms and operations (4):
    - obj : C
    - fst : obj ⟶ E.X i
    - snd : obj ⟶ E.X j
    - w : fst ≫ E.f i = snd ≫ E.f j

中文:
结构 Relation
  参数: {S : C} (E : PreZeroHypercover S) (i j : E.I₀)
  公理与运算 (4 个):
    - obj : C
    - fst : obj ⟶ E.X i
    - snd : obj ⟶ E.X j
    - w : fst ≫ E.f i = snd ≫ E.f j
-/
structure Relation {S : C} (E : PreZeroHypercover S) (i j : E.I₀) where
  /-- The object. -/
  obj : C
  /-- The first projection. -/
  fst : obj ⟶ E.X i
  /-- The second projection. -/
  snd : obj ⟶ E.X j
  w : fst ≫ E.f i = snd ≫ E.f j

/-- The maximal pre-`1`-hypercover containing `E`, where the `1`-components are all relations
on `E`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/--
Definition of `saturate` / `saturate` 的定义

English:
definition saturate
  signature: {S : C} (E : PreZeroHypercover S)
  body: E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w

中文:
定义 saturate
  签名: {S : C} (E : PreZeroHypercover S)
  定义体: E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w
-/
def saturate {S : C} (E : PreZeroHypercover S) : PreOneHypercover S where
  __ := E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w

/-- For a presheaf of types, sections over the multifork associated to `E.saturate` are equivalent
to compatible families. -/
@[simps]
/--
Definition of `sectionsSaturateEquiv` / `sectionsSaturateEquiv` 的定义

English:
definition sectionsSaturateEquiv
  signature: {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*)
  body: ⟨s.val, fun i j _ _ _ hgij => s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 sectionsSaturateEquiv
  签名: {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ 类型)
  定义体: ⟨s.val, fun i j _ _ _ hgij => s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: DecidableRel, property, s.property, s.val
-/
def sectionsSaturateEquiv {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    (E.saturate.multicospanIndex F).sections ≃ Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s := ⟨s.val, fun i j _ _ _ hgij => s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `isLimit_saturate_type_iff` / 引理 `isLimit_saturate_type_iff`

English:
lemma isLimit_saturate_type_iff
  given: {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*)
  proof: by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

中文:
引理 isLimit_saturate_type_iff
  条件: {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ 类型)
  证明: by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

Depends on / 依赖: Bijective, E.sectionsSaturateEquiv, Function, Function.Bijective.of_comp_iff, Multifork, Multifork.isLimit_types_iff, Presieve, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible, bijective, isLimit_types_iff, isSheafFor_ofArrows_iff_bijective_toCompabible, of_comp_iff, sectionsSaturateEquiv, symm.bijective
-/
lemma isLimit_saturate_type_iff {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.saturate.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `E` has pairwise pullbacks, this is the canonical map from the minimal `1`-hypercover
to the saturation. -/
@[simps]
noncomputable
/--
Definition of `toSaturateOfHasPullbacks` / `toSaturateOfHasPullbacks` 的定义

English:
definition toSaturateOfHasPullbacks
  signature: {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
  body: i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _

中文:
定义 toSaturateOfHasPullbacks
  签名: {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
  定义体: i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _
-/
def toSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover ⟶ E.saturate where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- If `E` has pairwise pullbacks, this is the canonical map to the minimal `1`-hypercover
from the saturation. -/
@[simps]
noncomputable
/--
Definition of `fromSaturateOfHasPullbacks` / `fromSaturateOfHasPullbacks` 的定义

English:
definition fromSaturateOfHasPullbacks
  signature: {S : C} (E : PreZeroHypercover S)
  body: i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w

中文:
定义 fromSaturateOfHasPullbacks
  签名: {S : C} (E : PreZeroHypercover S)
  定义体: i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w
-/
def fromSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] : E.saturate ⟶ E.toPreOneHypercover where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The identity of the minimal pre-`1`-hypercover when `E` has pairwise pullbacks
is homotopic to itself. -/
noncomputable
/--
Definition of `toPreOneHypercoverHomotopy` / `toPreOneHypercoverHomotopy` 的定义

English:
definition toPreOneHypercoverHomotopy
  signature: {S : C} (E : PreZeroHypercover S)
  body: ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

中文:
定义 toPreOneHypercoverHomotopy
  签名: {S : C} (E : PreZeroHypercover S)
  定义体: ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

Depends on / 依赖: G.adj_symm, adj_symm
-/
def toPreOneHypercoverHomotopy {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover.Homotopy (.id E.toPreOneHypercover) (.id E.toPreOneHypercover) where
  H _ := ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks` / 引理 `toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks`

English:
lemma toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks
  proof: by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

中文:
引理 toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks
  证明: by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

Depends on / 依赖: PreOneHypercover, PreOneHypercover.Hom.ext
-/
lemma toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks :
    E.toSaturateOfHasPullbacks.comp E.fromSaturateOfHasPullbacks = .id _ := by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The composition `E.saturate ⟶ E.toPreOneHypercover ⟶ E.saturate` is homotopic to the
identity. -/
noncomputable
/--
Definition of `fromSaturateToSaturateHomotopy` / `fromSaturateToSaturateHomotopy` 的定义

English:
definition fromSaturateToSaturateHomotopy
  signature: : PreOneHypercover.Homotopy
  body: ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

中文:
定义 fromSaturateToSaturateHomotopy
  签名: : PreOneHypercover.Homotopy
  定义体: ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

Depends on / 依赖: condition, pullback, pullback.condition, pullback.fst, pullback.snd
-/
def fromSaturateToSaturateHomotopy : PreOneHypercover.Homotopy
    (E.fromSaturateOfHasPullbacks.comp E.toSaturateOfHasPullbacks) (.id _) where
  H i := ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, then the multifork associated to the
full saturated pre-`1`-hypercover is exact if and only if the minimal one given by taking
the pairwise pullbacks is exact. -/
noncomputable
/--
Definition of `isLimitSaturateEquivOfHasPullbacks` / `isLimitSaturateEquivOfHasPullbacks` 的定义

English:
definition isLimitSaturateEquivOfHasPullbacks
  signature: {S : C} (E : PreZeroHypercover S)
  body: PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

中文:
定义 isLimitSaturateEquivOfHasPullbacks
  签名: {S : C} (E : PreZeroHypercover S)
  定义体: PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

Depends on / 依赖: E.fromSaturateOfHasPullbacks, E.fromSaturateToSaturateHomotopy, E.toPreOneHypercoverHomotopy, E.toSaturateOfHasPullbacks, Homotopy, PreOneHypercover, PreOneHypercover.Homotopy.isLimitMultiforkEquiv, fromSaturateOfHasPullbacks, fromSaturateToSaturateHomotopy, isLimitMultiforkEquiv, toPreOneHypercoverHomotopy, toSaturateOfHasPullbacks, toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks
-/
def isLimitSaturateEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ A) :
    IsLimit (E.saturate.multifork F) ≃ IsLimit (E.toPreOneHypercover.multifork F) :=
  PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

end CategoryTheory.PreZeroHypercover
