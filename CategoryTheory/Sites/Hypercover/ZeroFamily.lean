/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Defining precoverages via pre-`0`-hypercovers

A precoverage is a condition on all presieves. In some applications, it is practical
to instead define a condition on all pre-`0`-hypercovers. Such a condition
for every object is a pre-`0`-hypercover family if these conditions are
invariant under deduplication.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]

variable (C) in
/--
A pre-`0`-hypercover family on `C` is a property on the category of pre-`0`-hypercovers
for every `X : C` that is invariant under deduplication.
The data of a pre-`0`-hypercover family is the same as the data of a precoverage
(see: `Precoverage.equivPreZeroHypercoverFamily`).
-/
@[ext]
/--
Definition of `PreZeroHypercoverFamily` / `PreZeroHypercoverFamily` 的定义

English:
structure PreZeroHypercoverFamily
  parameters: where
  axioms and operations (2):
    - property(⦃X) : C⦄ : ObjectProperty (PreZeroHypercover.{max u v} X)
    - iff_shrink({X : C} {E : PreZeroHypercover.{max u v} X}) : property E ↔ property E.shrink

中文:
结构 PreZeroHypercoverFamily
  参数: where
  公理与运算 (2 个):
    - property(⦃X) : C⦄ : ObjectProperty (PreZeroHypercover.{最大值 u v} X)
    - iff_shrink({X : C} {E : PreZeroHypercover.{最大值 u v} X}) : property E ↔ property E.shrink
-/
structure PreZeroHypercoverFamily where
  /-- The condition on pre-`0`-hypercovers for every object. -/
  property ⦃X : C⦄ : ObjectProperty (PreZeroHypercover.{max u v} X)
  iff_shrink {X : C} {E : PreZeroHypercover.{max u v} X} : property E ↔ property E.shrink

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (PreZeroHypercoverFamily C)
  body: P.property

中文:
实例 :
  签名: CoeFun (PreZeroHypercoverFamily C)
  定义体: P.property

Depends on / 依赖: P.property, property
-/
instance : CoeFun (PreZeroHypercoverFamily C)
    fun _ => ⦃X : C⦄ -> (E : PreZeroHypercover.{max u v} X) -> Prop where
  coe P := P.property

/--
Inductive type `PreZeroHypercoverFamily.presieve` / 归纳类型 `PreZeroHypercoverFamily.presieve`

English:
inductive PreZeroHypercoverFamily.presieve
  parameters: (P : PreZeroHypercoverFamily C) {X : C}
  constructors (1):
    - mk: (E : PreZeroHypercover.{max u v} X) : P E -> presieve P E.presieve₀

中文:
归纳类型 PreZeroHypercoverFamily.presieve
  参数: (P : PreZeroHypercoverFamily C) {X : C}
  构造子 (1 个):
    - mk: (E : PreZeroHypercover.{最大值 u v} X) : P E -> presieve P E.presieve₀
-/
inductive PreZeroHypercoverFamily.presieve (P : PreZeroHypercoverFamily C) {X : C} :
    Presieve X -> Prop where
  | mk (E : PreZeroHypercover.{max u v} X) : P E -> presieve P E.presieve₀

/--
Definition of `PreZeroHypercoverFamily.precoverage` / `PreZeroHypercoverFamily.precoverage` 的定义

English:
definition PreZeroHypercoverFamily.precoverage
  signature: (P : PreZeroHypercoverFamily C)
  body: {R | P.presieve R}

中文:
定义 PreZeroHypercoverFamily.precoverage
  签名: (P : PreZeroHypercoverFamily C)
  定义体: {R | P.presieve R}

Depends on / 依赖: P.presieve, presieve
-/
def PreZeroHypercoverFamily.precoverage (P : PreZeroHypercoverFamily C) :
    Precoverage C where
  coverings _ := {R | P.presieve R}

/--
lemma `PreZeroHypercoverFamily.mem_precoverage_iff` / 引理 `PreZeroHypercoverFamily.mem_precoverage_iff`

English:
lemma PreZeroHypercoverFamily.mem_precoverage_iff
  statement: {P : PreZeroHypercoverFamily C} {X : C}
  proof: ⟨fun ⟨E, hE⟩ => ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ => h ▸ ⟨_, hE⟩⟩

@[simp]

中文:
引理 PreZeroHypercoverFamily.mem_precoverage_iff
  结论: {P : PreZeroHypercoverFamily C} {X : C}
  证明: ⟨fun ⟨E, hE⟩ => ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ => h ▸ ⟨_, hE⟩⟩

@[simp]
-/
lemma PreZeroHypercoverFamily.mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {R : Presieve X} :
    R in P.precoverage X ↔ exists (E : PreZeroHypercover.{max u v} X), P E ∧ R = E.presieve₀ :=
  ⟨fun ⟨E, hE⟩ => ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ => h ▸ ⟨_, hE⟩⟩

@[simp]
/--
lemma `PreZeroHypercover.presieve₀_mem_precoverage_iff` / 引理 `PreZeroHypercover.presieve₀_mem_precoverage_iff`

English:
lemma PreZeroHypercover.presieve₀_mem_precoverage_iff
  statement: {P : PreZeroHypercoverFamily C} {X : C}
  proof: by
  refine ⟨fun h => ?_, fun h => .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

中文:
引理 PreZeroHypercover.presieve₀_mem_precoverage_iff
  结论: {P : PreZeroHypercoverFamily C} {X : C}
  证明: by
  refine ⟨fun h => ?_, fun h => .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

Depends on / 依赖: P.iff_shrink, PreZeroHypercover, PreZeroHypercover.shrink_eq_shrink_of_presieve, PreZeroHypercoverFamily, PreZeroHypercoverFamily.mem_precoverage_iff, iff_shrink, mem_precoverage_iff
-/
lemma PreZeroHypercover.presieve₀_mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {E : PreZeroHypercover.{max u v} X} :
    E.presieve₀ in P.precoverage X ↔ P E := by
  refine ⟨fun h => ?_, fun h => .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

/-- The associated pre-`0`-hypercover family to a precoverage. -/
@[simps]
/--
Definition of `Precoverage.preZeroHypercoverFamily` / `Precoverage.preZeroHypercoverFamily` 的定义

English:
definition Precoverage.preZeroHypercoverFamily
  signature: (K : Precoverage C)
  body: E.presieve₀ in K X
  iff_shrink {X} E := by simp

中文:
定义 Precoverage.preZeroHypercoverFamily
  签名: (K : Precoverage C)
  定义体: E.presieve₀ in K X
  iff_shrink {X} E := by simp

Depends on / 依赖: E.presieve
-/
def Precoverage.preZeroHypercoverFamily (K : Precoverage C) :
    PreZeroHypercoverFamily C where
  property X E := E.presieve₀ in K X
  iff_shrink {X} E := by simp

variable (C) in
/--
Definition of `Precoverage.equivPreZeroHypercoverFamily` / `Precoverage.equivPreZeroHypercoverFamily` 的定义

English:
definition Precoverage.equivPreZeroHypercoverFamily
  signature: :
  body: K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch

中文:
定义 Precoverage.equivPreZeroHypercoverFamily
  签名: :
  定义体: K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch

Depends on / 依赖: K.preZeroHypercoverFamily, preZeroHypercoverFamily
-/
def Precoverage.equivPreZeroHypercoverFamily :
    Precoverage C ≃ PreZeroHypercoverFamily C where
  toFun K := K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch

/--
lemma `Precoverage.HasIsos.of_preZeroHypercoverFamily` / 引理 `Precoverage.HasIsos.of_preZeroHypercoverFamily`

English:
lemma Precoverage.HasIsos.of_preZeroHypercoverFamily
  statement: {P : PreZeroHypercoverFamily C}
  proof: by
    rw [← PreZeroHypercover.presieve₀_singleton.{_]; rw [_]; rw [max u v}]
    refine .mk _ (h _)

中文:
引理 Precoverage.有是os.of_preZeroHypercoverFamily
  结论: {P : PreZeroHypercoverFamily C}
  证明: by
    rw [← PreZeroHypercover.presieve₀_singleton.{_]; rw [_]; rw [max u v}]
    refine .mk _ (h _)

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.presieve
-/
lemma Precoverage.HasIsos.of_preZeroHypercoverFamily {P : PreZeroHypercoverFamily C}
    (h : forall ⦃X Y : C⦄ (f : X ⟶ Y) [IsIso f], P (.singleton f)) :
    P.precoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf := by
    rw [← PreZeroHypercover.presieve₀_singleton.{_]; rw [_]; rw [max u v}]
    refine .mk _ (h _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms` / 引理 `Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms`

English:
lemma Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
  proof: by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i => (h i).isoPullback)
    change F.presieve₀ in _
    rw [F.presieve₀_mem_precoverage_iff]; rw [(P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]

中文:
引理 Precoverage.是StableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
  证明: by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i => (h i).isoPullback)
    change F.presieve₀ in _
    rw [F.presieve₀_mem_precoverage_iff]; rw [(P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
lemma Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
    {P : PreZeroHypercoverFamily C}
    (h₁ : forall {X : C}, (P (X := X)).IsClosedUnderIsomorphisms)
    (h₂ : forall {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{max u v} Y)
      [forall (i : E.I₀), HasPullback f (E.f i)], P E -> P (E.pullback₁ f)) :
    Precoverage.IsStableUnderBaseChange P.precoverage where
  mem_coverings_of_isPullback {ι} S X f hf Y g Z p₁ p₂ h := by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i => (h i).isoPullback)
    change F.presieve₀ in _
    rw [F.presieve₀_mem_precoverage_iff]; rw [(P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]

/--
lemma `Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily` / 引理 `Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily`

English:
lemma Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
  proof: by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i => ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i

中文:
引理 Precoverage.是StableUnderComposition.of_preZeroHypercoverFamily
  证明: by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i => ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i

Depends on / 依赖: E.bind, E.presieve, PreZeroHypercover, _mem_precoverage_iff.mpr
-/
lemma Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : forall {X : C} (E : PreZeroHypercover.{max u v} X)
      (F : forall i, PreZeroHypercover.{max u v} (E.X i)),
      P E -> (forall i, P (F i)) -> P (E.bind F)) :
    Precoverage.IsStableUnderComposition P.precoverage where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i => ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i

/--
lemma `Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily` / 引理 `Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily`

English:
lemma Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily
  proof: by
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    obtain ⟨F, rfl⟩ := S.exists_eq_preZeroHypercover
    rw [← PreZeroHypercover.presieve₀_sum]
    rw [PreZeroHypercover.presieve₀_mem_precoverage_iff] at hR hS ⊢
    exact h hR hS

中文:
引理 Precoverage.是StableUnderSup.of_preZeroHypercoverFamily
  证明: by
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    obtain ⟨F, rfl⟩ := S.exists_eq_preZeroHypercover
    rw [← PreZeroHypercover.presieve₀_sum]
    rw [PreZeroHypercover.presieve₀_mem_precoverage_iff] at hR hS ⊢
    exact h hR hS

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.presieve, R.exists_eq_preZeroHypercover, S.exists_eq_preZeroHypercover, exists_eq_preZeroHypercover
-/
lemma Precoverage.IsStableUnderSup.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : forall ⦃X : C⦄ ⦃E F : PreZeroHypercover.{max u v} X⦄,
      P E -> P F -> P (E.sum F)) :
    P.precoverage.IsStableUnderSup where
  sup_mem_coverings {X} R S hR hS := by
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    obtain ⟨F, rfl⟩ := S.exists_eq_preZeroHypercover
    rw [← PreZeroHypercover.presieve₀_sum]
    rw [PreZeroHypercover.presieve₀_mem_precoverage_iff] at hR hS ⊢
    exact h hR hS

end CategoryTheory
