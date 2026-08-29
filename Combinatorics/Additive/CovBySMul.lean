/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Relation of covering by cosets

This file defines a predicate for a set to be covered by at most `K` cosets of another set.

This is a fundamental relation to study in additive combinatorics.
-/

@[expose] public section

open scoped Finset Pointwise

variable {M N X : Type*} [Monoid M] [Monoid N] [MulAction M X] [MulAction N X] {K L : Real}
  {A A₁ A₂ B B₁ B₂ C : Set X}

variable (M) in
/-- Predicate for a set `A` to be covered by at most `K` cosets of another set `B` under the action
by the monoid `M`. -/
@[to_additive /-- Predicate for a set `A` to be covered by at most `K` cosets of another set `B`
under the action by the monoid `M`. -/]
/--
Definition of `CovBySMul` / `CovBySMul` 的定义

English:
definition CovBySMul
  signature: (K : Real) (A B : Set X)
  body: exists F : Finset M, #F <= K ∧ A subseteq (F : Set M) • B

@[to_additive (attr := simp, refl)]

中文:
定义 CovBySMul
  签名: (K : 实数) (A B : Set X)
  定义体: exists F : Finset M, #F <= K ∧ A subseteq (F : Set M) • B

@[to_additive (attr := simp, refl)]

Depends on / 依赖: Finset, subseteq
-/
def CovBySMul (K : Real) (A B : Set X) : Prop := exists F : Finset M, #F <= K ∧ A subseteq (F : Set M) • B

@[to_additive (attr := simp, refl)]
/--
lemma `CovBySMul.rfl` / 引理 `CovBySMul.rfl`

English:
lemma CovBySMul.rfl
  statement: CovBySMul M 1 A A
  proof: ⟨1, by simp⟩

@[to_additive (attr := simp)]

中文:
引理 CovBySMul.rfl
  结论: CovBySMul M 1 A A
  证明: ⟨1, by simp⟩

@[to_additive (attr := simp)]
-/
lemma CovBySMul.rfl : CovBySMul M 1 A A := ⟨1, by simp⟩

@[to_additive (attr := simp)]
/--
lemma `CovBySMul.of_subset` / 引理 `CovBySMul.of_subset`

English:
lemma CovBySMul.of_subset
  given: (hAB : A subseteq B)
  statement: CovBySMul M 1 A B
  proof: ⟨1, by simpa⟩

中文:
引理 CovBySMul.of_subset
  条件: (hAB : A subseteq B)
  结论: CovBySMul M 1 A B
  证明: ⟨1, by simpa⟩
-/
lemma CovBySMul.of_subset (hAB : A subseteq B) : CovBySMul M 1 A B := ⟨1, by simpa⟩

/--
lemma `CovBySMul.nonneg` / 引理 `CovBySMul.nonneg`

English:
lemma CovBySMul.nonneg
  statement: CovBySMul M K A B -> 0 <= K
  proof: by
  rintro ⟨F, hF, -⟩; exact (#F).cast_nonneg.trans hF

@[to_additive (attr := simp)]

中文:
引理 CovBySMul.nonneg
  结论: CovBySMul M K A B -> 0 <= K
  证明: by
  rintro ⟨F, hF, -⟩; exact (#F).cast_nonneg.trans hF

@[to_additive (attr := simp)]
-/
@[to_additive] lemma CovBySMul.nonneg : CovBySMul M K A B -> 0 <= K := by
  rintro ⟨F, hF, -⟩; exact (#F).cast_nonneg.trans hF

@[to_additive (attr := simp)]
/--
lemma `covBySMul_zero` / 引理 `covBySMul_zero`

English:
lemma covBySMul_zero
  statement: CovBySMul M 0 A B ↔ A = ∅
  proof: by simp [CovBySMul]

@[to_additive]

中文:
引理 covBySMul_zero
  结论: CovBySMul M 0 A B ↔ A = ∅
  证明: by simp [CovBySMul]

@[to_additive]

Depends on / 依赖: CovBySMul
-/
lemma covBySMul_zero : CovBySMul M 0 A B ↔ A = ∅ := by simp [CovBySMul]

@[to_additive]
/--
lemma `CovBySMul.mono` / 引理 `CovBySMul.mono`

English:
lemma CovBySMul.mono
  given: (hKL : K <= L)
  statement: CovBySMul M K A B -> CovBySMul M L A B
  proof: by
  rintro ⟨F, hF, hFAB⟩; exact ⟨F, hF.trans hKL, hFAB⟩

中文:
引理 CovBySMul.mono
  条件: (hKL : K <= L)
  结论: CovBySMul M K A B -> CovBySMul M L A B
  证明: by
  rintro ⟨F, hF, hFAB⟩; exact ⟨F, hF.trans hKL, hFAB⟩

Depends on / 依赖: hF.trans
-/
lemma CovBySMul.mono (hKL : K <= L) : CovBySMul M K A B -> CovBySMul M L A B := by
  rintro ⟨F, hF, hFAB⟩; exact ⟨F, hF.trans hKL, hFAB⟩

/--
lemma `CovBySMul.trans` / 引理 `CovBySMul.trans`

English:
lemma CovBySMul.trans
  statement: [SMul M N] [IsScalarTower M N X]
  proof: by
  classical
  have := hAB.nonneg
  obtain ⟨F₁, hF₁, hFAB⟩ := hAB
  obtain ⟨F₂, hF₂, hFBC⟩ := hBC
  refine ⟨F₁ • F₂, ?_, ?_⟩
  · calc
      (#(F₁ • F₂) : Real) <= #F₁ * #F₂ := mod_cast Finset.card_smul_le
      _ <= K * L := by gcongr
  · calc
      A subseteq (F₁ : Set M) • B := hFAB
      _ subs

中文:
引理 CovBySMul.trans
  结论: [SMul M N] [IsScalarTower M N X]
  证明: by
  classical
  have := hAB.nonneg
  obtain ⟨F₁, hF₁, hFAB⟩ := hAB
  obtain ⟨F₂, hF₂, hFBC⟩ := hBC
  refine ⟨F₁ • F₂, ?_, ?_⟩
  · calc
      (#(F₁ • F₂) : Real) <= #F₁ * #F₂ := mod_cast Finset.card_smul_le
      _ <= K * L := by gcongr
  · calc
      A subseteq (F₁ : Set M) • B := hFAB
      _ subs
-/
@[to_additive] lemma CovBySMul.trans [SMul M N] [IsScalarTower M N X]
    (hAB : CovBySMul M K A B) (hBC : CovBySMul N L B C) : CovBySMul N (K * L) A C := by
  classical
  have := hAB.nonneg
  obtain ⟨F₁, hF₁, hFAB⟩ := hAB
  obtain ⟨F₂, hF₂, hFBC⟩ := hBC
  refine ⟨F₁ • F₂, ?_, ?_⟩
  · calc
      (#(F₁ • F₂) : Real) <= #F₁ * #F₂ := mod_cast Finset.card_smul_le
      _ <= K * L := by gcongr
  · calc
      A subseteq (F₁ : Set M) • B := hFAB
      _ subseteq (F₁ : Set M) • (F₂ : Set N) • C := by gcongr
      _ = (↑(F₁ • F₂) : Set N) • C := by simp

@[to_additive]
/--
lemma `CovBySMul.subset_left` / 引理 `CovBySMul.subset_left`

English:
lemma CovBySMul.subset_left
  given: (hA : A₁ subseteq A₂) (hAB : CovBySMul M K A₂ B)
  proof: by simpa using (CovBySMul.of_subset (M := M) hA).trans hAB

@[to_additive]

中文:
引理 CovBySMul.subset_left
  条件: (hA : A₁ subseteq A₂) (hAB : CovBySMul M K A₂ B)
  证明: by simpa using (CovBySMul.of_subset (M := M) hA).trans hAB

@[to_additive]

Depends on / 依赖: CovBySMul, CovBySMul.of_subset, of_subset
-/
lemma CovBySMul.subset_left (hA : A₁ subseteq A₂) (hAB : CovBySMul M K A₂ B) :
    CovBySMul M K A₁ B := by simpa using (CovBySMul.of_subset (M := M) hA).trans hAB

@[to_additive]
/--
lemma `CovBySMul.subset_right` / 引理 `CovBySMul.subset_right`

English:
lemma CovBySMul.subset_right
  given: (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A B₁)
  proof: by simpa using hAB.trans (.of_subset (M := M) hB)

@[to_additive]

中文:
引理 CovBySMul.subset_right
  条件: (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A B₁)
  证明: by simpa using hAB.trans (.of_subset (M := M) hB)

@[to_additive]

Depends on / 依赖: hAB.trans, of_subset
-/
lemma CovBySMul.subset_right (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A B₁) :
    CovBySMul M K A B₂ := by simpa using hAB.trans (.of_subset (M := M) hB)

@[to_additive]
/--
lemma `CovBySMul.subset` / 引理 `CovBySMul.subset`

English:
lemma CovBySMul.subset
  given: (hA : A₁ subseteq A₂) (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A₂ B₁)
  proof: (hAB.subset_left hA).subset_right hB

中文:
引理 CovBySMul.subset
  条件: (hA : A₁ subseteq A₂) (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A₂ B₁)
  证明: (hAB.subset_left hA).subset_right hB

Depends on / 依赖: hAB.subset_left, subset_left, subset_right
-/
lemma CovBySMul.subset (hA : A₁ subseteq A₂) (hB : B₁ subseteq B₂) (hAB : CovBySMul M K A₂ B₁) :
    CovBySMul M K A₁ B₂ := (hAB.subset_left hA).subset_right hB
