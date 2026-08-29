/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Quasicategories

In this file we define quasicategories,
a common model of infinity categories.
We show that every Kan complex is a quasicategory.

In `Mathlib/AlgebraicTopology/Quasicategory/Nerve.lean`,
we show that the nerve of a category is a quasicategory.

## TODO

- Generalize the definition to higher universes.
  See the corresponding TODO in
  `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex.lean`.

-/

public section

namespace SSet

open CategoryTheory Simplicial

/-- A simplicial set `S` is a *quasicategory* if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.
-/
@[kerodon 003A]
/--
Definition of `Quasicategory` / `Quasicategory` 的定义

English:
class Quasicategory
  parameters: (S : SSet)
  axioms and operations (1):
    - hornFilling' : forall ⦃n : Nat⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)), exists σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

中文:
类 拟范畴
  参数: (S : SSet)
  公理与运算 (1 个):
    - hornFilling' : 对任意 ⦃n : 自然数⦄ ⦃i : 有限集 (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S) (_h0 : 0 < i) (_hn : i < 有限集.last (n + 2)), 存在 σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ
-/
class Quasicategory (S : SSet) : Prop where
  hornFilling' : forall ⦃n : Nat⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
    (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      exists σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

/--
lemma `Quasicategory.hornFilling` / 引理 `Quasicategory.hornFilling`

English:
lemma Quasicategory.hornFilling
  given: {S : SSet} [Quasicategory S] ⦃n
  statement: Nat⦄ ⦃i : Fin (n + 1)⦄
  proof: by
  match n with
  | 0
  | 1 => lia
  | n + 2 => exact Quasicategory.hornFilling' σ₀ h0 hn

中文:
引理 拟范畴.hornFilling
  条件: {S : SSet} [拟范畴 S] ⦃n
  结论: 自然数⦄ ⦃i : 有限集 (n + 1)⦄
  证明: by
  match n with
  | 0
  | 1 => lia
  | n + 2 => exact Quasicategory.hornFilling' σ₀ h0 hn

Depends on / 依赖: Quasicategory, Quasicategory.hornFilling, hornFilling
-/
lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : Nat⦄ ⦃i : Fin (n + 1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : (Λ[n, i] : SSet) ⟶ S) : exists σ : Δ[n] ⟶ S, σ₀ = Λ[n, i].ι ≫ σ := by
  match n with
  | 0
  | 1 => lia
  | n + 2 => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory. -/
@[kerodon 003C]
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

/--
lemma `quasicategory_of_filler` / 引理 `quasicategory_of_filler`

English:
lemma quasicategory_of_filler
  statement: (S : SSet)
  proof: by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj]; rw [NatTrans.comp_app]
    rfl

中文:
引理 quasicategory_of_filler
  结论: (S : SSet)
  证明: by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj]; rw [NatTrans.comp_app]
    rfl

Depends on / 依赖: NatTrans, NatTrans.comp_app, comp_app, filler, hom_ext, horn.hom_ext, yonedaEquiv, yonedaEquiv.symm
-/
lemma quasicategory_of_filler (S : SSet)
    (filler : forall ⦃n : Nat⦄ ⦃i : Fin (n + 3)⦄ (σ₀ : (Λ[n + 2, i] : SSet) ⟶ S)
      (_h0 : 0 < i) (_hn : i < Fin.last (n + 2)),
      exists σ : S _⦋n + 2⦌, forall (j) (h : j != i), S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := filler σ₀ h₀ hₙ
    refine ⟨yonedaEquiv.symm σ, ?_⟩
    apply horn.hom_ext
    intro j hj
    rw [← h j hj]; rw [NatTrans.comp_app]
    rfl

/--
lemma `quasicategory_of_hasLiftingProperty` / 引理 `quasicategory_of_hasLiftingProperty`

English:
lemma quasicategory_of_hasLiftingProperty
  statement: (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
  proof: let := h h0 hn
    ⟨(CommSq.mk (t.hom_ext (σ₀ ≫ t.from S) (Λ[n + 2, i].ι ≫ t.from Δ[n + 2]))).lift, by simp⟩

中文:
引理 quasicategory_of_hasLiftingProperty
  结论: (S : SSet) {X : SSet} (t : Limits.是终止 X)
  证明: let := h h0 hn
    ⟨(CommSq.mk (t.hom_ext (σ₀ ≫ t.from S) (Λ[n + 2, i].ι ≫ t.from Δ[n + 2]))).lift, by simp⟩

Depends on / 依赖: CommSq, CommSq.mk, hom_ext, t.from, t.hom_ext
-/
lemma quasicategory_of_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : forall {n : Nat} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S)) :
    Quasicategory S where
  hornFilling' n i σ₀ h0 hn :=
    let := h h0 hn
    ⟨(CommSq.mk (t.hom_ext (σ₀ ≫ t.from S) (Λ[n + 2, i].ι ≫ t.from Δ[n + 2]))).lift, by simp⟩

/--
lemma `Quasicategory.hasLiftingProperty` / 引理 `Quasicategory.hasLiftingProperty`

English:
lemma Quasicategory.hasLiftingProperty
  statement: (S : SSet) [Quasicategory S] {X : SSet}
  proof: ⟨(hornFilling h0 hn _).choose, (hornFilling h0 hn _).choose_spec.symm, t.hom_ext _ _⟩

中文:
引理 拟范畴.hasLiftingProperty
  结论: (S : SSet) [拟范畴 S] {X : SSet}
  证明: ⟨(hornFilling h0 hn _).choose, (hornFilling h0 hn _).choose_spec.symm, t.hom_ext _ _⟩

Depends on / 依赖: choose_spec, choose_spec.symm, hom_ext, hornFilling, t.hom_ext
-/
lemma Quasicategory.hasLiftingProperty (S : SSet) [Quasicategory S] {X : SSet}
    (t : Limits.IsTerminal X) {n : Nat} {i : Fin (n + 1)} (h0 : 0 < i) (hn : i < Fin.last n) :
    HasLiftingProperty Λ[n, i].ι (t.from S) where
  sq_hasLift _ :=
    ⟨(hornFilling h0 hn _).choose, (hornFilling h0 hn _).choose_spec.symm, t.hom_ext _ _⟩

/--
lemma `quasicategory_iff_hasLiftingProperty` / 引理 `quasicategory_iff_hasLiftingProperty`

English:
lemma quasicategory_iff_hasLiftingProperty
  given: (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
  proof: ⟨fun _ => Quasicategory.hasLiftingProperty S t, quasicategory_of_hasLiftingProperty S t⟩

中文:
引理 quasicategory_iff_hasLiftingProperty
  条件: (S : SSet) {X : SSet} (t : Limits.是终止 X)
  证明: ⟨fun _ => Quasicategory.hasLiftingProperty S t, quasicategory_of_hasLiftingProperty S t⟩

Depends on / 依赖: Quasicategory, Quasicategory.hasLiftingProperty, hasLiftingProperty, quasicategory_of_hasLiftingProperty
-/
lemma quasicategory_iff_hasLiftingProperty (S : SSet) {X : SSet} (t : Limits.IsTerminal X) :
    Quasicategory S ↔ forall {n : Nat} {i : Fin (n + 1)} (_ : 0 < i) (_ : i < Fin.last n),
      HasLiftingProperty Λ[n, i].ι (t.from S) :=
  ⟨fun _ => Quasicategory.hasLiftingProperty S t, quasicategory_of_hasLiftingProperty S t⟩

end SSet
