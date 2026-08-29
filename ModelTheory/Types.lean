/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability

/-!
# Type Spaces

This file defines the space of complete types over a first-order theory.
(Note that types in model theory are different from types in type theory.)

## Main Definitions

- `FirstOrder.Language.Theory.CompleteType`:
  `T.CompleteType α` consists of complete types over the theory `T` with variables `α`.
- `FirstOrder.Language.Theory.typeOf` is the type of a given tuple.
- `FirstOrder.Language.Theory.realizedTypes`: `T.realizedTypes M α` is the set of
  types in `T.CompleteType α` that are realized in `M` - that is, the type of some tuple in `M`.

## Main Results

- `FirstOrder.Language.Theory.CompleteType.nonempty_iff`:
  The space `T.CompleteType α` is nonempty exactly when `T` is satisfiable.
- `FirstOrder.Language.Theory.CompleteType.exists_modelType_is_realized_in`: Every type is realized
  in some model.

## Implementation Notes

- Complete types are implemented as maximal consistent theories in an expanded language.
  More frequently they are described as maximal consistent sets of formulas, but this is equivalent.

## TODO

- Connect `T.CompleteType α` to sets of formulas `L.Formula α`.
-/

@[expose] public section



universe u v w w'

open Cardinal Set FirstOrder

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

/--
Definition of `CompleteType` / `CompleteType` 的定义

English:
structure CompleteType
  parameters: where
  axioms and operations (3):
    - toTheory : L[[α]].Theory
    - subset' : (L.lhomWithConstants α).onTheory T subseteq toTheory
    - isMaximal' : toTheory.IsMaximal

中文:
结构 CompleteType
  参数: where
  公理与运算 (3 个):
    - toTheory : L[[α]].Theory
    - subset' : (L.lhomWithConstants α).onTheory T subseteq toTheory
    - isMaximal' : toTheory.IsMaximal
-/
structure CompleteType where
  /-- The underlying theory -/
  toTheory : L[[α]].Theory
  subset' : (L.lhomWithConstants α).onTheory T subseteq toTheory
  isMaximal' : toTheory.IsMaximal

variable {α}

/--
Definition of `typesWith` / `typesWith` 的定义

English:
definition typesWith
  signature: (T : L.Theory)
  body: fun φ => {p | φ in p.toTheory}

中文:
定义 typesWith
  签名: (T : L.Theory)
  定义体: fun φ => {p | φ in p.toTheory}

Depends on / 依赖: p.toTheory, toTheory
-/
def typesWith (T : L.Theory) : L[[α]].Sentence -> Set (CompleteType T α) :=
  fun φ => {p | φ in p.toTheory}

variable {T}

namespace CompleteType

attribute [coe] CompleteType.toTheory

/--
Instance `Sentence.instSetLike` / 实例 `Sentence.instSetLike`

English:
instance Sentence.instSetLike
  signature: : SetLike (T.CompleteType α) L[[α]].Sentence
  body: ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩

中文:
实例 Sentence.instSetLike
  签名: : SetLike (T.CompleteType α) L[[α]].Sentence
  定义体: ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩

Depends on / 依赖: p.toTheory, toTheory
-/
instance Sentence.instSetLike : SetLike (T.CompleteType α) L[[α]].Sentence :=
  ⟨fun p => p.toTheory, fun p q h => by
    cases p
    cases q
    congr ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (T.CompleteType α)
  body: .ofSetLike (T.CompleteType α) (L[[α]].Sentence)

中文:
实例 :
  签名: PartialOrder (T.CompleteType α)
  定义体: .ofSetLike (T.CompleteType α) (L[[α]].Sentence)

Depends on / 依赖: CompleteType, Sentence, T.CompleteType, ofSetLike
-/
instance : PartialOrder (T.CompleteType α) := .ofSetLike (T.CompleteType α) (L[[α]].Sentence)

/--
theorem `isMaximal` / 定理 `isMaximal`

English:
theorem isMaximal
  given: (p : T.CompleteType α)
  statement: IsMaximal (p : L[[α]].Theory)
  proof: p.isMaximal'

中文:
定理 isMaximal
  条件: (p : T.CompleteType α)
  结论: IsMaximal (p : L[[α]].Theory)
  证明: p.isMaximal'

Depends on / 依赖: isMaximal, p.isMaximal
-/
theorem isMaximal (p : T.CompleteType α) : IsMaximal (p : L[[α]].Theory) :=
  p.isMaximal'

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (p : T.CompleteType α)
  statement: (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
  proof: p.subset'

中文:
定理 subset
  条件: (p : T.CompleteType α)
  结论: (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory)
  证明: p.subset'

Depends on / 依赖: p.subset, subset
-/
theorem subset (p : T.CompleteType α) : (L.lhomWithConstants α).onTheory T subseteq (p : L[[α]].Theory) :=
  p.subset'

/--
theorem `mem_or_not_mem` / 定理 `mem_or_not_mem`

English:
theorem mem_or_not_mem
  given: (p : T.CompleteType α) (φ : L[[α]].Sentence)
  statement: φ in p ∨ φ.not in p
  proof: p.isMaximal.mem_or_not_mem φ

中文:
定理 mem_or_not_mem
  条件: (p : T.CompleteType α) (φ : L[[α]].Sentence)
  结论: φ in p ∨ φ.not in p
  证明: p.isMaximal.mem_or_not_mem φ

Depends on / 依赖: isMaximal, mem_or_not_mem, p.isMaximal.mem_or_not_mem
-/
theorem mem_or_not_mem (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ in p ∨ φ.not in p :=
  p.isMaximal.mem_or_not_mem φ

/--
lemma `false_of_mem_of_not_mem` / 引理 `false_of_mem_of_not_mem`

English:
lemma false_of_mem_of_not_mem
  given: (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ in T) (hφ' : ∼φ in T)
  proof: have ⟨M⟩ := hT
  (M.is_model.realize_of_mem _ hφ') (M.is_model.realize_of_mem _ hφ)

中文:
引理 false_of_mem_of_not_mem
  条件: (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ in T) (hφ' : ∼φ in T)
  证明: have ⟨M⟩ := hT
  (M.is_model.realize_of_mem _ hφ') (M.is_model.realize_of_mem _ hφ)

Depends on / 依赖: M.is_model.realize_of_mem, is_model, realize_of_mem
-/
lemma false_of_mem_of_not_mem (hT : T.IsSatisfiable) {φ : L.Sentence} (hφ : φ in T) (hφ' : ∼φ in T) :
    False :=
  have ⟨M⟩ := hT
  (M.is_model.realize_of_mem _ hφ') (M.is_model.realize_of_mem _ hφ)

/--
theorem `mem_of_models` / 定理 `mem_of_models`

English:
theorem mem_of_models
  statement: (p : T.CompleteType α) {φ : L[[α]].Sentence}
  proof: (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))

中文:
定理 mem_of_models
  结论: (p : T.CompleteType α) {φ : L[[α]].Sentence}
  证明: (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))

Depends on / 依赖: isMaximal, mem_or_not_mem, models_iff_not_satisfiable, p.isMaximal, p.mem_or_not_mem, p.subset, resolve_right, singleton_subset_iff, subset, union_subset
-/
theorem mem_of_models (p : T.CompleteType α) {φ : L[[α]].Sentence}
    (h : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ) : φ in p :=
  (p.mem_or_not_mem φ).resolve_right fun con =>
    ((models_iff_not_satisfiable _).1 h)
      (p.isMaximal.1.mono (union_subset p.subset (singleton_subset_iff.2 con)))

/--
theorem `not_mem_iff` / 定理 `not_mem_iff`

English:
theorem not_mem_iff
  given: (p : T.CompleteType α) (φ : L[[α]].Sentence)
  statement: φ.not in p ↔ φ ∉ p
  proof: ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff]; rw [singl

中文:
定理 not_mem_iff
  条件: (p : T.CompleteType α) (φ : L[[α]].Sentence)
  结论: φ.not in p ↔ φ ∉ p
  证明: ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff]; rw [singl

Depends on / 依赖: IsSatisfiable, Theory, forall_eq, forall_eq_or_imp, insert_subset_iff, isMaximal, mem_insert_iff, mem_or_not_mem, mem_singleton_iff, model_iff, p.isMaximal, p.mem_or_not_mem, resolve_left, singleton_subset_iff
-/
theorem not_mem_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) : φ.not in p ↔ φ ∉ p :=
  ⟨fun hf ht => by
    have h : ¬IsSatisfiable ({φ, φ.not} : L[[α]].Theory) := by
      rintro ⟨@⟨_, _, h, _⟩⟩
      simp only [model_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq] at h
      exact h.2 h.1
    refine h (p.isMaximal.1.mono ?_)
    rw [insert_subset_iff]; rw [singleton_subset_iff]
    exact ⟨ht, hf⟩, (p.mem_or_not_mem φ).resolve_left⟩

@[simp]
/--
theorem `compl_setOfPred_mem` / 定理 `compl_setOfPred_mem`

English:
theorem compl_setOfPred_mem
  given: {φ : L[[α]].Sentence}
  proof: ext fun _ => (not_mem_iff _ _).symm

@[deprecated (since := "2026-07-09")] alias compl_setOf_mem := compl_setOfPred_mem

中文:
定理 compl_setOfPred_mem
  条件: {φ : L[[α]].Sentence}
  证明: ext fun _ => (not_mem_iff _ _).symm

@[deprecated (since := "2026-07-09")] alias compl_setOf_mem := compl_setOfPred_mem

Depends on / 依赖: not_mem_iff
-/
theorem compl_setOfPred_mem {φ : L[[α]].Sentence} :
    { p : T.CompleteType α | φ in p }ᶜ = { p : T.CompleteType α | φ.not in p } :=
  ext fun _ => (not_mem_iff _ _).symm

@[deprecated (since := "2026-07-09")] alias compl_setOf_mem := compl_setOfPred_mem

/--
theorem `setOfPred_subset_eq_empty_iff` / 定理 `setOfPred_subset_eq_empty_iff`

English:
theorem setOfPred_subset_eq_empty_iff
  given: (S : L[[α]].Theory)
  proof: by
  rw [iff_not_comm]; rw [← not_nonempty_iff_eq_empty]; rw [Classical.not_not]; rw [Set.Nonempty]
  refine
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left (t := S)).trans completeTheory.subset,
          completeTheory.isMaximal L[[α]] h.some⟩,
        (((L.lhomWithConstants

中文:
定理 setOfPred_subset_eq_empty_iff
  条件: (S : L[[α]].Theory)
  证明: by
  rw [iff_not_comm]; rw [← not_nonempty_iff_eq_empty]; rw [Classical.not_not]; rw [Set.Nonempty]
  refine
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left (t := S)).trans completeTheory.subset,
          completeTheory.isMaximal L[[α]] h.some⟩,
        (((L.lhomWithConstants

Depends on / 依赖: Classical, Classical.not_not, L.lhomWithConstants, Nonempty, Set.Nonempty, completeTheory, completeTheory.isMaximal, completeTheory.subset, h.some, iff_not_comm, isMaximal, lhomWithConstants, not_nonempty_iff_eq_empty, not_not, onTheory, p.isMaximal, p.subset, subset, subset_union_left, subset_union_right
-/
theorem setOfPred_subset_eq_empty_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S subseteq ↑p } = ∅ ↔
      ¬((L.lhomWithConstants α).onTheory T union S).IsSatisfiable := by
  rw [iff_not_comm]; rw [← not_nonempty_iff_eq_empty]; rw [Classical.not_not]; rw [Set.Nonempty]
  refine
    ⟨fun h =>
      ⟨⟨L[[α]].completeTheory h.some, (subset_union_left (t := S)).trans completeTheory.subset,
          completeTheory.isMaximal L[[α]] h.some⟩,
        (((L.lhomWithConstants α).onTheory T).subset_union_right).trans completeTheory.subset⟩,
      ?_⟩
  rintro ⟨p, hp⟩
  exact p.isMaximal.1.mono (union_subset p.subset hp)

@[deprecated (since := "2026-07-09")]
alias setOf_subset_eq_empty_iff := setOfPred_subset_eq_empty_iff

/--
theorem `setOfPred_mem_eq_univ_iff` / 定理 `setOfPred_mem_eq_univ_iff`

English:
theorem setOfPred_mem_eq_univ_iff
  given: (φ : L[[α]].Sentence)
  proof: by
  rw [models_iff_not_satisfiable]; rw [← compl_empty_iff]; rw [compl_setOfPred_mem]; rw [← setOfPred_subset_eq_empty_iff]
  simp

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_univ_iff := setOfPred_mem_eq_univ_iff

中文:
定理 setOfPred_mem_eq_univ_iff
  条件: (φ : L[[α]].Sentence)
  证明: by
  rw [models_iff_not_satisfiable]; rw [← compl_empty_iff]; rw [compl_setOfPred_mem]; rw [← setOfPred_subset_eq_empty_iff]
  simp

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_univ_iff := setOfPred_mem_eq_univ_iff

Depends on / 依赖: compl_empty_iff, compl_setOfPred_mem, models_iff_not_satisfiable, setOfPred_subset_eq_empty_iff
-/
theorem setOfPred_mem_eq_univ_iff (φ : L[[α]].Sentence) :
    { p : T.CompleteType α | φ in p } = Set.univ ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [models_iff_not_satisfiable]; rw [← compl_empty_iff]; rw [compl_setOfPred_mem]; rw [← setOfPred_subset_eq_empty_iff]
  simp

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_univ_iff := setOfPred_mem_eq_univ_iff

/--
theorem `setOfPred_subset_eq_univ_iff` / 定理 `setOfPred_subset_eq_univ_iff`

English:
theorem setOfPred_subset_eq_univ_iff
  given: (S : L[[α]].Theory)
  proof: by
  have h : { p : T.CompleteType α | S subseteq ↑p } = ⋂₀ ((fun φ => { p | φ in p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOfPred_mem_eq_univ_iff]
  refine ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, ?_⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1

@[deprecated (since := "

中文:
定理 setOfPred_subset_eq_univ_iff
  条件: (S : L[[α]].Theory)
  证明: by
  have h : { p : T.CompleteType α | S subseteq ↑p } = ⋂₀ ((fun φ => { p | φ in p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOfPred_mem_eq_univ_iff]
  refine ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, ?_⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1

@[deprecated (since := "

Depends on / 依赖: CompleteType, T.CompleteType, sInter_eq_univ, setOfPred_mem_eq_univ_iff, simp_rw, subset_def, subseteq
-/
theorem setOfPred_subset_eq_univ_iff (S : L[[α]].Theory) :
    { p : T.CompleteType α | S subseteq ↑p } = Set.univ ↔
      forall φ, φ in S -> (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  have h : { p : T.CompleteType α | S subseteq ↑p } = ⋂₀ ((fun φ => { p | φ in p }) '' S) := by
    ext
    simp [subset_def]
  simp_rw [h, sInter_eq_univ, ← setOfPred_mem_eq_univ_iff]
  refine ⟨fun h φ φS => h _ ⟨_, φS, rfl⟩, ?_⟩
  rintro h _ ⟨φ, h1, rfl⟩
  exact h _ h1

@[deprecated (since := "2026-07-09")] alias setOf_subset_eq_univ_iff := setOfPred_subset_eq_univ_iff

/--
theorem `nonempty_iff` / 定理 `nonempty_iff`

English:
theorem nonempty_iff
  statement: Nonempty (T.CompleteType α) ↔ T.IsSatisfiable
  proof: by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  rw [nonempty_iff_univ_nonempty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [not_iff_comm]; rw [← union_empty ((L.lhomWithConstants α).onTheory T)]; rw [← setOfPred_subset_eq_empty_iff]
  simp

中文:
定理 nonempty_iff
  结论: Nonempty (T.CompleteType α) ↔ T.IsSatisfiable
  证明: by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  rw [nonempty_iff_univ_nonempty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [not_iff_comm]; rw [← union_empty ((L.lhomWithConstants α).onTheory T)]; rw [← setOfPred_subset_eq_empty_iff]
  simp

Depends on / 依赖: L.lhomWithConstants, isSatisfiable_onTheory_iff, lhomWithConstants, lhomWithConstants_injective, nonempty_iff_ne_empty, nonempty_iff_univ_nonempty, not_iff_comm, onTheory, setOfPred_subset_eq_empty_iff, union_empty
-/
theorem nonempty_iff : Nonempty (T.CompleteType α) ↔ T.IsSatisfiable := by
  rw [← isSatisfiable_onTheory_iff (lhomWithConstants_injective L α)]
  rw [nonempty_iff_univ_nonempty]; rw [nonempty_iff_ne_empty]; rw [Ne]; rw [not_iff_comm]; rw [← union_empty ((L.lhomWithConstants α).onTheory T)]; rw [← setOfPred_subset_eq_empty_iff]
  simp

/--
Instance `instNonempty` / 实例 `instNonempty`

English:
instance instNonempty
  signature: : Nonempty (CompleteType (∅ : L.Theory) α)
  body: nonempty_iff.2 (isSatisfiable_empty L)

中文:
实例 instNonempty
  签名: : Nonempty (CompleteType (∅ : L.Theory) α)
  定义体: nonempty_iff.2 (isSatisfiable_empty L)

Depends on / 依赖: isSatisfiable_empty, nonempty_iff
-/
instance instNonempty : Nonempty (CompleteType (∅ : L.Theory) α) :=
  nonempty_iff.2 (isSatisfiable_empty L)

/--
theorem `iInter_setOfPred_subset` / 定理 `iInter_setOfPred_subset`

English:
theorem iInter_setOfPred_subset
  given: {ι : Type*} (S : ι -> L[[α]].Theory)
  proof: by
  ext
  simp only [mem_iInter, mem_ofPred_eq, iUnion_subset_iff]

@[deprecated (since := "2026-07-09")] alias iInter_setOf_subset := iInter_setOfPred_subset

中文:
定理 iInter_setOfPred_subset
  条件: {ι : 类型} (S : ι -> L[[α]].Theory)
  证明: by
  ext
  simp only [mem_iInter, mem_ofPred_eq, iUnion_subset_iff]

@[deprecated (since := "2026-07-09")] alias iInter_setOf_subset := iInter_setOfPred_subset

Depends on / 依赖: iUnion_subset_iff, mem_iInter, mem_ofPred_eq
-/
theorem iInter_setOfPred_subset {ι : Type*} (S : ι -> L[[α]].Theory) :
    ⋂ i : ι, { p : T.CompleteType α | S i subseteq p } =
      { p : T.CompleteType α | ⋃ i : ι, S i subseteq p } := by
  ext
  simp only [mem_iInter, mem_ofPred_eq, iUnion_subset_iff]

@[deprecated (since := "2026-07-09")] alias iInter_setOf_subset := iInter_setOfPred_subset

/--
theorem `toList_foldr_inf_mem` / 定理 `toList_foldr_inf_mem`

English:
theorem toList_foldr_inf_mem
  given: {p : T.CompleteType α} {t : Finset L[[α]].Sentence}
  proof: by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩

中文:
定理 toList_foldr_inf_mem
  条件: {p : T.CompleteType α} {t : Finset L[[α]].Sentence}
  证明: by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_foldr_inf, Finset, Finset.mem_toList, Formula, Formula.Realize, Realize, Sentence, Sentence.Realize, SetLike, SetLike.mem_coe, isMaximal, mem_coe, mem_iff_models, mem_toList, models_sentence_iff, p.isMaximal.mem_iff_models, realize_foldr_inf, simp_rw, subset_def
-/
theorem toList_foldr_inf_mem {p : T.CompleteType α} {t : Finset L[[α]].Sentence} :
    t.toList.foldr (· ⊓ ·) ⊤ in p ↔ (t : L[[α]].Theory) subseteq ↑p := by
  simp_rw [subset_def, ← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.Realize, BoundedFormula.realize_foldr_inf, Finset.mem_toList]
  exact ⟨fun h φ hφ M => h _ _ hφ, fun h M φ hφ => h _ hφ _⟩

end CompleteType

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (T)

/--
Definition of `typeOf` / `typeOf` 的定义

English:
definition typeOf
  signature: (v : α -> M)
  body: haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }

中文:
定义 typeOf
  签名: (v : α -> M)
  定义体: haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }

Depends on / 依赖: LHom.onTheory_model, Structure, completeTheory, completeTheory.isMaximal, constantsOn, constantsOn.structure, isMaximal, model_iff_subset_completeTheory, onTheory_model, structure, subset, toTheory
-/
def typeOf (v : α -> M) : T.CompleteType α :=
  haveI : (constantsOn α).Structure M := constantsOn.structure v
  { toTheory := L[[α]].completeTheory M
    subset' := model_iff_subset_completeTheory.1 ((LHom.onTheory_model _ T).2 inferInstance)
    isMaximal' := completeTheory.isMaximal _ _ }

namespace CompleteType

variable {T} {v : α -> M}

@[simp]
/--
theorem `mem_typeOf` / 定理 `mem_typeOf`

English:
theorem mem_typeOf
  given: {φ : L[[α]].Sentence}
  proof: letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm

中文:
定理 mem_typeOf
  条件: {φ : L[[α]].Sentence}
  证明: letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm

Depends on / 依赖: Formula, Formula.realize_equivSentence_symm, Structure, constantsOn, constantsOn.structure, mem_completeTheory, mem_completeTheory.trans, realize_equivSentence_symm, structure
-/
theorem mem_typeOf {φ : L[[α]].Sentence} :
    φ in T.typeOf v ↔ (Formula.equivSentence.symm φ).Realize v :=
  letI : (constantsOn α).Structure M := constantsOn.structure v
  mem_completeTheory.trans (Formula.realize_equivSentence_symm _ _ _).symm

/--
theorem `formula_mem_typeOf` / 定理 `formula_mem_typeOf`

English:
theorem formula_mem_typeOf
  given: {φ : L.Formula α}
  proof: by simp

@[simp]

中文:
定理 formula_mem_typeOf
  条件: {φ : L.Formula α}
  证明: by simp

@[simp]
-/
theorem formula_mem_typeOf {φ : L.Formula α} :
    Formula.equivSentence φ in T.typeOf v ↔ φ.Realize v := by simp

@[simp]
/--
lemma `mem_typesWith_iff` / 引理 `mem_typesWith_iff`

English:
lemma mem_typesWith_iff
  given: (φ : L[[α]].Sentence) (p : CompleteType T α)
  proof: by
  rfl

中文:
引理 mem_typesWith_iff
  条件: (φ : L[[α]].Sentence) (p : CompleteType T α)
  证明: by
  rfl
-/
lemma mem_typesWith_iff (φ : L[[α]].Sentence) (p : CompleteType T α) :
    p in T.typesWith φ ↔ φ in p := by
  rfl

/--
lemma `typesWith_inf` / 引理 `typesWith_inf`

English:
lemma typesWith_inf
  given: (φ ψ : L[[α]].Sentence)
  proof: by
  ext p
  simp only [mem_typesWith_iff, mem_inter_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    ModelsBoundedFormula, ← forall_and]
  exact forall₃_congr fun _ _ _ => BoundedFormula.realize_inf

中文:
引理 typesWith_inf
  条件: (φ ψ : L[[α]].Sentence)
  证明: by
  ext p
  simp only [mem_typesWith_iff, mem_inter_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    ModelsBoundedFormula, ← forall_and]
  exact forall₃_congr fun _ _ _ => BoundedFormula.realize_inf

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_inf, ModelsBoundedFormula, SetLike, SetLike.mem_coe, forall_and, isMaximal, mem_coe, mem_iff_models, mem_inter_iff, mem_typesWith_iff, p.isMaximal.mem_iff_models, realize_inf
-/
lemma typesWith_inf (φ ψ : L[[α]].Sentence) :
    T.typesWith (φ ⊓ ψ) = T.typesWith φ inter T.typesWith ψ := by
  ext p
  simp only [mem_typesWith_iff, mem_inter_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    ModelsBoundedFormula, ← forall_and]
  exact forall₃_congr fun _ _ _ => BoundedFormula.realize_inf

/--
lemma `typesWith_eq_univ_of_mem_onTheory_lhomWithConstants` / 引理 `typesWith_eq_univ_of_mem_onTheory_lhomWithConstants`

English:
lemma typesWith_eq_univ_of_mem_onTheory_lhomWithConstants
  statement: {φ}
  proof: univ_subset_iff.mp fun p _ => p.subset hφ

中文:
引理 typesWith_eq_univ_of_mem_onTheory_lhomWithConstants
  结论: {φ}
  证明: univ_subset_iff.mp fun p _ => p.subset hφ

Depends on / 依赖: p.subset, subset, univ_subset_iff, univ_subset_iff.mp
-/
lemma typesWith_eq_univ_of_mem_onTheory_lhomWithConstants {φ}
    (hφ : φ in (L.lhomWithConstants α).onTheory T) : T.typesWith φ = Set.univ :=
  univ_subset_iff.mp fun p _ => p.subset hφ

/--
lemma `typesWith_top` / 引理 `typesWith_top`

English:
lemma typesWith_top
  statement: T.typesWith (α := α) ⊤ = Set.univ
  proof: univ_subset_iff.mp fun p _ => p.isMaximal.mem_of_models (φ := ⊤) (fun _ _ _ a => a)

中文:
引理 typesWith_top
  结论: T.typesWith (α := α) ⊤ = Set.univ
  证明: univ_subset_iff.mp fun p _ => p.isMaximal.mem_of_models (φ := ⊤) (fun _ _ _ a => a)

Depends on / 依赖: Set.univ
-/
lemma typesWith_top : T.typesWith (α := α) ⊤ = Set.univ :=
  univ_subset_iff.mp fun p _ => p.isMaximal.mem_of_models (φ := ⊤) (fun _ _ _ a => a)

/--
lemma `typesWith_not` / 引理 `typesWith_not`

English:
lemma typesWith_not
  given: (φ : L[[α]].Sentence)
  statement: T.typesWith ∼φ = (T.typesWith φ)ᶜ
  proof: by
  exact Eq.symm compl_setOfPred_mem

中文:
引理 typesWith_not
  条件: (φ : L[[α]].Sentence)
  结论: T.typesWith ∼φ = (T.typesWith φ)ᶜ
  证明: by
  exact Eq.symm compl_setOfPred_mem

Depends on / 依赖: Eq.symm, compl_setOfPred_mem
-/
lemma typesWith_not (φ : L[[α]].Sentence) : T.typesWith ∼φ = (T.typesWith φ)ᶜ := by
  exact Eq.symm compl_setOfPred_mem

end CompleteType

variable (M)

/-- A complete type `p` is realized in a particular structure when there is some
  tuple `v` whose type is `p`. -/
@[simp]
/--
Definition of `realizedTypes` / `realizedTypes` 的定义

English:
definition realizedTypes
  signature: (α : Type w)
  body: Set.range (T.typeOf : (α -> M) -> T.CompleteType α)

中文:
定义 realizedTypes
  签名: (α : Type w)
  定义体: Set.range (T.typeOf : (α -> M) -> T.CompleteType α)

Depends on / 依赖: CompleteType, Set.range, T.CompleteType, T.typeOf, typeOf
-/
def realizedTypes (α : Type w) : Set (T.CompleteType α) :=
  Set.range (T.typeOf : (α -> M) -> T.CompleteType α)

section

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_modelType_is_realized_in` / 定理 `exists_modelType_is_realized_in`

English:
theorem exists_modelType_is_realized_in
  given: (p : T.CompleteType α)
  proof: by
  obtain ⟨M⟩ := p.isMaximal.1
  refine ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), ?_⟩
  refine SetLike.ext fun φ => ?_
  simp only [CompleteType.mem_typeOf]
  refine
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct 

中文:
定理 exists_modelType_is_realized_in
  条件: (p : T.CompleteType α)
  证明: by
  obtain ⟨M⟩ := p.isMaximal.1
  refine ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), ?_⟩
  refine SetLike.ext fun φ => ?_
  simp only [CompleteType.mem_typeOf]
  refine
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct 

Depends on / 依赖: CompleteType, CompleteType.mem_typeOf, Formula, Formula.realize_equivSentence_symm_con, L.con, L.lhomWithConstants, M.struc, M.subtheoryModel, SetLike, SetLike.ext, _root_, _root_.trans, isComplete, isMaximal, lhomWithConstants, mem_iff_models, mem_typeOf, p.isMaximal, p.isMaximal.isComplete.realize_sentence_iff, p.isMaximal.mem_iff_models
-/
theorem exists_modelType_is_realized_in (p : T.CompleteType α) :
    exists M : Theory.ModelType.{u, v, max u v w} T, p in T.realizedTypes M α := by
  obtain ⟨M⟩ := p.isMaximal.1
  refine ⟨(M.subtheoryModel p.subset).reduct (L.lhomWithConstants α), fun a => (L.con a : M), ?_⟩
  refine SetLike.ext fun φ => ?_
  simp only [CompleteType.mem_typeOf]
  refine
    (@Formula.realize_equivSentence_symm_con _
      ((M.subtheoryModel p.subset).reduct (L.lhomWithConstants α)) _ _ M.struc _ φ).trans
      (_root_.trans (_root_.trans ?_ (p.isMaximal.isComplete.realize_sentence_iff φ M))
        (p.isMaximal.mem_iff_models φ).symm)
  rfl

end

end Theory

end Language

end FirstOrder
