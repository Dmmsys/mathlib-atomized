/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2

import Mathlib.Data.Sym.Card

/-!
# `Nat.card` versions of `Fintype.card` lemmas on `Sym`

Each of the lemmas assuming `[Fintype α]` and `Fintype.card` can be restated using `Nat.card` alone.
-/

public section

open Nat

variable (α : Type*)

namespace Sym

instance {k : Nat} [Infinite α] [NeZero k] : Infinite (Sym α k) :=
.of_injective (Sym.replicate k) Sym.replicate_right_injective (NeZero.ne _)

/--
theorem `natCard_sym_eq_multichoose` / 定理 `natCard_sym_eq_multichoose`

English:
theorem natCard_sym_eq_multichoose
  given: (k : Nat)
  proof: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_sym_eq_multichoose _ _
  cases k <;> simp

中文:
定理 natCard_sym_eq_multichoose
  条件: (k : 自然数)
  证明: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_sym_eq_multichoose _ _
  cases k <;> simp

Depends on / 依赖: Classical, Classical.decEq, Nat.card_eq_fintype_card, card_eq_fintype_card, card_sym_eq_multichoose, finite_or_infinite, nonempty_fintype, simp_rw
-/
theorem natCard_sym_eq_multichoose (k : Nat) :
    Nat.card (Sym α k) = multichoose (Nat.card α) k := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_sym_eq_multichoose _ _
  cases k <;> simp

/--
theorem `natCard_sym_eq_choose` / 定理 `natCard_sym_eq_choose`

English:
theorem natCard_sym_eq_choose
  given: (k : Nat)
  proof: by
  rw [natCard_sym_eq_multichoose]; rw [Nat.multichoose_eq]

中文:
定理 natCard_sym_eq_choose
  条件: (k : 自然数)
  证明: by
  rw [natCard_sym_eq_multichoose]; rw [Nat.multichoose_eq]

Depends on / 依赖: Nat.multichoose_eq, multichoose_eq, natCard_sym_eq_multichoose
-/
theorem natCard_sym_eq_choose (k : Nat) :
    Nat.card (Sym α k) = (Nat.card α + k - 1).choose k := by
  rw [natCard_sym_eq_multichoose]; rw [Nat.multichoose_eq]

end Sym

namespace Sym2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite (Sym2 α)
  body: .of_injective Sym2.diag Sym2.diag_injective

中文:
实例 [Infinite
  签名: α] : Infinite (Sym2 α)
  定义体: .of_injective Sym2.diag Sym2.diag_injective

Depends on / 依赖: Sym2.diag, Sym2.diag_injective, diag_injective, of_injective
-/
instance [Infinite α] : Infinite (Sym2 α) :=
.of_injective Sym2.diag Sym2.diag_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite {a
  body: .of_injective (fun a : α => ⟨.diag a, rfl⟩) fun _ _ h => Sym2.diag_injective congr($h)

中文:
实例 [Infinite
  签名: α] : Infinite {a
  定义体: .of_injective (fun a : α => ⟨.diag a, rfl⟩) fun _ _ h => Sym2.diag_injective congr($h)

Depends on / 依赖: Sym2.diag_injective, diag_injective, of_injective
-/
instance [Infinite α] : Infinite {a : Sym2 α // a.IsDiag} :=
  .of_injective (fun a : α => ⟨.diag a, rfl⟩) fun _ _ h => Sym2.diag_injective congr($h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Infinite
  signature: α] : Infinite {a
  body: let e := Infinite.natEmbedding α
  .of_injective (fun n => ⟨s(e 0, e (n + 1)), by simp⟩) fun _ _ => by simp

中文:
实例 [Infinite
  签名: α] : Infinite {a
  定义体: let e := Infinite.natEmbedding α
  .of_injective (fun n => ⟨s(e 0, e (n + 1)), by simp⟩) fun _ _ => by simp

Depends on / 依赖: Infinite, Infinite.natEmbedding, natEmbedding, of_injective
-/
instance [Infinite α] : Infinite {a : Sym2 α // ¬a.IsDiag} :=
  let e := Infinite.natEmbedding α
  .of_injective (fun n => ⟨s(e 0, e (n + 1)), by simp⟩) fun _ _ => by simp

/--
theorem `natCard_subtype_diag` / 定理 `natCard_subtype_diag`

English:
theorem natCard_subtype_diag
  statement: Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α
  proof: Nat.card_congr diagElemEquiv

中文:
定理 natCard_subtype_diag
  结论: 自然数.card { a : Sym2 α // a.IsDiag } = 自然数.card α
  证明: Nat.card_congr diagElemEquiv

Depends on / 依赖: Nat.card_congr, card_congr, diagElemEquiv
-/
theorem natCard_subtype_diag : Nat.card { a : Sym2 α // a.IsDiag } = Nat.card α :=
  Nat.card_congr diagElemEquiv

/--
theorem `natCard_subtype_not_diag` / 定理 `natCard_subtype_not_diag`

English:
theorem natCard_subtype_not_diag
  proof: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_not_diag
  · simp

中文:
定理 natCard_subtype_not_diag
  证明: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_not_diag
  · simp

Depends on / 依赖: Classical, Classical.decEq, Nat.card_eq_fintype_card, card_eq_fintype_card, card_subtype_not_diag, finite_or_infinite, nonempty_fintype, simp_rw
-/
theorem natCard_subtype_not_diag :
    Nat.card { a : Sym2 α // ¬a.IsDiag } = (Nat.card α).choose 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact card_subtype_not_diag
  · simp

/--
lemma `ncard_diagSet` / 引理 `ncard_diagSet`

English:
lemma ncard_diagSet
  statement: (diagSet : Set (Sym2 α)).ncard = Nat.card α
  proof: natCard_subtype_diag _

中文:
引理 ncard_diagSet
  结论: (diagSet : Set (Sym2 α)).ncard = 自然数.card α
  证明: natCard_subtype_diag _

Depends on / 依赖: natCard_subtype_diag
-/
lemma ncard_diagSet : (diagSet : Set (Sym2 α)).ncard = Nat.card α :=
  natCard_subtype_diag _

/--
lemma `ncard_diagSet_compl` / 引理 `ncard_diagSet_compl`

English:
lemma ncard_diagSet_compl
  statement: (diagSetᶜ : Set (Sym2 α)).ncard = (Nat.card α).choose 2
  proof: natCard_subtype_not_diag _

中文:
引理 ncard_diagSet_compl
  结论: (diagSetᶜ : Set (Sym2 α)).ncard = (自然数.card α).choose 2
  证明: natCard_subtype_not_diag _

Depends on / 依赖: natCard_subtype_not_diag
-/
lemma ncard_diagSet_compl : (diagSetᶜ : Set (Sym2 α)).ncard = (Nat.card α).choose 2 :=
  natCard_subtype_not_diag _

/--
theorem `natCard` / 定理 `natCard`

English:
theorem natCard
  statement: Nat.card (Sym2 α) = Nat.choose (Nat.card α + 1) 2
  proof: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact Sym2.card
  · simp

中文:
定理 natCard
  结论: 自然数.card (Sym2 α) = 自然数.choose (自然数.card α + 1) 2
  证明: by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact Sym2.card
  · simp
-/
protected theorem natCard : Nat.card (Sym2 α) = Nat.choose (Nat.card α + 1) 2 := by
  cases finite_or_infinite α
  · obtain ⟨_⟩ := nonempty_fintype α; let := Classical.decEq α
    simp_rw [Nat.card_eq_fintype_card]
    exact Sym2.card
  · simp

end Sym2
