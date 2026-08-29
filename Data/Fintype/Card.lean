/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-!
# Cardinalities of finite types

This file defines the cardinality `Fintype.card α` as the number of elements in `(univ : Finset α)`.
We also include some elementary results on the values of `Fintype.card` on specific types.

## Main declarations

* `Fintype.card α`: Cardinality of a fintype. Equal to `Finset.univ.card`.
* `Finite.surjective_of_injective`: an injective function from a finite type to
  itself is also surjective.

-/

@[expose] public section

assert_not_exists Monoid

open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Fintype

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (α) [Fintype α]
  body: (@univ α _).card

中文:
定义 card
  签名: (α) [有限类型 α]
  定义体: (@univ α _).card
-/
def card (α) [Fintype α] : Nat :=
  (@univ α _).card

/--
theorem `subtype_card` / 定理 `subtype_card`

English:
theorem subtype_card
  given: {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x)
  proof: Multiset.card_pmap _ _ _

中文:
定理 subtype_card
  条件: {p : α -> 命题} (s : 有限集 α) (H : 对任意 x : α, x in s ↔ p x)
  证明: Multiset.card_pmap _ _ _

Depends on / 依赖: Multiset, Multiset.card_pmap, card_pmap
-/
theorem subtype_card {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = #s :=
  Multiset.card_pmap _ _ _

/--
theorem `card_of_subtype` / 定理 `card_of_subtype`

English:
theorem card_of_subtype
  statement: {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x)
  proof: by
  rw [← subtype_card s H]
  congr!

@[simp]

中文:
定理 card_of_subtype
  结论: {p : α -> 命题} (s : 有限集 α) (H : 对任意 x : α, x in s ↔ p x)
  证明: by
  rw [← subtype_card s H]
  congr!

@[simp]

Depends on / 依赖: subtype_card
-/
theorem card_of_subtype {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x)
    [Fintype { x // p x }] : card { x // p x } = #s := by
  rw [← subtype_card s H]
  congr!

@[simp]
/--
theorem `card_ofFinset` / 定理 `card_ofFinset`

English:
theorem card_ofFinset
  given: {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p)
  proof: Fintype.subtype_card s H

中文:
定理 card_ofFinset
  条件: {p : 集合 α} (s : 有限集 α) (H : 对任意 x, x in s ↔ x in p)
  证明: Fintype.subtype_card s H

Depends on / 依赖: Fintype, Fintype.subtype_card, subtype_card
-/
theorem card_ofFinset {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) :
    @Fintype.card p (ofFinset s H) = #s :=
  Fintype.subtype_card s H

/--
theorem `card_of_finset'` / 定理 `card_of_finset'`

English:
theorem card_of_finset'
  given: {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) [Fintype p]
  proof: by rw [← card_ofFinset s H]; congr!

中文:
定理 card_of_finset'
  条件: {p : 集合 α} (s : 有限集 α) (H : 对任意 x, x in s ↔ x in p) [有限类型 p]
  证明: by rw [← card_ofFinset s H]; congr!

Depends on / 依赖: card_ofFinset
-/
theorem card_of_finset' {p : Set α} (s : Finset α) (H : forall x, x in s ↔ x in p) [Fintype p] :
    Fintype.card p = #s := by rw [← card_ofFinset s H]; congr!

end Fintype

namespace Fintype

/--
theorem `ofEquiv_card` / 定理 `ofEquiv_card`

English:
theorem ofEquiv_card
  given: [Fintype α] (f : α ≃ β)
  statement: @card β (ofEquiv α f) = card α
  proof: Multiset.card_map _ _

中文:
定理 ofEquiv_card
  条件: [有限类型 α] (f : α ≃ β)
  结论: @card β (ofEquiv α f) = card α
  证明: Multiset.card_map _ _

Depends on / 依赖: Multiset, Multiset.card_map, card_map
-/
theorem ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _

/--
theorem `card_congr` / 定理 `card_congr`

English:
theorem card_congr
  given: {α β} [Fintype α] [Fintype β] (f : α ≃ β)
  statement: card α = card β
  proof: by
  rw [← ofEquiv_card f]; congr!

@[congr]

中文:
定理 card_congr
  条件: {α β} [有限类型 α] [有限类型 β] (f : α ≃ β)
  结论: card α = card β
  证明: by
  rw [← ofEquiv_card f]; congr!

@[congr]

Depends on / 依赖: ofEquiv_card
-/
theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← ofEquiv_card f]; congr!

@[congr]
/--
theorem `card_congr'` / 定理 `card_congr'`

English:
theorem card_congr'
  given: {α β} [Fintype α] [Fintype β] (h : α = β)
  statement: card α = card β
  proof: card_congr (by rw [h])

中文:
定理 card_congr'
  条件: {α β} [有限类型 α] [有限类型 β] (h : α = β)
  结论: card α = card β
  证明: card_congr (by rw [h])

Depends on / 依赖: card_congr
-/
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr (by rw [h])

/--
theorem `card_ofSubsingleton` / 定理 `card_ofSubsingleton`

English:
theorem card_ofSubsingleton
  given: (a : α) [Subsingleton α]
  statement: @Fintype.card _ (ofSubsingleton a) = 1
  proof: rfl

@[simp]

中文:
定理 card_ofSubsingleton
  条件: (a : α) [子单例 α]
  结论: @有限类型.card _ (ofSubsingleton a) = 1
  证明: rfl

@[simp]
-/
theorem card_ofSubsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl

@[simp]
/--
theorem `card_unique` / 定理 `card_unique`

English:
theorem card_unique
  given: [Unique α] [h : Fintype α]
  statement: Fintype.card α = 1
  proof: Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

中文:
定理 card_unique
  条件: [唯一 α] [h : 有限类型 α]
  结论: 有限类型.card α = 1
  证明: Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

Depends on / 依赖: Subsingleton, Subsingleton.elim, card_ofSubsingleton, ofSubsingleton
-/
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elim (ofSubsingleton default) h ▸ card_ofSubsingleton _

/--
theorem `card_ofIsEmpty` / 定理 `card_ofIsEmpty`

English:
theorem card_ofIsEmpty
  given: [IsEmpty α]
  statement: @Fintype.card α Fintype.ofIsEmpty = 0
  proof: rfl

中文:
定理 card_ofIsEmpty
  条件: [是空 α]
  结论: @有限类型.card α 有限类型.ofIsEmpty = 0
  证明: rfl
-/
theorem card_ofIsEmpty [IsEmpty α] : @Fintype.card α Fintype.ofIsEmpty = 0 :=
  rfl

end Fintype

namespace Set

variable {s t : Set α}

-- We use an arbitrary `[Fintype s]` instance here,
-- not necessarily coming from a `[Fintype α]`.
@[simp]
/--
theorem `toFinset_card` / 定理 `toFinset_card`

English:
theorem toFinset_card
  given: {α : Type*} (s : Set α) [Fintype s]
  statement: s.toFinset.card = Fintype.card s
  proof: Multiset.card_map Subtype.val Finset.univ.val

中文:
定理 toFinset_card
  条件: {α : 类型} (s : 集合 α) [有限类型 s]
  结论: s.toFinset.card = 有限类型.card s
  证明: Multiset.card_map Subtype.val Finset.univ.val

Depends on / 依赖: Finset, Finset.univ.val, Multiset, Multiset.card_map, Subtype, Subtype.val, card_map
-/
theorem toFinset_card {α : Type*} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

end Set

@[simp, grind =]
/--
theorem `Finset.card_univ` / 定理 `Finset.card_univ`

English:
theorem Finset.card_univ
  given: [Fintype α]
  statement: #(univ : Finset α) = Fintype.card α
  proof: rfl

中文:
定理 有限集.card_univ
  条件: [有限类型 α]
  结论: #(univ : 有限集 α) = 有限类型.card α
  证明: rfl
-/
theorem Finset.card_univ [Fintype α] : #(univ : Finset α) = Fintype.card α := rfl

/--
theorem `Finset.eq_univ_of_card` / 定理 `Finset.eq_univ_of_card`

English:
theorem Finset.eq_univ_of_card
  given: [Fintype α] (s : Finset α) (hs : #s = Fintype.card α)
  proof: eq_of_subset_of_card_le (subset_univ _) by rw [hs, Finset.card_univ]

中文:
定理 有限集.eq_univ_of_card
  条件: [有限类型 α] (s : 有限集 α) (hs : #s = 有限类型.card α)
  证明: eq_of_subset_of_card_le (subset_univ _) by rw [hs, Finset.card_univ]

Depends on / 依赖: Finset, Finset.card_univ, card_univ, eq_of_subset_of_card_le, subset_univ
-/
theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : #s = Fintype.card α) :
    s = univ :=
eq_of_subset_of_card_le (subset_univ _) by rw [hs, Finset.card_univ]

/--
theorem `Finset.card_eq_iff_eq_univ` / 定理 `Finset.card_eq_iff_eq_univ`

English:
theorem Finset.card_eq_iff_eq_univ
  given: [Fintype α] (s : Finset α)
  statement: #s = Fintype.card α ↔ s = univ
  proof: ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

中文:
定理 有限集.card_eq_iff_eq_univ
  条件: [有限类型 α] (s : 有限集 α)
  结论: #s = 有限类型.card α ↔ s = univ
  证明: ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

Depends on / 依赖: Finset, Finset.card_univ, card_univ, eq_univ_of_card, s.eq_univ_of_card
-/
theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : #s = Fintype.card α ↔ s = univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

/--
theorem `Finset.card_le_univ` / 定理 `Finset.card_le_univ`

English:
theorem Finset.card_le_univ
  given: [Fintype α] (s : Finset α)
  statement: #s <= Fintype.card α
  proof: card_le_card (subset_univ s)

中文:
定理 有限集.card_le_univ
  条件: [有限类型 α] (s : 有限集 α)
  结论: #s <= 有限类型.card α
  证明: card_le_card (subset_univ s)

Depends on / 依赖: card_le_card, subset_univ
-/
theorem Finset.card_le_univ [Fintype α] (s : Finset α) : #s <= Fintype.card α :=
  card_le_card (subset_univ s)

/--
theorem `Finset.card_lt_univ_of_notMem` / 定理 `Finset.card_lt_univ_of_notMem`

English:
theorem Finset.card_lt_univ_of_notMem
  given: [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s)
  proof: card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

中文:
定理 有限集.card_lt_univ_of_notMem
  条件: [有限类型 α] {s : 有限集 α} {x : α} (hx : x ∉ s)
  证明: card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

Depends on / 依赖: card_lt_card, mem_univ, not_forall, subset_univ
-/
theorem Finset.card_lt_univ_of_notMem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) :
    #s < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

/--
theorem `Finset.card_lt_iff_ne_univ` / 定理 `Finset.card_lt_iff_ne_univ`

English:
theorem Finset.card_lt_iff_ne_univ
  given: [Fintype α] (s : Finset α)
  proof: s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)

中文:
定理 有限集.card_lt_iff_ne_univ
  条件: [有限类型 α] (s : 有限集 α)
  证明: s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)

Depends on / 依赖: card_eq_iff_eq_univ, card_le_univ, lt_iff_ne, not_congr, s.card_eq_iff_eq_univ, s.card_le_univ.lt_iff_ne.trans
-/
theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) :
    #s < Fintype.card α ↔ s != Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_congr s.card_eq_iff_eq_univ)

/--
theorem `Finset.card_compl_lt_iff_nonempty` / 定理 `Finset.card_compl_lt_iff_nonempty`

English:
theorem Finset.card_compl_lt_iff_nonempty
  given: [Fintype α] [DecidableEq α] (s : Finset α)
  proof: sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

中文:
定理 有限集.card_compl_lt_iff_nonempty
  条件: [有限类型 α] [DecidableEq α] (s : 有限集 α)
  证明: sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

Depends on / 依赖: card_lt_iff_ne_univ, card_lt_iff_ne_univ.trans, compl_ne_univ_iff_nonempty, s.compl_ne_univ_iff_nonempty
-/
theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    #sᶜ < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

/--
theorem `Finset.card_univ_sdiff` / 定理 `Finset.card_univ_sdiff`

English:
theorem Finset.card_univ_sdiff
  given: [DecidableEq α] [Fintype α] (s : Finset α)
  proof: by grind

@[deprecated (since := "2026-06-03")] alias Finset.card_univ_diff := Finset.card_univ_sdiff

中文:
定理 有限集.card_univ_sdiff
  条件: [DecidableEq α] [有限类型 α] (s : 有限集 α)
  证明: by grind

@[deprecated (since := "2026-06-03")] alias Finset.card_univ_diff := Finset.card_univ_sdiff
-/
theorem Finset.card_univ_sdiff [DecidableEq α] [Fintype α] (s : Finset α) :
    #(univ \ s) = Fintype.card α - #s := by grind

@[deprecated (since := "2026-06-03")] alias Finset.card_univ_diff := Finset.card_univ_sdiff

/--
theorem `Finset.card_compl` / 定理 `Finset.card_compl`

English:
theorem Finset.card_compl
  given: [DecidableEq α] [Fintype α] (s : Finset α)
  statement: #sᶜ = Fintype.card α - #s
  proof: Finset.card_univ_sdiff s

@[simp]

中文:
定理 有限集.card_compl
  条件: [DecidableEq α] [有限类型 α] (s : 有限集 α)
  结论: #sᶜ = 有限类型.card α - #s
  证明: Finset.card_univ_sdiff s

@[simp]

Depends on / 依赖: Finset, Finset.card_univ_sdiff, card_univ_sdiff
-/
theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : #sᶜ = Fintype.card α - #s :=
  Finset.card_univ_sdiff s

@[simp]
/--
theorem `Finset.card_add_card_compl` / 定理 `Finset.card_add_card_compl`

English:
theorem Finset.card_add_card_compl
  given: [DecidableEq α] [Fintype α] (s : Finset α)
  proof: by
  rw [Finset.card_compl]; rw [← Nat.add_sub_assoc (card_le_univ s)]; rw [Nat.add_sub_cancel_left]

@[simp]

中文:
定理 有限集.card_add_card_compl
  条件: [DecidableEq α] [有限类型 α] (s : 有限集 α)
  证明: by
  rw [Finset.card_compl]; rw [← Nat.add_sub_assoc (card_le_univ s)]; rw [Nat.add_sub_cancel_left]

@[simp]

Depends on / 依赖: Finset, Finset.card_compl, Nat.add_sub_assoc, Nat.add_sub_cancel_left, add_sub_assoc, add_sub_cancel_left, card_compl, card_le_univ
-/
theorem Finset.card_add_card_compl [DecidableEq α] [Fintype α] (s : Finset α) :
    #s + #sᶜ = Fintype.card α := by
  rw [Finset.card_compl]; rw [← Nat.add_sub_assoc (card_le_univ s)]; rw [Nat.add_sub_cancel_left]

@[simp]
/--
theorem `Finset.card_compl_add_card` / 定理 `Finset.card_compl_add_card`

English:
theorem Finset.card_compl_add_card
  given: [DecidableEq α] [Fintype α] (s : Finset α)
  proof: by
  rw [Nat.add_comm]; rw [card_add_card_compl]

中文:
定理 有限集.card_compl_add_card
  条件: [DecidableEq α] [有限类型 α] (s : 有限集 α)
  证明: by
  rw [Nat.add_comm]; rw [card_add_card_compl]

Depends on / 依赖: Nat.add_comm, add_comm, card_add_card_compl
-/
theorem Finset.card_compl_add_card [DecidableEq α] [Fintype α] (s : Finset α) :
    #sᶜ + #s = Fintype.card α := by
  rw [Nat.add_comm]; rw [card_add_card_compl]

/--
theorem `Finset.compl_eq_of_disjoint_of_card_add_eq` / 定理 `Finset.compl_eq_of_disjoint_of_card_add_eq`

English:
theorem Finset.compl_eq_of_disjoint_of_card_add_eq
  proof: (Finset.eq_of_subset_of_card_le
    (by rwa [Finset.subset_compl_iff_disjoint_left])
    (by simp [← Nat.add_le_add_iff_left (n := S₁.card), h'])).symm

中文:
定理 有限集.compl_eq_of_disjoint_of_card_add_eq
  证明: (Finset.eq_of_subset_of_card_le
    (by rwa [Finset.subset_compl_iff_disjoint_left])
    (by simp [← Nat.add_le_add_iff_left (n := S₁.card), h'])).symm

Depends on / 依赖: Finset, Finset.eq_of_subset_of_card_le, Finset.subset_compl_iff_disjoint_left, Nat.add_le_add_iff_left, add_le_add_iff_left, eq_of_subset_of_card_le, subset_compl_iff_disjoint_left
-/
theorem Finset.compl_eq_of_disjoint_of_card_add_eq
    {ι : Type*} [DecidableEq ι] [Fintype ι] {S₁ S₂ : Finset ι} (h : Disjoint S₁ S₂)
    (h' : S₁.card + S₂.card = Finset.card (.univ : Finset ι)) :
    S₁ᶜ = S₂ :=
  (Finset.eq_of_subset_of_card_le
    (by rwa [Finset.subset_compl_iff_disjoint_left])
    (by simp [← Nat.add_le_add_iff_left (n := S₁.card), h'])).symm

/--
theorem `Fintype.card_compl_set` / 定理 `Fintype.card_compl_set`

English:
theorem Fintype.card_compl_set
  given: [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)]
  proof: by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]

中文:
定理 有限类型.card_compl_set
  条件: [有限类型 α] (s : 集合 α) [有限类型 s] [有限类型 (↥sᶜ : 类型层 _)]
  证明: by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]

Depends on / 依赖: Finset, Finset.card_compl, Set.toFinset_card, Set.toFinset_compl, card_compl, classical, toFinset_card, toFinset_compl
-/
theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype (↥sᶜ : Sort _)] :
    Fintype.card (↥sᶜ : Sort _) = Fintype.card α - Fintype.card s := by
  classical rw [← Set.toFinset_card, ← Set.toFinset_card, ← Finset.card_compl, Set.toFinset_compl]

/--
theorem `Fintype.card_subtype_eq` / 定理 `Fintype.card_subtype_eq`

English:
theorem Fintype.card_subtype_eq
  given: (y : α) [Fintype { x // x = y }]
  proof: Fintype.card_unique

中文:
定理 有限类型.card_subtype_eq
  条件: (y : α) [有限类型 { x // x = y }]
  证明: Fintype.card_unique

Depends on / 依赖: Fintype, Fintype.card_unique, card_unique
-/
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] :
    Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique

/--
theorem `Fintype.card_subtype_eq'` / 定理 `Fintype.card_subtype_eq'`

English:
theorem Fintype.card_subtype_eq'
  given: (y : α) [Fintype { x // y = x }]
  proof: Fintype.card_unique

中文:
定理 有限类型.card_subtype_eq'
  条件: (y : α) [有限类型 { x // y = x }]
  证明: Fintype.card_unique

Depends on / 依赖: Fintype, Fintype.card_unique, card_unique
-/
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] :
    Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique

/--
theorem `Fintype.card_empty` / 定理 `Fintype.card_empty`

English:
theorem Fintype.card_empty
  statement: Fintype.card Empty = 0
  proof: rfl

中文:
定理 有限类型.card_empty
  结论: 有限类型.card 空 = 0
  证明: rfl
-/
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl

/--
theorem `Fintype.card_pempty` / 定理 `Fintype.card_pempty`

English:
theorem Fintype.card_pempty
  statement: Fintype.card PEmpty = 0
  proof: rfl

中文:
定理 有限类型.card_pempty
  结论: 有限类型.card 命题空 = 0
  证明: rfl
-/
theorem Fintype.card_pempty : Fintype.card PEmpty = 0 :=
  rfl

/--
theorem `Fintype.card_unit` / 定理 `Fintype.card_unit`

English:
theorem Fintype.card_unit
  statement: Fintype.card Unit = 1
  proof: rfl

@[simp]

中文:
定理 有限类型.card_unit
  结论: 有限类型.card 单元 = 1
  证明: rfl

@[simp]
-/
theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

@[simp]
/--
theorem `Fintype.card_punit` / 定理 `Fintype.card_punit`

English:
theorem Fintype.card_punit
  statement: Fintype.card PUnit = 1
  proof: rfl

@[simp]

中文:
定理 有限类型.card_punit
  结论: 有限类型.card 命题单元 = 1
  证明: rfl

@[simp]
-/
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

@[simp]
/--
theorem `Fintype.card_bool` / 定理 `Fintype.card_bool`

English:
theorem Fintype.card_bool
  statement: Fintype.card Bool = 2
  proof: rfl

@[simp]

中文:
定理 有限类型.card_bool
  结论: 有限类型.card 布尔值 = 2
  证明: rfl

@[simp]
-/
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

@[simp]
/--
theorem `Fintype.card_ulift` / 定理 `Fintype.card_ulift`

English:
theorem Fintype.card_ulift
  given: (α : Type*) [Fintype α]
  statement: Fintype.card (ULift α) = Fintype.card α
  proof: Fintype.ofEquiv_card _

@[simp]

中文:
定理 有限类型.card_ulift
  条件: (α : 类型) [有限类型 α]
  结论: 有限类型.card (类型层提升 α) = 有限类型.card α
  证明: Fintype.ofEquiv_card _

@[simp]

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, ofEquiv_card
-/
theorem Fintype.card_ulift (α : Type*) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
/--
theorem `Fintype.card_plift` / 定理 `Fintype.card_plift`

English:
theorem Fintype.card_plift
  given: (α : Type*) [Fintype α]
  statement: Fintype.card (PLift α) = Fintype.card α
  proof: Fintype.ofEquiv_card _

@[simp]

中文:
定理 有限类型.card_plift
  条件: (α : 类型) [有限类型 α]
  结论: 有限类型.card (命题层提升 α) = 有限类型.card α
  证明: Fintype.ofEquiv_card _

@[simp]

Depends on / 依赖: Fintype, Fintype.ofEquiv_card, ofEquiv_card
-/
theorem Fintype.card_plift (α : Type*) [Fintype α] : Fintype.card (PLift α) = Fintype.card α :=
  Fintype.ofEquiv_card _

@[simp]
/--
theorem `Fintype.card_orderDual` / 定理 `Fintype.card_orderDual`

English:
theorem Fintype.card_orderDual
  given: (α : Type*) [Fintype α]
  statement: Fintype.card αᵒᵈ = Fintype.card α
  proof: rfl

@[simp]

中文:
定理 有限类型.card_orderDual
  条件: (α : 类型) [有限类型 α]
  结论: 有限类型.card αᵒᵈ = 有限类型.card α
  证明: rfl

@[simp]
-/
theorem Fintype.card_orderDual (α : Type*) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl

@[simp]
/--
theorem `Fintype.card_lex` / 定理 `Fintype.card_lex`

English:
theorem Fintype.card_lex
  given: (α : Type*) [Fintype α]
  statement: Fintype.card (Lex α) = Fintype.card α
  proof: rfl

中文:
定理 有限类型.card_lex
  条件: (α : 类型) [有限类型 α]
  结论: 有限类型.card (Lex α) = 有限类型.card α
  证明: rfl
-/
theorem Fintype.card_lex (α : Type*) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl

-- Note: The extra hypothesis `h` is there so that the rewrite lemma applies,
-- no matter what instance of `Fintype (Set.univ : Set α)` is used.
/--
theorem `Fintype.card_setUniv` / 定理 `Fintype.card_setUniv`

English:
theorem Fintype.card_setUniv
  given: [Fintype α] {h : Fintype (Set.univ : Set α)}
  proof: by
  apply Fintype.card_of_finset'
  simp

@[simp]

中文:
定理 有限类型.card_setUniv
  条件: [有限类型 α] {h : 有限类型 (集合.univ : 集合 α)}
  证明: by
  apply Fintype.card_of_finset'
  simp

@[simp]

Depends on / 依赖: Fintype, Fintype.card_of_finset, card_of_finset
-/
theorem Fintype.card_setUniv [Fintype α] {h : Fintype (Set.univ : Set α)} :
    Fintype.card (Set.univ : Set α) = Fintype.card α := by
  apply Fintype.card_of_finset'
  simp

@[simp]
/--
theorem `Fintype.card_subtype_true` / 定理 `Fintype.card_subtype_true`

English:
theorem Fintype.card_subtype_true
  given: [Fintype α] {h : Fintype {_a : α // True}}
  proof: by
  apply Fintype.card_of_subtype
  simp

中文:
定理 有限类型.card_subtype_true
  条件: [有限类型 α] {h : 有限类型 {_a : α // 真}}
  证明: by
  apply Fintype.card_of_subtype
  simp

Depends on / 依赖: Fintype, Fintype.card_of_subtype, card_of_subtype
-/
theorem Fintype.card_subtype_true [Fintype α] {h : Fintype {_a : α // True}} :
    @Fintype.card {_a // True} h = Fintype.card α := by
  apply Fintype.card_of_subtype
  simp

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `Sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
@[instance_reducible]
/--
Definition of `Fintype.sumLeft` / `Fintype.sumLeft` 的定义

English:
definition Fintype.sumLeft
  signature: {α β} [Fintype (α oplus β)]
  body: Fintype.ofInjective (Sum.inl : α -> α oplus β) Sum.inl_injective

中文:
定义 有限类型.sumLeft
  签名: {α β} [有限类型 (α oplus β)]
  定义体: Fintype.ofInjective (Sum.inl : α -> α oplus β) Sum.inl_injective

Depends on / 依赖: Fintype, Fintype.ofInjective, Sum.inl, Sum.inl_injective, inl_injective, ofInjective
-/
noncomputable def Fintype.sumLeft {α β} [Fintype (α oplus β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α -> α oplus β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `Sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
@[instance_reducible]
/--
Definition of `Fintype.sumRight` / `Fintype.sumRight` 的定义

English:
definition Fintype.sumRight
  signature: {α β} [Fintype (α oplus β)]
  body: Fintype.ofInjective (Sum.inr : β -> α oplus β) Sum.inr_injective

中文:
定义 有限类型.sumRight
  签名: {α β} [有限类型 (α oplus β)]
  定义体: Fintype.ofInjective (Sum.inr : β -> α oplus β) Sum.inr_injective

Depends on / 依赖: Fintype, Fintype.ofInjective, Sum.inr, Sum.inr_injective, inr_injective, ofInjective
-/
noncomputable def Fintype.sumRight {α β} [Fintype (α oplus β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β -> α oplus β) Sum.inr_injective

/--
theorem `Finite.exists_univ_list` / 定理 `Finite.exists_univ_list`

English:
theorem Finite.exists_univ_list
  given: (α) [Finite α]
  statement: exists l : List α, l.Nodup ∧ forall x : α, x in l
  proof: by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩

中文:
定理 有限.存在_univ_list
  条件: (α) [有限 α]
  结论: 存在 l : 列表 α, l.Nodup ∧ 对任意 x : α, x in l
  证明: by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩

Depends on / 依赖: And.intro, Quotient, Quotient.exists_rep, exists_rep, mem_univ_val, nonempty_fintype
-/
theorem Finite.exists_univ_list (α) [Finite α] : exists l : List α, l.Nodup ∧ forall x : α, x in l := by
  cases nonempty_fintype α
  obtain ⟨l, e⟩ := Quotient.exists_rep (@univ α _).1
  have := And.intro (@univ α _).2 (@mem_univ_val α _)
  exact ⟨_, by rwa [← e] at this⟩

/--
theorem `List.Nodup.length_le_card` / 定理 `List.Nodup.length_le_card`

English:
theorem List.Nodup.length_le_card
  given: {α : Type*} [Fintype α] {l : List α} (h : l.Nodup)
  proof: by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

中文:
定理 列表.Nodup.length_le_card
  条件: {α : 类型} [有限类型 α] {l : 列表 α} (h : l.Nodup)
  证明: by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

Depends on / 依赖: List.toFinset_card_of_nodup, card_le_univ, classical, l.toFinset.card_le_univ, toFinset, toFinset_card_of_nodup
-/
theorem List.Nodup.length_le_card {α : Type*} [Fintype α] {l : List α} (h : l.Nodup) :
    l.length <= Fintype.card α := by
  classical exact List.toFinset_card_of_nodup h ▸ l.toFinset.card_le_univ

namespace Fintype

variable [Fintype α] [Fintype β]

/--
theorem `card_le_of_injective` / 定理 `card_le_of_injective`

English:
theorem card_le_of_injective
  given: (f : α -> β) (hf : Function.Injective f)
  statement: card α <= card β
  proof: Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

中文:
定理 card_le_of_injective
  条件: (f : α -> β) (hf : 函数.单射 f)
  结论: card α <= card β
  证明: Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

Depends on / 依赖: Finset, Finset.card_le_card_of_injOn, Finset.mem_univ, card_le_card_of_injOn, mem_univ
-/
theorem card_le_of_injective (f : α -> β) (hf : Function.Injective f) : card α <= card β :=
  Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

/--
theorem `not_injective_of_card_lt` / 定理 `not_injective_of_card_lt`

English:
theorem not_injective_of_card_lt
  given: (f : α -> β) (h : card β < card α)
  proof: Nat.not_le_of_lt h ∘ card_le_of_injective f

中文:
定理 not_injective_of_card_lt
  条件: (f : α -> β) (h : card β < card α)
  证明: Nat.not_le_of_lt h ∘ card_le_of_injective f

Depends on / 依赖: Nat.not_le_of_lt, card_le_of_injective, not_le_of_lt
-/
theorem not_injective_of_card_lt (f : α -> β) (h : card β < card α) :
    ¬Function.Injective f :=
  Nat.not_le_of_lt h ∘ card_le_of_injective f

/--
theorem `card_le_of_embedding` / 定理 `card_le_of_embedding`

English:
theorem card_le_of_embedding
  given: (f : α ↪ β)
  statement: card α <= card β
  proof: card_le_of_injective f f.2

中文:
定理 card_le_of_embedding
  条件: (f : α ↪ β)
  结论: card α <= card β
  证明: card_le_of_injective f f.2

Depends on / 依赖: card_le_of_injective
-/
theorem card_le_of_embedding (f : α ↪ β) : card α <= card β :=
  card_le_of_injective f f.2

/--
theorem `card_lt_of_injective_of_notMem` / 定理 `card_lt_of_injective_of_notMem`

English:
theorem card_lt_of_injective_of_notMem
  statement: (f : α -> β) (h : Function.Injective f) {b : β}
  proof: calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
Finset.card_lt_univ_of_notMem (x := b) by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

中文:
定理 card_lt_of_injective_of_notMem
  结论: (f : α -> β) (h : 函数.单射 f) {b : β}
  证明: calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
Finset.card_lt_univ_of_notMem (x := b) by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

Depends on / 依赖: Finset, Finset.card_lt_univ_of_notMem, Set.image_univ, card_lt_univ_of_notMem, card_map, coe_map, coe_univ, image_univ, mem_coe, univ.map
-/
theorem card_lt_of_injective_of_notMem (f : α -> β) (h : Function.Injective f) {b : β}
    (w : b ∉ Set.range f) : card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
Finset.card_lt_univ_of_notMem (x := b) by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]

/--
theorem `existsUnique_notMem_image_of_injective_of_card_eq_add_one` / 定理 `existsUnique_notMem_image_of_injective_of_card_eq_add_one`

English:
theorem existsUnique_notMem_image_of_injective_of_card_eq_add_one
  statement: [DecidableEq β]
  proof: by
    simpa using existsUnique_notMem_image_of_injOn_of_card_eq_add_one
      (s := .univ) (t := .univ) (Set.injOn_of_injective hf) (by simp) (by simpa)

中文:
定理 存在Unique_notMem_image_of_injective_of_card_eq_add_one
  结论: [DecidableEq β]
  证明: by
    simpa using existsUnique_notMem_image_of_injOn_of_card_eq_add_one
      (s := .univ) (t := .univ) (Set.injOn_of_injective hf) (by simp) (by simpa)

Depends on / 依赖: Set.injOn_of_injective, existsUnique_notMem_image_of_injOn_of_card_eq_add_one, injOn_of_injective
-/
theorem existsUnique_notMem_image_of_injective_of_card_eq_add_one [DecidableEq β]
    (f : α -> β) (hf : f.Injective) (h : card β = card α + 1) : exists! x, x ∉ univ.image f := by
    simpa using existsUnique_notMem_image_of_injOn_of_card_eq_add_one
      (s := .univ) (t := .univ) (Set.injOn_of_injective hf) (by simp) (by simpa)

/--
theorem `card_lt_of_injective_not_surjective` / 定理 `card_lt_of_injective_not_surjective`

English:
theorem card_lt_of_injective_not_surjective
  statement: (f : α -> β) (h : Function.Injective f)
  proof: let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_notMem f h hy

中文:
定理 card_lt_of_injective_not_surjective
  结论: (f : α -> β) (h : 函数.单射 f)
  证明: let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_notMem f h hy

Depends on / 依赖: card_lt_of_injective_of_notMem, not_forall
-/
theorem card_lt_of_injective_not_surjective (f : α -> β) (h : Function.Injective f)
    (h' : ¬Function.Surjective f) : card α < card β :=
  let ⟨_y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_notMem f h hy

/--
theorem `card_le_of_surjective` / 定理 `card_le_of_surjective`

English:
theorem card_le_of_surjective
  given: (f : α -> β) (h : Function.Surjective f)
  statement: card β <= card α
  proof: card_le_of_injective _ (Function.injective_surjInv h)

中文:
定理 card_le_of_surjective
  条件: (f : α -> β) (h : 函数.满射 f)
  结论: card β <= card α
  证明: card_le_of_injective _ (Function.injective_surjInv h)

Depends on / 依赖: Function, Function.injective_surjInv, card_le_of_injective, injective_surjInv
-/
theorem card_le_of_surjective (f : α -> β) (h : Function.Surjective f) : card β <= card α :=
  card_le_of_injective _ (Function.injective_surjInv h)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `card_range_le` / 定理 `card_range_le`

English:
theorem card_range_le
  given: {α β : Type*} (f : α -> β) [Fintype α] [Fintype (Set.range f)]
  proof: Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩

中文:
定理 card_range_le
  条件: {α β : 类型} (f : α -> β) [有限类型 α] [有限类型 (集合.range f)]
  证明: Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩

Depends on / 依赖: Fintype, Fintype.card_le_of_surjective, card_le_of_surjective
-/
theorem card_range_le {α β : Type*} (f : α -> β) [Fintype α] [Fintype (Set.range f)] :
    Fintype.card (Set.range f) <= Fintype.card α :=
  Fintype.card_le_of_surjective (fun a => ⟨f a, by simp⟩) fun ⟨_, a, ha⟩ => ⟨a, by simpa using ha⟩

/--
theorem `card_range` / 定理 `card_range`

English:
theorem card_range
  statement: {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [Fintype α]
  proof: Eq.symm Fintype.card_congr Equiv.ofInjective _ EmbeddingLike.injective f

中文:
定理 card_range
  结论: {α β F : 类型} [函数状 F α β] [EmbeddingLike F α β] (f : F) [有限类型 α]
  证明: Eq.symm Fintype.card_congr Equiv.ofInjective _ EmbeddingLike.injective f

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, Eq.symm, Equiv.ofInjective, Fintype, Fintype.card_congr, card_congr, injective, ofInjective
-/
theorem card_range {α β F : Type*} [FunLike F α β] [EmbeddingLike F α β] (f : F) [Fintype α]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card α :=
Eq.symm Fintype.card_congr Equiv.ofInjective _ EmbeddingLike.injective f

/--
theorem `card_eq_zero_iff` / 定理 `card_eq_zero_iff`

English:
theorem card_eq_zero_iff
  statement: card α = 0 ↔ IsEmpty α
  proof: by
  rw [card]; rw [Finset.card_eq_zero]; rw [univ_eq_empty_iff]

中文:
定理 card_eq_zero_iff
  结论: card α = 0 ↔ 是空 α
  证明: by
  rw [card]; rw [Finset.card_eq_zero]; rw [univ_eq_empty_iff]

Depends on / 依赖: Finset, Finset.card_eq_zero, card_eq_zero, univ_eq_empty_iff
-/
theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card]; rw [Finset.card_eq_zero]; rw [univ_eq_empty_iff]

/--
theorem `card_eq_zero` / 定理 `card_eq_zero`

English:
theorem card_eq_zero
  given: [IsEmpty α]
  statement: card α = 0
  proof: card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero

中文:
定理 card_eq_zero
  条件: [是空 α]
  结论: card α = 0
  证明: card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero
-/
@[simp] theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

alias card_of_isEmpty := card_eq_zero

/--
Definition of `cardEqZeroEquivEquivEmpty` / `cardEqZeroEquivEquivEmpty` 的定义

English:
definition cardEqZeroEquivEquivEmpty
  signature: : card α = 0 ≃ (α ≃ Empty)
  body: (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

中文:
定义 cardEqZeroEquivEquivEmpty
  签名: : card α = 0 ≃ (α ≃ 空)
  定义体: (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

Depends on / 依赖: Equiv.equivEmptyEquiv, Equiv.ofIff, card_eq_zero_iff, equivEmptyEquiv
-/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

/--
theorem `card_pos_iff` / 定理 `card_pos_iff`

English:
theorem card_pos_iff
  statement: 0 < card α ↔ Nonempty α
  proof: Nat.pos_iff_ne_zero.trans not_iff_comm.mp not_nonempty_iff.trans card_eq_zero_iff.symm

中文:
定理 card_pos_iff
  结论: 0 < card α ↔ 非空 α
  证明: Nat.pos_iff_ne_zero.trans not_iff_comm.mp not_nonempty_iff.trans card_eq_zero_iff.symm

Depends on / 依赖: Nat.pos_iff_ne_zero.trans, card_eq_zero_iff, card_eq_zero_iff.symm, not_iff_comm, not_iff_comm.mp, not_nonempty_iff, not_nonempty_iff.trans, pos_iff_ne_zero
-/
theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
Nat.pos_iff_ne_zero.trans not_iff_comm.mp not_nonempty_iff.trans card_eq_zero_iff.symm

/--
theorem `card_pos` / 定理 `card_pos`

English:
theorem card_pos
  given: [h : Nonempty α]
  statement: 0 < card α
  proof: card_pos_iff.mpr h

@[simp]

中文:
定理 card_pos
  条件: [h : 非空 α]
  结论: 0 < card α
  证明: card_pos_iff.mpr h

@[simp]

Depends on / 依赖: card_pos_iff, card_pos_iff.mpr
-/
theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

@[simp]
/--
theorem `card_ne_zero` / 定理 `card_ne_zero`

English:
theorem card_ne_zero
  given: [Nonempty α]
  statement: card α != 0
  proof: _root_.ne_of_gt card_pos

中文:
定理 card_ne_zero
  条件: [非空 α]
  结论: card α != 0
  证明: _root_.ne_of_gt card_pos

Depends on / 依赖: _root_, _root_.ne_of_gt, card_pos, ne_of_gt
-/
theorem card_ne_zero [Nonempty α] : card α != 0 :=
  _root_.ne_of_gt card_pos

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : NeZero (card α)
  body: ⟨card_ne_zero⟩

中文:
实例 [非空
  签名: α] : NeZero (card α)
  定义体: ⟨card_ne_zero⟩

Depends on / 依赖: card_ne_zero
-/
instance [Nonempty α] : NeZero (card α) := ⟨card_ne_zero⟩

/--
theorem `existsUnique_iff_card_one` / 定理 `existsUnique_iff_card_one`

English:
theorem existsUnique_iff_card_one
  given: {α} [Fintype α] (p : α -> Prop) [DecidablePred p]
  proof: by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff, and_comm,
    mem_filter_univ]

nonrec theorem two_lt_card_iff : 2 < card α ↔ exists a b c : α, a != b ∧ a != c ∧ b != c := by
  simp_rw [← Finset.card_univ, 

中文:
定理 存在Unique_iff_card_one
  条件: {α} [有限类型 α] (p : α -> 命题) [DecidablePred p]
  证明: by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff, and_comm,
    mem_filter_univ]

nonrec theorem two_lt_card_iff : 2 < card α ↔ exists a b c : α, a != b ∧ a != c ∧ b != c := by
  simp_rw [← Finset.card_univ, 

Depends on / 依赖: Finset, Finset.card_eq_one, Subset, Subset.antisymm_iff, and_comm, antisymm_iff, card_eq_one, exists_congr, mem_filter_univ, singleton_subset_iff, subset_singleton_iff
-/
theorem existsUnique_iff_card_one {α} [Fintype α] (p : α -> Prop) [DecidablePred p] :
    (exists! a : α, p a) ↔ #{x | p x} = 1 := by
  rw [Finset.card_eq_one]
  refine exists_congr fun x => ?_
  simp only [Subset.antisymm_iff, subset_singleton_iff', singleton_subset_iff, and_comm,
    mem_filter_univ]

nonrec theorem two_lt_card_iff : 2 < card α ↔ exists a b c : α, a != b ∧ a != c ∧ b != c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_and]

/--
theorem `card_of_bijective` / 定理 `card_of_bijective`

English:
theorem card_of_bijective
  given: {f : α -> β} (hf : Bijective f)
  statement: card α = card β
  proof: card_congr (Equiv.ofBijective f hf)

中文:
定理 card_of_bijective
  条件: {f : α -> β} (hf : 双射 f)
  结论: card α = card β
  证明: card_congr (Equiv.ofBijective f hf)

Depends on / 依赖: Equiv.ofBijective, card_congr, ofBijective
-/
theorem card_of_bijective {f : α -> β} (hf : Bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)

end Fintype

namespace Finite

variable [Finite α]

/--
theorem `surjective_of_injective` / 定理 `surjective_of_injective`

English:
theorem surjective_of_injective
  given: {f : α -> α} (hinj : Injective f)
  statement: Surjective f
  proof: by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x in image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
 

中文:
定理 surjective_of_injective
  条件: {f : α -> α} (hinj : 单射 f)
  结论: 满射 f
  证明: by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x in image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
 

Depends on / 依赖: Classical, Classical.propDecidable, card_image_of_injective, eq_of_subset_of_card_le, le_rfl, mem_image, mem_univ, nonempty_fintype, propDecidable, subset_univ
-/
theorem surjective_of_injective {f : α -> α} (hinj : Injective f) : Surjective f := by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  have h₁ : image f univ = univ :=
    eq_of_subset_of_card_le (subset_univ _)
      ((card_image_of_injective univ hinj).symm ▸ le_rfl)
  have h₂ : x in image f univ := h₁.symm ▸ mem_univ x
  obtain ⟨y, h⟩ := mem_image.1 h₂
  exact ⟨y, h.2⟩

/--
theorem `injective_iff_surjective` / 定理 `injective_iff_surjective`

English:
theorem injective_iff_surjective
  given: {f : α -> α}
  statement: Injective f ↔ Surjective f
  proof: ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩

中文:
定理 injective_iff_surjective
  条件: {f : α -> α}
  结论: 单射 f ↔ 满射 f
  证明: ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, injective, injective_surjInv, leftInverse_of_surjective_of_rightInverse, rightInverse_surjInv, surjInv, surjective_of_injective
-/
theorem injective_iff_surjective {f : α -> α} : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    HasLeftInverse.injective ⟨surjInv hsurj, leftInverse_of_surjective_of_rightInverse
      (surjective_of_injective (injective_surjInv _))
      (rightInverse_surjInv _)⟩⟩

/--
theorem `injective_iff_bijective` / 定理 `injective_iff_bijective`

English:
theorem injective_iff_bijective
  given: {f : α -> α}
  statement: Injective f ↔ Bijective f
  proof: by
  simp [Bijective, injective_iff_surjective]

中文:
定理 injective_iff_bijective
  条件: {f : α -> α}
  结论: 单射 f ↔ 双射 f
  证明: by
  simp [Bijective, injective_iff_surjective]

Depends on / 依赖: Bijective, injective_iff_surjective
-/
theorem injective_iff_bijective {f : α -> α} : Injective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

/--
theorem `surjective_iff_bijective` / 定理 `surjective_iff_bijective`

English:
theorem surjective_iff_bijective
  given: {f : α -> α}
  statement: Surjective f ↔ Bijective f
  proof: by
  simp [Bijective, injective_iff_surjective]

中文:
定理 surjective_iff_bijective
  条件: {f : α -> α}
  结论: 满射 f ↔ 双射 f
  证明: by
  simp [Bijective, injective_iff_surjective]

Depends on / 依赖: Bijective, injective_iff_surjective
-/
theorem surjective_iff_bijective {f : α -> α} : Surjective f ↔ Bijective f := by
  simp [Bijective, injective_iff_surjective]

/--
theorem `injective_iff_surjective_of_equiv` / 定理 `injective_iff_surjective_of_equiv`

English:
theorem injective_iff_surjective_of_equiv
  given: {f : α -> β} (e : α ≃ β)
  statement: Injective f ↔ Surjective f
  proof: have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

中文:
定理 injective_iff_surjective_of_equiv
  条件: {f : α -> β} (e : α ≃ β)
  结论: 单射 f ↔ 满射 f
  证明: have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

Depends on / 依赖: Function, Function.comp, Injective, Surjective, e.injective.comp, e.surjective.comp, e.symm, e.symm.injective.comp, e.symm.surjective.comp, injective, injective_iff_surjective, surjective
-/
theorem injective_iff_surjective_of_equiv {f : α -> β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj => by
    simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

alias ⟨_root_.Function.Injective.bijective_of_finite, _⟩ := injective_iff_bijective

alias ⟨_root_.Function.Surjective.bijective_of_finite, _⟩ := surjective_iff_bijective

alias ⟨_root_.Function.Injective.surjective_of_finite,
    _root_.Function.Surjective.injective_of_finite⟩ :=
  injective_iff_surjective_of_equiv

end Finite

@[simp]
/--
theorem `Fintype.card_coe` / 定理 `Fintype.card_coe`

English:
theorem Fintype.card_coe
  given: (s : Finset α) [Fintype s]
  statement: Fintype.card s = #s
  proof: @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

中文:
定理 有限类型.card_coe
  条件: (s : 有限集 α) [有限类型 s]
  结论: 有限类型.card s = #s
  证明: @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

Depends on / 依赖: Fintype, Fintype.card_of_finset, Iff.rfl, card_of_finset
-/
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = #s :=
  @Fintype.card_of_finset' _ _ _ (fun _ => Iff.rfl) (id _)

/--
lemma `Finset.exists_superset_card_eq` / 引理 `Finset.exists_superset_card_eq`

English:
lemma Finset.exists_superset_card_eq
  statement: [Fintype α] {n : Nat} {s : Finset α} (hsn : #s <= n)
  proof: by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]

中文:
引理 有限集.存在_superset_card_eq
  结论: [有限类型 α] {n : 自然数} {s : 有限集 α} (hsn : #s <= n)
  证明: by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]

Depends on / 依赖: exists_subsuperset_card_eq, s.subset_univ, subset_univ
-/
lemma Finset.exists_superset_card_eq [Fintype α] {n : Nat} {s : Finset α} (hsn : #s <= n)
    (hnα : n <= Fintype.card α) :
    exists t, s subseteq t ∧ #t = n := by simpa using exists_subsuperset_card_eq s.subset_univ hsn hnα

@[simp]
/--
theorem `Fintype.card_prop` / 定理 `Fintype.card_prop`

English:
theorem Fintype.card_prop
  statement: Fintype.card Prop = 2
  proof: rfl

中文:
定理 有限类型.card_prop
  结论: 有限类型.card 命题 = 2
  证明: rfl
-/
theorem Fintype.card_prop : Fintype.card Prop = 2 :=
  rfl

/--
theorem `set_fintype_card_le_univ` / 定理 `set_fintype_card_le_univ`

English:
theorem set_fintype_card_le_univ
  given: [Fintype α] (s : Set α) [Fintype s]
  proof: Fintype.card_le_of_embedding (Function.Embedding.subtype (· in s))

中文:
定理 set_fintype_card_le_univ
  条件: [有限类型 α] (s : 集合 α) [有限类型 s]
  证明: Fintype.card_le_of_embedding (Function.Embedding.subtype (· in s))

Depends on / 依赖: Embedding, Fintype, Fintype.card_le_of_embedding, Function, Function.Embedding.subtype, card_le_of_embedding, subtype
-/
theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s <= Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype (· in s))

/--
theorem `set_fintype_card_eq_univ_iff` / 定理 `set_fintype_card_eq_univ_iff`

English:
theorem set_fintype_card_eq_univ_iff
  given: [Fintype α] (s : Set α) [Fintype s]
  proof: by
  rw [← Set.toFinset_card]; rw [Finset.card_eq_iff_eq_univ]; rw [← Set.toFinset_univ]; rw [Set.toFinset_inj]

中文:
定理 set_fintype_card_eq_univ_iff
  条件: [有限类型 α] (s : 集合 α) [有限类型 s]
  证明: by
  rw [← Set.toFinset_card]; rw [Finset.card_eq_iff_eq_univ]; rw [← Set.toFinset_univ]; rw [Set.toFinset_inj]

Depends on / 依赖: Finset, Finset.card_eq_iff_eq_univ, Set.toFinset_card, Set.toFinset_inj, Set.toFinset_univ, card_eq_iff_eq_univ, toFinset_card, toFinset_inj, toFinset_univ
-/
theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype s] :
    Fintype.card s = Fintype.card α ↔ s = Set.univ := by
  rw [← Set.toFinset_card]; rw [Finset.card_eq_iff_eq_univ]; rw [← Set.toFinset_univ]; rw [Set.toFinset_inj]

/--
theorem `Fintype.card_subtype_le` / 定理 `Fintype.card_subtype_le`

English:
theorem Fintype.card_subtype_le
  given: [Fintype α] (p : α -> Prop) [Fintype {a // p a}]
  proof: Fintype.card_le_of_embedding (Function.Embedding.subtype _)

中文:
定理 有限类型.card_subtype_le
  条件: [有限类型 α] (p : α -> 命题) [有限类型 {a // p a}]
  证明: Fintype.card_le_of_embedding (Function.Embedding.subtype _)

Depends on / 依赖: Embedding, Fintype, Fintype.card_le_of_embedding, Function, Function.Embedding.subtype, card_le_of_embedding, subtype
-/
theorem Fintype.card_subtype_le [Fintype α] (p : α -> Prop) [Fintype {a // p a}] :
    Fintype.card { x // p x } <= Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)

/--
lemma `Fintype.card_subtype_lt` / 引理 `Fintype.card_subtype_lt`

English:
lemma Fintype.card_subtype_lt
  given: [Fintype α] {p : α -> Prop} [Fintype {a // p a}] {x : α} (hx : ¬p x)
  proof: Fintype.card_lt_of_injective_of_notMem (b := x) (↑) Subtype.coe_injective by
    rwa [Subtype.range_coe_subtype]

中文:
引理 有限类型.card_subtype_lt
  条件: [有限类型 α] {p : α -> 命题} [有限类型 {a // p a}] {x : α} (hx : ¬p x)
  证明: Fintype.card_lt_of_injective_of_notMem (b := x) (↑) Subtype.coe_injective by
    rwa [Subtype.range_coe_subtype]

Depends on / 依赖: Fintype, Fintype.card_lt_of_injective_of_notMem, Subtype, Subtype.coe_injective, Subtype.range_coe_subtype, card_lt_of_injective_of_notMem, coe_injective, range_coe_subtype
-/
lemma Fintype.card_subtype_lt [Fintype α] {p : α -> Prop} [Fintype {a // p a}] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
Fintype.card_lt_of_injective_of_notMem (b := x) (↑) Subtype.coe_injective by
    rwa [Subtype.range_coe_subtype]

/--
theorem `Fintype.card_subtype` / 定理 `Fintype.card_subtype`

English:
theorem Fintype.card_subtype
  given: [Fintype α] (p : α -> Prop) [Fintype {a // p a}] [DecidablePred p]
  proof: by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]

中文:
定理 有限类型.card_subtype
  条件: [有限类型 α] (p : α -> 命题) [有限类型 {a // p a}] [DecidablePred p]
  证明: by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]

Depends on / 依赖: Fintype, Fintype.card_of_subtype, card_of_subtype
-/
theorem Fintype.card_subtype [Fintype α] (p : α -> Prop) [Fintype {a // p a}] [DecidablePred p] :
    Fintype.card { x // p x } = #{x | p x} := by
  refine Fintype.card_of_subtype _ ?_
  simp

@[simp]
/--
theorem `Fintype.card_subtype_compl` / 定理 `Fintype.card_subtype_compl`

English:
theorem Fintype.card_subtype_compl
  statement: [Fintype α] (p : α -> Prop) [Fintype { x // p x }]
  proof: by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ)]; rw [Set.toFinset_compl]; rw [Finset.card_compl]; rw [Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_ofPred]

中文:
定理 有限类型.card_subtype_compl
  结论: [有限类型 α] (p : α -> 命题) [有限类型 { x // p x }]
  证明: by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ)]; rw [Set.toFinset_compl]; rw [Finset.card_compl]; rw [Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_ofPred]

Depends on / 依赖: Finset, Finset.card_compl, Fintype, Fintype.card_of_subtype, Set.mem_compl_iff, Set.mem_ofPred, Set.mem_toFinset, Set.toFinset, Set.toFinset_compl, card_compl, card_of_subtype, classical, mem_compl_iff, mem_ofPred, mem_toFinset, toFinset, toFinset_compl
-/
theorem Fintype.card_subtype_compl [Fintype α] (p : α -> Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
    rw [Fintype.card_of_subtype (Set.toFinset { x | p x }ᶜ)]; rw [Set.toFinset_compl]; rw [Finset.card_compl]; rw [Fintype.card_of_subtype] <;>
    · intro
      simp only [Set.mem_toFinset, Set.mem_compl_iff, Set.mem_ofPred]

/--
theorem `Fintype.card_subtype_mono` / 定理 `Fintype.card_subtype_mono`

English:
theorem Fintype.card_subtype_mono
  statement: (p q : α -> Prop) (h : p <= q) [Fintype { x // p x }]
  proof: Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

中文:
定理 有限类型.card_subtype_mono
  结论: (p q : α -> 命题) (h : p <= q) [有限类型 { x // p x }]
  证明: Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

Depends on / 依赖: Fintype, Fintype.card_le_of_embedding, Subtype, Subtype.impEmbedding, card_le_of_embedding, impEmbedding
-/
theorem Fintype.card_subtype_mono (p q : α -> Prop) (h : p <= q) [Fintype { x // p x }]
    [Fintype { x // q x }] : Fintype.card { x // p x } <= Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

/--
theorem `Fintype.card_compl_eq_card_compl` / 定理 `Fintype.card_compl_eq_card_compl`

English:
theorem Fintype.card_compl_eq_card_compl
  statement: [Finite α] (p q : α -> Prop) [Fintype { x // p x }]
  proof: by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]

中文:
定理 有限类型.card_compl_eq_card_compl
  结论: [有限 α] (p q : α -> 命题) [有限类型 { x // p x }]
  证明: by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]

Depends on / 依赖: Fintype, Fintype.card_subtype_compl, card_subtype_compl, nonempty_fintype
-/
theorem Fintype.card_compl_eq_card_compl [Finite α] (p q : α -> Prop) [Fintype { x // p x }]
    [Fintype { x // ¬p x }] [Fintype { x // q x }] [Fintype { x // ¬q x }]
    (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  cases nonempty_fintype α
  simp only [Fintype.card_subtype_compl, h]

/--
theorem `Fintype.card_quotient_le` / 定理 `Fintype.card_quotient_le`

English:
theorem Fintype.card_quotient_le
  statement: [Fintype α] (s : Setoid α)
  proof: Fintype.card_le_of_surjective _ Quotient.mk'_surjective

中文:
定理 有限类型.card_quotient_le
  结论: [有限类型 α] (s : 集合等价关系 α)
  证明: Fintype.card_le_of_surjective _ Quotient.mk'_surjective

Depends on / 依赖: Fintype, Fintype.card_le_of_surjective, Quotient, Quotient.mk, _surjective, card_le_of_surjective
-/
theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α)
    [DecidableRel ((· ≈ ·) : α -> α -> Prop)] : Fintype.card (Quotient s) <= Fintype.card α :=
  Fintype.card_le_of_surjective _ Quotient.mk'_surjective

/--
theorem `univ_eq_singleton_of_card_one` / 定理 `univ_eq_singleton_of_card_one`

English:
theorem univ_eq_singleton_of_card_one
  given: {α} [Fintype α] (x : α) (h : Fintype.card α = 1)
  proof: by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  simp [h]

中文:
定理 univ_eq_singleton_of_card_one
  条件: {α} [有限类型 α] (x : α) (h : 有限类型.card α = 1)
  证明: by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  simp [h]

Depends on / 依赖: eq_of_subset_of_card_le, subset_univ
-/
theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) :
    (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  simp [h]

namespace Finite

variable [Finite α]

/--
theorem `wellFounded_of_trans_of_irrefl` / 定理 `wellFounded_of_trans_of_irrefl`

English:
theorem wellFounded_of_trans_of_irrefl
  given: (r : α -> α -> Prop) [IsTrans α r] [Std.Irrefl r]
  proof: by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
Finset.card_lt_card by
      simp_rw [lt_iff_le_not_ge, Finset.subset_iff, mem_filter_univ]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.n

中文:
定理 wellFounded_of_trans_of_irrefl
  条件: (r : α -> α -> 命题) [是Trans α r] [Std.Irrefl r]
  证明: by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
Finset.card_lt_card by
      simp_rw [lt_iff_le_not_ge, Finset.subset_iff, mem_filter_univ]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.n

Depends on / 依赖: Classical, Classical.not_imp, Finset, Finset.card_lt_card, Finset.subset_iff, Subrelation, Subrelation.wf, _root_, _root_.trans, card_lt_card, classical, irrefl, lt_iff_le_not_ge, measure, mem_filter_univ, nonempty_fintype, not_forall_of_exists_not, not_imp, simp_rw, subset_iff
-/
theorem wellFounded_of_trans_of_irrefl (r : α -> α -> Prop) [IsTrans α r] [Std.Irrefl r] :
    WellFounded r := by
  classical
  cases nonempty_fintype α
  have (x y) (hxy : r x y) : #{z | r z x} < #{z | r z y} :=
Finset.card_lt_card by
      simp_rw [lt_iff_le_not_ge, Finset.subset_iff, mem_filter_univ]
      exact
        ⟨fun z hzx => _root_.trans hzx hxy,
          not_forall_of_exists_not ⟨x, Classical.not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
  exact Subrelation.wf (this _ _) (measure _).wf

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) to_wellFoundedLT [Preorder α] : WellFoundedLT α :=
  ⟨wellFounded_of_trans_of_irrefl _⟩

end Finite

-- Shortcut instances to make sure those are found even in the presence of other instances
-- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/WellFoundedLT.20Prop.20is.20not.20found.20when.20importing.20too.20much
/--
Instance `Bool.instWellFoundedLT` / 实例 `Bool.instWellFoundedLT`

English:
instance Bool.instWellFoundedLT
  signature: : WellFoundedLT Bool
  body: inferInstance

中文:
实例 布尔值.instWellFoundedLT
  签名: : WellFoundedLT 布尔值
  定义体: inferInstance
-/
instance Bool.instWellFoundedLT : WellFoundedLT Bool := inferInstance
/--
Instance `Bool.instWellFoundedGT` / 实例 `Bool.instWellFoundedGT`

English:
instance Bool.instWellFoundedGT
  signature: : WellFoundedGT Bool
  body: inferInstance

中文:
实例 布尔值.instWellFoundedGT
  签名: : WellFoundedGT 布尔值
  定义体: inferInstance
-/
instance Bool.instWellFoundedGT : WellFoundedGT Bool := inferInstance
/--
Instance `Prop.instWellFoundedLT` / 实例 `Prop.instWellFoundedLT`

English:
instance Prop.instWellFoundedLT
  signature: : WellFoundedLT Prop
  body: inferInstance

中文:
实例 命题.instWellFoundedLT
  签名: : WellFoundedLT 命题
  定义体: inferInstance
-/
instance Prop.instWellFoundedLT : WellFoundedLT Prop := inferInstance
/--
Instance `Prop.instWellFoundedGT` / 实例 `Prop.instWellFoundedGT`

English:
instance Prop.instWellFoundedGT
  signature: : WellFoundedGT Prop
  body: inferInstance

中文:
实例 命题.instWellFoundedGT
  签名: : WellFoundedGT 命题
  定义体: inferInstance
-/
instance Prop.instWellFoundedGT : WellFoundedGT Prop := inferInstance

section Trunc

/--
Definition of `truncOfCardPos` / `truncOfCardPos` 的定义

English:
definition truncOfCardPos
  signature: {α} [Fintype α] (h : 0 < Fintype.card α)
  body: letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

中文:
定义 truncOfCardPos
  签名: {α} [有限类型 α] (h : 0 < 有限类型.card α)
  定义体: letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

Depends on / 依赖: Fintype, Fintype.card_pos_iff.mp, card_pos_iff, truncOfNonemptyFintype
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α :=
  letI := Fintype.card_pos_iff.mp h
  truncOfNonemptyFintype α

end Trunc

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `Fintype.card`).

The major premise is `Fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_elim]
/--
theorem `Fintype.induction_subsingleton_or_nontrivial` / 定理 `Fintype.induction_subsingleton_or_nontrivial`

English:
theorem Fintype.induction_subsingleton_or_nontrivial
  statement: {P : forall (α) [Fintype α], Prop} (α : Type*)
  proof: by
  obtain ⟨n, hn⟩ : exists n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.

中文:
定理 有限类型.induction_subsingleton_or_nontrivial
  结论: {P : 对任意 (α) [有限类型 α], 命题} (α : 类型)
  证明: by
  obtain ⟨n, hn⟩ : exists n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.

Depends on / 依赖: Fintype, Fintype.card, Nat.strong_induction_on, generalizing, hnontriv, strong_induction_on, subsingleton_or_nontrivial
-/
theorem Fintype.induction_subsingleton_or_nontrivial {P : forall (α) [Fintype α], Prop} (α : Type*)
    [Fintype α] (hbase : forall (α) [Fintype α] [Subsingleton α], P α)
    (hstep : forall (α) [Fintype α] [Nontrivial α],
      (forall (β) [Fintype β], Fintype.card β < Fintype.card α -> P β) -> P α) :
    P α := by
  obtain ⟨n, hn⟩ : exists n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl

section Fin

@[simp]
/--
theorem `Fintype.card_fin` / 定理 `Fintype.card_fin`

English:
theorem Fintype.card_fin
  given: (n : Nat)
  statement: Fintype.card (Fin n) = n
  proof: List.length_finRange

中文:
定理 有限类型.card_fin
  条件: (n : 自然数)
  结论: 有限类型.card (有限集 n) = n
  证明: List.length_finRange

Depends on / 依赖: List.length_finRange, length_finRange
-/
theorem Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n :=
  List.length_finRange

/--
theorem `Fintype.card_fin_lt_of_le` / 定理 `Fintype.card_fin_lt_of_le`

English:
theorem Fintype.card_fin_lt_of_le
  given: {m n : Nat} (h : m <= n)
  proof: by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ => ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ => ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩ }

中文:
定理 有限类型.card_fin_lt_of_le
  条件: {m n : 自然数} (h : m <= n)
  证明: by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ => ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ => ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩ }

Depends on / 依赖: Fintype, Fintype.card_congr, Fintype.card_fin, card_congr, card_fin, conv_rhs, invFun, lt_of_lt_of_le
-/
theorem Fintype.card_fin_lt_of_le {m n : Nat} (h : m <= n) :
    Fintype.card {i : Fin n // i < m} = m := by
  conv_rhs => rw [← Fintype.card_fin m]
  apply Fintype.card_congr
  exact { toFun := fun ⟨⟨i, _⟩, hi⟩ => ⟨i, hi⟩
          invFun := fun ⟨i, hi⟩ => ⟨⟨i, lt_of_lt_of_le hi h⟩, hi⟩ }

/--
theorem `Finset.card_fin` / 定理 `Finset.card_fin`

English:
theorem Finset.card_fin
  given: (n : Nat)
  statement: #(univ : Finset (Fin n)) = n
  proof: by simp

中文:
定理 有限集.card_fin
  条件: (n : 自然数)
  结论: #(univ : 有限集 (有限集 n)) = n
  证明: by simp
-/
theorem Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = n := by simp

/--
theorem `fin_injective` / 定理 `fin_injective`

English:
theorem fin_injective
  statement: Function.Injective Fin
  proof: fun m n h =>
(Fintype.card_fin m).symm.trans (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)

中文:
定理 fin_injective
  结论: 函数.单射 有限集
  证明: fun m n h =>
(Fintype.card_fin m).symm.trans (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)
-/
theorem fin_injective : Function.Injective Fin := fun m n h =>
(Fintype.card_fin m).symm.trans (Fintype.card_congr <| Equiv.cast h).trans (Fintype.card_fin n)

/--
theorem `Fin.val_eq_val_of_heq` / 定理 `Fin.val_eq_val_of_heq`

English:
theorem Fin.val_eq_val_of_heq
  given: {k l : Nat} {i : Fin k} {j : Fin l} (h : i ≍ j)
  proof: (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

中文:
定理 有限集.val_eq_val_of_heq
  条件: {k l : 自然数} {i : 有限集 k} {j : 有限集 l} (h : i ≍ j)
  证明: (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

Depends on / 依赖: Fin.heq_ext_iff, fin_injective, heq_ext_iff, type_eq_of_heq
-/
theorem Fin.val_eq_val_of_heq {k l : Nat} {i : Fin k} {j : Fin l} (h : i ≍ j) :
    (i : Nat) = (j : Nat) :=
  (Fin.heq_ext_iff (fin_injective (type_eq_of_heq h))).1 h

/--
theorem `Fin.cast_eq_cast'` / 定理 `Fin.cast_eq_cast'`

English:
theorem Fin.cast_eq_cast'
  given: {n m : Nat} (h : Fin n = Fin m)
  proof: by
  cases fin_injective h
  rfl

中文:
定理 有限集.cast_eq_cast'
  条件: {n m : 自然数} (h : 有限集 n = 有限集 m)
  证明: by
  cases fin_injective h
  rfl

Depends on / 依赖: fin_injective
-/
theorem Fin.cast_eq_cast' {n m : Nat} (h : Fin n = Fin m) :
    _root_.cast h = Fin.cast (fin_injective h) := by
  cases fin_injective h
  rfl

/--
theorem `card_finset_fin_le` / 定理 `card_finset_fin_le`

English:
theorem card_finset_fin_le
  given: {n : Nat} (s : Finset (Fin n))
  statement: #s <= n
  proof: by
  simpa only [Fintype.card_fin] using s.card_le_univ

中文:
定理 card_finset_fin_le
  条件: {n : 自然数} (s : 有限集 (有限集 n))
  结论: #s <= n
  证明: by
  simpa only [Fintype.card_fin] using s.card_le_univ

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, card_le_univ, s.card_le_univ
-/
theorem card_finset_fin_le {n : Nat} (s : Finset (Fin n)) : #s <= n := by
  simpa only [Fintype.card_fin] using s.card_le_univ

end Fin
