/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Big operators

In this file we prove theorems about products and sums over a `Finset.powerset`.

-/

public section

variable {α β γ : Type*}

variable {s : Finset α} {a : α}

namespace Finset

variable [CommMonoid β]

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
/--
lemma `prod_powerset_insert` / 引理 `prod_powerset_insert`

English:
lemma prod_powerset_insert
  given: [DecidableEq α] (ha : a ∉ s) (f : Finset α -> β)
  proof: by
  rw [powerset_insert]; rw [prod_union]; rw [prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht => notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

中文:
引理 prod_powerset_insert
  条件: [DecidableEq α] (ha : a ∉ s) (f : Finset α -> β)
  证明: by
  rw [powerset_insert]; rw [prod_union]; rw [prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht => notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

Depends on / 依赖: disjoint_left, injOn.mono, insert_erase_invOn, insert_subset_iff, mem_powerset, notMem_mono, powerset_insert, prod_image, prod_union
-/
lemma prod_powerset_insert [DecidableEq α] (ha : a ∉ s) (f : Finset α -> β) :
    ∏ t in (insert a s).powerset, f t =
      (∏ t in s.powerset, f t) * ∏ t in s.powerset, f (insert a t) := by
  rw [powerset_insert]; rw [prod_union]; rw [prod_image]
  · exact insert_erase_invOn.2.injOn.mono fun t ht => notMem_mono (mem_powerset.1 ht) ha
  · aesop (add simp [disjoint_left, insert_subset_iff])

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive /-- A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all
subsets of `s`, and over all subsets of `s` to which one adds `x`. -/]
/--
lemma `prod_powerset_cons` / 引理 `prod_powerset_cons`

English:
lemma prod_powerset_cons
  given: (ha : a ∉ s) (f : Finset α -> β)
  proof: by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha]; rw [prod_attach _ fun t => f (insert a t)]

中文:
引理 prod_powerset_cons
  条件: (ha : a ∉ s) (f : Finset α -> β)
  证明: by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha]; rw [prod_attach _ fun t => f (insert a t)]

Depends on / 依赖: classical, cons_eq_insert, insert, prod_attach, prod_powerset_insert, simp_rw
-/
lemma prod_powerset_cons (ha : a ∉ s) (f : Finset α -> β) :
    ∏ t in (s.cons a ha).powerset, f t = (∏ t in s.powerset, f t) *
      ∏ t in s.powerset.attach, f (cons a t <| notMem_mono (mem_powerset.1 t.2) ha) := by
  classical
  simp_rw [cons_eq_insert]
  rw [prod_powerset_insert ha]; rw [prod_attach _ fun t => f (insert a t)]

set_option backward.isDefEq.respectTransparency false in
/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`#s = k`, for `k = 0, ..., #s`. -/
@[to_additive /-- A sum over `powerset s` is equal to the double sum over sets of subsets of `s`
with `#s = k`, for `k = 0, ..., #s` -/]
/--
lemma `prod_powerset` / 引理 `prod_powerset`

English:
lemma prod_powerset
  given: (s : Finset α) (f : Finset α -> β)
  proof: by
  rw [powerset_card_disjiUnion]; rw [prod_disjiUnion]

中文:
引理 prod_powerset
  条件: (s : Finset α) (f : Finset α -> β)
  证明: by
  rw [powerset_card_disjiUnion]; rw [prod_disjiUnion]

Depends on / 依赖: powerset_card_disjiUnion, prod_disjiUnion
-/
lemma prod_powerset (s : Finset α) (f : Finset α -> β) :
    ∏ t in powerset s, f t = ∏ j in range (#s + 1), ∏ t in powersetCard j s, f t := by
  rw [powerset_card_disjiUnion]; rw [prod_disjiUnion]

/-- A product over `Finset.powersetCard` which only depends on the size of the sets is constant. -/
@[to_additive
/-- A sum over `Finset.powersetCard` which only depends on the size of the sets is constant. -/]
/--
lemma `prod_powersetCard` / 引理 `prod_powersetCard`

English:
lemma prod_powersetCard
  given: (n : Nat) (s : Finset α) (f : Nat -> β)
  proof: by
  rw [prod_eq_pow_card]; rw [card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

中文:
引理 prod_powersetCard
  条件: (n : 自然数) (s : Finset α) (f : 自然数 -> β)
  证明: by
  rw [prod_eq_pow_card]; rw [card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

Depends on / 依赖: card_powersetCard, mem_powersetCard, prod_eq_pow_card
-/
lemma prod_powersetCard (n : Nat) (s : Finset α) (f : Nat -> β) :
    ∏ t in powersetCard n s, f #t = f n ^ (#s).choose n := by
  rw [prod_eq_pow_card]; rw [card_powersetCard]; rintro a ha; rw [(mem_powersetCard.1 ha).2]

end Finset
