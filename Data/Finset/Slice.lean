/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# `r`-sets and slice

This file defines the `r`-th slice of a set family and provides a way to say that a set family is
made of `r`-sets.

An `r`-set is a finset of cardinality `r` (aka of *size* `r`). The `r`-th slice of a set family is
the set family made of its `r`-sets.

## Main declarations

* `Set.Sized`: `A.Sized r` means that `A` only contains `r`-sets.
* `Finset.slice`: `A.slice r` is the set of `r`-sets in `A`.

## Notation

`A # r` is notation for `A.slice r` in scope `finset_family`.
-/

@[expose] public section


open Finset Nat

variable {α : Type*} {ι : Sort*} {κ : ι -> Sort*}

namespace Set

variable {A B : Set (Finset α)} {s : Finset α} {r : Nat}

/-! ### Families of `r`-sets -/


/--
Definition of `Sized` / `Sized` 的定义

English:
definition Sized
  signature: (r : Nat) (A : Set (Finset α))
  body: forall ⦃x⦄, x in A -> #x = r

中文:
定义 Sized
  签名: (r : 自然数) (A : Set (Finset α))
  定义体: forall ⦃x⦄, x in A -> #x = r
-/
def Sized (r : Nat) (A : Set (Finset α)) : Prop := forall ⦃x⦄, x in A -> #x = r

/--
theorem `Sized.mono` / 定理 `Sized.mono`

English:
theorem Sized.mono
  given: (h : A subseteq B) (hB : B.Sized r)
  statement: A.Sized r
  proof: fun _x hx => hB h hx

中文:
定理 Sized.mono
  条件: (h : A subseteq B) (hB : B.Sized r)
  结论: A.Sized r
  证明: fun _x hx => hB h hx
-/
theorem Sized.mono (h : A subseteq B) (hB : B.Sized r) : A.Sized r := fun _x hx => hB h hx

/--
lemma `sized_empty` / 引理 `sized_empty`

English:
lemma sized_empty
  statement: (∅ : Set (Finset α)).Sized r
  proof: by simp [Sized]

中文:
引理 sized_empty
  结论: (∅ : Set (Finset α)).Sized r
  证明: by simp [Sized]
-/
@[simp] lemma sized_empty : (∅ : Set (Finset α)).Sized r := by simp [Sized]
/--
lemma `sized_singleton` / 引理 `sized_singleton`

English:
lemma sized_singleton
  statement: ({s} : Set (Finset α)).Sized r ↔ #s = r
  proof: by simp [Sized]

中文:
引理 sized_singleton
  结论: ({s} : Set (Finset α)).Sized r ↔ #s = r
  证明: by simp [Sized]
-/
@[simp] lemma sized_singleton : ({s} : Set (Finset α)).Sized r ↔ #s = r := by simp [Sized]

/--
theorem `sized_union` / 定理 `sized_union`

English:
theorem sized_union
  statement: (A union B).Sized r ↔ A.Sized r ∧ B.Sized r
  proof: ⟨fun hA => ⟨hA.mono subset_union_left, hA.mono subset_union_right⟩, fun hA _x hx =>
    hx.elim (fun h => hA.1 h) fun h => hA.2 h⟩

alias ⟨_, sized.union⟩ := sized_union

中文:
定理 sized_union
  结论: (A union B).Sized r ↔ A.Sized r ∧ B.Sized r
  证明: ⟨fun hA => ⟨hA.mono subset_union_left, hA.mono subset_union_right⟩, fun hA _x hx =>
    hx.elim (fun h => hA.1 h) fun h => hA.2 h⟩

alias ⟨_, sized.union⟩ := sized_union

Depends on / 依赖: hA.mono, hx.elim, subset_union_left, subset_union_right
-/
theorem sized_union : (A union B).Sized r ↔ A.Sized r ∧ B.Sized r :=
  ⟨fun hA => ⟨hA.mono subset_union_left, hA.mono subset_union_right⟩, fun hA _x hx =>
    hx.elim (fun h => hA.1 h) fun h => hA.2 h⟩

alias ⟨_, sized.union⟩ := sized_union

--TODO: A `forall_iUnion` lemma would be handy here.
@[simp]
/--
theorem `sized_iUnion` / 定理 `sized_iUnion`

English:
theorem sized_iUnion
  given: {f : ι -> Set (Finset α)}
  statement: (⋃ i, f i).Sized r ↔ forall i, (f i).Sized r
  proof: by
  simp_rw [Set.Sized, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

中文:
定理 sized_iUnion
  条件: {f : ι -> Set (Finset α)}
  结论: (⋃ i, f i).Sized r ↔ 对任意 i, (f i).Sized r
  证明: by
  simp_rw [Set.Sized, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

Depends on / 依赖: Set.Sized, Set.mem_iUnion, forall_comm, forall_exists_index, mem_iUnion, simp_rw
-/
theorem sized_iUnion {f : ι -> Set (Finset α)} : (⋃ i, f i).Sized r ↔ forall i, (f i).Sized r := by
  simp_rw [Set.Sized, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

-- `simp` normal form is `sized_iUnion`.
/--
theorem `sized_iUnion₂` / 定理 `sized_iUnion₂`

English:
theorem sized_iUnion₂
  given: {f : forall i, κ i -> Set (Finset α)}
  proof: by
  simp only [Set.sized_iUnion]

中文:
定理 sized_iUnion₂
  条件: {f : 对任意 i, κ i -> Set (Finset α)}
  证明: by
  simp only [Set.sized_iUnion]

Depends on / 依赖: Set.sized_iUnion, sized_iUnion
-/
theorem sized_iUnion₂ {f : forall i, κ i -> Set (Finset α)} :
    (⋃ (i) (j), f i j).Sized r ↔ forall i j, (f i j).Sized r := by
  simp only [Set.sized_iUnion]

/--
theorem `Sized.isAntichain` / 定理 `Sized.isAntichain`

English:
theorem Sized.isAntichain
  given: (hA : A.Sized r)
  statement: IsAntichain (· subseteq ·) A
  proof: fun _s hs _t ht h hst => h Finset.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le

中文:
定理 Sized.isAntichain
  条件: (hA : A.Sized r)
  结论: IsAntichain (· subseteq ·) A
  证明: fun _s hs _t ht h hst => h Finset.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le
-/
protected theorem Sized.isAntichain (hA : A.Sized r) : IsAntichain (· subseteq ·) A :=
fun _s hs _t ht h hst => h Finset.eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le

/--
theorem `Sized.subsingleton` / 定理 `Sized.subsingleton`

English:
theorem Sized.subsingleton
  given: (hA : A.Sized 0)
  statement: A.Subsingleton
  proof: subsingleton_of_forall_eq ∅ fun _s hs => card_eq_zero.1 hA hs

中文:
定理 Sized.subsingleton
  条件: (hA : A.Sized 0)
  结论: A.Subsingleton
  证明: subsingleton_of_forall_eq ∅ fun _s hs => card_eq_zero.1 hA hs
-/
protected theorem Sized.subsingleton (hA : A.Sized 0) : A.Subsingleton :=
subsingleton_of_forall_eq ∅ fun _s hs => card_eq_zero.1 hA hs

/--
theorem `Sized.subsingleton'` / 定理 `Sized.subsingleton'`

English:
theorem Sized.subsingleton'
  given: [Fintype α] (hA : A.Sized (Fintype.card α))
  statement: A.Subsingleton
  proof: subsingleton_of_forall_eq Finset.univ fun s hs => s.card_eq_iff_eq_univ.1 hA hs

中文:
定理 Sized.subsingleton'
  条件: [Fintype α] (hA : A.Sized (Fintype.card α))
  结论: A.Subsingleton
  证明: subsingleton_of_forall_eq Finset.univ fun s hs => s.card_eq_iff_eq_univ.1 hA hs

Depends on / 依赖: Finset, Finset.univ, card_eq_iff_eq_univ, s.card_eq_iff_eq_univ, subsingleton_of_forall_eq
-/
theorem Sized.subsingleton' [Fintype α] (hA : A.Sized (Fintype.card α)) : A.Subsingleton :=
subsingleton_of_forall_eq Finset.univ fun s hs => s.card_eq_iff_eq_univ.1 hA hs

/--
theorem `Sized.empty_mem_iff` / 定理 `Sized.empty_mem_iff`

English:
theorem Sized.empty_mem_iff
  given: (hA : A.Sized r)
  statement: ∅ in A ↔ A = {∅}
  proof: hA.isAntichain.bot_mem_iff

中文:
定理 Sized.empty_mem_iff
  条件: (hA : A.Sized r)
  结论: ∅ in A ↔ A = {∅}
  证明: hA.isAntichain.bot_mem_iff

Depends on / 依赖: bot_mem_iff, divMod_to_nat, hA.isAntichain.bot_mem_iff, isAntichain
-/
theorem Sized.empty_mem_iff (hA : A.Sized r) : ∅ in A ↔ A = {∅} :=
  hA.isAntichain.bot_mem_iff

/--
theorem `Sized.univ_mem_iff` / 定理 `Sized.univ_mem_iff`

English:
theorem Sized.univ_mem_iff
  given: [Fintype α] (hA : A.Sized r)
  statement: Finset.univ in A ↔ A = {Finset.univ}
  proof: hA.isAntichain.top_mem_iff

中文:
定理 Sized.univ_mem_iff
  条件: [Fintype α] (hA : A.Sized r)
  结论: Finset.univ in A ↔ A = {Finset.univ}
  证明: hA.isAntichain.top_mem_iff

Depends on / 依赖: divMod_to_nat, hA.isAntichain.top_mem_iff, isAntichain, top_mem_iff
-/
theorem Sized.univ_mem_iff [Fintype α] (hA : A.Sized r) : Finset.univ in A ↔ A = {Finset.univ} :=
  hA.isAntichain.top_mem_iff

/--
theorem `sized_powersetCard` / 定理 `sized_powersetCard`

English:
theorem sized_powersetCard
  given: (s : Finset α) (r : Nat)
  statement: (powersetCard r s : Set (Finset α)).Sized r
  proof: fun _t ht => (mem_powersetCard.1 ht).2

中文:
定理 sized_powersetCard
  条件: (s : Finset α) (r : 自然数)
  结论: (powersetCard r s : Set (Finset α)).Sized r
  证明: fun _t ht => (mem_powersetCard.1 ht).2

Depends on / 依赖: mem_powersetCard
-/
theorem sized_powersetCard (s : Finset α) (r : Nat) : (powersetCard r s : Set (Finset α)).Sized r :=
  fun _t ht => (mem_powersetCard.1 ht).2

end Set

namespace Finset

section Sized

variable [Fintype α] {𝒜 : Finset (Finset α)} {s : Finset α} {r : Nat}

/--
theorem `subset_powersetCard_univ_iff` / 定理 `subset_powersetCard_univ_iff`

English:
theorem subset_powersetCard_univ_iff
  statement: 𝒜 subseteq powersetCard r univ ↔ (𝒜 : Set (Finset α)).Sized r
  proof: forall_congr' fun A => by rw [mem_powersetCard_univ, mem_coe]

alias ⟨_, _root_.Set.Sized.subset_powersetCard_univ⟩ := subset_powersetCard_univ_iff

中文:
定理 subset_powersetCard_univ_iff
  结论: 𝒜 subseteq powersetCard r univ ↔ (𝒜 : Set (Finset α)).Sized r
  证明: forall_congr' fun A => by rw [mem_powersetCard_univ, mem_coe]

alias ⟨_, _root_.Set.Sized.subset_powersetCard_univ⟩ := subset_powersetCard_univ_iff

Depends on / 依赖: forall_congr, mem_coe, mem_powersetCard_univ
-/
theorem subset_powersetCard_univ_iff : 𝒜 subseteq powersetCard r univ ↔ (𝒜 : Set (Finset α)).Sized r :=
  forall_congr' fun A => by rw [mem_powersetCard_univ, mem_coe]

alias ⟨_, _root_.Set.Sized.subset_powersetCard_univ⟩ := subset_powersetCard_univ_iff

/--
theorem `_root_.Set.Sized.card_le` / 定理 `_root_.Set.Sized.card_le`

English:
theorem _root_.Set.Sized.card_le
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  proof: by
  rw [Fintype.card]; rw [← card_powersetCard]
  exact card_le_card (subset_powersetCard_univ_iff.mpr h𝒜)

中文:
定理 _root_.Set.Sized.card_le
  条件: (h𝒜 : (𝒜 : Set (Finset α)).Sized r)
  证明: by
  rw [Fintype.card]; rw [← card_powersetCard]
  exact card_le_card (subset_powersetCard_univ_iff.mpr h𝒜)

Depends on / 依赖: Fintype, Fintype.card, card_le_card, card_powersetCard, subset_powersetCard_univ_iff, subset_powersetCard_univ_iff.mpr
-/
theorem _root_.Set.Sized.card_le (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 <= (Fintype.card α).choose r := by
  rw [Fintype.card]; rw [← card_powersetCard]
  exact card_le_card (subset_powersetCard_univ_iff.mpr h𝒜)

end Sized

/-! ### Slices -/


section Slice

variable {𝒜 : Finset (Finset α)} {A A₁ A₂ : Finset α} {r r₁ r₂ : Nat}

/--
Definition of `slice` / `slice` 的定义

English:
definition slice
  signature: (𝒜 : Finset (Finset α)) (r : Nat)
  body: {A in 𝒜 | #A = r}

@[inherit_doc]
scoped[Finset] infixl:90 " # " => Finset.slice

中文:
定义 slice
  签名: (𝒜 : Finset (Finset α)) (r : 自然数)
  定义体: {A in 𝒜 | #A = r}

@[inherit_doc]
scoped[Finset] infixl:90 " # " => Finset.slice
-/
def slice (𝒜 : Finset (Finset α)) (r : Nat) : Finset (Finset α) := {A in 𝒜 | #A = r}

@[inherit_doc]
scoped[Finset] infixl:90 " # " => Finset.slice

/--
theorem `mem_slice` / 定理 `mem_slice`

English:
theorem mem_slice
  statement: A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r
  proof: mem_filter

中文:
定理 mem_slice
  结论: A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r
  证明: mem_filter

Depends on / 依赖: mem_filter
-/
theorem mem_slice : A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r :=
  mem_filter

/--
theorem `slice_subset` / 定理 `slice_subset`

English:
theorem slice_subset
  statement: 𝒜 # r subseteq 𝒜
  proof: filter_subset _ _

中文:
定理 slice_subset
  结论: 𝒜 # r subseteq 𝒜
  证明: filter_subset _ _

Depends on / 依赖: filter_subset
-/
theorem slice_subset : 𝒜 # r subseteq 𝒜 :=
  filter_subset _ _

/--
theorem `sized_slice` / 定理 `sized_slice`

English:
theorem sized_slice
  statement: (𝒜 # r : Set (Finset α)).Sized r
  proof: fun _ => And.right ∘ mem_slice.mp

中文:
定理 sized_slice
  结论: (𝒜 # r : Set (Finset α)).Sized r
  证明: fun _ => And.right ∘ mem_slice.mp

Depends on / 依赖: And.right, mem_slice, mem_slice.mp
-/
theorem sized_slice : (𝒜 # r : Set (Finset α)).Sized r := fun _ => And.right ∘ mem_slice.mp

/--
theorem `eq_of_mem_slice` / 定理 `eq_of_mem_slice`

English:
theorem eq_of_mem_slice
  given: (h₁ : A in 𝒜 # r₁) (h₂ : A in 𝒜 # r₂)
  statement: r₁ = r₂
  proof: (sized_slice h₁).symm.trans sized_slice h₂

中文:
定理 eq_of_mem_slice
  条件: (h₁ : A in 𝒜 # r₁) (h₂ : A in 𝒜 # r₂)
  结论: r₁ = r₂
  证明: (sized_slice h₁).symm.trans sized_slice h₂

Depends on / 依赖: sized_slice, symm.trans
-/
theorem eq_of_mem_slice (h₁ : A in 𝒜 # r₁) (h₂ : A in 𝒜 # r₂) : r₁ = r₂ :=
(sized_slice h₁).symm.trans sized_slice h₂

/--
theorem `ne_of_mem_slice` / 定理 `ne_of_mem_slice`

English:
theorem ne_of_mem_slice
  given: (h₁ : A₁ in 𝒜 # r₁) (h₂ : A₂ in 𝒜 # r₂)
  statement: r₁ != r₂ -> A₁ != A₂
  proof: mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

中文:
定理 ne_of_mem_slice
  条件: (h₁ : A₁ in 𝒜 # r₁) (h₂ : A₂ in 𝒜 # r₂)
  结论: r₁ != r₂ -> A₁ != A₂
  证明: mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

Depends on / 依赖: congr_arg, sized_slice, symm.trans
-/
theorem ne_of_mem_slice (h₁ : A₁ in 𝒜 # r₁) (h₂ : A₂ in 𝒜 # r₂) : r₁ != r₂ -> A₁ != A₂ :=
  mt fun h => (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

/--
theorem `pairwiseDisjoint_slice` / 定理 `pairwiseDisjoint_slice`

English:
theorem pairwiseDisjoint_slice
  statement: (Set.univ : Set Nat).PairwiseDisjoint (slice 𝒜)
  proof: fun _ _ _ _ hmn =>
disjoint_filter.2 fun _s _hs hm hn => hmn hm.symm.trans hn

中文:
定理 pairwiseDisjoint_slice
  结论: (Set.univ : Set 自然数).PairwiseDisjoint (slice 𝒜)
  证明: fun _ _ _ _ hmn =>
disjoint_filter.2 fun _s _hs hm hn => hmn hm.symm.trans hn
-/
theorem pairwiseDisjoint_slice : (Set.univ : Set Nat).PairwiseDisjoint (slice 𝒜) := fun _ _ _ _ hmn =>
disjoint_filter.2 fun _s _hs hm hn => hmn hm.symm.trans hn

variable [Fintype α] (𝒜)

@[simp]
/--
theorem `biUnion_slice` / 定理 `biUnion_slice`

English:
theorem biUnion_slice
  given: [DecidableEq α]
  statement: (Iic <| Fintype.card α).biUnion 𝒜.slice = 𝒜
  proof: Subset.antisymm (biUnion_subset.2 fun _r _ => slice_subset) fun s hs =>
mem_biUnion.2 ⟨#s, mem_Iic.2 s.card_le_univ, mem_slice.2 ⟨hs, rfl⟩⟩

@[simp]

中文:
定理 biUnion_slice
  条件: [DecidableEq α]
  结论: (Iic <| Fintype.card α).biUnion 𝒜.slice = 𝒜
  证明: Subset.antisymm (biUnion_subset.2 fun _r _ => slice_subset) fun s hs =>
mem_biUnion.2 ⟨#s, mem_Iic.2 s.card_le_univ, mem_slice.2 ⟨hs, rfl⟩⟩

@[simp]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, biUnion_subset, card_le_univ, mem_Iic, mem_biUnion, mem_slice, s.card_le_univ, slice_subset
-/
theorem biUnion_slice [DecidableEq α] : (Iic <| Fintype.card α).biUnion 𝒜.slice = 𝒜 :=
  Subset.antisymm (biUnion_subset.2 fun _r _ => slice_subset) fun s hs =>
mem_biUnion.2 ⟨#s, mem_Iic.2 s.card_le_univ, mem_slice.2 ⟨hs, rfl⟩⟩

@[simp]
/--
theorem `sum_card_slice` / 定理 `sum_card_slice`

English:
theorem sum_card_slice
  statement: ∑ r in Iic (Fintype.card α), #(𝒜 # r) = #𝒜
  proof: by
  let := Classical.decEq α
  rw [← card_biUnion]; rw [biUnion_slice]
  exact Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)

中文:
定理 sum_card_slice
  结论: ∑ r in Iic (Fintype.card α), #(𝒜 # r) = #𝒜
  证明: by
  let := Classical.decEq α
  rw [← card_biUnion]; rw [biUnion_slice]
  exact Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.pairwiseDisjoint_slice.subset, Set.subset_univ, biUnion_slice, card_biUnion, pairwiseDisjoint_slice, subset, subset_univ
-/
theorem sum_card_slice : ∑ r in Iic (Fintype.card α), #(𝒜 # r) = #𝒜 := by
  let := Classical.decEq α
  rw [← card_biUnion]; rw [biUnion_slice]
  exact Finset.pairwiseDisjoint_slice.subset (Set.subset_univ _)

end Slice

end Finset
