/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.RelIso.Set
public import Mathlib.Order.SupClosed
public import Mathlib.Order.SupIndep
public import Mathlib.Order.Zorn
public import Mathlib.Data.Finset.Order
public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Data.Finite.Set
public import Mathlib.Tactic.TFAE

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `IsCompactElement`
* `IsCompactlyGenerated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
* `well_founded (>)`
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `∀ k, IsCompactElement k`

This is demonstrated by means of the following four lemmas:
* `CompleteLattice.WellFounded.isSupFiniteCompact`
* `CompleteLattice.IsSupFiniteCompact.isSupClosedCompact`
* `CompleteLattice.IsSupClosedCompact.wellFounded`
* `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`

We also show well-founded lattices are compactly generated
(`CompleteLattice.isCompactlyGenerated_of_wellFounded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/

@[expose] public section

open Set
/--
Definition of `IsCompactElement` / `IsCompactElement` 的定义

English:
definition IsCompactElement
  signature: {α : Type*} [PartialOrder α] (k : α)
  body: forall (s : Set α) (u : α),
    s.Nonempty ->
    DirectedOn (· <= ·) s ->
    IsLUB s u ->
    k <= u ->
    exists x in s, k <= x

中文:
定义 IsCompactElement
  签名: {α : 类型} [偏序 α] (k : α)
  定义体: forall (s : Set α) (u : α),
    s.Nonempty ->
    DirectedOn (· <= ·) s ->
    IsLUB s u ->
    k <= u ->
    exists x in s, k <= x

Depends on / 依赖: DirectedOn, Nonempty, s.Nonempty
-/
def IsCompactElement {α : Type*} [PartialOrder α] (k : α) :=
  forall (s : Set α) (u : α),
    s.Nonempty ->
    DirectedOn (· <= ·) s ->
    IsLUB s u ->
    k <= u ->
    exists x in s, k <= x

variable {ι : Sort*} {α : Type*} [CompleteLattice α] {f : ι -> α}

namespace CompleteLattice

variable (α)

/--
Definition of `IsSupClosedCompact` / `IsSupClosedCompact` 的定义

English:
definition IsSupClosedCompact
  signature: : Prop
  body: forall (s : Set α) (_ : s.Nonempty), SupClosed s -> sSup s in s

中文:
定义 IsSupClosedCompact
  签名: : 命题
  定义体: forall (s : Set α) (_ : s.Nonempty), SupClosed s -> sSup s in s

Depends on / 依赖: Nonempty, SupClosed, s.Nonempty
-/
def IsSupClosedCompact : Prop :=
  forall (s : Set α) (_ : s.Nonempty), SupClosed s -> sSup s in s

/--
Definition of `IsSupFiniteCompact` / `IsSupFiniteCompact` 的定义

English:
definition IsSupFiniteCompact
  signature: : Prop
  body: forall s : Set α, exists t : Finset α, ↑t subseteq s ∧ sSup s = t.sup id

中文:
定义 IsSupFiniteCompact
  签名: : 命题
  定义体: forall s : Set α, exists t : Finset α, ↑t subseteq s ∧ sSup s = t.sup id

Depends on / 依赖: Finset, subseteq, t.sup
-/
def IsSupFiniteCompact : Prop :=
  forall s : Set α, exists t : Finset α, ↑t subseteq s ∧ sSup s = t.sup id

/--
theorem `isCompactElement_iff_le_of_directed_sSup_le` / 定理 `isCompactElement_iff_le_of_directed_sSup_le`

English:
theorem isCompactElement_iff_le_of_directed_sSup_le
  given: (k : α)
  proof: by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (isLUB_sSup s) h_le
  · intro h s u hs hs' hu h_le
    rw [isLUB_iff_sSup_eq] at hu
    rw [← hu] at h_le
    exact h s hs hs' h_le

中文:
定理 isCompactElement_iff_le_of_directed_sSup_le
  条件: (k : α)
  证明: by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (isLUB_sSup s) h_le
  · intro h s u hs hs' hu h_le
    rw [isLUB_iff_sSup_eq] at hu
    rw [← hu] at h_le
    exact h s hs hs' h_le

Depends on / 依赖: h_le, isLUB_iff_sSup_eq, isLUB_sSup
-/
theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      forall s : Set α, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSup s -> exists x : α, x in s ∧ k <= x := by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (isLUB_sSup s) h_le
  · intro h s u hs hs' hu h_le
    rw [isLUB_iff_sSup_eq] at hu
    rw [← hu] at h_le
    exact h s hs hs' h_le

/--
theorem `isCompactElement_iff_exists_le_sSup_of_le_sSup` / 定理 `isCompactElement_iff_exists_le_sSup_of_le_sSup`

English:
theorem isCompactElement_iff_exists_le_sSup_of_le_sSup
  given: (k : α)
  proof: by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    constructor
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | exists t : Finset α, ↑t subseteq s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· <= ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c union d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s <= sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ in S from Set.nonempty_of_mem this
        use ∅
        simp
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : forall x in t, exists y in s, x <= y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩

中文:
定理 isCompactElement_iff_存在_le_sSup_of_le_sSup
  条件: (k : α)
  证明: by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    constructor
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | exists t : Finset α, ↑t subseteq s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· <= ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c union d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s <= sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ in S from Set.nonempty_of_mem this
        use ∅
        simp
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : forall x in t, exists y in s, x <= y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩

Depends on / 依赖: classical, isCompactElement_iff_le_of_directed_sSup_le
-/
theorem isCompactElement_iff_exists_le_sSup_of_le_sSup (k : α) :
    IsCompactElement k ↔ forall s : Set α, k <= sSup s -> exists t : Finset α, ↑t subseteq s ∧ k <= t.sup id := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    constructor
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | exists t : Finset α, ↑t subseteq s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· <= ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c union d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s <= sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ in S from Set.nonempty_of_mem this
        use ∅
        simp
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : forall x in t, exists y in s, x <= y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩

/--
theorem `isCompactElement_iff_exists_le_iSup_of_le_iSup.` / 定理 `isCompactElement_iff_exists_le_iSup_of_le_iSup.`

English:
theorem isCompactElement_iff_exists_le_iSup_of_le_iSup.{u}
  statement: {α : Type u} [CompleteLattice α]
  proof: by
  classical
    rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : forall x : t, exists i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b]; rw [hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine ⟨t.image Subtype.val, by simp, ht.trans ?_⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)

中文:
定理 isCompactElement_iff_存在_le_iSup_of_le_iSup.{u}
  结论: {α : 类型u} [完备格 α]
  证明: by
  classical
    rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : forall x : t, exists i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b]; rw [hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine ⟨t.image Subtype.val, by simp, ht.trans ?_⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_image_of_mem, Finset.mem_univ, Finset.sup_le_iff, Finset.univ.image, Set.range, Subtype, Subtype.mk, Subtype.val, classical, isCompactElement_iff_exists_le_sSup_of_le_sSup, le_sup, mem_image_of_mem, mem_univ, sup_le_iff, x.prop
-/
theorem isCompactElement_iff_exists_le_iSup_of_le_iSup.{u} {α : Type u} [CompleteLattice α]
    (k : α) : IsCompactElement k ↔
      forall (ι : Type u) (s : ι -> α), k <= iSup s -> exists t : Finset ι, k <= t.sup s := by
  classical
    rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : forall x : t, exists i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b]; rw [hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine ⟨t.image Subtype.val, by simp, ht.trans ?_⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)

/--
theorem `IsCompactElement.exists_finset_of_le_iSup` / 定理 `IsCompactElement.exists_finset_of_le_iSup`

English:
theorem IsCompactElement.exists_finset_of_le_iSup
  statement: {k : α} (hk : IsCompactElement k) {ι : Type*}
  proof: by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
    let g : Finset ι -> α := fun s => ⨆ i in s, f i
    have h1 : DirectedOn (· <= ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s union t), ⟨s union t, rfl⟩, iSup_le_iSup_of_subset Finset.subset_union_left,
          iSup_le_iSup_of_subset Finset.subset_union_right⟩
    have h2 : k <= sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ := hk (Set.range g) (Set.range_nonempty g) h1 h2
    exact ⟨s, hs⟩

中文:
定理 IsCompactElement.存在_finset_of_le_iSup
  结论: {k : α} (hk : IsCompactElement k) {ι : 类型}
  证明: by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
    let g : Finset ι -> α := fun s => ⨆ i in s, f i
    have h1 : DirectedOn (· <= ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s union t), ⟨s union t, rfl⟩, iSup_le_iSup_of_subset Finset.subset_union_left,
          iSup_le_iSup_of_subset Finset.subset_union_right⟩
    have h2 : k <= sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ := hk (Set.range g) (Set.range_nonempty g) h1 h2
    exact ⟨s, hs⟩

Depends on / 依赖: DirectedOn, Finset, Finset.mem_singleton_self, Finset.subset_union_left, Finset.subset_union_right, Set.range, classical, h.trans, iSup_le, iSup_le_iSup_of_subset, isCompactElement_iff_le_of_directed_sSup_le, le_iSup_of_le, le_rfl, le_sSup_of_le, mem_singleton_self, subset_union_left, subset_union_right
-/
theorem IsCompactElement.exists_finset_of_le_iSup {k : α} (hk : IsCompactElement k) {ι : Type*}
    (f : ι -> α) (h : k <= ⨆ i, f i) : exists s : Finset ι, k <= ⨆ i in s, f i := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
    let g : Finset ι -> α := fun s => ⨆ i in s, f i
    have h1 : DirectedOn (· <= ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s union t), ⟨s union t, rfl⟩, iSup_le_iSup_of_subset Finset.subset_union_left,
          iSup_le_iSup_of_subset Finset.subset_union_right⟩
    have h2 : k <= sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ := hk (Set.range g) (Set.range_nonempty g) h1 h2
    exact ⟨s, hs⟩

/--
theorem `IsCompactElement.directed_sSup_lt_of_lt` / 定理 `IsCompactElement.directed_sSup_lt_of_lt`

English:
theorem IsCompactElement.directed_sSup_lt_of_lt
  statement: {α : Type*} [CompleteLattice α] {k : α}
  proof: by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s <= k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

中文:
定理 IsCompactElement.directed_sSup_lt_of_lt
  结论: {α : 类型} [完备格 α] {k : α}
  证明: by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s <= k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

Depends on / 依赖: antisymm, eq_iff_le_not_lt, eq_iff_le_not_lt.mpr, hbelow, hxk.le.antisymm, hxk.ne, isCompactElement_iff_le_of_directed_sSup_le, replace, sSup.symm.le, sSup_le
-/
theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type*} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· <= ·) s)
    (hbelow : forall x in s, x < k) : sSup s < k := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s <= k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

/--
theorem `isCompactElement_finsetSup` / 定理 `isCompactElement_finsetSup`

English:
theorem isCompactElement_finsetSup
  statement: {α β : Type*} [CompleteLattice α] {f : β -> α} (s : Finset β)
  proof: by
  classical
    simp_rw [isCompactElement_iff_le_of_directed_sSup_le] at ⊢ h
    intro d hemp hdir hsup
    rw [← Function.id_comp f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

中文:
定理 isCompactElement_finsetSup
  结论: {α β : 类型} [完备格 α] {f : β -> α} (s : 有限集 β)
  证明: by
  classical
    simp_rw [isCompactElement_iff_le_of_directed_sSup_le] at ⊢ h
    intro d hemp hdir hsup
    rw [← Function.id_comp f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_image.mp, Finset.sup_image, Finset.sup_le_of_le_directed, Function, Function.id_comp, classical, exists_prop, id_comp, isCompactElement_iff_le_of_directed_sSup_le, le_sup, le_trans, mem_image, simp_rw, specialize, sup_image, sup_le_of_le_directed
-/
theorem isCompactElement_finsetSup {α β : Type*} [CompleteLattice α] {f : β -> α} (s : Finset β)
    (h : forall x in s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    simp_rw [isCompactElement_iff_le_of_directed_sSup_le] at ⊢ h
    intro d hemp hdir hsup
    rw [← Function.id_comp f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

/--
theorem `WellFoundedGT.isSupFiniteCompact` / 定理 `WellFoundedGT.isSupFiniteCompact`

English:
theorem WellFoundedGT.isSupFiniteCompact
  given: [WellFoundedGT α]
  proof: fun s => by
  let S := { x | exists t : Finset α, ↑t subseteq s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t]; rw [by simp [Set.insert_subset_iff]; rw [hy]; rw [ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁

中文:
定理 WellFoundedGT.isSupFiniteCompact
  条件: [WellFoundedGT α]
  证明: fun s => by
  let S := { x | exists t : Finset α, ↑t subseteq s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t]; rw [by simp [Set.insert_subset_iff]; rw [hy]; rw [ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁

Depends on / 依赖: Finset, Finset.sup_id_eq_sSup, Finset.sup_mono, Set.insert_subset_iff, antisymm, classical, eq_of_le_of_not_lt, has_min, insert, insert_subset_iff, sSup_le, sSup_le_sSup, subset_insert, subseteq, sup_id_eq_sSup, sup_mono, t.subset_insert, t.sup, wellFounded_gt, wellFounded_gt.has_min
-/
theorem WellFoundedGT.isSupFiniteCompact [WellFoundedGT α] :
    IsSupFiniteCompact α := fun s => by
  let S := { x | exists t : Finset α, ↑t subseteq s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t]; rw [by simp [Set.insert_subset_iff]; rw [hy]; rw [ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁

/--
theorem `IsSupFiniteCompact.isSupClosedCompact` / 定理 `IsSupFiniteCompact.isSupClosedCompact`

English:
theorem IsSupFiniteCompact.isSupClosedCompact
  given: (h : IsSupFiniteCompact α)
  proof: by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  rcases t.eq_empty_or_nonempty with rfl | h
  · rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact hsc.finsetSup_mem h ht₁

中文:
定理 IsSupFiniteCompact.isSupClosedCompact
  条件: (h : IsSupFiniteCompact α)
  证明: by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  rcases t.eq_empty_or_nonempty with rfl | h
  · rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact hsc.finsetSup_mem h ht₁

Depends on / 依赖: Finset, Finset.sup_empty, eq_empty_or_nonempty, eq_singleton_bot_of_sSup_eq_bot_of_nonempty, finsetSup_mem, hsc.finsetSup_mem, sup_empty, t.eq_empty_or_nonempty
-/
theorem IsSupFiniteCompact.isSupClosedCompact (h : IsSupFiniteCompact α) :
    IsSupClosedCompact α := by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  rcases t.eq_empty_or_nonempty with rfl | h
  · rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact hsc.finsetSup_mem h ht₁

/--
theorem `IsSupClosedCompact.wellFoundedGT` / 定理 `IsSupClosedCompact.wellFoundedGT`

English:
theorem IsSupClosedCompact.wellFoundedGT
  given: (h : IsSupClosedCompact α)
  statement: WellFoundedGT α
  proof: by
  rw [wellFoundedGT_iff_monotone_chain_condition']
  intro a
  obtain ⟨n, hn⟩ : sSup (range a) in range a := by
    apply h _ (range_nonempty a)
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact ⟨_, map_sup a m n⟩
  refine ⟨n, fun m hm => ?_⟩
  rw [hn]
  exact (le_sSup (mem_range_self m)).not_gt

中文:
定理 IsSupClosedCompact.wellFoundedGT
  条件: (h : IsSupClosedCompact α)
  结论: WellFoundedGT α
  证明: by
  rw [wellFoundedGT_iff_monotone_chain_condition']
  intro a
  obtain ⟨n, hn⟩ : sSup (range a) in range a := by
    apply h _ (range_nonempty a)
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact ⟨_, map_sup a m n⟩
  refine ⟨n, fun m hm => ?_⟩
  rw [hn]
  exact (le_sSup (mem_range_self m)).not_gt

Depends on / 依赖: le_sSup, map_sup, mem_range_self, not_gt, range_nonempty, wellFoundedGT_iff_monotone_chain_condition
-/
theorem IsSupClosedCompact.wellFoundedGT (h : IsSupClosedCompact α) : WellFoundedGT α := by
  rw [wellFoundedGT_iff_monotone_chain_condition']
  intro a
  obtain ⟨n, hn⟩ : sSup (range a) in range a := by
    apply h _ (range_nonempty a)
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact ⟨_, map_sup a m n⟩
  refine ⟨n, fun m hm => ?_⟩
  rw [hn]
  exact (le_sSup (mem_range_self m)).not_gt

/--
theorem `isSupFiniteCompact_iff_all_elements_compact` / 定理 `isSupFiniteCompact_iff_all_elements_compact`

English:
theorem isSupFiniteCompact_iff_all_elements_compact
  proof: by
  simp_rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
  refine ⟨fun h k s hs => ?_, fun h s => ?_⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    have : sSup s = t.sup id := by
      suffices t.sup id <= sSup s by apply le_antisymm <;> assumption
      simp only [id, Finset.sup_le_iff]
      intro x hx
      exact le_sSup (hts hx)
    exact ⟨t, hts, this⟩

中文:
定理 isSupFiniteCompact_iff_all_elements_compact
  证明: by
  simp_rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
  refine ⟨fun h k s hs => ?_, fun h s => ?_⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    have : sSup s = t.sup id := by
      suffices t.sup id <= sSup s by apply le_antisymm <;> assumption
      simp only [id, Finset.sup_le_iff]
      intro x hx
      exact le_sSup (hts hx)
    exact ⟨t, hts, this⟩

Depends on / 依赖: Finset, Finset.sup_le_iff, isCompactElement_iff_exists_le_sSup_of_le_sSup, le_antisymm, le_sSup, simp_rw, sup_le_iff, t.sup
-/
theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ forall k : α, IsCompactElement k := by
  simp_rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
  refine ⟨fun h k s hs => ?_, fun h s => ?_⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    have : sSup s = t.sup id := by
      suffices t.sup id <= sSup s by apply le_antisymm <;> assumption
      simp only [id, Finset.sup_le_iff]
      intro x hx
      exact le_sSup (hts hx)
    exact ⟨t, hts, this⟩

open List in
/--
theorem `wellFoundedGT_characterisations` / 定理 `wellFoundedGT_characterisations`

English:
theorem wellFoundedGT_characterisations
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 -> 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 -> 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish

中文:
定理 wellFoundedGT_characterisations
  结论: 列表.TFAE
  证明: by
  tfae_have 1 -> 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 -> 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 -> 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish

Depends on / 依赖: IsSupClosedCompact, IsSupClosedCompact.wellFoundedGT, IsSupFiniteCompact, IsSupFiniteCompact.isSupClosedCompact, WellFoundedGT, WellFoundedGT.isSupFiniteCompact, isSupClosedCompact, isSupFiniteCompact, isSupFiniteCompact_iff_all_elements_compact, tfae_finish, tfae_have, wellFoundedGT
-/
theorem wellFoundedGT_characterisations : List.TFAE
    [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact α, forall k : α, IsCompactElement k] := by
  tfae_have 1 -> 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 -> 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 -> 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish

/--
theorem `wellFoundedGT_iff_isSupFiniteCompact` / 定理 `wellFoundedGT_iff_isSupFiniteCompact`

English:
theorem wellFoundedGT_iff_isSupFiniteCompact
  proof: (wellFoundedGT_characterisations α).out 0 1

中文:
定理 wellFoundedGT_iff_isSupFiniteCompact
  证明: (wellFoundedGT_characterisations α).out 0 1

Depends on / 依赖: wellFoundedGT_characterisations
-/
theorem wellFoundedGT_iff_isSupFiniteCompact :
    WellFoundedGT α ↔ IsSupFiniteCompact α :=
  (wellFoundedGT_characterisations α).out 0 1

/--
theorem `isSupFiniteCompact_iff_isSupClosedCompact` / 定理 `isSupFiniteCompact_iff_isSupClosedCompact`

English:
theorem isSupFiniteCompact_iff_isSupClosedCompact
  statement: IsSupFiniteCompact α ↔ IsSupClosedCompact α
  proof: (wellFoundedGT_characterisations α).out 1 2

中文:
定理 isSupFiniteCompact_iff_isSupClosedCompact
  结论: IsSupFiniteCompact α ↔ IsSupClosedCompact α
  证明: (wellFoundedGT_characterisations α).out 1 2

Depends on / 依赖: wellFoundedGT_characterisations
-/
theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFoundedGT_characterisations α).out 1 2

/--
theorem `isSupClosedCompact_iff_wellFoundedGT` / 定理 `isSupClosedCompact_iff_wellFoundedGT`

English:
theorem isSupClosedCompact_iff_wellFoundedGT
  proof: (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

中文:
定理 isSupClosedCompact_iff_wellFoundedGT
  证明: (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

Depends on / 依赖: wellFoundedGT_characterisations
-/
theorem isSupClosedCompact_iff_wellFoundedGT :
    IsSupClosedCompact α ↔ WellFoundedGT α :=
  (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

end CompleteLattice


/--
theorem `WellFoundedGT.finite_of_sSupIndep` / 定理 `WellFoundedGT.finite_of_sSupIndep`

English:
theorem WellFoundedGT.finite_of_sSupIndep
  statement: [WellFoundedGT α] {s : Set α}
  proof: by
  classical
    by_contra! contra
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : exists x : α, x in s ∧ x != ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.sdiff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t union {x} <= s) (by simp : x in _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs]; rw [eq_comm]; rw [inf_eq_left]
    exact le_sSup hx₀

中文:
定理 WellFoundedGT.finite_of_sSupIndep
  结论: [WellFoundedGT α] {s : 集合 α}
  证明: by
  classical
    by_contra! contra
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : exists x : α, x in s ∧ x != ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.sdiff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t union {x} <= s) (by simp : x in _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs]; rw [eq_comm]; rw [inf_eq_left]
    exact le_sSup hx₀

Depends on / 依赖: CompleteLattice, CompleteLattice.WellFoundedGT.isSupFiniteCompact, Finset, Finset.finite_toSet, Infinite, Set.union_singleton, WellFoundedGT, classical, contra, contra.sdiff, finite_toSet, hs.mono, insert, isSupFiniteCompact, nonempty, not_or, replace, this.nonempty, union_singleton
-/
theorem WellFoundedGT.finite_of_sSupIndep [WellFoundedGT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  classical
    by_contra! contra
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : exists x : α, x in s ∧ x != ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.sdiff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t union {x} <= s) (by simp : x in _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs]; rw [eq_comm]; rw [inf_eq_left]
    exact le_sSup hx₀

/--
theorem `WellFoundedGT.finite_ne_bot_of_iSupIndep` / 定理 `WellFoundedGT.finite_ne_bot_of_iSupIndep`

English:
theorem WellFoundedGT.finite_ne_bot_of_iSupIndep
  statement: [WellFoundedGT α]
  proof: by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range

中文:
定理 WellFoundedGT.finite_ne_bot_of_iSupIndep
  结论: [WellFoundedGT α]
  证明: by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range

Depends on / 依赖: Finite, Finite.of_finite_image, Finite.subset, WellFoundedGT, WellFoundedGT.finite_of_sSupIndep, finite_of_sSupIndep, ht.injOn, ht.sSupIndep_range, image_subset_range, of_finite_image, sSupIndep_range, subset
-/
theorem WellFoundedGT.finite_ne_bot_of_iSupIndep [WellFoundedGT α]
    {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.Finite {i | t i != ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range

/--
theorem `WellFoundedGT.finite_of_iSupIndep` / 定理 `WellFoundedGT.finite_of_iSupIndep`

English:
theorem WellFoundedGT.finite_of_iSupIndep
  statement: [WellFoundedGT α] {ι : Type*}
  proof: haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

中文:
定理 WellFoundedGT.finite_of_iSupIndep
  结论: [WellFoundedGT α] {ι : 类型}
  证明: haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

Depends on / 依赖: Finite, Finite.of_injective_finite_range, WellFoundedGT, WellFoundedGT.finite_of_sSupIndep, finite_of_sSupIndep, h_ne_bot, ht.injective, ht.sSupIndep_range, injective, of_injective_finite_range, sSupIndep_range, to_subtype
-/
theorem WellFoundedGT.finite_of_iSupIndep [WellFoundedGT α] {ι : Type*}
    {t : ι -> α} (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : Finite ι :=
  haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

/--
theorem `WellFoundedLT.finite_of_sSupIndep` / 定理 `WellFoundedLT.finite_of_sSupIndep`

English:
theorem WellFoundedLT.finite_of_sSupIndep
  statement: [WellFoundedLT α] {s : Set α}
  proof: by
  by_contra inf
  let e := (Infinite.sdiff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i >= n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) <= a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi => le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi => le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded wellFounded_lt
exact ⟨(e i).2.1, fun h => n.lt_succ_self.not_ge hi.trans_eq e.2 Subtype.val_injective h⟩

中文:
定理 WellFoundedLT.finite_of_sSupIndep
  结论: [WellFoundedLT α] {s : 集合 α}
  证明: by
  by_contra inf
  let e := (Infinite.sdiff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i >= n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) <= a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi => le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi => le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded wellFounded_lt
exact ⟨(e i).2.1, fun h => n.lt_succ_self.not_ge hi.trans_eq e.2 Subtype.val_injective h⟩

Depends on / 依赖: Disjoint, Disjoint.right_lt_sup_of_left_ne_bot, Infinite, Infinite.sdiff, RelEmbedding, RelEmbedding.natGT, finite_singleton, le_rfl, le_sSup, le_succ, mono_right, n.le_succ.trans, natEmbedding, not_wellFounded, right_lt_sup_of_left_ne_bot, sup_le, sup_le_iff, sup_le_iff.mpr, to_subtype, to_subtype.natEmbedding
-/
theorem WellFoundedLT.finite_of_sSupIndep [WellFoundedLT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  by_contra inf
  let e := (Infinite.sdiff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i >= n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) <= a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi => le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi => le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded wellFounded_lt
exact ⟨(e i).2.1, fun h => n.lt_succ_self.not_ge hi.trans_eq e.2 Subtype.val_injective h⟩

/--
theorem `WellFoundedLT.finite_ne_bot_of_iSupIndep` / 定理 `WellFoundedLT.finite_ne_bot_of_iSupIndep`

English:
theorem WellFoundedLT.finite_ne_bot_of_iSupIndep
  statement: [WellFoundedLT α]
  proof: by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range

中文:
定理 WellFoundedLT.finite_ne_bot_of_iSupIndep
  结论: [WellFoundedLT α]
  证明: by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range

Depends on / 依赖: Finite, Finite.of_finite_image, Finite.subset, WellFoundedLT, WellFoundedLT.finite_of_sSupIndep, finite_of_sSupIndep, ht.injOn, ht.sSupIndep_range, image_subset_range, of_finite_image, sSupIndep_range, subset
-/
theorem WellFoundedLT.finite_ne_bot_of_iSupIndep [WellFoundedLT α]
    {ι : Type*} {t : ι -> α} (ht : iSupIndep t) : Set.Finite {i | t i != ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range

/--
theorem `WellFoundedLT.finite_of_iSupIndep` / 定理 `WellFoundedLT.finite_of_iSupIndep`

English:
theorem WellFoundedLT.finite_of_iSupIndep
  statement: [WellFoundedLT α] {ι : Type*}
  proof: haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

中文:
定理 WellFoundedLT.finite_of_iSupIndep
  结论: [WellFoundedLT α] {ι : 类型}
  证明: haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

Depends on / 依赖: Finite, Finite.of_injective_finite_range, WellFoundedLT, WellFoundedLT.finite_of_sSupIndep, finite_of_sSupIndep, h_ne_bot, ht.injective, ht.sSupIndep_range, injective, of_injective_finite_range, sSupIndep_range, to_subtype
-/
theorem WellFoundedLT.finite_of_iSupIndep [WellFoundedLT α] {ι : Type*}
    {t : ι -> α} (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : Finite ι :=
  haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

/--
Definition of `IsCompactlyGenerated` / `IsCompactlyGenerated` 的定义

English:
class IsCompactlyGenerated
  parameters: (α : Type*) [CompleteLattice α]
  axioms and operations (1):
    - exists_sSup_eq : forall x : α, exists s : Set α, (forall x in s, IsCompactElement x) ∧ sSup s = x

中文:
类 是余mpactlyGenerated
  参数: (α : 类型) [完备格 α]
  公理与运算 (1 个):
    - exists_sSup_eq : 对任意 x : α, 存在 s : 集合 α, (对任意 x in s, IsCompactElement x) ∧ sSup s = x
-/
class IsCompactlyGenerated (α : Type*) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
  every element is the `sSup` of some set of compact elements. -/
  exists_sSup_eq : forall x : α, exists s : Set α, (forall x in s, IsCompactElement x) ∧ sSup s = x

section

variable [IsCompactlyGenerated α] {a : α} {s : Set α}

@[simp]
/--
theorem `sSup_compact_le_eq` / 定理 `sSup_compact_le_eq`

English:
theorem sSup_compact_le_eq
  given: (b)
  proof: by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)

@[simp]

中文:
定理 sSup_compact_le_eq
  条件: (b)
  证明: by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)

@[simp]

Depends on / 依赖: IsCompactlyGenerated, IsCompactlyGenerated.exists_sSup_eq, exists_sSup_eq, le_antisymm, le_sSup, sSup_le, sSup_le_sSup
-/
theorem sSup_compact_le_eq (b) :
    sSup { c : α | IsCompactElement c ∧ c <= b } = b := by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)

@[simp]
/--
theorem `sSup_compact_eq_top` / 定理 `sSup_compact_eq_top`

English:
theorem sSup_compact_eq_top
  statement: sSup { a : α | IsCompactElement a } = ⊤
  proof: by
  rw [← sSup_compact_le_eq ⊤]
  simp_rw [le_top, and_true]

中文:
定理 sSup_compact_eq_top
  结论: sSup { a : α | IsCompactElement a } = ⊤
  证明: by
  rw [← sSup_compact_le_eq ⊤]
  simp_rw [le_top, and_true]

Depends on / 依赖: and_true, le_top, sSup_compact_le_eq, simp_rw
-/
theorem sSup_compact_eq_top : sSup { a : α | IsCompactElement a } = ⊤ := by
  rw [← sSup_compact_le_eq ⊤]
  simp_rw [le_top, and_true]

/--
theorem `le_iff_compact_le_imp` / 定理 `le_iff_compact_le_imp`

English:
theorem le_iff_compact_le_imp
  given: {a b : α}
  proof: ⟨fun ab _ _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a]; rw [← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

中文:
定理 le_iff_compact_le_imp
  条件: {a b : α}
  证明: ⟨fun ab _ _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a]; rw [← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

Depends on / 依赖: le_trans, sSup_compact_le_eq, sSup_le_sSup
-/
theorem le_iff_compact_le_imp {a b : α} :
    a <= b ↔ forall c : α, IsCompactElement c -> c <= a -> c <= b :=
  ⟨fun ab _ _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a]; rw [← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

/--
theorem `DirectedOn.inf_sSup_eq` / 定理 `DirectedOn.inf_sSup_eq`

English:
theorem DirectedOn.inf_sSup_eq
  given: (h : DirectedOn (· <= ·) s)
  statement: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  proof: le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.Nonempty
      · intro c hc hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        rw [le_inf_iff] at hcinf
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_biSup _ ds)
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    iSup_inf_le_inf_sSup

中文:
定理 DirectedOn.inf_sSup_eq
  条件: (h : DirectedOn (· <= ·) s)
  结论: a ⊓ sSup s = ⨆ b in s, a ⊓ b
  证明: le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.Nonempty
      · intro c hc hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        rw [le_inf_iff] at hcinf
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_biSup _ ds)
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    iSup_inf_le_inf_sSup

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le, Nonempty, Set.not_nonempty_iff_eq_empty, iSup_inf_le_inf_sSup, isCompactElement_iff_le_of_directed_sSup_le, le_antisymm, le_biSup, le_iff_compact_le_imp, le_inf, le_inf_iff, not_nonempty_iff_eq_empty, s.Nonempty
-/
theorem DirectedOn.inf_sSup_eq (h : DirectedOn (· <= ·) s) : a ⊓ sSup s = ⨆ b in s, a ⊓ b :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.Nonempty
      · intro c hc hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        rw [le_inf_iff] at hcinf
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        exact (le_inf hcinf.1 cd).trans (le_biSup _ ds)
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    iSup_inf_le_inf_sSup

/--
theorem `DirectedOn.sSup_inf_eq` / 定理 `DirectedOn.sSup_inf_eq`

English:
theorem DirectedOn.sSup_inf_eq
  given: (h : DirectedOn (· <= ·) s)
  proof: by
  simp_rw [inf_comm _ a, h.inf_sSup_eq]

中文:
定理 DirectedOn.sSup_inf_eq
  条件: (h : DirectedOn (· <= ·) s)
  证明: by
  simp_rw [inf_comm _ a, h.inf_sSup_eq]
-/
protected theorem DirectedOn.sSup_inf_eq (h : DirectedOn (· <= ·) s) :
    sSup s ⊓ a = ⨆ b in s, b ⊓ a := by
  simp_rw [inf_comm _ a, h.inf_sSup_eq]

/--
theorem `Directed.inf_iSup_eq` / 定理 `Directed.inf_iSup_eq`

English:
theorem Directed.inf_iSup_eq
  given: (h : Directed (· <= ·) f)
  proof: by
  rw [iSup]; rw [h.directedOn_range.inf_sSup_eq]; rw [iSup_range]

中文:
定理 Directed.inf_iSup_eq
  条件: (h : Directed (· <= ·) f)
  证明: by
  rw [iSup]; rw [h.directedOn_range.inf_sSup_eq]; rw [iSup_range]
-/
protected theorem Directed.inf_iSup_eq (h : Directed (· <= ·) f) :
    (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  rw [iSup]; rw [h.directedOn_range.inf_sSup_eq]; rw [iSup_range]

/--
theorem `Directed.iSup_inf_eq` / 定理 `Directed.iSup_inf_eq`

English:
theorem Directed.iSup_inf_eq
  given: (h : Directed (· <= ·) f)
  proof: by
  rw [iSup]; rw [h.directedOn_range.sSup_inf_eq]; rw [iSup_range]

中文:
定理 Directed.iSup_inf_eq
  条件: (h : Directed (· <= ·) f)
  证明: by
  rw [iSup]; rw [h.directedOn_range.sSup_inf_eq]; rw [iSup_range]
-/
protected theorem Directed.iSup_inf_eq (h : Directed (· <= ·) f) :
    (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup]; rw [h.directedOn_range.sSup_inf_eq]; rw [iSup_range]

/--
theorem `DirectedOn.disjoint_sSup_right` / 定理 `DirectedOn.disjoint_sSup_right`

English:
theorem DirectedOn.disjoint_sSup_right
  given: (h : DirectedOn (· <= ·) s)
  proof: by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]

中文:
定理 DirectedOn.disjoint_sSup_right
  条件: (h : DirectedOn (· <= ·) s)
  证明: by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]
-/
protected theorem DirectedOn.disjoint_sSup_right (h : DirectedOn (· <= ·) s) :
    Disjoint a (sSup s) ↔ forall ⦃b⦄, b in s -> Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]

/--
theorem `DirectedOn.disjoint_sSup_left` / 定理 `DirectedOn.disjoint_sSup_left`

English:
theorem DirectedOn.disjoint_sSup_left
  given: (h : DirectedOn (· <= ·) s)
  proof: by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]

中文:
定理 DirectedOn.disjoint_sSup_left
  条件: (h : DirectedOn (· <= ·) s)
  证明: by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]
-/
protected theorem DirectedOn.disjoint_sSup_left (h : DirectedOn (· <= ·) s) :
    Disjoint (sSup s) a ↔ forall ⦃b⦄, b in s -> Disjoint b a := by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]

/--
theorem `Directed.disjoint_iSup_right` / 定理 `Directed.disjoint_iSup_right`

English:
theorem Directed.disjoint_iSup_right
  given: (h : Directed (· <= ·) f)
  proof: by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]

中文:
定理 Directed.disjoint_iSup_right
  条件: (h : Directed (· <= ·) f)
  证明: by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]
-/
protected theorem Directed.disjoint_iSup_right (h : Directed (· <= ·) f) :
    Disjoint a (⨆ i, f i) ↔ forall i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]

/--
theorem `Directed.disjoint_iSup_left` / 定理 `Directed.disjoint_iSup_left`

English:
theorem Directed.disjoint_iSup_left
  given: (h : Directed (· <= ·) f)
  proof: by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]

中文:
定理 Directed.disjoint_iSup_left
  条件: (h : Directed (· <= ·) f)
  证明: by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]
-/
protected theorem Directed.disjoint_iSup_left (h : Directed (· <= ·) f) :
    Disjoint (⨆ i, f i) a ↔ forall i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]

/--
theorem `inf_sSup_eq_iSup_inf_sup_finset` / 定理 `inf_sSup_eq_iSup_inf_sup_finset`

English:
theorem inf_sSup_eq_iSup_inf_sup_finset
  proof: le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine (le_inf hcinf.1 ht2).trans ?_
      exact le_iSup₂ (f := fun (t' : Finset α) (ht' : ↑t' subseteq s) => a ⊓ t'.sup id) t ht1)
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))

中文:
定理 inf_sSup_eq_iSup_inf_sup_finset
  证明: le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine (le_inf hcinf.1 ht2).trans ?_
      exact le_iSup₂ (f := fun (t' : Finset α) (ht' : ↑t' subseteq s) => a ⊓ t'.sup id) t ht1)
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup, Finset, Finset.sup_id_eq_sSup, iSup_le, inf_le_inf_left, isCompactElement_iff_exists_le_sSup_of_le_sSup, le_antisymm, le_iff_compact_le_imp, le_inf, le_inf_iff, sSup_le_sSup, subseteq, sup_id_eq_sSup
-/
theorem inf_sSup_eq_iSup_inf_sup_finset :
    a ⊓ sSup s = ⨆ (t : Finset α) (_ : ↑t subseteq s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine (le_inf hcinf.1 ht2).trans ?_
      exact le_iSup₂ (f := fun (t' : Finset α) (ht' : ↑t' subseteq s) => a ⊓ t'.sup id) t ht1)
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))

/--
theorem `sSupIndep_iff_finite` / 定理 `sSupIndep_iff_finite`

English:
theorem sSupIndep_iff_finite
  given: {s : Set α}
  proof: ⟨fun hs _ ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff]; rw [inf_sSup_eq_iSup_inf_sup_finset]; rw [iSup_eq_bot]
    intro t
    rw [iSup_eq_bot]; rw [Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_sdiff_self_of_notMem] at h'
        exact fun con => ((Set.mem_sdiff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht sdiff_subset⟩⟩

中文:
定理 sSupIndep_iff_finite
  条件: {s : 集合 α}
  证明: ⟨fun hs _ ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff]; rw [inf_sSup_eq_iSup_inf_sup_finset]; rw [iSup_eq_bot]
    intro t
    rw [iSup_eq_bot]; rw [Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_sdiff_self_of_notMem] at h'
        exact fun con => ((Set.mem_sdiff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht sdiff_subset⟩⟩

Depends on / 依赖: Finset, Finset.coe_insert, Finset.sup_id_eq_sSup, Set.Subset.trans, Set.insert_sdiff_self_of_notMem, Set.insert_subset_iff, Set.mem_sdiff, Set.mem_singleton, Subset, classical, coe_insert, disjoint_iff, eq_bot, hs.mono, iSup_eq_bot, inf_sSup_eq_iSup_inf_sup_finset, insert, insert_sdiff_self_of_notMem, insert_subset_iff, mem_insert_self
-/
theorem sSupIndep_iff_finite {s : Set α} :
    sSupIndep s ↔
      forall t : Finset α, ↑t subseteq s -> sSupIndep (↑t : Set α) :=
  ⟨fun hs _ ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff]; rw [inf_sSup_eq_iSup_inf_sup_finset]; rw [iSup_eq_bot]
    intro t
    rw [iSup_eq_bot]; rw [Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_sdiff_self_of_notMem] at h'
        exact fun con => ((Set.mem_sdiff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht sdiff_subset⟩⟩

/--
lemma `iSupIndep_iff_supIndep` / 引理 `iSupIndep_iff_supIndep`

English:
lemma iSupIndep_iff_supIndep
  given: {ι : Type*} {f : ι -> α}
  proof: by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  classical
  have hf : Set.InjOn f {i : ι | f i != ⊥} := by
    by_contra! hf
    simp_all only [Set.InjOn, ne_eq, Set.mem_ofPred_eq, not_forall]
    obtain ⟨x₁, hx₁, x₂, hx₂, hfeq, hneq⟩ := hf
    specialize h ({x₁, x₂} : Finset ι)
    rw [Finset.supIndep_pair hneq]; rw [disjoint_iff]; rw [hfeq]; rw [inf_idem (f x₂)] at h
    contradiction
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

@[deprecated iSupIndep_iff_supIndep (since := "2026-02-18")]

中文:
引理 iSupIndep_iff_supIndep
  条件: {ι : 类型} {f : ι -> α}
  证明: by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  classical
  have hf : Set.InjOn f {i : ι | f i != ⊥} := by
    by_contra! hf
    simp_all only [Set.InjOn, ne_eq, Set.mem_ofPred_eq, not_forall]
    obtain ⟨x₁, hx₁, x₂, hx₂, hfeq, hneq⟩ := hf
    specialize h ({x₁, x₂} : Finset ι)
    rw [Finset.supIndep_pair hneq]; rw [disjoint_iff]; rw [hfeq]; rw [inf_idem (f x₂)] at h
    contradiction
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

@[deprecated iSupIndep_iff_supIndep (since := "2026-02-18")]

Depends on / 依赖: Finset, Finset.s, Finset.supIndep_pair, Set.InjOn, Set.mem_ofPred_eq, classical, disjoint_iff, h.supIndep, iSupIndep_def, iSup_eq_bot, inf_idem, inf_sSup_eq_iSup_inf_sup_finset, mem_ofPred_eq, ne_eq, not_forall, simp_rw, specialize, supIndep, supIndep_pair
-/
lemma iSupIndep_iff_supIndep {ι : Type*} {f : ι -> α} :
    iSupIndep f ↔ forall (s : Finset ι), s.SupIndep f := by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  classical
  have hf : Set.InjOn f {i : ι | f i != ⊥} := by
    by_contra! hf
    simp_all only [Set.InjOn, ne_eq, Set.mem_ofPred_eq, not_forall]
    obtain ⟨x₁, hx₁, x₂, hx₂, hfeq, hneq⟩ := hf
    specialize h ({x₁, x₂} : Finset ι)
    rw [Finset.supIndep_pair hneq]; rw [disjoint_iff]; rw [hfeq]; rw [inf_idem (f x₂)] at h
    contradiction
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

@[deprecated iSupIndep_iff_supIndep (since := "2026-02-18")]
/--
lemma `iSupIndep_iff_supIndep_of_injOn` / 引理 `iSupIndep_iff_supIndep_of_injOn`

English:
lemma iSupIndep_iff_supIndep_of_injOn
  statement: {ι : Type*} {f : ι -> α}
  proof: by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  classical
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

中文:
引理 iSupIndep_iff_supIndep_of_injOn
  结论: {ι : 类型} {f : ι -> α}
  证明: by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  classical
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

Depends on / 依赖: Finset, Finset.erase, Finset.erase_insert_eq_erase, Finset.mem_erase, Finset.mem_preimage, Finset.sup_erase_bot, classical, disjoint_iff, erase_insert_eq_erase, h.supIndep, iSupIndep_def, iSup_eq_bot, inf_sSup_eq_iSup_inf_sup_finset, insert, mem_erase, mem_preimage, ne_eq, preimage, replace, s.erase
-/
lemma iSupIndep_iff_supIndep_of_injOn {ι : Type*} {f : ι -> α}
    (hf : InjOn f {i | f i != ⊥}) :
    iSupIndep f ↔ forall (s : Finset ι), s.SupIndep f := by
  refine ⟨fun h => h.supIndep', fun h => iSupIndep_def'.mpr fun i => ?_⟩
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  classical
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij => by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this]; rw [Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

/--
theorem `sSupIndep_iUnion_of_directed` / 定理 `sSupIndep_iUnion_of_directed`

English:
theorem sSupIndep_iUnion_of_directed
  statement: {η : Type*} {s : η -> Set α}
  proof: by
  by_cases hη : Nonempty η
  · rw [sSupIndep_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_toSet ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    exact (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩

中文:
定理 sSupIndep_iUnion_of_directed
  结论: {η : 类型} {s : η -> 集合 α}
  证明: by
  by_cases hη : Nonempty η
  · rw [sSupIndep_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_toSet ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    exact (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩

Depends on / 依赖: Nonempty, Set.Subset.trans, Set.finite_subset_iUnion, Set.iUnion, Subset, fi.mem_toFinset, fi.toFinset, finite_subset_iUnion, finite_toSet, finset_le, hs.finset_le, mem_toFinset, sSupIndep_iff_finite, t.finite_toSet, toFinset
-/
theorem sSupIndep_iUnion_of_directed {η : Type*} {s : η -> Set α}
    (hs : Directed (· subseteq ·) s) (h : forall i, sSupIndep (s i)) :
    sSupIndep (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · rw [sSupIndep_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_toSet ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    exact (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩

/--
theorem `iSupIndep_sUnion_of_directed` / 定理 `iSupIndep_sUnion_of_directed`

English:
theorem iSupIndep_sUnion_of_directed
  statement: {s : Set (Set α)} (hs : DirectedOn (· subseteq ·) s)
  proof: by
  rw [Set.sUnion_eq_iUnion]
  exact sSupIndep_iUnion_of_directed hs.directed_val (by simpa using h)

中文:
定理 iSupIndep_sUnion_of_directed
  结论: {s : 集合 (集合 α)} (hs : DirectedOn (· subseteq ·) s)
  证明: by
  rw [Set.sUnion_eq_iUnion]
  exact sSupIndep_iUnion_of_directed hs.directed_val (by simpa using h)

Depends on / 依赖: Set.sUnion_eq_iUnion, directed_val, hs.directed_val, sSupIndep_iUnion_of_directed, sUnion_eq_iUnion
-/
theorem iSupIndep_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· subseteq ·) s)
    (h : forall a in s, sSupIndep a) : sSupIndep (⋃₀ s) := by
  rw [Set.sUnion_eq_iUnion]
  exact sSupIndep_iUnion_of_directed hs.directed_val (by simpa using h)

/--
lemma `disjoint_biSup_of_finite_disjoint_biSup` / 引理 `disjoint_biSup_of_finite_disjoint_biSup`

English:
lemma disjoint_biSup_of_finite_disjoint_biSup
  statement: {ι : Type*} {f : ι -> α} {s : Set ι} {a : α}
  proof: by
  simp_rw [disjoint_iff, iSup_subtype', ← sSup_range, inf_comm, inf_sSup_eq_iSup_inf_sup_finset,
    iSup_eq_bot]
  intro u hu
  obtain ⟨t, ht, ht', htu⟩ : existsᵉ (t subseteq s) (hu : t.Finite), f '' t = u :=
Set.Finite.exists_subset_finite_image_eq u.finite_toSet by rwa [Set.image_eq_range f s]
  replace htu : u.sup id = ⨆ i in t, f i := by
    simp only [Finset.sup_eq_iSup, id_eq, ← Finset.mem_coe, ← htu, iSup_image]
  rw [inf_comm]; rw [← disjoint_iff]; rw [htu]
  exact hs t ht ht'

中文:
引理 disjoint_biSup_of_finite_disjoint_biSup
  结论: {ι : 类型} {f : ι -> α} {s : 集合 ι} {a : α}
  证明: by
  simp_rw [disjoint_iff, iSup_subtype', ← sSup_range, inf_comm, inf_sSup_eq_iSup_inf_sup_finset,
    iSup_eq_bot]
  intro u hu
  obtain ⟨t, ht, ht', htu⟩ : existsᵉ (t subseteq s) (hu : t.Finite), f '' t = u :=
Set.Finite.exists_subset_finite_image_eq u.finite_toSet by rwa [Set.image_eq_range f s]
  replace htu : u.sup id = ⨆ i in t, f i := by
    simp only [Finset.sup_eq_iSup, id_eq, ← Finset.mem_coe, ← htu, iSup_image]
  rw [inf_comm]; rw [← disjoint_iff]; rw [htu]
  exact hs t ht ht'

Depends on / 依赖: Finite, Finset, Finset.mem_coe, Finset.sup_eq_iSup, Set.Finite.exists_subset_finite_image_eq, Set.image_eq_range, disjoint_iff, exists_subset_finite_image_eq, finite_toSet, iSup_eq_bot, iSup_image, iSup_subtype, id_eq, image_eq_range, inf_comm, inf_sSup_eq_iSup_inf_sup_finset, mem_coe, replace, sSup_range, simp_rw
-/
lemma disjoint_biSup_of_finite_disjoint_biSup {ι : Type*} {f : ι -> α} {s : Set ι} {a : α}
    (hs : forall t subseteq s, t.Finite -> Disjoint (⨆ i in t, f i) a) :
    Disjoint (⨆ i in s, f i) a := by
  simp_rw [disjoint_iff, iSup_subtype', ← sSup_range, inf_comm, inf_sSup_eq_iSup_inf_sup_finset,
    iSup_eq_bot]
  intro u hu
  obtain ⟨t, ht, ht', htu⟩ : existsᵉ (t subseteq s) (hu : t.Finite), f '' t = u :=
Set.Finite.exists_subset_finite_image_eq u.finite_toSet by rwa [Set.image_eq_range f s]
  replace htu : u.sup id = ⨆ i in t, f i := by
    simp only [Finset.sup_eq_iSup, id_eq, ← Finset.mem_coe, ← htu, iSup_image]
  rw [inf_comm]; rw [← disjoint_iff]; rw [htu]
  exact hs t ht ht'

/--
lemma `iSupIndep.disjoint_biSup_biSup` / 引理 `iSupIndep.disjoint_biSup_biSup`

English:
lemma iSupIndep.disjoint_biSup_biSup
  statement: {ι : Type*} [IsModularLattice α]
  proof: disjoint_biSup_of_finite_disjoint_biSup fun _ h₁ h₂ =>
    disjoint_biSup_biSup' hf (Set.disjoint_of_subset_left h₁ hst) h₂

中文:
引理 iSupIndep.disjoint_biSup_biSup
  结论: {ι : 类型} [是Modular格 α]
  证明: disjoint_biSup_of_finite_disjoint_biSup fun _ h₁ h₂ =>
    disjoint_biSup_biSup' hf (Set.disjoint_of_subset_left h₁ hst) h₂

Depends on / 依赖: Set.disjoint_of_subset_left, disjoint_biSup_biSup, disjoint_biSup_of_finite_disjoint_biSup, disjoint_of_subset_left
-/
lemma iSupIndep.disjoint_biSup_biSup {ι : Type*} [IsModularLattice α]
    {f : ι -> α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t) :
    Disjoint (⨆ i in s, f i) (⨆ i in t, f i) :=
  disjoint_biSup_of_finite_disjoint_biSup fun _ h₁ h₂ =>
    disjoint_biSup_biSup' hf (Set.disjoint_of_subset_left h₁ hst) h₂

end

namespace CompleteLattice

/--
theorem `isCompactlyGenerated_of_wellFoundedGT` / 定理 `isCompactlyGenerated_of_wellFoundedGT`

English:
theorem isCompactlyGenerated_of_wellFoundedGT
  given: [h : WellFoundedGT α]
  proof: by
  rw [wellFoundedGT_iff_isSupFiniteCompact]; rw [isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩

中文:
定理 isCompactlyGenerated_of_wellFoundedGT
  条件: [h : WellFoundedGT α]
  证明: by
  rw [wellFoundedGT_iff_isSupFiniteCompact]; rw [isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩

Depends on / 依赖: isSupFiniteCompact_iff_all_elements_compact, wellFoundedGT_iff_isSupFiniteCompact
-/
theorem isCompactlyGenerated_of_wellFoundedGT [h : WellFoundedGT α] :
    IsCompactlyGenerated α := by
  rw [wellFoundedGT_iff_isSupFiniteCompact]; rw [isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩

/--
theorem `Iic_coatomic_of_compact_element` / 定理 `Iic_coatomic_of_compact_element`

English:
theorem Iic_coatomic_of_compact_element
  given: {k : α} (h : IsCompactElement k)
  proof: by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top]
  right
  have ⟨a, ba, h⟩ := zorn_le_nonempty₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  · refine ⟨⟨a, le_of_lt h.prop⟩, ⟨ne_of_lt h.prop, fun c hck => by_contradiction fun c₀ => ?_⟩, ba⟩
    cases h.eq_of_le (y := c.1) (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine ⟨sSup S, IsCompactElement.directed_sSup_lt_of_lt h hS cC.directedOn SC, ?_⟩
      intro; apply le_sSup
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩

中文:
定理 Iic_coatomic_of_compact_element
  条件: {k : α} (h : IsCompactElement k)
  证明: by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top]
  right
  have ⟨a, ba, h⟩ := zorn_le_nonempty₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  · refine ⟨⟨a, le_of_lt h.prop⟩, ⟨ne_of_lt h.prop, fun c hck => by_contradiction fun c₀ => ?_⟩, ba⟩
    cases h.eq_of_le (y := c.1) (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine ⟨sSup S, IsCompactElement.directed_sSup_lt_of_lt h hS cC.directedOn SC, ?_⟩
      intro; apply le_sSup
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩

Depends on / 依赖: IsCompactElement, IsCompactElement.directed_sSup_lt_of_lt, Nonempty, S.Nonempty, Set.Iic.coe_top, Set.Iio, Subtype, Subtype.ext, by_contradiction, coe_top, directed_sSup_lt_of_lt, eq_of_le, eq_or_ne, h.eq_of_le, h.prop, hck.le, le_of_lt, lt_irrefl, lt_of_le_of_ne, ne_of_lt
-/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) :
    IsCoatomic (Set.Iic k) := by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top]
  right
  have ⟨a, ba, h⟩ := zorn_le_nonempty₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  · refine ⟨⟨a, le_of_lt h.prop⟩, ⟨ne_of_lt h.prop, fun c hck => by_contradiction fun c₀ => ?_⟩, ba⟩
    cases h.eq_of_le (y := c.1) (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine ⟨sSup S, IsCompactElement.directed_sSup_lt_of_lt h hS cC.directedOn SC, ?_⟩
      intro; apply le_sSup
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩

/--
theorem `coatomic_of_top_compact` / 定理 `coatomic_of_top_compact`

English:
theorem coatomic_of_top_compact
  given: (h : IsCompactElement (⊤ : α))
  statement: IsCoatomic α
  proof: (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)

中文:
定理 coatomic_of_top_compact
  条件: (h : IsCompactElement (⊤ : α))
  结论: 是余原子的 α
  证明: (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)

Depends on / 依赖: IicTop, Iic_coatomic_of_compact_element, OrderIso, OrderIso.IicTop, isCoatomic_iff, isCoatomic_iff.mp
-/
theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

/--
theorem `iSupIndep.iInf` / 定理 `iSupIndep.iInf`

English:
theorem iSupIndep.iInf
  statement: {ι : Type*} {κ : ι -> Type*} (f : (i : ι) -> κ i -> α)
  proof: by
  rw [iSupIndep_iff_supIndep]
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : 1 < s.card; swap
    · by_cases hcard0 : s.card = 0 <;> grind [Finset.card_eq_zero, Finset.card_eq_one]
    · obtain ⟨k₁, k₂, _, _, h⟩ := Finset.one_lt_card_iff.mp hs
      obtain ⟨i, hi⟩ : exists i : ι, k₁ i != k₂ i := Function.ne_iff.mp h
      classical
      rw [← Finset.image_biUnion_filter_eq s (· i)]
      refine Finset.SupIndep.biUnion ?_ (by grind)
      apply ((h_indep i).supIndep' _).mono
      simp_rw [Finset.sup_le_iff, Finset.mem_filter, and_imp]
      rintro _ _ _ _ rfl
      exact iInf_le _ _

中文:
定理 iSupIndep.iInf
  结论: {ι : 类型} {κ : ι -> 类型} (f : (i : ι) -> κ i -> α)
  证明: by
  rw [iSupIndep_iff_supIndep]
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : 1 < s.card; swap
    · by_cases hcard0 : s.card = 0 <;> grind [Finset.card_eq_zero, Finset.card_eq_one]
    · obtain ⟨k₁, k₂, _, _, h⟩ := Finset.one_lt_card_iff.mp hs
      obtain ⟨i, hi⟩ : exists i : ι, k₁ i != k₂ i := Function.ne_iff.mp h
      classical
      rw [← Finset.image_biUnion_filter_eq s (· i)]
      refine Finset.SupIndep.biUnion ?_ (by grind)
      apply ((h_indep i).supIndep' _).mono
      simp_rw [Finset.sup_le_iff, Finset.mem_filter, and_imp]
      rintro _ _ _ _ rfl
      exact iInf_le _ _

Depends on / 依赖: Finset, Finset.SupIndep.biUnion, Finset.card_eq_one, Finset.card_eq_zero, Finset.image_biUnion_filter_eq, Finset.one_lt_card_iff.mp, Finset.strongInduction, Finset.sup_le_i, Function, Function.ne_iff.mp, SupIndep, biUnion, card_eq_one, card_eq_zero, classical, h_indep, hcard0, iSupIndep_iff_supIndep, image_biUnion_filter_eq, ne_iff
-/
theorem iSupIndep.iInf {ι : Type*} {κ : ι -> Type*} (f : (i : ι) -> κ i -> α)
    (h_indep : forall i : ι, iSupIndep (f i)) : iSupIndep (fun k : (i : ι) -> κ i => ⨅ i, f i (k i)) := by
  rw [iSupIndep_iff_supIndep]
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : 1 < s.card; swap
    · by_cases hcard0 : s.card = 0 <;> grind [Finset.card_eq_zero, Finset.card_eq_one]
    · obtain ⟨k₁, k₂, _, _, h⟩ := Finset.one_lt_card_iff.mp hs
      obtain ⟨i, hi⟩ : exists i : ι, k₁ i != k₂ i := Function.ne_iff.mp h
      classical
      rw [← Finset.image_biUnion_filter_eq s (· i)]
      refine Finset.SupIndep.biUnion ?_ (by grind)
      apply ((h_indep i).supIndep' _).mono
      simp_rw [Finset.sup_le_iff, Finset.mem_filter, and_imp]
      rintro _ _ _ _ rfl
      exact iInf_le _ _

instance (priority := 100) isAtomic_of_complementedLattice [ComplementedLattice α] : IsAtomic α :=
  ⟨fun b => by
    by_cases h : { c : α | IsCompactElement c ∧ c <= b } subseteq {⊥}
    · left
      rw [← sSup_compact_le_eq b]; rw [sSup_eq_bot]
      exact h
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      right
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      rw [← isAtomic_iff_isCoatomic] at hc'
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : Set.Iic c)
      · exfalso
        apply hcbot
        simp only [Subtype.ext_iff, Set.Iic.coe_bot] at con
        exact con
      rw [← Subtype.coe_le_coe]; rw [Subtype.coe_mk] at hac
      exact ⟨a, ha.of_isAtom_coe_Iic, hac.trans hcb⟩⟩

/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b =>
    ⟨{ a | IsAtom a ∧ a <= b }, by
      symm
      have hle : sSup { a : α | IsAtom a ∧ a <= b } <= b := sSup_le fun _ => And.right
      apply (lt_or_eq_of_le hle).resolve_left _
      intro con
      obtain ⟨c, hc⟩ := exists_isCompl (⟨sSup { a : α | IsAtom a ∧ a <= b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_lt con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
      · apply ha.1
        rw [eq_bot_iff]
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        rw [← Subtype.coe_le_coe]; rw [Subtype.coe_mk]
        exact le_sSup ⟨ha.of_isAtom_coe_Iic, a.2⟩, fun _ => And.left⟩

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of independent atoms.
-/

/--
theorem `exists_sSupIndep_disjoint_sSup_atoms` / 定理 `exists_sSupIndep_disjoint_sSup_atoms`

English:
theorem exists_sSupIndep_disjoint_sSup_atoms
  statement: (b c : α) (hbc : b <= c)
  proof: by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ forall a in s, IsAtom a ∧ a <= c})
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨iSupIndep_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
  simp_rw [maximal_subset_iff] at zorn
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := zorn
  refine ⟨s, s_ind, b_inf_Sup_s, le_antisymm ?_ ?_, fun a ha => (s_atoms a ha).1⟩
  · simp_all
  rw [← h]; rw [sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine (ha.2.le_iff.mp inf_le_left).resolve_left fun con => ha.2.1 ?_
  rw [← con]; rw [eq_comm]; rw [inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_]; rw [?_]; rw [fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_sdiff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.sdiff_subset).trans le_sup_right)
    · have h : (s union {a}) \ {x} = s \ {x} union {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_sdiff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h]; rw [sSup_union]; rw [sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha.symm

中文:
定理 存在_sSupIndep_disjoint_sSup_atoms
  结论: (b c : α) (hbc : b <= c)
  证明: by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ forall a in s, IsAtom a ∧ a <= c})
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨iSupIndep_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
  simp_rw [maximal_subset_iff] at zorn
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := zorn
  refine ⟨s, s_ind, b_inf_Sup_s, le_antisymm ?_ ?_, fun a ha => (s_atoms a ha).1⟩
  · simp_all
  rw [← h]; rw [sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine (ha.2.le_iff.mp inf_le_left).resolve_left fun con => ha.2.1 ?_
  rw [← con]; rw [eq_comm]; rw [inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_]; rw [?_]; rw [fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_sdiff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.sdiff_subset).trans le_sup_right)
    · have h : (s union {a}) \ {x} = s \ {x} union {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_sdiff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h]; rw [sSup_union]; rw [sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha.symm
-/
theorem exists_sSupIndep_disjoint_sSup_atoms (b c : α) (hbc : b <= c)
    (h : sSup {a <= c | IsAtom a} = c) :
    exists s : Set α, sSupIndep s ∧ Disjoint b (sSup s) ∧ b ⊔ sSup s = c ∧ forall ⦃a⦄, a in s -> IsAtom a := by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ forall a in s, IsAtom a ∧ a <= c})
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨iSupIndep_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
  simp_rw [maximal_subset_iff] at zorn
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := zorn
  refine ⟨s, s_ind, b_inf_Sup_s, le_antisymm ?_ ?_, fun a ha => (s_atoms a ha).1⟩
  · simp_all
  rw [← h]; rw [sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine (ha.2.le_iff.mp inf_le_left).resolve_left fun con => ha.2.1 ?_
  rw [← con]; rw [eq_comm]; rw [inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_]; rw [?_]; rw [fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_sdiff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.sdiff_subset).trans le_sup_right)
    · have h : (s union {a}) \ {x} = s \ {x} union {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_sdiff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h]; rw [sSup_union]; rw [sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert]; rw [Set.insert_sdiff_singleton]; rw [Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha.symm

/--
theorem `exists_sSupIndep_isCompl_sSup_atoms` / 定理 `exists_sSupIndep_isCompl_sSup_atoms`

English:
theorem exists_sSupIndep_isCompl_sSup_atoms
  given: (h : sSup { a : α | IsAtom a } = ⊤) (b : α)
  proof: by
  simpa [isCompl_iff, codisjoint_iff, and_assoc]
using exists_sSupIndep_disjoint_sSup_atoms b ⊤ le_top by simpa using h

中文:
定理 存在_sSupIndep_isCompl_sSup_atoms
  条件: (h : sSup { a : α | IsAtom a } = ⊤) (b : α)
  证明: by
  simpa [isCompl_iff, codisjoint_iff, and_assoc]
using exists_sSupIndep_disjoint_sSup_atoms b ⊤ le_top by simpa using h

Depends on / 依赖: and_assoc, codisjoint_iff, exists_sSupIndep_disjoint_sSup_atoms, isCompl_iff, le_top
-/
theorem exists_sSupIndep_isCompl_sSup_atoms (h : sSup { a : α | IsAtom a } = ⊤) (b : α) :
    exists s : Set α, sSupIndep s ∧ IsCompl b (sSup s) ∧ forall ⦃a⦄, a in s -> IsAtom a := by
  simpa [isCompl_iff, codisjoint_iff, and_assoc]
using exists_sSupIndep_disjoint_sSup_atoms b ⊤ le_top by simpa using h

/--
theorem `exists_sSupIndep_of_sSup_atoms` / 定理 `exists_sSupIndep_of_sSup_atoms`

English:
theorem exists_sSupIndep_of_sSup_atoms
  given: (b : α) (h : sSup {a <= b | IsAtom a} = b)
  proof: let ⟨s, s_ind, _, s_atoms⟩ := exists_sSupIndep_disjoint_sSup_atoms ⊥ b bot_le h
  ⟨s, s_ind, by simpa using s_atoms⟩

中文:
定理 存在_sSupIndep_of_sSup_atoms
  条件: (b : α) (h : sSup {a <= b | IsAtom a} = b)
  证明: let ⟨s, s_ind, _, s_atoms⟩ := exists_sSupIndep_disjoint_sSup_atoms ⊥ b bot_le h
  ⟨s, s_ind, by simpa using s_atoms⟩

Depends on / 依赖: bot_le, exists_sSupIndep_disjoint_sSup_atoms, s_atoms, s_ind
-/
theorem exists_sSupIndep_of_sSup_atoms (b : α) (h : sSup {a <= b | IsAtom a} = b) :
    exists s : Set α, sSupIndep s ∧ sSup s = b ∧ forall ⦃a⦄, a in s -> IsAtom a :=
  let ⟨s, s_ind, _, s_atoms⟩ := exists_sSupIndep_disjoint_sSup_atoms ⊥ b bot_le h
  ⟨s, s_ind, by simpa using s_atoms⟩

/--
theorem `exists_sSupIndep_of_sSup_atoms_eq_top` / 定理 `exists_sSupIndep_of_sSup_atoms_eq_top`

English:
theorem exists_sSupIndep_of_sSup_atoms_eq_top
  given: (h : sSup {a : α | IsAtom a} = ⊤)
  proof: exists_sSupIndep_of_sSup_atoms ⊤ (by simpa)

中文:
定理 存在_sSupIndep_of_sSup_atoms_eq_top
  条件: (h : sSup {a : α | IsAtom a} = ⊤)
  证明: exists_sSupIndep_of_sSup_atoms ⊤ (by simpa)

Depends on / 依赖: exists_sSupIndep_of_sSup_atoms
-/
theorem exists_sSupIndep_of_sSup_atoms_eq_top (h : sSup {a : α | IsAtom a} = ⊤) :
    exists s : Set α, sSupIndep s ∧ sSup s = ⊤ ∧ forall ⦃a⦄, a in s -> IsAtom a :=
  exists_sSupIndep_of_sSup_atoms ⊤ (by simpa)

/--
theorem `complementedLattice_of_sSup_atoms_eq_top` / 定理 `complementedLattice_of_sSup_atoms_eq_top`

English:
theorem complementedLattice_of_sSup_atoms_eq_top
  given: (h : sSup { a : α | IsAtom a } = ⊤)
  proof: let ⟨s, _, hcompl, _⟩ := exists_sSupIndep_isCompl_sSup_atoms (by simpa) b
    ⟨sSup s, hcompl⟩

中文:
定理 complementedLattice_of_sSup_atoms_eq_top
  条件: (h : sSup { a : α | IsAtom a } = ⊤)
  证明: let ⟨s, _, hcompl, _⟩ := exists_sSupIndep_isCompl_sSup_atoms (by simpa) b
    ⟨sSup s, hcompl⟩

Depends on / 依赖: exists_sSupIndep_isCompl_sSup_atoms, hcompl
-/
theorem complementedLattice_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α where
  exists_isCompl b :=
    let ⟨s, _, hcompl, _⟩ := exists_sSupIndep_isCompl_sSup_atoms (by simpa) b
    ⟨sSup s, hcompl⟩

/--
theorem `complementedLattice_of_isAtomistic` / 定理 `complementedLattice_of_isAtomistic`

English:
theorem complementedLattice_of_isAtomistic
  given: [IsAtomistic α]
  statement: ComplementedLattice α
  proof: complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top

中文:
定理 complementedLattice_of_isAtomistic
  条件: [是Atomistic α]
  结论: 有补格 α
  证明: complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top

Depends on / 依赖: complementedLattice_of_sSup_atoms_eq_top, sSup_atoms_eq_top
-/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top

/--
theorem `complementedLattice_iff_isAtomistic` / 定理 `complementedLattice_iff_isAtomistic`

English:
theorem complementedLattice_iff_isAtomistic
  statement: ComplementedLattice α ↔ IsAtomistic α
  proof: by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic

中文:
定理 complementedLattice_iff_isAtomistic
  结论: 有补格 α ↔ 是Atomistic α
  证明: by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic

Depends on / 依赖: complementedLattice_of_isAtomistic, intros, isAtomistic_of_complementedLattice
-/
theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α := by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic

end
