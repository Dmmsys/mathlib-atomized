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
/-- An element `k` is compact if any directed set with `LUB` (least upper bound) above
`k` has already got above `k` at some point in the set.
Such an element is also called "finite" or "S-compact". -/
/-
**IsCompactElement** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCompactElement {α : Type*} [PartialOrder α] (k : α)
参数：k : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `k` is compact if any directed set with `LUB` (least upper bound) abo
ve
`k` has already got above `k` at some point in the set.
Such an element is also called "finite" or "S-compact".
-/
def IsCompactElement {α : Type*} [PartialOrder α] (k : α) :=
  ∀ (s : Set α) (u : α),
    s.Nonempty →
    DirectedOn (· ≤ ·) s →
    IsLUB s u →
    k ≤ u →
    ∃ x ∈ s, k ≤ x

variable {ι : Sort*} {α : Type*} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `sSup`. -/
/-
**CompleteLattice.IsSupClosedCompact** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLattice`
。
形式化陈述：IsSupClosedCompact : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compactness property for a complete lattice is that any `sup`-closed non-empty
 subset
contains its `sSup`.
-/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), SupClosed s → sSup s ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `sSup`. -/
/-
**CompleteLattice.IsSupFiniteCompact** 是 Mathlib 中的一个定义，位于命名空间 `CompleteLattice`
。
形式化陈述：IsSupFiniteCompact : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compactness property for a complete lattice is that any subset has a finite su
bset with the
same `sSup`.
-/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id

/-- An element `k` is compact if and only if any directed set with `sSup` above
`k` already got above `k` at some point in the set. -/
/-
**CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le** 是 Mathlib 中的一个定理
，位于命名空间 `CompleteLattice`。
形式化陈述：isCompactElement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔
 forall s : Set α, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSup s -> exists 
x : α, x in s ∧ k <= x
参数：k : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.isLUB_sSup`：∀ {α : Type u_8} [self : CompleteLattice α] 
(s : Set α), IsLUB s (sSup s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isLUB_iff_sSup_eq`：isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a

--- 原说明 ---
An element `k` is compact if and only if any directed set with `sSup` above
`k` already got above `k` at some point in the set.
-/
theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sSup s → ∃ x : α, x ∈ s ∧ k ≤ x := by
  constructor
  · intro hk s hs hs' h_le
    exact hk s (sSup s) hs hs' (isLUB_sSup s) h_le
  · intro h s u hs hs' hu h_le
    rw [isLUB_iff_sSup_eq] at hu
    rw [← hu] at h_le
    exact h s hs hs' h_le

/-- An element `k` of is compact if any set with `sSup`
above `k` has a finite subset with `sSup` above `k`. -/
/-
**CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup** 是 Mathlib 中的一
个定理，位于命名空间 `CompleteLattice`。
形式化陈述：isCompactElement_iff_exists_le_sSup_of_le_sSup (k : α) : IsCompactElement 
k ↔ forall s : Set α, k <= sSup s -> exists t : Finset α, ↑t subseteq s ∧ k <= t
.sup id
参数：k : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.sup_le_of_le_directed`：sup_le_of_le_directed {α : Type*} [Semilat
ticeSup α] [OrderBot α] (s : Set α) (hs : s.Nonempty) (hdir : DirectedOn (· <= ·
) s) (t : Finset α…

--- 原说明 ---
An element `k` of is compact if any set with `sSup`
above `k` has a finite subset with `sSup` above `k`.
-/
theorem isCompactElement_iff_exists_le_sSup_of_le_sSup (k : α) :
    IsCompactElement k ↔ ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    constructor
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· ≤ ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c ∪ d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s ≤ sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ ∈ S from Set.nonempty_of_mem this
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
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩
/-
**CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup.** 是 Mathlib 中的
一个定理，位于命名空间 `CompleteLattice`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCompactElement_iff_exists_le_iSup_of_le_iSup.{u} {α : Type u} [CompleteLattice α]
    (k : α) : IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ iSup s → ∃ t : Finset ι, k ≤ t.sup s := by
  classical
    rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : ∀ x : t, ∃ i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b, hb⟩) = id b from hf _]
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
/-
**CompleteLattice.IsCompactElement.exists_finset_of_le_iSup** 是 Mathlib 中的一个定理，位
于命名空间 `CompleteLattice.IsCompactElement`。
形式化陈述：∀ (α : Type u_2) [inst : CompleteLattice α] {k : α},   IsCompactElement k 
→ ∀ {ι : Type u_3} (f : ι → α), k ≤ ⨆ i, f i → ∃ s, k ≤ ⨆ i ∈ s, f i
参数：α : Type u_2；f : ι → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le_iSup_of_subset`：iSup_le_iSup_of_subset {f : β -> α} {s t : Set β
} : s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_sSup_of_le`：le_sSup_of_le (hb : b in s) (h : a <= b) : a <= sSup s
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem IsCompactElement.exists_finset_of_le_iSup {k : α} (hk : IsCompactElement k) {ι : Type*}
    (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
    let g : Finset ι → α := fun s => ⨆ i ∈ s, f i
    have h1 : DirectedOn (· ≤ ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, iSup_le_iSup_of_subset Finset.subset_union_left,
          iSup_le_iSup_of_subset Finset.subset_union_right⟩
    have h2 : k ≤ sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ := hk (Set.range g) (Set.range_nonempty g) h1 h2
    exact ⟨s, hs⟩

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its `sSup` strictly below `k`. -/
/-
**CompleteLattice.IsCompactElement.directed_sSup_lt_of_lt** 是 Mathlib 中的一个定理，位于命
名空间 `CompleteLattice.IsCompactElement`。
形式化陈述：∀ {α : Type u_3} [inst : CompleteLattice α] {k : α},   IsCompactElement k 
→ ∀ {s : Set α}, s.Nonempty → DirectedOn (fun x1 x2 => x1 ≤ x2) s → (∀ x ∈ s, x 
< k) → sSup s < k
参数：fun x1 x2 => x1 ≤ x2；∀ x ∈ s, x < k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b

--- 原说明 ---
A compact element `k` has the property that any directed set lying strictly belo
w `k` has
its `sSup` strictly below `k`.
-/
theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type*} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : sSup s < k := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s ≤ k := sSup_le fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)
/-
**CompleteLattice.isCompactElement_finsetSup** 是 Mathlib 中的一个定理，位于命名空间 `Complete
Lattice`。
形式化陈述：isCompactElement_finsetSup {α β : Type*} [CompleteLattice α] {f : β -> α} 
(s : Finset β) (h : forall x in s, IsCompactElement (f x)) : IsCompactElement (s
.sup f)
参数：s : Finset β；h : forall x in s, IsCompactElement (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.sup_le_of_le_directed`：sup_le_of_le_directed {α : Type*} [Semilat
ticeSup α] [OrderBot α] (s : Set α) (hs : s.Nonempty) (hdir : DirectedOn (· <= ·
) s) (t : Finset α…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem isCompactElement_finsetSup {α β : Type*} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
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
/-
**CompleteLattice.WellFoundedGT.isSupFiniteCompact** 是 Mathlib 中的一个定理，位于命名空间 `Co
mpleteLattice.WellFoundedGT`。
形式化陈述：∀ (α : Type u_2) [inst : CompleteLattice α] [WellFoundedGT α], CompleteLat
tice.IsSupFiniteCompact α
参数：α : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `wellFounded_gt`：∀ {α : Type u} [inst : LT α] [WellFoundedGT α], WellFoun
ded fun x1 x2 => x2 < x1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
-/
theorem WellFoundedGT.isSupFiniteCompact [WellFoundedGT α] :
    IsSupFiniteCompact α := fun s => by
  let S := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t, by simp [Set.insert_subset_iff, hy, ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁
/-
**CompleteLattice.IsSupFiniteCompact.isSupClosedCompact** 是 Mathlib 中的一个定理，位于命名空
间 `CompleteLattice.IsSupFiniteCompact`。
形式化陈述：∀ (α : Type u_2) [inst : CompleteLattice α], CompleteLattice.IsSupFiniteCo
mpact α → CompleteLattice.IsSupClosedCompact α
参数：α : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_singleton_bot_of_sSup_eq_bot_of_nonempty`：eq_singleton_bot_of_sSup_eq
_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥) (hne : s.Nonempty) : s = {⊥}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SupClosed.finsetSup_mem`：SupClosed.finsetSup_mem [OrderBot α] (hs : SupC
losed s) (ht : t.Nonempty) : (forall i in t, f i in s) -> t.sup f in s
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
/-
**CompleteLattice.IsSupClosedCompact.wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间 `Co
mpleteLattice.IsSupClosedCompact`。
形式化陈述：∀ (α : Type u_2) [inst : CompleteLattice α], CompleteLattice.IsSupClosedCo
mpact α → WellFoundedGT α
参数：α : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition'`：wellFoundedGT_iff_monotone_
chain_condition' [Preorder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists n
, forall m, n <= m -> ¬a n < a m
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem IsSupClosedCompact.wellFoundedGT (h : IsSupClosedCompact α) : WellFoundedGT α := by
  rw [wellFoundedGT_iff_monotone_chain_condition']
  intro a
  obtain ⟨n, hn⟩ : sSup (range a) ∈ range a := by
    apply h _ (range_nonempty a)
    rintro x ⟨m, rfl⟩ y ⟨n, rfl⟩
    exact ⟨_, map_sup a m n⟩
  refine ⟨n, fun m hm ↦ ?_⟩
  rw [hn]
  exact (le_sSup (mem_range_self m)).not_gt
/-
**CompleteLattice.isSupFiniteCompact_iff_all_elements_compact** 是 Mathlib 中的一个定理
，位于命名空间 `CompleteLattice`。
形式化陈述：isSupFiniteCompact_iff_all_elements_compact : IsSupFiniteCompact α ↔ foral
l k : α, IsCompactElement k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k := by
  simp_rw [isCompactElement_iff_exists_le_sSup_of_le_sSup]
  refine ⟨fun h k s hs => ?_, fun h s => ?_⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    have : sSup s = t.sup id := by
      suffices t.sup id ≤ sSup s by apply le_antisymm <;> assumption
      simp only [id, Finset.sup_le_iff]
      intro x hx
      exact le_sSup (hts hx)
    exact ⟨t, hts, this⟩

open List in
/-
**CompleteLattice.wellFoundedGT_characterisations** 是 Mathlib 中的一个定理，位于命名空间 `Com
pleteLattice`。
形式化陈述：wellFoundedGT_characterisations : List.TFAE [WellFoundedGT α, IsSupFiniteC
ompact α, IsSupClosedCompact α, forall k : α, IsCompactElement k]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLattice.WellFoundedGT.isSupFiniteCompact`：∀ (α : Type u_2) [inst
 : CompleteLattice α] [WellFoundedGT α], CompleteLattice.IsSupFiniteCompact α
· 使用定理 `CompleteLattice.IsSupFiniteCompact.isSupClosedCompact`：∀ (α : Type u_2) 
[inst : CompleteLattice α], CompleteLattice.IsSupFiniteCompact α → CompleteLatti
ce.IsSupClosedCompact α
· 使用定理 `CompleteLattice.IsSupClosedCompact.wellFoundedGT`：∀ (α : Type u_2) [inst
 : CompleteLattice α], CompleteLattice.IsSupClosedCompact α → WellFoundedGT α
· 使用定理 `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`：isSupFinite
Compact_iff_all_elements_compact : IsSupFiniteCompact α ↔ forall k : α, IsCompac
tElement k
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem wellFoundedGT_characterisations : List.TFAE
    [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] := by
  tfae_have 1 → 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 → 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 → 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish
/-
**CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact** 是 Mathlib 中的一个定理，位于命名空间
 `CompleteLattice`。
形式化陈述：wellFoundedGT_iff_isSupFiniteCompact : WellFoundedGT α ↔ IsSupFiniteCompac
t α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompleteLattice.wellFoundedGT_characterisations`：wellFoundedGT_character
isations : List.TFAE [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact 
α, forall k : α, IsCompactElement k]
-/
theorem wellFoundedGT_iff_isSupFiniteCompact :
    WellFoundedGT α ↔ IsSupFiniteCompact α :=
  (wellFoundedGT_characterisations α).out 0 1
/-
**CompleteLattice.isSupFiniteCompact_iff_isSupClosedCompact** 是 Mathlib 中的一个定理，位
于命名空间 `CompleteLattice`。
形式化陈述：isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupCl
osedCompact α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompleteLattice.wellFoundedGT_characterisations`：wellFoundedGT_character
isations : List.TFAE [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact 
α, forall k : α, IsCompactElement k]
-/
theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFoundedGT_characterisations α).out 1 2
/-
**CompleteLattice.isSupClosedCompact_iff_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空间
 `CompleteLattice`。
形式化陈述：isSupClosedCompact_iff_wellFoundedGT : IsSupClosedCompact α ↔ WellFoundedG
T α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompleteLattice.wellFoundedGT_characterisations`：wellFoundedGT_character
isations : List.TFAE [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact 
α, forall k : α, IsCompactElement k]
-/
theorem isSupClosedCompact_iff_wellFoundedGT :
    IsSupClosedCompact α ↔ WellFoundedGT α :=
  (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

end CompleteLattice


/-
**WellFoundedGT.finite_of_sSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.finite_of_sSupIndep [WellFoundedGT α] {s : Set α} (hs : sSup
Indep s) : s.Finite
参数：hs : sSupIndep s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CompleteLattice.WellFoundedGT.isSupFiniteCompact`：∀ (α : Type u_2) [inst
 : CompleteLattice α] [WellFoundedGT α], CompleteLattice.IsSupFiniteCompact α
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `sSupIndep.mono`：sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIn
dep t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem WellFoundedGT.finite_of_sSupIndep [WellFoundedGT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  classical
    by_contra! contra
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.sdiff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_sSup hx₀
/-
**WellFoundedGT.finite_ne_bot_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.finite_ne_bot_of_iSupIndep [WellFoundedGT α] {ι : Type*} {t 
: ι -> α} (ht : iSupIndep t) : Set.Finite {i | t i != ⊥}
参数：ht : iSupIndep t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `WellFoundedGT.finite_of_sSupIndep`：WellFoundedGT.finite_of_sSupIndep [We
llFoundedGT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `iSupIndep.sSupIndep_range`：iSupIndep.sSupIndep_range (ht : iSupIndep t) 
: sSupIndep range t
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `iSupIndep.injOn`：iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i !
= ⊥}
-/
theorem WellFoundedGT.finite_ne_bot_of_iSupIndep [WellFoundedGT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range
/-
**WellFoundedGT.finite_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedGT.finite_of_iSupIndep [WellFoundedGT α] {ι : Type*} {t : ι -> 
α} (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : Finite ι
参数：ht : iSupIndep t；h_ne_bot : forall i, t i != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective_finite_range`：Finite.of_injective_finite_range {f : 
ι -> α} (hf : Function.Injective f) [Finite (range f)] : Finite ι
· 使用定理 `iSupIndep.injective`：iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : 
forall i, t i != ⊥) : Injective t
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `WellFoundedGT.finite_of_sSupIndep`：WellFoundedGT.finite_of_sSupIndep [We
llFoundedGT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `iSupIndep.sSupIndep_range`：iSupIndep.sSupIndep_range (ht : iSupIndep t) 
: sSupIndep range t
-/
theorem WellFoundedGT.finite_of_iSupIndep [WellFoundedGT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)
/-
**WellFoundedLT.finite_of_sSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedLT.finite_of_sSupIndep [WellFoundedLT α] {s : Set α} (hs : sSup
Indep s) : s.Finite
参数：hs : sSupIndep s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Set.Infinite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Infinite → t.Finite 
→ (s \ t).Infinite
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Disjoint.right_lt_sup_of_left_ne_bot`：Disjoint.right_lt_sup_of_left_ne_b
ot [SemilatticeSup α] [OrderBot α] {a b : α} (h : Disjoint a b) (ha : a != ⊥) : 
b < a ⊔ b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RelEmbedding.not_wellFounded`：not_wellFounded (f : ((· > ·) : Nat -> Nat
 -> Prop) ↪r r) : ¬WellFounded r
· 使用定理 `instIsStrictOrderLt`：∀ {α : Type u} [inst : Preorder α], IsStrictOrder α
 fun x1 x2 => x1 < x2
· 使用引理 `wellFounded_lt`：wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α
 (· < ·)
-/
theorem WellFoundedLT.finite_of_sSupIndep [WellFoundedLT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  by_contra inf
  let e := (Infinite.sdiff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i ≥ n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) ≤ a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi ↦ le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi ↦ le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded wellFounded_lt
  exact ⟨(e i).2.1, fun h ↦ n.lt_succ_self.not_ge <| hi.trans_eq <| e.2 <| Subtype.val_injective h⟩
/-
**WellFoundedLT.finite_ne_bot_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedLT.finite_ne_bot_of_iSupIndep [WellFoundedLT α] {ι : Type*} {t 
: ι -> α} (ht : iSupIndep t) : Set.Finite {i | t i != ⊥}
参数：ht : iSupIndep t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `WellFoundedLT.finite_of_sSupIndep`：WellFoundedLT.finite_of_sSupIndep [We
llFoundedLT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `iSupIndep.sSupIndep_range`：iSupIndep.sSupIndep_range (ht : iSupIndep t) 
: sSupIndep range t
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `iSupIndep.injOn`：iSupIndep.injOn (ht : iSupIndep t) : InjOn t {i | t i !
= ⊥}
-/
theorem WellFoundedLT.finite_ne_bot_of_iSupIndep [WellFoundedLT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range
/-
**WellFoundedLT.finite_of_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedLT.finite_of_iSupIndep [WellFoundedLT α] {ι : Type*} {t : ι -> 
α} (ht : iSupIndep t) (h_ne_bot : forall i, t i != ⊥) : Finite ι
参数：ht : iSupIndep t；h_ne_bot : forall i, t i != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective_finite_range`：Finite.of_injective_finite_range {f : 
ι -> α} (hf : Function.Injective f) [Finite (range f)] : Finite ι
· 使用定理 `iSupIndep.injective`：iSupIndep.injective (ht : iSupIndep t) (h_ne_bot : 
forall i, t i != ⊥) : Injective t
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `WellFoundedLT.finite_of_sSupIndep`：WellFoundedLT.finite_of_sSupIndep [We
llFoundedLT α] {s : Set α} (hs : sSupIndep s) : s.Finite
· 使用定理 `iSupIndep.sSupIndep_range`：iSupIndep.sSupIndep_range (ht : iSupIndep t) 
: sSupIndep range t
-/
theorem WellFoundedLT.finite_of_iSupIndep [WellFoundedLT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

/-- A complete lattice is said to be compactly generated if any
element is the `sSup` of compact elements. -/
/-
**IsCompactlyGenerated** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [CompleteLattice α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete lattice is said to be compactly generated if any
element is the `sSup` of compact elements.
-/
class IsCompactlyGenerated (α : Type*) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
  every element is the `sSup` of some set of compact elements. -/
  exists_sSup_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, IsCompactElement x) ∧ sSup s = x

section

variable [IsCompactlyGenerated α] {a : α} {s : Set α}

@[simp]
/-
**sSup_compact_le_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_compact_le_eq (b) : sSup { c : α | IsCompactElement c ∧ c <= b } = b
参数：b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactlyGenerated.exists_sSup_eq`：∀ {α : Type u_3} {inst : CompleteLa
ttice α} [self : IsCompactlyGenerated α] (x : α),   ∃ s, (∀ x ∈ s, IsCompactElem
ent x) ∧ sSup s = x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem sSup_compact_le_eq (b) :
    sSup { c : α | IsCompactElement c ∧ c ≤ b } = b := by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)

@[simp]
/-
**sSup_compact_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_compact_eq_top : sSup { a : α | IsCompactElement a } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_compact_le_eq`：sSup_compact_le_eq (b) : sSup { c : α | IsCompactEle
ment c ∧ c <= b } = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_compact_eq_top : sSup { a : α | IsCompactElement a } = ⊤ := by
  rw [← sSup_compact_le_eq ⊤]
  simp_rw [le_top, and_true]
/-
**le_iff_compact_le_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_compact_le_imp {a b : α} : a <= b ↔ forall c : α, IsCompactElement 
c -> c <= a -> c <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_compact_le_eq`：sSup_compact_le_eq (b) : sSup { c : α | IsCompactEle
ment c ∧ c <= b } = b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_iff_compact_le_imp {a b : α} :
    a ≤ b ↔ ∀ c : α, IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab _ _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a, ← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

/-- This property is sometimes referred to as `α` being upper continuous. -/
/-
**DirectedOn.inf_sSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedOn.inf_sSup_eq (h : DirectedOn (· <= ·) s) : a ⊓ sSup s = ⨆ b in s
, a ⊓ b
参数：h : DirectedOn (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_compact_le_imp`：le_iff_compact_le_imp {a b : α} : a <= b ↔ forall
 c : α, IsCompactElement c -> c <= a -> c <= b
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iSup_inf_le_inf_sSup`：∀ {α : Type u_1} [inst : CompleteLattice α] {a : α
} {s : Set α}, ⨆ b ∈ s, a ⊓ b ≤ a ⊓ sSup s

--- 原说明 ---
This property is sometimes referred to as `α` being upper continuous.
-/
theorem DirectedOn.inf_sSup_eq (h : DirectedOn (· ≤ ·) s) : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
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

/-- This property is sometimes referred to as `α` being upper continuous. -/
/-
**DirectedOn.sSup_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompleteLattice α] [IsCompactlyGenerated α] {a : 
α} {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → sSup s ⊓ a = ⨆ b ∈ s, b 
⊓ a
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectedOn.inf_sSup_eq`：DirectedOn.inf_sSup_eq (h : DirectedOn (· <= ·) 
s) : a ⊓ sSup s = ⨆ b in s, a ⊓ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This property is sometimes referred to as `α` being upper continuous.
-/
protected theorem DirectedOn.sSup_inf_eq (h : DirectedOn (· ≤ ·) s) :
    sSup s ⊓ a = ⨆ b ∈ s, b ⊓ a := by
  simp_rw [inf_comm _ a, h.inf_sSup_eq]
/-
**Directed.inf_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {f : ι → α} [Is
CompactlyGenerated α] {a : α},   Directed (fun x1 x2 => x1 ≤ x2) f → a ⊓ ⨆ i, f 
i = ⨆ i, a ⊓ f i
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `DirectedOn.inf_sSup_eq`：DirectedOn.inf_sSup_eq (h : DirectedOn (· <= ·) 
s) : a ⊓ sSup s = ⨆ b in s, a ⊓ b
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
protected theorem Directed.inf_iSup_eq (h : Directed (· ≤ ·) f) :
    (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  rw [iSup, h.directedOn_range.inf_sSup_eq, iSup_range]
/-
**Directed.iSup_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {f : ι → α} [Is
CompactlyGenerated α] {a : α},   Directed (fun x1 x2 => x1 ≤ x2) f → (⨆ i, f i) 
⊓ a = ⨆ i, f i ⊓ a
参数：fun x1 x2 => x1 ≤ x2；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `DirectedOn.sSup_inf_eq`：∀ {α : Type u_2} [inst : CompleteLattice α] [IsC
ompactlyGenerated α] {a : α} {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s 
→ sSup s ⊓ a…
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
protected theorem Directed.iSup_inf_eq (h : Directed (· ≤ ·) f) :
    (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, h.directedOn_range.sSup_inf_eq, iSup_range]
/-
**DirectedOn.disjoint_sSup_right** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompleteLattice α] [IsCompactlyGenerated α] {a : 
α} {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → (Disjoint a (sSup s) ↔ ∀
 ⦃b : α⦄, b ∈ s → Disjoint a b)
参数：fun x1 x2 => x1 ≤ x2；Disjoint a (sSup s) ↔ ∀ ⦃b : α⦄, b ∈ s → Disjoint a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectedOn.inf_sSup_eq`：DirectedOn.inf_sSup_eq (h : DirectedOn (· <= ·) 
s) : a ⊓ sSup s = ⨆ b in s, a ⊓ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem DirectedOn.disjoint_sSup_right (h : DirectedOn (· ≤ ·) s) :
    Disjoint a (sSup s) ↔ ∀ ⦃b⦄, b ∈ s → Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]
/-
**DirectedOn.disjoint_sSup_left** 是 Mathlib 中的一个定理，位于命名空间 `DirectedOn`。
形式化陈述：∀ {α : Type u_2} [inst : CompleteLattice α] [IsCompactlyGenerated α] {a : 
α} {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s → (Disjoint (sSup s) a ↔ ∀
 ⦃b : α⦄, b ∈ s → Disjoint b a)
参数：fun x1 x2 => x1 ≤ x2；Disjoint (sSup s) a ↔ ∀ ⦃b : α⦄, b ∈ s → Disjoint b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectedOn.sSup_inf_eq`：∀ {α : Type u_2} [inst : CompleteLattice α] [IsC
ompactlyGenerated α] {a : α} {s : Set α},   DirectedOn (fun x1 x2 => x1 ≤ x2) s 
→ sSup s ⊓ a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem DirectedOn.disjoint_sSup_left (h : DirectedOn (· ≤ ·) s) :
    Disjoint (sSup s) a ↔ ∀ ⦃b⦄, b ∈ s → Disjoint b a := by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]
/-
**Directed.disjoint_iSup_right** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {f : ι → α} [Is
CompactlyGenerated α] {a : α},   Directed (fun x1 x2 => x1 ≤ x2) f → (Disjoint a
 (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i))
参数：fun x1 x2 => x1 ≤ x2；Disjoint a (⨆ i, f i) ↔ ∀ (i : ι), Disjoint a (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Directed.inf_iSup_eq`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLa
ttice α] {f : ι → α} [IsCompactlyGenerated α] {a : α},   Directed (fun x1 x2 => 
x1 ≤ x2) f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem Directed.disjoint_iSup_right (h : Directed (· ≤ ·) f) :
    Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]
/-
**Directed.disjoint_iSup_left** 是 Mathlib 中的一个定理，位于命名空间 `Directed`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLattice α] {f : ι → α} [Is
CompactlyGenerated α] {a : α},   Directed (fun x1 x2 => x1 ≤ x2) f → (Disjoint (
⨆ i, f i) a ↔ ∀ (i : ι), Disjoint (f i) a)
参数：fun x1 x2 => x1 ≤ x2；Disjoint (⨆ i, f i) a ↔ ∀ (i : ι), Disjoint (f i) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Directed.iSup_inf_eq`：∀ {ι : Sort u_1} {α : Type u_2} [inst : CompleteLa
ttice α] {f : ι → α} [IsCompactlyGenerated α] {a : α},   Directed (fun x1 x2 => 
x1 ≤ x2) f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem Directed.disjoint_iSup_left (h : Directed (· ≤ ·) f) :
    Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]

/-- This property is equivalent to `α` being upper continuous. -/
/-
**inf_sSup_eq_iSup_inf_sup_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inf_sSup_eq_iSup_inf_sup_finset : a ⊓ sSup s = ⨆ (t : Finset α) (_ : ↑t su
bseteq s), a ⊓ t.sup id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_compact_le_imp`：le_iff_compact_le_imp {a b : α} : a <= b ↔ forall
 c : α, IsCompactElement c -> c <= a -> c <= b
· 使用定理 `CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup`：isCompac
tElement_iff_exists_le_sSup_of_le_sSup (k : α) : IsCompactElement k ↔ forall s :
 Set α, k <= sSup s -> exists t : Finset α, ↑t subse…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s

--- 原说明 ---
This property is equivalent to `α` being upper continuous.
-/
theorem inf_sSup_eq_iSup_inf_sup_finset :
    a ⊓ sSup s = ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup] at hc
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine (le_inf hcinf.1 ht2).trans ?_
      exact le_iSup₂ (f := fun (t' : Finset α) (ht' : ↑t' ⊆ s) => a ⊓ t'.sup id) t ht1)
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))
/-
**sSupIndep_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_iff_finite {s : Set α} : sSupIndep s ↔ forall t : Finset α, ↑t s
ubseteq s -> sSupIndep (↑t : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSupIndep.mono`：sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIn
dep t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `inf_sSup_eq_iSup_inf_sup_finset`：inf_sSup_eq_iSup_inf_sup_finset : a ⊓ s
Sup s = ⨆ (t : Finset α) (_ : ↑t subseteq s), a ⊓ t.sup id
· 使用定理 `iSup_eq_bot`：iSup_eq_bot : iSup s = ⊥ ↔ forall i, s i = ⊥
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `Set.insert_sdiff_self_of_notMem`：insert_sdiff_self_of_notMem (h : a ∉ s)
 : insert a s \ {a} = s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem sSupIndep_iff_finite {s : Set α} :
    sSupIndep s ↔
      ∀ t : Finset α, ↑t ⊆ s → sSupIndep (↑t : Set α) :=
  ⟨fun hs _ ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot]
    intro t
    rw [iSup_eq_bot, Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_sdiff_self_of_notMem] at h'
        exact fun con => ((Set.mem_sdiff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht sdiff_subset⟩⟩
/-
**iSupIndep_iff_supIndep** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_supIndep {ι : Type*} {f : ι -> α} : iSupIndep f ↔ forall (s 
: Finset ι), s.SupIndep f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.supIndep'`：iSupIndep.supIndep' {f : ι -> α} (s : Finset ι) (h 
: iSupIndep f) : s.SupIndep f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSupIndep_def'`：iSupIndep_def' : iSupIndep t ↔ forall i, Disjoint (t i) 
(sSup (t '' { j | j != i }))
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Finset.supIndep_pair`：supIndep_pair [DecidableEq ι] {i j : ι} (hij : i !
= j) : ({i, j} : Finset ι).SupIndep f ↔ Disjoint (f i) (f j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sSup_eq_iSup_inf_sup_finset`：inf_sSup_eq_iSup_inf_sup_finset : a ⊓ s
Sup s = ⨆ (t : Finset α) (_ : ↑t subseteq s), a ⊓ t.sup id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_erase_bot`：sup_erase_bot [DecidableEq α] (s : Finset α) : (s.
erase ⊥).sup id = s.sup id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.supIndep_iff_disjoint_erase`：supIndep_iff_disjoint_erase [Decidab
leEq ι] : s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
lemma iSupIndep_iff_supIndep {ι : Type*} {f : ι → α} :
    iSupIndep f ↔ ∀ (s : Finset ι), s.SupIndep f := by
  refine ⟨fun h ↦ h.supIndep', fun h ↦ iSupIndep_def'.mpr fun i ↦ ?_⟩
  classical
  have hf : Set.InjOn f {i : ι | f i ≠ ⊥} := by
    by_contra! hf
    simp_all only [Set.InjOn, ne_eq, Set.mem_ofPred_eq, not_forall]
    obtain ⟨x₁, hx₁, x₂, hx₂, hfeq, hneq⟩ := hf
    specialize h ({x₁, x₂} : Finset ι)
    rw [Finset.supIndep_pair hneq, disjoint_iff, hfeq, inf_idem (f x₂)] at h
    contradiction
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij ↦ by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this, Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

@[deprecated iSupIndep_iff_supIndep (since := "2026-02-18")]
/-
**iSupIndep_iff_supIndep_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep_iff_supIndep_of_injOn {ι : Type*} {f : ι -> α} (hf : InjOn f {i 
| f i != ⊥}) : iSupIndep f ↔ forall (s : Finset ι), s.SupIndep f
参数：hf : InjOn f {i | f i != ⊥}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.supIndep'`：iSupIndep.supIndep' {f : ι -> α} (s : Finset ι) (h 
: iSupIndep f) : s.SupIndep f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSupIndep_def'`：iSupIndep_def' : iSupIndep t ↔ forall i, Disjoint (t i) 
(sSup (t '' { j | j != i }))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_sSup_eq_iSup_inf_sup_finset`：inf_sSup_eq_iSup_inf_sup_finset : a ⊓ s
Sup s = ⨆ (t : Finset α) (_ : ↑t subseteq s), a ⊓ t.sup id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_erase_bot`：sup_erase_bot [DecidableEq α] (s : Finset α) : (s.
erase ⊥).sup id = s.sup id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.coe_erase`：coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \
 {a} : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.erase_insert_eq_erase`：erase_insert_eq_erase (s : Finset α) (a : 
α) : (insert a s).erase a = s.erase a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Finset.supIndep_iff_disjoint_erase`：supIndep_iff_disjoint_erase [Decidab
leEq ι] : s.SupIndep f ↔ forall i in s, Disjoint (f i) ((s.erase i).sup f)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
-/
lemma iSupIndep_iff_supIndep_of_injOn {ι : Type*} {f : ι → α}
    (hf : InjOn f {i | f i ≠ ⊥}) :
    iSupIndep f ↔ ∀ (s : Finset ι), s.SupIndep f := by
  refine ⟨fun h ↦ h.supIndep', fun h ↦ iSupIndep_def'.mpr fun i ↦ ?_⟩
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  classical
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij ↦ by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this, Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)
/-
**sSupIndep_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_iUnion_of_directed {η : Type*} {s : η -> Set α} (hs : Directed (
· subseteq ·) s) (h : forall i, sSupIndep (s i)) : sSupIndep (⋃ i, s i)
参数：hs : Directed (· subseteq ·) s；h : forall i, sSupIndep (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSupIndep_iff_finite`：sSupIndep_iff_finite {s : Set α} : sSupIndep s ↔ f
orall t : Finset α, ↑t subseteq s -> sSupIndep (↑t : Set α)
· 使用定理 `Set.finite_subset_iUnion`：finite_subset_iUnion {s : Set α} (hs : s.Finit
e) {ι} {t : ι -> Set α} (h : s subseteq ⋃ i, t i) : exists I : Set ι, I.Finite ∧
 s subseteq ⋃ …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Directed.finset_le`：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r
] {ι} [hι : Nonempty ι] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists 
z, foral…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `sSupIndep.mono`：sSupIndep.mono {t : Set α} (hst : t subseteq s) : sSupIn
dep t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
theorem sSupIndep_iUnion_of_directed {η : Type*} {s : η → Set α}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, sSupIndep (s i)) :
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
/-
**iSupIndep_sUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· subsete
q ·) s) (h : forall a in s, sSupIndep a) : sSupIndep (⋃₀ s)
参数：Set α；hs : DirectedOn (· subseteq ·) s；h : forall a in s, sSupIndep a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `sSupIndep_iUnion_of_directed`：sSupIndep_iUnion_of_directed {η : Type*} {
s : η -> Set α} (hs : Directed (· subseteq ·) s) (h : forall i, sSupIndep (s i))
 : sSupIndep (⋃ i,…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem iSupIndep_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, sSupIndep a) : sSupIndep (⋃₀ s) := by
  rw [Set.sUnion_eq_iUnion]
  exact sSupIndep_iUnion_of_directed hs.directed_val (by simpa using h)
/-
**disjoint_biSup_of_finite_disjoint_biSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_biSup_of_finite_disjoint_biSup {ι : Type*} {f : ι -> α} {s : Set 
ι} {a : α} (hs : forall t subseteq s, t.Finite -> Disjoint (⨆ i in t, f i) a) : 
Disjoint (⨆ i in s, f i) a
参数：hs : forall t subseteq s, t.Finite -> Disjoint (⨆ i in t, f i) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `inf_sSup_eq_iSup_inf_sup_finset`：inf_sSup_eq_iSup_inf_sup_finset : a ⊓ s
Sup s = ⨆ (t : Finset α) (_ : ↑t subseteq s), a ⊓ t.sup id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Finite.exists_subset_finite_image_eq`：∀ {α : Type u} {β : Type v} {f
 : α → β} {s : Set α} {u : Set β},   u.Finite → u ⊆ f '' s → ∃ t ⊆ s, ∃ (_ : t.F
inite), f '' t = u
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
-/
lemma disjoint_biSup_of_finite_disjoint_biSup {ι : Type*} {f : ι → α} {s : Set ι} {a : α}
    (hs : ∀ t ⊆ s, t.Finite → Disjoint (⨆ i ∈ t, f i) a) :
    Disjoint (⨆ i ∈ s, f i) a := by
  simp_rw [disjoint_iff, iSup_subtype', ← sSup_range, inf_comm, inf_sSup_eq_iSup_inf_sup_finset,
    iSup_eq_bot]
  intro u hu
  obtain ⟨t, ht, ht', htu⟩ : ∃ᵉ (t ⊆ s) (hu : t.Finite), f '' t = u :=
    Set.Finite.exists_subset_finite_image_eq u.finite_toSet <| by rwa [Set.image_eq_range f s]
  replace htu : u.sup id = ⨆ i ∈ t, f i := by
    simp only [Finset.sup_eq_iSup, id_eq, ← Finset.mem_coe, ← htu, iSup_image]
  rw [inf_comm, ← disjoint_iff, htu]
  exact hs t ht ht'
/-
**iSupIndep.disjoint_biSup_biSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSupIndep.disjoint_biSup_biSup {ι : Type*} [IsModularLattice α] {f : ι -> 
α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t) : Disjoint (⨆ i in s, f
 i) (⨆ i in t, f i)
参数：hf : iSupIndep f；hst : Disjoint s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `disjoint_biSup_of_finite_disjoint_biSup`：disjoint_biSup_of_finite_disjoi
nt_biSup {ι : Type*} {f : ι -> α} {s : Set ι} {a : α} (hs : forall t subseteq s,
 t.Finite -> Disjoint (⨆ i in…
· 使用引理 `iSupIndep.disjoint_biSup_biSup'`：iSupIndep.disjoint_biSup_biSup' [IsModu
larLattice α] {f : ι -> α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t)
 (hs : s.Finite) : Di…
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
-/
lemma iSupIndep.disjoint_biSup_biSup {ι : Type*} [IsModularLattice α]
    {f : ι → α} {s t : Set ι} (hf : iSupIndep f) (hst : Disjoint s t) :
    Disjoint (⨆ i ∈ s, f i) (⨆ i ∈ t, f i) :=
  disjoint_biSup_of_finite_disjoint_biSup fun _ h₁ h₂ ↦
    disjoint_biSup_biSup' hf (Set.disjoint_of_subset_left h₁ hst) h₂

end

namespace CompleteLattice

/-
**CompleteLattice.isCompactlyGenerated_of_wellFoundedGT** 是 Mathlib 中的一个定理，位于命名空
间 `CompleteLattice`。
形式化陈述：isCompactlyGenerated_of_wellFoundedGT [h : WellFoundedGT α] : IsCompactlyG
enerated α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`：isSupFinite
Compact_iff_all_elements_compact : IsSupFiniteCompact α ↔ forall k : α, IsCompac
tElement k
· 使用定理 `CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact`：wellFoundedGT_iff_
isSupFiniteCompact : WellFoundedGT α ↔ IsSupFiniteCompact α
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
-/
theorem isCompactlyGenerated_of_wellFoundedGT [h : WellFoundedGT α] :
    IsCompactlyGenerated α := by
  rw [wellFoundedGT_iff_isSupFiniteCompact, isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩

/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) :
    IsCoatomic (Set.Iic k) := by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top]
  right
  have ⟨a, ba, h⟩ := zorn_le_nonempty₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  · refine ⟨⟨a, le_of_lt h.prop⟩, ⟨ne_of_lt h.prop, fun c hck => by_contradiction fun c₀ => ?_⟩, ba⟩
    cases h.eq_of_le (y := c.1) (lt_of_le_of_ne c.2 fun con ↦ c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine ⟨sSup S, IsCompactElement.directed_sSup_lt_of_lt h hS cC.directedOn SC, ?_⟩
      intro; apply le_sSup
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩

theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

/--
If each family `f i` is `iSupIndep`, then the family of pointwise infima
`k ↦ ⨅ i, f i (k i)` is also `iSupIndep`.
-/
theorem iSupIndep.iInf {ι : Type*} {κ : ι → Type*} (f : (i : ι) → κ i → α)
    (h_indep : ∀ i : ι, iSupIndep (f i)) : iSupIndep (fun k : (i : ι) → κ i ↦ ⨅ i, f i (k i)) := by
  rw [iSupIndep_iff_supIndep]
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : 1 < s.card; swap
    · by_cases hcard0 : s.card = 0 <;> grind [Finset.card_eq_zero, Finset.card_eq_one]
    · obtain ⟨k₁, k₂, _, _, h⟩ := Finset.one_lt_card_iff.mp hs
      obtain ⟨i, hi⟩ : ∃ i : ι, k₁ i ≠ k₂ i := Function.ne_iff.mp h
      classical
      rw [← Finset.image_biUnion_filter_eq s (· i)]
      refine Finset.SupIndep.biUnion ?_ (by grind)
      apply ((h_indep i).supIndep' _).mono
      simp_rw [Finset.sup_le_iff, Finset.mem_filter, and_imp]
      rintro _ _ _ _ rfl
      exact iInf_le _ _

instance (priority := 100) isAtomic_of_complementedLattice [ComplementedLattice α] : IsAtomic α :=
  ⟨fun b => by
    by_cases h : { c : α | IsCompactElement c ∧ c ≤ b } ⊆ {⊥}
    · left
      rw [← sSup_compact_le_eq b, sSup_eq_bot]
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
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      exact ⟨a, ha.of_isAtom_coe_Iic, hac.trans hcb⟩⟩

/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      have hle : sSup { a : α | IsAtom a ∧ a ≤ b } ≤ b := sSup_le fun _ => And.right
      apply (lt_or_eq_of_le hle).resolve_left _
      intro con
      obtain ⟨c, hc⟩ := exists_isCompl (⟨sSup { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_lt con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
      · apply ha.1
        rw [eq_bot_iff]
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        exact le_sSup ⟨ha.of_isAtom_coe_Iic, a.2⟩, fun _ => And.left⟩

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of independent atoms.
-/

/-- In an atomic lattice, every element `b` has a complement of the form `sSup s` relative to a
given element `c`, where each element of `s` is an atom.
See also `complementedLattice_of_sSup_atoms_eq_top`. -/
theorem exists_sSupIndep_disjoint_sSup_atoms (b c : α) (hbc : b ≤ c)
    (h : sSup {a ≤ c | IsAtom a} = c) :
    ∃ s : Set α, sSupIndep s ∧ Disjoint b (sSup s) ∧ b ⊔ sSup s = c ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ ∀ a ∈ s, IsAtom a ∧ a ≤ c})
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
  refine ⟨s, s_ind, b_inf_Sup_s, le_antisymm ?_ ?_, fun a ha ↦ (s_atoms a ha).1⟩
  · simp_all
  rw [← h, sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine (ha.2.le_iff.mp inf_le_left).resolve_left fun con => ha.2.1 ?_
  rw [← con, eq_comm, inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_sdiff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.sdiff_subset).trans le_sup_right)
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_sdiff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, sSup_union, sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha.symm

/-- In an atomic lattice, every element `b` has a complement of the form `sSup s`, where each
element of `s` is an atom. See also `complementedLattice_of_sSup_atoms_eq_top`. -/
theorem exists_sSupIndep_isCompl_sSup_atoms (h : sSup { a : α | IsAtom a } = ⊤) (b : α) :
    ∃ s : Set α, sSupIndep s ∧ IsCompl b (sSup s) ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  simpa [isCompl_iff, codisjoint_iff, and_assoc]
    using exists_sSupIndep_disjoint_sSup_atoms b ⊤ le_top <| by simpa using h

theorem exists_sSupIndep_of_sSup_atoms (b : α) (h : sSup {a ≤ b | IsAtom a} = b) :
    ∃ s : Set α, sSupIndep s ∧ sSup s = b ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  let ⟨s, s_ind, _, s_atoms⟩ := exists_sSupIndep_disjoint_sSup_atoms ⊥ b bot_le h
  ⟨s, s_ind, by simpa using s_atoms⟩

theorem exists_sSupIndep_of_sSup_atoms_eq_top (h : sSup {a : α | IsAtom a} = ⊤) :
    ∃ s : Set α, sSupIndep s ∧ sSup s = ⊤ ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  exists_sSupIndep_of_sSup_atoms ⊤ (by simpa)

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α where
  exists_isCompl b :=
    let ⟨s, _, hcompl, _⟩ := exists_sSupIndep_isCompl_sSup_atoms (by simpa) b
    ⟨sSup s, hcompl⟩

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top

theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α := by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic

end

