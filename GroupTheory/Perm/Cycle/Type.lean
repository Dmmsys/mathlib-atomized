/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Tactic.NormNum.GCD

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `Equiv.Perm.cycleType σ` where `σ` is a permutation of a `Fintype`
- `Equiv.Perm.partition σ` where `σ` is a permutation of a `Fintype`

## Main results

- `sum_cycleType` : The sum of `σ.cycleType` equals `σ.support.card`
- `lcm_cycleType` : The lcm of `σ.cycleType` equals `orderOf σ`
- `isConj_iff_cycleType_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_orderOf_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/

@[expose] public section

open scoped Finset

namespace Equiv.Perm

open List (Vector)
open Equiv List Multiset

variable {α : Type*} [Fintype α]

section CycleType

variable [DecidableEq α]

/--
Definition of `cycleType` / `cycleType` 的定义

English:
definition cycleType
  signature: (σ : Perm α)
  body: σ.cycleFactorsFinset.1.map (Finset.card ∘ support)

中文:
定义 cycleType
  签名: (σ : 置换 α)
  定义体: σ.cycleFactorsFinset.1.map (Finset.card ∘ support)

Depends on / 依赖: Finset, Finset.card, cycleFactorsFinset, support
-/
def cycleType (σ : Perm α) : Multiset Nat :=
  σ.cycleFactorsFinset.1.map (Finset.card ∘ support)

/--
theorem `cycleType_def` / 定理 `cycleType_def`

English:
theorem cycleType_def
  given: (σ : Perm α)
  proof: rfl

中文:
定理 cycleType_def
  条件: (σ : 置换 α)
  证明: rfl
-/
theorem cycleType_def (σ : Perm α) :
    σ.cycleType = σ.cycleFactorsFinset.1.map (Finset.card ∘ support) :=
  rfl

/--
theorem `cycleType_eq'` / 定理 `cycleType_eq'`

English:
theorem cycleType_eq'
  statement: {σ : Perm α} (s : Finset (Perm α)) (h1 : forall f : Perm α, f in s -> f.IsCycle)
  proof: by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

中文:
定理 cycleType_eq'
  结论: {σ : 置换 α} (s : 有限集 (置换 α)) (h1 : 对任意 f : 置换 α, f in s -> f.是环)
  证明: by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

Depends on / 依赖: cycleFactorsFinset_eq_finset, cycleType_def
-/
theorem cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : forall f : Perm α, f in s -> f.IsCycle)
    (h2 : (s : Set (Perm α)).Pairwise Disjoint)
    (h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.commute) = σ) :
    σ.cycleType = s.1.map (Finset.card ∘ support) := by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cycleType_eq` / 定理 `cycleType_eq`

English:
theorem cycleType_eq
  statement: {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
  proof: by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

中文:
定理 cycleType_eq
  结论: {σ : 置换 α} (l : 列表 (置换 α)) (h0 : l.乘积 = σ)
  证明: by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

Depends on / 依赖: Function, Function.comp_def, List.dedup_eq_self.mpr, comp_def, cycleType_eq, dedup_eq_self, l.Nodup, l.toFinset, nodup_of_pairwise_disjoint_cycles, toFinset
-/
theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
    (h1 : forall σ : Perm α, σ in l -> σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) := by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `CycleType.count_def` / 定理 `CycleType.count_def`

English:
theorem CycleType.count_def
  given: {σ : Perm α} (n : Nat)
  proof: by
  -- work on the LHS
  rw [cycleType]; rw [Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card]; rw [Finset.univ_eq_attach]; rw [Finset.filter_attach']; rw [Finset.card_map]; rw [Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]

@[simp]

中文:
定理 CycleType.count_def
  条件: {σ : 置换 α} (n : 自然数)
  证明: by
  -- work on the LHS
  rw [cycleType]; rw [Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card]; rw [Finset.univ_eq_attach]; rw [Finset.filter_attach']; rw [Finset.card_map]; rw [Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]

@[simp]
-/
theorem CycleType.count_def {σ : Perm α} (n : Nat) :
    σ.cycleType.count n =
      Fintype.card {c : σ.cycleFactorsFinset // #(c : Perm α).support = n } := by
  -- work on the LHS
  rw [cycleType]; rw [Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card]; rw [Finset.univ_eq_attach]; rw [Finset.filter_attach']; rw [Finset.card_map]; rw [Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]

@[simp]
/--
theorem `cycleType_eq_zero` / 定理 `cycleType_eq_zero`

English:
theorem cycleType_eq_zero
  given: {σ : Perm α}
  statement: σ.cycleType = 0 ↔ σ = 1
  proof: by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]

@[simp]

中文:
定理 cycleType_eq_zero
  条件: {σ : 置换 α}
  结论: σ.cycleType = 0 ↔ σ = 1
  证明: by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]

@[simp]

Depends on / 依赖: cycleFactorsFinset_eq_empty_iff, cycleType_def
-/
theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]

@[simp]
/--
theorem `cycleType_one` / 定理 `cycleType_one`

English:
theorem cycleType_one
  statement: (1 : Perm α).cycleType = 0
  proof: cycleType_eq_zero.2 rfl

中文:
定理 cycleType_one
  结论: (1 : 置换 α).cycleType = 0
  证明: cycleType_eq_zero.2 rfl

Depends on / 依赖: cycleType_eq_zero
-/
theorem cycleType_one : (1 : Perm α).cycleType = 0 := cycleType_eq_zero.2 rfl

/--
theorem `card_cycleType_eq_zero` / 定理 `card_cycleType_eq_zero`

English:
theorem card_cycleType_eq_zero
  given: {σ : Perm α}
  statement: Multiset.card σ.cycleType = 0 ↔ σ = 1
  proof: by
  rw [card_eq_zero]; rw [cycleType_eq_zero]

中文:
定理 card_cycleType_eq_zero
  条件: {σ : 置换 α}
  结论: Multiset.card σ.cycleType = 0 ↔ σ = 1
  证明: by
  rw [card_eq_zero]; rw [cycleType_eq_zero]

Depends on / 依赖: card_eq_zero, cycleType_eq_zero
-/
theorem card_cycleType_eq_zero {σ : Perm α} : Multiset.card σ.cycleType = 0 ↔ σ = 1 := by
  rw [card_eq_zero]; rw [cycleType_eq_zero]

/--
theorem `card_cycleType_pos` / 定理 `card_cycleType_pos`

English:
theorem card_cycleType_pos
  given: {σ : Perm α}
  statement: 0 < Multiset.card σ.cycleType ↔ σ != 1
  proof: pos_iff_ne_zero.trans card_cycleType_eq_zero.not

中文:
定理 card_cycleType_pos
  条件: {σ : 置换 α}
  结论: 0 < Multiset.card σ.cycleType ↔ σ != 1
  证明: pos_iff_ne_zero.trans card_cycleType_eq_zero.not

Depends on / 依赖: card_cycleType_eq_zero, card_cycleType_eq_zero.not, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
theorem card_cycleType_pos {σ : Perm α} : 0 < Multiset.card σ.cycleType ↔ σ != 1 :=
  pos_iff_ne_zero.trans card_cycleType_eq_zero.not

/--
theorem `two_le_of_mem_cycleType` / 定理 `two_le_of_mem_cycleType`

English:
theorem two_le_of_mem_cycleType
  given: {σ : Perm α} {n : Nat} (h : n in σ.cycleType)
  statement: 2 <= n
  proof: by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support

中文:
定理 two_le_of_mem_cycleType
  条件: {σ : 置换 α} {n : 自然数} (h : n in σ.cycleType)
  结论: 2 <= n
  证明: by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support

Depends on / 依赖: Finset, Finset.mem_def, Function, Function.comp_apply, Multiset, Multiset.mem_map, comp_apply, cycleType_def, hc.two_le_card_support, mem_cycleFactorsFinset_iff, mem_def, mem_map, two_le_card_support
-/
theorem two_le_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : 2 <= n := by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support

/--
theorem `one_lt_of_mem_cycleType` / 定理 `one_lt_of_mem_cycleType`

English:
theorem one_lt_of_mem_cycleType
  given: {σ : Perm α} {n : Nat} (h : n in σ.cycleType)
  statement: 1 < n
  proof: two_le_of_mem_cycleType h

中文:
定理 one_lt_of_mem_cycleType
  条件: {σ : 置换 α} {n : 自然数} (h : n in σ.cycleType)
  结论: 1 < n
  证明: two_le_of_mem_cycleType h

Depends on / 依赖: two_le_of_mem_cycleType
-/
theorem one_lt_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : 1 < n :=
  two_le_of_mem_cycleType h

/--
theorem `IsCycle.cycleType` / 定理 `IsCycle.cycleType`

English:
theorem IsCycle.cycleType
  given: {σ : Perm α} (hσ : IsCycle σ)
  statement: σ.cycleType = {#σ.support}
  proof: cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)

中文:
定理 是环.cycleType
  条件: {σ : 置换 α} (hσ : 是环 σ)
  结论: σ.cycleType = {#σ.support}
  证明: cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)

Depends on / 依赖: Disjoint, IsCycle, List.mem_singleton.mp, List.pairwise_singleton, congr_arg, cycleType_eq, mem_singleton, mul_one, pairwise_singleton
-/
theorem IsCycle.cycleType {σ : Perm α} (hσ : IsCycle σ) : σ.cycleType = {#σ.support} :=
  cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)

/--
theorem `card_cycleType_eq_one` / 定理 `card_cycleType_eq_one`

English:
theorem card_cycleType_eq_one
  given: {σ : Perm α}
  statement: Multiset.card σ.cycleType = 1 ↔ σ.IsCycle
  proof: by
  rw [card_eq_one]
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  grind

中文:
定理 card_cycleType_eq_one
  条件: {σ : 置换 α}
  结论: Multiset.card σ.cycleType = 1 ↔ σ.是环
  证明: by
  rw [card_eq_one]
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  grind

Depends on / 依赖: Finset, Finset.singleton_val, Finset.val_inj, Multiset, Multiset.map_eq_singleton, card_eq_one, cycleFactorsFinset_eq_singleton_iff, cycleType_def, map_eq_singleton, simp_rw, singleton_val, val_inj
-/
theorem card_cycleType_eq_one {σ : Perm α} : Multiset.card σ.cycleType = 1 ↔ σ.IsCycle := by
  rw [card_eq_one]
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  grind

/--
theorem `Disjoint.cycleType_mul` / 定理 `Disjoint.cycleType_mul`

English:
theorem Disjoint.cycleType_mul
  given: {σ τ : Perm α} (h : Disjoint σ τ)
  proof: by
  rw [cycleType_def]; rw [cycleType_def]; rw [cycleType_def]; rw [h.cycleFactorsFinset_mul_eq_union]; rw [←
    Multiset.map_add]; rw [Finset.union_val]; rw [Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset

@[simp]

中文:
定理 Disjoint.cycleType_mul
  条件: {σ τ : 置换 α} (h : Disjoint σ τ)
  证明: by
  rw [cycleType_def]; rw [cycleType_def]; rw [cycleType_def]; rw [h.cycleFactorsFinset_mul_eq_union]; rw [←
    Multiset.map_add]; rw [Finset.union_val]; rw [Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset

@[simp]

Depends on / 依赖: Finset, Finset.disjoint_val, Finset.union_val, Multiset, Multiset.add_eq_union_iff_disjoint.mpr, Multiset.map_add, add_eq_union_iff_disjoint, cycleFactorsFinset_mul_eq_union, cycleType_def, disjoint_cycleFactorsFinset, disjoint_val, h.cycleFactorsFinset_mul_eq_union, h.disjoint_cycleFactorsFinset, map_add, union_val
-/
theorem Disjoint.cycleType_mul {σ τ : Perm α} (h : Disjoint σ τ) :
    (σ * τ).cycleType = σ.cycleType + τ.cycleType := by
  rw [cycleType_def]; rw [cycleType_def]; rw [cycleType_def]; rw [h.cycleFactorsFinset_mul_eq_union]; rw [←
    Multiset.map_add]; rw [Finset.union_val]; rw [Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset

@[simp]
/--
theorem `cycleType_inv` / 定理 `cycleType_inv`

English:
theorem cycleType_inv
  given: (σ : Perm α)
  statement: σ⁻¹.cycleType = σ.cycleType
  proof: cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType_mul, hστ.symm.inv_left.inv_right.cycleType_mul, hσ, hτ,
        add_comm]

@[simp]

中文:
定理 cycleType_inv
  条件: (σ : 置换 α)
  结论: σ⁻¹.cycleType = σ.cycleType
  证明: cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType_mul, hστ.symm.inv_left.inv_right.cycleType_mul, hσ, hτ,
        add_comm]

@[simp]

Depends on / 依赖: add_comm, cycleType, cycleType_mul, cycle_induction_on, inv.cycleType, inv_left, inv_right, mul_inv_rev, support_inv, symm.inv_left.inv_right.cycleType_mul
-/
theorem cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType :=
  cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType_mul, hστ.symm.inv_left.inv_right.cycleType_mul, hσ, hτ,
        add_comm]

@[simp]
/--
theorem `cycleType_conj` / 定理 `cycleType_conj`

English:
theorem cycleType_conj
  given: {σ τ : Perm α}
  statement: (τ * σ * τ⁻¹).cycleType = σ.cycleType
  proof: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul]; rw [hd.cycleType_mul]; rw [(hd.conj _).cycleType_mul]; rw [hσ]; rw [hπ]

中文:
定理 cycleType_conj
  条件: {σ τ : 置换 α}
  结论: (τ * σ * τ⁻¹).cycleType = σ.cycleType
  证明: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul]; rw [hd.cycleType_mul]; rw [(hd.conj _).cycleType_mul]; rw [hσ]; rw [hπ]

Depends on / 依赖: base_cycles, base_one, card_support_conj, conj.cycleType, conj_mul, cycleType, cycleType_mul, cycle_induction_on, hd.conj, hd.cycleType_mul, induction_disjoint
-/
theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul]; rw [hd.cycleType_mul]; rw [(hd.conj _).cycleType_mul]; rw [hσ]; rw [hπ]

/--
theorem `sum_cycleType` / 定理 `sum_cycleType`

English:
theorem sum_cycleType
  given: (σ : Perm α)
  statement: σ.cycleType.sum = #σ.support
  proof: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, Multiset.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType_mul, sum_add, hσ, hτ, hd.card_support_mul]

中文:
定理 sum_cycleType
  条件: (σ : 置换 α)
  结论: σ.cycleType.求和 = #σ.support
  证明: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, Multiset.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType_mul, sum_add, hσ, hτ, hd.card_support_mul]

Depends on / 依赖: Multiset, Multiset.sum_singleton, base_cycles, base_one, card_support_mul, cycleType, cycleType_mul, cycle_induction_on, hd.card_support_mul, hd.cycleType_mul, induction_disjoint, sum_add, sum_singleton
-/
theorem sum_cycleType (σ : Perm α) : σ.cycleType.sum = #σ.support := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, Multiset.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType_mul, sum_add, hσ, hτ, hd.card_support_mul]

/--
theorem `sum_cycleType_le` / 定理 `sum_cycleType_le`

English:
theorem sum_cycleType_le
  given: (σ : Perm α)
  statement: σ.cycleType.sum <= Fintype.card α
  proof: σ.sum_cycleType ▸ Finset.card_le_univ σ.support

中文:
定理 sum_cycleType_le
  条件: (σ : 置换 α)
  结论: σ.cycleType.求和 <= 有限类型.card α
  证明: σ.sum_cycleType ▸ Finset.card_le_univ σ.support

Depends on / 依赖: Finset, Finset.card_le_univ, card_le_univ, sum_cycleType, support
-/
theorem sum_cycleType_le (σ : Perm α) : σ.cycleType.sum <= Fintype.card α :=
  σ.sum_cycleType ▸ Finset.card_le_univ σ.support

/--
theorem `card_fixedPoints` / 定理 `card_fixedPoints`

English:
theorem card_fixedPoints
  given: (σ : Equiv.Perm α)
  proof: by
  rw [Equiv.Perm.sum_cycleType]; rw [← Finset.card_compl]; rw [Fintype.card_ofFinset]
  congr; aesop

中文:
定理 card_fixedPoints
  条件: (σ : 等价.置换 α)
  证明: by
  rw [Equiv.Perm.sum_cycleType]; rw [← Finset.card_compl]; rw [Fintype.card_ofFinset]
  congr; aesop

Depends on / 依赖: Equiv.Perm.sum_cycleType, Finset, Finset.card_compl, Fintype, Fintype.card_ofFinset, card_compl, card_ofFinset, sum_cycleType
-/
theorem card_fixedPoints (σ : Equiv.Perm α) :
    Fintype.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType]; rw [← Finset.card_compl]; rw [Fintype.card_ofFinset]
  congr; aesop

/--
theorem `sign_of_cycleType'` / 定理 `sign_of_cycleType'`

English:
theorem sign_of_cycleType'
  given: (σ : Perm α)
  proof: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType_mul]

中文:
定理 sign_of_cycleType'
  条件: (σ : 置换 α)
  证明: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType_mul]

Depends on / 依赖: base_cycles, base_one, cycleType, cycleType_mul, cycle_induction_on, hd.cycleType_mul, induction_disjoint
-/
theorem sign_of_cycleType' (σ : Perm α) :
    sign σ = (σ.cycleType.map fun n => -(-1 : Intˣ) ^ n).prod := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType_mul]

/--
theorem `sign_of_cycleType` / 定理 `sign_of_cycleType`

English:
theorem sign_of_cycleType
  given: (f : Perm α)
  proof: by
  rw [sign_of_cycleType']
  induction f.cycleType using Multiset.induction_on with
  | empty => rfl
  | cons a s ihs =>
    rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Multiset.sum_cons]; rw [Multiset.card_cons]; rw [ihs]
    simp only [pow_add, pow_one, neg_mul, mul_neg, mul_assoc, mul_one]

@[simp]

中文:
定理 sign_of_cycleType
  条件: (f : 置换 α)
  证明: by
  rw [sign_of_cycleType']
  induction f.cycleType using Multiset.induction_on with
  | empty => rfl
  | cons a s ihs =>
    rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Multiset.sum_cons]; rw [Multiset.card_cons]; rw [ihs]
    simp only [pow_add, pow_one, neg_mul, mul_neg, mul_assoc, mul_one]

@[simp]

Depends on / 依赖: Multiset, Multiset.card_cons, Multiset.induction_on, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, card_cons, cycleType, f.cycleType, induction_on, map_cons, mul_assoc, mul_neg, mul_one, neg_mul, pow_add, pow_one, prod_cons, sign_of_cycleType, sum_cons
-/
theorem sign_of_cycleType (f : Perm α) :
    sign f = (-1 : Intˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType) := by
  rw [sign_of_cycleType']
  induction f.cycleType using Multiset.induction_on with
  | empty => rfl
  | cons a s ihs =>
    rw [Multiset.map_cons]; rw [Multiset.prod_cons]; rw [Multiset.sum_cons]; rw [Multiset.card_cons]; rw [ihs]
    simp only [pow_add, pow_one, neg_mul, mul_neg, mul_assoc, mul_one]

@[simp]
/--
theorem `lcm_cycleType` / 定理 `lcm_cycleType`

English:
theorem lcm_cycleType
  given: (σ : Perm α)
  statement: σ.cycleType.lcm = orderOf σ
  proof: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType_mul, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]

中文:
定理 lcm_cycleType
  条件: (σ : 置换 α)
  结论: σ.cycleType.最小公倍数 = orderOf σ
  证明: by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType_mul, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]

Depends on / 依赖: base_cycles, base_one, cycleType, cycleType_mul, cycle_induction_on, hd.cycleType_mul, hd.orderOf, induction_disjoint, lcm_eq_nat_lcm, orderOf
-/
theorem lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType_mul, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]

/--
theorem `dvd_of_mem_cycleType` / 定理 `dvd_of_mem_cycleType`

English:
theorem dvd_of_mem_cycleType
  given: {σ : Perm α} {n : Nat} (h : n in σ.cycleType)
  statement: n ∣ orderOf σ
  proof: by
  rw [← lcm_cycleType]
  exact dvd_lcm h

中文:
定理 dvd_of_mem_cycleType
  条件: {σ : 置换 α} {n : 自然数} (h : n in σ.cycleType)
  结论: n ∣ orderOf σ
  证明: by
  rw [← lcm_cycleType]
  exact dvd_lcm h

Depends on / 依赖: dvd_lcm, lcm_cycleType
-/
theorem dvd_of_mem_cycleType {σ : Perm α} {n : Nat} (h : n in σ.cycleType) : n ∣ orderOf σ := by
  rw [← lcm_cycleType]
  exact dvd_lcm h

/--
theorem `orderOf_cycleOf_dvd_orderOf` / 定理 `orderOf_cycleOf_dvd_orderOf`

English:
theorem orderOf_cycleOf_dvd_orderOf
  given: (f : Perm α) (x : α)
  statement: orderOf (cycleOf f x) ∣ orderOf f
  proof: by
  by_cases hx : f x = x
  · rw [← cycleOf_eq_one_iff] at hx
    simp [hx]
  · refine dvd_of_mem_cycleType ?_
    rw [cycleType]; rw [Multiset.mem_map]
    refine ⟨f.cycleOf x, ?_, ?_⟩
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
    · simp [(isCycle_cycleOf _ hx).orderOf]

中文:
定理 orderOf_cycleOf_dvd_orderOf
  条件: (f : 置换 α) (x : α)
  结论: orderOf (cycleOf f x) ∣ orderOf f
  证明: by
  by_cases hx : f x = x
  · rw [← cycleOf_eq_one_iff] at hx
    simp [hx]
  · refine dvd_of_mem_cycleType ?_
    rw [cycleType]; rw [Multiset.mem_map]
    refine ⟨f.cycleOf x, ?_, ?_⟩
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
    · simp [(isCycle_cycleOf _ hx).orderOf]

Depends on / 依赖: Finset, Finset.mem_def, Multiset, Multiset.mem_map, cycleOf, cycleOf_eq_one_iff, cycleOf_mem_cycleFactorsFinset_iff, cycleType, dvd_of_mem_cycleType, f.cycleOf, isCycle_cycleOf, mem_def, mem_map, mem_support, orderOf
-/
theorem orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣ orderOf f := by
  by_cases hx : f x = x
  · rw [← cycleOf_eq_one_iff] at hx
    simp [hx]
  · refine dvd_of_mem_cycleType ?_
    rw [cycleType]; rw [Multiset.mem_map]
    refine ⟨f.cycleOf x, ?_, ?_⟩
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
    · simp [(isCycle_cycleOf _ hx).orderOf]

/--
theorem `two_dvd_card_support` / 定理 `two_dvd_card_support`

English:
theorem two_dvd_card_support
  given: {σ : Perm α} (hσ : σ ^ 2 = 1)
  statement: 2 ∣ #σ.support
  proof: (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [_root_.le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
(dvd_of_mem_cycleType hn).trans orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])

中文:
定理 two_dvd_card_support
  条件: {σ : 置换 α} (hσ : σ ^ 2 = 1)
  结论: 2 ∣ #σ.support
  证明: (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [_root_.le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
(dvd_of_mem_cycleType hn).trans orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])

Depends on / 依赖: Dvd.dvd, Multiset, Multiset.dvd_sum, Nat.le_of_dvd, _root_, _root_.le_antisymm, congr_arg, dvd_of_mem_cycleType, dvd_sum, le_antisymm, le_of_dvd, orderOf_dvd_of_pow_eq_one, sum_cycleType, two_le_of_mem_cycleType, zero_lt_two
-/
theorem two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ #σ.support :=
  (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [_root_.le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
(dvd_of_mem_cycleType hn).trans orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])

/--
theorem `cycleType_prime_order` / 定理 `cycleType_prime_order`

English:
theorem cycleType_prime_order
  given: {σ : Perm α} (hσ : (orderOf σ).Prime)
  proof: by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn => ?_⟩⟩
  · rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff]; rw [card_cycleType_pos]; rw [Ne]; rw [← orderOf_eq_one_iff]
    exact hσ.ne_one
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'

中文:
定理 cycleType_prime_order
  条件: {σ : 置换 α} (hσ : (orderOf σ).素)
  证明: by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn => ?_⟩⟩
  · rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff]; rw [card_cycleType_pos]; rw [Ne]; rw [← orderOf_eq_one_iff]
    exact hσ.ne_one
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'

Depends on / 依赖: Multiset, Multiset.card, Nat.succ_le_iff, card_cycleType_pos, cycleType, dvd_of_mem_cycleType, eq_one_or_self_of_dvd, eq_replicate, ne_one, one_lt_of_mem_cycleType, orderOf_eq_one_iff, resolve_left, succ_le_iff, tsub_add_cancel_of_le
-/
theorem cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) :
    exists n : Nat, σ.cycleType = Multiset.replicate (n + 1) (orderOf σ) := by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn => ?_⟩⟩
  · rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff]; rw [card_cycleType_pos]; rw [Ne]; rw [← orderOf_eq_one_iff]
    exact hσ.ne_one
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'

/--
theorem `pow_prime_eq_one_iff` / 定理 `pow_prime_eq_one_iff`

English:
theorem pow_prime_eq_one_iff
  given: {σ : Perm α} {p : Nat} [hp : Fact (Nat.Prime p)]
  proof: by
  rw [← orderOf_dvd_iff_pow_eq_one]; rw [← lcm_cycleType]; rw [Multiset.lcm_dvd]
  apply forall_congr'
  exact fun c => ⟨fun hc h => Or.resolve_left (hp.elim.eq_one_or_self_of_dvd c (hc h))
       (Nat.ne_of_lt' (one_lt_of_mem_cycleType h)),
     fun hc h => by rw [hc h]⟩

中文:
定理 pow_prime_eq_one_iff
  条件: {σ : 置换 α} {p : 自然数} [hp : Fact (自然数.素 p)]
  证明: by
  rw [← orderOf_dvd_iff_pow_eq_one]; rw [← lcm_cycleType]; rw [Multiset.lcm_dvd]
  apply forall_congr'
  exact fun c => ⟨fun hc h => Or.resolve_left (hp.elim.eq_one_or_self_of_dvd c (hc h))
       (Nat.ne_of_lt' (one_lt_of_mem_cycleType h)),
     fun hc h => by rw [hc h]⟩

Depends on / 依赖: Multiset, Multiset.lcm_dvd, Nat.ne_of_lt, Or.resolve_left, eq_one_or_self_of_dvd, forall_congr, hp.elim.eq_one_or_self_of_dvd, lcm_cycleType, lcm_dvd, ne_of_lt, one_lt_of_mem_cycleType, orderOf_dvd_iff_pow_eq_one, resolve_left
-/
theorem pow_prime_eq_one_iff {σ : Perm α} {p : Nat} [hp : Fact (Nat.Prime p)] :
    σ ^ p = 1 ↔ forall c in σ.cycleType, c = p := by
  rw [← orderOf_dvd_iff_pow_eq_one]; rw [← lcm_cycleType]; rw [Multiset.lcm_dvd]
  apply forall_congr'
  exact fun c => ⟨fun hc h => Or.resolve_left (hp.elim.eq_one_or_self_of_dvd c (hc h))
       (Nat.ne_of_lt' (one_lt_of_mem_cycleType h)),
     fun hc h => by rw [hc h]⟩

/--
theorem `cycleType_of_pow_prime_eq_one` / 定理 `cycleType_of_pow_prime_eq_one`

English:
theorem cycleType_of_pow_prime_eq_one
  given: {σ : Perm α} {p : Nat} [Fact (Nat.Prime p)] (hσ : σ ^ p = 1)
  proof: Multiset.eq_replicate.mpr ⟨rfl, pow_prime_eq_one_iff.mp hσ⟩

中文:
定理 cycleType_of_pow_prime_eq_one
  条件: {σ : 置换 α} {p : 自然数} [Fact (自然数.素 p)] (hσ : σ ^ p = 1)
  证明: Multiset.eq_replicate.mpr ⟨rfl, pow_prime_eq_one_iff.mp hσ⟩

Depends on / 依赖: Multiset, Multiset.eq_replicate.mpr, eq_replicate, pow_prime_eq_one_iff, pow_prime_eq_one_iff.mp
-/
theorem cycleType_of_pow_prime_eq_one {σ : Perm α} {p : Nat} [Fact (Nat.Prime p)] (hσ : σ ^ p = 1) :
    σ.cycleType = Multiset.replicate σ.cycleType.card p :=
  Multiset.eq_replicate.mpr ⟨rfl, pow_prime_eq_one_iff.mp hσ⟩

/--
theorem `isCycle_of_prime_order` / 定理 `isCycle_of_prime_order`

English:
theorem isCycle_of_prime_order
  statement: {σ : Perm α} (h1 : (orderOf σ).Prime)
  proof: by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  rw [← σ.sum_cycleType]; rw [hn]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]; rw [Nat.succ_lt_succ_iff]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero] at h2
  rw [← card_cycleType_eq_one]; rw [hn]; rw [card_replicate]; rw [h2]

中文:
定理 isCycle_of_prime_order
  结论: {σ : 置换 α} (h1 : (orderOf σ).素)
  证明: by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  rw [← σ.sum_cycleType]; rw [hn]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]; rw [Nat.succ_lt_succ_iff]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero] at h2
  rw [← card_cycleType_eq_one]; rw [hn]; rw [card_replicate]; rw [h2]

Depends on / 依赖: Multiset, Multiset.sum_replicate, Nat.cast_id, Nat.le_zero, Nat.lt_succ_iff, Nat.succ_lt_succ_iff, card_cycleType_eq_one, card_replicate, cast_id, cycleType_prime_order, le_zero, lt_succ_iff, nsmul_eq_mul, orderOf_pos, succ_lt_succ_iff, sum_cycleType, sum_replicate
-/
theorem isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : #σ.support < 2 * orderOf σ) : σ.IsCycle := by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  rw [← σ.sum_cycleType]; rw [hn]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]; rw [Nat.succ_lt_succ_iff]; rw [Nat.lt_succ_iff]; rw [Nat.le_zero] at h2
  rw [← card_cycleType_eq_one]; rw [hn]; rw [card_replicate]; rw [h2]

/--
theorem `cycleType_le_of_mem_cycleFactorsFinset` / 定理 `cycleType_le_of_mem_cycleFactorsFinset`

English:
theorem cycleType_le_of_mem_cycleFactorsFinset
  given: {f g : Perm α} (hf : f in g.cycleFactorsFinset)
  proof: by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  rw [cycleType_def]; rw [cycleType_def]; rw [hf'.left.cycleFactorsFinset_eq_singleton]
  refine map_le_map ?_
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf

中文:
定理 cycleType_le_of_mem_cycleFactorsFinset
  条件: {f g : 置换 α} (hf : f in g.cycleFactorsFinset)
  证明: by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  rw [cycleType_def]; rw [cycleType_def]; rw [hf'.left.cycleFactorsFinset_eq_singleton]
  refine map_le_map ?_
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf

Depends on / 依赖: Finset, Finset.mem_val, Finset.singleton_val, cycleFactorsFinset_eq_singleton, cycleType_def, left.cycleFactorsFinset_eq_singleton, map_le_map, mem_cycleFactorsFinset_iff, mem_val, singleton_le, singleton_val
-/
theorem cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f in g.cycleFactorsFinset) :
    f.cycleType <= g.cycleType := by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  rw [cycleType_def]; rw [cycleType_def]; rw [hf'.left.cycleFactorsFinset_eq_singleton]
  refine map_le_map ?_
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf

/--
theorem `Disjoint.cycleType_noncommProd` / 定理 `Disjoint.cycleType_noncommProd`

English:
theorem Disjoint.cycleType_noncommProd
  statement: {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.sum_insert hi]
    rw [Disjoint.cycleType_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

中文:
定理 Disjoint.cycleType_noncommProd
  结论: {ι : 类型} {k : ι -> 置换 α} {s : 有限集 ι}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.sum_insert hi]
    rw [Disjoint.cycleType_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

Depends on / 依赖: Disjoint, Disjoint.cycleType_mul, Finset, Finset.coe_insert, Finset.induction_on, Finset.noncommProd_insert_of_notMem, Finset.sum_insert, Pairwise, Perm.Disjoint.commute, Set.subset_insert, classical, coe_insert, commute, cycleType, cycleType_mul, disjoint_noncommProd_right, hs.imp, hs.mono, induction_on, insert
-/
theorem Disjoint.cycleType_noncommProd {ι : Type*} {k : ι -> Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j => Disjoint (k i) (k j))
    (hs' : Set.Pairwise s fun i j => Commute (k i) (k j) :=
      hs.imp (fun _ _ => Perm.Disjoint.commute)) :
    (s.noncommProd k hs').cycleType = s.sum fun i => (k i).cycleType := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j => Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi]; rw [Finset.sum_insert hi]
    rw [Disjoint.cycleType_mul]; rw [hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]


/--
theorem `cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub` / 定理 `cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub`

English:
theorem cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
  proof: add_right_cancel (b := f.cycleType) by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType_mul]; rw [inv_mul_cancel_right]; rw [tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]

中文:
定理 cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
  证明: add_right_cancel (b := f.cycleType) by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType_mul]; rw [inv_mul_cancel_right]; rw [tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]

Depends on / 依赖: add_right_cancel, cycleType, cycleType_le_of_mem_cycleFactorsFinset, cycleType_mul, disjoint_mul_inv_of_mem_cycleFactorsFinset, f.cycleType, inv_mul_cancel_right, tsub_add_cancel_of_le
-/
theorem cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
    {f g : Perm α} (hf : f in g.cycleFactorsFinset) :
    (g * f⁻¹).cycleType = g.cycleType - f.cycleType :=
add_right_cancel (b := f.cycleType) by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType_mul]; rw [inv_mul_cancel_right]; rw [tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]

/--
theorem `isConj_of_cycleType_eq` / 定理 `isConj_of_cycleType_eq`

English:
theorem isConj_of_cycleType_eq
  given: {σ τ : Perm α} (h : cycleType σ = cycleType τ)
  statement: IsConj σ τ
  proof: by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one]; rw [eq_comm]; rw [cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h]; rw [card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rwa [hσ.cycleType, hτ.cycleType, Multiset.singleton_inj] at h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType_mul] at h
    have h' : #σ.support in τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine IsConj.trans ?_ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def]; rw [mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType]; rw [← hσ']; rw [hσ'l.left.cycleType]; rfl
    refine hd.isConj_mul (hσ hs) (hπ ?_) ?_
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm

中文:
定理 isConj_of_cycleType_eq
  条件: {σ τ : 置换 α} (h : cycleType σ = cycleType τ)
  结论: IsConj σ τ
  证明: by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one]; rw [eq_comm]; rw [cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h]; rw [card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rwa [hσ.cycleType, hτ.cycleType, Multiset.singleton_inj] at h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType_mul] at h
    have h' : #σ.support in τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine IsConj.trans ?_ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def]; rw [mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType]; rw [← hσ']; rw [hσ'l.left.cycleType]; rfl
    refine hd.isConj_mul (hσ hs) (hπ ?_) ?_
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm

Depends on / 依赖: Multiset, Multiset.mem_ma, Multiset.singleton_inj, base_cycles, base_one, card_cycleType_eq_one, cycleType, cycleType_eq_zero, cycleType_mul, cycleType_one, cycle_induction_on, eq_comm, generalizing, hc.cycleType, hd.cycleType_mul, induction_disjoint, isConj, mem_ma, singleton_inj, support
-/
theorem isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : IsConj σ τ := by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one]; rw [eq_comm]; rw [cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h]; rw [card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rwa [hσ.cycleType, hτ.cycleType, Multiset.singleton_inj] at h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType_mul] at h
    have h' : #σ.support in τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine IsConj.trans ?_ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def]; rw [mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType]; rw [← hσ']; rw [hσ'l.left.cycleType]; rfl
    refine hd.isConj_mul (hσ hs) (hπ ?_) ?_
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm

/--
theorem `isConj_iff_cycleType_eq` / 定理 `isConj_iff_cycleType_eq`

English:
theorem isConj_iff_cycleType_eq
  given: {σ τ : Perm α}
  statement: IsConj σ τ ↔ σ.cycleType = τ.cycleType
  proof: ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycleType_conj], isConj_of_cycleType_eq⟩

@[simp]

中文:
定理 isConj_iff_cycleType_eq
  条件: {σ τ : 置换 α}
  结论: IsConj σ τ ↔ σ.cycleType = τ.cycleType
  证明: ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycleType_conj], isConj_of_cycleType_eq⟩

@[simp]

Depends on / 依赖: cycleType_conj, isConj_iff, isConj_of_cycleType_eq
-/
theorem isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycleType_conj], isConj_of_cycleType_eq⟩

@[simp]
/--
theorem `cycleType_extendDomain` / 定理 `cycleType_extendDomain`

English:
theorem cycleType_extendDomain
  statement: {β : Type*} [Fintype β] [DecidableEq β] {p : β -> Prop}
  proof: by
  induction g using cycle_induction_on with
  | base_one => rw [extendDomain_one, cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
    rw [(hσ.extendDomain f).cycleType]; rw [hσ.cycleType]; rw [card_support_extend_domain]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [hd.cycleType_mul]; rw [← extendDomain_mul]; rw [(hd.extendDomain f).cycleType_mul]; rw [hσ]; rw [hτ]

中文:
定理 cycleType_extendDomain
  结论: {β : 类型} [有限类型 β] [DecidableEq β] {p : β -> 命题}
  证明: by
  induction g using cycle_induction_on with
  | base_one => rw [extendDomain_one, cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
    rw [(hσ.extendDomain f).cycleType]; rw [hσ.cycleType]; rw [card_support_extend_domain]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [hd.cycleType_mul]; rw [← extendDomain_mul]; rw [(hd.extendDomain f).cycleType_mul]; rw [hσ]; rw [hτ]

Depends on / 依赖: base_cycles, base_one, card_support_extend_domain, cycleType, cycleType_mul, cycleType_one, cycle_induction_on, extendDomain, extendDomain_mul, extendDomain_one, hd.cycleType_mul, hd.extendDomain, induction_disjoint
-/
theorem cycleType_extendDomain {β : Type*} [Fintype β] [DecidableEq β] {p : β -> Prop}
    [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    cycleType (g.extendDomain f) = cycleType g := by
  induction g using cycle_induction_on with
  | base_one => rw [extendDomain_one, cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
    rw [(hσ.extendDomain f).cycleType]; rw [hσ.cycleType]; rw [card_support_extend_domain]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [hd.cycleType_mul]; rw [← extendDomain_mul]; rw [(hd.extendDomain f).cycleType_mul]; rw [hσ]; rw [hτ]

/--
theorem `cycleType_ofSubtype` / 定理 `cycleType_ofSubtype`

English:
theorem cycleType_ofSubtype
  statement: {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)]
  proof: cycleType_extendDomain (Equiv.refl (Subtype p))

中文:
定理 cycleType_ofSubtype
  结论: {p : α -> 命题} [DecidablePred p] [有限类型 (子类型 p)]
  证明: cycleType_extendDomain (Equiv.refl (Subtype p))

Depends on / 依赖: Equiv.refl, Subtype, cycleType_extendDomain
-/
theorem cycleType_ofSubtype {p : α -> Prop} [DecidablePred p] [Fintype (Subtype p)]
    {g : Perm (Subtype p)} :
    cycleType (ofSubtype g) = cycleType g :=
  cycleType_extendDomain (Equiv.refl (Subtype p))

/--
theorem `mem_cycleType_iff` / 定理 `mem_cycleType_iff`

English:
theorem mem_cycleType_iff
  given: {n : Nat} {σ : Perm α}
  proof: by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    rw [cycleType_eq _ rfl hlc hld]; rw [Multiset.mem_coe]; rw [List.mem_map] at h
    obtain ⟨c, cl, rfl⟩ := h
    rw [(List.perm_cons_erase cl).pairwise_iff symm] at hld
    refine ⟨c, (l.erase c).prod, ?_, ?_, hlc _ cl, rfl⟩
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycleType_mul, hc.cycleType]

中文:
定理 mem_cycleType_iff
  条件: {n : 自然数} {σ : 置换 α}
  证明: by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    rw [cycleType_eq _ rfl hlc hld]; rw [Multiset.mem_coe]; rw [List.mem_map] at h
    obtain ⟨c, cl, rfl⟩ := h
    rw [(List.perm_cons_erase cl).pairwise_iff symm] at hld
    refine ⟨c, (l.erase c).prod, ?_, ?_, hlc _ cl, rfl⟩
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycleType_mul, hc.cycleType]

Depends on / 依赖: Disjoint, Disjoint.commute, List.mem_map, List.perm_cons_erase, List.prod_cons, List.rel_of_pairwise_cons, Multiset, Multiset.mem_coe, commute, cycleType_, cycleType_eq, disjoint_prod_right, hd.cycleType_, hld.imp, l.erase, mem_coe, mem_map, pairwise_iff, perm_cons_erase, prod_cons
-/
theorem mem_cycleType_iff {n : Nat} {σ : Perm α} :
    n in cycleType σ ↔ exists c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n := by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    rw [cycleType_eq _ rfl hlc hld]; rw [Multiset.mem_coe]; rw [List.mem_map] at h
    obtain ⟨c, cl, rfl⟩ := h
    rw [(List.perm_cons_erase cl).pairwise_iff symm] at hld
    refine ⟨c, (l.erase c).prod, ?_, ?_, hlc _ cl, rfl⟩
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycleType_mul, hc.cycleType]

/--
theorem `le_card_support_of_mem_cycleType` / 定理 `le_card_support_of_mem_cycleType`

English:
theorem le_card_support_of_mem_cycleType
  given: {n : Nat} {σ : Perm α} (h : n in cycleType σ)
  proof: (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)

中文:
定理 le_card_support_of_mem_cycleType
  条件: {n : 自然数} {σ : 置换 α} (h : n in cycleType σ)
  证明: (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)

Depends on / 依赖: le_of_eq, le_sum_of_mem, sum_cycleType
-/
theorem le_card_support_of_mem_cycleType {n : Nat} {σ : Perm α} (h : n in cycleType σ) :
    n <= #σ.support :=
  (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)

/--
theorem `cycleType_of_card_le_mem_cycleType_add_two` / 定理 `cycleType_of_card_le_mem_cycleType_add_two`

English:
theorem cycleType_of_card_le_mem_cycleType_add_two
  statement: {n : Nat} {g : Perm α}
  proof: by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  suffices g'1 : g' = 1 by
    rw [hd.cycleType_mul]; rw [hc.cycleType]; rw [g'1]; rw [cycleType_one]; rw [add_zero]
  contrapose! hn2 with g'1
  grw [← (c * g').support.card_le_univ, hd.card_support_mul, two_le_card_support_of_ne_one g'1]

中文:
定理 cycleType_of_card_le_mem_cycleType_add_two
  结论: {n : 自然数} {g : 置换 α}
  证明: by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  suffices g'1 : g' = 1 by
    rw [hd.cycleType_mul]; rw [hc.cycleType]; rw [g'1]; rw [cycleType_one]; rw [add_zero]
  contrapose! hn2 with g'1
  grw [← (c * g').support.card_le_univ, hd.card_support_mul, two_le_card_support_of_ne_one g'1]

Depends on / 依赖: add_zero, card_le_univ, card_support_mul, contrapose, cycleType, cycleType_mul, cycleType_one, hc.cycleType, hd.card_support_mul, hd.cycleType_mul, mem_cycleType_iff, support, support.card_le_univ, two_le_card_support_of_ne_one
-/
theorem cycleType_of_card_le_mem_cycleType_add_two {n : Nat} {g : Perm α}
    (hn2 : Fintype.card α < n + 2) (hng : n in g.cycleType) : g.cycleType = {n} := by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  suffices g'1 : g' = 1 by
    rw [hd.cycleType_mul]; rw [hc.cycleType]; rw [g'1]; rw [cycleType_one]; rw [add_zero]
  contrapose! hn2 with g'1
  grw [← (c * g').support.card_le_univ, hd.card_support_mul, two_le_card_support_of_ne_one g'1]

/--
theorem `sign_of_cycleType_eq_replicate` / 定理 `sign_of_cycleType_eq_replicate`

English:
theorem sign_of_cycleType_eq_replicate
  statement: {σ : Perm α} {n : Nat} (hn : 0 < n)
  proof: by
  rw [sign_of_cycleType']; rw [hσ]; rw [Multiset.map_replicate]; rw [Multiset.prod_replicate]
  obtain h | h := Nat.even_or_odd n
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), h.neg_one_pow, σ.card_fixedPoints,
      Nat.sub_sub_self σ.sum_cycleType_le,
      show σ.cycleType.sum = σ.cycleType.card * n by rw [hσ]; simp,
        Nat.mul_div_cancel _ hn]
  · rw [if_pos h, h.neg_one_pow, neg_neg, one_pow]

中文:
定理 sign_of_cycleType_eq_replicate
  结论: {σ : 置换 α} {n : 自然数} (hn : 0 < n)
  证明: by
  rw [sign_of_cycleType']; rw [hσ]; rw [Multiset.map_replicate]; rw [Multiset.prod_replicate]
  obtain h | h := Nat.even_or_odd n
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), h.neg_one_pow, σ.card_fixedPoints,
      Nat.sub_sub_self σ.sum_cycleType_le,
      show σ.cycleType.sum = σ.cycleType.card * n by rw [hσ]; simp,
        Nat.mul_div_cancel _ hn]
  · rw [if_pos h, h.neg_one_pow, neg_neg, one_pow]

Depends on / 依赖: Multiset, Multiset.map_replicate, Multiset.prod_replicate, Nat.even_or_odd, Nat.mul_div_cancel, Nat.not_odd_iff_even.mpr, Nat.sub_sub_self, card_fixedPoints, cycleType, cycleType.card, cycleType.sum, even_or_odd, h.neg_one_pow, if_neg, if_pos, map_replicate, mul_div_cancel, neg_neg, neg_one_pow, not_odd_iff_even
-/
theorem sign_of_cycleType_eq_replicate {σ : Perm α} {n : Nat} (hn : 0 < n)
    (hσ : σ.cycleType = Multiset.replicate σ.cycleType.card n) :
    sign σ = if Odd n then 1 else
      (-1) ^ ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / n) := by
  rw [sign_of_cycleType']; rw [hσ]; rw [Multiset.map_replicate]; rw [Multiset.prod_replicate]
  obtain h | h := Nat.even_or_odd n
  · rw [if_neg (Nat.not_odd_iff_even.mpr h), h.neg_one_pow, σ.card_fixedPoints,
      Nat.sub_sub_self σ.sum_cycleType_le,
      show σ.cycleType.sum = σ.cycleType.card * n by rw [hσ]; simp,
        Nat.mul_div_cancel _ hn]
  · rw [if_pos h, h.neg_one_pow, neg_neg, one_pow]

/--
theorem `sign_of_pow_two_eq_one` / 定理 `sign_of_pow_two_eq_one`

English:
theorem sign_of_pow_two_eq_one
  given: {σ : Perm α} (hσ : σ ^ 2 = 1)
  proof: by
  rw [sign_of_cycleType_eq_replicate zero_lt_two (cycleType_of_pow_prime_eq_one hσ)]; rw [if_neg (Nat.not_odd_iff.mpr rfl)]

中文:
定理 sign_of_pow_two_eq_one
  条件: {σ : 置换 α} (hσ : σ ^ 2 = 1)
  证明: by
  rw [sign_of_cycleType_eq_replicate zero_lt_two (cycleType_of_pow_prime_eq_one hσ)]; rw [if_neg (Nat.not_odd_iff.mpr rfl)]

Depends on / 依赖: Nat.not_odd_iff.mpr, cycleType_of_pow_prime_eq_one, if_neg, not_odd_iff, sign_of_cycleType_eq_replicate, zero_lt_two
-/
theorem sign_of_pow_two_eq_one {σ : Perm α} (hσ : σ ^ 2 = 1) :
    sign σ = (-1) ^ ((Fintype.card α - Fintype.card (Function.fixedPoints σ)) / 2) := by
  rw [sign_of_cycleType_eq_replicate zero_lt_two (cycleType_of_pow_prime_eq_one hσ)]; rw [if_neg (Nat.not_odd_iff.mpr rfl)]

end CycleType

/--
theorem `card_compl_support_modEq` / 定理 `card_compl_support_modEq`

English:
theorem card_compl_support_modEq
  statement: [DecidableEq α] {p n : Nat} [hp : Fact p.Prime] {σ : Perm α}
  proof: by
  rw [Nat.modEq_iff_dvd']; rw [← Finset.card_compl]; rw [compl_compl]; rw [← sum_cycleType]
  · refine Multiset.dvd_sum fun k hk => ?_
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne by rw [h, pow_zero]
  · exact Finset.card_le_univ _

中文:
定理 card_compl_support_modEq
  结论: [DecidableEq α] {p n : 自然数} [hp : Fact p.素] {σ : 置换 α}
  证明: by
  rw [Nat.modEq_iff_dvd']; rw [← Finset.card_compl]; rw [compl_compl]; rw [← sum_cycleType]
  · refine Multiset.dvd_sum fun k hk => ?_
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne by rw [h, pow_zero]
  · exact Finset.card_le_univ _

Depends on / 依赖: Finset, Finset.card_compl, Finset.card_le_univ, Multiset, Multiset.dvd_sum, Nat.dvd_prime_pow, Nat.modEq_iff_dvd, card_compl, card_le_univ, compl_compl, congr_arg, dvd_of_mem_cycleType, dvd_pow_self, dvd_prime_pow, dvd_sum, hp.out, modEq_iff_dvd, one_lt_of_mem_cycleType, orderOf_dvd_of_pow_eq_one, pow_zero
-/
theorem card_compl_support_modEq [DecidableEq α] {p n : Nat} [hp : Fact p.Prime] {σ : Perm α}
    (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p] := by
  rw [Nat.modEq_iff_dvd']; rw [← Finset.card_compl]; rw [compl_compl]; rw [← sum_cycleType]
  · refine Multiset.dvd_sum fun k hk => ?_
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne by rw [h, pow_zero]
  · exact Finset.card_le_univ _

set_option backward.isDefEq.respectTransparency false in
open Function in
/--
theorem `card_fixedPoints_modEq` / 定理 `card_fixedPoints_modEq`

English:
theorem card_fixedPoints_modEq
  statement: [DecidableEq α] {f : Function.End α} {p n : Nat}
  proof: by
  let σ : α ≃ α := ⟨f, f ^ (p ^ n - 1),
    leftInverse_iff_comp.mpr ((pow_sub_mul_pow f (Nat.one_le_pow n p hp.out.pos)).trans hf),
    leftInverse_iff_comp.mpr ((pow_mul_pow_sub f (Nat.one_le_pow n p hp.out.pos)).trans hf)⟩
  have hσ : σ ^ p ^ n = 1 := by
    rw [DFunLike.ext'_iff]; rw [coe_pow]
    exact (hom_coe_pow (fun g : Function.End α => g) rfl (fun g h => rfl) f (p ^ n)).symm.trans hf
  suffices Fintype.card f.fixedPoints = (support σ)ᶜ.card from
    this ▸ (card_compl_support_modEq hσ).symm
  suffices f.fixedPoints = (support σ)ᶜ by
    simp only [this]; apply Fintype.card_coe
  simp [σ, Set.ext_iff, IsFixedPt]

中文:
定理 card_fixedPoints_modEq
  结论: [DecidableEq α] {f : 函数.End α} {p n : 自然数}
  证明: by
  let σ : α ≃ α := ⟨f, f ^ (p ^ n - 1),
    leftInverse_iff_comp.mpr ((pow_sub_mul_pow f (Nat.one_le_pow n p hp.out.pos)).trans hf),
    leftInverse_iff_comp.mpr ((pow_mul_pow_sub f (Nat.one_le_pow n p hp.out.pos)).trans hf)⟩
  have hσ : σ ^ p ^ n = 1 := by
    rw [DFunLike.ext'_iff]; rw [coe_pow]
    exact (hom_coe_pow (fun g : Function.End α => g) rfl (fun g h => rfl) f (p ^ n)).symm.trans hf
  suffices Fintype.card f.fixedPoints = (support σ)ᶜ.card from
    this ▸ (card_compl_support_modEq hσ).symm
  suffices f.fixedPoints = (support σ)ᶜ by
    simp only [this]; apply Fintype.card_coe
  simp [σ, Set.ext_iff, IsFixedPt]

Depends on / 依赖: DFunLike, DFunLike.ext, Fintype, Fintype.card, Function, Function.End, Nat.one_le_pow, _iff, card_compl_support_modEq, coe_pow, f.fixed, f.fixedPoints, fixedPoints, hom_coe_pow, hp.out.pos, leftInverse_iff_comp, leftInverse_iff_comp.mpr, one_le_pow, pow_mul_pow_sub, pow_sub_mul_pow
-/
theorem card_fixedPoints_modEq [DecidableEq α] {f : Function.End α} {p n : Nat}
    [hp : Fact p.Prime] (hf : f ^ p ^ n = 1) :
    Fintype.card α ≡ Fintype.card f.fixedPoints [MOD p] := by
  let σ : α ≃ α := ⟨f, f ^ (p ^ n - 1),
    leftInverse_iff_comp.mpr ((pow_sub_mul_pow f (Nat.one_le_pow n p hp.out.pos)).trans hf),
    leftInverse_iff_comp.mpr ((pow_mul_pow_sub f (Nat.one_le_pow n p hp.out.pos)).trans hf)⟩
  have hσ : σ ^ p ^ n = 1 := by
    rw [DFunLike.ext'_iff]; rw [coe_pow]
    exact (hom_coe_pow (fun g : Function.End α => g) rfl (fun g h => rfl) f (p ^ n)).symm.trans hf
  suffices Fintype.card f.fixedPoints = (support σ)ᶜ.card from
    this ▸ (card_compl_support_modEq hσ).symm
  suffices f.fixedPoints = (support σ)ᶜ by
    simp only [this]; apply Fintype.card_coe
  simp [σ, Set.ext_iff, IsFixedPt]

/--
theorem `exists_fixed_point_of_prime` / 定理 `exists_fixed_point_of_prime`

English:
theorem exists_fixed_point_of_prime
  statement: {p n : Nat} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
  proof: by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)

中文:
定理 存在_fixed_point_of_prime
  结论: {p n : 自然数} [hp : Fact p.素] (hα : ¬p ∣ 有限类型.card α)
  证明: by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)

Depends on / 依赖: Finset, Finset.card_eq_zero, Finset.eq_univ_iff_forall, Nat.modEq_zero_iff_dvd, card_compl_support_modEq, card_eq_zero, classical, compl_eq_bot, congr_arg, contrapose, eq_univ_iff_forall, mem_support, modEq_zero_iff_dvd, simp_rw
-/
theorem exists_fixed_point_of_prime {p n : Nat} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) : exists a : α, σ a = a := by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)

/--
theorem `exists_fixed_point_of_prime'` / 定理 `exists_fixed_point_of_prime'`

English:
theorem exists_fixed_point_of_prime'
  statement: {p n : Nat} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
  proof: by
  classical
    have h : forall b : α, b in σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl]; rw [mem_support]; rw [Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_mem_ne (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩

中文:
定理 存在_fixed_point_of_prime'
  结论: {p n : 自然数} [hp : Fact p.素] (hα : p ∣ 有限类型.card α)
  证明: by
  classical
    have h : forall b : α, b in σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl]; rw [mem_support]; rw [Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_mem_ne (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.card_pos.mpr, Finset.exists_mem_ne, Finset.mem_compl, Nat.le_of_dvd, Nat.modEq_zero_iff_dvd.mp, Nat.modEq_zero_iff_dvd.mpr, card_compl_support_modEq, card_pos, classical, exists_mem_ne, hp.out.one_lt.trans_le, le_of_dvd, mem_compl, mem_support, modEq_zero_iff_dvd, not_not, one_lt
-/
theorem exists_fixed_point_of_prime' {p n : Nat} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : exists b : α, σ b = b ∧ b != a := by
  classical
    have h : forall b : α, b in σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl]; rw [mem_support]; rw [Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_mem_ne (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩

/--
theorem `isCycle_of_prime_order'` / 定理 `isCycle_of_prime_order'`

English:
theorem isCycle_of_prime_order'
  statement: {σ : Perm α} (h1 : (orderOf σ).Prime)
  proof: by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)

中文:
定理 isCycle_of_prime_order'
  结论: {σ : 置换 α} (h1 : (orderOf σ).素)
  证明: by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)

Depends on / 依赖: card_le_univ, classical, isCycle_of_prime_order, lt_of_le_of_lt, support, support.card_le_univ
-/
theorem isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle := by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)

/--
theorem `isCycle_of_prime_order''` / 定理 `isCycle_of_prime_order''`

English:
theorem isCycle_of_prime_order''
  statement: {σ : Perm α} (h1 : (Fintype.card α).Prime)
  proof: isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) by
    rw [← one_mul (Fintype.card α)]; rw [← h2]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]
    exact one_lt_two

中文:
定理 isCycle_of_prime_order''
  结论: {σ : 置换 α} (h1 : (有限类型.card α).素)
  证明: isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) by
    rw [← one_mul (Fintype.card α)]; rw [← h2]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]
    exact one_lt_two

Depends on / 依赖: Fintype, Fintype.card, Nat.Prime, congr_arg, isCycle_of_prime_order, one_lt_two, one_mul, orderOf_pos
-/
theorem isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime)
    (h2 : orderOf σ = Fintype.card α) : σ.IsCycle :=
isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) by
    rw [← one_mul (Fintype.card α)]; rw [← h2]; rw [mul_lt_mul_iff_left₀ (orderOf_pos σ)]
    exact one_lt_two

section Cauchy

variable (G : Type*) [Group G] (n : Nat)

/--
Definition of `vectorsProdEqOne` / `vectorsProdEqOne` 的定义

English:
definition vectorsProdEqOne
  signature: : Set (List.Vector G n)
  body: { v | v.toList.prod = 1 }

中文:
定义 vectorsProdEqOne
  签名: : 集合 (列表.Vector G n)
  定义体: { v | v.toList.prod = 1 }

Depends on / 依赖: toList, v.toList.prod
-/
def vectorsProdEqOne : Set (List.Vector G n) :=
  { v | v.toList.prod = 1 }

namespace VectorsProdEqOne

/--
theorem `mem_iff` / 定理 `mem_iff`

English:
theorem mem_iff
  given: {n : Nat} (v : List.Vector G n)
  statement: v in vectorsProdEqOne G n ↔ v.toList.prod = 1
  proof: Iff.rfl

中文:
定理 mem_iff
  条件: {n : 自然数} (v : 列表.Vector G n)
  结论: v in vectorsProdEqOne G n ↔ v.toList.乘积 = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl, Shrink, Shrink.linearEquiv, TensorProduct, TensorProduct.congr, linearEquiv, symm.toEquiv, toEquiv
-/
theorem mem_iff {n : Nat} (v : List.Vector G n) : v in vectorsProdEqOne G n ↔ v.toList.prod = 1 :=
  Iff.rfl

/--
theorem `zero_eq` / 定理 `zero_eq`

English:
theorem zero_eq
  statement: vectorsProdEqOne G 0 = {Vector.nil}
  proof: Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩

中文:
定理 zero_eq
  结论: vectorsProdEqOne G 0 = {Vector.nil}
  证明: Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩

Depends on / 依赖: Eq.refl, Set.eq_singleton_iff_unique_mem.mpr, eq_nil, eq_singleton_iff_unique_mem, v.eq_nil
-/
theorem zero_eq : vectorsProdEqOne G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩

/--
theorem `one_eq` / 定理 `one_eq`

English:
theorem one_eq
  statement: vectorsProdEqOne G 1 = {Vector.nil.cons 1}
  proof: by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, List.Vector.toList_singleton,
    List.prod_singleton, List.Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)

中文:
定理 one_eq
  结论: vectorsProdEqOne G 1 = {Vector.nil.cons 1}
  证明: by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, List.Vector.toList_singleton,
    List.prod_singleton, List.Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)

Depends on / 依赖: List.Vector.head_cons, List.Vector.toList_singleton, List.prod_singleton, Set.eq_singleton_iff_unique_mem, Vector, Vector.cons, cons_head_tail, eq_nil, eq_singleton_iff_unique_mem, head_cons, mem_iff, prod_singleton, simp_rw, toList_singleton, true_and, v.cons_head_tail.symm.trans, v.tail.eq_nil
-/
theorem one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1} := by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, List.Vector.toList_singleton,
    List.prod_singleton, List.Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)

/--
Instance `zeroUnique` / 实例 `zeroUnique`

English:
instance zeroUnique
  signature: : Unique (vectorsProdEqOne G 0)
  body: by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil

中文:
实例 zeroUnique
  签名: : 唯一 (vectorsProdEqOne G 0)
  定义体: by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil

Depends on / 依赖: Set.uniqueSingleton, Vector, Vector.nil, uniqueSingleton, zero_eq
-/
instance zeroUnique : Unique (vectorsProdEqOne G 0) := by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil

/--
Instance `oneUnique` / 实例 `oneUnique`

English:
instance oneUnique
  signature: : Unique (vectorsProdEqOne G 1)
  body: by
  rw [one_eq]
  exact Set.uniqueSingleton (Vector.nil.cons 1)

中文:
实例 oneUnique
  签名: : 唯一 (vectorsProdEqOne G 1)
  定义体: by
  rw [one_eq]
  exact Set.uniqueSingleton (Vector.nil.cons 1)

Depends on / 依赖: Set.uniqueSingleton, Vector, Vector.nil.cons, one_eq, uniqueSingleton
-/
instance oneUnique : Unique (vectorsProdEqOne G 1) := by
  rw [one_eq]
  exact Set.uniqueSingleton (Vector.nil.cons 1)

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
/--
Definition of `vectorEquiv` / `vectorEquiv` 的定义

English:
definition vectorEquiv
  signature: : List.Vector G n ≃ vectorsProdEqOne G (n + 1) where
  body: ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff]; rw [Vector.toList_cons]; rw [List.prod_cons]; rw [inv_mul_cancel]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
right_inv v := Subtype.ext
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
congr_arg (· ::ᵥ v.1.tail) Eq.symm eq_inv_of_mul_eq_one_left by
          rw [← List.prod_cons]; rw [← Vector.toList_cons]; rw [v.1.cons_head_tail]
          exact v.2
      _ = v.1 := v.1.cons_head_tail

中文:
定义 vectorEquiv
  签名: : 列表.Vector G n ≃ vectorsProdEqOne G (n + 1) where
  定义体: ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff]; rw [Vector.toList_cons]; rw [List.prod_cons]; rw [inv_mul_cancel]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
right_inv v := Subtype.ext
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
congr_arg (· ::ᵥ v.1.tail) Eq.symm eq_inv_of_mul_eq_one_left by
          rw [← List.prod_cons]; rw [← Vector.toList_cons]; rw [v.1.cons_head_tail]
          exact v.2
      _ = v.1 := v.1.cons_head_tail

Depends on / 依赖: Eq.symm, List.prod_cons, Subtype, Subtype.ext, Vector, Vector.toList_cons, congr_arg, cons_head_tail, eq_inv_of_mul_eq_one_left, invFun, inv_mul_cancel, left_inv, mem_iff, prod_cons, right_inv, tail.toList.prod, tail_cons, toList, toList_cons, v.tail_cons
-/
def vectorEquiv : List.Vector G n ≃ vectorsProdEqOne G (n + 1) where
  toFun v := ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff]; rw [Vector.toList_cons]; rw [List.prod_cons]; rw [inv_mul_cancel]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
right_inv v := Subtype.ext
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
congr_arg (· ::ᵥ v.1.tail) Eq.symm eq_inv_of_mul_eq_one_left by
          rw [← List.prod_cons]; rw [← Vector.toList_cons]; rw [v.1.cons_head_tail]
          exact v.2
      _ = v.1 := v.1.cons_head_tail

/--
Definition of `equivVector` / `equivVector` 的定义

English:
definition equivVector
  signature: : forall n, vectorsProdEqOne G n ≃ List.Vector G (n - 1)

中文:
定义 equivVector
  签名: : 对任意 n, vectorsProdEqOne G n ≃ 列表.Vector G (n - 1)
-/
def equivVector : forall n, vectorsProdEqOne G n ≃ List.Vector G (n - 1)
  | 0 => (ofUnique (vectorsProdEqOne G 0) (vectorsProdEqOne G 1)).trans (vectorEquiv G 0).symm
  | (n + 1) => (vectorEquiv G n).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: G] : Fintype (vectorsProdEqOne G n)
  body: Fintype.ofEquiv (List.Vector G (n - 1)) (equivVector G n).symm

中文:
实例 [有限类型
  签名: G] : 有限类型 (vectorsProdEqOne G n)
  定义体: Fintype.ofEquiv (List.Vector G (n - 1)) (equivVector G n).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, List.Vector, Vector, equivVector, ofEquiv
-/
instance [Fintype G] : Fintype (vectorsProdEqOne G n) :=
  Fintype.ofEquiv (List.Vector G (n - 1)) (equivVector G n).symm

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: [Fintype G]
  statement: Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1)
  proof: (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))

中文:
定理 card
  条件: [有限类型 G]
  结论: 有限类型.card (vectorsProdEqOne G n) = 有限类型.card G ^ (n - 1)
  证明: (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, card_vector, equivVector
-/
theorem card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1) :=
  (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))

variable {G n} {g : G}
variable (v : vectorsProdEqOne G n) (j k : Nat)

/--
Definition of `rotate` / `rotate` 的定义

English:
definition rotate
  signature: : vectorsProdEqOne G n
  body: ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

中文:
定义 rotate
  签名: : vectorsProdEqOne G n
  定义体: ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

Depends on / 依赖: List.prod_rotate_eq_one_of_prod_eq_one, length_rotate, prod_rotate_eq_one_of_prod_eq_one
-/
def rotate : vectorsProdEqOne G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

/--
theorem `rotate_zero` / 定理 `rotate_zero`

English:
theorem rotate_zero
  statement: rotate v 0 = v
  proof: Subtype.ext (Subtype.ext v.1.1.rotate_zero)

中文:
定理 rotate_zero
  结论: rotate v 0 = v
  证明: Subtype.ext (Subtype.ext v.1.1.rotate_zero)

Depends on / 依赖: Subtype, Subtype.ext, rotate_zero
-/
theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)

/--
theorem `rotate_rotate` / 定理 `rotate_rotate`

English:
theorem rotate_rotate
  statement: rotate (rotate v j) k = rotate v (j + k)
  proof: Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))

中文:
定理 rotate_rotate
  结论: rotate (rotate v j) k = rotate v (j + k)
  证明: Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))

Depends on / 依赖: Subtype, Subtype.ext, rotate_rotate
-/
theorem rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))

/--
theorem `rotate_length` / 定理 `rotate_length`

English:
theorem rotate_length
  statement: rotate v n = v
  proof: Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

中文:
定理 rotate_length
  结论: rotate v n = v
  证明: Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, rotate_length
-/
theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

end VectorsProdEqOne

set_option backward.isDefEq.respectTransparency false in
-- TODO: Make the `Finite` version of this theorem the default
/--
theorem `_root_.exists_prime_orderOf_dvd_card` / 定理 `_root_.exists_prime_orderOf_dvd_card`

English:
theorem _root_.exists_prime_orderOf_dvd_card
  statement: {G : Type*} [Group G] [Fintype G] (p : Nat)
  proof: by
  have hp' : p - 1 != 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_gt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : Nat -> vectorsProdEqOne G p -> vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : forall v, f 0 v = v := VectorsProdEqOne.rotate_zero
  have hf2 : forall j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : forall v, f p v = v := VectorsProdEqOne.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : forall k v, (σ ^ k) v = f k v := fun k =>
    Nat.rec (fun v => (hf1 v).symm) (fun k hk v => by
      rw [pow_succ]; rw [Perm.mul_apply]; rw [hk (σ v)]; rw [Nat.succ_eq_one_add]; rw [← hf2 1 k]
      simp only [σ, coe_fn_mk]) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectorsProdEqOne G p :=
    ⟨List.Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine
    Exists.imp (fun g hg => orderOf_eq_prime ?_ fun hg' => hv2 ?_)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff, Subtype.ext_iff, hg, hg', v.1.2]
    simp only [v₀, List.Vector.replicate]

中文:
定理 _root_.存在_prime_orderOf_dvd_card
  结论: {G : 类型} [群 G] [有限类型 G] (p : 自然数)
  证明: by
  have hp' : p - 1 != 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_gt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : Nat -> vectorsProdEqOne G p -> vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : forall v, f 0 v = v := VectorsProdEqOne.rotate_zero
  have hf2 : forall j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : forall v, f p v = v := VectorsProdEqOne.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : forall k v, (σ ^ k) v = f k v := fun k =>
    Nat.rec (fun v => (hf1 v).symm) (fun k hk v => by
      rw [pow_succ]; rw [Perm.mul_apply]; rw [hk (σ v)]; rw [Nat.succ_eq_one_add]; rw [← hf2 1 k]
      simp only [σ, coe_fn_mk]) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectorsProdEqOne G p :=
    ⟨List.Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine
    Exists.imp (fun g hg => orderOf_eq_prime ?_ fun hg' => hv2 ?_)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff, Subtype.ext_iff, hg, hg', v.1.2]
    simp only [v₀, List.Vector.replicate]

Depends on / 依赖: Fintype, Fintype.card, VectorsProdEqOne, VectorsProdEqOne.card, VectorsProdEqOne.rot, VectorsProdEqOne.rotate, VectorsProdEqOne.rotate_zero, dvd_pow, dvd_refl, hdvd.trans, hp.out.one_lt, not_le_of_gt, one_lt, rotate, rotate_zero, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mp, vectorsProdEqOne
-/
theorem _root_.exists_prime_orderOf_dvd_card {G : Type*} [Group G] [Fintype G] (p : Nat)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : exists x : G, orderOf x = p := by
  have hp' : p - 1 != 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_gt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : Nat -> vectorsProdEqOne G p -> vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : forall v, f 0 v = v := VectorsProdEqOne.rotate_zero
  have hf2 : forall j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : forall v, f p v = v := VectorsProdEqOne.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : forall k v, (σ ^ k) v = f k v := fun k =>
    Nat.rec (fun v => (hf1 v).symm) (fun k hk v => by
      rw [pow_succ]; rw [Perm.mul_apply]; rw [hk (σ v)]; rw [Nat.succ_eq_one_add]; rw [← hf2 1 k]
      simp only [σ, coe_fn_mk]) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectorsProdEqOne G p :=
    ⟨List.Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine
    Exists.imp (fun g hg => orderOf_eq_prime ?_ fun hg' => hv2 ?_)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff, Subtype.ext_iff, hg, hg', v.1.2]
    simp only [v₀, List.Vector.replicate]

-- TODO: Make the `Finite` version of this theorem the default
/--
theorem `_root_.exists_prime_addOrderOf_dvd_card` / 定理 `_root_.exists_prime_addOrderOf_dvd_card`

English:
theorem _root_.exists_prime_addOrderOf_dvd_card
  statement: {G : Type*} [AddGroup G] [Fintype G] (p : Nat)
  proof: @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert! hdvd)

中文:
定理 _root_.存在_prime_addOrderOf_dvd_card
  结论: {G : 类型} [加法群 G] [有限类型 G] (p : 自然数)
  证明: @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert! hdvd)

Depends on / 依赖: Multiplicative, convert, exists_prime_orderOf_dvd_card
-/
theorem _root_.exists_prime_addOrderOf_dvd_card {G : Type*} [AddGroup G] [Fintype G] (p : Nat)
    [Fact p.Prime] (hdvd : p ∣ Fintype.card G) : exists x : G, addOrderOf x = p :=
  @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert! hdvd)

attribute [to_additive existing] exists_prime_orderOf_dvd_card

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
@[to_additive]
/--
theorem `_root_.exists_prime_orderOf_dvd_card'` / 定理 `_root_.exists_prime_orderOf_dvd_card'`

English:
theorem _root_.exists_prime_orderOf_dvd_card'
  statement: {G : Type*} [Group G] [Finite G] (p : Nat)
  proof: by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

中文:
定理 _root_.存在_prime_orderOf_dvd_card'
  结论: {G : 类型} [群 G] [有限 G] (p : 自然数)
  证明: by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, exists_prime_orderOf_dvd_card, ofFinite
-/
theorem _root_.exists_prime_orderOf_dvd_card' {G : Type*} [Group G] [Finite G] (p : Nat)
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) : exists x : G, orderOf x = p := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

end Cauchy

/--
theorem `subgroup_eq_top_of_swap_mem` / 定理 `subgroup_eq_top_of_swap_mem`

English:
theorem subgroup_eq_top_of_swap_mem
  statement: [DecidableEq α] {H : Subgroup (Perm α)}
  proof: by
  have : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff]; rw [← hσ4]; rw [Subgroup.closure_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩

中文:
定理 subgroup_eq_top_of_swap_mem
  结论: [DecidableEq α] {H : 子群 (置换 α)}
  证明: by
  have : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff]; rw [← hσ4]; rw [Subgroup.closure_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩

Depends on / 依赖: Finset, Finset.eq_univ_of_card, Fintype, Fintype.card, IsCycle, Subgroup, Subgroup.closure, Subgroup.orderOf_coe, closure, closure_prime_cycle_swap, eq_top_iff, eq_univ_of_card, exists_prime_orderOf_dvd_card, isCycle_of_prime_order, orderOf, orderOf.symm.trans, orderOf_coe, support
-/
theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)}
    [d : DecidablePred (· in H)] {τ : Perm α} (h0 : (Fintype.card α).Prime)
    (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ in H) (h3 : IsSwap τ) : H = ⊤ := by
  have : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff]; rw [← hσ4]; rw [Subgroup.closure_le]; rw [Set.insert_subset_iff]; rw [Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩

section Partition

variable [DecidableEq α]

/--
Definition of `partition` / `partition` 的定义

English:
definition partition
  signature: (σ : Perm α)
  body: σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
  parts_pos {n hn} := by
    rcases mem_add.mp hn with hn | hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add]; rw [sum_cycleType]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]; rw [add_tsub_cancel_of_le σ.support.card_le_univ]

中文:
定义 partition
  签名: (σ : 置换 α)
  定义体: σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
  parts_pos {n hn} := by
    rcases mem_add.mp hn with hn | hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add]; rw [sum_cycleType]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]; rw [add_tsub_cancel_of_le σ.support.card_le_univ]

Depends on / 依赖: Fintype, Fintype.card, Multiset, Multiset.replicate, cycleType, replicate, support
-/
def partition (σ : Perm α) : (Fintype.card α).Partition where
  parts := σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
  parts_pos {n hn} := by
    rcases mem_add.mp hn with hn | hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add]; rw [sum_cycleType]; rw [Multiset.sum_replicate]; rw [nsmul_eq_mul]; rw [Nat.cast_id]; rw [mul_one]; rw [add_tsub_cancel_of_le σ.support.card_le_univ]

/--
theorem `parts_partition` / 定理 `parts_partition`

English:
theorem parts_partition
  given: {σ : Perm α}
  proof: rfl

中文:
定理 parts_partition
  条件: {σ : 置换 α}
  证明: rfl
-/
theorem parts_partition {σ : Perm α} :
    σ.partition.parts = σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1 :=
  rfl

/--
theorem `filter_parts_partition_eq_cycleType` / 定理 `filter_parts_partition_eq_cycleType`

English:
theorem filter_parts_partition_eq_cycleType
  given: {σ : Perm α}
  proof: by
  rw [parts_partition]; rw [filter_add]; rw [Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType]; rw [Multiset.filter_eq_nil.2 fun a h => ?_]; rw [add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

中文:
定理 filter_parts_partition_eq_cycleType
  条件: {σ : 置换 α}
  证明: by
  rw [parts_partition]; rw [filter_add]; rw [Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType]; rw [Multiset.filter_eq_nil.2 fun a h => ?_]; rw [add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

Depends on / 依赖: Multiset, Multiset.eq_of_mem_replicate, Multiset.filter_eq_nil, Multiset.filter_eq_self, add_zero, eq_of_mem_replicate, filter_add, filter_eq_nil, filter_eq_self, parts_partition, two_le_of_mem_cycleType
-/
theorem filter_parts_partition_eq_cycleType {σ : Perm α} :
    ((partition σ).parts.filter fun n => 2 <= n) = σ.cycleType := by
  rw [parts_partition]; rw [filter_add]; rw [Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType]; rw [Multiset.filter_eq_nil.2 fun a h => ?_]; rw [add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

/--
theorem `partition_eq_of_isConj` / 定理 `partition_eq_of_isConj`

English:
theorem partition_eq_of_isConj
  given: {σ τ : Perm α}
  statement: IsConj σ τ ↔ σ.partition = τ.partition
  proof: by
  rw [isConj_iff_cycleType_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

中文:
定理 partition_eq_of_isConj
  条件: {σ τ : 置换 α}
  结论: IsConj σ τ ↔ σ.partition = τ.partition
  证明: by
  rw [isConj_iff_cycleType_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

Depends on / 依赖: Nat.Partition.ext_iff, Partition, ext_iff, filter_parts_partition_eq_cycleType, isConj_iff_cycleType_eq, parts_partition, sum_cycleType
-/
theorem partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partition = τ.partition := by
  rw [isConj_iff_cycleType_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

end Partition

section IsSwap

variable [DecidableEq α]

/--
theorem `isSwap_iff_cycleType` / 定理 `isSwap_iff_cycleType`

English:
theorem isSwap_iff_cycleType
  given: {σ : Perm α}
  statement: σ.IsSwap ↔ σ.cycleType = {2}
  proof: by
  constructor
  · intro h
    simpa [h.isCycle.cycleType, card_support_eq_two] using h
  · intro h
    simp [← card_support_eq_two, ← sum_cycleType, h]

omit [Fintype α] in variable [Finite α] in

中文:
定理 isSwap_iff_cycleType
  条件: {σ : 置换 α}
  结论: σ.IsSwap ↔ σ.cycleType = {2}
  证明: by
  constructor
  · intro h
    simpa [h.isCycle.cycleType, card_support_eq_two] using h
  · intro h
    simp [← card_support_eq_two, ← sum_cycleType, h]

omit [Fintype α] in variable [Finite α] in

Depends on / 依赖: card_support_eq_two, cycleType, h.isCycle.cycleType, isCycle, sum_cycleType
-/
theorem isSwap_iff_cycleType {σ : Perm α} : σ.IsSwap ↔ σ.cycleType = {2} := by
  constructor
  · intro h
    simpa [h.isCycle.cycleType, card_support_eq_two] using h
  · intro h
    simp [← card_support_eq_two, ← sum_cycleType, h]

omit [Fintype α] in variable [Finite α] in
/--
theorem `IsSwap.orderOf` / 定理 `IsSwap.orderOf`

English:
theorem IsSwap.orderOf
  given: {σ : Equiv.Perm α} (h : σ.IsSwap)
  proof: by
  have := Fintype.ofFinite α
  rw [← lcm_cycleType]; rw [isSwap_iff_cycleType.mp h]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

中文:
定理 IsSwap.orderOf
  条件: {σ : 等价.置换 α} (h : σ.IsSwap)
  证明: by
  have := Fintype.ofFinite α
  rw [← lcm_cycleType]; rw [isSwap_iff_cycleType.mp h]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

Depends on / 依赖: Fintype, Fintype.ofFinite, Multiset, Multiset.lcm_singleton, isSwap_iff_cycleType, isSwap_iff_cycleType.mp, lcm_cycleType, lcm_singleton, normalize_eq, ofFinite
-/
theorem IsSwap.orderOf {σ : Equiv.Perm α} (h : σ.IsSwap) :
    orderOf σ = 2 := by
  have := Fintype.ofFinite α
  rw [← lcm_cycleType]; rw [isSwap_iff_cycleType.mp h]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

end IsSwap

/-!
### 3-cycles
-/

/--
Definition of `IsThreeCycle` / `IsThreeCycle` 的定义

English:
definition IsThreeCycle
  signature: [DecidableEq α] (σ : Perm α)
  body: σ.cycleType = {3}

中文:
定义 IsThreeCycle
  签名: [DecidableEq α] (σ : 置换 α)
  定义体: σ.cycleType = {3}

Depends on / 依赖: cycleType
-/
def IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop :=
  σ.cycleType = {3}

namespace IsThreeCycle

variable [DecidableEq α] {σ : Perm α}

/--
theorem `cycleType` / 定理 `cycleType`

English:
theorem cycleType
  given: (h : IsThreeCycle σ)
  statement: σ.cycleType = {3}
  proof: h

中文:
定理 cycleType
  条件: (h : IsThreeCycle σ)
  结论: σ.cycleType = {3}
  证明: h
-/
theorem cycleType (h : IsThreeCycle σ) : σ.cycleType = {3} :=
  h

/--
theorem `ne_one` / 定理 `ne_one`

English:
theorem ne_one
  given: (h : IsThreeCycle σ)
  statement: σ != 1
  proof: by
  rintro rfl
  simpa using h.cycleType

中文:
定理 ne_one
  条件: (h : IsThreeCycle σ)
  结论: σ != 1
  证明: by
  rintro rfl
  simpa using h.cycleType

Depends on / 依赖: cycleType, h.cycleType
-/
theorem ne_one (h : IsThreeCycle σ) : σ != 1 := by
  rintro rfl
  simpa using h.cycleType

/--
theorem `card_support` / 定理 `card_support`

English:
theorem card_support
  given: (h : IsThreeCycle σ)
  statement: #σ.support = 3
  proof: by
  rw [← sum_cycleType]; rw [h.cycleType]; rw [Multiset.sum_singleton]

中文:
定理 card_support
  条件: (h : IsThreeCycle σ)
  结论: #σ.support = 3
  证明: by
  rw [← sum_cycleType]; rw [h.cycleType]; rw [Multiset.sum_singleton]

Depends on / 依赖: Multiset, Multiset.sum_singleton, cycleType, h.cycleType, sum_cycleType, sum_singleton
-/
theorem card_support (h : IsThreeCycle σ) : #σ.support = 3 := by
  rw [← sum_cycleType]; rw [h.cycleType]; rw [Multiset.sum_singleton]

/--
theorem `_root_.card_support_eq_three_iff` / 定理 `_root_.card_support_eq_three_iff`

English:
theorem _root_.card_support_eq_three_iff
  statement: #σ.support = 3 ↔ σ.IsThreeCycle
  proof: by
  refine ⟨fun h => ?_, IsThreeCycle.card_support⟩
  by_cases h0 : σ.cycleType = 0
  · rw [← sum_cycleType, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycleType.erase n = 0
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [IsThreeCycle]; rw [← cons_erase hn]; rw [h1]; rw [h]; rw [← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycleType]; rw [← cons_erase hn]; rw [← cons_erase hm]; rw [Multiset.sum_cons]; rw [Multiset.sum_cons] at h
  have : forall {k}, 2 <= m -> 2 <= n -> n + (m + k) = 3 -> False := by lia
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h

中文:
定理 _root_.card_support_eq_three_iff
  结论: #σ.support = 3 ↔ σ.IsThreeCycle
  证明: by
  refine ⟨fun h => ?_, IsThreeCycle.card_support⟩
  by_cases h0 : σ.cycleType = 0
  · rw [← sum_cycleType, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycleType.erase n = 0
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [IsThreeCycle]; rw [← cons_erase hn]; rw [h1]; rw [h]; rw [← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycleType]; rw [← cons_erase hn]; rw [← cons_erase hm]; rw [Multiset.sum_cons]; rw [Multiset.sum_cons] at h
  have : forall {k}, 2 <= m -> 2 <= n -> n + (m + k) = 3 -> False := by lia
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h

Depends on / 依赖: IsThreeCycle, IsThreeCycle.card_support, Multiset, Multiset.sum_singleton, card_support, cons_e, cons_erase, cons_zero, cycleType, cycleType.erase, exists_mem_of_ne_zero, ne_of_lt, sum_cycleType, sum_singleton, sum_zero, zero_lt_three
-/
theorem _root_.card_support_eq_three_iff : #σ.support = 3 ↔ σ.IsThreeCycle := by
  refine ⟨fun h => ?_, IsThreeCycle.card_support⟩
  by_cases h0 : σ.cycleType = 0
  · rw [← sum_cycleType, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycleType.erase n = 0
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [IsThreeCycle]; rw [← cons_erase hn]; rw [h1]; rw [h]; rw [← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycleType]; rw [← cons_erase hn]; rw [← cons_erase hm]; rw [Multiset.sum_cons]; rw [Multiset.sum_cons] at h
  have : forall {k}, 2 <= m -> 2 <= n -> n + (m + k) = 3 -> False := by lia
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h

/--
theorem `isCycle` / 定理 `isCycle`

English:
theorem isCycle
  given: (h : IsThreeCycle σ)
  statement: IsCycle σ
  proof: by
  rw [← card_cycleType_eq_one]; rw [h.cycleType]; rw [card_singleton]

中文:
定理 isCycle
  条件: (h : IsThreeCycle σ)
  结论: 是环 σ
  证明: by
  rw [← card_cycleType_eq_one]; rw [h.cycleType]; rw [card_singleton]

Depends on / 依赖: card_cycleType_eq_one, card_singleton, cycleType, h.cycleType
-/
theorem isCycle (h : IsThreeCycle σ) : IsCycle σ := by
  rw [← card_cycleType_eq_one]; rw [h.cycleType]; rw [card_singleton]

/--
theorem `sign` / 定理 `sign`

English:
theorem sign
  given: (h : IsThreeCycle σ)
  statement: sign σ = 1
  proof: by
  rw [Equiv.Perm.sign_of_cycleType]; rw [h.cycleType]
  rfl

中文:
定理 sign
  条件: (h : IsThreeCycle σ)
  结论: sign σ = 1
  证明: by
  rw [Equiv.Perm.sign_of_cycleType]; rw [h.cycleType]
  rfl

Depends on / 依赖: Equiv.Perm.sign_of_cycleType, cycleType, h.cycleType, sign_of_cycleType
-/
theorem sign (h : IsThreeCycle σ) : sign σ = 1 := by
  rw [Equiv.Perm.sign_of_cycleType]; rw [h.cycleType]
  rfl

/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: {f : Perm α} (h : IsThreeCycle f)
  statement: IsThreeCycle f⁻¹
  proof: by
  rwa [IsThreeCycle, cycleType_inv]

@[simp]

中文:
定理 inv
  条件: {f : 置换 α} (h : IsThreeCycle f)
  结论: IsThreeCycle f⁻¹
  证明: by
  rwa [IsThreeCycle, cycleType_inv]

@[simp]

Depends on / 依赖: IsThreeCycle, cycleType_inv
-/
theorem inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹ := by
  rwa [IsThreeCycle, cycleType_inv]

@[simp]
/--
theorem `inv_iff` / 定理 `inv_iff`

English:
theorem inv_iff
  given: {f : Perm α}
  statement: IsThreeCycle f⁻¹ ↔ IsThreeCycle f
  proof: ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩

中文:
定理 inv_iff
  条件: {f : 置换 α}
  结论: IsThreeCycle f⁻¹ ↔ IsThreeCycle f
  证明: ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩

Depends on / 依赖: inv_inv
-/
theorem inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f :=
  ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩

/--
theorem `orderOf` / 定理 `orderOf`

English:
theorem orderOf
  given: {g : Perm α} (ht : IsThreeCycle g)
  statement: orderOf g = 3
  proof: by
  rw [← lcm_cycleType]; rw [ht.cycleType]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

中文:
定理 orderOf
  条件: {g : 置换 α} (ht : IsThreeCycle g)
  结论: orderOf g = 3
  证明: by
  rw [← lcm_cycleType]; rw [ht.cycleType]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

Depends on / 依赖: Multiset, Multiset.lcm_singleton, cycleType, ht.cycleType, lcm_cycleType, lcm_singleton, normalize_eq
-/
theorem orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3 := by
  rw [← lcm_cycleType]; rw [ht.cycleType]; rw [Multiset.lcm_singleton]; rw [normalize_eq]

/--
theorem `isThreeCycle_sq` / 定理 `isThreeCycle_sq`

English:
theorem isThreeCycle_sq
  given: {g : Perm α} (ht : IsThreeCycle g)
  statement: IsThreeCycle (g * g)
  proof: by
  rw [← pow_two]; rw [← card_support_eq_three_iff]; rw [support_pow_coprime]; rw [ht.card_support]
  rw [ht.orderOf]
  norm_num

中文:
定理 isThreeCycle_sq
  条件: {g : 置换 α} (ht : IsThreeCycle g)
  结论: IsThreeCycle (g * g)
  证明: by
  rw [← pow_two]; rw [← card_support_eq_three_iff]; rw [support_pow_coprime]; rw [ht.card_support]
  rw [ht.orderOf]
  norm_num

Depends on / 依赖: card_support, card_support_eq_three_iff, ht.card_support, ht.orderOf, orderOf, pow_two, support_pow_coprime
-/
theorem isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g) := by
  rw [← pow_two]; rw [← card_support_eq_three_iff]; rw [support_pow_coprime]; rw [ht.card_support]
  rw [ht.orderOf]
  norm_num

end IsThreeCycle

section

variable [DecidableEq α]

/--
theorem `isThreeCycle_swap_mul_swap_same` / 定理 `isThreeCycle_swap_mul_swap_same`

English:
theorem isThreeCycle_swap_mul_swap_same
  given: {a b c : α} (ab : a != b) (ac : a != c) (bc : b != c)
  proof: by
  suffices h : support (swap a b * swap a c) = {a, b, c} by
    rw [← card_support_eq_three_iff]; rw [h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  · simp [ab, ac]
  · simp only [mem_support, coe_mul]
    grind

中文:
定理 isThreeCycle_swap_mul_swap_same
  条件: {a b c : α} (ab : a != b) (ac : a != c) (bc : b != c)
  证明: by
  suffices h : support (swap a b * swap a c) = {a, b, c} by
    rw [← card_support_eq_three_iff]; rw [h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  · simp [ab, ac]
  · simp only [mem_support, coe_mul]
    grind

Depends on / 依赖: card_support_eq_three_iff, coe_mul, le_antisymm, mem_support, support, support_mul_le
-/
theorem isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a != b) (ac : a != c) (bc : b != c) :
    IsThreeCycle (swap a b * swap a c) := by
  suffices h : support (swap a b * swap a c) = {a, b, c} by
    rw [← card_support_eq_three_iff]; rw [h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  · simp [ab, ac]
  · simp only [mem_support, coe_mul]
    grind

/--
theorem `IsThreeCycle.support_eq_iff_mem_support` / 定理 `IsThreeCycle.support_eq_iff_mem_support`

English:
theorem IsThreeCycle.support_eq_iff_mem_support
  proof: by
  constructor
  · intro hg; simp [hg]
  · intro ha
    symm
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset ha
      apply Finset.insert_subset
      · rwa [Perm.apply_mem_support]
      simpa only [Finset.singleton_subset_iff, Perm.apply_mem_support]
    · rw [hg3.card_support]
      simp only [mem_support, ne_eq] at ha
      rw [Finset.card_insert_eq_ite]; rw [if_neg]
      · rw [Finset.card_insert_eq_ite, if_neg]
        · simp
        · simpa using Ne.symm ha
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        contrapose ha
        rcases ha with ha | ha
        · exact ha.symm
        · suffices (g ^ 3) a = a by simpa [pow_succ, ← ha] using this
          simp [← hg3.orderOf]

中文:
定理 IsThreeCycle.support_eq_iff_mem_support
  证明: by
  constructor
  · intro hg; simp [hg]
  · intro ha
    symm
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset ha
      apply Finset.insert_subset
      · rwa [Perm.apply_mem_support]
      simpa only [Finset.singleton_subset_iff, Perm.apply_mem_support]
    · rw [hg3.card_support]
      simp only [mem_support, ne_eq] at ha
      rw [Finset.card_insert_eq_ite]; rw [if_neg]
      · rw [Finset.card_insert_eq_ite, if_neg]
        · simp
        · simpa using Ne.symm ha
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        contrapose ha
        rcases ha with ha | ha
        · exact ha.symm
        · suffices (g ^ 3) a = a by simpa [pow_succ, ← ha] using this
          simp [← hg3.orderOf]

Depends on / 依赖: Finset, Finset.card_insert_eq_ite, Finset.eq_of_subset_of_card_le, Finset.insert_subset, Finset.mem_insert, Finset.mem_singleton, Finset.singleton_subset_iff, Ne.symm, Perm.apply_mem_support, apply_mem_support, card_insert_eq_ite, card_support, contrapose, eq_of_subset_of_card_le, hg3.card_support, if_neg, insert_subset, mem_insert, mem_singleton, mem_support
-/
theorem IsThreeCycle.support_eq_iff_mem_support
    {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    g.support = {a, g a, g (g a)} ↔ a in g.support := by
  constructor
  · intro hg; simp [hg]
  · intro ha
    symm
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset ha
      apply Finset.insert_subset
      · rwa [Perm.apply_mem_support]
      simpa only [Finset.singleton_subset_iff, Perm.apply_mem_support]
    · rw [hg3.card_support]
      simp only [mem_support, ne_eq] at ha
      rw [Finset.card_insert_eq_ite]; rw [if_neg]
      · rw [Finset.card_insert_eq_ite, if_neg]
        · simp
        · simpa using Ne.symm ha
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        contrapose ha
        rcases ha with ha | ha
        · exact ha.symm
        · suffices (g ^ 3) a = a by simpa [pow_succ, ← ha] using this
          simp [← hg3.orderOf]

/--
theorem `IsThreeCycle.nodup_iff_mem_support` / 定理 `IsThreeCycle.nodup_iff_mem_support`

English:
theorem IsThreeCycle.nodup_iff_mem_support
  given: {g : Perm α} {a : α} (hg3 : g.IsThreeCycle)
  proof: by
  constructor
  · intro ha
    rw [mem_support]
    grind
  rw [← support_eq_iff_mem_support hg3]
  intro ha
  suffices g.support.card = 3 by grind
  exact hg3.card_support

中文:
定理 IsThreeCycle.nodup_iff_mem_support
  条件: {g : 置换 α} {a : α} (hg3 : g.IsThreeCycle)
  证明: by
  constructor
  · intro ha
    rw [mem_support]
    grind
  rw [← support_eq_iff_mem_support hg3]
  intro ha
  suffices g.support.card = 3 by grind
  exact hg3.card_support

Depends on / 依赖: card_support, g.support.card, hg3.card_support, mem_support, support, support_eq_iff_mem_support
-/
theorem IsThreeCycle.nodup_iff_mem_support {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    [a, g a, g (g a)].Nodup ↔ a in g.support := by
  constructor
  · intro ha
    rw [mem_support]
    grind
  rw [← support_eq_iff_mem_support hg3]
  intro ha
  suffices g.support.card = 3 by grind
  exact hg3.card_support

/--
theorem `IsThreeCycle.eq_swap_mul_swap_iff_mem_support` / 定理 `IsThreeCycle.eq_swap_mul_swap_iff_mem_support`

English:
theorem IsThreeCycle.eq_swap_mul_swap_iff_mem_support
  proof: by
  constructor
  · intro hg
    rw [mem_support]
    intro hx
    apply hg3.isCycle.ne_one
    simpa [hx] using! hg
  intro ha
  have ha' := hg3.support_eq_iff_mem_support.mpr ha
  have ha'' := hg3.nodup_iff_mem_support.mpr ha
  ext x
  simp only [coe_mul, Function.comp_apply]
  by_cases h : x in g.support
  · simp only [ha', Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | (rfl | rfl)
    · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
      simp
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (by grind) (by grind)]
    · simp only [swap_apply_right]
      suffices (g ^ 3) a = a by simpa
      simp [← hg3.orderOf]
  · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    simpa [notMem_support] using! h

中文:
定理 IsThreeCycle.eq_swap_mul_swap_iff_mem_support
  证明: by
  constructor
  · intro hg
    rw [mem_support]
    intro hx
    apply hg3.isCycle.ne_one
    simpa [hx] using! hg
  intro ha
  have ha' := hg3.support_eq_iff_mem_support.mpr ha
  have ha'' := hg3.nodup_iff_mem_support.mpr ha
  ext x
  simp only [coe_mul, Function.comp_apply]
  by_cases h : x in g.support
  · simp only [ha', Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | (rfl | rfl)
    · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
      simp
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (by grind) (by grind)]
    · simp only [swap_apply_right]
      suffices (g ^ 3) a = a by simpa
      simp [← hg3.orderOf]
  · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    simpa [notMem_support] using! h

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, Function, Function.comp_apply, coe_mul, comp_apply, g.support, hg3.isCycle.ne_one, hg3.nodup_iff_mem_support.mpr, hg3.support_eq_iff_mem_support.mpr, isCycle, mem_insert, mem_singleton, mem_support, ne_one, nodup_iff_mem_support, support, support_eq_iff_mem_support, swap_apply_left
-/
theorem IsThreeCycle.eq_swap_mul_swap_iff_mem_support
    {g : Perm α} {a : α} (hg3 : g.IsThreeCycle) :
    g = (swap a (g a)) * (swap (g a) (g (g a))) ↔ a in g.support := by
  constructor
  · intro hg
    rw [mem_support]
    intro hx
    apply hg3.isCycle.ne_one
    simpa [hx] using! hg
  intro ha
  have ha' := hg3.support_eq_iff_mem_support.mpr ha
  have ha'' := hg3.nodup_iff_mem_support.mpr ha
  ext x
  simp only [coe_mul, Function.comp_apply]
  by_cases h : x in g.support
  · simp only [ha', Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | (rfl | rfl)
    · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
      simp
    · rw [swap_apply_left, swap_apply_of_ne_of_ne (by grind) (by grind)]
    · simp only [swap_apply_right]
      suffices (g ^ 3) a = a by simpa
      simp [← hg3.orderOf]
  · rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    rw [swap_apply_of_ne_of_ne (x := x) (by grind) (by grind)]
    simpa [notMem_support] using! h

open Subgroup

/--
theorem `swap_mul_swap_same_mem_closure_three_cycles` / 定理 `swap_mul_swap_same_mem_closure_three_cycles`

English:
theorem swap_mul_swap_same_mem_closure_three_cycles
  given: {a b c : α} (ab : a != b) (ac : a != c)
  proof: by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)

中文:
定理 swap_mul_swap_same_mem_closure_three_cycles
  条件: {a b c : α} (ab : a != b) (ac : a != c)
  证明: by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)

Depends on / 依赖: isThreeCycle_swap_mul_swap_same, one_mem, subset_closure
-/
theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a != b) (ac : a != c) :
    swap a b * swap a c in closure { σ : Perm α | IsThreeCycle σ } := by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)

/--
theorem `IsSwap.mul_mem_closure_three_cycles` / 定理 `IsSwap.mul_mem_closure_three_cycles`

English:
theorem IsSwap.mul_mem_closure_three_cycles
  given: {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ)
  proof: by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  obtain ⟨c, d, cd, rfl⟩ := hτ
  by_cases ac : a = c
  · subst ac
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)

中文:
定理 IsSwap.mul_mem_closure_three_cycles
  条件: {σ τ : 置换 α} (hσ : IsSwap σ) (hτ : IsSwap τ)
  证明: by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  obtain ⟨c, d, cd, rfl⟩ := hτ
  by_cases ac : a = c
  · subst ac
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)

Depends on / 依赖: Ne.symm, mul_assoc, mul_mem, swap_comm, swap_mul_swap_same_mem_closure_three_cycles
-/
theorem IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
    σ * τ in closure { σ : Perm α | IsThreeCycle σ } := by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  obtain ⟨c, d, cd, rfl⟩ := hτ
  by_cases ac : a = c
  · subst ac
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)

end

section

variable [DecidableEq α]

/--
theorem `cycleType_swap_mul_swap_of_nodup` / 定理 `cycleType_swap_mul_swap_of_nodup`

English:
theorem cycleType_swap_mul_swap_of_nodup
  given: {x y z t : α} (h : [x, y, z, t].Nodup)
  proof: by
  rw [(disjoint_swap_swap h).cycleType_mul]
  rw [isSwap_iff_cycleType.mp ?_]; rw [isSwap_iff_cycleType.mp ?_]
  · simp
  · rw [swap_isSwap_iff]; grind
  · rw [swap_isSwap_iff]; grind

中文:
定理 cycleType_swap_mul_swap_of_nodup
  条件: {x y z t : α} (h : [x, y, z, t].Nodup)
  证明: by
  rw [(disjoint_swap_swap h).cycleType_mul]
  rw [isSwap_iff_cycleType.mp ?_]; rw [isSwap_iff_cycleType.mp ?_]
  · simp
  · rw [swap_isSwap_iff]; grind
  · rw [swap_isSwap_iff]; grind

Depends on / 依赖: cycleType_mul, disjoint_swap_swap, isSwap_iff_cycleType, isSwap_iff_cycleType.mp, swap_isSwap_iff
-/
theorem cycleType_swap_mul_swap_of_nodup {x y z t : α} (h : [x, y, z, t].Nodup) :
    (swap x y * swap z t).cycleType = {2, 2} := by
  rw [(disjoint_swap_swap h).cycleType_mul]
  rw [isSwap_iff_cycleType.mp ?_]; rw [isSwap_iff_cycleType.mp ?_]
  · simp
  · rw [swap_isSwap_iff]; grind
  · rw [swap_isSwap_iff]; grind

end

end Equiv.Perm
