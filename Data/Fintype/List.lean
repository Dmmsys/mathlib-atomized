/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Permutation

/-!

# Fintype instance for nodup lists

The subtype of `{l : List α // l.Nodup}` over a `[Fintype α]`
admits a `Fintype` instance.

## Implementation details
To construct the `Fintype` instance, a function lifting a `Multiset α`
to the `Multiset (List α)` is provided.
This function is applied to the `Finset.powerset` of `Finset.univ`.

-/

@[expose] public section


variable {α : Type*}
open List

namespace Multiset

/--
Definition of `lists` / `lists` 的定义

English:
definition lists
  signature: : Multiset α -> Multiset (List α)
  body: fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]

中文:
定义 lists
  签名: : Multiset α -> Multiset (列表 α)
  定义体: fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]
-/
def lists : Multiset α -> Multiset (List α) := fun s =>
  Quotient.liftOn s (fun l => l.permutations) fun l l' (h : l ~ l') => by
    refine coe_eq_coe.mpr ?_
    exact Perm.permutations h

@[simp]
/--
theorem `lists_coe` / 定理 `lists_coe`

English:
theorem lists_coe
  given: (l : List α)
  statement: lists (l : Multiset α) = l.permutations
  proof: rfl

@[simp]

中文:
定理 lists_coe
  条件: (l : 列表 α)
  结论: lists (l : Multiset α) = l.permutations
  证明: rfl

@[simp]
-/
theorem lists_coe (l : List α) : lists (l : Multiset α) = l.permutations :=
  rfl

@[simp]
/--
theorem `lists_nodup_finset` / 定理 `lists_nodup_finset`

English:
theorem lists_nodup_finset
  given: (l : Finset α)
  statement: (lists (l.val)).Nodup
  proof: by
  have h_nodup : l.val.Nodup := l.nodup
  rw [← Finset.coe_toList l]; rw [Multiset.coe_nodup] at h_nodup
  rw [← Finset.coe_toList l]
  exact nodup_permutations l.val.toList (h_nodup)

@[simp]

中文:
定理 lists_nodup_finset
  条件: (l : 有限集 α)
  结论: (lists (l.val)).Nodup
  证明: by
  have h_nodup : l.val.Nodup := l.nodup
  rw [← Finset.coe_toList l]; rw [Multiset.coe_nodup] at h_nodup
  rw [← Finset.coe_toList l]
  exact nodup_permutations l.val.toList (h_nodup)

@[simp]

Depends on / 依赖: Finset, Finset.coe_toList, Multiset, Multiset.coe_nodup, coe_nodup, coe_toList, h_nodup, l.nodup, l.val.Nodup, l.val.toList, nodup_permutations, toList
-/
theorem lists_nodup_finset (l : Finset α) : (lists (l.val)).Nodup := by
  have h_nodup : l.val.Nodup := l.nodup
  rw [← Finset.coe_toList l]; rw [Multiset.coe_nodup] at h_nodup
  rw [← Finset.coe_toList l]
  exact nodup_permutations l.val.toList (h_nodup)

@[simp]
/--
theorem `mem_lists_iff` / 定理 `mem_lists_iff`

English:
theorem mem_lists_iff
  given: (s : Multiset α) (l : List α)
  statement: l in lists s ↔ s = ⟦l⟧
  proof: by
  induction s using Quotient.inductionOn
  simpa using perm_comm

中文:
定理 mem_lists_iff
  条件: (s : Multiset α) (l : 列表 α)
  结论: l in lists s ↔ s = ⟦l⟧
  证明: by
  induction s using Quotient.inductionOn
  simpa using perm_comm

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, perm_comm
-/
theorem mem_lists_iff (s : Multiset α) (l : List α) : l in lists s ↔ s = ⟦l⟧ := by
  induction s using Quotient.inductionOn
  simpa using perm_comm

end Multiset

/--
Instance `fintypeNodupList` / 实例 `fintypeNodupList`

English:
instance fintypeNodupList
  signature: [Fintype α]
  body: by
  refine Fintype.subtype ?_ ?_
  · let univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    let allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList]
      rfl
    · -- Unfold `List.Nodup` in the type of the proof term to make it match with the goal.
      convert dsimp% [List.Nodup] Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
        with m n
      simp only [_root_.Disjoint]
      rw [← m.coe_toList]; rw [← n.coe_toList]; rw [Multiset.lists_coe]; rw [Multiset.lists_coe]
      have := Multiset.coe_disjoint m.toList.permutations n.toList.permutations
      rw [_root_.Disjoint] at this
      rw [this]; rw [List.disjoint_iff_ne]
      constructor
      · intro h
        by_contra hc
        rw [hc] at h
        contrapose! h
        use n.toList
        simp
      · intro h
        simp only [mem_permutations]
        intro a ha b hb
        by_contra hab
        absurd h
        rw [hab] at ha
exact Finset.perm_toList.mp Perm.trans ha.symm hb
  · intro l
    simp only [Finset.mem_mk, Multiset.mem_bind, Finset.mem_val, Finset.mem_powerset,
      Finset.subset_univ, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe, true_and]
    constructor
    · intro h
      rcases h with ⟨f, hf⟩
      convert! f.nodup
      rw [hf]
      rfl
    · intro h
      exact CanLift.prf _ h

中文:
实例 fintypeNodupList
  签名: [有限类型 α]
  定义体: by
  refine Fintype.subtype ?_ ?_
  · let univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    let allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList]
      rfl
    · -- Unfold `List.Nodup` in the type of the proof term to make it match with the goal.
      convert dsimp% [List.Nodup] Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
        with m n
      simp only [_root_.Disjoint]
      rw [← m.coe_toList]; rw [← n.coe_toList]; rw [Multiset.lists_coe]; rw [Multiset.lists_coe]
      have := Multiset.coe_disjoint m.toList.permutations n.toList.permutations
      rw [_root_.Disjoint] at this
      rw [this]; rw [List.disjoint_iff_ne]
      constructor
      · intro h
        by_contra hc
        rw [hc] at h
        contrapose! h
        use n.toList
        simp
      · intro h
        simp only [mem_permutations]
        intro a ha b hb
        by_contra hab
        absurd h
        rw [hab] at ha
exact Finset.perm_toList.mp Perm.trans ha.symm hb
  · intro l
    simp only [Finset.mem_mk, Multiset.mem_bind, Finset.mem_val, Finset.mem_powerset,
      Finset.subset_univ, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe, true_and]
    constructor
    · intro h
      rcases h with ⟨f, hf⟩
      convert! f.nodup
      rw [hf]
      rfl
    · intro h
      exact CanLift.prf _ h

Depends on / 依赖: Finset, Finset.coe_toList, Finset.univ, Fintype, Fintype.subtype, List.Nodup, Multiset, Multiset.Pairwise, Multiset.bind, Multiset.lists, Multiset.lists_nodup_finset, Multiset.nodup_bind.mpr, Pairwise, Unfold, allPerms, coe_toList, implies_true, lists_nodup_finset, nodup_bind, powerset
-/
instance fintypeNodupList [Fintype α] : Fintype { l : List α // l.Nodup } := by
  refine Fintype.subtype ?_ ?_
  · let univSubsets := ((Finset.univ : Finset α).powerset.1 : (Multiset (Finset α)))
    let allPerms := Multiset.bind univSubsets (fun s => (Multiset.lists s.1))
    refine ⟨allPerms, Multiset.nodup_bind.mpr ?_⟩
    simp only [Multiset.lists_nodup_finset, implies_true, true_and]
    unfold Multiset.Pairwise
    use ((Finset.univ : Finset α).powerset.toList : (List (Finset α)))
    constructor
    · simp only [Finset.coe_toList]
      rfl
    · -- Unfold `List.Nodup` in the type of the proof term to make it match with the goal.
      convert dsimp% [List.Nodup] Finset.nodup_toList (Finset.univ.powerset : Finset (Finset α))
        with m n
      simp only [_root_.Disjoint]
      rw [← m.coe_toList]; rw [← n.coe_toList]; rw [Multiset.lists_coe]; rw [Multiset.lists_coe]
      have := Multiset.coe_disjoint m.toList.permutations n.toList.permutations
      rw [_root_.Disjoint] at this
      rw [this]; rw [List.disjoint_iff_ne]
      constructor
      · intro h
        by_contra hc
        rw [hc] at h
        contrapose! h
        use n.toList
        simp
      · intro h
        simp only [mem_permutations]
        intro a ha b hb
        by_contra hab
        absurd h
        rw [hab] at ha
exact Finset.perm_toList.mp Perm.trans ha.symm hb
  · intro l
    simp only [Finset.mem_mk, Multiset.mem_bind, Finset.mem_val, Finset.mem_powerset,
      Finset.subset_univ, Multiset.mem_lists_iff, Multiset.quot_mk_to_coe, true_and]
    constructor
    · intro h
      rcases h with ⟨f, hf⟩
      convert! f.nodup
      rw [hf]
      rfl
    · intro h
      exact CanLift.prf _ h
