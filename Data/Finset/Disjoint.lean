/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert

/-!
# Disjoint finite sets

## Main declarations

* `Disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `Finset.disjUnion`: the union of the finite sets `s` and `t`, given a proof `Disjoint s t`

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

variable {ι α β γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### disjoint -/


section Disjoint

variable {f : α -> β} {s t u : Finset α} {a b : α}

/--
theorem `disjoint_left` / 定理 `disjoint_left`

English:
theorem disjoint_left
  statement: Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t
  proof: ⟨fun h a hs ht => notMem_empty a
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left

中文:
定理 disjoint_left
  结论: Disjoint s t ↔ 对任意 ⦃a⦄, a in s -> a ∉ t
  证明: ⟨fun h a hs ht => notMem_empty a
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left

Depends on / 依赖: notMem_empty, singleton_subset_iff, singleton_subset_iff.mp, singleton_subset_iff.mpr
-/
theorem disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> a ∉ t :=
⟨fun h a hs ht => notMem_empty a
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩

alias ⟨_root_.Disjoint.notMem_of_mem_left_finset, _⟩ := disjoint_left

/--
theorem `disjoint_right` / 定理 `disjoint_right`

English:
theorem disjoint_right
  statement: Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s
  proof: by
  rw [_root_.disjoint_comm]; rw [disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right

中文:
定理 disjoint_right
  结论: Disjoint s t ↔ 对任意 ⦃a⦄, a in t -> a ∉ s
  证明: by
  rw [_root_.disjoint_comm]; rw [disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, disjoint_left
-/
theorem disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -> a ∉ s := by
  rw [_root_.disjoint_comm]; rw [disjoint_left]

alias ⟨_root_.Disjoint.notMem_of_mem_right_finset, _⟩ := disjoint_right

/--
theorem `disjoint_iff_ne` / 定理 `disjoint_iff_ne`

English:
theorem disjoint_iff_ne
  statement: Disjoint s t ↔ forall a in s, forall b in t, a != b
  proof: by
  simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp]

中文:
定理 disjoint_iff_ne
  结论: Disjoint s t ↔ 对任意 a in s, 对任意 b in t, a != b
  证明: by
  simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp]

Depends on / 依赖: disjoint_left, forall_eq, imp_not_comm
-/
theorem disjoint_iff_ne : Disjoint s t ↔ forall a in s, forall b in t, a != b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']

@[simp]
/--
theorem `disjoint_val` / 定理 `disjoint_val`

English:
theorem disjoint_val
  statement: Disjoint s.1 t.1 ↔ Disjoint s t
  proof: Multiset.disjoint_left.trans disjoint_left.symm

中文:
定理 disjoint_val
  结论: Disjoint s.1 t.1 ↔ Disjoint s t
  证明: Multiset.disjoint_left.trans disjoint_left.symm

Depends on / 依赖: Multiset, Multiset.disjoint_left.trans, disjoint_left, disjoint_left.symm
-/
theorem disjoint_val : Disjoint s.1 t.1 ↔ Disjoint s t :=
  Multiset.disjoint_left.trans disjoint_left.symm

/--
theorem `_root_.Disjoint.forall_ne_finset` / 定理 `_root_.Disjoint.forall_ne_finset`

English:
theorem _root_.Disjoint.forall_ne_finset
  given: (h : Disjoint s t) (ha : a in s) (hb : b in t)
  statement: a != b
  proof: disjoint_iff_ne.1 h _ ha _ hb

中文:
定理 _root_.Disjoint.对任意_ne_finset
  条件: (h : Disjoint s t) (ha : a in s) (hb : b in t)
  结论: a != b
  证明: disjoint_iff_ne.1 h _ ha _ hb

Depends on / 依赖: disjoint_iff_ne
-/
theorem _root_.Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a in s) (hb : b in t) : a != b :=
  disjoint_iff_ne.1 h _ ha _ hb

/--
theorem `not_disjoint_iff` / 定理 `not_disjoint_iff`

English:
theorem not_disjoint_iff
  statement: ¬Disjoint s t ↔ exists a, a in s ∧ a in t
  proof: disjoint_left.not.trans not_forall.trans exists_congr fun _ => by
    rw [Classical.not_imp]; rw [not_not]

中文:
定理 not_disjoint_iff
  结论: ¬Disjoint s t ↔ 存在 a, a in s ∧ a in t
  证明: disjoint_left.not.trans not_forall.trans exists_congr fun _ => by
    rw [Classical.not_imp]; rw [not_not]

Depends on / 依赖: Classical, Classical.not_imp, disjoint_left, disjoint_left.not.trans, exists_congr, not_forall, not_forall.trans, not_imp, not_not
-/
theorem not_disjoint_iff : ¬Disjoint s t ↔ exists a, a in s ∧ a in t :=
disjoint_left.not.trans not_forall.trans exists_congr fun _ => by
    rw [Classical.not_imp]; rw [not_not]

/--
theorem `disjoint_of_subset_left` / 定理 `disjoint_of_subset_left`

English:
theorem disjoint_of_subset_left
  given: (h : s subseteq u) (d : Disjoint u t)
  statement: Disjoint s t
  proof: disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)

中文:
定理 disjoint_of_subset_left
  条件: (h : s subseteq u) (d : Disjoint u t)
  结论: Disjoint s t
  证明: disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)

Depends on / 依赖: disjoint_left
-/
theorem disjoint_of_subset_left (h : s subseteq u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun _x m₁ => (disjoint_left.1 d) (h m₁)

/--
theorem `disjoint_of_subset_right` / 定理 `disjoint_of_subset_right`

English:
theorem disjoint_of_subset_right
  given: (h : t subseteq u) (d : Disjoint s u)
  statement: Disjoint s t
  proof: disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]

中文:
定理 disjoint_of_subset_right
  条件: (h : t subseteq u) (d : Disjoint s u)
  结论: Disjoint s t
  证明: disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]

Depends on / 依赖: disjoint_right
-/
theorem disjoint_of_subset_right (h : t subseteq u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun _x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]
/--
theorem `disjoint_empty_left` / 定理 `disjoint_empty_left`

English:
theorem disjoint_empty_left
  given: (s : Finset α)
  statement: Disjoint ∅ s
  proof: disjoint_bot_left

@[simp]

中文:
定理 disjoint_empty_left
  条件: (s : 有限集 α)
  结论: Disjoint ∅ s
  证明: disjoint_bot_left

@[simp]

Depends on / 依赖: disjoint_bot_left
-/
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
/--
theorem `disjoint_empty_right` / 定理 `disjoint_empty_right`

English:
theorem disjoint_empty_right
  given: (s : Finset α)
  statement: Disjoint s ∅
  proof: disjoint_bot_right

中文:
定理 disjoint_empty_right
  条件: (s : 有限集 α)
  结论: Disjoint s ∅
  证明: disjoint_bot_right

Depends on / 依赖: disjoint_bot_right
-/
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right

-- Higher priority than `disjoint_singleton_right` to make sure `Disjoint {a} {b}`
-- simplifies to `a ≠ b`.
@[simp default + 1]
/--
theorem `disjoint_singleton_left` / 定理 `disjoint_singleton_left`

English:
theorem disjoint_singleton_left
  statement: Disjoint (singleton a) s ↔ a ∉ s
  proof: by
  simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]

中文:
定理 disjoint_singleton_left
  结论: Disjoint (singleton a) s ↔ a ∉ s
  证明: by
  simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]

Depends on / 依赖: disjoint_left, forall_eq, mem_singleton
-/
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]
/--
theorem `disjoint_singleton_right` / 定理 `disjoint_singleton_right`

English:
theorem disjoint_singleton_right
  statement: Disjoint s (singleton a) ↔ a ∉ s
  proof: disjoint_comm.trans disjoint_singleton_left

中文:
定理 disjoint_singleton_right
  结论: Disjoint s (singleton a) ↔ a ∉ s
  证明: disjoint_comm.trans disjoint_singleton_left

Depends on / 依赖: disjoint_comm, disjoint_comm.trans, disjoint_singleton_left
-/
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left

-- Not `simp` since `disjoint_singleton_{left,right}` prove it.
/--
theorem `disjoint_singleton` / 定理 `disjoint_singleton`

English:
theorem disjoint_singleton
  statement: Disjoint ({a} : Finset α) {b} ↔ a != b
  proof: by
  rw [disjoint_singleton_left]; rw [mem_singleton]

中文:
定理 disjoint_singleton
  结论: Disjoint ({a} : 有限集 α) {b} ↔ a != b
  证明: by
  rw [disjoint_singleton_left]; rw [mem_singleton]

Depends on / 依赖: disjoint_singleton_left, mem_singleton
-/
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a != b := by
  rw [disjoint_singleton_left]; rw [mem_singleton]

/--
theorem `disjoint_self_iff_empty` / 定理 `disjoint_self_iff_empty`

English:
theorem disjoint_self_iff_empty
  given: (s : Finset α)
  statement: Disjoint s s ↔ s = ∅
  proof: disjoint_self

@[simp, norm_cast]

中文:
定理 disjoint_self_iff_empty
  条件: (s : 有限集 α)
  结论: Disjoint s s ↔ s = ∅
  证明: disjoint_self

@[simp, norm_cast]

Depends on / 依赖: disjoint_self
-/
theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self

@[simp, norm_cast]
/--
theorem `disjoint_coe` / 定理 `disjoint_coe`

English:
theorem disjoint_coe
  statement: Disjoint (s : Set α) t ↔ Disjoint s t
  proof: by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]

@[simp, norm_cast]

中文:
定理 disjoint_coe
  结论: Disjoint (s : 集合 α) t ↔ Disjoint s t
  证明: by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.disjoint_left, Set.disjoint_left, disjoint_left, mem_coe
-/
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp only [Finset.disjoint_left, Set.disjoint_left, mem_coe]

@[simp, norm_cast]
/--
theorem `pairwiseDisjoint_coe` / 定理 `pairwiseDisjoint_coe`

English:
theorem pairwiseDisjoint_coe
  given: {ι : Type*} {s : Set ι} {f : ι -> Finset α}
  proof: forall₅_congr fun _ _ _ _ _ => disjoint_coe

中文:
定理 pairwiseDisjoint_coe
  条件: {ι : 类型} {s : 集合 ι} {f : ι -> 有限集 α}
  证明: forall₅_congr fun _ _ _ _ _ => disjoint_coe

Depends on / 依赖: disjoint_coe
-/
theorem pairwiseDisjoint_coe {ι : Type*} {s : Set ι} {f : ι -> Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι -> Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe

/--
lemma `pairwiseDisjoint_singleton_iff_injOn` / 引理 `pairwiseDisjoint_singleton_iff_injOn`

English:
lemma pairwiseDisjoint_singleton_iff_injOn
  given: {s : Set ι} {f : ι -> α}
  proof: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_not, Set.InjOn]

中文:
引理 pairwiseDisjoint_singleton_iff_injOn
  条件: {s : 集合 ι} {f : ι -> α}
  证明: by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_not, Set.InjOn]
-/
@[simp] lemma pairwiseDisjoint_singleton_iff_injOn {s : Set ι} {f : ι -> α} :
    s.PairwiseDisjoint (fun i => ({f i} : Finset α)) ↔ s.InjOn f := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, not_imp_not, Set.InjOn]

variable [DecidableEq α]

/--
Instance `decidableDisjoint` / 实例 `decidableDisjoint`

English:
instance decidableDisjoint
  signature: (U V : Finset α)
  body: decidable_of_iff _ disjoint_left.symm

中文:
实例 decidableDisjoint
  签名: (U V : 有限集 α)
  定义体: decidable_of_iff _ disjoint_left.symm

Depends on / 依赖: decidable_of_iff, disjoint_left, disjoint_left.symm
-/
instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidable_of_iff _ disjoint_left.symm

end Disjoint

/-! ### disjoint union -/


/-- `disjUnion s t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
@[simps]
/--
Definition of `disjUnion` / `disjUnion` 的定义

English:
definition disjUnion
  signature: (s t : Finset α) (h : Disjoint s t)
  body: ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp, grind =]

中文:
定义 disjUnion
  签名: (s t : 有限集 α) (h : Disjoint s t)
  定义体: ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp, grind =]

Depends on / 依赖: Multiset, Multiset.nodup_add, disjoint_val, nodup_add
-/
def disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩

@[simp, grind =]
/--
theorem `mem_disjUnion` / 定理 `mem_disjUnion`

English:
theorem mem_disjUnion
  given: {α s t h a}
  statement: a in @disjUnion α s t h ↔ a in s ∨ a in t
  proof: by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append

@[simp, norm_cast]

中文:
定理 mem_disjUnion
  条件: {α s t h a}
  结论: a in @disjUnion α s t h ↔ a in s ∨ a in t
  证明: by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append

@[simp, norm_cast]

Depends on / 依赖: List.mem_append, mem_append
-/
theorem mem_disjUnion {α s t h a} : a in @disjUnion α s t h ↔ a in s ∨ a in t := by
  rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply List.mem_append

@[simp, norm_cast]
/--
theorem `coe_disjUnion` / 定理 `coe_disjUnion`

English:
theorem coe_disjUnion
  given: {s t : Finset α} (h : Disjoint s t)
  proof: Set.ext by simp

中文:
定理 coe_disjUnion
  条件: {s t : 有限集 α} (h : Disjoint s t)
  证明: Set.ext by simp

Depends on / 依赖: Set.ext
-/
theorem coe_disjUnion {s t : Finset α} (h : Disjoint s t) :
    (disjUnion s t h : Set α) = (s : Set α) union t :=
Set.ext by simp

/--
theorem `disjUnion_comm` / 定理 `disjUnion_comm`

English:
theorem disjUnion_comm
  given: (s t : Finset α) (h : Disjoint s t)
  proof: eq_of_veq Multiset.add_comm _ _

@[simp]

中文:
定理 disjUnion_comm
  条件: (s t : 有限集 α) (h : Disjoint s t)
  证明: eq_of_veq Multiset.add_comm _ _

@[simp]

Depends on / 依赖: Multiset, Multiset.add_comm, add_comm, eq_of_veq
-/
theorem disjUnion_comm (s t : Finset α) (h : Disjoint s t) :
    disjUnion s t h = disjUnion t s h.symm :=
eq_of_veq Multiset.add_comm _ _

@[simp]
/--
theorem `disjUnion_inj_left` / 定理 `disjUnion_inj_left`

English:
theorem disjUnion_inj_left
  given: {s₁ s₂ t : Finset α} (h₁ : Disjoint s₁ t) (h₂ : Disjoint s₂ t)
  proof: by
  simp [← val_inj, Multiset.add_left_inj]

@[simp]

中文:
定理 disjUnion_inj_left
  条件: {s₁ s₂ t : 有限集 α} (h₁ : Disjoint s₁ t) (h₂ : Disjoint s₂ t)
  证明: by
  simp [← val_inj, Multiset.add_left_inj]

@[simp]

Depends on / 依赖: Multiset, Multiset.add_left_inj, add_left_inj, val_inj
-/
theorem disjUnion_inj_left {s₁ s₂ t : Finset α} (h₁ : Disjoint s₁ t) (h₂ : Disjoint s₂ t) :
    s₁.disjUnion t h₁ = s₂.disjUnion t h₂ ↔ s₁ = s₂ := by
  simp [← val_inj, Multiset.add_left_inj]

@[simp]
/--
theorem `disjUnion_inj_right` / 定理 `disjUnion_inj_right`

English:
theorem disjUnion_inj_right
  given: {s t₁ t₂ : Finset α} (h₁ : Disjoint s t₁) (h₂ : Disjoint s t₂)
  proof: by
  simp [← val_inj, Multiset.add_right_inj]

@[simp]

中文:
定理 disjUnion_inj_right
  条件: {s t₁ t₂ : 有限集 α} (h₁ : Disjoint s t₁) (h₂ : Disjoint s t₂)
  证明: by
  simp [← val_inj, Multiset.add_right_inj]

@[simp]

Depends on / 依赖: Multiset, Multiset.add_right_inj, add_right_inj, val_inj
-/
theorem disjUnion_inj_right {s t₁ t₂ : Finset α} (h₁ : Disjoint s t₁) (h₂ : Disjoint s t₂) :
    s.disjUnion t₁ h₁ = s.disjUnion t₂ h₂ ↔ t₁ = t₂ := by
  simp [← val_inj, Multiset.add_right_inj]

@[simp]
/--
theorem `empty_disjUnion` / 定理 `empty_disjUnion`

English:
theorem empty_disjUnion
  given: (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left)
  proof: eq_of_veq Multiset.zero_add _

@[simp]

中文:
定理 empty_disjUnion
  条件: (t : 有限集 α) (h : Disjoint ∅ t := disjoint_bot_left)
  证明: eq_of_veq Multiset.zero_add _

@[simp]

Depends on / 依赖: disjoint_bot_left
-/
theorem empty_disjUnion (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left) :
    disjUnion ∅ t h = t :=
eq_of_veq Multiset.zero_add _

@[simp]
/--
theorem `disjUnion_empty` / 定理 `disjUnion_empty`

English:
theorem disjUnion_empty
  given: (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right)
  proof: eq_of_veq Multiset.add_zero _

中文:
定理 disjUnion_empty
  条件: (s : 有限集 α) (h : Disjoint s ∅ := disjoint_bot_right)
  证明: eq_of_veq Multiset.add_zero _

Depends on / 依赖: disjoint_bot_right
-/
theorem disjUnion_empty (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right) :
    disjUnion s ∅ h = s :=
eq_of_veq Multiset.add_zero _

/--
theorem `singleton_disjUnion` / 定理 `singleton_disjUnion`

English:
theorem singleton_disjUnion
  given: (a : α) (t : Finset α) (h : Disjoint {a} t)
  proof: eq_of_veq Multiset.singleton_add _ _

中文:
定理 singleton_disjUnion
  条件: (a : α) (t : 有限集 α) (h : Disjoint {a} t)
  证明: eq_of_veq Multiset.singleton_add _ _

Depends on / 依赖: Multiset, Multiset.singleton_add, eq_of_veq, singleton_add
-/
theorem singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) :
    disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h) :=
eq_of_veq Multiset.singleton_add _ _

/--
theorem `disjUnion_singleton` / 定理 `disjUnion_singleton`

English:
theorem disjUnion_singleton
  given: (s : Finset α) (a : α) (h : Disjoint s {a})
  proof: by
  rw [disjUnion_comm]; rw [singleton_disjUnion]

中文:
定理 disjUnion_singleton
  条件: (s : 有限集 α) (a : α) (h : Disjoint s {a})
  证明: by
  rw [disjUnion_comm]; rw [singleton_disjUnion]

Depends on / 依赖: disjUnion_comm, singleton_disjUnion
-/
theorem disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) :
    disjUnion s {a} h = cons a s (disjoint_singleton_right.mp h) := by
  rw [disjUnion_comm]; rw [singleton_disjUnion]

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t u v : Finset α} {a b : α} {f : α -> β}

@[simp, grind =]
/--
theorem `disjoint_insert_left` / 定理 `disjoint_insert_left`

English:
theorem disjoint_insert_left
  statement: Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
  proof: by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]

@[simp, grind =]

中文:
定理 disjoint_insert_left
  结论: Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t
  证明: by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]

@[simp, grind =]

Depends on / 依赖: disjoint_left, forall_and, forall_eq, mem_insert, or_imp
-/
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]

@[simp, grind =]
/--
theorem `disjoint_insert_right` / 定理 `disjoint_insert_right`

English:
theorem disjoint_insert_right
  statement: Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
  proof: disjoint_comm.trans by rw [disjoint_insert_left, _root_.disjoint_comm]

中文:
定理 disjoint_insert_right
  结论: Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t
  证明: disjoint_comm.trans by rw [disjoint_insert_left, _root_.disjoint_comm]

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, disjoint_comm.trans, disjoint_insert_left
-/
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
disjoint_comm.trans by rw [disjoint_insert_left, _root_.disjoint_comm]

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
/--
theorem `disjoint_toFinset` / 定理 `disjoint_toFinset`

English:
theorem disjoint_toFinset
  given: {m1 m2 : Multiset α}
  proof: by
  simp [disjoint_left, Finset.disjoint_left]

中文:
定理 disjoint_toFinset
  条件: {m1 m2 : Multiset α}
  证明: by
  simp [disjoint_left, Finset.disjoint_left]

Depends on / 依赖: Finset, Finset.disjoint_left, disjoint_left
-/
theorem disjoint_toFinset {m1 m2 : Multiset α} :
    _root_.Disjoint m1.toFinset m2.toFinset ↔ Disjoint m1 m2 := by
  simp [disjoint_left, Finset.disjoint_left]

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
/--
theorem `disjoint_toFinset_iff_disjoint` / 定理 `disjoint_toFinset_iff_disjoint`

English:
theorem disjoint_toFinset_iff_disjoint
  statement: _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l'
  proof: Multiset.disjoint_toFinset.trans (Multiset.coe_disjoint _ _)

中文:
定理 disjoint_toFinset_iff_disjoint
  结论: _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l'
  证明: Multiset.disjoint_toFinset.trans (Multiset.coe_disjoint _ _)

Depends on / 依赖: Multiset, Multiset.coe_disjoint, Multiset.disjoint_toFinset.trans, coe_disjoint, disjoint_toFinset
-/
theorem disjoint_toFinset_iff_disjoint : _root_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset.trans (Multiset.coe_disjoint _ _)

end List
