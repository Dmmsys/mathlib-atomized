/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.FinsetOps

/-!
# Lattice structure on finite sets

This file puts a lattice structure on finite sets using the union and intersection operators.

For `Finset α`, where `α` is a lattice, see also `Mathlib/Data/Finset/Lattice/Fold.lean`.

## Main declarations

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`Mathlib/Order/Lattice.lean`. For the lattice structure on finsets, `⊥` is called `bot` with
`⊥ = ∅` and `⊤` is called `top` with `⊤ = univ`.


## Implementation Notes

All the theorems and instances expect `DecidableEq` instance for `α`

## Tags

finite sets, finset

-/

public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/

section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Union (Finset α)
  body: ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

中文:
实例 :
  签名: 并集 (有限集 α)
  定义体: ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

Depends on / 依赖: ndunion
-/
instance : Union (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inter (Finset α)
  body: ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

中文:
实例 :
  签名: 交集 (有限集 α)
  定义体: ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

Depends on / 依赖: ndinter
-/
instance : Inter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (Finset α)
  body: (· union ·)
  sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
le_sup_left := fun _ _ _ h => mem_ndunion.2 Or.inl h
le_sup_right := fun _ _ _ h => mem_ndunion.2 Or.inr h
  inf := (· inter ·)
  le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
  inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
  inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2

@[simp]

中文:
实例 :
  签名: 格 (有限集 α)
  定义体: (· union ·)
  sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
le_sup_left := fun _ _ _ h => mem_ndunion.2 Or.inl h
le_sup_right := fun _ _ _ h => mem_ndunion.2 Or.inr h
  inf := (· inter ·)
  le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
  inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
  inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2

@[simp]
-/
instance : Lattice (Finset α) where
  sup := (· union ·)
  sup_le := fun _ _ _ hs ht _ ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
le_sup_left := fun _ _ _ h => mem_ndunion.2 Or.inl h
le_sup_right := fun _ _ _ h => mem_ndunion.2 Or.inr h
  inf := (· inter ·)
  le_inf := fun _ _ _ ht hu _ h => mem_ndinter.2 ⟨ht h, hu h⟩
  inf_le_left := fun _ _ _ h => (mem_ndinter.1 h).1
  inf_le_right := fun _ _ _ h => (mem_ndinter.1 h).2

@[simp]
/--
theorem `sup_eq_union'` / 定理 `sup_eq_union'`

English:
theorem sup_eq_union'
  statement: (Max.max : Finset α -> Finset α -> Finset α) = Union.union
  proof: rfl

@[grind =]

中文:
定理 sup_eq_union'
  结论: (最大值.最大值 : 有限集 α -> 有限集 α -> 有限集 α) = 并集.union
  证明: rfl

@[grind =]
-/
theorem sup_eq_union' : (Max.max : Finset α -> Finset α -> Finset α) = Union.union :=
  rfl

@[grind =]
/--
theorem `sup_eq_union` / 定理 `sup_eq_union`

English:
theorem sup_eq_union
  given: {s t : Finset α}
  statement: s ⊔ t = s union t
  proof: rfl

@[simp]

中文:
定理 sup_eq_union
  条件: {s t : 有限集 α}
  结论: s ⊔ t = s union t
  证明: rfl

@[simp]
-/
theorem sup_eq_union {s t : Finset α} : s ⊔ t = s union t :=
  rfl

@[simp]
/--
theorem `inf_eq_inter'` / 定理 `inf_eq_inter'`

English:
theorem inf_eq_inter'
  statement: (Min.min : Finset α -> Finset α -> Finset α) = Inter.inter
  proof: rfl

@[grind =]

中文:
定理 inf_eq_inter'
  结论: (最小值.最小值 : 有限集 α -> 有限集 α -> 有限集 α) = 交集.inter
  证明: rfl

@[grind =]
-/
theorem inf_eq_inter' : (Min.min : Finset α -> Finset α -> Finset α) = Inter.inter :=
  rfl

@[grind =]
/--
theorem `inf_eq_inter` / 定理 `inf_eq_inter`

English:
theorem inf_eq_inter
  given: {s t : Finset α}
  statement: s ⊓ t = s inter t
  proof: rfl

中文:
定理 inf_eq_inter
  条件: {s t : 有限集 α}
  结论: s ⊓ t = s inter t
  证明: rfl
-/
theorem inf_eq_inter {s t : Finset α} : s ⊓ t = s inter t :=
  rfl


/--
theorem `union_val_nd` / 定理 `union_val_nd`

English:
theorem union_val_nd
  given: (s t : Finset α)
  statement: (s union t).1 = ndunion s.1 t.1
  proof: rfl

@[simp]

中文:
定理 union_val_nd
  条件: (s t : 有限集 α)
  结论: (s union t).1 = ndunion s.1 t.1
  证明: rfl

@[simp]
-/
theorem union_val_nd (s t : Finset α) : (s union t).1 = ndunion s.1 t.1 :=
  rfl

@[simp]
/--
theorem `union_val` / 定理 `union_val`

English:
theorem union_val
  given: (s t : Finset α)
  statement: (s union t).1 = s.1 union t.1
  proof: ndunion_eq_union s.2

@[simp, grind =]

中文:
定理 union_val
  条件: (s t : 有限集 α)
  结论: (s union t).1 = s.1 union t.1
  证明: ndunion_eq_union s.2

@[simp, grind =]

Depends on / 依赖: ndunion_eq_union
-/
theorem union_val (s t : Finset α) : (s union t).1 = s.1 union t.1 :=
  ndunion_eq_union s.2

@[simp, grind =]
/--
theorem `mem_union` / 定理 `mem_union`

English:
theorem mem_union
  statement: a in s union t ↔ a in s ∨ a in t
  proof: mem_ndunion

中文:
定理 mem_union
  结论: a in s union t ↔ a in s ∨ a in t
  证明: mem_ndunion

Depends on / 依赖: mem_ndunion
-/
theorem mem_union : a in s union t ↔ a in s ∨ a in t :=
  mem_ndunion

/--
theorem `mem_union_left` / 定理 `mem_union_left`

English:
theorem mem_union_left
  given: (t : Finset α) (h : a in s)
  statement: a in s union t
  proof: mem_union.2 Or.inl h

中文:
定理 mem_union_left
  条件: (t : 有限集 α) (h : a in s)
  结论: a in s union t
  证明: mem_union.2 Or.inl h

Depends on / 依赖: Or.inl, mem_union
-/
theorem mem_union_left (t : Finset α) (h : a in s) : a in s union t :=
mem_union.2 Or.inl h

/--
theorem `mem_union_right` / 定理 `mem_union_right`

English:
theorem mem_union_right
  given: (s : Finset α) (h : a in t)
  statement: a in s union t
  proof: mem_union.2 Or.inr h

中文:
定理 mem_union_right
  条件: (s : 有限集 α) (h : a in t)
  结论: a in s union t
  证明: mem_union.2 Or.inr h

Depends on / 依赖: Or.inr, mem_union
-/
theorem mem_union_right (s : Finset α) (h : a in t) : a in s union t :=
mem_union.2 Or.inr h

/--
theorem `forall_mem_union` / 定理 `forall_mem_union`

English:
theorem forall_mem_union
  given: {p : α -> Prop}
  statement: (forall a in s union t, p a) ↔ (forall a in s, p a) ∧ forall a in t, p a
  proof: by
  grind

中文:
定理 对任意_mem_union
  条件: {p : α -> 命题}
  结论: (对任意 a in s union t, p a) ↔ (对任意 a in s, p a) ∧ 对任意 a in t, p a
  证明: by
  grind
-/
theorem forall_mem_union {p : α -> Prop} : (forall a in s union t, p a) ↔ (forall a in s, p a) ∧ forall a in t, p a := by
  grind

/--
theorem `notMem_union` / 定理 `notMem_union`

English:
theorem notMem_union
  statement: a ∉ s union t ↔ a ∉ s ∧ a ∉ t
  proof: by rw [mem_union, not_or]

@[simp, norm_cast]

中文:
定理 notMem_union
  结论: a ∉ s union t ↔ a ∉ s ∧ a ∉ t
  证明: by rw [mem_union, not_or]

@[simp, norm_cast]

Depends on / 依赖: mem_union, not_or
-/
theorem notMem_union : a ∉ s union t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or]

@[simp, norm_cast]
/--
theorem `coe_union` / 定理 `coe_union`

English:
theorem coe_union
  given: (s₁ s₂ : Finset α)
  statement: ↑(s₁ union s₂) = (s₁ union s₂ : Set α)
  proof: Set.ext fun _ => mem_union

中文:
定理 coe_union
  条件: (s₁ s₂ : 有限集 α)
  结论: ↑(s₁ union s₂) = (s₁ union s₂ : 集合 α)
  证明: Set.ext fun _ => mem_union

Depends on / 依赖: Set.ext, mem_union
-/
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ union s₂ : Set α) :=
  Set.ext fun _ => mem_union

/--
theorem `union_subset` / 定理 `union_subset`

English:
theorem union_subset
  given: (hs : s subseteq u)
  statement: t subseteq u -> s union t subseteq u
  proof: sup_le hs

中文:
定理 union_subset
  条件: (hs : s subseteq u)
  结论: t subseteq u -> s union t subseteq u
  证明: sup_le hs

Depends on / 依赖: sup_le
-/
theorem union_subset (hs : s subseteq u) : t subseteq u -> s union t subseteq u :=
  sup_le hs

/--
lemma `subset_union_left` / 引理 `subset_union_left`

English:
lemma subset_union_left
  statement: s₁ subseteq s₁ union s₂
  proof: fun _ => mem_union_left _

中文:
引理 subset_union_left
  结论: s₁ subseteq s₁ union s₂
  证明: fun _ => mem_union_left _
-/
@[simp] lemma subset_union_left : s₁ subseteq s₁ union s₂ := fun _ => mem_union_left _
/--
lemma `subset_union_right` / 引理 `subset_union_right`

English:
lemma subset_union_right
  statement: s₂ subseteq s₁ union s₂
  proof: fun _ => mem_union_right _

@[gcongr]

中文:
引理 subset_union_right
  结论: s₂ subseteq s₁ union s₂
  证明: fun _ => mem_union_right _

@[gcongr]
-/
@[simp] lemma subset_union_right : s₂ subseteq s₁ union s₂ := fun _ => mem_union_right _

@[gcongr]
/--
theorem `union_subset_union` / 定理 `union_subset_union`

English:
theorem union_subset_union
  given: (hsu : s subseteq u) (htv : t subseteq v)
  statement: s union t subseteq u union v
  proof: sup_le_sup hsu htv

中文:
定理 union_subset_union
  条件: (hsu : s subseteq u) (htv : t subseteq v)
  结论: s union t subseteq u union v
  证明: sup_le_sup hsu htv

Depends on / 依赖: sup_le_sup
-/
theorem union_subset_union (hsu : s subseteq u) (htv : t subseteq v) : s union t subseteq u union v :=
  sup_le_sup hsu htv

/--
theorem `union_subset_union_left` / 定理 `union_subset_union_left`

English:
theorem union_subset_union_left
  given: (h : s₁ subseteq s₂)
  statement: s₁ union t subseteq s₂ union t
  proof: union_subset_union h Subset.rfl

中文:
定理 union_subset_union_left
  条件: (h : s₁ subseteq s₂)
  结论: s₁ union t subseteq s₂ union t
  证明: union_subset_union h Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, union_subset_union
-/
theorem union_subset_union_left (h : s₁ subseteq s₂) : s₁ union t subseteq s₂ union t :=
  union_subset_union h Subset.rfl

/--
theorem `union_subset_union_right` / 定理 `union_subset_union_right`

English:
theorem union_subset_union_right
  given: (h : t₁ subseteq t₂)
  statement: s union t₁ subseteq s union t₂
  proof: union_subset_union Subset.rfl h

中文:
定理 union_subset_union_right
  条件: (h : t₁ subseteq t₂)
  结论: s union t₁ subseteq s union t₂
  证明: union_subset_union Subset.rfl h

Depends on / 依赖: Subset, Subset.rfl, union_subset_union
-/
theorem union_subset_union_right (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂ :=
  union_subset_union Subset.rfl h

/--
theorem `union_comm` / 定理 `union_comm`

English:
theorem union_comm
  given: (s₁ s₂ : Finset α)
  statement: s₁ union s₂ = s₂ union s₁
  proof: sup_comm _ _

中文:
定理 union_comm
  条件: (s₁ s₂ : 有限集 α)
  结论: s₁ union s₂ = s₂ union s₁
  证明: sup_comm _ _

Depends on / 依赖: sup_comm
-/
theorem union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ union s₁ := sup_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Commutative (α := Finset α) (· union ·)
  body: ⟨union_comm⟩

@[simp]

中文:
实例 :
  签名: Std.交换 (α := 有限集 α) (· union ·)
  定义体: ⟨union_comm⟩

@[simp]

Depends on / 依赖: Finset
-/
instance : Std.Commutative (α := Finset α) (· union ·) :=
  ⟨union_comm⟩

@[simp]
/--
theorem `union_assoc` / 定理 `union_assoc`

English:
theorem union_assoc
  given: (s₁ s₂ s₃ : Finset α)
  statement: s₁ union s₂ union s₃ = s₁ union (s₂ union s₃)
  proof: sup_assoc _ _ _

中文:
定理 union_assoc
  条件: (s₁ s₂ s₃ : 有限集 α)
  结论: s₁ union s₂ union s₃ = s₁ union (s₂ union s₃)
  证明: sup_assoc _ _ _

Depends on / 依赖: sup_assoc
-/
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ union s₃ = s₁ union (s₂ union s₃) := sup_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Associative (α := Finset α) (· union ·)
  body: ⟨union_assoc⟩

@[simp]

中文:
实例 :
  签名: Std.结合 (α := 有限集 α) (· union ·)
  定义体: ⟨union_assoc⟩

@[simp]

Depends on / 依赖: Finset
-/
instance : Std.Associative (α := Finset α) (· union ·) :=
  ⟨union_assoc⟩

@[simp]
/--
theorem `union_idempotent` / 定理 `union_idempotent`

English:
theorem union_idempotent
  given: (s : Finset α)
  statement: s union s = s
  proof: sup_idem _

中文:
定理 union_idempotent
  条件: (s : 有限集 α)
  结论: s union s = s
  证明: sup_idem _

Depends on / 依赖: sup_idem
-/
theorem union_idempotent (s : Finset α) : s union s = s := sup_idem _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.IdempotentOp (α := Finset α) (· union ·)
  body: ⟨union_idempotent⟩

中文:
实例 :
  签名: Std.IdempotentOp (α := 有限集 α) (· union ·)
  定义体: ⟨union_idempotent⟩

Depends on / 依赖: Finset
-/
instance : Std.IdempotentOp (α := Finset α) (· union ·) :=
  ⟨union_idempotent⟩

/--
theorem `union_subset_left` / 定理 `union_subset_left`

English:
theorem union_subset_left
  given: (h : s union t subseteq u)
  statement: s subseteq u
  proof: subset_union_left.trans h

中文:
定理 union_subset_left
  条件: (h : s union t subseteq u)
  结论: s subseteq u
  证明: subset_union_left.trans h

Depends on / 依赖: subset_union_left, subset_union_left.trans
-/
theorem union_subset_left (h : s union t subseteq u) : s subseteq u :=
  subset_union_left.trans h

/--
theorem `union_subset_right` / 定理 `union_subset_right`

English:
theorem union_subset_right
  given: {s t u : Finset α} (h : s union t subseteq u)
  statement: t subseteq u
  proof: Subset.trans subset_union_right h

中文:
定理 union_subset_right
  条件: {s t u : 有限集 α} (h : s union t subseteq u)
  结论: t subseteq u
  证明: Subset.trans subset_union_right h

Depends on / 依赖: Subset, Subset.trans, subset_union_right
-/
theorem union_subset_right {s t u : Finset α} (h : s union t subseteq u) : t subseteq u :=
  Subset.trans subset_union_right h

/--
theorem `union_left_comm` / 定理 `union_left_comm`

English:
theorem union_left_comm
  given: (s t u : Finset α)
  statement: s union (t union u) = t union (s union u)
  proof: ext fun _ => by simp only [mem_union, or_left_comm]

中文:
定理 union_left_comm
  条件: (s t u : 有限集 α)
  结论: s union (t union u) = t union (s union u)
  证明: ext fun _ => by simp only [mem_union, or_left_comm]

Depends on / 依赖: mem_union, or_left_comm
-/
theorem union_left_comm (s t u : Finset α) : s union (t union u) = t union (s union u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]

/--
theorem `union_right_comm` / 定理 `union_right_comm`

English:
theorem union_right_comm
  given: (s t u : Finset α)
  statement: s union t union u = s union u union t
  proof: ext fun x => by simp only [mem_union, or_assoc, @or_comm (x in t)]

中文:
定理 union_right_comm
  条件: (s t u : 有限集 α)
  结论: s union t union u = s union u union t
  证明: ext fun x => by simp only [mem_union, or_assoc, @or_comm (x in t)]

Depends on / 依赖: mem_union, or_assoc, or_comm
-/
theorem union_right_comm (s t u : Finset α) : s union t union u = s union u union t :=
  ext fun x => by simp only [mem_union, or_assoc, @or_comm (x in t)]

/--
theorem `union_self` / 定理 `union_self`

English:
theorem union_self
  given: (s : Finset α)
  statement: s union s = s
  proof: union_idempotent s

中文:
定理 union_self
  条件: (s : 有限集 α)
  结论: s union s = s
  证明: union_idempotent s

Depends on / 依赖: union_idempotent
-/
theorem union_self (s : Finset α) : s union s = s :=
  union_idempotent s

/--
lemma `union_eq_left` / 引理 `union_eq_left`

English:
lemma union_eq_left
  statement: s union t = s ↔ t subseteq s
  proof: sup_eq_left

中文:
引理 union_eq_left
  结论: s union t = s ↔ t subseteq s
  证明: sup_eq_left
-/
@[simp] lemma union_eq_left : s union t = s ↔ t subseteq s := sup_eq_left

/--
lemma `left_eq_union` / 引理 `left_eq_union`

English:
lemma left_eq_union
  statement: s = s union t ↔ t subseteq s
  proof: by rw [eq_comm, union_eq_left]

中文:
引理 left_eq_union
  结论: s = s union t ↔ t subseteq s
  证明: by rw [eq_comm, union_eq_left]
-/
@[simp] lemma left_eq_union : s = s union t ↔ t subseteq s := by rw [eq_comm, union_eq_left]

/--
lemma `union_eq_right` / 引理 `union_eq_right`

English:
lemma union_eq_right
  statement: s union t = t ↔ s subseteq t
  proof: sup_eq_right

中文:
引理 union_eq_right
  结论: s union t = t ↔ s subseteq t
  证明: sup_eq_right
-/
@[simp] lemma union_eq_right : s union t = t ↔ s subseteq t := sup_eq_right

/--
lemma `right_eq_union` / 引理 `right_eq_union`

English:
lemma right_eq_union
  statement: s = t union s ↔ t subseteq s
  proof: by rw [eq_comm, union_eq_right]

中文:
引理 right_eq_union
  结论: s = t union s ↔ t subseteq s
  证明: by rw [eq_comm, union_eq_right]
-/
@[simp] lemma right_eq_union : s = t union s ↔ t subseteq s := by rw [eq_comm, union_eq_right]

/--
theorem `union_congr_left` / 定理 `union_congr_left`

English:
theorem union_congr_left
  given: (ht : t subseteq s union u) (hu : u subseteq s union t)
  statement: s union t = s union u
  proof: sup_congr_left ht hu

中文:
定理 union_congr_left
  条件: (ht : t subseteq s union u) (hu : u subseteq s union t)
  结论: s union t = s union u
  证明: sup_congr_left ht hu

Depends on / 依赖: sup_congr_left
-/
theorem union_congr_left (ht : t subseteq s union u) (hu : u subseteq s union t) : s union t = s union u :=
  sup_congr_left ht hu

/--
theorem `union_congr_right` / 定理 `union_congr_right`

English:
theorem union_congr_right
  given: (hs : s subseteq t union u) (ht : t subseteq s union u)
  statement: s union u = t union u
  proof: sup_congr_right hs ht

中文:
定理 union_congr_right
  条件: (hs : s subseteq t union u) (ht : t subseteq s union u)
  结论: s union u = t union u
  证明: sup_congr_right hs ht

Depends on / 依赖: sup_congr_right
-/
theorem union_congr_right (hs : s subseteq t union u) (ht : t subseteq s union u) : s union u = t union u :=
  sup_congr_right hs ht

/--
theorem `union_eq_union_iff_left` / 定理 `union_eq_union_iff_left`

English:
theorem union_eq_union_iff_left
  statement: s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t
  proof: sup_eq_sup_iff_left

中文:
定理 union_eq_union_iff_left
  结论: s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t
  证明: sup_eq_sup_iff_left

Depends on / 依赖: sup_eq_sup_iff_left
-/
theorem union_eq_union_iff_left : s union t = s union u ↔ t subseteq s union u ∧ u subseteq s union t :=
  sup_eq_sup_iff_left

/--
theorem `union_eq_union_iff_right` / 定理 `union_eq_union_iff_right`

English:
theorem union_eq_union_iff_right
  statement: s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u
  proof: sup_eq_sup_iff_right

中文:
定理 union_eq_union_iff_right
  结论: s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u
  证明: sup_eq_sup_iff_right

Depends on / 依赖: sup_eq_sup_iff_right
-/
theorem union_eq_union_iff_right : s union u = t union u ↔ s subseteq t union u ∧ t subseteq s union u :=
  sup_eq_sup_iff_right

/--
theorem `inter_val_nd` / 定理 `inter_val_nd`

English:
theorem inter_val_nd
  given: (s₁ s₂ : Finset α)
  statement: (s₁ inter s₂).1 = ndinter s₁.1 s₂.1
  proof: rfl

@[simp]

中文:
定理 inter_val_nd
  条件: (s₁ s₂ : 有限集 α)
  结论: (s₁ inter s₂).1 = ndinter s₁.1 s₂.1
  证明: rfl

@[simp]
-/
theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl

@[simp]
/--
theorem `inter_val` / 定理 `inter_val`

English:
theorem inter_val
  given: (s₁ s₂ : Finset α)
  statement: (s₁ inter s₂).1 = s₁.1 inter s₂.1
  proof: ndinter_eq_inter s₁.2

@[simp, grind =]

中文:
定理 inter_val
  条件: (s₁ s₂ : 有限集 α)
  结论: (s₁ inter s₂).1 = s₁.1 inter s₂.1
  证明: ndinter_eq_inter s₁.2

@[simp, grind =]

Depends on / 依赖: ndinter_eq_inter
-/
theorem inter_val (s₁ s₂ : Finset α) : (s₁ inter s₂).1 = s₁.1 inter s₂.1 :=
  ndinter_eq_inter s₁.2

@[simp, grind =]
/--
theorem `mem_inter` / 定理 `mem_inter`

English:
theorem mem_inter
  given: {a : α} {s₁ s₂ : Finset α}
  statement: a in s₁ inter s₂ ↔ a in s₁ ∧ a in s₂
  proof: mem_ndinter

中文:
定理 mem_inter
  条件: {a : α} {s₁ s₂ : 有限集 α}
  结论: a in s₁ inter s₂ ↔ a in s₁ ∧ a in s₂
  证明: mem_ndinter

Depends on / 依赖: mem_ndinter
-/
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s₂ ↔ a in s₁ ∧ a in s₂ :=
  mem_ndinter

/--
theorem `mem_of_mem_inter_left` / 定理 `mem_of_mem_inter_left`

English:
theorem mem_of_mem_inter_left
  given: {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂)
  statement: a in s₁
  proof: (mem_inter.1 h).1

中文:
定理 mem_of_mem_inter_left
  条件: {a : α} {s₁ s₂ : 有限集 α} (h : a in s₁ inter s₂)
  结论: a in s₁
  证明: (mem_inter.1 h).1

Depends on / 依赖: mem_inter
-/
theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂) : a in s₁ :=
  (mem_inter.1 h).1

/--
theorem `mem_of_mem_inter_right` / 定理 `mem_of_mem_inter_right`

English:
theorem mem_of_mem_inter_right
  given: {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂)
  statement: a in s₂
  proof: (mem_inter.1 h).2

中文:
定理 mem_of_mem_inter_right
  条件: {a : α} {s₁ s₂ : 有限集 α} (h : a in s₁ inter s₂)
  结论: a in s₂
  证明: (mem_inter.1 h).2

Depends on / 依赖: mem_inter
-/
theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a in s₁ inter s₂) : a in s₂ :=
  (mem_inter.1 h).2

/--
theorem `mem_inter_of_mem` / 定理 `mem_inter_of_mem`

English:
theorem mem_inter_of_mem
  given: {a : α} {s₁ s₂ : Finset α}
  statement: a in s₁ -> a in s₂ -> a in s₁ inter s₂
  proof: and_imp.1 mem_inter.2

中文:
定理 mem_inter_of_mem
  条件: {a : α} {s₁ s₂ : 有限集 α}
  结论: a in s₁ -> a in s₂ -> a in s₁ inter s₂
  证明: and_imp.1 mem_inter.2

Depends on / 依赖: and_imp, mem_inter
-/
theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a in s₁ -> a in s₂ -> a in s₁ inter s₂ :=
  and_imp.1 mem_inter.2

/--
lemma `inter_subset_left` / 引理 `inter_subset_left`

English:
lemma inter_subset_left
  statement: s₁ inter s₂ subseteq s₁
  proof: fun _ => mem_of_mem_inter_left

中文:
引理 inter_subset_left
  结论: s₁ inter s₂ subseteq s₁
  证明: fun _ => mem_of_mem_inter_left
-/
@[simp] lemma inter_subset_left : s₁ inter s₂ subseteq s₁ := fun _ => mem_of_mem_inter_left
/--
lemma `inter_subset_right` / 引理 `inter_subset_right`

English:
lemma inter_subset_right
  statement: s₁ inter s₂ subseteq s₂
  proof: fun _ => mem_of_mem_inter_right

中文:
引理 inter_subset_right
  结论: s₁ inter s₂ subseteq s₂
  证明: fun _ => mem_of_mem_inter_right
-/
@[simp] lemma inter_subset_right : s₁ inter s₂ subseteq s₂ := fun _ => mem_of_mem_inter_right

/--
theorem `subset_inter` / 定理 `subset_inter`

English:
theorem subset_inter
  given: {s₁ s₂ u : Finset α}
  statement: s₁ subseteq s₂ -> s₁ subseteq u -> s₁ subseteq s₂ inter u
  proof: by grind

@[simp, norm_cast]

中文:
定理 subset_inter
  条件: {s₁ s₂ u : 有限集 α}
  结论: s₁ subseteq s₂ -> s₁ subseteq u -> s₁ subseteq s₂ inter u
  证明: by grind

@[simp, norm_cast]
-/
theorem subset_inter {s₁ s₂ u : Finset α} : s₁ subseteq s₂ -> s₁ subseteq u -> s₁ subseteq s₂ inter u := by grind

@[simp, norm_cast]
/--
theorem `coe_inter` / 定理 `coe_inter`

English:
theorem coe_inter
  given: (s₁ s₂ : Finset α)
  statement: ↑(s₁ inter s₂) = (s₁ inter s₂ : Set α)
  proof: Set.ext fun _ => mem_inter

@[simp]

中文:
定理 coe_inter
  条件: (s₁ s₂ : 有限集 α)
  结论: ↑(s₁ inter s₂) = (s₁ inter s₂ : 集合 α)
  证明: Set.ext fun _ => mem_inter

@[simp]

Depends on / 依赖: Set.ext, mem_inter
-/
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ inter s₂ : Set α) :=
  Set.ext fun _ => mem_inter

@[simp]
/--
theorem `union_inter_cancel_left` / 定理 `union_inter_cancel_left`

English:
theorem union_inter_cancel_left
  given: {s t : Finset α}
  statement: (s union t) inter s = s
  proof: by grind

@[simp]

中文:
定理 union_inter_cancel_left
  条件: {s t : 有限集 α}
  结论: (s union t) inter s = s
  证明: by grind

@[simp]
-/
theorem union_inter_cancel_left {s t : Finset α} : (s union t) inter s = s := by grind

@[simp]
/--
theorem `union_inter_cancel_right` / 定理 `union_inter_cancel_right`

English:
theorem union_inter_cancel_right
  given: {s t : Finset α}
  statement: (s union t) inter t = t
  proof: by grind

中文:
定理 union_inter_cancel_right
  条件: {s t : 有限集 α}
  结论: (s union t) inter t = t
  证明: by grind
-/
theorem union_inter_cancel_right {s t : Finset α} : (s union t) inter t = t := by grind

/--
theorem `inter_comm` / 定理 `inter_comm`

English:
theorem inter_comm
  given: (s₁ s₂ : Finset α)
  statement: s₁ inter s₂ = s₂ inter s₁
  proof: by grind

@[simp]

中文:
定理 inter_comm
  条件: (s₁ s₂ : 有限集 α)
  结论: s₁ inter s₂ = s₂ inter s₁
  证明: by grind

@[simp]
-/
theorem inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inter s₁ := by grind

@[simp]
/--
theorem `inter_assoc` / 定理 `inter_assoc`

English:
theorem inter_assoc
  given: (s₁ s₂ s₃ : Finset α)
  statement: s₁ inter s₂ inter s₃ = s₁ inter (s₂ inter s₃)
  proof: by grind

中文:
定理 inter_assoc
  条件: (s₁ s₂ s₃ : 有限集 α)
  结论: s₁ inter s₂ inter s₃ = s₁ inter (s₂ inter s₃)
  证明: by grind
-/
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ inter s₂ inter s₃ = s₁ inter (s₂ inter s₃) := by grind

/--
theorem `inter_left_comm` / 定理 `inter_left_comm`

English:
theorem inter_left_comm
  given: (s₁ s₂ s₃ : Finset α)
  statement: s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃)
  proof: by grind

中文:
定理 inter_left_comm
  条件: (s₁ s₂ s₃ : 有限集 α)
  结论: s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃)
  证明: by grind
-/
theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ inter (s₂ inter s₃) = s₂ inter (s₁ inter s₃) := by grind

/--
theorem `inter_right_comm` / 定理 `inter_right_comm`

English:
theorem inter_right_comm
  given: (s₁ s₂ s₃ : Finset α)
  statement: s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂
  proof: by grind

@[simp]

中文:
定理 inter_right_comm
  条件: (s₁ s₂ s₃ : 有限集 α)
  结论: s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂
  证明: by grind

@[simp]
-/
theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ inter s₂ inter s₃ = s₁ inter s₃ inter s₂ := by grind

@[simp]
/--
theorem `inter_self` / 定理 `inter_self`

English:
theorem inter_self
  given: (s : Finset α)
  statement: s inter s = s
  proof: ext fun _ => mem_inter.trans and_self_iff

@[simp]

中文:
定理 inter_self
  条件: (s : 有限集 α)
  结论: s inter s = s
  证明: ext fun _ => mem_inter.trans and_self_iff

@[simp]

Depends on / 依赖: and_self_iff, mem_inter, mem_inter.trans
-/
theorem inter_self (s : Finset α) : s inter s = s :=
ext fun _ => mem_inter.trans and_self_iff

@[simp]
/--
theorem `inter_union_self` / 定理 `inter_union_self`

English:
theorem inter_union_self
  given: (s t : Finset α)
  statement: s inter (t union s) = s
  proof: by
  rw [inter_comm]; rw [union_inter_cancel_right]

@[mono, gcongr]

中文:
定理 inter_union_self
  条件: (s t : 有限集 α)
  结论: s inter (t union s) = s
  证明: by
  rw [inter_comm]; rw [union_inter_cancel_right]

@[mono, gcongr]

Depends on / 依赖: inter_comm, union_inter_cancel_right
-/
theorem inter_union_self (s t : Finset α) : s inter (t union s) = s := by
  rw [inter_comm]; rw [union_inter_cancel_right]

@[mono, gcongr]
/--
theorem `inter_subset_inter` / 定理 `inter_subset_inter`

English:
theorem inter_subset_inter
  given: {x y s t : Finset α} (h : x subseteq y) (h' : s subseteq t)
  statement: x inter s subseteq y inter t
  proof: inf_le_inf h h'

中文:
定理 inter_subset_inter
  条件: {x y s t : 有限集 α} (h : x subseteq y) (h' : s subseteq t)
  结论: x inter s subseteq y inter t
  证明: inf_le_inf h h'

Depends on / 依赖: inf_le_inf
-/
theorem inter_subset_inter {x y s t : Finset α} (h : x subseteq y) (h' : s subseteq t) : x inter s subseteq y inter t :=
  inf_le_inf h h'

/--
theorem `inter_subset_inter_left` / 定理 `inter_subset_inter_left`

English:
theorem inter_subset_inter_left
  given: (h : t subseteq u)
  statement: s inter t subseteq s inter u
  proof: inter_subset_inter Subset.rfl h

中文:
定理 inter_subset_inter_left
  条件: (h : t subseteq u)
  结论: s inter t subseteq s inter u
  证明: inter_subset_inter Subset.rfl h

Depends on / 依赖: Subset, Subset.rfl, inter_subset_inter
-/
theorem inter_subset_inter_left (h : t subseteq u) : s inter t subseteq s inter u :=
  inter_subset_inter Subset.rfl h

/--
theorem `inter_subset_inter_right` / 定理 `inter_subset_inter_right`

English:
theorem inter_subset_inter_right
  given: (h : s subseteq t)
  statement: s inter u subseteq t inter u
  proof: inter_subset_inter h Subset.rfl

中文:
定理 inter_subset_inter_right
  条件: (h : s subseteq t)
  结论: s inter u subseteq t inter u
  证明: inter_subset_inter h Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, inter_subset_inter
-/
theorem inter_subset_inter_right (h : s subseteq t) : s inter u subseteq t inter u :=
  inter_subset_inter h Subset.rfl

/--
theorem `inter_subset_union` / 定理 `inter_subset_union`

English:
theorem inter_subset_union
  statement: s inter t subseteq s union t
  proof: inf_le_sup

中文:
定理 inter_subset_union
  结论: s inter t subseteq s union t
  证明: inf_le_sup

Depends on / 依赖: inf_le_sup
-/
theorem inter_subset_union : s inter t subseteq s union t :=
  inf_le_sup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice (Finset α)
  body: { le_sup_inf := fun a b c => by
      simp +contextual only
        [sup_eq_union, inf_eq_inter, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or, imp_true_iff, true_and, or_true] }

@[simp]

中文:
实例 :
  签名: Distrib格 (有限集 α)
  定义体: { le_sup_inf := fun a b c => by
      simp +contextual only
        [sup_eq_union, inf_eq_inter, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or, imp_true_iff, true_and, or_true] }

@[simp]

Depends on / 依赖: and_imp, contextual, imp_true_iff, inf_eq_inter, le_sup_inf, mem_inter, mem_union, or_imp, or_true, subset_iff, sup_eq_union, true_and, true_or
-/
instance : DistribLattice (Finset α) :=
  { le_sup_inf := fun a b c => by
      simp +contextual only
        [sup_eq_union, inf_eq_inter, subset_iff, mem_inter, mem_union, and_imp,
        or_imp, true_or, imp_true_iff, true_and, or_true] }

@[simp]
/--
theorem `union_left_idem` / 定理 `union_left_idem`

English:
theorem union_left_idem
  given: (s t : Finset α)
  statement: s union (s union t) = s union t
  proof: sup_left_idem _ _

中文:
定理 union_left_idem
  条件: (s t : 有限集 α)
  结论: s union (s union t) = s union t
  证明: sup_left_idem _ _

Depends on / 依赖: sup_left_idem
-/
theorem union_left_idem (s t : Finset α) : s union (s union t) = s union t := sup_left_idem _ _

/--
theorem `union_right_idem` / 定理 `union_right_idem`

English:
theorem union_right_idem
  given: (s t : Finset α)
  statement: s union t union t = s union t
  proof: sup_right_idem _ _

@[simp]

中文:
定理 union_right_idem
  条件: (s t : 有限集 α)
  结论: s union t union t = s union t
  证明: sup_right_idem _ _

@[simp]

Depends on / 依赖: sup_right_idem
-/
theorem union_right_idem (s t : Finset α) : s union t union t = s union t := sup_right_idem _ _

@[simp]
/--
theorem `inter_left_idem` / 定理 `inter_left_idem`

English:
theorem inter_left_idem
  given: (s t : Finset α)
  statement: s inter (s inter t) = s inter t
  proof: inf_left_idem _ _

中文:
定理 inter_left_idem
  条件: (s t : 有限集 α)
  结论: s inter (s inter t) = s inter t
  证明: inf_left_idem _ _

Depends on / 依赖: inf_left_idem
-/
theorem inter_left_idem (s t : Finset α) : s inter (s inter t) = s inter t := inf_left_idem _ _

/--
theorem `inter_right_idem` / 定理 `inter_right_idem`

English:
theorem inter_right_idem
  given: (s t : Finset α)
  statement: s inter t inter t = s inter t
  proof: inf_right_idem _ _

中文:
定理 inter_right_idem
  条件: (s t : 有限集 α)
  结论: s inter t inter t = s inter t
  证明: inf_right_idem _ _

Depends on / 依赖: inf_right_idem
-/
theorem inter_right_idem (s t : Finset α) : s inter t inter t = s inter t := inf_right_idem _ _

/--
theorem `inter_union_distrib_left` / 定理 `inter_union_distrib_left`

English:
theorem inter_union_distrib_left
  given: (s t u : Finset α)
  statement: s inter (t union u) = s inter t union s inter u
  proof: inf_sup_left _ _ _

中文:
定理 inter_union_distrib_left
  条件: (s t u : 有限集 α)
  结论: s inter (t union u) = s inter t union s inter u
  证明: inf_sup_left _ _ _

Depends on / 依赖: inf_sup_left
-/
theorem inter_union_distrib_left (s t u : Finset α) : s inter (t union u) = s inter t union s inter u :=
  inf_sup_left _ _ _

/--
theorem `union_inter_distrib_right` / 定理 `union_inter_distrib_right`

English:
theorem union_inter_distrib_right
  given: (s t u : Finset α)
  statement: (s union t) inter u = s inter u union t inter u
  proof: inf_sup_right _ _ _

中文:
定理 union_inter_distrib_right
  条件: (s t u : 有限集 α)
  结论: (s union t) inter u = s inter u union t inter u
  证明: inf_sup_right _ _ _

Depends on / 依赖: inf_sup_right
-/
theorem union_inter_distrib_right (s t u : Finset α) : (s union t) inter u = s inter u union t inter u :=
  inf_sup_right _ _ _

/--
theorem `union_inter_distrib_left` / 定理 `union_inter_distrib_left`

English:
theorem union_inter_distrib_left
  given: (s t u : Finset α)
  statement: s union t inter u = (s union t) inter (s union u)
  proof: sup_inf_left _ _ _

中文:
定理 union_inter_distrib_left
  条件: (s t u : 有限集 α)
  结论: s union t inter u = (s union t) inter (s union u)
  证明: sup_inf_left _ _ _

Depends on / 依赖: sup_inf_left
-/
theorem union_inter_distrib_left (s t u : Finset α) : s union t inter u = (s union t) inter (s union u) :=
  sup_inf_left _ _ _

/--
theorem `inter_union_distrib_right` / 定理 `inter_union_distrib_right`

English:
theorem inter_union_distrib_right
  given: (s t u : Finset α)
  statement: s inter t union u = (s union u) inter (t union u)
  proof: sup_inf_right _ _ _

中文:
定理 inter_union_distrib_right
  条件: (s t u : 有限集 α)
  结论: s inter t union u = (s union u) inter (t union u)
  证明: sup_inf_right _ _ _

Depends on / 依赖: sup_inf_right
-/
theorem inter_union_distrib_right (s t u : Finset α) : s inter t union u = (s union u) inter (t union u) :=
  sup_inf_right _ _ _

/--
theorem `union_union_distrib_left` / 定理 `union_union_distrib_left`

English:
theorem union_union_distrib_left
  given: (s t u : Finset α)
  statement: s union (t union u) = s union t union (s union u)
  proof: sup_sup_distrib_left _ _ _

中文:
定理 union_union_distrib_left
  条件: (s t u : 有限集 α)
  结论: s union (t union u) = s union t union (s union u)
  证明: sup_sup_distrib_left _ _ _

Depends on / 依赖: sup_sup_distrib_left
-/
theorem union_union_distrib_left (s t u : Finset α) : s union (t union u) = s union t union (s union u) :=
  sup_sup_distrib_left _ _ _

/--
theorem `union_union_distrib_right` / 定理 `union_union_distrib_right`

English:
theorem union_union_distrib_right
  given: (s t u : Finset α)
  statement: s union t union u = s union u union (t union u)
  proof: sup_sup_distrib_right _ _ _

中文:
定理 union_union_distrib_right
  条件: (s t u : 有限集 α)
  结论: s union t union u = s union u union (t union u)
  证明: sup_sup_distrib_right _ _ _

Depends on / 依赖: sup_sup_distrib_right
-/
theorem union_union_distrib_right (s t u : Finset α) : s union t union u = s union u union (t union u) :=
  sup_sup_distrib_right _ _ _

/--
theorem `inter_inter_distrib_left` / 定理 `inter_inter_distrib_left`

English:
theorem inter_inter_distrib_left
  given: (s t u : Finset α)
  statement: s inter (t inter u) = s inter t inter (s inter u)
  proof: inf_inf_distrib_left _ _ _

中文:
定理 inter_inter_distrib_left
  条件: (s t u : 有限集 α)
  结论: s inter (t inter u) = s inter t inter (s inter u)
  证明: inf_inf_distrib_left _ _ _

Depends on / 依赖: inf_inf_distrib_left
-/
theorem inter_inter_distrib_left (s t u : Finset α) : s inter (t inter u) = s inter t inter (s inter u) :=
  inf_inf_distrib_left _ _ _

/--
theorem `inter_inter_distrib_right` / 定理 `inter_inter_distrib_right`

English:
theorem inter_inter_distrib_right
  given: (s t u : Finset α)
  statement: s inter t inter u = s inter u inter (t inter u)
  proof: inf_inf_distrib_right _ _ _

中文:
定理 inter_inter_distrib_right
  条件: (s t u : 有限集 α)
  结论: s inter t inter u = s inter u inter (t inter u)
  证明: inf_inf_distrib_right _ _ _

Depends on / 依赖: inf_inf_distrib_right
-/
theorem inter_inter_distrib_right (s t u : Finset α) : s inter t inter u = s inter u inter (t inter u) :=
  inf_inf_distrib_right _ _ _

/--
theorem `union_union_union_comm` / 定理 `union_union_union_comm`

English:
theorem union_union_union_comm
  given: (s t u v : Finset α)
  statement: s union t union (u union v) = s union u union (t union v)
  proof: sup_sup_sup_comm _ _ _ _

中文:
定理 union_union_union_comm
  条件: (s t u v : 有限集 α)
  结论: s union t union (u union v) = s union u union (t union v)
  证明: sup_sup_sup_comm _ _ _ _

Depends on / 依赖: sup_sup_sup_comm
-/
theorem union_union_union_comm (s t u v : Finset α) : s union t union (u union v) = s union u union (t union v) :=
  sup_sup_sup_comm _ _ _ _

/--
theorem `inter_inter_inter_comm` / 定理 `inter_inter_inter_comm`

English:
theorem inter_inter_inter_comm
  given: (s t u v : Finset α)
  statement: s inter t inter (u inter v) = s inter u inter (t inter v)
  proof: inf_inf_inf_comm _ _ _ _

中文:
定理 inter_inter_inter_comm
  条件: (s t u v : 有限集 α)
  结论: s inter t inter (u inter v) = s inter u inter (t inter v)
  证明: inf_inf_inf_comm _ _ _ _

Depends on / 依赖: inf_inf_inf_comm
-/
theorem inter_inter_inter_comm (s t u v : Finset α) : s inter t inter (u inter v) = s inter u inter (t inter v) :=
  inf_inf_inf_comm _ _ _ _

/--
theorem `union_subset_iff` / 定理 `union_subset_iff`

English:
theorem union_subset_iff
  statement: s union t subseteq u ↔ s subseteq u ∧ t subseteq u
  proof: (sup_le_iff : s ⊔ t <= u ↔ s <= u ∧ t <= u)

中文:
定理 union_subset_iff
  结论: s union t subseteq u ↔ s subseteq u ∧ t subseteq u
  证明: (sup_le_iff : s ⊔ t <= u ↔ s <= u ∧ t <= u)

Depends on / 依赖: sup_le_iff
-/
theorem union_subset_iff : s union t subseteq u ↔ s subseteq u ∧ t subseteq u :=
  (sup_le_iff : s ⊔ t <= u ↔ s <= u ∧ t <= u)

/--
theorem `subset_inter_iff` / 定理 `subset_inter_iff`

English:
theorem subset_inter_iff
  statement: s subseteq t inter u ↔ s subseteq t ∧ s subseteq u
  proof: (le_inf_iff : s <= t ⊓ u ↔ s <= t ∧ s <= u)

中文:
定理 subset_inter_iff
  结论: s subseteq t inter u ↔ s subseteq t ∧ s subseteq u
  证明: (le_inf_iff : s <= t ⊓ u ↔ s <= t ∧ s <= u)

Depends on / 依赖: le_inf_iff
-/
theorem subset_inter_iff : s subseteq t inter u ↔ s subseteq t ∧ s subseteq u :=
  (le_inf_iff : s <= t ⊓ u ↔ s <= t ∧ s <= u)

/--
lemma `inter_eq_left` / 引理 `inter_eq_left`

English:
lemma inter_eq_left
  statement: s inter t = s ↔ s subseteq t
  proof: inf_eq_left

中文:
引理 inter_eq_left
  结论: s inter t = s ↔ s subseteq t
  证明: inf_eq_left
-/
@[simp] lemma inter_eq_left : s inter t = s ↔ s subseteq t := inf_eq_left

/--
lemma `inter_eq_right` / 引理 `inter_eq_right`

English:
lemma inter_eq_right
  statement: t inter s = s ↔ s subseteq t
  proof: inf_eq_right

中文:
引理 inter_eq_right
  结论: t inter s = s ↔ s subseteq t
  证明: inf_eq_right
-/
@[simp] lemma inter_eq_right : t inter s = s ↔ s subseteq t := inf_eq_right

/--
theorem `inter_congr_left` / 定理 `inter_congr_left`

English:
theorem inter_congr_left
  given: (ht : s inter u subseteq t) (hu : s inter t subseteq u)
  statement: s inter t = s inter u
  proof: inf_congr_left ht hu

中文:
定理 inter_congr_left
  条件: (ht : s inter u subseteq t) (hu : s inter t subseteq u)
  结论: s inter t = s inter u
  证明: inf_congr_left ht hu

Depends on / 依赖: inf_congr_left
-/
theorem inter_congr_left (ht : s inter u subseteq t) (hu : s inter t subseteq u) : s inter t = s inter u :=
  inf_congr_left ht hu

/--
theorem `inter_congr_right` / 定理 `inter_congr_right`

English:
theorem inter_congr_right
  given: (hs : t inter u subseteq s) (ht : s inter u subseteq t)
  statement: s inter u = t inter u
  proof: inf_congr_right hs ht

中文:
定理 inter_congr_right
  条件: (hs : t inter u subseteq s) (ht : s inter u subseteq t)
  结论: s inter u = t inter u
  证明: inf_congr_right hs ht

Depends on / 依赖: inf_congr_right
-/
theorem inter_congr_right (hs : t inter u subseteq s) (ht : s inter u subseteq t) : s inter u = t inter u :=
  inf_congr_right hs ht

/--
theorem `inter_eq_inter_iff_left` / 定理 `inter_eq_inter_iff_left`

English:
theorem inter_eq_inter_iff_left
  statement: s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u
  proof: inf_eq_inf_iff_left

中文:
定理 inter_eq_inter_iff_left
  结论: s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u
  证明: inf_eq_inf_iff_left

Depends on / 依赖: inf_eq_inf_iff_left
-/
theorem inter_eq_inter_iff_left : s inter t = s inter u ↔ s inter u subseteq t ∧ s inter t subseteq u :=
  inf_eq_inf_iff_left

/--
theorem `inter_eq_inter_iff_right` / 定理 `inter_eq_inter_iff_right`

English:
theorem inter_eq_inter_iff_right
  statement: s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t
  proof: inf_eq_inf_iff_right

中文:
定理 inter_eq_inter_iff_right
  结论: s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t
  证明: inf_eq_inf_iff_right

Depends on / 依赖: inf_eq_inf_iff_right
-/
theorem inter_eq_inter_iff_right : s inter u = t inter u ↔ t inter u subseteq s ∧ s inter u subseteq t :=
  inf_eq_inf_iff_right

/--
theorem `ite_subset_union` / 定理 `ite_subset_union`

English:
theorem ite_subset_union
  given: (s s' : Finset α) (P : Prop) [Decidable P]
  statement: ite P s s' subseteq s union s'
  proof: ite_le_sup s s' P

中文:
定理 ite_subset_union
  条件: (s s' : 有限集 α) (P : 命题) [可判定 P]
  结论: ite P s s' subseteq s union s'
  证明: ite_le_sup s s' P

Depends on / 依赖: ite_le_sup
-/
theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' subseteq s union s' :=
  ite_le_sup s s' P

/--
theorem `inter_subset_ite` / 定理 `inter_subset_ite`

English:
theorem inter_subset_ite
  given: (s s' : Finset α) (P : Prop) [Decidable P]
  statement: s inter s' subseteq ite P s s'
  proof: inf_le_ite s s' P

中文:
定理 inter_subset_ite
  条件: (s s' : 有限集 α) (P : 命题) [可判定 P]
  结论: s inter s' subseteq ite P s s'
  证明: inf_le_ite s s' P

Depends on / 依赖: inf_le_ite
-/
theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s inter s' subseteq ite P s s' :=
  inf_le_ite s s' P

end Lattice

end Finset
