/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.ZeroCons
public import Aesop

/-!
# Empty and nonempty finite sets

This file defines the empty finite set ∅ and a predicate for nonempty `Finset`s.

## Main declarations
* `Finset.Nonempty`: A finset is nonempty if it has elements. This is equivalent to saying `s ≠ ∅`.
* `Finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Nonempty -/


/--
Definition of `Nonempty` / `Nonempty` 的定义

English:
definition Nonempty
  signature: (s : Finset α)
  body: exists x : α, x in s

@[grind =]

中文:
定义 非空
  签名: (s : 有限集 α)
  定义体: exists x : α, x in s

@[grind =]
-/
protected def Nonempty (s : Finset α) : Prop := exists x : α, x in s

@[grind =]
/--
theorem `nonempty_def` / 定理 `nonempty_def`

English:
theorem nonempty_def
  given: {s : Finset α}
  statement: s.Nonempty ↔ exists x, x in s
  proof: Iff.rfl

中文:
定理 nonempty_def
  条件: {s : 有限集 α}
  结论: s.非空 ↔ 存在 x, x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem nonempty_def {s : Finset α} : s.Nonempty ↔ exists x, x in s := Iff.rfl

/--
Instance `decidableNonempty` / 实例 `decidableNonempty`

English:
instance decidableNonempty
  signature: {s : Finset α}
  body: decidable_of_iff (exists a in s, true) by simp [Finset.Nonempty]

@[simp, norm_cast]

中文:
实例 decidableNonempty
  签名: {s : 有限集 α}
  定义体: decidable_of_iff (exists a in s, true) by simp [Finset.Nonempty]

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, decidable_of_iff
-/
instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
decidable_of_iff (exists a in s, true) by simp [Finset.Nonempty]

@[simp, norm_cast]
/--
theorem `coe_nonempty` / 定理 `coe_nonempty`

English:
theorem coe_nonempty
  given: {s : Finset α}
  statement: (s : Set α).Nonempty ↔ s.Nonempty
  proof: Iff.rfl

中文:
定理 coe_nonempty
  条件: {s : 有限集 α}
  结论: (s : 集合 α).非空 ↔ s.非空
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl

-- Not `@[simp]` since `nonempty_subtype` already is.
/--
theorem `nonempty_coe_sort` / 定理 `nonempty_coe_sort`

English:
theorem nonempty_coe_sort
  given: {s : Finset α}
  statement: Nonempty (s : Type _) ↔ s.Nonempty
  proof: nonempty_subtype

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

中文:
定理 nonempty_coe_sort
  条件: {s : 有限集 α}
  结论: 非空 (s : 类型 _) ↔ s.非空
  证明: nonempty_subtype

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

Depends on / 依赖: nonempty_subtype
-/
theorem nonempty_coe_sort {s : Finset α} : Nonempty (s : Type _) ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

/--
theorem `Nonempty.exists_mem` / 定理 `Nonempty.exists_mem`

English:
theorem Nonempty.exists_mem
  given: {s : Finset α} (h : s.Nonempty)
  statement: exists x : α, x in s
  proof: h

中文:
定理 非空.存在_mem
  条件: {s : 有限集 α} (h : s.非空)
  结论: 存在 x : α, x in s
  证明: h
-/
theorem Nonempty.exists_mem {s : Finset α} (h : s.Nonempty) : exists x : α, x in s :=
  h

/--
theorem `Nonempty.mono` / 定理 `Nonempty.mono`

English:
theorem Nonempty.mono
  given: {s t : Finset α} (hst : s subseteq t) (hs : s.Nonempty)
  statement: t.Nonempty
  proof: Set.Nonempty.mono hst hs

中文:
定理 非空.mono
  条件: {s t : 有限集 α} (hst : s subseteq t) (hs : s.非空)
  结论: t.非空
  证明: Set.Nonempty.mono hst hs
-/
@[gcongr] theorem Nonempty.mono {s t : Finset α} (hst : s subseteq t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs

/--
theorem `Nonempty.forall_const` / 定理 `Nonempty.forall_const`

English:
theorem Nonempty.forall_const
  given: {s : Finset α} (h : s.Nonempty) {p : Prop}
  statement: (forall x in s, p) ↔ p
  proof: let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]

中文:
定理 非空.对任意_const
  条件: {s : 有限集 α} (h : s.非空) {p : 命题}
  结论: (对任意 x in s, p) ↔ p
  证明: let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]
-/
theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (forall x in s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

@[simp]
/--
theorem `forall_mem_const` / 定理 `forall_mem_const`

English:
theorem forall_mem_const
  given: {s : Finset α} [Nonempty s] {p : Prop}
  statement: (forall x in s, p) ↔ p
  proof: (nonempty_coe_sort.mp ‹_›).forall_const

中文:
定理 对任意_mem_const
  条件: {s : 有限集 α} [非空 s] {p : 命题}
  结论: (对任意 x in s, p) ↔ p
  证明: (nonempty_coe_sort.mp ‹_›).forall_const

Depends on / 依赖: forall_const, nonempty_coe_sort, nonempty_coe_sort.mp
-/
theorem forall_mem_const {s : Finset α} [Nonempty s] {p : Prop} : (forall x in s, p) ↔ p :=
  (nonempty_coe_sort.mp ‹_›).forall_const

/--
theorem `Nonempty.to_subtype` / 定理 `Nonempty.to_subtype`

English:
theorem Nonempty.to_subtype
  given: {s : Finset α}
  statement: s.Nonempty -> Nonempty s
  proof: nonempty_coe_sort.2

中文:
定理 非空.to_subtype
  条件: {s : 有限集 α}
  结论: s.非空 -> 非空 s
  证明: nonempty_coe_sort.2

Depends on / 依赖: nonempty_coe_sort
-/
theorem Nonempty.to_subtype {s : Finset α} : s.Nonempty -> Nonempty s :=
  nonempty_coe_sort.2

/--
theorem `Nonempty.to_type` / 定理 `Nonempty.to_type`

English:
theorem Nonempty.to_type
  given: {s : Finset α}
  statement: s.Nonempty -> Nonempty α
  proof: fun ⟨x, _hx⟩ => ⟨x⟩

中文:
定理 非空.to_type
  条件: {s : 有限集 α}
  结论: s.非空 -> 非空 α
  证明: fun ⟨x, _hx⟩ => ⟨x⟩
-/
theorem Nonempty.to_type {s : Finset α} : s.Nonempty -> Nonempty α := fun ⟨x, _hx⟩ => ⟨x⟩

/-! ### empty -/


section Empty

variable {s : Finset α}

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Finset α
  body: ⟨0, nodup_zero⟩

中文:
定义 empty
  签名: : 有限集 α
  定义体: ⟨0, nodup_zero⟩
-/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Finset α)
  body: ⟨Finset.empty⟩

中文:
实例 :
  签名: EmptyCollection (有限集 α)
  定义体: ⟨Finset.empty⟩

Depends on / 依赖: Finset, Finset.empty
-/
instance : EmptyCollection (Finset α) :=
  ⟨Finset.empty⟩

/--
Instance `inhabitedFinset` / 实例 `inhabitedFinset`

English:
instance inhabitedFinset
  signature: : Inhabited (Finset α)
  body: ⟨∅⟩

@[simp]

中文:
实例 inhabitedFinset
  签名: : 可居 (有限集 α)
  定义体: ⟨∅⟩

@[simp]

Depends on / 依赖: instOfNat
-/
instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩

@[simp]
/--
theorem `empty_val` / 定理 `empty_val`

English:
theorem empty_val
  statement: (∅ : Finset α).1 = 0
  proof: rfl

@[simp, grind ←]

中文:
定理 empty_val
  结论: (∅ : 有限集 α).1 = 0
  证明: rfl

@[simp, grind ←]
-/
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl

@[simp, grind ←]
/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (a : α)
  statement: a ∉ (∅ : Finset α)
  proof: by
  simp only [mem_def, empty_val, notMem_zero, not_false_iff]

@[simp]

中文:
定理 notMem_empty
  条件: (a : α)
  结论: a ∉ (∅ : 有限集 α)
  证明: by
  simp only [mem_def, empty_val, notMem_zero, not_false_iff]

@[simp]

Depends on / 依赖: empty_val, mem_def, notMem_zero, not_false_iff
-/
theorem notMem_empty (a : α) : a ∉ (∅ : Finset α) := by
  simp only [mem_def, empty_val, notMem_zero, not_false_iff]

@[simp]
/--
theorem `not_nonempty_empty` / 定理 `not_nonempty_empty`

English:
theorem not_nonempty_empty
  statement: ¬(∅ : Finset α).Nonempty
  proof: fun ⟨x, hx⟩ => notMem_empty x hx

@[simp]

中文:
定理 not_nonempty_empty
  结论: ¬(∅ : 有限集 α).非空
  证明: fun ⟨x, hx⟩ => notMem_empty x hx

@[simp]

Depends on / 依赖: notMem_empty
-/
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => notMem_empty x hx

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: (⟨0, nodup_zero⟩ : Finset α) = ∅
  proof: rfl

中文:
定理 mk_zero
  结论: (⟨0, nodup_zero⟩ : 有限集 α) = ∅
  证明: rfl
-/
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl

/--
theorem `ne_empty_of_mem` / 定理 `ne_empty_of_mem`

English:
theorem ne_empty_of_mem
  given: {a : α} {s : Finset α} (h : a in s)
  statement: s != ∅
  proof: fun e =>
notMem_empty a e ▸ h

中文:
定理 ne_empty_of_mem
  条件: {a : α} {s : 有限集 α} (h : a in s)
  结论: s != ∅
  证明: fun e =>
notMem_empty a e ▸ h
-/
theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a in s) : s != ∅ := fun e =>
notMem_empty a e ▸ h

/--
theorem `Nonempty.ne_empty` / 定理 `Nonempty.ne_empty`

English:
theorem Nonempty.ne_empty
  given: {s : Finset α} (h : s.Nonempty)
  statement: s != ∅
  proof: (Exists.elim h) fun _a => ne_empty_of_mem

@[simp]

中文:
定理 非空.ne_empty
  条件: {s : 有限集 α} (h : s.非空)
  结论: s != ∅
  证明: (Exists.elim h) fun _a => ne_empty_of_mem

@[simp]

Depends on / 依赖: Exists, Exists.elim, ne_empty_of_mem
-/
theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s != ∅ :=
  (Exists.elim h) fun _a => ne_empty_of_mem

@[simp]
/--
theorem `empty_subset` / 定理 `empty_subset`

English:
theorem empty_subset
  given: (s : Finset α)
  statement: ∅ subseteq s
  proof: zero_subset _

中文:
定理 empty_subset
  条件: (s : 有限集 α)
  结论: ∅ subseteq s
  证明: zero_subset _

Depends on / 依赖: zero_subset
-/
theorem empty_subset (s : Finset α) : ∅ subseteq s :=
  zero_subset _

/--
theorem `eq_empty_of_forall_notMem` / 定理 `eq_empty_of_forall_notMem`

English:
theorem eq_empty_of_forall_notMem
  given: {s : Finset α} (H : forall x, x ∉ s)
  statement: s = ∅
  proof: eq_of_veq (eq_zero_of_forall_notMem H)

中文:
定理 eq_empty_of_对任意_notMem
  条件: {s : 有限集 α} (H : 对任意 x, x ∉ s)
  结论: s = ∅
  证明: eq_of_veq (eq_zero_of_forall_notMem H)

Depends on / 依赖: eq_of_veq, eq_zero_of_forall_notMem
-/
theorem eq_empty_of_forall_notMem {s : Finset α} (H : forall x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_notMem H)

/--
theorem `eq_empty_iff_forall_notMem` / 定理 `eq_empty_iff_forall_notMem`

English:
theorem eq_empty_iff_forall_notMem
  given: {s : Finset α}
  statement: s = ∅ ↔ forall x, x ∉ s
  proof: by grind

@[simp]

中文:
定理 eq_empty_iff_对任意_notMem
  条件: {s : 有限集 α}
  结论: s = ∅ ↔ 对任意 x, x ∉ s
  证明: by grind

@[simp]
-/
theorem eq_empty_iff_forall_notMem {s : Finset α} : s = ∅ ↔ forall x, x ∉ s := by grind

@[simp]
/--
theorem `val_eq_zero` / 定理 `val_eq_zero`

English:
theorem val_eq_zero
  given: {s : Finset α}
  statement: s.1 = 0 ↔ s = ∅
  proof: @val_inj _ s ∅

中文:
定理 val_eq_zero
  条件: {s : 有限集 α}
  结论: s.1 = 0 ↔ s = ∅
  证明: @val_inj _ s ∅

Depends on / 依赖: val_inj
-/
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅

/--
lemma `subset_empty` / 引理 `subset_empty`

English:
lemma subset_empty
  statement: s subseteq ∅ ↔ s = ∅
  proof: subset_zero.trans val_eq_zero

@[simp]

中文:
引理 subset_empty
  结论: s subseteq ∅ ↔ s = ∅
  证明: subset_zero.trans val_eq_zero

@[simp]
-/
@[simp] lemma subset_empty : s subseteq ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

@[simp]
/--
theorem `not_ssubset_empty` / 定理 `not_ssubset_empty`

English:
theorem not_ssubset_empty
  given: (s : Finset α)
  statement: ¬s ⊂ ∅
  proof: by grind

中文:
定理 not_ssubset_empty
  条件: (s : 有限集 α)
  结论: ¬s ⊂ ∅
  证明: by grind
-/
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := by grind

/--
theorem `nonempty_of_ne_empty` / 定理 `nonempty_of_ne_empty`

English:
theorem nonempty_of_ne_empty
  given: {s : Finset α} (h : s != ∅)
  statement: s.Nonempty
  proof: exists_mem_of_ne_zero (mt val_eq_zero.1 h)

@[push ←]

中文:
定理 nonempty_of_ne_empty
  条件: {s : 有限集 α} (h : s != ∅)
  结论: s.非空
  证明: exists_mem_of_ne_zero (mt val_eq_zero.1 h)

@[push ←]

Depends on / 依赖: exists_mem_of_ne_zero, val_eq_zero
-/
theorem nonempty_of_ne_empty {s : Finset α} (h : s != ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)

@[push ←]
/--
theorem `nonempty_iff_ne_empty` / 定理 `nonempty_iff_ne_empty`

English:
theorem nonempty_iff_ne_empty
  given: {s : Finset α}
  statement: s.Nonempty ↔ s != ∅
  proof: ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp, push]

中文:
定理 nonempty_iff_ne_empty
  条件: {s : 有限集 α}
  结论: s.非空 ↔ s != ∅
  证明: ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp, push]

Depends on / 依赖: Nonempty, Nonempty.ne_empty, ne_empty, nonempty_of_ne_empty
-/
theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s != ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp, push]
/--
theorem `not_nonempty_iff_eq_empty` / 定理 `not_nonempty_iff_eq_empty`

English:
theorem not_nonempty_iff_eq_empty
  given: {s : Finset α}
  statement: ¬s.Nonempty ↔ s = ∅
  proof: nonempty_iff_ne_empty.not.trans not_not

中文:
定理 not_nonempty_iff_eq_empty
  条件: {s : 有限集 α}
  结论: ¬s.非空 ↔ s = ∅
  证明: nonempty_iff_ne_empty.not.trans not_not

Depends on / 依赖: nonempty_iff_ne_empty, nonempty_iff_ne_empty.not.trans, not_not
-/
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.not.trans not_not

/--
theorem `eq_empty_or_nonempty` / 定理 `eq_empty_or_nonempty`

English:
theorem eq_empty_or_nonempty
  given: (s : Finset α)
  statement: s = ∅ ∨ s.Nonempty
  proof: by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]

中文:
定理 eq_empty_or_nonempty
  条件: (s : 有限集 α)
  结论: s = ∅ ∨ s.非空
  证明: by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]

Depends on / 依赖: Or.inl, Or.inr, nonempty_of_ne_empty
-/
theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]
/--
theorem `coe_empty` / 定理 `coe_empty`

English:
theorem coe_empty
  statement: ((∅ : Finset α) : Set α) = ∅
  proof: by grind

@[simp, norm_cast]

中文:
定理 coe_empty
  结论: ((∅ : 有限集 α) : 集合 α) = ∅
  证明: by grind

@[simp, norm_cast]
-/
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ := by grind

@[simp, norm_cast]
/--
theorem `coe_eq_empty` / 定理 `coe_eq_empty`

English:
theorem coe_eq_empty
  given: {s : Finset α}
  statement: (s : Set α) = ∅ ↔ s = ∅
  proof: by grind

@[simp]

中文:
定理 coe_eq_empty
  条件: {s : 有限集 α}
  结论: (s : 集合 α) = ∅ ↔ s = ∅
  证明: by grind

@[simp]
-/
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by grind

@[simp]
/--
theorem `isEmpty_coe_sort` / 定理 `isEmpty_coe_sort`

English:
theorem isEmpty_coe_sort
  given: {s : Finset α}
  statement: IsEmpty (s : Type _) ↔ s = ∅
  proof: by
  simpa using @Set.isEmpty_coe_sort α s

中文:
定理 isEmpty_coe_sort
  条件: {s : 有限集 α}
  结论: 是空 (s : 类型 _) ↔ s = ∅
  证明: by
  simpa using @Set.isEmpty_coe_sort α s

Depends on / 依赖: Set.isEmpty_coe_sort, isEmpty_coe_sort
-/
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s

/--
Instance `instIsEmpty` / 实例 `instIsEmpty`

English:
instance instIsEmpty
  signature: : IsEmpty (∅ : Finset α)
  body: isEmpty_coe_sort.2 rfl

中文:
实例 instIsEmpty
  签名: : 是空 (∅ : 有限集 α)
  定义体: isEmpty_coe_sort.2 rfl

Depends on / 依赖: AtLeastTwo, Nat.AtLeastTwo, NatCast, instOfNatAtLeastTwo, isEmpty_coe_sort
-/
instance instIsEmpty : IsEmpty (∅ : Finset α) :=
  isEmpty_coe_sort.2 rfl

/--
theorem `eq_empty_of_isEmpty` / 定理 `eq_empty_of_isEmpty`

English:
theorem eq_empty_of_isEmpty
  given: [IsEmpty α] (s : Finset α)
  statement: s = ∅
  proof: Finset.eq_empty_of_forall_notMem isEmptyElim

中文:
定理 eq_empty_of_isEmpty
  条件: [是空 α] (s : 有限集 α)
  结论: s = ∅
  证明: Finset.eq_empty_of_forall_notMem isEmptyElim

Depends on / 依赖: Finset, Finset.eq_empty_of_forall_notMem, eq_empty_of_forall_notMem, isEmptyElim
-/
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_notMem isEmptyElim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (Finset α)
  body: ∅
  bot_le := empty_subset

@[simp, grind =]

中文:
实例 :
  签名: 有底序 (有限集 α)
  定义体: ∅
  bot_le := empty_subset

@[simp, grind =]
-/
instance : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

@[simp, grind =]
/--
theorem `bot_eq_empty` / 定理 `bot_eq_empty`

English:
theorem bot_eq_empty
  statement: (⊥ : Finset α) = ∅
  proof: rfl

@[simp]

中文:
定理 bot_eq_empty
  结论: (⊥ : 有限集 α) = ∅
  证明: rfl

@[simp]
-/
theorem bot_eq_empty : (⊥ : Finset α) = ∅ :=
  rfl

@[simp]
/--
theorem `empty_ssubset` / 定理 `empty_ssubset`

English:
theorem empty_ssubset
  statement: ∅ ⊂ s ↔ s.Nonempty
  proof: (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

中文:
定理 empty_ssubset
  结论: ∅ ⊂ s ↔ s.非空
  证明: (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

Depends on / 依赖: Finset, bot_lt_iff_ne_bot, nonempty_iff_ne_empty, nonempty_iff_ne_empty.symm
-/
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

-- useful rules for calculations with quantifiers
/--
theorem `exists_mem_empty_iff` / 定理 `exists_mem_empty_iff`

English:
theorem exists_mem_empty_iff
  given: (p : α -> Prop)
  statement: (exists x, x in (∅ : Finset α) ∧ p x) ↔ False
  proof: by
  grind

中文:
定理 存在_mem_empty_iff
  条件: (p : α -> 命题)
  结论: (存在 x, x in (∅ : 有限集 α) ∧ p x) ↔ 假
  证明: by
  grind
-/
theorem exists_mem_empty_iff (p : α -> Prop) : (exists x, x in (∅ : Finset α) ∧ p x) ↔ False := by
  grind

/--
theorem `forall_mem_empty_iff` / 定理 `forall_mem_empty_iff`

English:
theorem forall_mem_empty_iff
  given: (p : α -> Prop)
  statement: (forall x, x in (∅ : Finset α) -> p x) ↔ True
  proof: by
  grind

中文:
定理 对任意_mem_empty_iff
  条件: (p : α -> 命题)
  结论: (对任意 x, x in (∅ : 有限集 α) -> p x) ↔ 真
  证明: by
  grind
-/
theorem forall_mem_empty_iff (p : α -> Prop) : (forall x, x in (∅ : Finset α) -> p x) ↔ True := by
  grind

end Empty
end Finset

namespace Mathlib.Meta
open Qq Lean Meta Finset

/-- Attempt to prove that a finset is nonempty using the `finsetNonempty` aesop rule-set.

You can add lemmas to the rule-set by tagging them with either:
* `aesop safe apply (rule_sets := [finsetNonempty])` if they are always a good idea to follow or
* `aesop unsafe apply (rule_sets := [finsetNonempty])` if they risk directing the search to a blind
  alley.

TODO: should some of the lemmas be `aesop safe simp` instead?
-/
meta def proveFinsetNonempty {u : Level} {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (Option Q(Finset.Nonempty $s)) := do
  -- Aesop expects to operate on goals, so we're going to make a new goal.
  let goal ← Lean.Meta.mkFreshExprMVar q(Finset.Nonempty $s)
  let mvar := goal.mvarId!
  -- We want this to be fast, so use only the basic and `Finset.Nonempty`-specific rules.
  let rulesets ← Aesop.Frontend.getGlobalRuleSets #[`builtin, `finsetNonempty]
  let options : Aesop.Options' :=
    { terminal := true -- Fail if the new goal is not closed.
      generateScript := false
      useDefaultSimpSet := false -- Avoiding the whole simp set to speed up the tactic.
      warnOnNonterminal := false -- Don't show a warning on failure, simply return `none`.
      forwardMaxDepth? := none }
  let rules ← Aesop.mkLocalRuleSet rulesets options
  let (remainingGoals, _) ←
    try Aesop.search (options := options.toOptions) mvar (.some rules)
    catch _ => return none
  -- Fail if there are open goals remaining, this serves as an extra check for the
  -- Aesop configuration option `terminal := true`.
  if remainingGoals.size > 0 then return none
  Lean.getExprMVarAssignment? mvar

end Mathlib.Meta
