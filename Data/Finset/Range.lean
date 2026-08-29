/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Multiset.Range
public import Mathlib.Order.Interval.Set.Defs

/-!
# Finite sets made of a range of elements.

## Main declarations

### Finset constructions

* `Finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ..., n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

open Multiset Subtype Function

/-! ### range -/


section Range

open Nat

variable {n m l : Nat}

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (n : Nat)
  body: ⟨_, nodup_range n⟩

@[simp]

中文:
定义 range
  签名: (n : 自然数)
  定义体: ⟨_, nodup_range n⟩

@[simp]

Depends on / 依赖: nodup_range
-/
def range (n : Nat) : Finset Nat :=
  ⟨_, nodup_range n⟩

@[simp]
/--
theorem `range_val` / 定理 `range_val`

English:
theorem range_val
  given: (n : Nat)
  statement: (range n).1 = Multiset.range n
  proof: rfl

中文:
定理 range_val
  条件: (n : 自然数)
  结论: (range n).1 = Multiset.range n
  证明: rfl
-/
theorem range_val (n : Nat) : (range n).1 = Multiset.range n :=
  rfl

/--
lemma `_root_.Multiset.toFinset_range` / 引理 `_root_.Multiset.toFinset_range`

English:
lemma _root_.Multiset.toFinset_range
  given: (n : Nat)
  statement: (Multiset.range n).toFinset = .range n
  proof: Finset.val_injective (Finset.range n).nodup.dedup

@[simp, grind =]

中文:
引理 _root_.Multiset.toFinset_range
  条件: (n : 自然数)
  结论: (Multiset.range n).toFinset = .range n
  证明: Finset.val_injective (Finset.range n).nodup.dedup

@[simp, grind =]
-/
@[simp] lemma _root_.Multiset.toFinset_range (n : Nat) : (Multiset.range n).toFinset = .range n :=
  Finset.val_injective (Finset.range n).nodup.dedup

@[simp, grind =]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  statement: m in range n ↔ m < n
  proof: Multiset.mem_range

@[simp, grind =, norm_cast]

中文:
定理 mem_range
  结论: m in range n ↔ m < n
  证明: Multiset.mem_range

@[simp, grind =, norm_cast]

Depends on / 依赖: Multiset, Multiset.mem_range, mem_range
-/
theorem mem_range : m in range n ↔ m < n :=
  Multiset.mem_range

@[simp, grind =, norm_cast]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: (n : Nat)
  statement: (range n : Set Nat) = Set.Iio n
  proof: Set.ext fun _ => mem_range

@[simp]

中文:
定理 coe_range
  条件: (n : 自然数)
  结论: (range n : 集合 自然数) = 集合.左无界右开区间 n
  证明: Set.ext fun _ => mem_range

@[simp]

Depends on / 依赖: Set.ext, mem_range
-/
theorem coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n :=
  Set.ext fun _ => mem_range

@[simp]
/--
theorem `range_zero` / 定理 `range_zero`

English:
theorem range_zero
  statement: range 0 = ∅
  proof: rfl

@[simp]

中文:
定理 range_zero
  结论: range 0 = ∅
  证明: rfl

@[simp]
-/
theorem range_zero : range 0 = ∅ :=
  rfl

@[simp]
/--
theorem `range_one` / 定理 `range_one`

English:
theorem range_one
  statement: range 1 = {0}
  proof: rfl

中文:
定理 range_one
  结论: range 1 = {0}
  证明: rfl
-/
theorem range_one : range 1 = {0} :=
  rfl

/--
theorem `range_add_one` / 定理 `range_add_one`

English:
theorem range_add_one
  statement: range (n + 1) = insert n (range n)
  proof: by grind

中文:
定理 range_add_one
  结论: range (n + 1) = insert n (range n)
  证明: by grind
-/
theorem range_add_one : range (n + 1) = insert n (range n) := by grind

/--
theorem `notMem_range_self` / 定理 `notMem_range_self`

English:
theorem notMem_range_self
  statement: n ∉ range n
  proof: by grind

中文:
定理 notMem_range_self
  结论: n ∉ range n
  证明: by grind
-/
theorem notMem_range_self : n ∉ range n := by grind

/--
theorem `self_mem_range_succ` / 定理 `self_mem_range_succ`

English:
theorem self_mem_range_succ
  given: (n : Nat)
  statement: n in range (n + 1)
  proof: by grind

@[grind =]

中文:
定理 self_mem_range_succ
  条件: (n : 自然数)
  结论: n in range (n + 1)
  证明: by grind

@[grind =]
-/
theorem self_mem_range_succ (n : Nat) : n in range (n + 1) := by grind

@[grind =]
/--
theorem `range_subset` / 定理 `range_subset`

English:
theorem range_subset
  given: {n s}
  statement: range n subseteq s ↔ forall x, x < n -> x in s
  proof: by grind

中文:
定理 range_subset
  条件: {n s}
  结论: range n subseteq s ↔ 对任意 x, x < n -> x in s
  证明: by grind
-/
theorem range_subset {n s} : range n subseteq s ↔ forall x, x < n -> x in s := by grind

/--
theorem `subset_range` / 定理 `subset_range`

English:
theorem subset_range
  given: {s n}
  statement: s subseteq range n ↔ forall x, x in s -> x < n
  proof: by grind

@[simp, gcongr]

中文:
定理 subset_range
  条件: {s n}
  结论: s subseteq range n ↔ 对任意 x, x in s -> x < n
  证明: by grind

@[simp, gcongr]
-/
theorem subset_range {s n} : s subseteq range n ↔ forall x, x in s -> x < n := by grind

@[simp, gcongr]
/--
theorem `range_subset_range` / 定理 `range_subset_range`

English:
theorem range_subset_range
  given: {n m}
  statement: range n subseteq range m ↔ n <= m
  proof: by grind

中文:
定理 range_subset_range
  条件: {n m}
  结论: range n subseteq range m ↔ n <= m
  证明: by grind

Depends on / 依赖: Nat.add_one, Nat.pred_succ, Num.to_nat_inj, _to_nat, add_one, pred_succ, to_nat_inj
-/
theorem range_subset_range {n m} : range n subseteq range m ↔ n <= m := by grind

/--
theorem `range_mono` / 定理 `range_mono`

English:
theorem range_mono
  statement: Monotone range
  proof: fun _ _ => range_subset_range.2

中文:
定理 range_mono
  结论: 递增 range
  证明: fun _ _ => range_subset_range.2

Depends on / 依赖: range_subset_range
-/
theorem range_mono : Monotone range := fun _ _ => range_subset_range.2

/--
theorem `strictMono_range` / 定理 `strictMono_range`

English:
theorem strictMono_range
  statement: StrictMono range
  proof: strictMono_nat_of_lt_succ fun _ => by simp [ssubset_def]

中文:
定理 strictMono_range
  结论: 严格递增 range
  证明: strictMono_nat_of_lt_succ fun _ => by simp [ssubset_def]

Depends on / 依赖: ssubset_def, strictMono_nat_of_lt_succ
-/
theorem strictMono_range : StrictMono range :=
  strictMono_nat_of_lt_succ fun _ => by simp [ssubset_def]

/--
theorem `mem_range_succ_iff` / 定理 `mem_range_succ_iff`

English:
theorem mem_range_succ_iff
  given: {a b : Nat}
  statement: a in range b.succ ↔ a <= b
  proof: by grind

中文:
定理 mem_range_succ_iff
  条件: {a b : 自然数}
  结论: a in range b.succ ↔ a <= b
  证明: by grind
-/
theorem mem_range_succ_iff {a b : Nat} : a in range b.succ ↔ a <= b := by grind

/--
theorem `mem_range_le` / 定理 `mem_range_le`

English:
theorem mem_range_le
  given: {n x : Nat} (hx : x in range n)
  statement: x <= n
  proof: by grind

中文:
定理 mem_range_le
  条件: {n x : 自然数} (hx : x in range n)
  结论: x <= n
  证明: by grind
-/
theorem mem_range_le {n x : Nat} (hx : x in range n) : x <= n := by grind

/--
theorem `mem_range_sub_ne_zero` / 定理 `mem_range_sub_ne_zero`

English:
theorem mem_range_sub_ne_zero
  given: {n x : Nat} (hx : x in range n)
  statement: n - x != 0
  proof: by grind

@[simp, grind =]

中文:
定理 mem_range_sub_ne_zero
  条件: {n x : 自然数} (hx : x in range n)
  结论: n - x != 0
  证明: by grind

@[simp, grind =]
-/
theorem mem_range_sub_ne_zero {n x : Nat} (hx : x in range n) : n - x != 0 := by grind

@[simp, grind =]
/--
theorem `nonempty_range_iff` / 定理 `nonempty_range_iff`

English:
theorem nonempty_range_iff
  statement: (range n).Nonempty ↔ n != 0
  proof: ⟨fun ⟨k, hk⟩ => by grind, fun h => ⟨0, by grind⟩⟩

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.range_nonempty⟩ := nonempty_range_iff

@[simp]

中文:
定理 nonempty_range_iff
  结论: (range n).非空 ↔ n != 0
  证明: ⟨fun ⟨k, hk⟩ => by grind, fun h => ⟨0, by grind⟩⟩

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.range_nonempty⟩ := nonempty_range_iff

@[simp]
-/
theorem nonempty_range_iff : (range n).Nonempty ↔ n != 0 :=
  ⟨fun ⟨k, hk⟩ => by grind, fun h => ⟨0, by grind⟩⟩

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.range_nonempty⟩ := nonempty_range_iff

@[simp]
/--
theorem `range_eq_empty_iff` / 定理 `range_eq_empty_iff`

English:
theorem range_eq_empty_iff
  statement: range n = ∅ ↔ n = 0
  proof: by
  grind [nonempty_range_iff]

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 range_eq_empty_iff
  结论: range n = ∅ ↔ n = 0
  证明: by
  grind [nonempty_range_iff]

@[aesop safe apply (rule_sets := [finsetNonempty])]

Depends on / 依赖: nonempty_range_iff
-/
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  grind [nonempty_range_iff]

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `nonempty_range_add_one` / 定理 `nonempty_range_add_one`

English:
theorem nonempty_range_add_one
  statement: (range <| n + 1).Nonempty
  proof: nonempty_range_iff.2 n.succ_ne_zero

中文:
定理 nonempty_range_add_one
  结论: (range <| n + 1).非空
  证明: nonempty_range_iff.2 n.succ_ne_zero

Depends on / 依赖: n.succ_ne_zero, nonempty_range_iff, succ_ne_zero
-/
theorem nonempty_range_add_one : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero

/--
lemma `range_nontrivial` / 引理 `range_nontrivial`

English:
lemma range_nontrivial
  given: {n : Nat} (hn : 1 < n)
  statement: (range n).Nontrivial
  proof: by
  rw [Finset.Nontrivial]; rw [Finset.coe_range]
  exact ⟨0, by grind, 1, hn, Nat.zero_ne_one⟩

中文:
引理 range_nontrivial
  条件: {n : 自然数} (hn : 1 < n)
  结论: (range n).非平凡
  证明: by
  rw [Finset.Nontrivial]; rw [Finset.coe_range]
  exact ⟨0, by grind, 1, hn, Nat.zero_ne_one⟩

Depends on / 依赖: Finset, Finset.Nontrivial, Finset.coe_range, Nat.zero_ne_one, Nontrivial, coe_range, zero_ne_one
-/
lemma range_nontrivial {n : Nat} (hn : 1 < n) : (range n).Nontrivial := by
  rw [Finset.Nontrivial]; rw [Finset.coe_range]
  exact ⟨0, by grind, 1, hn, Nat.zero_ne_one⟩

/--
theorem `exists_nat_subset_range` / 定理 `exists_nat_subset_range`

English:
theorem exists_nat_subset_range
  given: (s : Finset Nat)
  statement: exists n : Nat, s subseteq range n
  proof: s.induction_on (by simp) fun a _ _ ⟨n, hn⟩ => ⟨max (a + 1) n, by grind⟩

中文:
定理 存在_nat_subset_range
  条件: (s : 有限集 自然数)
  结论: 存在 n : 自然数, s subseteq range n
  证明: s.induction_on (by simp) fun a _ _ ⟨n, hn⟩ => ⟨max (a + 1) n, by grind⟩

Depends on / 依赖: induction_on, s.induction_on
-/
theorem exists_nat_subset_range (s : Finset Nat) : exists n : Nat, s subseteq range n :=
  s.induction_on (by simp) fun a _ _ ⟨n, hn⟩ => ⟨max (a + 1) n, by grind⟩

end Range

end Finset

open Finset

/--
Definition of `notMemRangeEquiv` / `notMemRangeEquiv` 的定义

English:
definition notMemRangeEquiv
  signature: (k : Nat)
  body: i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv := by grind
  right_inv := by grind

@[simp]

中文:
定义 notMemRangeEquiv
  签名: (k : 自然数)
  定义体: i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
-/
def notMemRangeEquiv (k : Nat) : { n // n ∉ range k } ≃ Nat where
  toFun i := i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/--
theorem `coe_notMemRangeEquiv` / 定理 `coe_notMemRangeEquiv`

English:
theorem coe_notMemRangeEquiv
  given: (k : Nat)
  proof: rfl

@[simp]

中文:
定理 coe_notMemRangeEquiv
  条件: (k : 自然数)
  证明: rfl

@[simp]
-/
theorem coe_notMemRangeEquiv (k : Nat) :
    (notMemRangeEquiv k : { n // n ∉ range k } -> Nat) = fun (i : { n // n ∉ range k }) => i - k :=
  rfl

@[simp]
/--
theorem `coe_notMemRangeEquiv_symm` / 定理 `coe_notMemRangeEquiv_symm`

English:
theorem coe_notMemRangeEquiv_symm
  given: (k : Nat)
  proof: rfl

中文:
定理 coe_notMemRangeEquiv_symm
  条件: (k : 自然数)
  证明: rfl
-/
theorem coe_notMemRangeEquiv_symm (k : Nat) :
    ((notMemRangeEquiv k).symm : Nat -> { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
  rfl
