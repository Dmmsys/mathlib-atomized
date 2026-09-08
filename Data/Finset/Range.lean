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

variable {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
/-
**Finset.range** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：range (n : Nat) : Finset Nat
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_range`：nodup_range (n : Nat) : Nodup (range n)

--- 原说明 ---
`range n` is the set of natural numbers less than `n`.
-/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩

@[simp]
/-
**Finset.range_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_val (n : Nat) : (range n).1 = Multiset.range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl
/-
**Finset._root_.Multiset.toFinset_range** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.Multiset.toFinset_range (n : ℕ) : (Multiset.range n).toFinset = .range n :=
  Finset.val_injective (Finset.range n).nodup.dedup

@[simp, grind =]
/-
**Finset.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_range : m in range n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_range`：mem_range {m n : Nat} : m in range n ↔ m < n
-/
theorem mem_range : m ∈ range n ↔ m < n :=
  Multiset.mem_range

@[simp, grind =, norm_cast]
/-
**Finset.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
theorem coe_range (n : ℕ) : (range n : Set ℕ) = Set.Iio n :=
  Set.ext fun _ => mem_range

@[simp]
/-
**Finset.range_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_zero : range 0 = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_zero : range 0 = ∅ :=
  rfl

@[simp]
/-
**Finset.range_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_one : range 1 = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_one : range 1 = {0} :=
  rfl
/-
**Finset.range_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_add_one : range (n + 1) = insert n (range n)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_add_one : range (n + 1) = insert n (range n) := by grind
/-
**Finset.notMem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：notMem_range_self : n ∉ range n
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_range_self : n ∉ range n := by grind
/-
**Finset.self_mem_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：self_mem_range_succ (n : Nat) : n in range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := by grind

@[grind =]
/-
**Finset.range_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_subset {n s} : range n subseteq s ↔ forall x, x < n -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_subset {n s} : range n ⊆ s ↔ ∀ x, x < n → x ∈ s := by grind
/-
**Finset.subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_range {s n} : s subseteq range n ↔ forall x, x in s -> x < n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_range {s n} : s ⊆ range n ↔ ∀ x, x ∈ s → x < n := by grind

@[simp, gcongr]
/-
**Finset.range_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_subset_range {n m} : range n subseteq range m ↔ n <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_subset_range {n m} : range n ⊆ range m ↔ n ≤ m := by grind
/-
**Finset.range_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_mono : Monotone range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.range_subset_range`：range_subset_range {n m} : range n subseteq r
ange m ↔ n <= m
-/
theorem range_mono : Monotone range := fun _ _ => range_subset_range.2
/-
**Finset.strictMono_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strictMono_range : StrictMono range
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem strictMono_range : StrictMono range :=
  strictMono_nat_of_lt_succ fun _ ↦ by simp [ssubset_def]
/-
**Finset.mem_range_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_range_succ_iff {a b : Nat} : a in range b.succ ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_succ_iff {a b : ℕ} : a ∈ range b.succ ↔ a ≤ b := by grind
/-
**Finset.mem_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_range_le {n x : Nat} (hx : x in range n) : x <= n
参数：hx : x in range n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n := by grind
/-
**Finset.mem_range_sub_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_range_sub_ne_zero {n x : Nat} (hx : x in range n) : n - x != 0
参数：hx : x in range n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 := by grind

@[simp, grind =]
/-
**Finset.nonempty_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_range_iff : (range n).Nonempty ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => by grind, fun h => ⟨0, by grind⟩⟩

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Aesop.range_nonempty⟩ := nonempty_range_iff

@[simp]
/-
**Finset.range_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_eq_empty_iff : range n = ∅ ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  grind [nonempty_range_iff]

@[aesop safe apply (rule_sets := [finsetNonempty])]
/-
**Finset.nonempty_range_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：nonempty_range_add_one : (range <| n + 1).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_range_iff`：nonempty_range_iff : (range n).Nonempty ↔ n !
= 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem nonempty_range_add_one : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero
/-
**Finset.range_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：range_nontrivial {n : Nat} (hn : 1 < n) : (range n).Nontrivial
参数：hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nontrivial.eq_1`：∀ {α : Type u_1} (s : Finset α), s.Nontrivial = 
(↑s).Nontrivial
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Nat.zero_ne_one`：0 ≠ 1
-/
lemma range_nontrivial {n : ℕ} (hn : 1 < n) : (range n).Nontrivial := by
  rw [Finset.Nontrivial, Finset.coe_range]
  exact ⟨0, by grind, 1, hn, Nat.zero_ne_one⟩
/-
**Finset.exists_nat_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_nat_subset_range (s : Finset Nat) : exists n : Nat, s subseteq rang
e n
参数：s : Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem exists_nat_subset_range (s : Finset ℕ) : ∃ n : ℕ, s ⊆ range n :=
  s.induction_on (by simp) fun a _ _ ⟨n, hn⟩ => ⟨max (a + 1) n, by grind⟩

end Range

end Finset

open Finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
/-
**notMemRangeEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：notMemRangeEquiv (k : Nat) : { n // n ∉ range k } ≃ Nat where toFun i
参数：k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by
 `n → n - k`.
-/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ where
  toFun i := i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv := by grind
  right_inv := by grind

@[simp]
/-
**coe_notMemRangeEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_notMemRangeEquiv (k : Nat) : (notMemRangeEquiv k : { n // n ∉ range k 
} -> Nat) = fun (i : { n // n ∉ range k }) => i - k
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_notMemRangeEquiv (k : ℕ) :
    (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun (i : { n // n ∉ range k }) => i - k :=
  rfl

@[simp]
/-
**coe_notMemRangeEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_notMemRangeEquiv_symm (k : Nat) : ((notMemRangeEquiv k).symm : Nat -> 
{ n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_notMemRangeEquiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
  rfl
