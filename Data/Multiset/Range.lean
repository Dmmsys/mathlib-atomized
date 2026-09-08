/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.UnionInter

/-! # `Multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/

@[expose] public section

assert_not_exists Monoid

open List Nat

namespace Multiset

-- range
/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
/-
**Multiset.range** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：range (n : Nat) : Multiset Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`.
-/
def range (n : ℕ) : Multiset ℕ :=
  List.range n
/-
**Multiset.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_range (n : Nat) : ↑(List.range n) = range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range (n : ℕ) : ↑(List.range n) = range n :=
  rfl

@[simp]
/-
**Multiset.range_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_zero : range 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_zero : range 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_succ (n : Nat) : range (succ n) = n ::ₘ range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.range.eq_1`：∀ (n : ℕ), Multiset.range n = ↑(List.range n)
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_add`：coe_add (s t : List α) : (s + t : Multiset α) = (s ++ 
t : List α)
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.coe_singleton`：coe_singleton (a : α) : ([a] : Multiset α) = {a}
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
-/
theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n := by
  rw [range, List.range_succ, ← coe_add, Multiset.add_comm, range, coe_singleton, singleton_add]

@[simp]
/-
**Multiset.card_range** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_range (n : Nat) : card (range n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
-/
theorem card_range (n : ℕ) : card (range n) = n :=
  length_range
/-
**Multiset.range_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_subset {m n : Nat} : range m subseteq range n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.range_subset`：∀ {m n : ℕ}, List.range m ⊆ List.range n ↔ m ≤ n
-/
theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  List.range_subset

@[simp]
/-
**Multiset.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_range {m n : Nat} : m in range n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
-/
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
  List.mem_range
/-
**Multiset.notMem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：notMem_range_self {n : Nat} : n ∉ range n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_range_self`：∀ {n : ℕ}, n ∉ List.range n
-/
theorem notMem_range_self {n : ℕ} : n ∉ range n :=
  List.not_mem_range_self
/-
**Multiset.self_mem_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：self_mem_range_succ (n : Nat) : n in range (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.self_mem_range_succ`：∀ {n : ℕ}, n ∈ List.range (n + 1)
-/
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  List.self_mem_range_succ
/-
**Multiset.range_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_add (a b : Nat) : range (a + b) = range a + (range b).map (a + ·)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.range_add`：∀ {n m : ℕ}, List.range (n + m) = List.range n ++ List.m
ap (fun x => n + x) (List.range m)
-/
theorem range_add (a b : ℕ) : range (a + b) = range a + (range b).map (a + ·) :=
  congr_arg ((↑) : List ℕ → Multiset ℕ) List.range_add
/-
**Multiset.range_disjoint_map_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_disjoint_map_add (a : Nat) (m : Multiset Nat) : Disjoint (range a) (
m.map (a + ·))
参数：a : Nat；m : Multiset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `Multiset.mem_coe`：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔
 a in l
· 使用定理 `Multiset.range.eq_1`：∀ (n : ℕ), Multiset.range n = ↑(List.range n)
-/
theorem range_disjoint_map_add (a : ℕ) (m : Multiset ℕ) :
    Disjoint (range a) (m.map (a + ·)) := by
  rw [disjoint_left]
  intro x hxa hxb
  rw [range, mem_coe, List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (Nat.le_add_right _ _).not_gt hxa
/-
**Multiset.range_add_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_add_eq_union (a b : Nat) : range (a + b) = range a union (range b).m
ap (a + ·)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.range_add`：range_add (a b : Nat) : range (a + b) = range a + (r
ange b).map (a + ·)
· 使用定理 `Multiset.add_eq_union_iff_disjoint`：add_eq_union_iff_disjoint [Decidable
Eq α] {s t : Multiset α} : s + t = s union t ↔ Disjoint s t
· 使用定理 `Multiset.range_disjoint_map_add`：range_disjoint_map_add (a : Nat) (m : M
ultiset Nat) : Disjoint (range a) (m.map (a + ·))
-/
theorem range_add_eq_union (a b : ℕ) : range (a + b) = range a ∪ (range b).map (a + ·) := by
  rw [range_add, add_eq_union_iff_disjoint]
  apply range_disjoint_map_add

section Nodup

/-
**Multiset.nodup_range** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_range (n : Nat) : Nodup (range n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_range`：∀ {n : ℕ}, (List.range n).Nodup
-/
theorem nodup_range (n : ℕ) : Nodup (range n) :=
  List.nodup_range
/-
**Multiset.range_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：range_le {m n : Nat} : range m <= range n ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Multiset.nodup_range`：nodup_range (n : Nat) : Nodup (range n)
· 使用定理 `Multiset.range_subset`：range_subset {m n : Nat} : range m subseteq range
 n ↔ m <= n
-/
theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
  (le_iff_subset (nodup_range _)).trans range_subset

end Nodup

end Multiset

