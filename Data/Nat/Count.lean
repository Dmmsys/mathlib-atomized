/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Kim Morrison, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Nat.Range
public import Mathlib.Data.Set.Finite.Basic

/-!
# Counting on ℕ

This file defines the `count` function, which gives, for any predicate on the natural numbers,
"how many numbers under `k` satisfy this predicate?".
We then prove several expected lemmas about `count`, relating it to the cardinality of other
objects, and helping to evaluate it for specific `k`.

-/

@[expose] public section

assert_not_imported Mathlib.Dynamics.FixedPoints.Basic
assert_not_exists Ring

open Finset

namespace Nat

variable (p : ℕ → Prop)

section Count

variable [DecidablePred p]

/-- Count the number of naturals `k < n` satisfying `p k`. -/
/-
**Nat.count** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：count (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Count the number of naturals `k < n` satisfying `p k`.
-/
def count (n : ℕ) : ℕ :=
  (List.range n).countP p

@[simp, grind =]
/-
**Nat.count_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_zero : count p 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_zero : count p 0 = 0 := by simp [count]

/-- A fintype instance for the set relevant to `Nat.count`. Locally an instance in scope `count` -/
@[instance_reducible]
/-
**Nat.CountSet.fintype** 是 Mathlib 中的一个定义，位于命名空间 `Nat.CountSet`。
形式化陈述：(p : ℕ → Prop) → [DecidablePred p] → (n : ℕ) → Fintype { i // i < n ∧ p i 
}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fintype instance for the set relevant to `Nat.count`. Locally an instance in s
cope `count`
-/
def CountSet.fintype (n : ℕ) : Fintype { i // i < n ∧ p i } :=
  Fintype.subtype {x ∈ range n | p x} <| by simp

scoped[Count] attribute [instance] Nat.CountSet.fintype

open Count
/-
**Nat.count_eq_card_filter_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_eq_card_filter_range (n : Nat) : count p n = #{x in range n | p x}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count.eq_1`：∀ (p : ℕ → Prop) [inst : DecidablePred p] (n : ℕ), Nat.c
ount p n = List.countP (fun b => decide (p b)) (List.range n)
· 使用定理 `List.countP_eq_length_filter`：∀ {α : Type u_1} {p : α → Bool} {l : List 
α}, List.countP p l = (List.filter p l).length
-/
theorem count_eq_card_filter_range (n : ℕ) : count p n = #{x ∈ range n | p x} := by
  rw [count, List.countP_eq_length_filter]
  rfl

/-- `count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`. -/
/-
**Nat.count_eq_card_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_eq_card_fintype (n : Nat) : count p n = Fintype.card { k : Nat // k 
< n ∧ p k }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Fintype.card_of_subtype`：card_of_subtype {p : α -> Prop} (s : Finset α) 
(H : forall x : α, x in s ↔ p x) [Fintype { x // p x }] : card { x // p x } = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`.
-/
theorem count_eq_card_fintype (n : ℕ) : count p n = Fintype.card { k : ℕ // k < n ∧ p k } := by
  rw [count_eq_card_filter_range, Fintype.card_of_subtype]
  simp
/-
**Nat.count_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le {n : Nat} : count p n <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem count_le {n : ℕ} : count p n ≤ n := by
  rw [count_eq_card_filter_range]
  exact (card_filter_le _ _).trans_eq (card_range _)

@[grind =]
/-
**Nat.count_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_succ (n : Nat) : count p (n + 1) = count p n + if p n then 1 else 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_succ (n : ℕ) : count p (n + 1) = count p n + if p n then 1 else 0 := by
  grind [count, List.range_succ]

@[gcongr, mono]
/-
**Nat.count_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_monotone : Monotone (count p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
-/
theorem count_monotone : Monotone (count p) :=
  monotone_nat_of_le_succ (by grind)
/-
**Nat.count_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_add (a b : Nat) : count p (a + b) = count p a + count (fun k => p (a
 + k)) b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.range_add`：∀ {n m : ℕ}, List.range (n + m) = List.range n ++ List.m
ap (fun x => n + x) (List.range m)
· 使用定理 `List.countP_append`：∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}, Li
st.countP p (l₁ ++ l₂) = List.countP p l₁ + List.countP p l₂
· 使用定理 `List.countP_map`：∀ {α : Type u_2} {β : Type u_1} {p : β → Bool} {f : α →
 β} {l : List α},   List.countP p (List.map f l) = List.countP (p ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_add (a b : ℕ) : count p (a + b) = count p a + count (fun k ↦ p (a + k)) b := by
  simp [count, List.range_add, Function.comp_def]
/-
**Nat.count_add'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_add' (a b : Nat) : count p (a + b) = count (fun k => p (k + b)) a + 
count p b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.count_add`：count_add (a b : Nat) : count p (a + b) = count p a + cou
nt (fun k => p (a + k)) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.count.congr_simp`：∀ (p p_1 : ℕ → Prop),   p = p_1 →     ∀ {inst : De
cidablePred p} [inst_1 : DecidablePred p_1] (n n_1 : ℕ), n = n_1 → Nat.count p n
 = Nat.cou…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_add' (a b : ℕ) : count p (a + b) = count (fun k ↦ p (k + b)) a + count p b := by
  rw [add_comm, count_add, add_comm]
  simp_rw [add_comm b]
/-
**Nat.count_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_one : count p 1 = if p 0 then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_succ`：count_succ (n : Nat) : count p (n + 1) = count p n + if 
p n then 1 else 0
· 使用定理 `Nat.count_zero`：count_zero : count p 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_one : count p 1 = if p 0 then 1 else 0 := by simp [count_succ]
/-
**Nat.count_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_succ' (n : Nat) : count p (n + 1) = count (fun k => p (k + 1)) n + i
f p 0 then 1 else 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_add'`：count_add' (a b : Nat) : count p (a + b) = count (fun k 
=> p (k + b)) a + count p b
· 使用定理 `Nat.count_one`：count_one : count p 1 = if p 0 then 1 else 0
-/
theorem count_succ' (n : ℕ) :
    count p (n + 1) = count (fun k ↦ p (k + 1)) n + if p 0 then 1 else 0 := by
  rw [count_add', count_one]

variable {p}

@[simp]
/-
**Nat.count_lt_count_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_lt_count_succ_iff {n : Nat} : count p n < count p (n + 1) ↔ p n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_lt_count_succ_iff {n : ℕ} : count p n < count p (n + 1) ↔ p n := by grind
/-
**Nat.count_succ_eq_succ_count_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_succ_eq_succ_count_iff {n : Nat} : count p (n + 1) = count p n + 1 ↔
 p n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n := by grind
/-
**Nat.count_succ_eq_count_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_succ_eq_count_iff {n : Nat} : count p (n + 1) = count p n ↔ ¬p n
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n := by grind

alias ⟨_, count_succ_eq_succ_count⟩ := count_succ_eq_succ_count_iff

alias ⟨_, count_succ_eq_count⟩ := count_succ_eq_count_iff
/-
**Nat.lt_of_count_lt_count** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_count_lt_count {a b : Nat} (h : count p a < count p b) : a < b
参数：h : count p a < count p b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `Nat.count_monotone`：count_monotone : Monotone (count p)
-/
theorem lt_of_count_lt_count {a b : ℕ} (h : count p a < count p b) : a < b :=
  (count_monotone p).reflect_lt h
/-
**Nat.count_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_strict_mono {m n : Nat} (hm : p m) (hmn : m < n) : count p m < count
 p n
参数：hm : p m；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.count_lt_count_succ_iff`：count_lt_count_succ_iff {n : Nat} : count p
 n < count p (n + 1) ↔ p n
· 使用定理 `Nat.count_monotone`：count_monotone : Monotone (count p)
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
-/
theorem count_strict_mono {m n : ℕ} (hm : p m) (hmn : m < n) : count p m < count p n :=
  (count_lt_count_succ_iff.2 hm).trans_le <| count_monotone _ (Nat.succ_le_iff.2 hmn)
/-
**Nat.count_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_injective {m n : Nat} (hm : p m) (hn : p n) (heq : count p m = count
 p n) : m = n
参数：hm : p m；hn : p n；heq : count p m = count p n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_strict_mono`：count_strict_mono {m n : Nat} (hm : p m) (hmn : m
 < n) : count p m < count p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem count_injective {m n : ℕ} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n := by
  by_contra h : m ≠ n
  wlog hmn : m < n
  · exact this hn hm heq.symm h.symm (by grind)
  · simpa [heq] using count_strict_mono hm hmn
/-
**Nat.count_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_le_card (hp : (Set.ofPred p).Finite) (n : Nat) : count p n <= #hp.to
Finset
参数：hp : (Set.ofPred p).Finite；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem count_le_card (hp : (Set.ofPred p).Finite) (n : ℕ) : count p n ≤ #hp.toFinset := by
  rw [count_eq_card_filter_range]
  exact Finset.card_mono fun x hx ↦ hp.mem_toFinset.2 (mem_filter.1 hx).2
/-
**Nat.count_lt_card** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_lt_card {n : Nat} (hp : (Set.ofPred p).Finite) (hpn : p n) : count p
 n < #hp.toFinset
参数：hp : (Set.ofPred p).Finite；hpn : p n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.count_lt_count_succ_iff`：count_lt_count_succ_iff {n : Nat} : count p
 n < count p (n + 1) ↔ p n
· 使用定理 `Nat.count_le_card`：count_le_card (hp : (Set.ofPred p).Finite) (n : Nat) 
: count p n <= #hp.toFinset
-/
theorem count_lt_card {n : ℕ} (hp : (Set.ofPred p).Finite) (hpn : p n) : count p n < #hp.toFinset :=
  (count_lt_count_succ_iff.2 hpn).trans_le (count_le_card hp _)
/-
**Nat.count_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_iff_forall {n : Nat} : count p n = n ↔ forall n' < n, p n'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.card_filter_eq_iff`：card_filter_eq_iff {p : α -> Prop} [Decidable
Pred p] : #(s.filter p) = #s ↔ forall x in s, p x
-/
theorem count_iff_forall {n : ℕ} : count p n = n ↔ ∀ n' < n, p n' := by
  simpa [count_eq_card_filter_range, card_range, mem_range] using
    card_filter_eq_iff (p := p) (s := range n)

alias ⟨_, count_of_forall⟩ := count_iff_forall
/-
**Nat.count_true** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.count (fun x => True) n = n
参数：n : ℕ；fun x => True。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_of_forall`：∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : ℕ}, 
(∀ n' < n, p n') → Nat.count p n = n
· 使用定理 `trivial`：True
-/
@[simp] theorem count_true (n : ℕ) : count (fun _ ↦ True) n = n := count_of_forall fun _ _ ↦ trivial
/-
**Nat.count_iff_forall_not** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_iff_forall_not {n : Nat} : count p n = 0 ↔ forall m < n, ¬p m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_iff_forall_not {n : ℕ} : count p n = 0 ↔ ∀ m < n, ¬p m := by
  simp [count_eq_card_filter_range]

alias ⟨_, count_of_forall_not⟩ := count_iff_forall_not
/-
**Nat.count_ne_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_ne_iff_exists {n : Nat} : n.count p != 0 ↔ exists m < n, p m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_ne_iff_exists {n : ℕ} : n.count p ≠ 0 ↔ ∃ m < n, p m := by
  simp [Nat.count_iff_forall_not]
/-
**Nat.count_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), Nat.count (fun x => False) n = 0
参数：n : ℕ；fun x => False。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_of_forall_not`：∀ {p : ℕ → Prop} [inst : DecidablePred p] {n : 
ℕ}, (∀ m < n, ¬p m) → Nat.count p n = 0
-/
@[simp] theorem count_false (n : ℕ) : count (fun _ ↦ False) n = 0 :=
  count_of_forall_not fun _ _ ↦ id
/-
**Nat.exists_of_count_lt_count** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：exists_of_count_lt_count {a b : Nat} (h : a.count p < b.count p) : exists 
x in Set.Ico a b, p x
参数：h : a.count p < b.count p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `Nat.lt_of_count_lt_count`：lt_of_count_lt_count {a b : Nat} (h : count p 
a < count p b) : a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.count_ne_iff_exists`：count_ne_iff_exists {n : Nat} : n.count p != 0 
↔ exists m < n, p m
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_add_right_iff_pos`：∀ {n k : ℕ}, n < n + k ↔ 0 < k
· 使用定理 `Nat.count_add`：count_add (a b : Nat) : count p (a + b) = count p a + cou
nt (fun k => p (a + k)) b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma exists_of_count_lt_count {a b : ℕ} (h : a.count p < b.count p) : ∃ x ∈ Set.Ico a b, p x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (lt_of_count_lt_count h)
  rw [add_assoc, count_add, Nat.lt_add_right_iff_pos] at h
  obtain ⟨t, ht, hp⟩ := count_ne_iff_exists.mp h.ne'
  simp_rw [Set.mem_Ico]
  exact ⟨a + t, by grind⟩

variable {q : ℕ → Prop}
variable [DecidablePred q]

@[gcongr]
/-
**Nat.count_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：count_mono_left {n : Nat} (hpq : forall k < n, p k -> q k) : count p n <= 
count q n
参数：hpq : forall k < n, p k -> q k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.countP_mono_left`：∀ {α : Type u_1} {p q : α → Bool} {l : List α}, (
∀ x ∈ l, p x = true → q x = true) → List.countP p l ≤ List.countP q l
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem count_mono_left {n : ℕ} (hpq : ∀ k < n, p k → q k) : count p n ≤ count q n :=
  List.countP_mono_left <| by simpa

end Count

end Nat

