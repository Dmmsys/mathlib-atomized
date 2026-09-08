/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.List.Lattice
public import Mathlib.Data.Bool.Basic
public import Mathlib.Order.Lattice

/-!
# Intervals in ℕ

This file defines intervals of naturals. `List.Ico m n` is the list of integers greater than `m`
and strictly less than `n`.

## TODO
- Define `Ioo` and `Icc`, state basic lemmas about them.
- Also do the versions for integers?
- One could generalise even further, defining 'locally finite partial orders', for which
  `Set.Ico a b` is `[Finite]`, and 'locally finite total orders', for which there is a list model.
- Once the above is done, get rid of `Int.range` (and maybe `List.range'`?).
-/

@[expose] public section


open Nat

namespace List

/-- `Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `Mathlib/Order/Interval/Basic.lean` for modelling intervals in general preorders, as well
as sibling definitions alongside it such as `Set.Ico`, `Multiset.Ico` and `Finset.Ico`
for sets, multisets and finite sets respectively.
-/
/-
**List.Ico** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：Ico (n m : Nat) : List Nat
参数：n m : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a

--- 原说明 ---
`Ico n m` is the list of natural numbers `n ≤ x < m`.
(Ico stands for "interval, closed-open".)

See also `Mathlib/Order/Interval/Basic.lean` for modelling intervals in general 
preorders, as well
as sibling definitions alongside it such as `Set.Ico`, `Multiset.Ico` and `Finse
t.Ico`
for sets, multisets and finite sets respectively.
-/
def Ico (n m : ℕ) : List ℕ :=
  range' n (m - n)

namespace Ico

/-
**List.Ico.zero_bot** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：zero_bot (n : Nat) : Ico 0 n = range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Ico.eq_1`：∀ (n m : ℕ), List.Ico n m = List.range' n (m - n)
· 使用定理 `Nat.sub_zero`：∀ (n : ℕ), n - 0 = n
· 使用定理 `List.range_eq_range'`：∀ {n : ℕ}, List.range n = List.range' 0 n
-/
theorem zero_bot (n : ℕ) : Ico 0 n = range n := by rw [Ico, Nat.sub_zero, range_eq_range']

@[simp]
/-
**List.Ico.length** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：length (n m : Nat) : length (Ico n m) = m - n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_range'`：∀ {s step n : ℕ}, (List.range' s n step).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length (n m : ℕ) : length (Ico n m) = m - n := by
  dsimp [Ico]
  simp [length_range']
/-
**List.Ico.pairwise_lt** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：pairwise_lt (n m : Nat) : Pairwise (· < ·) (Ico n m)
参数：n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
-/
theorem pairwise_lt (n m : ℕ) : Pairwise (· < ·) (Ico n m) := by
  dsimp [Ico]
  simp [pairwise_lt_range']
/-
**List.Ico.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：nodup (n m : Nat) : Nodup (Ico n m)
参数：n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
-/
theorem nodup (n m : ℕ) : Nodup (Ico n m) := by
  dsimp [Ico]
  simp [nodup_range']

@[simp]
/-
**List.Ico.mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := by
  suffices n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m by simp [Ico, this]
  lia
/-
**List.Ico.eq_nil_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m = []
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `List.range'_zero`：∀ {s step : ℕ}, List.range' s 0 step = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_nil_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = [] := by
  simp [Ico, Nat.sub_eq_zero_iff_le.mpr h]
/-
**List.Ico.map_add** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：map_add (n m k : Nat) : (Ico n m).map (k + ·) = Ico (n + k) (m + k)
参数：n m k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Ico.eq_1`：∀ (n m : ℕ), List.Ico n m = List.range' n (m - n)
· 使用定理 `List.map_add_range'`：∀ {a : ℕ} (s n step : ℕ), List.map (fun x => a + x)
 (List.range' s n step) = List.range' (a + s) n step
· 使用定理 `Nat.add_sub_add_right`：∀ (n k m : ℕ), n + k - (m + k) = n - m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem map_add (n m k : ℕ) : (Ico n m).map (k + ·) = Ico (n + k) (m + k) := by
  rw [Ico, Ico, map_add_range', Nat.add_sub_add_right m k, Nat.add_comm n k]
/-
**List.Ico.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：map_sub (n m k : Nat) (h₁ : k <= n) : ((Ico n m).map fun x => x - k) = Ico
 (n - k) (m - k)
参数：n m k : Nat；h₁ : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Ico.eq_1`：∀ (n m : ℕ), List.Ico n m = List.range' n (m - n)
· 使用定理 `Nat.sub_sub_sub_cancel_right`：∀ {a b c : ℕ}, c ≤ b → a - c - (b - c) = a
 - b
· 使用定理 `List.map_sub_range'`：∀ {step a s : ℕ}, a ≤ s → ∀ (n : ℕ), List.map (fun 
x => x - a) (List.range' s n step) = List.range' (s - a) n step
-/
theorem map_sub (n m k : ℕ) (h₁ : k ≤ n) :
    ((Ico n m).map fun x => x - k) = Ico (n - k) (m - k) := by
  rw [Ico, Ico, Nat.sub_sub_sub_cancel_right h₁, map_sub_range' h₁]

@[simp]
/-
**List.Ico.self_empty** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：self_empty {n : Nat} : Ico n n = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Ico.eq_nil_of_le`：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m =
 []
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem self_empty {n : ℕ} : Ico n n = [] :=
  eq_nil_of_le (le_refl n)

@[simp]
/-
**List.Ico.eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：eq_empty_iff {n m : Nat} : Ico n m = [] ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.length`：length (n m : Nat) : length (Ico n m) = m - n
· 使用定理 `List.length.eq_1`：∀ {α : Type u_1}, [].length = 0
· 使用定理 `List.Ico.eq_nil_of_le`：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m =
 []
-/
theorem eq_empty_iff {n m : ℕ} : Ico n m = [] ↔ m ≤ n :=
  Iff.intro (fun h => Nat.sub_eq_zero_iff_le.mp <| by rw [← length, h, List.length]) eq_nil_of_le
/-
**List.Ico.append_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：append_consecutive {n m l : Nat} (hnm : n <= m) (hml : m <= l) : Ico n m +
+ Ico m l = Ico n l
参数：hnm : n <= m；hml : m <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.one_mul`：∀ (n : ℕ), 1 * n = n
· 使用定理 `Nat.add_sub_cancel'`：∀ {n m : ℕ}, m ≤ n → m + (n - m) = n
· 使用定理 `List.range'_append`：∀ {s m n step : ℕ}, List.range' s m step ++ List.ran
ge' (s + step * m) n step = List.range' s (m + n) step
-/
theorem append_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
    Ico n m ++ Ico m l = Ico n l := by
  dsimp only [Ico]
  convert! range'_append using 2
  · rw [Nat.one_mul, Nat.add_sub_cancel' hnm]
  · lia

@[simp]
/-
**List.Ico.inter_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：inter_consecutive (n m l : Nat) : Ico n m inter Ico m l = []
参数：n m l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_nil_iff_forall_not_mem`：∀ {α : Type u_1} {l : List α}, l = [] ↔ 
∀ (a : α), a ∉ l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = [] := by
  apply eq_nil_iff_forall_not_mem.2
  intro a
  simp only [and_imp, not_and, not_lt, List.mem_inter_iff, List.Ico.mem]
  intro _ h₂ h₃
  exfalso
  exact not_lt_of_ge h₃ h₂

@[simp]
/-
**List.Ico.bagInter_consecutive** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：bagInter_consecutive (n m l : Nat) : @List.bagInter Nat instBEqOfDecidable
Eq (Ico n m) (Ico m l) = []
参数：n m l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.bagInter_nil_iff_inter_nil`：∀ {α : Type u_1} [inst : DecidableEq α]
 (l₁ l₂ : List α), l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
· 使用定理 `List.Ico.inter_consecutive`：inter_consecutive (n m l : Nat) : Ico n m in
ter Ico m l = []
-/
theorem bagInter_consecutive (n m l : Nat) :
    @List.bagInter ℕ instBEqOfDecidableEq (Ico n m) (Ico m l) = [] :=
  (bagInter_nil_iff_inter_nil _ _).2 (by convert! inter_consecutive n m l)

@[simp]
/-
**List.Ico.succ_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：succ_singleton {n : Nat} : Ico n (n + 1) = [n]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `List.range'_one`：∀ {s step : ℕ}, List.range' s 1 step = [s]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem succ_singleton {n : ℕ} : Ico n (n + 1) = [n] := by
  dsimp [Ico]
  simp [Nat.add_sub_cancel_left]
/-
**List.Ico.succ_top** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：succ_top {n m : Nat} (h : n <= m) : Ico n (m + 1) = Ico n m ++ [m]
参数：h : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.succ_singleton`：succ_singleton {n : Nat} : Ico n (n + 1) = [n]
· 使用定理 `List.Ico.append_consecutive`：append_consecutive {n m l : Nat} (hnm : n <
= m) (hml : m <= l) : Ico n m ++ Ico m l = Ico n l
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = Ico n m ++ [m] := by
  rwa [← succ_singleton, append_consecutive]
  exact Nat.le_succ _
/-
**List.Ico.eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：eq_cons {n m : Nat} (h : n < m) : Ico n m = n :: Ico (n + 1) m
参数：h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.append_consecutive`：append_consecutive {n m l : Nat} (hnm : n <
= m) (hml : m <= l) : Ico n m ++ Ico m l = Ico n l
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `List.Ico.succ_singleton`：succ_singleton {n : Nat} : Ico n (n + 1) = [n]
-/
theorem eq_cons {n m : ℕ} (h : n < m) : Ico n m = n :: Ico (n + 1) m := by
  rw [← append_consecutive (Nat.le_succ n) h, succ_singleton]
  rfl

@[simp]
/-
**List.Ico.pred_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：pred_singleton {m : Nat} (h : 0 < m) : Ico (m - 1) m = [m - 1]
参数：h : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.range'_one`：∀ {s step : ℕ}, List.range' s 1 step = [s]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = [m - 1] := by
  simp [Ico, Nat.sub_sub_self (succ_le_of_lt h)]
/-
**List.Ico.isChain_succ** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：isChain_succ (n m : Nat) : IsChain (fun a b => b = succ a) (Ico n m)
参数：n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Ico.eq_cons`：eq_cons {n m : Nat} (h : n < m) : Ico n m = n :: Ico (
n + 1) m
· 使用定理 `List.isChain_range'`：∀ (s n step : ℕ), List.IsChain (fun a b => b = a + 
step) (List.range' s n step)
· 使用定理 `List.Ico.eq_nil_of_le`：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m =
 []
-/
theorem isChain_succ (n m : ℕ) : IsChain (fun a b => b = succ a) (Ico n m) := by
  by_cases! h : n < m
  · rw [eq_cons h]
    unfold List.Ico
    exact isChain_range' _ (_ + 1) 1
  · rw [eq_nil_of_le h]
    exact .nil
/-
**List.Ico.notMem_top** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：notMem_top {n m : Nat} : m ∉ Ico n m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem notMem_top {n m : ℕ} : m ∉ Ico n m := by simp
/-
**List.Ico.filter_lt_of_top_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_lt_of_top_le {n m l : Nat} (hml : m <= l) : ((Ico n m).filter fun x
 => x < l) = Ico n m
参数：hml : m <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_self`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, List.
filter p l = l ↔ ∀ a ∈ l, p a = true
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Ico.mem`：mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) :
    ((Ico n m).filter fun x => x < l) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    simp only [(lt_of_lt_of_le (mem.1 hk).2 hml), decide_true]
/-
**List.Ico.filter_lt_of_le_bot** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_lt_of_le_bot {n m l : Nat} (hln : l <= n) : ((Ico n m).filter fun x
 => x < l) = []
参数：hln : l <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_nil_iff`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, Li
st.filter p l = [] ↔ ∀ a ∈ l, ¬p a = true
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Ico.mem`：mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m
-/
theorem filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : ((Ico n m).filter fun x => x < l) = [] :=
  filter_eq_nil_iff.2 fun k hk => by
     simp only [decide_eq_true_eq, not_lt]
     apply le_trans hln
     exact (mem.1 hk).1
/-
**List.Ico.filter_lt_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_lt_of_ge {n m l : Nat} (hlm : l <= m) : ((Ico n m).filter fun x => 
x < l) = Ico n l
参数：hlm : l <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.append_consecutive`：append_consecutive {n m l : Nat} (hnm : n <
= m) (hml : m <= l) : Ico n m ++ Ico m l = Ico n l
· 使用定理 `List.filter_append`：∀ {α : Type u_1} {p : α → Bool} (l₁ l₂ : List α), Li
st.filter p (l₁ ++ l₂) = List.filter p l₁ ++ List.filter p l₂
· 使用定理 `List.Ico.filter_lt_of_top_le`：filter_lt_of_top_le {n m l : Nat} (hml : m
 <= l) : ((Ico n m).filter fun x => x < l) = Ico n m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `List.Ico.filter_lt_of_le_bot`：filter_lt_of_le_bot {n m l : Nat} (hln : l
 <= n) : ((Ico n m).filter fun x => x < l) = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.Ico.eq_nil_of_le`：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m =
 []
-/
theorem filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) :
    ((Ico n m).filter fun x => x < l) = Ico n l := by
  rcases le_total n l with hnl | hln
  · rw [← append_consecutive hnl hlm, filter_append, filter_lt_of_top_le (le_refl l),
      filter_lt_of_le_bot (le_refl l), append_nil]
  · rw [eq_nil_of_le hln, filter_lt_of_le_bot hln]

@[simp]
/-
**List.Ico.filter_lt** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_lt (n m l : Nat) : ((Ico n m).filter fun x => x < l) = Ico n (min m
 l)
参数：n m l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `List.Ico.filter_lt_of_top_le`：filter_lt_of_top_le {n m l : Nat} (hml : m
 <= l) : ((Ico n m).filter fun x => x < l) = Ico n m
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `List.Ico.filter_lt_of_ge`：filter_lt_of_ge {n m l : Nat} (hlm : l <= m) :
 ((Ico n m).filter fun x => x < l) = Ico n l
-/
theorem filter_lt (n m l : ℕ) :
    ((Ico n m).filter fun x => x < l) = Ico n (min m l) := by
  rcases le_total m l with hml | hlm
  · rw [min_eq_left hml, filter_lt_of_top_le hml]
  · rw [min_eq_right hlm, filter_lt_of_ge hlm]
/-
**List.Ico.filter_le_of_le_bot** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_le_of_le_bot {n m l : Nat} (hln : l <= n) : ((Ico n m).filter fun x
 => l <= x) = Ico n m
参数：hln : l <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_self`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, List.
filter p l = l ↔ ∀ a ∈ l, p a = true
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Ico.mem`：mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m
-/
theorem filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) :
    ((Ico n m).filter fun x => l ≤ x) = Ico n m :=
  filter_eq_self.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact le_trans hln (mem.1 hk).1
/-
**List.Ico.filter_le_of_top_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_le_of_top_le {n m l : Nat} (hml : m <= l) : ((Ico n m).filter fun x
 => l <= x) = []
参数：hml : m <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_nil_iff`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, Li
st.filter p l = [] ↔ ∀ a ∈ l, ¬p a = true
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Ico.mem`：mem {n m l : Nat} : l in Ico n m ↔ n <= l ∧ l < m
-/
theorem filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : ((Ico n m).filter fun x => l ≤ x) = [] :=
  filter_eq_nil_iff.2 fun k hk => by
    rw [decide_eq_true_eq]
    exact not_le_of_gt (lt_of_lt_of_le (mem.1 hk).2 hml)
/-
**List.Ico.filter_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_le_of_le {n m l : Nat} (hnl : n <= l) : ((Ico n m).filter fun x => 
l <= x) = Ico l m
参数：hnl : n <= l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.append_consecutive`：append_consecutive {n m l : Nat} (hnm : n <
= m) (hml : m <= l) : Ico n m ++ Ico m l = Ico n l
· 使用定理 `List.filter_append`：∀ {α : Type u_1} {p : α → Bool} (l₁ l₂ : List α), Li
st.filter p (l₁ ++ l₂) = List.filter p l₁ ++ List.filter p l₂
· 使用定理 `List.Ico.filter_le_of_top_le`：filter_le_of_top_le {n m l : Nat} (hml : m
 <= l) : ((Ico n m).filter fun x => l <= x) = []
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `List.Ico.filter_le_of_le_bot`：filter_le_of_le_bot {n m l : Nat} (hln : l
 <= n) : ((Ico n m).filter fun x => l <= x) = Ico n m
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `List.Ico.eq_nil_of_le`：eq_nil_of_le {n m : Nat} (h : m <= n) : Ico n m =
 []
-/
theorem filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) :
    ((Ico n m).filter fun x => l ≤ x) = Ico l m := by
  rcases le_total l m with hlm | hml
  · rw [← append_consecutive hnl hlm, filter_append, filter_le_of_top_le (le_refl l),
      filter_le_of_le_bot (le_refl l), nil_append]
  · rw [eq_nil_of_le hml, filter_le_of_top_le hml]

@[simp]
/-
**List.Ico.filter_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_le (n m l : Nat) : ((Ico n m).filter fun x => l <= x) = Ico (max n 
l) m
参数：n m l : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `List.Ico.filter_le_of_le`：filter_le_of_le {n m l : Nat} (hnl : n <= l) :
 ((Ico n m).filter fun x => l <= x) = Ico l m
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `List.Ico.filter_le_of_le_bot`：filter_le_of_le_bot {n m l : Nat} (hln : l
 <= n) : ((Ico n m).filter fun x => l <= x) = Ico n m
-/
theorem filter_le (n m l : ℕ) : ((Ico n m).filter fun x => l ≤ x) = Ico (max n l) m := by
  rcases le_total n l with hnl | hln
  · rw [max_eq_right hnl, filter_le_of_le hnl]
  · rw [max_eq_left hln, filter_le_of_le_bot hln]
/-
**List.Ico.filter_lt_of_succ_bot** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_lt_of_succ_bot {n m : Nat} (hnm : n < m) : ((Ico n m).filter fun x 
=> x < n + 1) = [n]
参数：hnm : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Ico.filter_lt`：filter_lt (n m l : Nat) : ((Ico n m).filter fun x =>
 x < l) = Ico n (min m l)
· 使用定理 `List.Ico.succ_singleton`：succ_singleton {n : Nat} : Ico n (n + 1) = [n]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) :
    ((Ico n m).filter fun x => x < n + 1) = [n] := by
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm
  simp [filter_lt n m (n + 1), r]

@[simp]
/-
**List.Ico.filter_le_of_bot** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：filter_le_of_bot {n m : Nat} (hnm : n < m) : ((Ico n m).filter fun x => x 
<= n) = [n]
参数：hnm : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Ico.filter_lt_of_succ_bot`：filter_lt_of_succ_bot {n m : Nat} (hnm :
 n < m) : ((Ico n m).filter fun x => x < n + 1) = [n]
· 使用定理 `List.filter_congr`：∀ {α : Type u_1} {p q : α → Bool} {l : List α}, (∀ x 
∈ l, p x = q x) → List.filter p l = List.filter q l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
-/
theorem filter_le_of_bot {n m : ℕ} (hnm : n < m) : ((Ico n m).filter fun x => x ≤ n) = [n] := by
  rw [← filter_lt_of_succ_bot hnm]
  exact filter_congr fun _ _ => by
    simpa using Nat.lt_succ_iff.symm

/-- For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
/-
**List.Ico.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `List.Ico`。
形式化陈述：trichotomy (n a b : Nat) : n < a ∨ b <= n ∨ n in Ico a b
参数：n a b : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any natural numbers n, a, and b, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
theorem trichotomy (n a b : ℕ) : n < a ∨ b ≤ n ∨ n ∈ Ico a b := by
  grind [mem]

end Ico

end List

