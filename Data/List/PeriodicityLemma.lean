/-
Copyright (c) 2025 Štěpán Holub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Štěpán Holub
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.TacticAnalysis.Declarations

/-! # Periods of words (Lists)

This file defines the notion of a period of a word (list) and proves the Periodicity Lemma.

## Implementation notes

The definition of a period is given in terms of self-overlap.
Equivalent characterizations in terms of indices and modular arithmetic are also provided.

## Tags

periodicity lemma, Fine-Wilf theorem, period, periodicity

-/

@[expose] public section

variable {α : Type _}

open Nat

namespace List
/--
`HasPeriod w p`, means that the list `w` has the period `p`,
which can be seen in two equivalent ways:
· The list `w` starts again after the prefix of length `p`. That is, `w` overlaps with itself
  with offset `p`.
· The element of `w` at index `i` is the same as the element at index `i + p`, for all `i`
The definition is given in terms of the self-overlap.
-/
/-
**List.HasPeriod** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：HasPeriod (w : List α) (p : Nat) : Prop
参数：w : List α；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasPeriod w p`, means that the list `w` has the period `p`,
which can be seen in two equivalent ways:
· The list `w` starts again after the prefix of length `p`. That is, `w` overlap
s with itself
  with offset `p`.
· The element of `w` at index `i` is the same as the element at index `i + p`, f
or all `i`
The definition is given in terms of the self-overlap.
-/
def HasPeriod (w : List α) (p : ℕ) : Prop := w <+: take p w ++ w

/-- This is the equivalent definition of `HasPeriod w p` by indices. -/
/-
**List.hasPeriod_iff_getElem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：hasPeriod_iff_getElem? {p : Nat} {w : List α} : HasPeriod w p ↔ forall i <
 w.length - p, w[i]? = w[i + p]?
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the equivalent definition of `HasPeriod w p` by indices.
-/
lemma hasPeriod_iff_getElem? {p : ℕ} {w : List α} :
    HasPeriod w p ↔ ∀ i < w.length - p, w[i]? = w[i + p]? := by
  constructor
  · rw [HasPeriod]
    intro pref j len
    have i1 : j < w.length := by lia
    have i2 : j + p < w.length := by lia
    have min : p < w.length := by lia
    have : j + p - (List.take p w).length = j := by
      simp_all [min_eq_left_of_lt]
    simp_all [getElem_append_right, IsPrefix.getElem pref, min_eq_left_of_lt]
  · intro lhs
    rw [HasPeriod]
    have drop : drop p w <+: w := by
      simp only [prefix_iff_getElem?, length_drop, getElem_drop]
      intro i leni
      have len : i + p < w.length := by lia
      simp_all only [getElem?_pos, add_comm p i]
    rw [← prefix_append_right_inj (w.take p)] at drop
    simp_all

@[simp]
/-
**List.hasPeriod_zero** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：hasPeriod_zero (w : List α) : HasPeriod w 0
参数：w : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma hasPeriod_zero (w : List α) : HasPeriod w 0 := by
  simp [HasPeriod]

@[simp]
/-
**List.hasPeriod_of_length_le** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：hasPeriod_of_length_le (w : List α) (p : Nat) (large : w.length <= p) : Ha
sPeriod w p
参数：w : List α；p : Nat；large : w.length <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.HasPeriod.eq_1`：∀ {α : Type u_1} (w : List α) (p : ℕ), w.HasPeriod 
p = (w <+: List.take p w ++ w)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.take_eq_self_iff`：∀ {α : Type u} (x : List α) {n : ℕ}, List.take n 
x = x ↔ x.length ≤ n
-/
lemma hasPeriod_of_length_le (w : List α) (p : ℕ) (large : w.length ≤ p) : HasPeriod w p := by
  rw [HasPeriod]; simp_all [(take_eq_self_iff w).mpr large]
/-
**List.hasPeriod_empty** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：hasPeriod_empty (p : Nat) : HasPeriod ([] : List α) p
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
lemma hasPeriod_empty (p : ℕ) : HasPeriod ([] : List α) p := by
  simp
/-
**List.HasPeriod.getElem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma HasPeriod.getElem?_mod (p i : ℕ) (w : List α) (per : HasPeriod w p)
    (less : i < w.length) : w[i % p]? = w[i]? := by
  by_cases p_zero : p = 0
  · rw [p_zero, mod_zero]
  · cases lt_or_ge i p with
    | inl small =>
        have eq : i % p = i := mod_eq_of_lt small
        rw [eq]
    | inr large =>
        have len' : i - p < w.length := by lia
        have IH : w[(i - p) % p]? = w[i - p]? := per.getElem?_mod p (i - p) w len'
        rw [hasPeriod_iff_getElem?] at per
        have minus : i - p < w.length - p := by lia
        have per' := per (i - p) minus
        simp only [large, Nat.sub_add_cancel] at per'
        have mod : i % p = (i - p) % p := mod_eq_sub_mod large
        aesop

/-- An equivalent definition of `HasPeriod w p` by modular equivalence on indices. -/
/-
**List.hasPeriod_iff_forall_getElem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：hasPeriod_iff_forall_getElem?_mod {p : Nat} {w : List α} : HasPeriod w p ↔
 (forall i < w.length, w[i]? = w[i % p]?)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalent definition of `HasPeriod w p` by modular equivalence on indices.
-/
lemma hasPeriod_iff_forall_getElem?_mod {p : ℕ} {w : List α} :
    HasPeriod w p ↔ (∀ i < w.length, w[i]? = w[i % p]?) := by
  constructor
  · intro per i len
    exact Eq.symm (per.getElem?_mod p i w len)
  · intro mod
    rw [hasPeriod_iff_getElem?]
    intro i less
    rw [mod (i + p) (by lia), add_mod_right, mod i (by lia)]

/-- If `w` has a period `p`, then any of its factors has a period `p` as well. -/
/-
**List.HasPeriod.factor** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod`。
形式化陈述：∀ {α : Type u_1} {u v w : List α} {p : ℕ}, (u ++ v ++ w).HasPeriod p → v.H
asPeriod p
参数：u ++ v ++ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem?_append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l
₁.length ≤ i → (l₁ ++ l₂)[i]? = l₂[i - l₁.length]?
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `List.getElem?_append_left`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, i 
< l₁.length → (l₁ ++ l₂)[i]? = l₁[i]?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `w` has a period `p`, then any of its factors has a period `p` as well.
-/
lemma HasPeriod.factor {u v w : List α} {p : ℕ} (per : HasPeriod (u ++ v ++ w) p) :
    HasPeriod v p := by
  suffices ∀ j < v.length - p, v[j]? = v[j + p]? by simpa [hasPeriod_iff_getElem?]
  intro j len
  have shift_position : (u ++ (v ++ w))[j + u.length]? = v[j]? := by
    rw [getElem?_append_right, Nat.add_sub_cancel, getElem?_append_left]
    all_goals lia
  have shift_position' : (u ++ (v ++ w))[j + u.length + p]? = v[j + p]? := by
    have eq : j + u.length + p - u.length = j + p := by lia
    rw [getElem?_append_right]
    · rw [getElem?_append_left]
      · exact congrArg (getElem? v) eq
      · lia
    · lia
  have : ∀ i < u.length + (v.length + w.length) - p,
      (u ++ (v ++ w))[i]? = (u ++ (v ++ w))[i + p]? := by
    simp_all [hasPeriod_iff_getElem?]
  rw [← shift_position', ← shift_position]
  exact this (j + u.length) (by lia)
/-
**List.HasPeriod.infix** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod`。
形式化陈述：∀ {α : Type u_1} {u w : List α} {p : ℕ}, w.HasPeriod p → u <:+: w → u.HasP
eriod p
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.HasPeriod.factor`：∀ {α : Type u_1} {u v w : List α} {p : ℕ}, (u ++ 
v ++ w).HasPeriod p → v.HasPeriod p
-/
lemma HasPeriod.infix {u w : List α} {p : ℕ} (per : HasPeriod w p) (h : u <:+: w) :
    HasPeriod u p := by
  obtain ⟨s, t, rfl⟩ := h
  exact per.factor
/-
**List.HasPeriod.drop_prefix** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod`。
形式化陈述：∀ {α : Type u_1} {w : List α} (p : ℕ), w.HasPeriod p → List.drop p w <+: w
参数：p : ℕ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prefix_append_right_inj`：∀ {α : Type u_1} {l₁ l₂ : List α} (l : Lis
t α), l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma HasPeriod.drop_prefix {w : List α} (p : ℕ) (per : HasPeriod w p) :
    drop p w <+: w := by
  rw [← prefix_append_right_inj (take p w)]
  simp_all [HasPeriod, take_append_drop]

/-- If `w` has a period `p`, and we extend it to the left by its prefix whose length divides `p`,
then the resulting word also has a period `p`. -/
/-
**List.HasPeriod.take_append** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod`。
形式化陈述：∀ {α : Type u_1} (p n : ℕ) (w : List α), p ∣ n → n ≤ w.length → w.HasPerio
d p → (List.take n w ++ w).HasPeriod p
参数：p n : ℕ；w : List α；List.take n w ++ w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.hasPeriod_iff_forall_getElem?_mod`：∀ {α : Type u_1} {p : ℕ} {w : Li
st α}, w.HasPeriod p ↔ ∀ i < w.length, w[i]? = w[i % p]?
· 使用定理 `List.HasPeriod.getElem?_mod`：∀ {α : Type u_1} (p i : ℕ) (w : List α), w.
HasPeriod p → i < w.length → w[i % p]? = w[i]?
· 使用定理 `List.getElem?_append_left`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, i 
< l₁.length → (l₁ ++ l₂)[i]? = l₁[i]?
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.getElem?_take_of_lt`：∀ {α : Type u_1} {l : List α} {i j : ℕ}, i < j
 → (List.take j l)[i]? = l[i]?
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.sub_mul_mod`：∀ {x k n : ℕ}, n * k ≤ x → (x - n * k) % n = x % n
· 使用定理 `List.getElem?_append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} {i : ℕ}, l
₁.length ≤ i → (l₁ ++ l₂)[i]? = l₂[i - l₁.length]?
· 使用定理 `getElem?_pos`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `implies_dep_congr_ctx`：∀ {p₁ p₂ q₁ : Prop}, p₁ = p₂ → ∀ {q₂ : p₂ → Prop}
, (∀ (h : p₂), q₁ = q₂ h) → (p₁ → q₁) = ∀ (h : p₂), q₂ h
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
If `w` has a period `p`, and we extend it to the left by its prefix whose length
 divides `p`,
then the resulting word also has a period `p`.
-/
lemma HasPeriod.take_append (p n : ℕ) (w : List α) (dvd : p ∣ n)
    (len : n ≤ w.length) (per : HasPeriod w p) : HasPeriod (take n w ++ w) p := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos n with rfl | pos
  · simp_all
  rw [hasPeriod_iff_forall_getElem?_mod]
  have mod_w : ∀ i < w.length, w[i % p]? = w[i]? := (per.getElem?_mod)
  suffices ∀ i < n + w.length, (take n w ++ w)[i]? = (take n w ++ w)[i % p]? by simp_all
  intro i less_i
  have mod_p : ∀ j < n + length w, (take n w ++ w)[j]? = w[j % p]? := by
    intro j less_j
    by_cases j_lt_n : j < n
    · -- indices within `take n w` can be reduced due to the period of `w`
      calc
        (take n w ++ w)[j]? = (take n w)[j]? := getElem?_append_left (by simp_all)
        _ = w[j]? := getElem?_take_of_lt j_lt_n
        _ = w[j % p]? := Eq.symm (mod_w j (by lia))
    · -- larger indices are indices of `w` decreased by `n`
      have j_minus : j - n < w.length := by lia
      have n_le_j : n ≤ j := le_of_not_gt j_lt_n; clear j_lt_n;
      have j_mod : (j - n) % p = j % p := by
        calc
          (j - n) % p = (j - p * (n / p)) % p := by rw [Nat.mul_div_cancel' dvd]
          _ = j % p := sub_mul_mod ((Nat.mul_div_cancel' dvd).symm ▸ n_le_j)
      calc
        (take n w ++ w)[j]? = w[j - (take n w).length]? := getElem?_append_right (by simp_all)
        _ = w[j - n]? := by simp_all
        _ = w[(j - n) % p]? := Eq.symm (mod_w (j - n) (by lia))
        _ = w[j % p]? := by rw [j_mod]
  have less_mod : i % p < n + w.length := by
    have : i % p < p := mod_lt i p_pos; have : p ≤ n := le_of_dvd pos dvd; lia
  rw [mod_p i less_i, mod_p (i % p) less_mod, mod_mod]

/-- Induction step for the `periodicity_lemma` -/
/-
**List.HasPeriod.drop_of_hasPeriod_add** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod
`。
形式化陈述：∀ {α : Type u_1} {q k : ℕ} {w : List α}, w.HasPeriod q → w.HasPeriod (k + 
q) → (List.drop q w).HasPeriod k
参数：k + q；List.drop q w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.hasPeriod_iff_getElem?`：∀ {α : Type u_1} {p : ℕ} {w : List α}, w.Ha
sPeriod p ↔ ∀ i < w.length - p, w[i]? = w[i + p]?
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getElem?_drop`：∀ {α : Type u_1} {xs : List α} {i j : ℕ}, (List.drop
 i xs)[j]? = xs[i + j]?
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Induction step for the `periodicity_lemma`
-/
lemma HasPeriod.drop_of_hasPeriod_add {q k : ℕ} {w : List α}
    (per_q : HasPeriod w q) (per_plus : HasPeriod w (k + q)) :
    HasPeriod (drop q w) k := by
  rw [hasPeriod_iff_getElem?] at per_plus per_q ⊢
  simp only [length_drop, getElem?_drop]
  intro i i_lt
  calc
     w[q + i]? = w[i + q]? := congrArg (getElem? w) (add_comm q i)
     _ = w[i]? := (per_q i (by lia)).symm
     _ = w[i + (k + q)]? := per_plus i (by lia)
     _ = w[q + (i + k)]? := congr_arg (getElem? w) (by lia)

/-- The **Periodicity Lemma**, also known as the **Fine and Wilf theorem**, shows that
if word `w` of length at least `p + q - gcd p q` has two periods `p` and `q`,
then it has a period `gcd p q`.
The proof is similar to the Euclidean algorithm for computing `gcd`.
-/
/-
**List.HasPeriod.gcd** 是 Mathlib 中的一个定理，位于命名空间 `List.HasPeriod`。
形式化陈述：∀ {α : Type u_1} {w : List α} {p q : ℕ},   w.HasPeriod p → w.HasPeriod q →
 p + q - p.gcd q ≤ w.length → w.HasPeriod (p.gcd q)
参数：p.gcd q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.HasPeriod.gcd._unary`：∀ {α : Type u_1}   (_x : (w : List α) ×' (p :
 ℕ) ×' (q : ℕ) ×' (_ : w.HasPeriod p) ×' (_ : w.HasPeriod q) ×' p + q - p.gcd q 
≤ w.length),   …

--- 原说明 ---
The **Periodicity Lemma**, also known as the **Fine and Wilf theorem**, shows th
at
if word `w` of length at least `p + q - gcd p q` has two periods `p` and `q`,
then it has a period `gcd p q`.
The proof is similar to the Euclidean algorithm for computing `gcd`.
-/
theorem HasPeriod.gcd {w : List α} {p q : ℕ} (per_p : HasPeriod w p) (per_q : HasPeriod w q)
    (len : p + q - p.gcd q ≤ w.length) : HasPeriod w (p.gcd q) := by
  rcases Nat.eq_zero_or_pos p with rfl | p_pos
  · simp_all [HasPeriod]
  rcases Nat.eq_zero_or_pos q with rfl | q_pos
  · simp_all
  cases hyp : compare p q with
  | lt => -- if `p` is less than `q`, switch the two periods
      have p_lt_q := Nat.compare_eq_lt.mp hyp
      exact (gcd_comm q p ▸ per_q.gcd) per_p (add_comm p q ▸ len)
  | eq => simpa [(Nat.compare_eq_eq).mp hyp]
  | gt =>
      have q_lt_p : q < p := Nat.compare_eq_gt.mp hyp
      have gcd_lt_p : p.gcd q < p := by
        have : p.gcd q ≠ p := by
          simp [gcd_eq_left_iff_dvd, not_dvd_of_pos_of_lt q_pos q_lt_p]
        exact this.lt_of_le (gcd_le_left q p_pos)
      have per_diff : HasPeriod (drop q w) (p - q) := by
        have : p = (p - q) + q := by lia
        exact per_q.drop_of_hasPeriod_add (this ▸ per_p)
      have per_q' : HasPeriod (drop q w) q := by
        apply @HasPeriod.factor _ (take q w) (drop q w) [] q
        all_goals simp_all
      have gcd_stable : (p - q).gcd q = p.gcd q := gcd_sub_self_left (le_of_lt q_lt_p)
      have drop_len : q ≤ (drop q w).length := by
        rw [length_drop]
        have : p.gcd q ≤ p - q := by
          rw [← gcd_stable]; apply gcd_le_left q; lia
        lia
      have take_eq : take q (drop q w) = take q w := by
          let ⟨z, hz⟩ := per_q.drop_prefix
          convert_to take q (drop q w) = take q (drop q w ++ z)
          · rw [hz]
          exact (take_append_of_le_length drop_len).symm
      -- the induction step
      have IH : HasPeriod (drop q w) ((p - q).gcd q) :=
        per_diff.gcd per_q' (by simp; lia)
      convert_to HasPeriod (take q (drop q w) ++ drop q w) (p.gcd q)
      · rw [take_eq, take_append_drop q w]
      · exact (gcd_stable ▸ IH).take_append (p.gcd q) q (drop q w)
          (gcd_dvd_right p q) drop_len
  termination_by (q, p)
  decreasing_by
    all_goals grind

end List

