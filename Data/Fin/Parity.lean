/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Iván Renison
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.ZMod.Defs

/-!
# Parity in `Fin n`

In this file we prove that an element `k : Fin n` is even in `Fin n`
iff `n` is odd or `Fin.val k` is even.

We also prove a lemma about parity of `Fin.succAbove i j + Fin.predAbove j i`
which can be used to prove `d ∘ d = 0` for de Rham cohomologies.
-/

public section

open Fin

namespace Fin

open Fin.CommRing

variable {n : ℕ} {k : Fin n}

/-
**Fin.even_succAbove_add_predAbove** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：even_succAbove_add_predAbove (i : Fin (n + 1)) (j : Fin n) : Even (i.succA
bove j + j.predAbove i : Nat) ↔ Odd (i + j : Nat)
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.succAbove_of_castSucc_lt`：succAbove_of_castSucc_lt (p : Fin (n + 1))
 (i : Fin n) (h : castSucc i < p) : p.succAbove i = castSucc i
· 使用引理 `Fin.ne_zero_of_lt`：ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b !
= 0
· 使用引理 `Fin.predAbove_of_castSucc_lt`：predAbove_of_castSucc_lt (p : Fin n) (i : 
Fin (n + 1)) (h : castSucc p < i) : p.predAbove i = i.pred (Fin.ne_zero_of_lt h)
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Fin.succAbove_of_le_castSucc`：succAbove_of_le_castSucc (p : Fin (n + 1))
 (i : Fin n) (h : p <= castSucc i) : p.succAbove i = i.succ
· 使用定理 `Fin.ne_of_lt`：∀ {n : ℕ} {a b : Fin n}, a < b → a ≠ b
· 使用定理 `Fin.lt_of_le_of_lt`：∀ {n : ℕ} {a b c : Fin n}, a ≤ b → b < c → a < c
· 使用定理 `Fin.castSucc_lt_last`：∀ {n : ℕ} (a : Fin n), a.castSucc < Fin.last n
· 使用引理 `Fin.predAbove_of_le_castSucc`：predAbove_of_le_castSucc (p : Fin n) (i : 
Fin (n + 1)) (h : i <= castSucc p) : p.predAbove i = i.castPred (Fin.ne_of_lt <|
 Fin.lt_of_le_of_l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem even_succAbove_add_predAbove (i : Fin (n + 1)) (j : Fin n) :
    Even (i.succAbove j + j.predAbove i : ℕ) ↔ Odd (i + j : ℕ) := by
  rcases lt_or_ge j.castSucc i with hji | hij
  · have : 1 ≤ (i : ℕ) := (Nat.zero_le j).trans_lt hji
    simp [succAbove_of_castSucc_lt _ _ hji, predAbove_of_castSucc_lt _ _ hji, this, iff_comm,
      parity_simps]
  · simp [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij,
      ← Nat.not_even_iff_odd, not_iff, not_iff_comm, parity_simps]
/-
**Fin.neg_one_pow_succAbove_add_predAbove** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：neg_one_pow_succAbove_add_predAbove {R : Type*} [Monoid R] [HasDistribNeg 
R] (i : Fin (n + 1)) (j : Fin n) : (-1 : R) ^ (i.succAbove j + j.predAbove i : N
at) = -(-1) ^ (i + j : Nat)
参数：i : Fin (n + 1)；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用引理 `neg_one_pow_congr`：neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ 
m = (-1) ^ n
· 使用定理 `Fin.even_succAbove_add_predAbove`：even_succAbove_add_predAbove (i : Fin 
(n + 1)) (j : Fin n) : Even (i.succAbove j + j.predAbove i : Nat) ↔ Odd (i + j :
 Nat)
· 使用定理 `Nat.even_add_one`：∀ {n : ℕ}, Even (n + 1) ↔ ¬Even n
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma neg_one_pow_succAbove_add_predAbove {R : Type*} [Monoid R] [HasDistribNeg R]
    (i : Fin (n + 1)) (j : Fin n) :
    (-1 : R) ^ (i.succAbove j + j.predAbove i : ℕ) = -(-1) ^ (i + j : ℕ) := by
  rw [← neg_one_mul (_ ^ _), ← pow_succ', neg_one_pow_congr]
  rw [even_succAbove_add_predAbove, Nat.even_add_one, Nat.not_even_iff_odd]
/-
**Fin.even_of_val** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_of_val (h : Even k.val) : Even k
参数：h : Even k.val。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用定理 `Even.natCast`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] {n : ℕ}, Even
 n → Even ↑n
-/
lemma even_of_val (h : Even k.val) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast
/-
**Fin.odd_of_val** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_of_val [NeZero n] (h : Odd k.val) : Odd k
参数：h : Odd k.val。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用引理 `Odd.natCast`：Odd.natCast {R : Type*} [Semiring R] {n : Nat} (hn : Odd n)
 : Odd (n : R)
-/
lemma odd_of_val [NeZero n] (h : Odd k.val) : Odd k := by
  rw [← Fin.cast_val_eq_self k]
  exact h.natCast
/-
**Fin.even_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_of_odd (hn : Odd n) (k : Fin n) : Even k
参数：hn : Odd n；k : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fin.pos`：∀ {n : ℕ} (i : Fin n), 0 < n
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用引理 `Fin.even_of_val`：even_of_val (h : Even k.val) : Even k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用定理 `Fin.natCast_self`：∀ (n : ℕ) [inst : NeZero n], ↑n = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Even.natCast`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] {n : ℕ}, Even
 n → Even ↑n
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
-/
lemma even_of_odd (hn : Odd n) (k : Fin n) : Even k := by
  have : NeZero n := ⟨k.pos.ne'⟩
  rcases k.val.even_or_odd with hk | hk
  · exact even_of_val hk
  · simpa using (hk.add_odd hn).natCast (α := Fin n)
/-
**Fin.odd_of_odd** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_of_odd [NeZero n] (hn : Odd n) (k : Fin n) : Odd k
参数：hn : Odd n；k : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用定理 `Fin.natCast_self`：∀ (n : ℕ) [inst : NeZero n], ↑n = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Odd.natCast`：Odd.natCast {R : Type*} [Semiring R] {n : Nat} (hn : Odd n)
 : Odd (n : R)
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用引理 `Fin.odd_of_val`：odd_of_val [NeZero n] (h : Odd k.val) : Odd k
-/
lemma odd_of_odd [NeZero n] (hn : Odd n) (k : Fin n) : Odd k := by
  rcases k.val.even_or_odd with hk | hk
  · simpa using (Even.add_odd hk hn).natCast (R := Fin n)
  · exact odd_of_val hk
/-
**Fin.even_iff_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_iff_of_even (hn : Even n) : Even k ↔ Even k.val
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_add_eq_ite`：val_add_eq_ite {n : Nat} (a b : Fin n) : (↑(a + b) :
 Nat) = if n <= a + b then a + b - n else a + b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fin.even_of_val`：even_of_val (h : Even k.val) : Even k
-/
lemma even_iff_of_even (hn : Even n) : Even k ↔ Even k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, even_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add_eq_ite]
  split_ifs with h <;> simp [Nat.even_sub, *]
/-
**Fin.odd_iff_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ Odd k.val
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_add`：∀ {n : ℕ} (a b : Fin n), ↑(a + b) = (↑a + ↑b) % n
· 使用定理 `Fin.val_mul`：∀ {n : ℕ} (a b : Fin n), ↑(a * b) = ↑a * ↑b % n
· 使用定理 `Fin.coe_ofNat_eq_mod`：coe_ofNat_eq_mod (m n : Nat) [NeZero m] : ((ofNat(
n) : Fin m) : Nat) = ofNat(n) % m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_mul_mod`：∀ (m n l : ℕ), m % l * n % l = m * n % l
· 使用定理 `Nat.add_mod_mod`：∀ (m n k : ℕ), (m + n % k) % k = (m + n) % k
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
· 使用引理 `Nat.odd_add_one`：odd_add_one {n : Nat} : Odd (n + 1) ↔ ¬ Odd n
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `Fin.odd_of_val`：odd_of_val [NeZero n] (h : Odd k.val) : Odd k
-/
lemma odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ Odd k.val := by
  rcases hn with ⟨n, rfl⟩
  refine ⟨?_, odd_of_val⟩
  rintro ⟨l, rfl⟩
  rw [val_add, val_mul, coe_ofNat_eq_mod, coe_ofNat_eq_mod]
  simp only [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.odd_iff]
  rw [Nat.mod_mod_of_dvd _ ⟨n, (two_mul n).symm⟩, ← Nat.odd_iff, Nat.odd_add_one,
    Nat.not_odd_iff_even]
  simp

/-- In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even. -/
/-
**Fin.even_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_iff : Even k ↔ (Odd n ∨ Even k.val)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.even_iff_of_even`：even_iff_of_even (hn : Even n) : Even k ↔ Even k.v
al
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用引理 `Fin.even_of_odd`：even_of_odd (hn : Odd n) (k : Fin n) : Even k
· 使用引理 `Fin.even_of_val`：even_of_val (h : Even k.val) : Even k

--- 原说明 ---
In `Fin n`, all elements are even for odd `n`,
otherwise an element is even iff its `Fin.val` value is even.
-/
lemma even_iff : Even k ↔ (Odd n ∨ Even k.val) := by
  refine ⟨fun hk ↦ ?_, or_imp.mpr ⟨(even_of_odd · k), even_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (even_iff_of_even hn).mp hk
/-
**Fin.even_iff_imp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_iff_imp : Even k ↔ (Even n -> Even k.val)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `Fin.even_iff`：even_iff : Even k ↔ (Odd n ∨ Even k.val)
-/
lemma even_iff_imp : Even k ↔ (Even n → Even k.val) := by
  rw [imp_iff_not_or, Nat.not_even_iff_odd]
  exact even_iff

/-- In `Fin n`, all elements are odd for odd `n`,
otherwise an element is odd iff its `Fin.val` value is odd. -/
/-
**Fin.odd_iff** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_iff [NeZero n] : Odd k ↔ Odd n ∨ Odd k.val
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Fin.odd_iff_of_even`：odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ 
Odd k.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_imp`：∀ {a b c : Prop}, a ∨ b → c ↔ (a → c) ∧ (b → c)
· 使用引理 `Fin.odd_of_odd`：odd_of_odd [NeZero n] (hn : Odd n) (k : Fin n) : Odd k
· 使用引理 `Fin.odd_of_val`：odd_of_val [NeZero n] (h : Odd k.val) : Odd k

--- 原说明 ---
In `Fin n`, all elements are odd for odd `n`,
otherwise an element is odd iff its `Fin.val` value is odd.
-/
lemma odd_iff [NeZero n] : Odd k ↔ Odd n ∨ Odd k.val := by
  refine ⟨fun hk ↦ ?_, or_imp.mpr ⟨(odd_of_odd · k), odd_of_val⟩⟩
  rw [← Nat.not_even_iff_odd, ← imp_iff_not_or]
  exact fun hn ↦ (odd_iff_of_even hn).mp hk
/-
**Fin.odd_iff_imp** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_iff_imp [NeZero n] : Odd k ↔ (Even n -> Odd k.val)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imp_iff_not_or`：imp_iff_not_or : a -> b ↔ ¬a ∨ b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用引理 `Fin.odd_iff`：odd_iff [NeZero n] : Odd k ↔ Odd n ∨ Odd k.val
-/
lemma odd_iff_imp [NeZero n] : Odd k ↔ (Even n → Odd k.val) := by
  rw [imp_iff_not_or, Nat.not_even_iff_odd]
  exact odd_iff
/-
**Fin.even_iff_mod_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_iff_mod_of_even (hn : Even n) : Even k ↔ k.val % 2 = 0
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.even_iff_of_even`：even_iff_of_even (hn : Even n) : Even k ↔ Even k.v
al
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
-/
lemma even_iff_mod_of_even (hn : Even n) : Even k ↔ k.val % 2 = 0 := by
  rw [even_iff_of_even hn]
  exact Nat.even_iff
/-
**Fin.odd_iff_mod_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_iff_mod_of_even [NeZero n] (hn : Even n) : Odd k ↔ k.val % 2 = 1
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.odd_iff_of_even`：odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ 
Odd k.val
· 使用引理 `Nat.odd_iff`：odd_iff : Odd n ↔ n % 2 = 1
-/
lemma odd_iff_mod_of_even [NeZero n] (hn : Even n) : Odd k ↔ k.val % 2 = 1 := by
  rw [odd_iff_of_even hn]
  exact Nat.odd_iff
/-
**Fin.not_odd_iff_even_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：not_odd_iff_even_of_even [NeZero n] (hn : Even n) : ¬Odd k ↔ Even k
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.even_iff_of_even`：even_iff_of_even (hn : Even n) : Even k ↔ Even k.v
al
· 使用引理 `Fin.odd_iff_of_even`：odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ 
Odd k.val
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
-/
lemma not_odd_iff_even_of_even [NeZero n] (hn : Even n) : ¬Odd k ↔ Even k := by
  rw [even_iff_of_even hn, odd_iff_of_even hn]
  exact Nat.not_odd_iff_even
/-
**Fin.not_even_iff_odd_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：not_even_iff_odd_of_even [NeZero n] (hn : Even n) : ¬Even k ↔ Odd k
参数：hn : Even n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.even_iff_of_even`：even_iff_of_even (hn : Even n) : Even k ↔ Even k.v
al
· 使用引理 `Fin.odd_iff_of_even`：odd_iff_of_even [NeZero n] (hn : Even n) : Odd k ↔ 
Odd k.val
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
-/
lemma not_even_iff_odd_of_even [NeZero n] (hn : Even n) : ¬Even k ↔ Odd k := by
  rw [even_iff_of_even hn, odd_iff_of_even hn]
  exact Nat.not_even_iff_odd
/-
**Fin.odd_add_one_iff_even** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：odd_add_one_iff_even [NeZero n] : Odd (k + 1) ↔ Even k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Even.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → Odd
 (a + 1)
-/
lemma odd_add_one_iff_even [NeZero n] : Odd (k + 1) ↔ Even k :=
  ⟨fun ⟨k, hk⟩ ↦ add_right_cancel hk ▸ even_two_mul k, Even.add_one⟩
/-
**Fin.even_add_one_iff_odd** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：even_add_one_iff_odd [NeZero n] : Even (k + 1) ↔ Odd k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Even.sub_odd`：Even.sub_odd (ha : Even a) (hb : Odd b) : Odd (a - b)
· 使用定理 `Even.add_self`：∀ {α : Type u_2} [inst : Add α] (r : α), Even (r + r)
· 使用定理 `odd_one`：∀ {α : Type u_2} [inst : Semiring α], Odd 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Odd.add_one`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Odd a → Even 
(a + 1)
-/
lemma even_add_one_iff_odd [NeZero n] : Even (k + 1) ↔ Odd k :=
  ⟨fun ⟨k, hk⟩ ↦ eq_sub_iff_add_eq.mpr hk ▸ (Even.add_self k).sub_odd odd_one, Odd.add_one⟩

end Fin

