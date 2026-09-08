/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Gödel's Beta Function Lemma

This file proves Gödel's Beta Function Lemma, used to prove the First Incompleteness Theorem. It
permits quantification over finite sequences of natural numbers in formal theories of arithmetic.
This Beta Function has no connection with the unrelated Beta Function defined in analysis. Note
that `Nat.beta` and `Nat.unbeta` provide similar functionality to `Encodable.encodeList` and
`Encodable.decodeList`. We define these separately, because it is easier to prove that `Nat.beta`
and `Nat.unbeta` are arithmetically definable, and this is hard to prove that for
`Encodable.encodeList` and `Encodable.decodeList` directly. The arithmetic
definability is needed for the proof of the First Incompleteness Theorem.

## Main result

- `beta_unbeta_coe`: Gödel's Beta Function Lemma.

## Implementation note

This code is a step towards eventually including a proof of Gödel's First Incompleteness Theorem
and other key results from the repository https://github.com/iehality/lean4-logic.

## References

* [R. Kaye, *Models of Peano arithmetic*][kaye1991]
* <https://en.wikipedia.org/wiki/G%C3%B6del%27s_%CE%B2_function>

## Tags

Gödel, beta function
-/

@[expose] public section

namespace Nat

/-
**Nat.coprime_mul_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprime_mul_succ {n m a} (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1
)
参数：ha : m - n ∣ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.succ_sub_succ`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `Nat.dvd_sub`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m - n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
lemma coprime_mul_succ {n m a} (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    apply pp.ne_one
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hn (this.mul_left n)

variable {m : ℕ}

set_option backward.privateInPublic true in
/-
**Nat.supOfSeq** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def supOfSeq (a : Fin m → ℕ) : ℕ := max m (Finset.sup .univ a) + 1

set_option backward.privateInPublic true in
/-
**Nat.coprimes** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def coprimes (a : Fin m → ℕ) : Fin m → ℕ := fun i => (i + 1) * (supOfSeq a)! + 1

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Nat.coprimes_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprimes_lt (a : Fin m -> Nat) (i) : a i < coprimes a i
参数：a : Fin m -> Nat；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_add_one_iff`：∀ {m n : ℕ}, m < n + 1 ↔ m ≤ n
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
lemma coprimes_lt (a : Fin m → ℕ) (i) : a i < coprimes a i := by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a ≤ (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa only [coprimes] using lt_of_lt_of_le h₁ h₂

open scoped Function in -- required for scoped `on` notation
/-
**Nat.pairwise_coprime_coprimes** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairwise_coprime_coprimes (a : Fin m → ℕ) : Pairwise (Coprime on coprimes a) := by
  intro i j hij
  wlog! ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne ltij hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_succ_of_le (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.dvd_factorial (by lia)
      (by simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hja)))

/-- Gödel's Beta Function. This is similar to `(Encodable.decodeList)[i]`, but it is easier to
prove that it is arithmetically definable. -/
/-
**Nat.beta** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：beta (n i : Nat) : Nat
参数：n i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Gödel's Beta Function. This is similar to `(Encodable.decodeList)[i]`, but it is
 easier to
prove that it is arithmetically definable.
-/
def beta (n i : ℕ) : ℕ := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Inverse of Gödel's Beta Function. This is similar to `Encodable.encodeList`, but it is easier
to prove that it is arithmetically definable. -/
/-
**Nat.unbeta** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：unbeta (l : List Nat) : Nat
参数：l : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of Gödel's Beta Function. This is similar to `Encodable.encodeList`, but
 it is easier
to prove that it is arithmetically definable.
-/
def unbeta (l : List ℕ) : ℕ :=
  (chineseRemainderOfFinset (ι := Fin l.length) (l[·]) (coprimes (l[·])) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : ℕ).pair
  (supOfSeq (m := l.length) (l[·]))!

/-- **Gödel's Beta Function Lemma** -/
/-
**Nat.beta_unbeta_coe** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：beta_unbeta_coe (l : List Nat) (i : Fin l.length) : beta (unbeta l) i = l[
i]
参数：l : List Nat；i : Fin l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用引理 `Nat.mod_eq_of_modEq`：mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b
 < n) : a % n = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.pairwise_univ`：pairwise_univ : (univ : Set α).Pairwise r ↔ Pairwise 
r
· 使用定理 `_private.Mathlib.Logic.Godel.GodelBetaFunction.0.Nat.pairwise_coprime_co
primes`：∀ {m : ℕ} (a : Fin m → ℕ), Pairwise (Function.onFun Nat.Coprime (Nat.cop
rimes✝ a))
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `Nat.coprimes_lt`：coprimes_lt (a : Fin m -> Nat) (i) : a i < coprimes a i

--- 原说明 ---
**Gödel's Beta Function Lemma**
-/
lemma beta_unbeta_coe (l : List ℕ) (i : Fin l.length) : beta (unbeta l) i = l[i] := by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt _ _)

end Nat

