/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.Choose.Factorization

/-!
# Natural number multiplicity

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `Nat.Prime.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n / p + ... + n / p ^ b` for any `b` such that `n / p ^ (b + 1) = 0`. See `padicValNat_factorial`
  for this result stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_factorial` for a related result.
* `Nat.Prime.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than
  that of `n!`.
* `Nat.Prime.multiplicity_choose`: Kummer's Theorem. The multiplicity of `p` in `n.choose k` is the
  number of carries when `k` and `n - k` are added in base `p`. See `padicValNat_choose` for the
  same result but stated in the language of `p`-adic valuations and
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` for a related result.

## Other declarations

* `Nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `Nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `Nat.Prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `Prime` and `Nat.Prime`.

## TODO

Derive results from the corresponding ones `Mathlib.Data.Nat.Factorization.Multiplicity`

## Tags

Legendre, p-adic
-/

public section

open Finset

namespace Nat

/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
/-
**Nat.emultiplicity_eq_card_pow_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：emultiplicity_eq_card_pow_dvd {m n b : Nat} (hm : m != 1) (hn : 0 < n) (hb
 : log m n < b) : emultiplicity m n = #{i in Ico 1 b | m ^ i ∣ n}
参数：hm : m != 1；hn : 0 < n；hb : log m n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`：FiniteMultiplicity.pow_d
vd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : Nat} : a ^ k ∣ b ↔ k <
= multiplicity a b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_log_of_pow_le`：le_log_of_pow_le {b x y : Nat} (hb : 1 < b) (h : b
 ^ x <= y) : x <= log b y
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The multiplicity of `m` in `n` is the number of positive natural numbers `i` suc
h that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound
 greater than
`log m n`.
-/
theorem emultiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b) :
    emultiplicity m n = #{i ∈ Ico 1 b | m ^ i ∣ n} :=
  have fin := Nat.finiteMultiplicity_iff.2 ⟨hm, hn⟩
  calc
    emultiplicity m n = #(Ico 1 <| multiplicity m n + 1) := by
      simp [fin.emultiplicity_eq_multiplicity]
    _ = #{i ∈ Ico 1 b | m ^ i ∣ n} :=
      congr_arg _ <|
        congr_arg card <|
          Finset.ext fun i => by
            simp only [mem_Ico, Nat.lt_succ_iff,
              fin.pow_dvd_iff_le_multiplicity, mem_filter,
              and_assoc, and_congr_right_iff, iff_and_self]
            intro hi h
            rw [← fin.pow_dvd_iff_le_multiplicity] at h
            rcases m with - | m
            · rw [zero_pow, zero_dvd_iff] at h
              exacts [(hn.ne' h).elim, one_le_iff_ne_zero.1 hi]
            refine LE.le.trans_lt ?_ hb
            exact le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
                (le_of_dvd hn h)

namespace Prime

/-
**Nat.Prime.emultiplicity_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_one {p : Nat} (hp : p.Prime) : emultiplicity p 1 = 0
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_of_one_right`：emultiplicity_of_one_right {a : α} (ha : ¬Is
Unit a) : emultiplicity a 1 = 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem emultiplicity_one {p : ℕ} (hp : p.Prime) : emultiplicity p 1 = 0 :=
  emultiplicity_of_one_right hp.prime.not_isUnit
/-
**Nat.Prime.emultiplicity_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_mul {p m n : Nat} (hp : p.Prime) : emultiplicity p (m * n) =
 emultiplicity p m + emultiplicity p n
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem emultiplicity_mul {p m n : ℕ} (hp : p.Prime) :
    emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n :=
  _root_.emultiplicity_mul hp.prime
/-
**Nat.Prime.emultiplicity_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_pow {p m n : Nat} (hp : p.Prime) : emultiplicity p (m ^ n) =
 n * emultiplicity p m
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_pow`：emultiplicity_pow {p a : α} (hp : Prime p) {k : Nat} 
: emultiplicity p (a ^ k) = k * emultiplicity p a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem emultiplicity_pow {p m n : ℕ} (hp : p.Prime) :
    emultiplicity p (m ^ n) = n * emultiplicity p m :=
  _root_.emultiplicity_pow hp.prime
/-
**Nat.Prime.emultiplicity_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_self {p : Nat} (hp : p.Prime) : emultiplicity p p = 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteMultiplicity.emultiplicity_self`：FiniteMultiplicity.emultiplicity_
self {a : α} (hfin : FiniteMultiplicity a a) : emultiplicity a a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
-/
theorem emultiplicity_self {p : ℕ} (hp : p.Prime) : emultiplicity p p = 1 :=
  (Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, hp.pos⟩).emultiplicity_self
/-
**Nat.Prime.emultiplicity_pow_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_pow_self {p n : Nat} (hp : p.Prime) : emultiplicity p (p ^ n
) = n
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `emultiplicity_pow_self`：emultiplicity_pow_self {p : α} (h0 : p != 0) (hu
 : ¬IsUnit p) (n : Nat) : emultiplicity p (p ^ n) = n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem emultiplicity_pow_self {p n : ℕ} (hp : p.Prime) : emultiplicity p (p ^ n) = n :=
  _root_.emultiplicity_pow_self hp.ne_zero hp.prime.not_isUnit n

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
/-
**Nat.Prime.emultiplicity_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_factorial {p : Nat} (hp : p.Prime) : forall {n b : Nat}, log
 p n < b -> emultiplicity p n ! = (∑ i in Ico 1 b, n / p ^ i : Nat) | 0, b, _ =>
 by simp [Ico, hp.emultiplicity_one] | n + 1, b, hb => calc emultiplicity p (n +
 1)! = emultiplicity p n ! + emultiplicity p (n + 1)
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. Thi
s sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`.
-/
theorem emultiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → emultiplicity p n ! = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ)
  | 0, b, _ => by simp [Ico, hp.emultiplicity_one]
  | n + 1, b, hb =>
    calc
      emultiplicity p (n + 1)! = emultiplicity p n ! + emultiplicity p (n + 1) := by
        rw [factorial_succ, hp.emultiplicity_mul, add_comm]
      _ = (∑ i ∈ Ico 1 b, n / p ^ i : ℕ) + #{i ∈ Ico 1 b | p ^ i ∣ n + 1} := by
        rw [emultiplicity_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), ←
          emultiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) : ℕ) := by
        rw [sum_add_distrib, sum_boole]
        simp
      _ = (∑ i ∈ Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        congr_arg _ <| Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/-- For a prime number `p`, taking `(p - 1)` times the multiplicity of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
/-
**Nat.Prime.sub_one_mul_multiplicity_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Pr
ime`。
形式化陈述：sub_one_mul_multiplicity_factorial {n p : Nat} (hp : p.Prime) : (p - 1) * 
multiplicity p n ! = n - (p.digits n).sum
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `Nat.Prime.emultiplicity_factorial`：emultiplicity_factorial {p : Nat} (hp
 : p.Prime) : forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in I
co 1 b, n / p ^ i : Nat…
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_add'`：∀ {α : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : AddCommMonoid α] [inst_2 : PartialOrder α]   [IsOrderedCancelAdd
Monoid α]…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a prime number `p`, taking `(p - 1)` times the multiplicity of `p` in `n!` e
quals `n` minus
the sum of base `p` digits of `n`.
-/
theorem sub_one_mul_multiplicity_factorial {n p : ℕ} (hp : p.Prime) :
    (p - 1) * multiplicity p n ! =
    n - (p.digits n).sum := by
  simp only [multiplicity_eq_of_emultiplicity_eq_some <|
      emultiplicity_factorial hp <| lt_succ_of_lt <| Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range, ←
    sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

set_option backward.isDefEq.respectTransparency false in
/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
/-
**Nat.Prime.emultiplicity_factorial_mul_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prim
e`。
形式化陈述：emultiplicity_factorial_mul_succ {n p : Nat} (hp : p.Prime) : emultiplicit
y p (p * (n + 1))! = emultiplicity p (p * n)! + emultiplicity p (n + 1) + 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`.
-/
theorem emultiplicity_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    emultiplicity p (p * (n + 1))! = emultiplicity p (p * n)! + emultiplicity p (n + 1) + 1 := by
  have hp' := hp.prime
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by lia
  have hm : emultiplicity p (p * n)! ≠ ⊤ := by
    rw [Ne, emultiplicity_eq_top, Classical.not_not, Nat.finiteMultiplicity_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), emultiplicity p m = 0 := by
    intro m hm
    rw [emultiplicity_eq_zero, not_dvd_iff_lt_mul_succ _ hp.pos]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, Finset.emultiplicity_prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  intro h
  rw [WithTop.add_left_inj h, sum_Ico_succ_top h2, hp.emultiplicity_mul, hp.emultiplicity_self,
    sum_congr rfl h4, sum_const_zero, zero_add, add_comm 1]

/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
/-
**Nat.Prime.emultiplicity_factorial_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_factorial_mul {n p : Nat} (hp : p.Prime) : emultiplicity p (
p * n)! = emultiplicity p n ! + n
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.Prime.emultiplicity_factorial_mul_succ`：emultiplicity_factorial_mul_
succ {n p : Nat} (hp : p.Prime) : emultiplicity p (p * (n + 1))! = emultiplicity
 p (p * n)! + emultiplicity p (n…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Prime.emultiplicity_mul`：emultiplicity_mul {p m n : Nat} (hp : p.Pri
me) : emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)

--- 原说明 ---
The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`.
-/
theorem emultiplicity_factorial_mul {n p : ℕ} (hp : p.Prime) :
    emultiplicity p (p * n)! = emultiplicity p n ! + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [hp, emultiplicity_factorial_mul_succ, ih, factorial_succ, emultiplicity_mul,
      cast_add, cast_one, ← add_assoc]
    congr 1
    rw [add_comm, add_assoc]

/-- The multiplicity of a prime `p` in `p ^ n` is the sum of `p ^ i`, where `i` ranges between `0`
and `n - 1`. -/
/-
**Nat.Prime.multiplicity_factorial_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：multiplicity_factorial_pow {n p : Nat} (hp : p.Prime) : multiplicity p (p 
^ n).factorial = ∑ i in Finset.range n, p ^ i
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.Prime.emultiplicity_one`：emultiplicity_one {p : Nat} (hp : p.Prime) 
: emultiplicity p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.Prime.emultiplicity_factorial_mul`：emultiplicity_factorial_mul {n p 
: Nat} (hp : p.Prime) : emultiplicity p (p * n)! = emultiplicity p n ! + n
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)

--- 原说明 ---
The multiplicity of a prime `p` in `p ^ n` is the sum of `p ^ i`, where `i` rang
es between `0`
and `n - 1`.
-/
theorem multiplicity_factorial_pow {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p ^ n).factorial = ∑ i ∈ Finset.range n, p ^ i := by
  rw [← ENat.natCast_inj, ← (Nat.finiteMultiplicity_iff.2
      ⟨hp.ne_one, (p ^ n).factorial_pos⟩).emultiplicity_eq_multiplicity]
  induction n with
  | zero => simp [hp.emultiplicity_one]
  | succ n h =>
    rw [pow_succ', hp.emultiplicity_factorial_mul, h, Finset.sum_range_succ, ENat.natCast_add]

/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
/-
**Nat.Prime.pow_dvd_factorial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：pow_dvd_factorial_iff {p : Nat} {n r b : Nat} (hp : p.Prime) (hbn : log p 
n < b) : p ^ r ∣ n ! ↔ r <= ∑ i in Ico 1 b, n / p ^ i
参数：hp : p.Prime；hbn : log p n < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENat.natCast_le_natCast`：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= 
(m : Nat∞) ↔ n <= m
· 使用定理 `Nat.Prime.emultiplicity_factorial`：emultiplicity_factorial {p : Nat} (hp
 : p.Prime) : forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in I
co 1 b, n / p ^ i : Nat…
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i
`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater th
an `log p n`
-/
theorem pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r ≤ ∑ i ∈ Ico 1 b, n / p ^ i := by
  rw [← ENat.natCast_le_natCast, ← hp.emultiplicity_factorial hbn, pow_dvd_iff_le_emultiplicity]
/-
**Nat.Prime.emultiplicity_factorial_le_div_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat.P
rime`。
形式化陈述：emultiplicity_factorial_le_div_pred {p : Nat} (hp : p.Prime) (n : Nat) : e
multiplicity p n ! <= (n / (p - 1) : Nat)
参数：hp : p.Prime；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.emultiplicity_factorial`：emultiplicity_factorial {p : Nat} (hp
 : p.Prime) : forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in I
co 1 b, n / p ^ i : Nat…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `WithTop.coe_mono`：∀ {α : Type u_1} [inst : Preorder α], Monotone fun a =
> ↑a
· 使用引理 `Nat.geom_sum_Ico_le`：Nat.geom_sum_Ico_le {b : Nat} (hb : 2 <= b) (a n : 
Nat) : ∑ i in Ico 1 n, a / b ^ i <= a / (b - 1)
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem emultiplicity_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    emultiplicity p n ! ≤ (n / (p - 1) : ℕ) := by
  rw [hp.emultiplicity_factorial (lt_succ_self _)]
  apply WithTop.coe_mono
  exact Nat.geom_sum_Ico_le hp.two_le _ _

/-- The multiplicity of `p` in `choose (n + k) k` is the number of carries when `k` and `n`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p (n + k)`. -/
/-
**Nat.Prime.emultiplicity_choose'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_choose' {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) 
< b) : emultiplicity p (choose (n + k) k) = #{i in Ico 1 b | p ^ i <= k % p ^ i 
+ n % p ^ i}
参数：hp : p.Prime；hnb : log p (n + k) < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.emultiplicity_mul`：emultiplicity_mul {p m n : Nat} (hp : p.Pri
me) : emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.Prime.emultiplicity_factorial`：emultiplicity_factorial {p : Nat} (hp
 : p.Prime) : forall {n b : Nat}, log p n < b -> emultiplicity p n ! = (∑ i in I
co 1 b, n / p ^ i : Nat…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.log_mono_right`：log_mono_right {b n m : Nat} (h : n <= m) : log b n 
<= log b m
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.multiplicity_choose_aux`：multiplicity_choose_aux {p n b k : Nat} (hp
 : p.Prime) (hkn : k <= n) : ∑ i in Finset.Ico 1 b, n / p ^ i = ((∑ i in Finset.
Ico 1 b, k / p ^ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `WithTop.add_right_cancel`：add_right_cancel [IsRightCancelAdd α] (hz : z 
!= ⊤) (h : x + z = y + z) : x = y
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `finiteMultiplicity_iff_emultiplicity_ne_top`：finiteMultiplicity_iff_emul
tiplicity_ne_top : FiniteMultiplicity a b ↔ emultiplicity a b != ⊤
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The multiplicity of `p` in `choose (n + k) k` is the number of carries when `k` 
and `n`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p (n + k)`.
-/
theorem emultiplicity_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    emultiplicity p (choose (n + k) k) = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ :
      emultiplicity p (choose (n + k) k) + emultiplicity p (k ! * n !) =
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + emultiplicity p (k ! * n !) := by
    rw [← hp.emultiplicity_mul, ← mul_assoc]
    have := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [this, hp.emultiplicity_factorial hnb, hp.emultiplicity_mul,
      hp.emultiplicity_factorial ((log_mono_right (le_add_left k n)).trans_lt hnb),
      hp.emultiplicity_factorial ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb)), multiplicity_choose_aux hp (le_add_left k n)]
    simp [add_comm]
  refine WithTop.add_right_cancel ?_ h₁
  apply finiteMultiplicity_iff_emultiplicity_ne_top.1
  exact Nat.finiteMultiplicity_iff.2 ⟨hp.ne_one, mul_pos (factorial_pos k) (factorial_pos n)⟩

/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
/-
**Nat.Prime.emultiplicity_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_choose {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : 
log p n < b) : emultiplicity p (choose n k) = #{i in Ico 1 b | p ^ i <= k % p ^ 
i + (n - k) % p ^ i}
参数：hp : p.Prime；hkn : k <= n；hnb : log p n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.emultiplicity_choose'`：emultiplicity_choose' {p n k b : Nat} (
hp : p.Prime) (hnb : log p (n + k) < b) : emultiplicity p (choose (n + k) k) = #
{i in Ico 1 b | p ^ i…

--- 原说明 ---
The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n
 - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`.
-/
theorem emultiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    emultiplicity p (choose n k) = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  have := Nat.sub_add_cancel hkn
  convert! @emultiplicity_choose' p (n - k) k b hp _
  · rw [this]
  exact this.symm ▸ hnb

/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
/-
**Nat.Prime.emultiplicity_le_emultiplicity_choose_add** 是 Mathlib 中的一个定理，位于命名空间 
`Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ∀ (n k : ℕ), emultiplicity p n ≤ emultiplicity p 
(n.choose k) + emultiplicity p k
参数：n k : ℕ；n.choose k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.emultiplicity_mul`：emultiplicity_mul {p m n : Nat} (hp : p.Pri
me) : emultiplicity p (m * n) = emultiplicity p m + emultiplicity p n
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_right`：emultiplicity_le_emultiplic
ity_of_dvd_right {a b c : α} (h : b ∣ c) : emultiplicity a b <= emultiplicity a 
c
· 使用定理 `Nat.add_one_mul_choose_eq`：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).c
hoose (k + 1) * (k + 1)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b

--- 原说明 ---
A lower bound on the multiplicity of `p` in `choose n k`.
-/
theorem emultiplicity_le_emultiplicity_choose_add {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, emultiplicity p n ≤ emultiplicity p (choose n k) + emultiplicity p k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    rw [← hp.emultiplicity_mul]
    refine emultiplicity_le_emultiplicity_of_dvd_right ?_
    rw [← add_one_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : ℕ}
/-
**Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity** 是 Mathlib 中的一个定理，
位于命名空间 `Nat.Prime`。
形式化陈述：emultiplicity_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k <
= p ^ n) (hk0 : k != 0) : emultiplicity p (choose (p ^ n) k) + emultiplicity p k
 = n
参数：hp : p.Prime；hkn : k <= p ^ n；hk0 : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.Prime.emultiplicity_choose`：emultiplicity_choose {p n k b : Nat} (hp
 : p.Prime) (hkn : k <= n) (hnb : log p n < b) : emultiplicity p (choose n k) = 
#{i in Ico 1 b | p ^…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.emultiplicity_eq_card_pow_dvd`：emultiplicity_eq_card_pow_dvd {m n b 
: Nat} (hm : m != 1) (hn : 0 < n) (hb : log m n < b) : emultiplicity m n = #{i i
n Ico 1 b | m ^ i ∣ n}
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Nat.log_mono_right`：log_mono_right {b n m : Nat} (h : n <= m) : log b n 
<= log b m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `WithTop.coe_mono`：∀ {α : Type u_1} [inst : Preorder α], Monotone fun a =
> ↑a
（共 37 条，此处仅展示前 30 条）
-/
theorem emultiplicity_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : emultiplicity p (choose (p ^ n) k) + emultiplicity p k = n :=
  le_antisymm
    (by
      have hdisj :
        Disjoint {i ∈ Ico 1 n.succ | p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i}
          {i ∈ Ico 1 n.succ | p ^ i ∣ k} := by
        simp +contextual [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [emultiplicity_choose hp hkn (lt_succ_self _),
        emultiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn)),
        ← Nat.cast_add]
      apply WithTop.coe_mono
      rw [log_pow hp.one_lt, ← card_union_of_disjoint hdisj, filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le
        fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
    (by rw [← hp.emultiplicity_pow_self]; exact emultiplicity_le_emultiplicity_choose_add hp _ _)
/-
**Nat.Prime.emultiplicity_choose_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`
。
形式化陈述：emultiplicity_choose_prime_pow {p n k : Nat} (hp : p.Prime) (hkn : k <= p 
^ n) (hk0 : k != 0) : emultiplicity p (choose (p ^ n) k) = ↑(n - multiplicity p 
k)
参数：hp : p.Prime；hkn : k <= p ^ n；hk0 : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity`：emultiplicit
y_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k 
!= 0) : emultiplicity p (choose (p ^ n) k) + emu…
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem emultiplicity_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    emultiplicity p (choose (p ^ n) k) = ↑(n - multiplicity p k) := by
  push_cast
  rw [← emultiplicity_choose_prime_pow_add_emultiplicity hp hkn hk0,
    (finiteMultiplicity_iff.2 ⟨hp.ne_one, Nat.pos_of_ne_zero hk0⟩).emultiplicity_eq_multiplicity,
    (finiteMultiplicity_iff.2 ⟨hp.ne_one, choose_pos hkn⟩).emultiplicity_eq_multiplicity]
  norm_cast
  rw [Nat.add_sub_cancel_right]
/-
**Nat.Prime.dvd_choose_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_choose_pow (hp : Prime p) (hk : k != 0) (hkp : k != p ^ n) : p ∣ (p ^ 
n).choose k
参数：hp : Prime p；hk : k != 0；hkp : k != p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `emultiplicity_ne_zero`：emultiplicity_ne_zero : emultiplicity a b != 0 ↔ 
a ∣ b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity`：emultiplicit
y_choose_prime_pow_add_emultiplicity (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k 
!= 0) : emultiplicity p (choose (p ^ n) k) + emu…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem dvd_choose_pow (hp : Prime p) (hk : k ≠ 0) (hkp : k ≠ p ^ n) : p ∣ (p ^ n).choose k := by
  obtain hkp | hkp := hkp.symm.lt_or_gt
  · simp [choose_eq_zero_of_lt hkp]
  refine emultiplicity_ne_zero.1 fun h => hkp.not_ge <| Nat.le_of_dvd hk.bot_lt ?_
  have H := hp.emultiplicity_choose_prime_pow_add_emultiplicity hkp.le hk
  rw [h, zero_add, emultiplicity_eq_coe] at H
  exact H.1
/-
**Nat.Prime.dvd_choose_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k != 0 ∧ k != p
 ^ n
参数：hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.Prime.dvd_choose_pow`：dvd_choose_pow (hp : Prime p) (hk : k != 0) (h
kp : k != p ^ n) : p ∣ (p ^ n).choose k
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k ≠ 0 ∧ k ≠ p ^ n := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simp [hp.ne_one] at h

end Prime

/-
**Nat.emultiplicity_two_factorial_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：emultiplicity_two_factorial_lt : forall {n : Nat} (_ : n != 0), emultiplic
ity 2 n ! < n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Bool.not_eq_false`：∀ (b : Bool), (¬b = false) = (b = true)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.Prime.emultiplicity_one`：emultiplicity_one {p : Nat} (hp : p.Prime) 
: emultiplicity p 1 = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.emultiplicity_factorial_mul`：emultiplicity_factorial_mul {n p 
: Nat} (hp : p.Prime) : emultiplicity p (p * n)! = emultiplicity p n ! + n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `WithTop.add_lt_add_right`：∀ {α : Type u} [inst : Add α] {x y z : WithTop
 α} [inst_1 : LT α] [AddRightStrictMono α], z ≠ ⊤ → x < y → x + z < y + z
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 41 条，此处仅展示前 30 条）
-/
theorem emultiplicity_two_factorial_lt : ∀ {n : ℕ} (_ : n ≠ 0), emultiplicity 2 n ! < n := by
  have h2 := prime_two.prime
  refine binaryRec ?_ ?_
  · exact fun h => False.elim <| h rfl
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn
      simp only [ne_eq, bit_eq_zero_iff, true_and, Bool.not_eq_false] at h
      simp only [bit, h, cond_true, mul_zero, zero_add, factorial_one]
      rw [Prime.emultiplicity_one]
      · exact zero_lt_one
      · decide
    have : emultiplicity 2 (2 * n)! < (2 * n : ℕ) := by
      rw [prime_two.emultiplicity_factorial_mul]
      rw [two_mul]
      push_cast
      apply WithTop.add_lt_add_right _ (ih hn)
      exact Ne.symm nofun
    cases b
    · simpa
    · suffices emultiplicity 2 (2 * n + 1) + emultiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [emultiplicity_mul, h2, prime_two, bit, factorial]
      rw [emultiplicity_eq_zero.2 (two_not_dvd_two_mul_add_one n), zero_add]
      refine this.trans ?_
      exact mod_cast lt_succ_self _

end Nat

