/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/
module

public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the multiplicity of prime factors within certain size
bounds in binomial coefficients. These include:

* `Nat.factorization_choose_le_log`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `Nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul`: Primes from `2 * n / 3` to `n`
  do not appear in the factorization of the `n`th central binomial coefficient.
* `Nat.factorization_choose_eq_zero_of_lt`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/

public section

open Finset List Finsupp

namespace Nat
variable {a b c : ℕ}

/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
/-
**Nat.factorization_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_factorial {p : Nat} (hp : p.Prime) : forall {n b : Nat}, log
 p n < b -> (n)!.factorization p = ∑ i in Ico 1 b, n / p ^ i | 0, b, _ => by sim
p | n + 1, b, hb => calc (n + 1)!.factorization p = (n + 1).factorization p + (n
)!.factorization p
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. Thi
s sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`.
-/
theorem factorization_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → (n)!.factorization p = ∑ i ∈ Ico 1 b, n / p ^ i
  | 0, b, _ => by simp
  | n + 1, b, hb =>
    calc
      (n + 1)!.factorization p = (n + 1).factorization p + (n)!.factorization p := by
        rw [factorial_succ, factorization_mul (zero_ne_add_one n).symm n.factorial_ne_zero,
          coe_add, Pi.add_apply]
      _ = #{i ∈ Ico 1 b | p ^ i ∣ n + 1} + ∑ i ∈ Ico 1 b, n / p ^ i := by
        rw [factorization_factorial hp ((log_mono_right <| le_succ _).trans_lt hb), add_left_inj]
        apply factorization_eq_card_pow_dvd_of_lt hp (zero_lt_succ n)
          (lt_pow_of_log_lt hp.one_lt hb)
      _ = ∑ i ∈ Ico 1 b, (n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0) := by
        simp [Nat.add_comm, sum_add_distrib, sum_boole]
      _ = ∑ i ∈ Ico 1 b, (n + 1) / p ^ i := Finset.sum_congr rfl fun _ _ => Nat.succ_div.symm

/-- For a prime number `p`, taking `(p - 1)` times the factorization of `p` in `n!` equals `n` minus
the sum of base `p` digits of `n`. -/
/-
**Nat.sub_one_mul_factorization_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sub_one_mul_factorization_factorial {n p : Nat} (hp : p.Prime) : (p - 1) *
 (n)!.factorization p = n - (p.digits n).sum
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_factorial`：factorization_factorial {p : Nat} (hp : p.P
rime) : forall {n b : Nat}, log p n < b -> (n)!.factorization p = ∑ i in Ico 1 b
, n / p ^ i | 0, …
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
For a prime number `p`, taking `(p - 1)` times the factorization of `p` in `n!` 
equals `n` minus
the sum of base `p` digits of `n`.
-/
theorem sub_one_mul_factorization_factorial {n p : ℕ} (hp : p.Prime) :
    (p - 1) * (n)!.factorization p = n - (p.digits n).sum := by
  simp only [factorization_factorial hp <| lt_succ_of_lt <| Nat.lt_add_one (log p n),
    ← Finset.sum_Ico_add' _ 0 _ 1, Ico_zero_eq_range,
    ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

/-- The factorization of `p` in `(p * (n + 1))!` is one more than the sum of the factorizations of
`p` in `(p * n)!` and `n + 1`. -/
/-
**Nat.factorization_factorial_mul_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_factorial_mul_succ {n p : Nat} (hp : p.Prime) : (p * (n + 1)
)!.factorization p = (p * n)!.factorization p + (n + 1).factorization p + 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
The factorization of `p` in `(p * (n + 1))!` is one more than the sum of the fac
torizations of
`p` in `(p * n)!` and `n + 1`.
-/
theorem factorization_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    (p * (n + 1))!.factorization p = (p * n)!.factorization p + (n + 1).factorization p + 1 := by
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1) := by linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1 := by lia
  have h4 m (hm : m ∈ Ico (p * n + 1) (p * (n + 1))) : m.factorization p = 0 := by
    apply factorization_eq_zero_of_not_dvd
    exact not_dvd_of_lt_of_lt_mul_succ (mem_Ico.mp hm).left (mem_Ico.mp hm).right
  rw [← prod_Ico_id_eq_factorial, factorization_prod_apply (fun _ hx ↦ ne_zero_of_lt
    (mem_Ico.mp hx).left), ← sum_Ico_consecutive _ h1 h3, add_assoc, sum_Ico_succ_top h2,
    ← prod_Ico_id_eq_factorial, factorization_prod_apply (fun _ hx ↦ ne_zero_of_lt
    (mem_Ico.mp hx).left), factorization_mul (ne_zero_of_lt h0) (zero_ne_add_one n).symm,
    coe_add, Pi.add_apply, hp.factorization_self, sum_congr rfl h4, sum_const_zero, zero_add,
    add_comm 1]

/-- The factorization of `p` in `(p * n)!` is `n` more than that of `n!`. -/
/-
**Nat.factorization_factorial_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_factorial_mul {n p : Nat} (hp : p.Prime) : (p * n)!.factoriz
ation p = (n)!.factorization p + n
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorization_factorial_mul_succ`：factorization_factorial_mul_succ {
n p : Nat} (hp : p.Prime) : (p * (n + 1))!.factorization p = (p * n)!.factorizat
ion p + (n + 1).factorizat…
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a

--- 原说明 ---
The factorization of `p` in `(p * n)!` is `n` more than that of `n!`.
-/
theorem factorization_factorial_mul {n p : ℕ} (hp : p.Prime) :
    (p * n)!.factorization p = (n)!.factorization p + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [factorization_factorial_mul_succ hp, ih, factorial_succ,
      factorization_mul (zero_ne_add_one n).symm (factorial_ne_zero n)]
    ring
/-
**Nat.factorization_factorial_le_div_pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_factorial_le_div_pred {p : Nat} (hp : p.Prime) (n : Nat) : (
n)!.factorization p <= (n / (p - 1) : Nat)
参数：hp : p.Prime；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_factorial`：factorization_factorial {p : Nat} (hp : p.P
rime) : forall {n b : Nat}, log p n < b -> (n)!.factorization p = ∑ i in Ico 1 b
, n / p ^ i | 0, …
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用引理 `Nat.geom_sum_Ico_le`：Nat.geom_sum_Ico_le {b : Nat} (hb : 2 <= b) (a n : 
Nat) : ∑ i in Ico 1 n, a / b ^ i <= a / (b - 1)
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem factorization_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n)!.factorization p ≤ (n / (p - 1) : ℕ) := by
  rw [factorization_factorial hp (Nat.lt_add_one (log p n))]
  exact Nat.geom_sum_Ico_le hp.two_le _ _
/-
**Nat.multiplicity_choose_aux** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：multiplicity_choose_aux {p n b k : Nat} (hp : p.Prime) (hkn : k <= n) : ∑ 
i in Finset.Ico 1 b, n / p ^ i = ((∑ i in Finset.Ico 1 b, k / p ^ i) + ∑ i in Fi
nset.Ico 1 b, (n - k) / p ^ i) + #{i in Ico 1 b | p ^ i <= k % p ^ i + (n - k) %
 p ^ i}
参数：hp : p.Prime；hkn : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_div`：∀ {a b c : ℕ}, 0 < c → (a + b) / c = a / c + b / c + if c ≤
 a % c + b % c then 1 else 0
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
-/
lemma multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i =
      ((∑ i ∈ Finset.Ico 1 b, k / p ^ i) + ∑ i ∈ Finset.Ico 1 b, (n - k) / p ^ i) +
        #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} :=
  calc
    ∑ i ∈ Finset.Ico 1 b, n / p ^ i = ∑ i ∈ Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ = ∑ i ∈ Finset.Ico 1 b,
          (k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0) := by
      simp only [Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by simp [sum_add_distrib, sum_boole]

/-- The factorization of `p` in `choose (n + k) k` is the number of carries when `k` and `n` are
added in base `p`. The set is expressed by filtering `Ico 1 b` where `b` is any bound greater
than `log p (n + k)`. -/
/-
**Nat.factorization_choose'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose' {p n k b : Nat} (hp : p.Prime) (hnb : log p (n + k) 
< b) : (choose (n + k) k).factorization p = #{i in Ico 1 b | p ^ i <= k % p ^ i 
+ n % p ^ i}
参数：hp : p.Prime；hnb : log p (n + k) < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.factorization_factorial`：factorization_factorial {p : Nat} (hp : p.P
rime) : forall {n b : Nat}, log p n < b -> (n)!.factorization p = ∑ i in Ico 1 b
, n / p ^ i | 0, …
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
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
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The factorization of `p` in `choose (n + k) k` is the number of carries when `k`
 and `n` are
added in base `p`. The set is expressed by filtering `Ico 1 b` where `b` is any 
bound greater
than `log p (n + k)`.
-/
theorem factorization_choose' {p n k b : ℕ} (hp : p.Prime) (hnb : log p (n + k) < b) :
    (choose (n + k) k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  have h₁ : (choose (n + k) k).factorization p + (k ! * n !).factorization p
    = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} + (k ! * n !).factorization p := by
    have h2 := (add_tsub_cancel_right n k) ▸ choose_mul_factorial_mul_factorial (le_add_left k n)
    rw [← Pi.add_apply, ← coe_add, ← factorization_mul (ne_of_gt <| choose_pos (le_add_left k n))
      (by positivity), ← mul_assoc, h2,
      factorization_factorial hp hnb, factorization_mul (factorial_ne_zero k) (factorial_ne_zero n),
      coe_add, Pi.add_apply, factorization_factorial hp ((log_mono_right (le_add_left k n)).trans_lt
      hnb), factorization_factorial hp ((log_mono_right (le_add_left n k)).trans_lt
      (add_comm n k ▸ hnb)), multiplicity_choose_aux hp (le_add_left k n)]
    simp only [add_tsub_cancel_right, add_comm]
  exact Nat.add_right_cancel h₁

/-- The factorization of `p` in `choose n k` is the number of carries when `k` and `n - k`
are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
is any bound greater than `log p n`. -/
/-
**Nat.factorization_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose {p n k b : Nat} (hp : p.Prime) (hkn : k <= n) (hnb : 
log p n < b) : (choose n k).factorization p = #{i in Ico 1 b | p ^ i <= k % p ^ 
i + (n - k) % p ^ i}
参数：hp : p.Prime；hkn : k <= n；hnb : log p n < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_choose'`：factorization_choose' {p n k b : Nat} (hp : p
.Prime) (hnb : log p (n + k) < b) : (choose (n + k) k).factorization p = #{i in 
Ico 1 b | p ^ i…
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n

--- 原说明 ---
The factorization of `p` in `choose n k` is the number of carries when `k` and `
n - k`
are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
is any bound greater than `log p n`.
-/
theorem factorization_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    (choose n k).factorization p = #{i ∈ Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  rw [← factorization_choose' hp ((Nat.sub_add_cancel hkn).symm ▸ hnb), Nat.sub_add_cancel hkn]

/-- Modified version of `emultiplicity_le_emultiplicity_of_dvd_right`
but for factorization. -/
/-
**Nat.factorization_le_factorization_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat
`。
形式化陈述：factorization_le_factorization_of_dvd_right (h : b ∣ c) (hb : b != 0) (hc 
: c != 0) : b.factorization a <= c.factorization a
参数：h : b ∣ c；hb : b != 0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `Nat.ne_zero_of_mul_ne_zero_right`：∀ {n m : ℕ}, n * m ≠ 0 → m ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Modified version of `emultiplicity_le_emultiplicity_of_dvd_right`
but for factorization.
-/
theorem factorization_le_factorization_of_dvd_right (h : b ∣ c) (hb : b ≠ 0) (hc : c ≠ 0) :
    b.factorization a ≤ c.factorization a := by
  obtain ⟨k, rfl⟩ := h; simp [factorization_mul hb (Nat.ne_zero_of_mul_ne_zero_right hc)]

/-- A lower bound on the factorization of `p` in `choose n k`. -/
/-
**Nat.factorization_le_factorization_choose_add** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {p n k : ℕ}, k ≤ n → k ≠ 0 → n.factorization p ≤ (n.choose k).factorizat
ion p + k.factorization p
参数：n.choose k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1
· 使用定理 `Nat.factorization_le_factorization_of_dvd_right`：factorization_le_factor
ization_of_dvd_right (h : b ∣ c) (hb : b != 0) (hc : c != 0) : b.factorization a
 <= c.factorization a
· 使用定理 `Nat.add_one_mul_choose_eq`：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).c
hoose (k + 1) * (k + 1)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n

--- 原说明 ---
A lower bound on the factorization of `p` in `choose n k`.
-/
theorem factorization_le_factorization_choose_add {p : ℕ} :
    ∀ {n k : ℕ}, k ≤ n → k ≠ 0 →
      n.factorization p ≤ (choose n k).factorization p + k.factorization p
  | n, 0, _, _ => by tauto
  | 0, x + 1, _, _ => by simp
  | n + 1, k + 1, hkn, hk => by
    rw [← Pi.add_apply, ← coe_add, ← factorization_mul (ne_of_gt <| choose_pos hkn)
      (zero_ne_add_one k).symm]
    refine factorization_le_factorization_of_dvd_right ?_ (zero_ne_add_one n).symm
      (Nat.mul_ne_zero (ne_of_gt <| choose_pos hkn) (by positivity))
    rw [← add_one_mul_choose_eq]
    exact dvd_mul_right _ _

variable {p n k : ℕ}
/-
**Nat.factorization_choose_prime_pow_add_factorization** 是 Mathlib 中的一个定理，位于命名空间
 `Nat`。
形式化陈述：factorization_choose_prime_pow_add_factorization (hp : p.Prime) (hkn : k <
= p ^ n) (hk0 : k != 0) : (choose (p ^ n) k).factorization p + k.factorization p
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
· 使用定理 `Nat.factorization_choose`：factorization_choose {p n k b : Nat} (hp : p.P
rime) (hkn : k <= n) (hnb : log p n < b) : (choose n k).factorization p = #{i in
 Ico 1 b | p ^…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.factorization_eq_card_pow_dvd_of_lt`：factorization_eq_card_pow_dvd_o
f_lt (hm : m.Prime) (hn : 0 < n) (hb : n < m ^ b) : n.factorization m = #{i in I
co 1 b | m ^ i ∣ n}
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.pow_lt_pow_succ`：∀ {a n : ℕ}, 1 < a → a ^ n < a ^ (n + 1)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.log_pow`：log_pow {b : Nat} (hb : 1 < b) (x : Nat) : log b (b ^ x) = 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.filter_union_right`：filter_union_right (s : Finset α) : s.filter 
p union s.filter q = s.filter fun x => p x ∨ q x
（共 34 条，此处仅展示前 30 条）
-/
theorem factorization_choose_prime_pow_add_factorization (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : (choose (p ^ n) k).factorization p + k.factorization p = n := by
  apply le_antisymm
  · have hdisj : Disjoint {i ∈ Ico 1 n.succ | p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i}
        {i ∈ Ico 1 n.succ | p ^ i ∣ k} := by
      simp +contextual [Finset.disjoint_right, dvd_iff_mod_eq_zero, Nat.mod_lt _ (pow_pos hp.pos _)]
    rw [factorization_choose hp hkn (lt_succ_self _), factorization_eq_card_pow_dvd_of_lt hp
      hk0.bot_lt (lt_of_le_of_lt hkn <| Nat.pow_lt_pow_succ hp.one_lt), log_pow hp.one_lt,
      ← card_union_of_disjoint hdisj, filter_union_right]
    have filter_le_Ico := (Ico 1 n.succ).card_filter_le
      fun x => p ^ x ≤ k % p ^ x + (p ^ n - k) % p ^ x ∨ p ^ x ∣ k
    rwa [card_Ico 1 n.succ] at filter_le_Ico
  · nth_rewrite 1 [← factorization_pow_self (n := n) hp]
    exact factorization_le_factorization_choose_add hkn hk0
/-
**Nat.factorization_choose_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose_prime_pow {p n k : Nat} (hp : p.Prime) (hkn : k <= p 
^ n) (hk0 : k != 0) : (choose (p ^ n) k).factorization p = n - k.factorization p
参数：hp : p.Prime；hkn : k <= p ^ n；hk0 : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.factorization_choose_prime_pow_add_factorization`：factorization_choo
se_prime_pow_add_factorization (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0) 
: (choose (p ^ n) k).factorization p + k.f…
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
-/
theorem factorization_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    (choose (p ^ n) k).factorization p = n - k.factorization p := by
  nth_rewrite 2 [← factorization_choose_prime_pow_add_factorization hp hkn hk0]
  rw [Nat.add_sub_cancel_right]

end Nat


namespace Nat

variable {p n k : ℕ}

/-- A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient. -/
/-
**Nat.factorization_choose_le_log** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose_le_log : (choose n k).factorization p <= log p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorization_choose`：factorization_choose {p n k b : Nat} (hp : p.P
rime) (hkn : k <= n) (hnb : log p n < b) : (choose n k).factorization p = #{i in
 Ico 1 b | p ^…
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a

--- 原说明 ---
A logarithmic upper bound on the multiplicity of a prime in a binomial coefficie
nt.
-/
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n := by
  by_cases h : (choose n k).factorization p = 0
  · simp [h]
  have hp : p.Prime := Not.imp_symm (choose n k).factorization_eq_zero_of_not_prime h
  have hkn : k ≤ n := by
    refine le_of_not_gt fun hnk => h ?_
    simp [choose_eq_zero_of_lt hnk]
  rw [factorization_choose hp hkn (Nat.lt_add_one _)]
  exact (card_filter_le ..).trans_eq (Nat.card_Ico _ _)

/-- A `pow` form of `Nat.factorization_choose_le` -/
/-
**Nat.pow_factorization_choose_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization 
p <= n
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_le_of_le_log`：pow_le_of_le_log {b x y : Nat} (hy : y != 0) (h : 
x <= log b y) : b ^ x <= y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorization_choose_le_log`：factorization_choose_le_log : (choose n
 k).factorization p <= log p n

--- 原说明 ---
A `pow` form of `Nat.factorization_choose_le`
-/
theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n :=
  pow_le_of_le_log hn.ne' factorization_choose_le_log

/-- Primes greater than about `sqrt n` appear only to multiplicity 0 or 1
in the binomial coefficient. -/
/-
**Nat.factorization_choose_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factoriza
tion p <= 1
参数：p_large : n < p ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.factorization_choose_le_log`：factorization_choose_le_log : (choose n
 k).factorization p <= log p n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.log_zero_right`：log_zero_right (b : Nat) : log b 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.log_lt_of_lt_pow`：log_lt_of_lt_pow {b x y : Nat} (hy : y != 0) : y <
 b ^ x -> log b y < x

--- 原说明 ---
Primes greater than about `sqrt n` appear only to multiplicity 0 or 1
in the binomial coefficient.
-/
theorem factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p ≤ 1 := by
  apply factorization_choose_le_log.trans
  rcases eq_or_ne n 0 with (rfl | hn0); · simp
  exact Nat.lt_succ_iff.1 (log_lt_of_lt_pow hn0 p_large)
/-
**Nat.factorization_choose_of_lt_three_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose_of_lt_three_mul (hp' : p != 2) (hk : p <= k) (hk' : p
 <= n - k) (hn : n < 3 * p) : (choose n k).factorization p = 0
参数：hp' : p != 2；hk : p <= k；hk' : p <= n - k；hn : n < 3 * p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorization_choose`：factorization_choose {p n k b : Nat} (hp : p.P
rime) (hkn : k <= n) (hnb : log p n < b) : (choose n k).factorization p = #{i in
 Ico 1 b | p ^…
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [Ad
dLeftStrictMono α] [AddLeftReflectLT α] (a : α) {b c : α},   a + b < a + c ↔ b <
 c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
（共 51 条，此处仅展示前 30 条）
-/
theorem factorization_choose_of_lt_three_mul (hp' : p ≠ 2) (hk : p ≤ k) (hk' : p ≤ n - k)
    (hn : n < 3 * p) : (choose n k).factorization p = 0 := by
  rcases em' p.Prime with hp | hp
  · exact factorization_eq_zero_of_not_prime (choose n k) hp
  rcases lt_or_ge n k with hnk | hkn
  · simp [choose_eq_zero_of_lt hnk]
  simp only [factorization_choose hp hkn (Nat.lt_add_one _), card_eq_zero, filter_eq_empty_iff,
    mem_Ico, not_le, and_imp]
  intro i hi₁ hi
  rcases eq_or_lt_of_le hi₁ with (rfl | hi)
  · rw [pow_one, ← add_lt_add_iff_left (2 * p), ← succ_mul, two_mul, add_add_add_comm]
    exact
      lt_of_le_of_lt
        (add_le_add
          (add_le_add_left (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk)) (k % p))
          (add_le_add_left (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk'))
            ((n - k) % p)))
        (by rwa [div_add_mod, div_add_mod, add_tsub_cancel_of_le hkn])
  · replace hn : n < p ^ i := by
      have : 3 ≤ p := lt_of_le_of_ne hp.two_le hp'.symm
      calc
        n < 3 * p := hn
        _ ≤ p * p := by gcongr
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ i := pow_right_mono₀ hp.one_lt.le hi
    rwa [mod_eq_of_lt (lt_of_le_of_lt hkn hn), mod_eq_of_lt (lt_of_le_of_lt tsub_le_self hn),
      add_tsub_cancel_of_le hkn]

/-- Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`centralBinom n`. -/
/-
**Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul** 是 Mathlib 中的一个定理
，位于命名空间 `Nat`。
形式化陈述：factorization_centralBinom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p
_le_n : p <= n) (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0
参数：n_big : 2 < n；p_le_n : p <= n；big : 2 * n < 3 * p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_choose_of_lt_three_mul`：factorization_choose_of_lt_thr
ee_mul (hp' : p != 2) (hk : p <= k) (hk' : p <= n - k) (hn : n < 3 * p) : (choos
e n k).factorization p = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Primes greater than about `2 * n / 3` and less than `n` do not appear in the fac
torization of
`centralBinom n`.
-/
theorem factorization_centralBinom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p_le_n : p ≤ n)
    (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0 := by
  refine factorization_choose_of_lt_three_mul ?_ p_le_n (p_le_n.trans ?_) big
  · lia
  · rw [two_mul, add_tsub_cancel_left]
/-
**Nat.factorization_factorial_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factoriz
ation p = 0
参数：h : n < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Nat.lt_of_succ_lt`：∀ {n m : ℕ}, n.succ < m → n < m
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.factorization_eq_zero_of_lt`：factorization_eq_zero_of_lt {n p : Nat}
 (h : n < p) : n.factorization p = 0
-/
theorem factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factorization p = 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [factorial_succ, factorization_mul n.succ_ne_zero n.factorial_ne_zero, Finsupp.coe_add,
      Pi.add_apply, hn (lt_of_succ_lt h), add_zero, factorization_eq_zero_of_lt h]
/-
**Nat.factorization_choose_eq_zero_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factorization_choose_eq_zero_of_lt (h : n < p) : (choose n k).factorizatio
n p = 0
参数：h : n < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用定理 `Nat.factorization_div`：factorization_div {d n : Nat} (h : d ∣ n) : (n / 
d).factorization = n.factorization - d.factorization
· 使用定理 `Nat.factorial_mul_factorial_dvd_factorial`：factorial_mul_factorial_dvd_f
actorial {n k : Nat} (hk : k <= n) : k ! * (n - k)! ∣ n !
· 使用定理 `Finsupp.coe_tsub`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommMonoid 
α] [inst_1 : PartialOrder α] [inst_2 : CanonicallyOrderedAdd α]   [inst_3 : Sub 
α] [in…
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `Nat.factorization_factorial_eq_zero_of_lt`：factorization_factorial_eq_ze
ro_of_lt (h : n < p) : (factorial n).factorization p = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
-/
theorem factorization_choose_eq_zero_of_lt (h : n < p) : (choose n k).factorization p = 0 := by
  by_cases! hnk : n < k; · simp [choose_eq_zero_of_lt hnk]
  rw [choose_eq_factorial_div_factorial hnk,
    factorization_div (factorial_mul_factorial_dvd_factorial hnk), Finsupp.coe_tsub,
    Pi.sub_apply, factorization_factorial_eq_zero_of_lt h, zero_tsub]

/-- If a prime `p` has positive multiplicity in the `n`th central binomial coefficient,
`p` is no more than `2 * n` -/
/-
**Nat.factorization_centralBinom_eq_zero_of_two_mul_lt** 是 Mathlib 中的一个定理，位于命名空间
 `Nat`。
形式化陈述：factorization_centralBinom_eq_zero_of_two_mul_lt (h : 2 * n < p) : (centra
lBinom n).factorization p = 0
参数：h : 2 * n < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.factorization_choose_eq_zero_of_lt`：factorization_choose_eq_zero_of_
lt (h : n < p) : (choose n k).factorization p = 0

--- 原说明 ---
If a prime `p` has positive multiplicity in the `n`th central binomial coefficie
nt,
`p` is no more than `2 * n`
-/
theorem factorization_centralBinom_eq_zero_of_two_mul_lt (h : 2 * n < p) :
    (centralBinom n).factorization p = 0 :=
  factorization_choose_eq_zero_of_lt h

/-- Contrapositive form of `Nat.factorization_centralBinom_eq_zero_of_two_mul_lt` -/
/-
**Nat.le_two_mul_of_factorization_centralBinom_pos** 是 Mathlib 中的一个定理，位于命名空间 `Na
t`。
形式化陈述：le_two_mul_of_factorization_centralBinom_pos (h_pos : 0 < (centralBinom n)
.factorization p) : p <= 2 * n
参数：h_pos : 0 < (centralBinom n).factorization p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.factorization_centralBinom_eq_zero_of_two_mul_lt`：factorization_cent
ralBinom_eq_zero_of_two_mul_lt (h : 2 * n < p) : (centralBinom n).factorization 
p = 0

--- 原说明 ---
Contrapositive form of `Nat.factorization_centralBinom_eq_zero_of_two_mul_lt`
-/
theorem le_two_mul_of_factorization_centralBinom_pos
    (h_pos : 0 < (centralBinom n).factorization p) : p ≤ 2 * n :=
  le_of_not_gt (pos_iff_ne_zero.mp h_pos ∘ factorization_centralBinom_eq_zero_of_two_mul_lt)

/-- A binomial coefficient is the product of its prime factors, which are at most `n`. -/
/-
**Nat.prod_pow_factorization_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_factorization_choose (n k : Nat) (hkn : k <= n) : (∏ p in Finset.
range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k
参数：n k : Nat；hkn : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用引理 `Nat.choose_ne_zero`：choose_ne_zero {n k : Nat} (h : k <= n) : n.choose k
 != 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Nat.factorization_choose_eq_zero_of_lt`：factorization_choose_eq_zero_of_
lt (h : n < p) : (choose n k).factorization p = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A binomial coefficient is the product of its prime factors, which are at most `n
`.
-/
theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ Finset.range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k := by
  conv_rhs => rw [← prod_factorization_pow_eq_self (choose_ne_zero hkn)]
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff, Classical.not_not, factorization_choose_eq_zero_of_lt hp]
  · intro p _ h2
    simp [Classical.not_not.1 (mt Finsupp.mem_support_iff.2 h2)]

/-- The `n`th central binomial coefficient is the product of its prime factors, which are
at most `2n`. -/
/-
**Nat.prod_pow_factorization_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_pow_factorization_centralBinom (n : Nat) : (∏ p in Finset.range (2 * 
n + 1), p ^ (centralBinom n).factorization p) = centralBinom n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prod_pow_factorization_choose`：prod_pow_factorization_choose (n k : 
Nat) (hkn : k <= n) : (∏ p in Finset.range (n + 1), p ^ (Nat.choose n k).factori
zation p) = choose n k

--- 原说明 ---
The `n`th central binomial coefficient is the product of its prime factors, whic
h are
at most `2n`.
-/
theorem prod_pow_factorization_centralBinom (n : ℕ) :
    (∏ p ∈ Finset.range (2 * n + 1), p ^ (centralBinom n).factorization p) = centralBinom n := by
  apply prod_pow_factorization_choose
  lia

end Nat

