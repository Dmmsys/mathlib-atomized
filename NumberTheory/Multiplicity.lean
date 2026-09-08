/-
Copyright (c) 2022 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen, Mantas Bakšys
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-!
# Multiplicity in Number Theory

This file contains results in number theory relating to multiplicity.

## Main statements

* `multiplicity.Int.pow_sub_pow` is the lifting the exponent lemma for odd primes.
  We also prove several variations of the lemma.

## References

* [Wikipedia, *Lifting-the-exponent lemma*](https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma)
-/

public section


open Ideal Ideal.Quotient Finset

variable {R : Type*} {n : ℕ}

section CommRing

variable [CommRing R] {a b x y : R}

/-
**dvd_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dvd_geom_sum₂_iff_of_dvd_sub {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * y ^ (n - 1) := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq] at h
  simp only [← mem_span_singleton, ← eq_zero_iff_mem, RingHom.map_geom_sum₂, h, geom_sum₂_self,
    map_mul, map_pow, map_natCast]
/-
**dvd_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dvd_geom_sum₂_iff_of_dvd_sub' {x y p : R} (h : p ∣ x - y) :
    (p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) ↔ p ∣ n * x ^ (n - 1) := by
  rw [geom_sum₂_comm, dvd_geom_sum₂_iff_of_dvd_sub]; simpa using h.neg_right
/-
**dvd_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dvd_geom_sum₂_self {x y : R} (h : ↑n ∣ x - y) :
    ↑n ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  (dvd_geom_sum₂_iff_of_dvd_sub h).mpr (dvd_mul_right _ _)
/-
**sq_dvd_add_pow_sub_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sq_dvd_add_pow_sub_sub (p x : R) (n : Nat) : p ^ 2 ∣ (x + p) ^ n - x ^ (n 
- 1) * p * n - x ^ n
参数：p x : R；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.choose_succ_self_right`：∀ (n : ℕ), (n + 1).choose n = n + 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 78 条，此处仅展示前 30 条）
-/
theorem sq_dvd_add_pow_sub_sub (p x : R) (n : ℕ) :
    p ^ 2 ∣ (x + p) ^ n - x ^ (n - 1) * p * n - x ^ n := by
  rcases n with - | n
  · simp only [pow_zero, Nat.cast_zero, sub_zero, sub_self, dvd_zero, mul_zero]
  · simp only [add_pow, sum_range_succ, add_tsub_cancel_left, pow_one, Nat.choose_succ_self_right,
      Nat.cast_succ, tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_zero, zero_add,
      Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    suffices p ^ 2 ∣ ∑ i ∈ range n, x ^ i * p ^ (n + 1 - i) * ↑((n + 1).choose i) by
      convert! this; abel
    apply Finset.dvd_sum
    intro y hy
    calc
      p ^ 2 ∣ p ^ (n + 1 - y) :=
        pow_dvd_pow p (le_tsub_of_add_le_left (by linarith [Finset.mem_range.mp hy]))
      _ ∣ x ^ y * p ^ (n + 1 - y) * ↑((n + 1).choose y) :=
        dvd_mul_of_dvd_left (dvd_mul_left _ _) _
/-
**not_dvd_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_dvd_geom_sum₂ {p : R} (hp : Prime p) (hxy : p ∣ x - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) :
    ¬p ∣ ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := fun h =>
  hx <|
    hp.dvd_of_dvd_pow <| (hp.dvd_or_dvd <| (dvd_geom_sum₂_iff_of_dvd_sub' hxy).mp h).resolve_left hn

variable {p : ℕ} (a b)
/-
**odd_sq_dvd_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem odd_sq_dvd_geom_sum₂_sub (hp : Odd p) :
    (p : R) ^ 2 ∣ (∑ i ∈ range p, (a + p * b) ^ i * a ^ (p - 1 - i)) - p * a ^ (p - 1) := by
  have h1 : ∀ (i : ℕ),
      (p : R) ^ 2 ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * i + a ^ i) := by
    intro i
    calc
      ↑p ^ 2 ∣ (↑p * b) ^ 2 := by simp only [mul_pow, dvd_mul_right]
      _ ∣ (a + ↑p * b) ^ i - (a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) := by
        simp only [sq_dvd_add_pow_sub_sub (↑p * b) a i, ← sub_sub]
  simp_rw [← mem_span_singleton, ← Ideal.Quotient.eq] at *
  let s : R := (p : R) ^ 2
  calc
    (Ideal.Quotient.mk (span {s})) (∑ i ∈ range p, (a + (p : R) * b) ^ i * a ^ (p - 1 - i)) =
        ∑ i ∈ Finset.range p,
        mk (span {s}) ((a ^ (i - 1) * (↑p * b) * ↑i + a ^ i) * a ^ (p - 1 - i)) := by
      simp_rw [s, RingHom.map_geom_sum₂, ← map_pow, h1, ← map_mul]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ x ∈ Finset.range p, a ^ (x + (p - 1 - x))) := by
      ring_nf
      simp_rw [← map_sum, sum_add_distrib, map_add]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (∑ _x ∈ Finset.range p, a ^ (p - 1)) := by
      rw [add_right_inj]
      have : ∀ (x : ℕ), (hx : x ∈ range p) → a ^ (x + (p - 1 - x)) = a ^ (p - 1) := by
        intro x hx
        rw [← Nat.add_sub_assoc _ x, Nat.add_sub_cancel_left]
        exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hx)
      rw [Finset.sum_congr rfl this]
    _ =
        mk (span {s})
            (∑ x ∈ Finset.range p, a ^ (x - 1) * (a ^ (p - 1 - x) * (↑p * (b * ↑x)))) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ =
        mk (span {s}) (↑p * b * ∑ x ∈ Finset.range p, a ^ (p - 2) * x) +
          mk (span {s}) (↑p * a ^ (p - 1)) := by
      simp only [Finset.mul_sum, ← mul_assoc, ← pow_add]
      rw [Finset.sum_congr rfl]
      rintro (⟨⟩ | ⟨x⟩) hx
      · rw [Nat.cast_zero, mul_zero, mul_zero]
      · have : x.succ - 1 + (p - 1 - x.succ) = p - 2 := by
          rw [← Nat.add_sub_assoc (Nat.le_sub_one_of_lt (Finset.mem_range.mp hx))]
          exact congr_arg Nat.pred (Nat.add_sub_cancel_left _ _)
        rw [this]
        ring1
    _ = mk (span {s}) (↑p * a ^ (p - 1)) := by
      have : Finset.sum (range p) (fun (x : ℕ) ↦ (x : R)) =
          ((Finset.sum (range p) (fun (x : ℕ) ↦ (x : ℕ)))) := by simp only [Nat.cast_sum]
      simp only [add_eq_right, ← Finset.mul_sum, this]
      norm_cast
      simp only [Finset.sum_range_id]
      norm_cast
      simp only [Nat.cast_mul, map_mul,
          Nat.mul_div_assoc p (even_iff_two_dvd.mp (Nat.Odd.sub_odd hp odd_one))]
      ring_nf
      rw [mul_assoc, mul_assoc]
      refine mul_eq_zero_of_left ?_ _
      refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
      simp [s]

section IntegralDomain

variable [IsDomain R]

/-
**emultiplicity_pow_sub_pow_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow_sub_pow_of_prime {p : R} (hp : Prime p) {x y : R} (hxy :
 p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : ¬p ∣ n) : emultiplicity p (x ^ n - y ^
 n) = emultiplicity p (x - y)
参数：hp : Prime p；hxy : p ∣ x - y；hx : ¬p ∣ x；hn : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `emultiplicity_eq_zero`：emultiplicity_eq_zero : emultiplicity a b = 0 ↔ ¬
a ∣ b
· 使用定理 `not_dvd_geom_sum₂`：not_dvd_geom_sum₂ {p : R} (hp : Prime p) (hxy : p ∣ x
 - y) (hx : ¬p ∣ x) (hn : ¬p ∣ n) : ¬p ∣ ∑ i in range n, x ^ i * y ^ (n - 1 - i)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem emultiplicity_pow_sub_pow_of_prime {p : R} (hp : Prime p) {x y : R}
    (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : ¬p ∣ n) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) := by
  rw [← geom_sum₂_mul, emultiplicity_mul hp,
    emultiplicity_eq_zero.2 (not_dvd_geom_sum₂ hp hxy hx hn), zero_add]

variable (hp : Prime (p : R)) (hp1 : Odd p) (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x)
include hp hp1 hxy hx
/-
**emultiplicity_geom_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem emultiplicity_geom_sum₂_eq_one :
    emultiplicity (↑p) (∑ i ∈ range p, x ^ i * y ^ (p - 1 - i)) = 1 := by
  rw [← Nat.cast_one]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one]
    exact dvd_geom_sum₂_self hxy
  rw [dvd_iff_dvd_of_dvd_sub hxy] at hx
  obtain ⟨k, hk⟩ := hxy
  rw [one_add_one_eq_two, eq_add_of_sub_eq' hk]
  refine mt (dvd_iff_dvd_of_dvd_sub (@odd_sq_dvd_geom_sum₂_sub _ _ y k _ hp1)).mp ?_
  rw [pow_two, mul_dvd_mul_iff_left hp.ne_zero]
  exact mt hp.dvd_of_dvd_pow hx
/-
**emultiplicity_pow_prime_sub_pow_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow_prime_sub_pow_prime : emultiplicity (↑p) (x ^ p - y ^ p)
 = emultiplicity (↑p) (x - y) + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `emultiplicity_geom_sum₂_eq_one`：emultiplicity_geom_sum₂_eq_one : emultip
licity (↑p) (∑ i in range p, x ^ i * y ^ (p - 1 - i)) = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem emultiplicity_pow_prime_sub_pow_prime :
    emultiplicity (↑p) (x ^ p - y ^ p) = emultiplicity (↑p) (x - y) + 1 := by
  rw [← geom_sum₂_mul, emultiplicity_mul hp, emultiplicity_geom_sum₂_eq_one hp hp1 hxy hx, add_comm]
/-
**emultiplicity_pow_prime_pow_sub_pow_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：emultiplicity_pow_prime_pow_sub_pow_prime_pow (a : Nat) : emultiplicity (↑
p) (x ^ p ^ a - y ^ p ^ a) = emultiplicity (↑p) (x - y) + a
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `emultiplicity_pow_prime_sub_pow_prime`：emultiplicity_pow_prime_sub_pow_p
rime : emultiplicity (↑p) (x ^ p - y ^ p) = emultiplicity (↑p) (x - y) + 1
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
-/
theorem emultiplicity_pow_prime_pow_sub_pow_prime_pow (a : ℕ) :
    emultiplicity (↑p) (x ^ p ^ a - y ^ p ^ a) = emultiplicity (↑p) (x - y) + a := by
  induction a with
  | zero => rw [Nat.cast_zero, add_zero, pow_zero, pow_one, pow_one]
  | succ a h_ind =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← h_ind, pow_succ, pow_mul, pow_mul]
    apply emultiplicity_pow_prime_sub_pow_prime hp hp1
    · rw [← geom_sum₂_mul]
      exact dvd_mul_of_dvd_right hxy _
    · exact fun h => hx (hp.dvd_of_dvd_pow h)

end IntegralDomain

section LiftingTheExponent

variable (hp : Nat.Prime p) (hp1 : Odd p)
include hp hp1

/-- **Lifting the exponent lemma** for odd primes. -/
/-
**Int.emultiplicity_pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.emultiplicity_pow_sub_pow {x y : Int} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x
) (n : Nat) : emultiplicity (↑p) (x ^ n - y ^ n) = emultiplicity (↑p) (x - y) + 
emultiplicity p n
参数：hxy : ↑p ∣ x - y；hx : ¬↑p ∣ x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `emultiplicity_pow_sub_pow_of_prime`：emultiplicity_pow_sub_pow_of_prime {
p : R} (hp : Prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : 
¬p ∣ n) : emultiplicity …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `Int.dvd_mul_of_dvd_right`：∀ {a b c : ℤ}, a ∣ c → a ∣ b * c
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `emultiplicity_pow_prime_pow_sub_pow_prime_pow`：emultiplicity_pow_prime_p
ow_sub_pow_prime_pow (a : Nat) : emultiplicity (↑p) (x ^ p ^ a - y ^ p ^ a) = em
ultiplicity (↑p) (x - y) + a

--- 原说明 ---
**Lifting the exponent lemma** for odd primes.
-/
theorem Int.emultiplicity_pow_sub_pow {x y : ℤ} (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : ℕ) :
    emultiplicity (↑p) (x ^ n - y ^ n) = emultiplicity (↑p) (x - y) + emultiplicity p n := by
  rcases n with - | n
  · simp only [emultiplicity_zero, add_top, pow_zero, sub_self]
  have h : FiniteMultiplicity _ _ := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  conv_lhs => rw [hk, pow_mul, pow_mul]
  rw [Nat.prime_iff_prime_int] at hp
  rw [emultiplicity_pow_sub_pow_of_prime hp,
    emultiplicity_pow_prime_pow_sub_pow_prime_pow hp hp1 hxy hx, h.emultiplicity_eq_multiplicity]
  · rw [← geom_sum₂_mul]
    exact dvd_mul_of_dvd_right hxy
  · exact fun h => hx (hp.dvd_of_dvd_pow h)
  · rw [Int.natCast_dvd_natCast]
    rintro ⟨c, rfl⟩
    refine hpn ⟨c, ?_⟩
    rwa [pow_succ, mul_assoc]
/-
**Int.emultiplicity_pow_add_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.emultiplicity_pow_add_pow {x y : Int} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x
) {n : Nat} (hn : Odd n) : emultiplicity (↑p) (x ^ n + y ^ n) = emultiplicity (↑
p) (x + y) + emultiplicity p n
参数：hxy : ↑p ∣ x + y；hx : ¬↑p ∣ x；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `Odd.neg_pow`：Odd.neg_pow : Odd n -> forall a : α, (-a) ^ n = -a ^ n
· 使用定理 `Int.emultiplicity_pow_sub_pow`：Int.emultiplicity_pow_sub_pow {x y : Int}
 (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : Nat) : emultiplicity (↑p) (x ^ n - y ^ n
) = emultiplicity (…
-/
theorem Int.emultiplicity_pow_add_pow {x y : ℤ} (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x)
    {n : ℕ} (hn : Odd n) :
    emultiplicity (↑p) (x ^ n + y ^ n) = emultiplicity (↑p) (x + y) + emultiplicity p n := by
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, ← Odd.neg_pow hn]
  exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
/-
**Nat.emultiplicity_pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.emultiplicity_pow_sub_pow {x y : Nat} (hxy : p ∣ x - y) (hx : ¬p ∣ x) 
(n : Nat) : emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) + emultipl
icity p n
参数：hxy : p ∣ x - y；hx : ¬p ∣ x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_emultiplicity`：Int.natCast_emultiplicity (a b : Nat) : emult
iplicity (a : Int) (b : Int) = emultiplicity a b
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `Nat.pow_le_pow_left`：∀ {n m : ℕ}, n ≤ m → ∀ (i : ℕ), n ^ i ≤ m ^ i
· 使用定理 `Int.natCast_sub`：∀ {n m : ℕ}, n ≤ m → ↑(m - n) = ↑m - ↑n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.emultiplicity_pow_sub_pow`：Int.emultiplicity_pow_sub_pow {x y : Int}
 (hxy : ↑p ∣ x - y) (hx : ¬↑p ∣ x) (n : Nat) : emultiplicity (↑p) (x ^ n - y ^ n
) = emultiplicity (…
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Nat.emultiplicity_pow_sub_pow {x y : ℕ} (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : ℕ) :
    emultiplicity p (x ^ n - y ^ n) = emultiplicity p (x - y) + emultiplicity p n := by
  obtain hyx | hyx := le_total y x
  · iterate 2 rw [← Int.natCast_emultiplicity]
    rw [Int.ofNat_sub (Nat.pow_le_pow_left hyx n)]
    rw [← Int.natCast_dvd_natCast] at hxy hx
    rw [Int.natCast_sub hyx] at *
    push_cast at *
    exact Int.emultiplicity_pow_sub_pow hp hp1 hxy hx n
  · simp only [Nat.sub_eq_zero_iff_le.mpr (Nat.pow_le_pow_left hyx n), emultiplicity_zero,
    Nat.sub_eq_zero_iff_le.mpr hyx, top_add]
/-
**Nat.emultiplicity_pow_add_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.emultiplicity_pow_add_pow {x y : Nat} (hxy : p ∣ x + y) (hx : ¬p ∣ x) 
{n : Nat} (hn : Odd n) : emultiplicity p (x ^ n + y ^ n) = emultiplicity p (x + 
y) + emultiplicity p n
参数：hxy : p ∣ x + y；hx : ¬p ∣ x；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_emultiplicity`：Int.natCast_emultiplicity (a b : Nat) : emult
iplicity (a : Int) (b : Int) = emultiplicity a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.emultiplicity_pow_add_pow`：Int.emultiplicity_pow_add_pow {x y : Int}
 (hxy : ↑p ∣ x + y) (hx : ¬↑p ∣ x) {n : Nat} (hn : Odd n) : emultiplicity (↑p) (
x ^ n + y ^ n) = em…
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
theorem Nat.emultiplicity_pow_add_pow {x y : ℕ} (hxy : p ∣ x + y) (hx : ¬p ∣ x)
    {n : ℕ} (hn : Odd n) :
    emultiplicity p (x ^ n + y ^ n) = emultiplicity p (x + y) + emultiplicity p n := by
  iterate 2 rw [← Int.natCast_emultiplicity]
  rw [← Int.natCast_dvd_natCast] at hxy hx
  push_cast at *
  exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

end LiftingTheExponent

end CommRing

/-
**pow_two_pow_sub_pow_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_two_pow_sub_pow_two_pow [CommRing R] {x y : R} (n : Nat) : x ^ 2 ^ n -
 y ^ 2 ^ n = (∏ i in Finset.range n, (x ^ 2 ^ i + y ^ 2 ^ i)) * (x - y)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_prod_atom`：∀ {R : Type u_1} [inst : CommS
emiring R] (a : R) (b : ℕ) {e : R}, (a + 0) ^ b * Nat.rawCast 1 = e → a ^ b = e
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 57 条，此处仅展示前 30 条）
-/
theorem pow_two_pow_sub_pow_two_pow [CommRing R] {x y : R} (n : ℕ) :
    x ^ 2 ^ n - y ^ 2 ^ n = (∏ i ∈ Finset.range n, (x ^ 2 ^ i + y ^ 2 ^ i)) * (x - y) := by
  induction n with
  | zero => simp only [pow_zero, pow_one, range_zero, prod_empty, one_mul]
  | succ d hd =>
    suffices x ^ 2 ^ d.succ - y ^ 2 ^ d.succ = (x ^ 2 ^ d + y ^ 2 ^ d) * (x ^ 2 ^ d - y ^ 2 ^ d) by
      rw [this, hd, Finset.prod_range_succ, ← mul_assoc, mul_comm (x ^ 2 ^ d + y ^ 2 ^ d)]
    rw [Nat.succ_eq_add_one]
    ring
/-
**Int.sq_mod_four_eq_one_of_odd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.sq_mod_four_eq_one_of_odd {x : Int} : Odd x -> x ^ 2 % 4 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_bit0`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a b c : R} {k : ℕ}, a ^ k = b → b * b = c → a ^ Nat.mul 2 k = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one`：∀ {R : Type u_1} [inst : CommSemirin
g R] (a : R), a ^ 1 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 46 条，此处仅展示前 30 条）
-/
theorem Int.sq_mod_four_eq_one_of_odd {x : ℤ} : Odd x → x ^ 2 % 4 = 1 := by
  intro hx
  unfold Odd at hx
  rcases hx with ⟨_, rfl⟩
  ring_nf
  rw [add_assoc, ← add_mul, Int.add_mul_emod_self_right]
  decide
/-
**Int.eight_dvd_sq_sub_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.eight_dvd_sq_sub_one_of_odd {k : Int} (hk : Odd k) : 8 ∣ k ^ 2 - 1
参数：hk : Odd k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_nat`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} {b c k : ℕ} {d e : R}, b = c * k → a ^ c = d → d ^ k = e → a ^ b = 
e
· 使用定理 `Mathlib.Tactic.Ring.Common.coeff_one`：∀ (k : ℕ) {e : ℕ}, Nat.rawCast 1 =
 e → k.rawCast = e * k
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_bit0`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a b c : R} {k : ℕ}, a ^ k = b → b * b = c → a ^ Nat.mul 2 k = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one`：∀ {R : Type u_1} [inst : CommSemirin
g R] (a : R), a ^ 1 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 52 条，此处仅展示前 30 条）
-/
lemma Int.eight_dvd_sq_sub_one_of_odd {k : ℤ} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by ring
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)
/-
**Nat.eight_dvd_sq_sub_one_of_odd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.eight_dvd_sq_sub_one_of_odd {k : Nat} (hk : Odd k) : 8 ∣ k ^ 2 - 1
参数：hk : Odd k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `four_ne_zero`：four_ne_zero [OfNat α 4] [NeZero (4 : α)] : (4 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.two_dvd_mul_add_one`：two_dvd_mul_add_one (k : Nat) : 2 ∣ k * (k + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Nat.eight_dvd_sq_sub_one_of_odd {k : ℕ} (hk : Odd k) : 8 ∣ k ^ 2 - 1 := by
  rcases hk with ⟨m, rfl⟩
  have eq : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by grind
  simpa [eq] using (mul_dvd_mul_iff_left four_ne_zero).mpr (two_dvd_mul_add_one m)
/-
**Int.two_pow_two_pow_add_two_pow_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.two_pow_two_pow_add_two_pow_two_pow {x y : Int} (hx : ¬2 ∣ x) (hxy : 4
 ∣ x - y) (i : Nat) : emultiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : Nat)
参数：hx : ¬2 ∣ x；hxy : 4 ∣ x - y；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用引理 `Odd.sub_even`：Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b)
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Odd.add_odd`：Odd.add_odd : Odd a -> Odd b -> Even (a + b)
· 使用引理 `Odd.pow`：Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Int.sq_mod_four_eq_one_of_odd`：Int.sq_mod_four_eq_one_of_odd {x : Int} :
 Odd x -> x ^ 2 % 4 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Int.add_emod`：∀ (a b n : ℤ), (a + b) % n = (a % n + b % n) % n
-/
theorem Int.two_pow_two_pow_add_two_pow_two_pow {x y : ℤ} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : ℕ) :
    emultiplicity 2 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(1 : ℕ) := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [pow_one, ← even_iff_two_dvd]
    exact hx_odd.pow.add_odd hy_odd.pow
  rcases i with - | i
  · grind
  suffices ∀ x : ℤ, Odd x → x ^ 2 ^ (i + 1) % 4 = 1 by
    rw [show (2 ^ (1 + 1) : ℤ) = 4 by simp, Int.dvd_iff_emod_eq_zero, Int.add_emod,
      this _ hx_odd, this _ hy_odd]
    decide
  intro x hx
  rw [pow_succ', mul_comm, pow_mul, Int.sq_mod_four_eq_one_of_odd hx.pow]
/-
**Int.two_pow_two_pow_sub_pow_two_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.two_pow_two_pow_sub_pow_two_pow {x y : Int} (n : Nat) (hxy : 4 ∣ x - y
) (hx : ¬2 ∣ x) : emultiplicity 2 (x ^ 2 ^ n - y ^ 2 ^ n) = emultiplicity 2 (x -
 y) + n
参数：n : Nat；hxy : 4 ∣ x - y；hx : ¬2 ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two_pow_sub_pow_two_pow`：pow_two_pow_sub_pow_two_pow [CommRing R] {x
 y : R} (n : Nat) : x ^ 2 ^ n - y ^ 2 ^ n = (∏ i in Finset.range n, (x ^ 2 ^ i +
 y ^ 2 ^ i)) * (x…
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Int.prime_two`：prime_two : Prime (2 : Int)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.emultiplicity_prod`：Finset.emultiplicity_prod {β : Type*} {p : α}
 (hp : Prime p) (s : Finset β) (f : β -> α) : emultiplicity p (∏ x in s, f x) = 
∑ x in s, emult…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Int.two_pow_two_pow_add_two_pow_two_pow`：Int.two_pow_two_pow_add_two_pow
_two_pow {x y : Int} (hx : ¬2 ∣ x) (hxy : 4 ∣ x - y) (i : Nat) : emultiplicity 2
 (x ^ 2 ^ i + y ^ 2 ^ i) = ↑(…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Int.two_pow_two_pow_sub_pow_two_pow {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ 2 ^ n - y ^ 2 ^ n) = emultiplicity 2 (x - y) + n := by
  simp only [pow_two_pow_sub_pow_two_pow n, emultiplicity_mul Int.prime_two,
    Finset.emultiplicity_prod Int.prime_two, add_comm, Nat.cast_one, Finset.sum_const,
    Finset.card_range, nsmul_one, Int.two_pow_two_pow_add_two_pow_two_pow hx hxy]
/-
**Int.two_pow_sub_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.two_pow_sub_pow' {x y : Int} (n : Nat) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x)
 : emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 
: Int) n
参数：n : Nat；hxy : 4 ∣ x - y；hx : ¬2 ∣ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用引理 `Odd.sub_even`：Odd.sub_even (ha : Odd a) (hb : Even b) : Odd (a - b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `emultiplicity_pow_sub_pow_of_prime`：emultiplicity_pow_sub_pow_of_prime {
p : R} (hp : Prime p) {x y : R} (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : 
¬p ∣ n) : emultiplicity …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Int.prime_two`：prime_two : Prime (2 : Int)
· 使用引理 `Odd.sub_odd`：Odd.sub_odd (ha : Odd a) (hb : Odd b) : Even (a - b)
（共 36 条，此处仅展示前 30 条）
-/
theorem Int.two_pow_sub_pow' {x y : ℤ} (n : ℕ) (hxy : 4 ∣ x - y) (hx : ¬2 ∣ x) :
    emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n := by
  have hx_odd : Odd x := by rwa [← Int.not_even_iff_odd, even_iff_two_dvd]
  have hxy_even : Even (x - y) := even_iff_two_dvd.mpr (dvd_trans (by decide) hxy)
  have hy_odd : Odd y := by simpa using hx_odd.sub_even hxy_even
  rcases n with - | n
  · simp only [pow_zero, sub_self, emultiplicity_zero, Int.ofNat_zero, add_top]
  have h : FiniteMultiplicity 2 n.succ := Nat.finiteMultiplicity_iff.mpr ⟨by simp, n.succ_pos⟩
  simp only [Nat.succ_eq_add_one] at h
  rcases emultiplicity_eq_coe.mp h.emultiplicity_eq_multiplicity with ⟨⟨k, hk⟩, hpn⟩
  rw [hk, pow_mul, pow_mul, emultiplicity_pow_sub_pow_of_prime,
    Int.two_pow_two_pow_sub_pow_two_pow _ hxy hx, ← hk]
  · norm_cast
    rw [h.emultiplicity_eq_multiplicity]
  · exact Int.prime_two
  · simpa only [even_iff_two_dvd] using hx_odd.pow.sub_odd hy_odd.pow
  · simpa only [even_iff_two_dvd, ← Int.not_even_iff_odd] using hx_odd.pow
  norm_cast
  contrapose hpn
  rw [pow_succ]
  conv_rhs => rw [hk]
  exact mul_dvd_mul_left _ hpn

/-- **Lifting the exponent lemma** for `p = 2` -/
/-
**Int.two_pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.two_pow_sub_pow {x y : Int} {n : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) 
(hn : Even n) : emultiplicity 2 (x ^ n - y ^ n) + 1 = emultiplicity 2 (x + y) + 
emultiplicity 2 (x - y) + emultiplicity (2 : Int) n
参数：hxy : 2 ∣ x - y；hx : ¬2 ∣ x；hn : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `even_neg`：∀ {α : Type u_2} [inst : SubtractionMonoid α] {a : α}, Even (-
a) ↔ Even a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.NumberTheory.Multiplicity.0.Int.two_pow_sub_pow._abel_1
_1`：∀ {x y : ℤ}, y = -(x - y) + x
· 使用引理 `Even.add_odd`：Even.add_odd : Even a -> Odd b -> Odd (a + b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Int.dvd_iff_emod_eq_zero`：∀ {a b : ℤ}, a ∣ b ↔ b % a = 0
· 使用定理 `Int.sub_emod`：∀ (a b n : ℤ), (a - b) % n = (a % n - b % n) % n
· 使用定理 `Int.sq_mod_four_eq_one_of_odd`：Int.sq_mod_four_eq_one_of_odd {x : Int} :
 Odd x -> x ^ 2 % 4 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.two_pow_sub_pow'`：Int.two_pow_sub_pow' {x y : Int} (n : Nat) (hxy : 
4 ∣ x - y) (hx : ¬2 ∣ x) : emultiplicity 2 (x ^ n - y ^ n) = emultiplicity 2 (x 
- y) + emu…
· 使用引理 `Odd.pow`：Odd.pow {n : Nat} (ha : Odd a) : Odd (a ^ n)
· 使用引理 `sq_sub_sq`：sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `Int.ofNat_mul_ofNat`：∀ (m n : ℕ), ↑m * ↑n = ↑(m * n)
· 使用定理 `emultiplicity_mul`：emultiplicity_mul {p a b : α} (hp : Prime p) : emulti
plicity p (a * b) = emultiplicity p a + emultiplicity p b
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `Int.prime_two`：prime_two : Prime (2 : Int)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Lifting the exponent lemma** for `p = 2`
-/
theorem Int.two_pow_sub_pow {x y : ℤ} {n : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity (2 : ℤ) n := by
  have hy : Odd y := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd] at hx
    replace hxy := (@even_neg _ _ (x - y)).mpr (even_iff_two_dvd.mpr hxy)
    convert! Even.add_odd hxy hx
    abel
  obtain ⟨d, rfl⟩ := hn
  simp only [← two_mul, pow_mul]
  have hxy4 : 4 ∣ x ^ 2 - y ^ 2 := by
    rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, Int.sq_mod_four_eq_one_of_odd _,
      Int.sq_mod_four_eq_one_of_odd hy]
    · simp
    · simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]
  rw [Int.two_pow_sub_pow' d hxy4 _, sq_sub_sq, ← Int.ofNat_mul_ofNat,
    emultiplicity_mul Int.prime_two, emultiplicity_mul Int.prime_two]
  · suffices emultiplicity (2 : ℤ) ↑(2 : ℕ) = 1 by rw [this, add_comm 1, ← add_assoc]
    norm_cast
    rw [FiniteMultiplicity.emultiplicity_self]
    rw [Nat.finiteMultiplicity_iff]
    decide
  · rw [← even_iff_two_dvd, Int.not_even_iff_odd]
    apply Odd.pow
    simp only [← Int.not_even_iff_odd, even_iff_two_dvd, hx, not_false_iff]
/-
**Nat.two_pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.two_pow_sub_pow {x y : Nat} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} 
(hn : Even n) : emultiplicity 2 (x ^ n - y ^ n) + 1 = emultiplicity 2 (x + y) + 
emultiplicity 2 (x - y) + emultiplicity 2 n
参数：hxy : 2 ∣ x - y；hx : ¬2 ∣ x；hn : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_emultiplicity`：Int.natCast_emultiplicity (a b : Nat) : emult
iplicity (a : Int) (b : Int) = emultiplicity a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.ofNat_sub`：∀ {m n : ℕ}, m ≤ n → ↑(n - m) = ↑n - ↑m
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Int.two_pow_sub_pow`：Int.two_pow_sub_pow {x y : Int} {n : Nat} (hxy : 2 
∣ x - y) (hx : ¬2 ∣ x) (hn : Even n) : emultiplicity 2 (x ^ n - y ^ n) + 1 = emu
ltiplicit…
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Nat.two_pow_sub_pow {x y : ℕ} (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : Even n) :
    emultiplicity 2 (x ^ n - y ^ n) + 1 =
      emultiplicity 2 (x + y) + emultiplicity 2 (x - y) + emultiplicity 2 n := by
  obtain hyx | hyx := le_total y x
  · iterate 3 rw [← Int.natCast_emultiplicity]
    simp only [Int.ofNat_sub hyx, Int.ofNat_sub (pow_le_pow_left' hyx _), Int.natCast_add,
      Int.natCast_pow]
    rw [← Int.natCast_dvd_natCast] at hx
    rw [← Int.natCast_dvd_natCast, Int.ofNat_sub hyx] at hxy
    convert! Int.two_pow_sub_pow hxy hx hn using 2
    rw [← Int.natCast_emultiplicity]
    rfl
  · simp only [Nat.sub_eq_zero_iff_le.mpr hyx,
      Nat.sub_eq_zero_iff_le.mpr (pow_le_pow_left' hyx n), emultiplicity_zero,
      top_add, add_top]

namespace padicValNat

variable {x y : ℕ}

/-
**padicValNat.pow_two_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : Nat} (h
n : n != 0) (hneven : Even n) : padicValNat 2 (x ^ n - y ^ n) + 1 = padicValNat 
2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n
参数：hyx : y < x；hxy : 2 ∣ x - y；hx : ¬2 ∣ x；hn : n != 0；hneven : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用定理 `Nat.two_pow_sub_pow`：Nat.two_pow_sub_pow {x y : Nat} (hxy : 2 ∣ x - y) (
hx : ¬2 ∣ x) {n : Nat} (hn : Even n) : emultiplicity 2 (x ^ n - y ^ n) + 1 = emu
ltiplicit…
-/
theorem pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x - y) (hx : ¬2 ∣ x) {n : ℕ} (hn : n ≠ 0)
    (hneven : Even n) :
    padicValNat 2 (x ^ n - y ^ n) + 1 =
      padicValNat 2 (x + y) + padicValNat 2 (x - y) + padicValNat 2 n := by
  simp only [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 4 rw [padicValNat_eq_emultiplicity]
  · exact Nat.two_pow_sub_pow hxy hx hneven
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · lia
  · simp [← Nat.pos_iff_ne_zero, tsub_pos_iff_lt, Nat.pow_lt_pow_left hyx hn]
/-
**padicValNat.pow_two_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：pow_two_sub_one {x n : Nat} (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hne
ven : Even n) : padicValNat 2 (x ^ n - 1) + 1 = padicValNat 2 (x + 1) + padicVal
Nat 2 (x - 1) + padicValNat 2 n
参数：h1x : 1 < x；hx : ¬2 ∣ x；hn : n != 0；hneven : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `padicValNat.pow_two_sub_pow`：pow_two_sub_pow (hyx : y < x) (hxy : 2 ∣ x 
- y) (hx : ¬2 ∣ x) {n : Nat} (hn : n != 0) (hneven : Even n) : padicValNat 2 (x 
^ n - y ^ n) + 1 …
-/
theorem pow_two_sub_one {x n : ℕ} (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n ≠ 0) (hneven : Even n) :
    padicValNat 2 (x ^ n - 1) + 1 = padicValNat 2 (x + 1) +
    padicValNat 2 (x - 1) + padicValNat 2 n := by
  simpa using pow_two_sub_pow h1x (by grind) hx hn hneven
/-
**padicValNat.pow_two_sub_one_ge** 是 Mathlib 中的一个引理，位于命名空间 `padicValNat`。
形式化陈述：pow_two_sub_one_ge (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n != 0) (hneven : Eve
n n) : padicValNat 2 n + 2 <= padicValNat 2 (x ^ n - 1)
参数：h1x : 1 < x；hx : ¬2 ∣ x；hn : n != 0；hneven : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `padicValNat_dvd_iff_le`：padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n 
: Nat} (ha : a != 0) : p ^ n ∣ a ↔ n <= padicValNat p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.pow_two_sub_pow_two`：∀ (a b : ℕ), a ^ 2 - b ^ 2 = (a + b) * (a - b)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `padicValNat.pow_two_sub_one`：pow_two_sub_one {x n : Nat} (h1x : 1 < x) (
hx : ¬2 ∣ x) (hn : n != 0) (hneven : Even n) : padicValNat 2 (x ^ n - 1) + 1 = p
adicValNat 2 (x +…
-/
lemma pow_two_sub_one_ge (h1x : 1 < x) (hx : ¬2 ∣ x) (hn : n ≠ 0) (hneven : Even n) :
    padicValNat 2 n + 2 ≤ padicValNat 2 (x ^ n - 1) := by
  have : padicValNat 2 ((x + 1) * (x - 1)) ≥ 3 := by
    refine (padicValNat_dvd_iff_le (by grind [mul_ne_zero])).mp ?_
    simp [← Nat.pow_two_sub_pow_two x 1]
    grind [Nat.eight_dvd_sq_sub_one_of_odd]
  have := pow_two_sub_one h1x hx hn hneven
  grind [← padicValNat.mul]

variable {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p)
include hp hp1
/-
**padicValNat.pow_sub_pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : Nat} (hn : 
n != 0) : padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p 
n
参数：hyx : y < x；hxy : p ∣ x - y；hx : ¬p ∣ x；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `Nat.sub_ne_zero_of_lt`：∀ {a b : ℕ}, a < b → b - a ≠ 0
· 使用定理 `Nat.pow_lt_pow_left`：∀ {a b n : ℕ}, a < b → n ≠ 0 → a ^ n < b ^ n
· 使用定理 `Nat.emultiplicity_pow_sub_pow`：Nat.emultiplicity_pow_sub_pow {x y : Nat}
 (hxy : p ∣ x - y) (hx : ¬p ∣ x) (n : Nat) : emultiplicity p (x ^ n - y ^ n) = e
multiplicity p (x -…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem pow_sub_pow (hyx : y < x) (hxy : p ∣ x - y) (hx : ¬p ∣ x) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p n := by
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_sub_pow hp.out hp1 hxy hx n
  · exact hn
  · exact Nat.sub_ne_zero_of_lt hyx
  · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hyx hn)
/-
**padicValNat.pow_add_pow** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : Nat} (hn : Odd n) : padic
ValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n
参数：hxy : p ∣ x + y；hx : ¬p ∣ x；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `padicValNat_eq_emultiplicity`：padicValNat_eq_emultiplicity [hp : Fact p.
Prime] {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.lt_add_left`：∀ {a b : ℕ} (c : ℕ), a < b → a < c + b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Odd.pos`：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
 [Nontrivial R] {a : R} : Odd a -> 0 < a
· 使用定理 `Nat.emultiplicity_pow_add_pow`：Nat.emultiplicity_pow_add_pow {x y : Nat}
 (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : Nat} (hn : Odd n) : emultiplicity p (x ^ n
 + y ^ n) = emultip…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem pow_add_pow (hxy : p ∣ x + y) (hx : ¬p ∣ x) {n : ℕ} (hn : Odd n) :
    padicValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n := by
  rcases y with - | y
  · contradiction
  rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add]
  iterate 3 rw [padicValNat_eq_emultiplicity]
  · exact Nat.emultiplicity_pow_add_pow hp.out hp1 hxy hx hn
  · exact (Odd.pos hn).ne'
  · simp
  · exact (Nat.lt_add_left _ (pow_pos y.succ_pos _)).ne'

end padicValNat

