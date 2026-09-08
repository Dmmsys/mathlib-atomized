/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-!
# Basic results in number theory

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/

public section


section

open Ideal Ideal.Quotient

/-
**dvd_sub_pow_of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : Nat} {a b : R} (h : (
p : R) ∣ a - b) (k : Nat) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k
参数：h : (p : R) ∣ a - b；k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `geom_sum₂_mul`：geom_sum₂_mul (x y : R) (n : Nat) : (∑ i in range n, x ^ 
i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `RingHom.map_geom_sum₂`：RingHom.map_geom_sum₂ (x y : R) (n : Nat) (f : R 
->+* S) : f (∑ i in range n, x ^ i * y ^ (n - 1 - i)) = ∑ i in range n, f x ^ i 
* f y ^ (n …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `geom_sum₂_self`：geom_sum₂_self (x : R) (n : Nat) : ∑ i in range n, x ^ i
 * x ^ (n - 1 - i) = n * x ^ (n - 1)
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} (h : (p : R) ∣ a - b)
    (k : ℕ) : (p ^ (k + 1) : R) ∣ a ^ p ^ k - b ^ p ^ k := by
  induction k with
  | zero => rwa [pow_one, pow_zero, pow_one, pow_one]
  | succ k ih =>
    rw [pow_succ p k, pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ']
    refine mul_dvd_mul ?_ ih
    let f : R →+* R ⧸ span {(p : R)} := mk (span {(p : R)})
    have hf : ∀ r : R, (p : R) ∣ r ↔ f r = 0 := fun r ↦ by rw [eq_zero_iff_mem, mem_span_singleton]
    rw [hf, map_sub, sub_eq_zero] at h
    rw [hf, RingHom.map_geom_sum₂, map_pow, map_pow, h, geom_sum₂_self, mul_eq_zero_of_left]
    rw [← map_natCast f, eq_zero_iff_mem, mem_span_singleton]

end

