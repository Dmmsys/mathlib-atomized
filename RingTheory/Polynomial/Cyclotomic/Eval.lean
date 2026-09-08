/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Tactic.ByContra
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Analysis.Complex.Arg

/-!
# Evaluating cyclotomic polynomials

This file states some results about evaluating cyclotomic polynomials in various different ways.

## Main definitions
* `Polynomial.eval(₂)_one_cyclotomic_prime(_pow)`: `eval 1 (cyclotomic p^k R) = p`.
* `Polynomial.eval_one_cyclotomic_not_prime_pow`: Otherwise, `eval 1 (cyclotomic n R) = 1`.
* `Polynomial.cyclotomic_pos` : `∀ x, 0 < eval x (cyclotomic n R)` if `2 < n`.
-/

public section


namespace Polynomial

open Finset Nat

@[simp]
/-
**Polynomial.eval_one_cyclotomic_prime** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_one_cyclotomic_prime {R : Type*} [CommRing R] {p : Nat} [hn : Fact p.
Prime] : eval 1 (cyclotomic p R) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime`：cyclotomic_prime (R : Type*) [Ring R] (p : 
Nat) [hp : Fact p.Prime] : cyclotomic p R = ∑ i in Finset.range p, X ^ i
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_one_cyclotomic_prime {R : Type*} [CommRing R] {p : ℕ} [hn : Fact p.Prime] :
    eval 1 (cyclotomic p R) = p := by
  simp only [cyclotomic_prime, eval_X, one_pow, Finset.sum_const, eval_pow, eval_finsetSum,
    Finset.card_range, smul_one_eq_cast]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_one_cyclotomic_prime {R S : Type*} [CommRing R] [Semiring S] (f : R →+* S) {p : ℕ}
    [Fact p.Prime] : eval₂ f 1 (cyclotomic p R) = p := by simp

@[simp]
/-
**Polynomial.eval_one_cyclotomic_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：eval_one_cyclotomic_prime_pow {R : Type*} [CommRing R] {p : Nat} (k : Nat)
 [hn : Fact p.Prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_prime_pow_eq_geom_sum`：cyclotomic_prime_pow_eq_geo
m_sum {R : Type*} [CommRing R] {p n : Nat} (hp : p.Prime) : cyclotomic (p ^ (n +
 1)) R = ∑ i in Finset.range p, (…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_one_cyclotomic_prime_pow {R : Type*} [CommRing R] {p : ℕ} (k : ℕ)
    [hn : Fact p.Prime] : eval 1 (cyclotomic (p ^ (k + 1)) R) = p := by
  simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, eval_X, one_pow, Finset.sum_const, eval_pow,
    eval_finsetSum, Finset.card_range, smul_one_eq_cast]
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_one_cyclotomic_prime_pow {R S : Type*} [CommRing R] [Semiring S] (f : R →+* S)
    {p : ℕ} (k : ℕ) [Fact p.Prime] : eval₂ f 1 (cyclotomic (p ^ (k + 1)) R) = p := by simp
/-
**Polynomial.cyclotomic_neg_one_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem cyclotomic_neg_one_pos {n : ℕ} (hn : 2 < n) {R}
    [CommRing R] [PartialOrder R] [IsStrictOrderedRing R] :
    0 < eval (-1 : R) (cyclotomic n R) := by
  have := NeZero.of_gt hn
  rw [← map_cyclotomic_int, ← Int.cast_one, ← Int.cast_neg, eval_intCast_map, Int.coe_castRingHom,
    Int.cast_pos]
  suffices 0 < eval (↑(-1 : ℤ)) (cyclotomic n ℝ) by
    rw [← map_cyclotomic_int n ℝ, eval_intCast_map, Int.coe_castRingHom] at this
    simpa only [Int.cast_pos] using this
  simp only [Int.cast_one, Int.cast_neg]
  have h0 := cyclotomic_coeff_zero ℝ hn.le
  rw [coeff_zero_eq_eval_zero] at h0
  by_contra! hx
  have := intermediate_value_univ (-1) 0 (cyclotomic n ℝ).continuous
  obtain ⟨y, hy : IsRoot _ y⟩ := this (show (0 : ℝ) ∈ Set.Icc _ _ by simpa [h0] using hx)
  rw [@isRoot_cyclotomic_iff] at hy
  rw [hy.eq_orderOf] at hn
  exact hn.not_ge LinearOrderedRing.orderOf_le_two
/-
**Polynomial.cyclotomic_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_pos {n : Nat} (hn : 2 < n) {R} [CommRing R] [LinearOrder R] [Is
StrictOrderedRing R] (x : R) : 0 < eval x (cyclotomic n R)
参数：hn : 2 < n；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
· 使用定理 `Polynomial.prod_cyclotomic_eq_geom_sum`：prod_cyclotomic_eq_geom_sum {n :
 Nat} (h : 0 < n) (R) [CommRing R] : ∏ i in n.divisors.erase 1, cyclotomic i R =
 ∑ i in Finset.range n, X ^ …
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_geom_sum`：eval_geom_sum {R} [CommSemiring R] {n : Nat} {
x : R} : eval x (∑ i in range n, X ^ i) = ∑ i in range n, x ^ i
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Nat.self_notMem_properDivisors`：self_notMem_properDivisors : n ∉ properD
ivisors n
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.erase_cons_of_ne`：erase_cons_of_ne {a b : α} {s : Finset α} (ha :
 a ∉ s) (hb : a != b) : (s.cons a ha).erase b = (s.erase b).cons a fun h => ha e
rase_subset _…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cons_self_properDivisors`：cons_self_properDivisors (h : n != 0) : co
ns n (properDivisors n) self_notMem_properDivisors = divisors n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.eval_prod`：eval_prod {ι : Type*} (s : Finset ι) (p : ι -> R[X
]) (x : R) : eval x (∏ j in s, p j) = ∏ j in s, eval x (p j)
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
（共 69 条，此处仅展示前 30 条）
-/
theorem cyclotomic_pos {n : ℕ} (hn : 2 < n) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) :
    0 < eval x (cyclotomic n R) := by
  induction n using Nat.strong_induction_on with | _ n ih
  have hn' : 0 < n := pos_of_gt hn
  have hn'' : 1 < n := one_lt_two.trans hn
  have := prod_cyclotomic_eq_geom_sum hn' R
  apply_fun eval x at this
  rw [← cons_self_properDivisors hn'.ne', Finset.erase_cons_of_ne _ hn''.ne', Finset.prod_cons,
    eval_mul, eval_geom_sum] at this
  rcases lt_trichotomy 0 (∑ i ∈ Finset.range n, x ^ i) with (h | h | h)
  · apply pos_of_mul_pos_left
    · rwa [this]
    rw [eval_prod]
    refine Finset.prod_nonneg fun i hi => ?_
    simp only [Finset.mem_erase, mem_properDivisors] at hi
    rw [geom_sum_pos_iff hn'.ne'] at h
    rcases h with hk | hx
    · refine (ih _ hi.2.2 (Nat.two_lt_of_ne ?_ hi.1 ?_)).le <;> rintro rfl
      · exact hn'.ne' (zero_dvd_iff.mp hi.2.1)
      · exact not_odd_iff_even.2 (even_iff_two_dvd.mpr hi.2.1) hk
    · rcases eq_or_ne i 2 with (rfl | hk)
      · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using hx.le
      refine (ih _ hi.2.2 (Nat.two_lt_of_ne ?_ hi.1 hk)).le
      rintro rfl
      exact hn'.ne' <| zero_dvd_iff.mp hi.2.1
  · rw [eq_comm, geom_sum_eq_zero_iff_neg_one hn'.ne'] at h
    exact h.1.symm ▸ cyclotomic_neg_one_pos hn
  · apply pos_of_mul_neg_left
    · rwa [this]
    rw [geom_sum_neg_iff hn'.ne'] at h
    have h2 : 2 ∈ n.properDivisors.erase 1 := by
      rw [Finset.mem_erase, mem_properDivisors]
      exact ⟨by decide, even_iff_two_dvd.mp h.1, hn⟩
    rw [eval_prod, ← Finset.prod_erase_mul _ _ h2]
    apply mul_nonpos_of_nonneg_of_nonpos
    · refine Finset.prod_nonneg fun i hi => le_of_lt ?_
      simp only [Finset.mem_erase, mem_properDivisors] at hi
      refine ih _ hi.2.2.2 (Nat.two_lt_of_ne ?_ hi.2.1 hi.1)
      rintro rfl
      rw [zero_dvd_iff] at hi
      exact hn'.ne' hi.2.2.1
    · simpa only [eval_X, eval_one, cyclotomic_two, eval_add] using h.right.le
/-
**Polynomial.cyclotomic_pos_and_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_pos_and_nonneg (n : Nat) {R} [CommRing R] [LinearOrder R] [IsSt
rictOrderedRing R] (x : R) : (1 < x -> 0 < eval x (cyclotomic n R)) ∧ (1 <= x ->
 0 <= eval x (cyclotomic n R))
参数：n : Nat；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.cyclotomic_two`：cyclotomic_two (R : Type*) [Ring R] : cycloto
mic 2 R = X + 1
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
（共 81 条，此处仅展示前 30 条）
-/
theorem cyclotomic_pos_and_nonneg (n : ℕ) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) :
    (1 < x → 0 < eval x (cyclotomic n R)) ∧ (1 ≤ x → 0 ≤ eval x (cyclotomic n R)) := by
  rcases n with (_ | _ | _ | n)
  · simp only [cyclotomic_zero, eval_one, zero_lt_one, implies_true, zero_le_one, and_self]
  · simp
  · simp only [zero_add, reduceAdd, cyclotomic_two, eval_add, eval_X, eval_one]
    constructor <;> intro <;> linarith
  · constructor <;> intro <;> [skip; apply le_of_lt] <;> apply cyclotomic_pos (by lia)

/-- Cyclotomic polynomials are always positive on inputs larger than one.
Similar to `cyclotomic_pos` but with the condition on the input rather than index of the
cyclotomic polynomial. -/
/-
**Polynomial.cyclotomic_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_pos' (n : Nat) {R} [CommRing R] [LinearOrder R] [IsStrictOrdere
dRing R] {x : R} (hx : 1 < x) : 0 < eval x (cyclotomic n R)
参数：n : Nat；hx : 1 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.cyclotomic_pos_and_nonneg`：cyclotomic_pos_and_nonneg (n : Nat
) {R} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : (1 < x -> 0
 < eval x (cyclotomic n R)…

--- 原说明 ---
Cyclotomic polynomials are always positive on inputs larger than one.
Similar to `cyclotomic_pos` but with the condition on the input rather than inde
x of the
cyclotomic polynomial.
-/
theorem cyclotomic_pos' (n : ℕ) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {x : R} (hx : 1 < x) :
    0 < eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).1 hx

/-- Cyclotomic polynomials are always nonnegative on inputs one or more. -/
/-
**Polynomial.cyclotomic_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cyclotomic_nonneg (n : Nat) {R} [CommRing R] [LinearOrder R] [IsStrictOrde
redRing R] {x : R} (hx : 1 <= x) : 0 <= eval x (cyclotomic n R)
参数：n : Nat；hx : 1 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.cyclotomic_pos_and_nonneg`：cyclotomic_pos_and_nonneg (n : Nat
) {R} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (x : R) : (1 < x -> 0
 < eval x (cyclotomic n R)…

--- 原说明 ---
Cyclotomic polynomials are always nonnegative on inputs one or more.
-/
theorem cyclotomic_nonneg (n : ℕ) {R}
    [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {x : R} (hx : 1 ≤ x) :
    0 ≤ eval x (cyclotomic n R) :=
  (cyclotomic_pos_and_nonneg n x).2 hx
/-
**Polynomial.eval_one_cyclotomic_not_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：eval_one_cyclotomic_not_prime_pow {R : Type*} [Ring R] {n : Nat} (h : fora
ll {p : Nat}, p.Prime -> forall k : Nat, p ^ k != n) : eval 1 (cyclotomic n R) =
 1
参数：h : forall {p : Nat}, p.Prime -> forall k : Nat, p ^ k != n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Int.natAbs_eq_natAbs_iff`：∀ {a b : ℤ}, a.natAbs = b.natAbs ↔ a = b ∨ a =
 -b
· 使用定理 `Int.natAbs_one`：Int.natAbs 1 = 1
· 使用定理 `Nat.eq_one_iff_not_exists_prime_dvd`：eq_one_iff_not_exists_prime_dvd {n 
: Nat} : n = 1 ↔ forall p : Nat, p.Prime -> ¬p ∣ n
· 使用定理 `Polynomial.prod_cyclotomic_eq_geom_sum`：prod_cyclotomic_eq_geom_sum {n :
 Nat} (h : 0 < n) (R) [CommRing R] : ∏ i in n.divisors.erase 1, cyclotomic i R =
 ∑ i in Finset.range n, X ^ …
· 使用定理 `Int.natAbs_dvd_natAbs`：∀ {a b : ℤ}, a.natAbs ∣ b.natAbs ↔ a ∣ b
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
（共 84 条，此处仅展示前 30 条）
-/
theorem eval_one_cyclotomic_not_prime_pow {R : Type*} [Ring R] {n : ℕ}
    (h : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n) : eval 1 (cyclotomic n R) = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn')
  · simp
  have hn : 1 < n := one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn'.ne', (h Nat.prime_two 0).symm⟩
  rsuffices h | h : eval 1 (cyclotomic n ℤ) = 1 ∨ eval 1 (cyclotomic n ℤ) = -1
  · have := eval_intCast_map (Int.castRingHom R) (cyclotomic n ℤ) 1
    simpa only [map_cyclotomic, Int.cast_one, h, eq_intCast] using this
  · exfalso
    linarith [cyclotomic_nonneg n (le_refl (1 : ℤ))]
  rw [← Int.natAbs_eq_natAbs_iff, Int.natAbs_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpe
  have := Fact.mk hp
  have := prod_cyclotomic_eq_geom_sum hn' ℤ
  apply_fun eval 1 at this
  rw [eval_geom_sum, one_geom_sum, eval_prod, eq_comm, ←
    Finset.prod_sdiff <| @range_pow_padicValNat_subset_divisors' p _ _, Finset.prod_image] at this
  · simp_rw [eval_one_cyclotomic_prime_pow, Finset.prod_const, Finset.card_range, mul_comm] at this
    rw [← Finset.prod_sdiff (s₁ := {n})] at this
    swap
    · simp only [singleton_subset_iff, mem_sdiff, mem_erase, Ne, mem_divisors, dvd_refl,
        true_and, mem_image, mem_range, not_exists, not_and]
      exact ⟨⟨hn.ne', hn'.ne'⟩, fun t _ => h hp _⟩
    rw [← Int.natAbs_natCast p, Int.natAbs_dvd_natAbs] at hpe
    obtain ⟨t, ht⟩ := hpe
    rw [Finset.prod_singleton, ht, mul_left_comm, mul_comm, ← mul_assoc, mul_assoc] at this
    have : (p : ℤ) ^ padicValNat p n * p ∣ n := ⟨_, this⟩
    simp only [← _root_.pow_succ, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast,
      Int.natAbs_pow] at this
    exact pow_succ_padicValNat_not_dvd hn'.ne' this
  · rintro x - y - hxy
    apply Nat.succ_injective
    exact Nat.pow_right_injective hp.two_le hxy
/-
**Polynomial.sub_one_pow_totient_lt_cyclotomic_eval** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：sub_one_pow_totient_lt_cyclotomic_eval {n : Nat} {q : Real} (hn' : 2 <= n)
 (hq' : 1 < q) : (q - 1) ^ totient n < (cyclotomic n Real).eval q
参数：hn' : 2 <= n；hq' : 1 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsPrimitiveRoot.norm'_eq_one`：∀ {ζ : ℂ} {n : ℕ}, IsPrimitiveRoot ζ n → n
 ≠ 0 → ‖ζ‖ = 1
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsPrimitiveRoot.ne_zero`：∀ {k : ℕ} {M₀ : Type u_7} [inst : CommMonoidWit
hZero M₀] [Nontrivial M₀] {ζ : M₀}, IsPrimitiveRoot ζ k → k ≠ 0 → ζ ≠ 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsPrimitiveRoot.arg_eq_zero_iff`：IsPrimitiveRoot.arg_eq_zero_iff {n : Na
t} {ζ : Complex} (hζ : IsPrimitiveRoot ζ n) (hn : n != 0) : ζ.arg = 0 ↔ ζ = 1
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 114 条，此处仅展示前 30 条）
-/
theorem sub_one_pow_totient_lt_cyclotomic_eval {n : ℕ} {q : ℝ} (hn' : 2 ≤ n) (hq' : 1 < q) :
    (q - 1) ^ totient n < (cyclotomic n ℝ).eval q := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀ ζ' ∈ primitiveRoots n ℂ, q - 1 ≤ ‖↑q - ζ'‖ := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_norm_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg hq.le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, q - 1 < ‖↑q - ζ'‖ := by
    refine ⟨ζ, (mem_primitiveRoots hn).mpr hζ, ?_⟩
    suffices ¬SameRay ℝ (q : ℂ) ζ by
      convert! lt_norm_sub_of_not_sameRay this <;>
        simp only [hζ.norm'_eq_one hn.ne', Real.norm_of_nonneg hq.le, Complex.norm_real]
    rw [Complex.sameRay_iff]
    push Not
    refine ⟨mod_cast hq.ne', hζ.ne_zero hn.ne', ?_⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le, Ne, eq_comm, hζ.arg_eq_zero_iff hn.ne']
    clear_value ζ
    rintro rfl
    linarith [hζ.unique IsPrimitiveRoot.one]
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by simpa using (cyclotomic_pos' n hq').ne'
  suffices Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq']) ^ totient n <
      Units.mk0 ‖(cyclotomic n ℂ).eval ↑q‖₊ (by simp_all) by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      hq'.le, coe_nnnorm, NNReal.coe_pow, Real.coe_toNNReal', sub_nonneg, sup_of_le_left] at this
    convert! this
    rw [eq_comm]
    simp [cyclotomic_nonneg n hq'.le]
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert! Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q - 1)) (by simp [hq'])
  · simp only [Complex.card_primitiveRoots, prod_const, card_attach]
  · simp only [Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, norm_nonneg, Units.val_mk0,
      Real.coe_toNNReal', coe_nnnorm, max_le_iff, tsub_le_iff_right]
    intro x hx
    simpa only [and_true, tsub_le_iff_right] using hfor x hx
  · simp only [Finset.mem_attach, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    simpa [hq'.le, Real.coe_toNNReal', max_eq_left, sub_nonneg] using hex
/-
**Polynomial.sub_one_pow_totient_le_cyclotomic_eval** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：∀ {q : ℝ}, 1 < q → ∀ (n : ℕ), (q - 1) ^ n.totient ≤ Polynomial.eval q (Pol
ynomial.cyclotomic n ℝ)
参数：n : ℕ；q - 1；Polynomial.cyclotomic n ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.sub_one_pow_totient_lt_cyclotomic_eval`：sub_one_pow_totient_l
t_cyclotomic_eval {n : Nat} {q : Real} (hn' : 2 <= n) (hq' : 1 < q) : (q - 1) ^ 
totient n < (cyclotomic n Real).eval q
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem sub_one_pow_totient_le_cyclotomic_eval {q : ℝ} (hq' : 1 < q) :
    ∀ n, (q - 1) ^ totient n ≤ (cyclotomic n ℝ).eval q
  | 0 => by simp only [totient_zero, _root_.pow_zero, cyclotomic_zero, eval_one, le_refl]
  | 1 => by simp only [totient_one, pow_one, cyclotomic_one, eval_sub, eval_X, eval_one, le_refl]
  | _ + 2 => (sub_one_pow_totient_lt_cyclotomic_eval le_add_self hq').le
/-
**Polynomial.cyclotomic_eval_lt_add_one_pow_totient** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：cyclotomic_eval_lt_add_one_pow_totient {n : Nat} {q : Real} (hn' : 3 <= n)
 (hq' : 1 < q) : (cyclotomic n Real).eval q < (q + 1) ^ totient n
参数：hn' : 3 <= n；hq' : 1 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsPrimitiveRoot.norm'_eq_one`：∀ {ζ : ℂ} {n : ℕ}, IsPrimitiveRoot ζ n → n
 ≠ 0 → ‖ζ‖ = 1
· 使用定理 `mem_primitiveRoots`：mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ in primi
tiveRoots k R ↔ IsPrimitiveRoot ζ k
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isPrimitiveRoot_exp`：isPrimitiveRoot_exp (n : Nat) (h0 : n != 0)
 : IsPrimitiveRoot (exp (2 * π * I / n)) n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.sameRay_iff`：sameRay_iff : SameRay Real x y ↔ x = 0 ∨ y = 0 ∨ x.
arg = y.arg
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `IsPrimitiveRoot.ne_zero`：∀ {k : ℕ} {M₀ : Type u_7} [inst : CommMonoidWit
hZero M₀] [Nontrivial M₀] {ζ : M₀}, IsPrimitiveRoot ζ k → k ≠ 0 → ζ ≠ 0
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `Complex.arg_ofReal_of_nonneg`：arg_ofReal_of_nonneg {x : Real} (hx : 0 <=
 x) : arg x = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
（共 151 条，此处仅展示前 30 条）
-/
theorem cyclotomic_eval_lt_add_one_pow_totient {n : ℕ} {q : ℝ} (hn' : 3 ≤ n) (hq' : 1 < q) :
    (cyclotomic n ℝ).eval q < (q + 1) ^ totient n := by
  have hn : 0 < n := pos_of_gt hn'
  have hq := zero_lt_one.trans hq'
  have hfor : ∀ ζ' ∈ primitiveRoots n ℂ, ‖↑q - ζ'‖ ≤ q + 1 := by
    intro ζ' hζ'
    rw [mem_primitiveRoots hn] at hζ'
    convert! norm_sub_le (↑q) ζ'
    · rw [Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans_lt hq').le]
    · rw [hζ'.norm'_eq_one hn.ne']
  let ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hex : ∃ ζ' ∈ primitiveRoots n ℂ, ‖↑q - ζ'‖ < q + 1 := by
    refine ⟨ζ, (mem_primitiveRoots hn).mpr hζ, ?_⟩
    suffices ¬SameRay ℝ (q : ℂ) (-ζ) by
      convert! norm_add_lt_of_not_sameRay this using 2
      · rw [Complex.norm_real]
        symm
        exact abs_eq_self.mpr hq.le
      · simp [hζ.norm'_eq_one hn.ne']
    rw [Complex.sameRay_iff]
    push Not
    refine ⟨mod_cast hq.ne', neg_ne_zero.mpr <| hζ.ne_zero hn.ne', ?_⟩
    rw [Complex.arg_ofReal_of_nonneg hq.le, Ne, eq_comm]
    intro h
    rw [Complex.arg_eq_zero_iff, Complex.neg_re, neg_nonneg, Complex.neg_im, neg_eq_zero] at h
    have hζ₀ : ζ ≠ 0 := by
      clear_value ζ
      rintro rfl
      exact hn.ne' (hζ.unique IsPrimitiveRoot.zero)
    have : ζ.re < 0 ∧ ζ.im = 0 := ⟨h.1.lt_of_ne ?_, h.2⟩
    · rw [← Complex.arg_eq_pi_iff, hζ.arg_eq_pi_iff hn.ne'] at this
      rw [this] at hζ
      linarith [hζ.unique <| IsPrimitiveRoot.neg_one 0 two_ne_zero.symm]
    · contrapose hζ₀
      apply Complex.ext <;> simp [hζ₀, h.2]
  have : ¬eval (↑q) (cyclotomic n ℂ) = 0 := by simpa using (cyclotomic_pos' n hq').ne.symm
  suffices Units.mk0 ‖(cyclotomic n ℂ).eval ↑q‖₊ (by simp_all) <
      Units.mk0 (Real.toNNReal (q + 1)) (by simp; linarith) ^ totient n by
    simp only [← Units.val_lt_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← NNReal.coe_lt_coe,
      coe_nnnorm, NNReal.coe_pow,
      Real.coe_toNNReal'] at this
    convert! this using 2
    · rw [eq_comm]
      simp [cyclotomic_nonneg n hq'.le]
    rw [eq_comm, max_eq_left_iff]
    linarith
  simp only [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, eval_prod, eval_C, eval_X, eval_sub,
    nnnorm_prod, Units.mk0_prod]
  convert! Finset.prod_lt_prod' (M := NNRealˣ) _ _
  swap; · exact fun _ => Units.mk0 (Real.toNNReal (q + 1)) (by positivity)
  · simp [Complex.card_primitiveRoots]
  · simp only [Finset.mem_attach, forall_true_left, Subtype.forall, ←
      Units.val_le_val, ← NNReal.coe_le_coe, Units.val_mk0,
      coe_nnnorm]
    intro x hx
    have : ‖_‖ ≤ _ := hfor x hx
    simp [this]
  · simp only [Finset.mem_attach, Subtype.exists, ←
      NNReal.coe_lt_coe, ← Units.val_lt_val, Units.val_mk0 _, coe_nnnorm]
    obtain ⟨ζ, hζ, hhζ : ‖_‖ < _⟩ := hex
    exact ⟨ζ, hζ, by simp [hhζ]⟩
/-
**Polynomial.cyclotomic_eval_le_add_one_pow_totient** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：∀ {q : ℝ}, 1 < q → ∀ (n : ℕ), Polynomial.eval q (Polynomial.cyclotomic n ℝ
) ≤ (q + 1) ^ n.totient
参数：n : ℕ；Polynomial.cyclotomic n ℝ；q + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.cyclotomic_zero`：cyclotomic_zero (R : Type*) [Ring R] : cyclo
tomic 0 R = 1
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Polynomial.cyclotomic_one`：cyclotomic_one (R : Type*) [Ring R] : cycloto
mic 1 R = X - 1
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Polynomial.cyclotomic_two`：cyclotomic_two (R : Type*) [Ring R] : cycloto
mic 2 R = X + 1
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Nat.totient_two`：totient_two : φ 2 = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.cyclotomic_eval_lt_add_one_pow_totient`：cyclotomic_eval_lt_ad
d_one_pow_totient {n : Nat} {q : Real} (hn' : 3 <= n) (hq' : 1 < q) : (cyclotomi
c n Real).eval q < (q + 1) ^ totient n
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
theorem cyclotomic_eval_le_add_one_pow_totient {q : ℝ} (hq' : 1 < q) :
    ∀ n, (cyclotomic n ℝ).eval q ≤ (q + 1) ^ totient n
  | 0 => by simp
  | 1 => by simp [add_assoc, zero_le_one]
  | 2 => by simp
  | _ + 3 => (cyclotomic_eval_lt_add_one_pow_totient le_add_self hq').le
/-
**Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial`。
形式化陈述：sub_one_pow_totient_lt_natAbs_cyclotomic_eval {n : Nat} {q : Nat} (hn' : 1
 < n) (hq : q != 1) : (q - 1) ^ totient n < ((cyclotomic n Int).eval ↑q).natAbs
参数：hn' : 1 < n；hq : q != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Int.natAbs_ne_zero`：∀ {a : ℤ}, a.natAbs ≠ 0 ↔ a ≠ 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.cyclotomic_coeff_zero`：cyclotomic_coeff_zero (R : Type*) [Com
mRing R] {n : Nat} (hn : 1 < n) : (cyclotomic n R).coeff 0 = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 42 条，此处仅展示前 30 条）
-/
theorem sub_one_pow_totient_lt_natAbs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq : q ≠ 1) :
    (q - 1) ^ totient n < ((cyclotomic n ℤ).eval ↑q).natAbs := by
  rcases hq.lt_or_gt.imp_left Nat.lt_one_iff.mp with (rfl | hq')
  · rw [zero_tsub, zero_pow (Nat.totient_pos.2 (pos_of_gt hn')).ne', pos_iff_ne_zero,
      Int.natAbs_ne_zero, Nat.cast_zero, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero _ hn']
    exact one_ne_zero
  rw [← @Nat.cast_lt ℝ, Nat.cast_pow, Nat.cast_sub hq'.le, Nat.cast_one, Nat.cast_natAbs]
  refine (sub_one_pow_totient_lt_cyclotomic_eval hn' (Nat.one_lt_cast.2 hq')).trans_le ?_
  convert! (cyclotomic.eval_apply (q : ℤ) n (algebraMap ℤ ℝ)).trans_le (le_abs_self _)
  simp
/-
**Polynomial.sub_one_lt_natAbs_cyclotomic_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：sub_one_lt_natAbs_cyclotomic_eval {n : Nat} {q : Nat} (hn' : 1 < n) (hq : 
q != 1) : q - 1 < ((cyclotomic n Int).eval ↑q).natAbs
参数：hn' : 1 < n；hq : q != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_self_pow`：∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), a ≤ a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.sub_one_pow_totient_lt_natAbs_cyclotomic_eval`：sub_one_pow_to
tient_lt_natAbs_cyclotomic_eval {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1) 
: (q - 1) ^ totient n < ((cyclotomic n Int).ev…
-/
theorem sub_one_lt_natAbs_cyclotomic_eval {n : ℕ} {q : ℕ} (hn' : 1 < n) (hq : q ≠ 1) :
    q - 1 < ((cyclotomic n ℤ).eval ↑q).natAbs :=
  calc
    q - 1 ≤ (q - 1) ^ totient n := Nat.le_self_pow (Nat.totient_pos.2 <| pos_of_gt hn').ne' _
    _ < ((cyclotomic n ℤ).eval ↑q).natAbs := sub_one_pow_totient_lt_natAbs_cyclotomic_eval hn' hq

end Polynomial

