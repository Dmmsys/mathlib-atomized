/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Cast.Commute

/-!
# Invertibility of elements given a characteristic

This file includes some instances of `Invertible` for specific numbers in
characteristic zero. Some more cases are given as a `def`, to be included only
when needed. To construct instances for concrete numbers,
`invertibleOfNonzero` is a useful definition.
-/

@[expose] public section


variable {R K : Type*}

/-- When two is invertible, every element is `Even`. -/
@[simp]
/-
**Even.all** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Even.all [Semiring R] [Invertible (2 : R)] (a : R) : Even a
参数：2 : R；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Even.of_isUnit_two`：Even.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Ev
en a
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a

--- 原说明 ---
When two is invertible, every element is `Even`.
-/
theorem Even.all [Semiring R] [Invertible (2 : R)] (a : R) : Even a :=
  .of_isUnit_two (isUnit_of_invertible _) _

/-- When two is invertible in a ring, every element is `Odd`. -/
@[simp low]
/-
**Odd.all** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Odd.all [Ring R] [Invertible (2 : R)] (a : R) : Odd a
参数：2 : R；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Odd.of_isUnit_two`：Odd.of_isUnit_two (h : IsUnit (2 : α)) (a : α) : Odd 
a
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a

--- 原说明 ---
When two is invertible in a ring, every element is `Odd`.
-/
theorem Odd.all [Ring R] [Invertible (2 : R)] (a : R) : Odd a :=
  .of_isUnit_two (isUnit_of_invertible _) _

section Ring
variable [Ring R] {p : ℕ} [CharP R p]

/-
**not_ringChar_dvd_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_ringChar_dvd_of_invertible {t : Nat} [Invertible (t : R)] [Nontrivial 
R] : ¬ringChar R ∣ t
参数：t : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Invertible.ne_zero`：Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nont
rivial α] [Invertible a] : a != 0
-/
theorem not_ringChar_dvd_of_invertible {t : ℕ} [Invertible (t : R)] [Nontrivial R] :
    ¬ringChar R ∣ t := by
  rw [← ringChar.spec, ← Ne]
  exact Invertible.ne_zero (t : R)
/-
**CharP.intCast_mul_natCast_gcdA_eq_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.intCast_mul_natCast_gcdA_eq_gcd (n : Nat) : (n * n.gcdA p : R) = n.g
cd p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem CharP.intCast_mul_natCast_gcdA_eq_gcd (n : ℕ) :
    (n * n.gcdA p : R) = n.gcd p := by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : ℤ) = ((n.gcd p : ℤ) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]
/-
**CharP.natCast_gcdA_mul_intCast_eq_gcd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.natCast_gcdA_mul_intCast_eq_gcd (n : Nat) : (n.gcdA p * n : R) = n.g
cd p
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `CharP.intCast_mul_natCast_gcdA_eq_gcd`：CharP.intCast_mul_natCast_gcdA_eq
_gcd (n : Nat) : (n * n.gcdA p : R) = n.gcd p
-/
theorem CharP.natCast_gcdA_mul_intCast_eq_gcd (n : ℕ) :
    (n.gcdA p * n : R) = n.gcd p :=
  Nat.commute_cast _ _ |>.eq.trans <| CharP.intCast_mul_natCast_gcdA_eq_gcd n

/-- In a ring of characteristic `p`, `(n : R)` is invertible when `n` is coprime with `p`, with
inverse `n.gcdA p`. -/
@[instance_reducible]
/-
**invertibleOfCoprime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfCoprime {n : Nat} (h : n.Coprime p) : Invertible (n : R) where
 invOf
参数：h : n.Coprime p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a ring of characteristic `p`, `(n : R)` is invertible when `n` is coprime wit
h `p`, with
inverse `n.gcdA p`.
-/
def invertibleOfCoprime {n : ℕ} (h : n.Coprime p) :
    Invertible (n : R) where
  invOf := n.gcdA p
  invOf_mul_self := by rw [CharP.natCast_gcdA_mul_intCast_eq_gcd, h, Nat.cast_one]
  mul_invOf_self := by rw [CharP.intCast_mul_natCast_gcdA_eq_gcd, h, Nat.cast_one]
/-
**invOf_eq_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_of_coprime {n : Nat} [Invertible (n : R)] (h : n.Coprime p) : ⅟(n
 : R) = n.gcdA p
参数：n : R；h : n.Coprime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem invOf_eq_of_coprime {n : ℕ} [Invertible (n : R)] (h : n.Coprime p) :
    ⅟(n : R) = n.gcdA p := by
  let : Invertible (n : R) := invertibleOfCoprime h
  convert! (rfl : ⅟(n : R) = _)
/-
**CharP.isUnit_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.isUnit_natCast_iff {n : Nat} (hp : p.Prime) : IsUnit (n : R) ↔ ¬p ∣ 
n where mp h
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.nontrivial_of_char_ne_one`：nontrivial_of_char_ne_one {v : Nat} (hv
 : v != 1) [hr : CharP R v] : Nontrivial R
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
-/
theorem CharP.isUnit_natCast_iff {n : ℕ} (hp : p.Prime) : IsUnit (n : R) ↔ ¬p ∣ n where
  mp h := by
    have := CharP.nontrivial_of_char_ne_one (R := R) hp.ne_one
    rw [← CharP.cast_eq_zero_iff (R := R)]
    exact h.ne_zero
  mpr not_dvd :=
    letI := invertibleOfCoprime (R := R) (hp.coprime_iff_not_dvd.2 not_dvd).symm
    isUnit_of_invertible _
/-
**CharP.isUnit_ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.isUnit_ofNat_iff {n : Nat} [n.AtLeastTwo] (hp : p.Prime) : IsUnit (o
fNat(n) : R) ↔ ¬p ∣ ofNat(n)
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.isUnit_natCast_iff`：CharP.isUnit_natCast_iff {n : Nat} (hp : p.Pri
me) : IsUnit (n : R) ↔ ¬p ∣ n where mp h
-/
theorem CharP.isUnit_ofNat_iff {n : ℕ} [n.AtLeastTwo] (hp : p.Prime) :
    IsUnit (ofNat(n) : R) ↔ ¬p ∣ ofNat(n) :=
  CharP.isUnit_natCast_iff hp
/-
**CharP.isUnit_intCast_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharP.isUnit_intCast_iff {z : Int} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣
 z
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `CharP.isUnit_natCast_iff`：CharP.isUnit_natCast_iff {n : Nat} (hp : p.Pri
me) : IsUnit (n : R) ↔ ¬p ∣ n where mp h
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
theorem CharP.isUnit_intCast_iff {z : ℤ} (hp : p.Prime) : IsUnit (z : R) ↔ ¬↑p ∣ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simp [CharP.isUnit_natCast_iff hp, Int.ofNat_dvd]
  · simp [CharP.isUnit_natCast_iff hp, Int.dvd_neg, Int.ofNat_dvd]

end Ring

section Semifield
variable [Semifield K]

/-- A natural number `t` is invertible in a semifield `K` if the characteristic of `K` does not
divide `t`. -/
@[instance_reducible]
/-
**invertibleOfRingCharNotDvd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfRingCharNotDvd {t : Nat} (not_dvd : ¬ringChar K ∣ t) : Inverti
ble (t : K)
参数：not_dvd : ¬ringChar K ∣ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural number `t` is invertible in a semifield `K` if the characteristic of `
K` does not
divide `t`.
-/
def invertibleOfRingCharNotDvd {t : ℕ} (not_dvd : ¬ringChar K ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((ringChar.spec K t).mp h)

/-- A natural number `t` is invertible in a semifield `K` of characteristic `p` if `p` does not
divide `t`. -/
@[instance_reducible]
/-
**invertibleOfCharPNotDvd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfCharPNotDvd {p : Nat} [CharP K p] {t : Nat} (not_dvd : ¬p ∣ t)
 : Invertible (t : K)
参数：not_dvd : ¬p ∣ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural number `t` is invertible in a semifield `K` of characteristic `p` if `
p` does not
divide `t`.
-/
def invertibleOfCharPNotDvd {p : ℕ} [CharP K p] {t : ℕ} (not_dvd : ¬p ∣ t) : Invertible (t : K) :=
  invertibleOfNonzero fun h => not_dvd ((CharP.cast_eq_zero_iff K p t).mp h)

-- warning: this could potentially loop with `Invertible.ne_zero` - if there are weird type-class
-- loops, watch out for that.
/-
**invertibleOfPos** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleOfPos [CharZero K] (n : Nat) [NeZero n] : Invertible (n : K)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invertibleOfPos [CharZero K] (n : ℕ) [NeZero n] : Invertible (n : K) :=
  invertibleOfNonzero <| NeZero.out

end Semifield

section DivisionSemiring
variable [DivisionSemiring K] [CharZero K]

/-
**invertibleSucc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleSucc (n : Nat) : Invertible (n.succ : K)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invertibleSucc (n : ℕ) : Invertible (n.succ : K) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))

/-!
A few `Invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/


/-
**invertibleTwo** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleTwo : Invertible (2 : K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A few `Invertible n` instances for small numerals `n`. Feel free to add your own
number when you need its inverse.
-/
instance invertibleTwo : Invertible (2 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 2 ≠ 0))
/-
**invertibleThree** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleThree : Invertible (3 : K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invertibleThree : Invertible (3 : K) :=
  invertibleOfNonzero (mod_cast (by decide : 3 ≠ 0))

end DivisionSemiring

