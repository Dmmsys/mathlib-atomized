/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Prime elements

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`
(see `irreducible_iff_prime`), however this is not true in general.

## Main definitions

* `Prime`: a prime element of a commutative monoid with zero

## Main results

* `irreducible_iff_prime`: the two definitions are equivalent in a decomposition monoid.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

/-- An element `p` of a commutative monoid with zero (e.g., a ring) is called *prime*,
if it's not zero, not a unit, and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`. -/
/-
**Prime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Prime (p : M) : Prop
参数：p : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `p` of a commutative monoid with zero (e.g., a ring) is called *prime
*,
if it's not zero, not a unit, and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`.
-/
def Prime (p : M) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b

namespace Prime

variable {p : M} (hp : Prime p)
include hp

/-
**Prime.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：ne_zero : p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ne_zero : p ≠ 0 :=
  hp.1
/-
**Prime.not_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：not_isUnit : ¬IsUnit p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem not_isUnit : ¬IsUnit p :=
  hp.2.1

@[deprecated (since := "2026-08-02")]
alias not_unit := not_isUnit
/-
**Prime.not_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：not_dvd_one : ¬p ∣ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
-/
theorem not_dvd_one : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one ·) hp.not_isUnit
/-
**Prime.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：ne_one : p != 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_one : p ≠ 1 := fun h => hp.2.1 (h.symm ▸ isUnit_one)
/-
**Prime.dvd_or_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
参数：h : p ∣ a * b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h
/-
**Prime.dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
-/
theorem dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩
/-
**Prime.isPrimal** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：isPrimal : IsPrimal p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem isPrimal : IsPrimal p := fun _a _b dvd ↦ (hp.dvd_or_dvd dvd).elim
  (fun h ↦ ⟨p, 1, h, one_dvd _, (mul_one p).symm⟩) fun h ↦ ⟨1, p, one_dvd _, h, (one_mul p).symm⟩
/-
**Prime.not_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b
参数：ha : ¬ p ∣ a；hb : ¬ p ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Prime.dvd_mul`：dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
  hp.dvd_mul.not.mpr <| not_or.mpr ⟨ha, hb⟩
/-
**Prime.dvd_of_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) : p ∣ a
参数：h : p ∣ a ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem dvd_of_dvd_pow {a : M} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_isUnit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow
/-
**Prime.dvd_pow_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：dvd_pow_iff_dvd {a : M} {n : Nat} (hn : n != 0) : p ∣ a ^ n ↔ p ∣ a
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用引理 `dvd_pow`：dvd_pow (hab : a ∣ b) : forall {n : Nat} (_ : n != 0), a ∣ b ^ 
n | 0, hn => (hn rfl).elim | n + 1, _ => by rw [pow_succ']; exact hab.mul_rig…
-/
theorem dvd_pow_iff_dvd {a : M} {n : ℕ} (hn : n ≠ 0) : p ∣ a ^ n ↔ p ∣ a :=
  ⟨hp.dvd_of_dvd_pow, (dvd_pow · hn)⟩

end Prime

@[simp]
/-
**not_prime_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_prime_zero : ¬Prime (0 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
-/
theorem not_prime_zero : ¬Prime (0 : M) := fun h => h.ne_zero rfl

@[simp]
/-
**not_prime_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_prime_one : ¬Prime (1 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem not_prime_one : ¬Prime (1 : M) := fun h => h.not_isUnit isUnit_one

end Prime

/-
**Irreducible.not_dvd_isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.not_dvd_isUnit [CommMonoid M] {p u : M} (hp : Irreducible p) (
hu : IsUnit u) : ¬p ∣ u
参数：hp : Irreducible p；hu : IsUnit u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `isUnit_of_dvd_unit`：isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUn
it y) : IsUnit x
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
-/
theorem Irreducible.not_dvd_isUnit [CommMonoid M] {p u : M} (hp : Irreducible p) (hu : IsUnit u) :
    ¬p ∣ u :=
  mt (isUnit_of_dvd_unit · hu) hp.not_isUnit
/-
**Irreducible.not_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣
 1
参数：hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_dvd_isUnit`：Irreducible.not_dvd_isUnit [CommMonoid M] {p
 u : M} (hp : Irreducible p) (hu : IsUnit u) : ¬p ∣ u
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
-/
theorem Irreducible.not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣ 1 :=
  hp.not_dvd_isUnit isUnit_one
/-
**Irreducible.not_dvd_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.not_dvd_unit [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible
 p) : ¬ p ∣ u
参数：u : Mˣ；hp : Irreducible p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_dvd_isUnit`：Irreducible.not_dvd_isUnit [CommMonoid M] {p
 u : M} (hp : Irreducible p) (hu : IsUnit u) : ¬p ∣ u
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem Irreducible.not_dvd_unit [CommMonoid M] {p : M} (u : Mˣ) (hp : Irreducible p) :
    ¬ p ∣ u :=
  hp.not_dvd_isUnit u.isUnit

@[simp]
/-
**not_irreducible_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M) | ⟨hn0, h⟩ 
=> have : IsUnit (0 : M) ∨ IsUnit (0 : M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : M) ∨ IsUnit (0 : M) := h (mul_zero 0).symm
    this.elim hn0 hn0
/-
**Irreducible.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Irreducible`。
形式化陈述：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M}, Irreducible p → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_irreducible_zero`：not_irreducible_zero [MonoidWithZero M] : ¬Irreduc
ible (0 : M) | ⟨hn0, h⟩ => have : IsUnit (0 : M) ∨ IsUnit (0 : M)
-/
theorem Irreducible.ne_zero [MonoidWithZero M] : ∀ {p : M}, Irreducible p → p ≠ 0
  | _, hp, rfl => not_irreducible_zero hp

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
/-
**Irreducible.dvd_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irred
ucible q) : p ∣ q -> q ∣ p
参数：hp : Irreducible p；hq : Irreducible q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.mul_right_dvd`：mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `of_irreducible_mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Irredu
cible (a * b) → IsUnit a ∨ IsUnit b
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`.
-/
theorem Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q → q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_isUnit)]
/-
**Irreducible.dvd_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irred
ucible q) : p ∣ q ↔ q ∣ p
参数：hp : Irreducible p；hq : Irreducible q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.dvd_symm`：Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Ir
reducible p) (hq : Irreducible q) : p ∣ q -> q ∣ p
-/
theorem Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section CommMonoidWithZero

variable [CommMonoidWithZero M]

/-
**Irreducible.prime_of_isPrimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.prime_of_isPrimal {a : M} (irr : Irreducible a) (primal : IsPr
imal a) : Prime a
参数：irr : Irreducible a；primal : IsPrimal a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsUnit.mul_right_dvd`：mul_right_dvd (hu : IsUnit u) : a * u ∣ b ↔ a ∣ b
· 使用定理 `IsUnit.mul_left_dvd`：mul_left_dvd (hu : IsUnit u) : u * a ∣ b ↔ a ∣ b
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `of_irreducible_mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Irredu
cible (a * b) → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Irreducible.prime_of_isPrimal {a : M}
    (irr : Irreducible a) (primal : IsPrimal a) : Prime a :=
  ⟨irr.ne_zero, irr.not_isUnit, fun a b dvd ↦ by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩
/-
**Irreducible.prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : 
Prime a
参数：irr : Irreducible a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.prime_of_isPrimal`：Irreducible.prime_of_isPrimal {a : M} (ir
r : Irreducible a) (primal : IsPrimal a) : Prime a
· 使用定理 `DecompositionMonoid.primal`：∀ {α : Type u_1} {inst : Semigroup α} [self 
: DecompositionMonoid α] (a : α), IsPrimal a
-/
theorem Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : Prime a :=
  irr.prime_of_isPrimal (DecompositionMonoid.primal a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M] [IsCancelMulZero M] {p : M}

/-
**Prime.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Prime`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCancelMulZero M] {p : M}
, Prime p → Irreducible p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_dvd_mul_iff_right`：mul_dvd_mul_iff_right [CommMonoidWithZero α] [IsC
ancelMulZero α] {a b c : α} (hc : c != 0) : a * c ∣ b * c ↔ a ∣ b
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Prime.irreducible (hp : Prime p) : Irreducible p :=
  ⟨hp.not_isUnit, fun a b ↦ by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_left · _)⟩
/-
**irreducible_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Pr
ime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.prime`：Irreducible.prime [DecompositionMonoid M] {a : M} (ir
r : Irreducible a) : Prime a
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Prime a :=
  ⟨Irreducible.prime, Prime.irreducible⟩

end CancelCommMonoidWithZero

