/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `ZMod p` vanishes if and only if
`a` and `p` are not coprime.
-/

public section

assert_not_exists TwoSidedIdeal

namespace ZMod

/-- If `p` is a prime and `a` is an integer, then `a : ZMod p` is zero if and only if
`gcd a p ≠ 1`. -/
/-
**ZMod.eq_zero_iff_gcd_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eq_zero_iff_gcd_ne_one {a : Int} {p : Nat} [pp : Fact p.Prime] : (a : ZMod
 p) = 0 ↔ a.gcd p != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Int.gcd_comm`：∀ (a b : ℤ), a.gcd b = b.gcd a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用定理 `Prime.coprime_iff_not_dvd`：Prime.coprime_iff_not_dvd {p n : Nat} (pp : P
rime p) : Coprime p n ↔ ¬p ∣ n
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `ZMod.intCast_zmod_eq_zero_iff_dvd`：intCast_zmod_eq_zero_iff_dvd (a : Int
) (b : Nat) : (a : ZMod b) = 0 ↔ (b : Int) ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `p` is a prime and `a` is an integer, then `a : ZMod p` is zero if and only i
f
`gcd a p ≠ 1`.
-/
theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, ← Int.isCoprime_iff_gcd_eq_one,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    intCast_zmod_eq_zero_iff_dvd]

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : ZMod p` is nonzero. -/
/-
**ZMod.ne_zero_of_gcd_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：ne_zero_of_gcd_eq_one {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p = 1)
 : (a : ZMod p) != 0
参数：pp : p.Prime；h : a.gcd p = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.eq_zero_iff_gcd_ne_one`：eq_zero_iff_gcd_ne_one {a : Int} {p : Nat} 
[pp : Fact p.Prime] : (a : ZMod p) = 0 ↔ a.gcd p != 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : ZMod p` is no
nzero.
-/
theorem ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p = 1) : (a : ZMod p) ≠ 0 :=
  mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : ZMod p` is zero. -/
/-
**ZMod.eq_zero_of_gcd_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eq_zero_of_gcd_ne_one {a : Int} {p : Nat} (pp : p.Prime) (h : a.gcd p != 1
) : (a : ZMod p) = 0
参数：pp : p.Prime；h : a.gcd p != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.eq_zero_iff_gcd_ne_one`：eq_zero_iff_gcd_ne_one {a : Int} {p : Nat} 
[pp : Fact p.Prime] : (a : ZMod p) = 0 ↔ a.gcd p != 1

--- 原说明 ---
If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : ZMod p` is ze
ro.
-/
theorem eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p ≠ 1) : (a : ZMod p) = 0 :=
  (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

end ZMod

