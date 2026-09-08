/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Invertibility of factorials

This file contains lemmas providing sufficient conditions for the cast of `n!` to a (semi)ring `A`
to be a unit.

-/

public section

namespace IsUnit

open Nat
section Semiring

variable {A : Type*} [Semiring A]

/-
**IsUnit.natCast_factorial_of_le** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：natCast_factorial_of_le {n : Nat} (hn_fac : IsUnit (n ! : A)) {m : Nat} (h
mn : m <= n) : IsUnit (m ! : A)
参数：hn_fac : IsUnit (n ! : A)；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
-/
theorem natCast_factorial_of_le {n : ℕ} (hn_fac : IsUnit (n ! : A))
    {m : ℕ} (hmn : m ≤ n) : IsUnit (m ! : A) := by
  obtain ⟨k, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction k generalizing m with
  | zero => simpa using hn_fac
  | succ k ih =>
    rw [← add_assoc, add_right_comm] at hn_fac
    have := ih hn_fac
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff] at this
    exact this.2
/-
**IsUnit.natCast_factorial_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：natCast_factorial_of_lt {n : Nat} (hn_fac : IsUnit ((n - 1)! : A)) {m : Na
t} (hmn : m < n) : IsUnit (m ! : A)
参数：hn_fac : IsUnit ((n - 1)! : A)；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.natCast_factorial_of_le`：natCast_factorial_of_le {n : Nat} (hn_fa
c : IsUnit (n ! : A)) {m : Nat} (hmn : m <= n) : IsUnit (m ! : A)
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
-/
theorem natCast_factorial_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A))
    {m : ℕ} (hmn : m < n) : IsUnit (m ! : A) :=
  hn_fac.natCast_factorial_of_le <| le_sub_one_of_lt hmn

/-- If `A` is an algebra over a characteristic-zero (semi)field, then `n!` is a unit. -/
/-
**IsUnit.natCast_factorial_of_algebra** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：natCast_factorial_of_algebra (K : Type*) [Semifield K] [CharZero K] [Algeb
ra K A] (n : Nat) : IsUnit (n ! : A)
参数：K : Type*；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If `A` is an algebra over a characteristic-zero (semi)field, then `n!` is a unit
.
-/
theorem natCast_factorial_of_algebra (K : Type*) [Semifield K] [CharZero K] [Algebra K A] (n : ℕ) :
    IsUnit (n ! : A) := by
  suffices IsUnit (n ! : K) by
    simpa using this.map (algebraMap K A)
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

end Semiring

section CharP

variable {A : Type*} [Ring A] (p : ℕ) [Fact (Nat.Prime p)] [CharP A p]

/-
**IsUnit.natCast_factorial_iff_of_charP** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：natCast_factorial_iff_of_charP {n : Nat} : IsUnit (n ! : A) ↔ n < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `CharP.isUnit_natCast_iff`：CharP.isUnit_natCast_iff {n : Nat} (hp : p.Pri
me) : IsUnit (n : R) ↔ ¬p ∣ n where mp h
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem natCast_factorial_iff_of_charP {n : ℕ} : IsUnit (n ! : A) ↔ n < p := by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp [hp.pos]
  | succ n ih =>
    -- TODO: why is `.symm.symm` needed here!?
    rw [factorial_succ, cast_mul, Nat.cast_commute _ _ |>.isUnit_mul_iff, ih.symm.symm,
      ← Nat.add_one_le_iff, CharP.isUnit_natCast_iff hp]
    exact ⟨fun ⟨h1, h2⟩ ↦ lt_of_le_of_ne h2 (mt (· ▸ dvd_rfl) h1),
      fun h ↦ ⟨not_dvd_of_pos_of_lt (Nat.succ_pos _) h, h.le⟩⟩

end CharP

section Nilpotent

variable {A : Type*} [CommRing A] {n p : ℕ} (hp : IsNilpotent (p : A))
include hp

/-
**IsUnit.natCast_of_isNilpotent_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：natCast_of_isNilpotent_of_coprime (h : p.Coprime n) : IsUnit (n : A)
参数：h : p.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma natCast_of_isNilpotent_of_coprime (h : p.Coprime n) :
    IsUnit (n : A) := by
  obtain ⟨m, hm⟩ := hp
  suffices ∃ a b : A, p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    refine .of_mul_eq_one b ?_
    simpa [hm] using h
  refine ⟨(p ^ m).gcdA n, (p ^ m).gcdB n, ?_⟩
  norm_cast
  rw [← Nat.cast_one, ← Int.cast_natCast 1, ← (h.pow_left m).gcd_eq_one, Nat.gcd_eq_gcd_ab]
/-
**IsUnit.natCast_factorial_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：natCast_factorial_of_isNilpotent [Fact p.Prime] (h : n < p) : IsUnit (n ! 
: A)
参数：h : n < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `IsUnit.natCast_of_isNilpotent_of_coprime`：natCast_of_isNilpotent_of_copr
ime (h : p.Coprime n) : IsUnit (n : A)
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
-/
theorem natCast_factorial_of_isNilpotent [Fact p.Prime] (h : n < p) :
    IsUnit (n ! : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    refine ⟨.natCast_of_isNilpotent_of_coprime hp ?_, ih (by lia)⟩
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    exact Nat.not_dvd_of_pos_of_lt (by lia) h

end Nilpotent

end IsUnit

open Nat Ring

/-
**Nat.castChoose_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.castChoose_eq {A : Type*} [CommSemiring A] {m : Nat} {k : Nat × Nat} (
hm : IsUnit (m ! : A)) (hk : k in Finset.antidiagonal m) : (choose m k.1 : A) = 
↑m ! * inverse ↑k.1! * inverse ↑k.2!
参数：hm : IsUnit (m ! : A)；hk : k in Finset.antidiagonal m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.eq_mul_inverse_iff_mul_eq`：eq_mul_inverse_iff_mul_eq (x y z : M₀) (
h : IsUnit z) : x = y * z⁻¹ʳ ↔ x * z = y
· 使用定理 `IsUnit.natCast_factorial_of_le`：natCast_factorial_of_le {n : Nat} (hn_fa
c : IsUnit (n ! : A)) {m : Nat} (hmn : m <= n) : IsUnit (m ! : A)
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.add_choose_mul_factorial_mul_factorial`：add_choose_mul_factorial_mul
_factorial (i j : Nat) : (i + j).choose j * i ! * j ! = (i + j)!
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
lemma Nat.castChoose_eq {A : Type*} [CommSemiring A] {m : ℕ} {k : ℕ × ℕ}
    (hm : IsUnit (m ! : A)) (hk : k ∈ Finset.antidiagonal m) :
    (choose m k.1 : A) = ↑m ! * inverse ↑k.1! * inverse ↑k.2! := by
  rw [Finset.mem_antidiagonal] at hk
  subst hk
  rw [eq_mul_inverse_iff_mul_eq, eq_mul_inverse_iff_mul_eq, ← Nat.cast_mul, ← Nat.cast_mul,
    add_comm, Nat.add_choose_mul_factorial_mul_factorial] <;>
    apply hm.natCast_factorial_of_le
  exacts [Nat.le_add_right k.1 k.2, Nat.le_add_left k.2 k.1]
