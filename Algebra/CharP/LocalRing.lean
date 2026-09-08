/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Characteristics of local rings

## Main result

- `charP_zero_or_prime_power`: In a commutative local ring the characteristic is either
  zero or a prime power.

-/

public section


/-- In a local ring the characteristic is either zero or a prime power. -/
/-
**charP_zero_or_prime_power** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：charP_zero_or_prime_power (R : Type*) [CommRing R] [IsLocalRing R] (q : Na
t) [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q
参数：R : Type*；q : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用定理 `Nat.not_dvd_ordCompl`：not_dvd_ordCompl {n p : Nat} (hp : Prime p) (hn : 
n != 0) : ¬p ∣ ordCompl[p] n
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `mem_nonunits_iff`：mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUni
t a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
In a local ring the characteristic is either zero or a prime power.
-/
theorem charP_zero_or_prime_power (R : Type*) [CommRing R] [IsLocalRing R] (q : ℕ)
    [char_R_q : CharP R q] : q = 0 ∨ IsPrimePow q := by
  -- Assume `q := char(R)` is not zero.
  apply or_iff_not_imp_left.2
  intro q_pos
  let K := IsLocalRing.ResidueField R
  have RM_char := ringChar.charP K
  let r := ringChar K
  let n := q.factorization r
  -- `r := char(R/m)` is either prime or zero:
  rcases CharP.char_is_prime_or_zero K r with r_prime | r_zero
  · let a := q / r ^ n
    -- If `r` is prime, we can write `q` as `a * r^n` ...
    have q_eq_a_mul_rn : q = r ^ n * a := by rw [Nat.mul_div_cancel' (Nat.ordProj_dvd q r)]
    have r_ne_dvd_a := Nat.not_dvd_ordCompl r_prime q_pos
    have rn_dvd_q : r ^ n ∣ q := ⟨a, q_eq_a_mul_rn⟩
    rw [mul_comm] at q_eq_a_mul_rn
    -- ... where `a` is a unit.
    have a_unit : IsUnit (a : R) := by
      by_contra g
      rw [← mem_nonunits_iff] at g
      rw [← IsLocalRing.mem_maximalIdeal] at g
      have a_cast_zero := Ideal.Quotient.eq_zero_iff_mem.2 g
      rw [map_natCast] at a_cast_zero
      have r_dvd_a := (ringChar.spec K a).1 a_cast_zero
      exact absurd r_dvd_a r_ne_dvd_a
    have rn_cast_zero : ↑(r ^ n) = (0 : R) := by
      rw [← one_mul (↑(r ^ n) : R), ← a_unit.val_inv_mul, mul_assoc, ← Nat.cast_mul,
        ← q_eq_a_mul_rn, CharP.cast_eq_zero R q, mul_zero]
    have q_eq_rn := Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R q (r ^ n)).mp rn_cast_zero) rn_dvd_q
    have n_pos : n ≠ 0 := fun n_zero =>
      absurd (by simpa [n_zero] using q_eq_rn) (CharP.char_ne_one R q)
    -- Definition of prime power: `∃ r n, Prime r ∧ 0 < n ∧ r ^ n = q`.
    exact ⟨r, ⟨n, ⟨r_prime.prime, ⟨pos_iff_ne_zero.mpr n_pos, q_eq_rn.symm⟩⟩⟩⟩
  · have K_char_p_0 := ringChar.of_eq r_zero
    have K_char_zero : CharZero K := CharP.charP_to_charZero K
    have R_char_zero := RingHom.charZero (IsLocalRing.residue R)
    -- Finally, `r = 0` would lead to a contradiction:
    have q_zero := CharP.eq R char_R_q (CharP.ofCharZero R)
    exact absurd q_zero q_pos
