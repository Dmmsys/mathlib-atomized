/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Characteristic and cardinality

We prove some results relating characteristic and cardinality of finite rings

## Tags
characteristic, cardinality, ring
-/

public section


/-- A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it does not divide
the characteristic. -/
/-
**isUnit_iff_not_dvd_char_of_ringChar_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : 
Nat) [Fact p.Prime] (hR : ringChar R != 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R
参数：R : Type*；p : Nat；hR : ringChar R != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Coprime.isCoprime`：∀ {m n : ℕ}, m.Coprime n → IsCoprime ↑m ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
A prime `p` is a unit in a commutative ring `R` of nonzero characteristic iff it
 does not divide
the characteristic.
-/
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : ringChar R ≠ 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R := by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.Prime := Fact.out
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq
      nth_rw 1 [← mul_one (ringChar R)] at hq
      exact Nat.Prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩
    simp_all only [ne_eq]
    grind [ringChar.dvd]
  · intro h
    rcases (hp.coprime_iff_not_dvd.mpr h).isCoprime with ⟨a, b, hab⟩
    apply_fun ((↑) : ℤ → R) at hab
    push_cast at hab
    rw [hch, mul_zero, add_zero, mul_comm] at hab
    exact .of_mul_eq_one a hab

/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
/-
**isUnit_iff_not_dvd_char** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime] 
[Finite R] : IsUnit (p : R) ↔ ¬p ∣ ringChar R
参数：R : Type*；p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_iff_not_dvd_char_of_ringChar_ne_zero`：isUnit_iff_not_dvd_char_of_
ringChar_ne_zero (R : Type*) [CommRing R] (p : Nat) [Fact p.Prime] (hR : ringCha
r R != 0) : IsUnit (p : R) ↔ ¬p ∣…
· 使用定理 `CharP.char_ne_zero_of_finite`：char_ne_zero_of_finite (p : Nat) [CharP R 
p] [Finite R] : p != 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)

--- 原说明 ---
A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic.
-/
theorem isUnit_iff_not_dvd_char (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)

/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
/-
**prime_dvd_char_iff_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : Nat)
 [Fact p.Prime] : p ∣ ringChar R ↔ p ∣ Fintype.card R
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_prime_addOrderOf_dvd_card`：∀ {G : Type u_3} [inst : AddGroup G] [
inst_1 : Fintype G] (p : ℕ) [Fact (Nat.Prime p)],   p ∣ Fintype.card G → ∃ x, ad
dOrderOf x = p
· 使用定理 `addOrderOf_nsmul_eq_zero`：∀ {G : Type u_1} [inst : AddMonoid G] (x : G),
 addOrderOf x • x = 0
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_not_dvd_char`：isUnit_iff_not_dvd_char (R : Type*) [CommRing R
] (p : Nat) [Fact p.Prime] [Finite R] : IsUnit (p : R) ↔ ¬p ∣ ringChar R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AddMonoid.addOrderOf_eq_one_iff`：∀ {G : Type u_1} [inst : AddMonoid G] {
x : G}, addOrderOf x = 1 ↔ x = 0
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a

--- 原说明 ---
The prime divisors of the characteristic of a finite commutative ring are exactl
y
the prime divisors of its cardinality.
-/
theorem prime_dvd_char_iff_dvd_card {R : Type*} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R := by
  refine
    ⟨fun h =>
      h.trans <|
        Int.natCast_dvd_natCast.mp <|
          (CharP.intCast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <|
            mod_cast Nat.cast_card_eq_zero R,
      fun h => ?_⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zero r
  rw [hr, nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u at hr₁
  rw [mul_zero, ← mul_assoc, hu, one_mul] at hr₁
  exact mt AddMonoid.addOrderOf_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one Fact.out)) hr₁

/-- A prime that divides the cardinality of a finite commutative ring `R`
isn't a unit in `R`. -/
/-
**not_isUnit_prime_of_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] {p : Nat
} [Fact p.Prime] (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R)
参数：hp : p ∣ Fintype.card R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_not_dvd_char`：isUnit_iff_not_dvd_char (R : Type*) [CommRing R
] (p : Nat) [Fact p.Prime] [Finite R] : IsUnit (p : R) ↔ ¬p ∣ ringChar R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `prime_dvd_char_iff_dvd_card`：prime_dvd_char_iff_dvd_card {R : Type*} [Co
mmRing R] [Fintype R] (p : Nat) [Fact p.Prime] : p ∣ ringChar R ↔ p ∣ Fintype.ca
rd R

--- 原说明 ---
A prime that divides the cardinality of a finite commutative ring `R`
isn't a unit in `R`.
-/
theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))
/-
**charP_of_card_eq_prime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] {p : Nat} 
[hp : Fact p.Prime] (hR : Fintype.card R = p) : CharP R p
参数：hR : Fintype.card R = p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CharP.charP_iff_prime_eq_zero`：charP_iff_prime_eq_zero [Nontrivial R] {p
 : Nat} (hp : p.Prime) : CharP R p ↔ (p : R) = 0
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
-/
lemma charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] {p : ℕ} [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p :=
  have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)
/-
**charP_of_card_eq_prime_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：charP_of_card_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype 
R] {p f : Nat} [hp : Fact p.Prime] (hR : Fintype.card R = p ^ f) : CharP R p
参数：hR : Fintype.card R = p ^ f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton : car
d α <= 1 ↔ Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CharP.charP_iff_prime_eq_zero`：charP_iff_prime_eq_zero [Nontrivial R] {p
 : Nat} (hp : p.Prime) : CharP R p ↔ (p : R) = 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
-/
lemma charP_of_card_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype R] {p f : ℕ}
    [hp : Fact p.Prime] (hR : Fintype.card R = p ^ f) : CharP R p :=
  have hf : f ≠ 0 := fun h0 ↦ not_subsingleton R <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)
