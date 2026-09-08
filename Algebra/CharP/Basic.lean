/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Cast.Prod
public import Mathlib.Data.ULift
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Ring.GrindInstances

/-!
# Characteristic of semirings

This file collects some fundamental results on the characteristic of rings that don't need the extra
imports of `Mathlib/Algebra/CharP/Lemmas.lean`.

As such, we can probably reorganize and find a better home for most of these lemmas.
-/

public section

assert_not_exists Finset TwoSidedIdeal

open Set

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

/-
**CharP.natCast_eq_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b
参数：h : a ≡ b [MOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
lemma natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (cast_eq_zero_iff R p _).mpr h, zero_add]
/-
**CharP.natCast_eq_natCast_mod** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：natCast_eq_natCast_mod (a : Nat) : (a : R) = a % p
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.natCast_eq_natCast'`：natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a 
: R) = b
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `Nat.mod_modEq`：mod_modEq (a n) : a % n ≡ a [MOD n]
-/
lemma natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p :=
  natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

variable [IsRightCancelAdd R]
/-
**CharP.natCast_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
-/
lemma natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]
/-
**CharP.natCast_injOn_Iio** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : Nat -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ModEq.eq_of_lt_of_lt`：eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m
) (hb : b < m) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CharP.natCast_eq_natCast`：natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD 
p]
-/
lemma natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) :=
  fun _a ha _b hb hab ↦ ((natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

/-
**CharP.intCast_eq_intCast** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.intCast_eq_zero_iff R p, Int.modEq_iff_dvd]
/-
**CharP.intCast_eq_intCast_mod** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：intCast_eq_intCast_mod : (a : R) = a % (p : Int)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CharP.intCast_eq_intCast`：intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD
 p]
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
-/
lemma intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) :=
  (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm
/-
**CharP.intCast_injOn_Ico** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : Int -> R) (Ico 
0 p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用引理 `CharP.natCast_injOn_Iio`：natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : Na
t -> R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
-/
lemma intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : ℤ → R) (Ico 0 p) := by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to ℕ using ha₀
  lift b to ℕ using hb₀
  norm_cast at *
  exact natCast_injOn_Iio _ _ ha hb hab

end AddGroupWithOne
end CharP

namespace CharP

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

variable (R) in
/-- If a ring `R` is of characteristic `p`, then for any prime number `q` different from `p`,
it is not zero in `R`. -/
/-
**CharP.cast_ne_zero_of_ne_of_prime** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：cast_ne_zero_of_ne_of_prime [Nontrivial R] {p q : Nat} [CharP R p] (hq : q
.Prime) (hneq : p != q) : (q : R) != 0
参数：hq : q.Prime；hneq : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用引理 `CharP.false_of_nontrivial_of_char_one`：false_of_nontrivial_of_char_one [
Nontrivial R] [CharP R 1] : False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a ring `R` is of characteristic `p`, then for any prime number `q` different 
from `p`,
it is not zero in `R`.
-/
lemma cast_ne_zero_of_ne_of_prime [Nontrivial R]
    {p q : ℕ} [CharP R p] (hq : q.Prime) (hneq : p ≠ q) : (q : R) ≠ 0 := fun h ↦ by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with rfl | h
  · exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h
/-
**CharP.ringChar_of_prime_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：ringChar_of_prime_eq_zero [Nontrivial R] {p : Nat} (hprime : Nat.Prime p) 
(hp0 : (p : R) = 0) : ringChar R = p
参数：hprime : Nat.Prime p；hp0 : (p : R) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用引理 `ringChar.dvd`：dvd {x : Nat} (hx : (x : R) = 0) : ringChar R ∣ x
· 使用引理 `CharP.ringChar_ne_one`：ringChar_ne_one [Nontrivial R] : ringChar R != 1
-/
lemma ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one
/-
**CharP.charP_iff_prime_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharP`。
形式化陈述：charP_iff_prime_eq_zero [Nontrivial R] {p : Nat} (hp : p.Prime) : CharP R 
p ↔ (p : R) = 0
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用引理 `CharP.ringChar_of_prime_eq_zero`：ringChar_of_prime_eq_zero [Nontrivial R
] {p : Nat} (hprime : Nat.Prime p) (hp0 : (p : R) = 0) : ringChar R = p
-/
lemma charP_iff_prime_eq_zero [Nontrivial R] {p : ℕ} (hp : p.Prime) :
    CharP R p ↔ (p : R) = 0 :=
  ⟨fun _ => cast_eq_zero R p,
   fun hp0 => (ringChar_of_prime_eq_zero hp hp0) ▸ inferInstance⟩

end NonAssocSemiring
end CharP

section

/-- We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`. -/
/-
**Ring.two_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivial R], ringChar R ≠ 
2 → 2 ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `ringChar.spec`：spec : forall x : Nat, (x : R) = 0 ↔ ringChar R ∣ x
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用引理 `CharP.ringChar_ne_one`：ringChar_ne_one [Nontrivial R] : ringChar R != 1

--- 原说明 ---
We have `2 ≠ 0` in a nontrivial ring whose characteristic is not `2`.
-/
protected lemma Ring.two_ne_zero {R : Type*} [NonAssocSemiring R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (2 : R) ≠ 0 := by
  rw [Ne, (by norm_cast : (2 : R) = (2 : ℕ)), ringChar.spec, Nat.dvd_prime Nat.prime_two]
  exact mt (or_iff_left hR).mp CharP.ringChar_ne_one

-- We have `CharP.neg_one_ne_one`, which assumes `[Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)]`.
-- This is a version using `ringChar` instead.
/-- Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`. -/
/-
**Ring.neg_one_ne_one_of_char_ne_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivia
l R] (hR : ringChar R != 2) : (-1 : R) != 1
参数：hR : ringChar R != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.two_ne_zero`：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivi
al R], ringChar R ≠ 2 → 2 ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)

--- 原说明 ---
Characteristic `≠ 2` and nontrivial implies that `-1 ≠ 1`.
-/
lemma Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (-1 : R) ≠ 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)

/-- Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`. -/
/-
**Ring.eq_self_iff_eq_zero_of_char_ne_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nont
rivial R] [NoZeroDivisors R] (hR : ringChar R != 2) {a : R} : -a = a ↔ a = 0
参数：hR : ringChar R != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `Ring.two_ne_zero`：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivi
al R], ringChar R ≠ 2 → 2 ≠ 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Characteristic `≠ 2` in a domain implies that `-a = a` iff `a = 0`.
-/
lemma Ring.eq_self_iff_eq_zero_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    [NoZeroDivisors R] (hR : ringChar R ≠ 2) {a : R} : -a = a ↔ a = 0 :=
  ⟨fun h =>
    (mul_eq_zero.mp <| (two_mul a).trans <| neg_eq_iff_add_eq_zero.mp h).resolve_left
      (Ring.two_ne_zero hR),
    fun h => ((congr_arg (fun x => -x) h).trans neg_zero).trans h.symm⟩

end

section Prod
variable (S : Type*) [AddMonoidWithOne R] [AddMonoidWithOne S] (p q : ℕ) [CharP R p]

/-- The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings. -/
/-
**Nat.lcm.charP** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.lcm.charP [CharP S q] : CharP (R × S) (Nat.lcm p q) where cast_eq_zero
_iff
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.fst_natCast`：fst_natCast (n : Nat) : (n : α × β).fst = n
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Prod.snd_natCast`：snd_natCast (n : Nat) : (n : α × β).snd = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings.
-/
instance Nat.lcm.charP [CharP S q] : CharP (R × S) (Nat.lcm p q) where
  cast_eq_zero_iff := by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

/-- The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings -/
/-
**Prod.charP** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.charP [CharP S p] : CharP (R × S) p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lcm_self`：∀ (m : ℕ), m.lcm m = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings
-/
instance Prod.charP [CharP S p] : CharP (R × S) p := by
  convert! Nat.lcm.charP R S p p; simp
/-
**Prod.charZero_of_left** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.charZero_of_left [CharZero R] : CharZero (R × S) where cast_injective
 _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance Prod.charZero_of_left [CharZero R] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.fst $h)
/-
**Prod.charZero_of_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.charZero_of_right [CharZero S] : CharZero (R × S) where cast_injectiv
e _ _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CharZero.cast_injective`：∀ {R : Type u_1} {inst : AddMonoidWithOne R} [s
elf : CharZero R], Function.Injective Nat.cast
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance Prod.charZero_of_right [CharZero S] : CharZero (R × S) where
  cast_injective _ _ h := CharZero.cast_injective congr(Prod.snd $h)

end Prod

/-
**ULift.charP** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ULift.charP [AddMonoidWithOne R] (p : Nat) [CharP R p] : CharP (ULift R) p
 where cast_eq_zero_iff n
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ULift.ext_iff`：∀ {α : Type u} {x y : ULift.{u_1, u} α}, x = y ↔ x.down =
 y.down
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
instance ULift.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP (ULift R) p where
  cast_eq_zero_iff n := Iff.trans ULift.ext_iff <| CharP.cast_eq_zero_iff R p n
/-
**MulOpposite.charP** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulOpposite.charP [AddMonoidWithOne R] (p : Nat) [CharP R p] : CharP Rᵐᵒᵖ 
p where cast_eq_zero_iff n
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MulOpposite.unop_inj`：unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
-/
instance MulOpposite.charP [AddMonoidWithOne R] (p : ℕ) [CharP R p] : CharP Rᵐᵒᵖ p where
  cast_eq_zero_iff n := MulOpposite.unop_inj.symm.trans <| CharP.cast_eq_zero_iff R p n

section

/-- If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal. -/
/-
**Int.cast_injOn_of_ringChar_ne_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial
 R] (hR : ringChar R != 2) : ({0, 1, -1} : Set Int).InjOn ((↑) : Int -> R)
参数：hR : ringChar R != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Ring.neg_one_ne_one_of_char_ne_two`：Ring.neg_one_ne_one_of_char_ne_two {
R : Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : (-1 : R) != 
1

--- 原说明 ---
If two integers from `{0, 1, -1}` result in equal elements in a ring `R`
that is nontrivial and of characteristic not `2`, then they are equal.
-/
lemma Int.cast_injOn_of_ringChar_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : ({0, 1, -1} : Set ℤ).InjOn ((↑) : ℤ → R) := by
  rintro _ (rfl | rfl | rfl) _ (rfl | rfl | rfl) h <;>
  simp only
    [cast_neg, cast_one, cast_zero, neg_eq_zero, one_ne_zero, zero_ne_one, zero_eq_neg] at h ⊢
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR).symm h).elim
  · exact ((Ring.neg_one_ne_one_of_char_ne_two hR) h).elim

end

namespace CharZero

/-
**CharZero.charZero_iff_forall_prime_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `CharZero
`。
形式化陈述：charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Non
trivial R] : CharZero R ↔ forall p : Nat, p.Prime -> (p : R) != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `CharP.charP_to_charZero`：charP_to_charZero [CharP R 0] : CharZero R
-/
lemma charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  refine ⟨fun h p hp => by simp [hp.ne_zero], fun h => ?_⟩
  let p := ringChar R
  cases CharP.char_is_prime_or_zero R p with
  | inl hp => simpa using h p hp
  | inr h => have : CharP R 0 := h ▸ inferInstance; exact CharP.charP_to_charZero R

end CharZero

namespace Fin

open Fin.NatCast

/-- The characteristic of `F_p` is `p`. -/
@[stacks 09FS "First part. We don't require `p` to be a prime in mathlib."]
/-
**Fin.charP** 是 Mathlib 中的一个实例，位于命名空间 `Fin`。
形式化陈述：charP (n : Nat) [NeZero n] : CharP (Fin n) n where cast_eq_zero_iff _
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.natCast_eq_zero`：∀ {a n : ℕ} [inst : NeZero n], ↑a = 0 ↔ n ∣ a

--- 原说明 ---
The characteristic of `F_p` is `p`.
-/
instance charP (n : ℕ) [NeZero n] : CharP (Fin n) n where cast_eq_zero_iff _ := natCast_eq_zero

end Fin

section AddMonoidWithOne
variable [AddMonoidWithOne R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Type*) [Semiring S] (p) [ExpChar R p] [ExpChar S p] : ExpChar (R × S) p := by
  obtain hp | ⟨hp⟩ := ‹ExpChar R p›
  · constructor
  obtain _ | _ := ‹ExpChar S p›
  · exact (Nat.not_prime_one hp).elim
  · have := Prod.charP R S p; exact .prime hp

end AddMonoidWithOne

section CommRing

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Semiring α] [IsLeftCancelAdd α] (n : ℕ) [CharP α n] :
    Lean.Grind.IsCharP α n where
  ofNat_ext_iff {a b} := by
    rw [Lean.Grind.Semiring.ofNat_eq_natCast, Lean.Grind.Semiring.ofNat_eq_natCast]
    exact CharP.cast_eq_iff_mod_eq α n

end CommRing

