/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Quadratic reciprocity.

## Main results

We prove the law of quadratic reciprocity, see `legendreSym.quadratic_reciprocity` and
`legendreSym.quadratic_reciprocity'`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` and
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

We also prove the supplementary laws that give conditions for when `2` or `-2`
is a square modulo a prime `p`:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2` and
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Implementation notes

The proofs use results for quadratic characters on arbitrary finite fields
from `NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`, which in turn are based on
properties of quadratic Gauss sums as provided by `NumberTheory.LegendreSymbol.GaussSum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/

public section


open Nat

section Values

variable {p : ℕ} [Fact p.Prime]

open ZMod

/-!
### The value of the Legendre symbol at `2` and `-2`

See `jacobiSym.at_two` and `jacobiSym.at_neg_two` for the corresponding statements
for the Jacobi symbol.
-/


namespace legendreSym

/-- `legendreSym p 2` is given by `χ₈ p`. -/
/-
**legendreSym.at_two** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：at_two (hp : p != 2) : legendreSym p 2 = χ₈ p
参数：hp : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `quadraticChar_two`：quadraticChar_two [DecidableEq F] (hF : ringChar F !=
 2) : quadraticChar F 2 = χ₈ (Fintype.card F)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
`legendreSym p 2` is given by `χ₈ p`.
-/
theorem at_two (hp : p ≠ 2) : legendreSym p 2 = χ₈ p := by
  have : (2 : ZMod p) = (2 : ℤ) := by norm_cast
  rw [legendreSym, ← this, quadraticChar_two ((ringChar_zmod_n p).substr hp), card p]

/-- `legendreSym p (-2)` is given by `χ₈' p`. -/
/-
**legendreSym.at_neg_two** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：at_neg_two (hp : p != 2) : legendreSym p (-2) = χ₈' p
参数：hp : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `quadraticChar_neg_two`：quadraticChar_neg_two [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-2) = χ₈' (Fintype.card F)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
`legendreSym p (-2)` is given by `χ₈' p`.
-/
theorem at_neg_two (hp : p ≠ 2) : legendreSym p (-2) = χ₈' p := by
  have : (-2 : ZMod p) = (-2 : ℤ) := by norm_cast
  rw [legendreSym, ← this, quadraticChar_neg_two ((ringChar_zmod_n p).substr hp), card p]

end legendreSym

namespace ZMod

/-- `2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `8`. -/
/-
**ZMod.exists_sq_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：exists_sq_eq_two_iff (hp : p != 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p
 % 8 = 7
参数：hp : p != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.isSquare_two_iff`：FiniteField.isSquare_two_iff : IsSquare (2
 : F) ↔ Fintype.card F % 8 != 3 ∧ Fintype.card F % 8 != 5
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.mod_two_eq_one_iff_ne_two`：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1
 ↔ p ≠ 2)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
`2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `
8`.
-/
theorem exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  rw [FiniteField.isSquare_two_iff, card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

/-- `-2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `3` mod `8`. -/
/-
**ZMod.exists_sq_eq_neg_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：exists_sq_eq_neg_two_iff (hp : p != 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 
1 ∨ p % 8 = 3
参数：hp : p != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.isSquare_neg_two_iff`：FiniteField.isSquare_neg_two_iff : IsS
quare (-2 : F) ↔ Fintype.card F % 8 != 5 ∧ Fintype.card F % 8 != 7
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.mod_two_eq_one_iff_ne_two`：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1
 ↔ p ≠ 2)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
`-2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `3` mod 
`8`.
-/
theorem exists_sq_eq_neg_two_iff (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [FiniteField.isSquare_neg_two_iff, card p]
  have h₁ := (Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  lia

end ZMod

end Values

section Reciprocity

/-!
### The Law of Quadratic Reciprocity

See `jacobiSym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
for the Jacobi symbol.
-/


variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

namespace legendreSym

open ZMod

/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
/-
**legendreSym.quadratic_reciprocity** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：quadratic_reciprocity (hp : p != 2) (hq : q != 2) (hpq : p != q) : legendr
eSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2))
参数：hp : p != 2；hq : q != 2；hpq : p != q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `quadraticChar_odd_prime`：quadraticChar_odd_prime [DecidableEq F] (hF : r
ingChar F != 2) {p : Nat} [Fact p.Prime] (hp₁ : p != 2) (hp₂ : ringChar F != p) 
: quadraticCh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `legendreSym.eq_1`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (a : ℤ), legendr
eSym p a = (quadraticChar (ZMod p)) ↑a
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `mul_rotate'`：mul_rotate' (a b c : G) : a * (b * c) = b * (c * a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `quadraticChar_sq_one`：quadraticChar_sq_one {a : F} (ha : a != 0) : quadr
aticChar F a ^ 2 = 1
· 使用引理 `ZMod.prime_ne_zero`：prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : 
Fact q.Prime] (hpq : p != q) : (q : ZMod p) != 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
**The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, th
en
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`.
-/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by
  have hp₁ := (Prime.eq_two_or_odd <| @Fact.out p.Prime _).resolve_left hp
  have hq₁ := (Prime.eq_two_or_odd <| @Fact.out q.Prime _).resolve_left hq
  have hq₂ : ringChar (ZMod q) ≠ 2 := (ringChar_zmod_n q).substr hq
  have h :=
    quadraticChar_odd_prime ((ringChar_zmod_n p).substr hp) hq ((ringChar_zmod_n p).substr hpq)
  rw [card p] at h
  have nc : ∀ n r : ℕ, ((n : ℤ) : ZMod r) = n := fun n r => by norm_cast
  have nc' : (((-1) ^ (p / 2) : ℤ) : ZMod q) = (-1) ^ (p / 2) := by norm_cast
  rw [legendreSym, legendreSym, nc, nc, h, map_mul, mul_rotate', mul_comm (p / 2), ← pow_two,
    quadraticChar_sq_one (prime_ne_zero q p hpq.symm), mul_one, pow_mul, χ₄_eq_neg_one_pow hp₁, nc',
    map_pow, quadraticChar_neg_one hq₂, card q, χ₄_eq_neg_one_pow hq₁]

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes, then
`(q / p) = (-1)^((p-1)(q-1)/4) * (p / q)`. -/
/-
**legendreSym.quadratic_reciprocity'** 是 Mathlib 中的一个定理，位于命名空间 `legendreSym`。
形式化陈述：quadratic_reciprocity' (hp : p != 2) (hq : q != 2) : legendreSym q p = (-1
) ^ (p / 2 * (q / 2)) * legendreSym p q
参数：hp : p != 2；hq : q != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `legendreSym.eq_zero_iff`：eq_zero_iff (a : Int) : legendreSym p a = 0 ↔ (
a : ZMod p) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `legendreSym.quadratic_reciprocity`：quadratic_reciprocity (hp : p != 2) (
hq : q != 2) (hpq : p != q) : legendreSym q p * legendreSym p q = (-1) ^ (p / 2 
* (q / 2))
· 使用引理 `ZMod.prime_ne_zero`：prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : 
Fact q.Prime] (hpq : p != q) : (q : ZMod p) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `legendreSym.sq_one`：sq_one {a : Int} (ha : (a : ZMod p) != 0) : legendre
Sym p a ^ 2 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
The Law of Quadratic Reciprocity: if `p` and `q` are odd primes, then
`(q / p) = (-1)^((p-1)(q-1)/4) * (p / q)`.
-/
theorem quadratic_reciprocity' (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q := by
  rcases eq_or_ne p q with rfl | h
  · rw [(eq_zero_iff p p).mpr (mod_cast natCast_self p), mul_zero]
  · have qr := congr_arg (· * legendreSym p q) (quadratic_reciprocity hp hq h)
    have : ((q : ℤ) : ZMod p) ≠ 0 := mod_cast prime_ne_zero p q h
    simpa only [mul_assoc, ← pow_two, sq_one p this, mul_one] using qr

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes and `p % 4 = 1`,
then `(q / p) = (p / q)`. -/
/-
**legendreSym.quadratic_reciprocity_one_mod_four** 是 Mathlib 中的一个定理，位于命名空间 `lege
ndreSym`。
形式化陈述：quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q != 2) : legend
reSym q p = legendreSym p q
参数：hp : p % 4 = 1；hq : q != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.quadratic_reciprocity'`：quadratic_reciprocity' (hp : p != 2)
 (hq : q != 2) : legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.mod_two_eq_one_iff_ne_two`：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1
 ↔ p ≠ 2)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.odd_of_mod_four_eq_one`：odd_of_mod_four_eq_one {n : Nat} : n % 4 = 1
 -> n % 2 = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `ZMod.neg_one_pow_div_two_of_one_mod_four`：neg_one_pow_div_two_of_one_mod
_four {n : Nat} (hn : n % 4 = 1) : (-1 : Int) ^ (n / 2) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The Law of Quadratic Reciprocity: if `p` and `q` are odd primes and `p % 4 = 1`,
then `(q / p) = (p / q)`.
-/
theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q := by
  rw [quadratic_reciprocity'
      ((Prime.mod_two_eq_one_iff_ne_two Fact.out).mp (odd_of_mod_four_eq_one hp)) hq,
    pow_mul, neg_one_pow_div_two_of_one_mod_four hp, one_pow, one_mul]

/-- The Law of Quadratic Reciprocity: if `p` and `q` are primes that are both congruent
to `3` mod `4`, then `(q / p) = -(p / q)`. -/
/-
**legendreSym.quadratic_reciprocity_three_mod_four** 是 Mathlib 中的一个定理，位于命名空间 `le
gendreSym`。
形式化陈述：quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) : l
egendreSym q p = -legendreSym p q
参数：hp : p % 4 = 3；hq : q % 4 = 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.neg_one_pow_div_two_of_three_mod_four`：neg_one_pow_div_two_of_three
_mod_four {n : Nat} (hn : n % 4 = 3) : (-1 : Int) ^ (n / 2) = -1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.quadratic_reciprocity'`：quadratic_reciprocity' (hp : p != 2)
 (hq : q != 2) : legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.mod_two_eq_one_iff_ne_two`：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1
 ↔ p ≠ 2)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.odd_of_mod_four_eq_three`：odd_of_mod_four_eq_three {n : Nat} : n % 4
 = 3 -> n % 2 = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a

--- 原说明 ---
The Law of Quadratic Reciprocity: if `p` and `q` are primes that are both congru
ent
to `3` mod `4`, then `(q / p) = -(p / q)`.
-/
theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q := by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity', pow_mul, nop hp, nop hq, neg_one_mul] <;>
  rwa [← Prime.mod_two_eq_one_iff_ne_two Fact.out, odd_of_mod_four_eq_three]

end legendreSym

namespace ZMod

open legendreSym

/-- If `p` and `q` are odd primes and `p % 4 = 1`, then `q` is a square mod `p` iff
`p` is a square mod `q`. -/
/-
**ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod
`。
形式化陈述：exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q != 2)
 : IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q)
参数：hp1 : p % 4 = 1；hq1 : q != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `legendreSym.eq_one_iff'`：eq_one_iff' {a : Nat} (ha0 : (a : ZMod p) != 0)
 : legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
· 使用引理 `ZMod.prime_ne_zero`：prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : 
Fact q.Prime] (hpq : p != q) : (q : ZMod p) != 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `legendreSym.quadratic_reciprocity_one_mod_four`：quadratic_reciprocity_on
e_mod_four (hp : p % 4 = 1) (hq : q != 2) : legendreSym q p = legendreSym p q

--- 原说明 ---
If `p` and `q` are odd primes and `p % 4 = 1`, then `q` is a square mod `p` iff
`p` is a square mod `q`.
-/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
    IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q) := by
  rcases eq_or_ne p q with rfl | h
  · rfl
  · rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
      quadratic_reciprocity_one_mod_four hp1 hq1]

/-- If `p` and `q` are distinct primes that are both congruent to `3` mod `4`, then `q` is
a square mod `p` iff `p` is a nonsquare mod `q`. -/
/-
**ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `ZM
od`。
形式化陈述：exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4
 = 3) (hpq : p != q) : IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q)
参数：hp3 : p % 4 = 3；hq3 : q % 4 = 3；hpq : p != q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `legendreSym.eq_one_iff'`：eq_one_iff' {a : Nat} (ha0 : (a : ZMod p) != 0)
 : legendreSym p a = 1 ↔ IsSquare (a : ZMod p)
· 使用引理 `ZMod.prime_ne_zero`：prime_ne_zero (p q : Nat) [hp : Fact p.Prime] [hq : 
Fact q.Prime] (hpq : p != q) : (q : ZMod p) != 0
· 使用定理 `legendreSym.eq_neg_one_iff'`：eq_neg_one_iff' {a : Nat} : legendreSym p a
 = -1 ↔ ¬IsSquare (a : ZMod p)
· 使用定理 `legendreSym.quadratic_reciprocity_three_mod_four`：quadratic_reciprocity_
three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) : legendreSym q p = -legendreSy
m p q
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `p` and `q` are distinct primes that are both congruent to `3` mod `4`, then 
`q` is
a square mod `p` iff `p` is a nonsquare mod `q`.
-/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    (hpq : p ≠ q) : IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q) := by
  rw [← eq_one_iff' p (prime_ne_zero p q hpq), ← eq_neg_one_iff' q,
    quadratic_reciprocity_three_mod_four hp3 hq3, neg_inj]

end ZMod

end Reciprocity

