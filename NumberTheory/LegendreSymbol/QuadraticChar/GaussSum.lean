/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.GaussSum

/-!
# Quadratic characters of finite fields

Further facts relying on Gauss sums.

-/

public section


/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The value of the quadratic character at `2` -/
/-
**quadraticChar_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_two [DecidableEq F] (hF : ringChar F != 2) : quadraticChar F
 2 = χ₈ (Fintype.card F)
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.IsQuadratic.eq_of_eq_coe`：∀ {R : Type u_1} [inst : CommMonoid R]
 {R' : Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']
   {χ : MulChar R ℤ}, …
· 使用定理 `quadraticChar_isQuadratic`：quadraticChar_isQuadratic : (quadraticChar F)
.IsQuadratic
· 使用定理 `ZMod.isQuadratic_χ₈`：isQuadratic_χ₈ : χ₈.IsQuadratic
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `quadraticChar_eq_pow_of_char_ne_two'`：quadraticChar_eq_pow_of_char_ne_tw
o' (hF : ringChar F != 2) (a : F) : (quadraticChar F a : F) = a ^ (Fintype.card 
F / 2)
· 使用定理 `FiniteField.two_pow_card`：FiniteField.two_pow_card {F : Type*} [Fintype 
F] [Field F] (hF : ringChar F != 2) : (2 : F) ^ (Fintype.card F / 2) = χ₈ (Finty
pe.card F)

--- 原说明 ---
The value of the quadratic character at `2`
-/
theorem quadraticChar_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F 2 = χ₈ (Fintype.card F) :=
  IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))

/-- `2` is a square in `F` iff `#F` is not congruent to `3` or `5` mod `8`. -/
/-
**FiniteField.isSquare_two_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.isSquare_two_iff : IsSquare (2 : F) ↔ Fintype.card F % 8 != 3 
∧ Fintype.card F % 8 != 5
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FiniteField.even_card_of_char_two`：even_card_of_char_two (hF : ringChar 
F = 2) : Fintype.card F % 2 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FiniteField.isSquare_of_char_two`：isSquare_of_char_two (hF : ringChar F 
= 2) (a : F) : IsSquare a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a
· 使用定理 `Ring.two_ne_zero`：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivi
al R], ringChar R ≠ 2 → 2 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `quadraticChar_two`：quadraticChar_two [DecidableEq F] (hF : ringChar F !=
 2) : quadraticChar F 2 = χ₈ (Fintype.card F)
· 使用定理 `ZMod.χ₈_nat_eq_if_mod_eight`：χ₈_nat_eq_if_mod_eight (n : Nat) : χ₈ n = i
f n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1

--- 原说明 ---
`2` is a square in `F` iff `#F` is not congruent to `3` or `5` mod `8`.
-/
theorem FiniteField.isSquare_two_iff :
    IsSquare (2 : F) ↔ Fintype.card F % 8 ≠ 3 ∧ Fintype.card F % 8 ≠ 5 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (Ring.two_ne_zero hF), quadraticChar_two hF,
      χ₈_nat_eq_if_mod_eight]
    lia

/-- The value of the quadratic character at `-2` -/
/-
**quadraticChar_neg_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_neg_two [DecidableEq F] (hF : ringChar F != 2) : quadraticCh
ar F (-2) = χ₈' (Fintype.card F)
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
· 使用定理 `ZMod.χ₈'_eq_χ₄_mul_χ₈`：∀ (a : ZMod 8), ZMod.χ₈' a = ZMod.χ₄ a.cast * ZMo
d.χ₈ a
· 使用定理 `quadraticChar_neg_one`：quadraticChar_neg_one [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-1) = χ₄ (Fintype.card F)
· 使用定理 `quadraticChar_two`：quadraticChar_two [DecidableEq F] (hF : ringChar F !=
 2) : quadraticChar F 2 = χ₈ (Fintype.card F)
· 使用定理 `ZMod.cast_natCast`：cast_natCast (h : m ∣ n) (k : Nat) : (cast (k : ZMod 
n) : R) = k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
The value of the quadratic character at `-2`
-/
theorem quadraticChar_neg_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-2) = χ₈' (Fintype.card F) := by
  rw [(by simp : (-2 : F) = -1 * 2), map_mul, χ₈'_eq_χ₄_mul_χ₈, quadraticChar_neg_one hF,
    quadraticChar_two hF, @cast_natCast _ (ZMod 4) _ _ _ (by decide : 4 ∣ 8)]

/-- `-2` is a square in `F` iff `#F` is not congruent to `5` or `7` mod `8`. -/
/-
**FiniteField.isSquare_neg_two_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.isSquare_neg_two_iff : IsSquare (-2 : F) ↔ Fintype.card F % 8 
!= 5 ∧ Fintype.card F % 8 != 7
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FiniteField.even_card_of_char_two`：even_card_of_char_two (hF : ringChar 
F = 2) : Fintype.card F % 2 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `FiniteField.isSquare_of_char_two`：isSquare_of_char_two (hF : ringChar F 
= 2) (a : F) : IsSquare a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `quadraticChar_one_iff_isSquare`：quadraticChar_one_iff_isSquare {a : F} (
ha : a != 0) : quadraticChar F a = 1 ↔ IsSquare a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Ring.two_ne_zero`：∀ {R : Type u_2} [inst : NonAssocSemiring R] [Nontrivi
al R], ringChar R ≠ 2 → 2 ≠ 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `quadraticChar_neg_two`：quadraticChar_neg_two [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-2) = χ₈' (Fintype.card F)
· 使用定理 `ZMod.χ₈'_nat_eq_if_mod_eight`：∀ (n : ℕ), ZMod.χ₈' ↑n = if n % 2 = 0 then
 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1

--- 原说明 ---
`-2` is a square in `F` iff `#F` is not congruent to `5` or `7` mod `8`.
-/
theorem FiniteField.isSquare_neg_two_iff :
    IsSquare (-2 : F) ↔ Fintype.card F % 8 ≠ 5 ∧ Fintype.card F % 8 ≠ 7 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff]
    lia
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Ring.two_ne_zero hF)),
      quadraticChar_neg_two hF, χ₈'_nat_eq_if_mod_eight]
    lia

/-- The relation between the values of the quadratic character of one field `F` at the
cardinality of another field `F'` and of the quadratic character of `F'` at the cardinality
of `F`. -/
/-
**quadraticChar_card_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_card_card [DecidableEq F] (hF : ringChar F != 2) {F' : Type*
} [Field F'] [Fintype F'] [DecidableEq F'] (hF' : ringChar F' != 2) (h : ringCha
r F' != ringChar F) : quadraticChar F (Fintype.card F') = quadraticChar F' (quad
raticChar F (-1) * Fintype.card F)
参数：hF : ringChar F != 2；hF' : ringChar F' != 2；h : ringChar F' != ringChar F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quadraticChar_exists_neg_one'`：quadraticChar_exists_neg_one' (hF : ringC
har F != 2) : exists a : Fˣ, quadraticChar F a = -1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MulChar.ne_one_iff`：ne_one_iff {χ : MulChar R R'} : χ != 1 ↔ exists a : 
Rˣ, χ a != 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulChar.ringHomComp_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   (χ :
 MulChar R R') …
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `Ring.neg_one_ne_one_of_char_ne_two`：Ring.neg_one_ne_one_of_char_ne_two {
R : Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : (-1 : R) != 
1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Char.card_pow_card`：Char.card_pow_card {F : Type*} [Field F] [Fintype F]
 {F' : Type*} [Field F'] [Fintype F'] {χ : MulChar F F'} (hχ₁ : χ != 1) (hχ₂ : I
sQuadrat…
· 使用定理 `MulChar.IsQuadratic.comp`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   {χ : 
MulChar R R'},…
· 使用定理 `quadraticChar_isQuadratic`：quadraticChar_isQuadratic : (quadraticChar F)
.IsQuadratic
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulChar.IsQuadratic.eq_of_eq_coe`：∀ {R : Type u_1} [inst : CommMonoid R]
 {R' : Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']
   {χ : MulChar R ℤ}, …
· 使用定理 `quadraticChar_eq_pow_of_char_ne_two'`：quadraticChar_eq_pow_of_char_ne_tw
o' (hF : ringChar F != 2) (a : F) : (quadraticChar F a : F) = a ^ (Fintype.card 
F / 2)

--- 原说明 ---
The relation between the values of the quadratic character of one field `F` at t
he
cardinality of another field `F'` and of the quadratic character of `F'` at the 
cardinality
of `F`.
-/
theorem quadraticChar_card_card [DecidableEq F] (hF : ringChar F ≠ 2) {F' : Type*} [Field F']
    [Fintype F'] [DecidableEq F'] (hF' : ringChar F' ≠ 2) (h : ringChar F' ≠ ringChar F) :
    quadraticChar F (Fintype.card F') =
    quadraticChar F' (quadraticChar F (-1) * Fintype.card F) := by
  let χ := (quadraticChar F).ringHomComp (algebraMap ℤ F')
  have hχ₁ : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char_ne_two hF'
  have h := Char.card_pow_card hχ₁ ((quadraticChar_isQuadratic F).comp _) h hF'
  rw [← quadraticChar_eq_pow_of_char_ne_two' hF'] at h
  exact (IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F')
    (quadraticChar_isQuadratic F) hF' h).symm

/-- The value of the quadratic character at an odd prime `p` different from `ringChar F`. -/
/-
**quadraticChar_odd_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F != 2) {p : Nat} [
Fact p.Prime] (hp₁ : p != 2) (hp₂ : ringChar F != p) : quadraticChar F p = quadr
aticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F)
参数：hF : ringChar F != 2；hp₁ : p != 2；hp₂ : ringChar F != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `quadraticChar_neg_one`：quadraticChar_neg_one [DecidableEq F] (hF : ringC
har F != 2) : quadraticChar F (-1) = χ₄ (Fintype.card F)
· 使用定理 `quadraticChar_card_card`：quadraticChar_card_card [DecidableEq F] (hF : r
ingChar F != 2) {F' : Type*} [Field F'] [Fintype F'] [DecidableEq F'] (hF' : rin
gChar F' != 2…
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `ZMod.ringChar_zmod_n`：ringChar_zmod_n (n : Nat) : ringChar (ZMod n) = n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
The value of the quadratic character at an odd prime `p` different from `ringCha
r F`.
-/
theorem quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp₁ : p ≠ 2) (hp₂ : ringChar F ≠ p) :
    quadraticChar F p = quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) := by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h

/-- An odd prime `p` is a square in `F` iff the quadratic character of `ZMod p` does not
take the value `-1` on `χ₄#F * #F`. -/
/-
**FiniteField.isSquare_odd_prime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.isSquare_odd_prime_iff (hF : ringChar F != 2) {p : Nat} [Fact 
p.Prime] (hp : p != 2) : IsSquare (p : F) ↔ quadraticChar (ZMod p) (χ₄ (Fintype.
card F) * Fintype.card F) != -1
参数：hF : ringChar F != 2；hp : p != 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `ZMod.χ₄_apply`：∀ (a : ZMod 4),   ZMod.χ₄ a =     match a with     | 0 =>
 0     | 2 => 0     | 1 => 1     | 3 => -1
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulCharClass.map_nonunit`：∀ {F : Type u_3} {R : outParam (Type u_4)} {R'
 : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZero R'}
 {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `quadraticChar_neg_one_iff_not_isSquare`：quadraticChar_neg_one_iff_not_is
Square {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a
· 使用定理 `quadraticChar_odd_prime`：quadraticChar_odd_prime [DecidableEq F] (hF : r
ingChar F != 2) {p : Nat} [Fact p.Prime] (hp₁ : p != 2) (hp₂ : ringChar F != p) 
: quadraticCh…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An odd prime `p` is a square in `F` iff the quadratic character of `ZMod p` does
 not
take the value `-1` on `χ₄#F * #F`.
-/
theorem FiniteField.isSquare_odd_prime_iff (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) :
    IsSquare (p : F) ↔ quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) ≠ -1 := by
  classical
  rcases eq_or_ne (ringChar F) p with rfl | hFp
  · obtain ⟨q, hq, hq'⟩ := FiniteField.card F (ringChar F)
    simp [hq']
  · rwa [← Iff.not_left quadraticChar_neg_one_iff_not_isSquare, quadraticChar_odd_prime hF hp]

end SpecialValues

