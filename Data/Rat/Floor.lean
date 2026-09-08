/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public meta import Mathlib.Algebra.Order.Round

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

@[expose] public section

assert_not_exists Finset

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/--
This variant of `floor_def` uses the `Int.floor` (for any `FloorRing`) rather than `Rat.floor`.
-/
/-
**Rat.floor_def'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {q : ℚ}, ⌊q⌋ = q.num / ↑q.den
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.floor_def`：∀ (a : ℚ), a.floor = a.num / ↑a.den

--- 原说明 ---
This variant of `floor_def` uses the `Int.floor` (for any `FloorRing`) rather th
an `Rat.floor`.
-/
protected theorem floor_def' {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

/--
This variant of `ceil_def` uses the `Int.ceil` (for any `FloorRing`) rather than `Rat.ceil`.
-/
/-
**Rat.ceil_def'** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ (q : ℚ), ⌈q⌉ = -(-q.num / ↑q.den)
参数：q : ℚ；-q.num / ↑q.den。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.floor_def'`：∀ {q : ℚ}, ⌊q⌋ = q.num / ↑q.den
· 使用定理 `Rat.num_neg_eq_neg_num`：num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num
· 使用定理 `Rat.den_neg_eq_den`：den_neg_eq_den (q : Rat) : (-q).den = q.den

--- 原说明 ---
This variant of `ceil_def` uses the `Int.ceil` (for any `FloorRing`) rather than
 `Rat.ceil`.
-/
protected theorem ceil_def' (q : ℚ) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _
  rw [Rat.floor_def', num_neg_eq_neg_num, den_neg_eq_den]


@[norm_cast]
/-
**Rat.floor_intCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：floor_intCast_div_natCast (n : Int) (d : Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑
d : Int)
参数：n : Int；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.floor_def'`：∀ {q : ℚ}, ⌊q⌋ = q.num / ↑q.den
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.ediv_one`：∀ (a : ℤ), a / 1 = a
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.exists_eq_mul_div_num_and_eq_mul_div_den`：exists_eq_mul_div_num_and_
eq_mul_div_den (n : Int) {d : Int} (d_ne_zero : d != 0) : exists c : Int, n = c 
* ((n : Rat) / d).num ∧ (d : Int) …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Int.mul_ediv_mul_of_pos`：∀ {a : ℤ} (b c : ℤ), 0 < a → a * b / (a * c) = 
b / c
· 使用定理 `pos_of_mul_pos_left`：pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a 
* b) (hb : 0 <= b) : 0 < a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
theorem floor_intCast_div_natCast (n : ℤ) (d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / (↑d : ℤ) := by
  rw [Rat.floor_def']
  obtain rfl | hd := eq_zero_or_pos (a := d)
  · simp
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left ?_ <| Int.natCast_nonneg q.den).symm
  rwa [← d_eq_c_mul_denom, Int.natCast_pos]

@[norm_cast]
/-
**Rat.ceil_intCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ceil_intCast_div_natCast (n : Int) (d : Nat) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) 
/ (↑d : Int))
参数：n : Int；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.floor_neg`：floor_neg : ⌊-a⌋ = -⌈a⌉
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Rat.floor_intCast_div_natCast`：floor_intCast_div_natCast (n : Int) (d : 
Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
-/
theorem ceil_intCast_div_natCast (n : ℤ) (d : ℕ) : ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / (↑d : ℤ)) := by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div, ← Int.cast_neg, floor_intCast_div_natCast]

@[norm_cast]
/-
**Rat.floor_natCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：floor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / d
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.floor_intCast_div_natCast`：floor_intCast_div_natCast (n : Int) (d : 
Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
-/
theorem floor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / d :=
  floor_intCast_div_natCast n d

@[norm_cast]
/-
**Rat.ceil_natCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ceil_natCast_div_natCast (n d : Nat) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / d)
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.ceil_intCast_div_natCast`：ceil_intCast_div_natCast (n : Int) (d : Na
t) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int))
-/
theorem ceil_natCast_div_natCast (n d : ℕ) : ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / d) :=
  ceil_intCast_div_natCast n d

@[norm_cast]
/-
**Rat.natFloor_natCast_div_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：natFloor_natCast_div_natCast (n d : Nat) : ⌊(↑n / ↑d : Rat)⌋₊ = n / d
参数：n d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.natCast_floor_eq_floor`：Int.natCast_floor_eq_floor (ha : 0 <= a) : (
⌊a⌋₊ : Int) = ⌊a⌋
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Rat.floor_intCast_div_natCast`：floor_intCast_div_natCast (n : Int) (d : 
Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
-/
theorem natFloor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋₊ = n / d := by
  rw [← Int.ofNat_inj, Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]
/-
**Rat.floor_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.floor_eq_iff`：floor_eq_iff : ⌊a⌋ = z ↔ ↑z <= a ∧ a < z + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]
/-
**Rat.ceil_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：ceil_cast (x : Rat) : ⌈(x : α)⌉ = ⌈x⌉
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `Int.floor_neg`：floor_neg : ⌊-a⌋ = -⌈a⌉
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
-/
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]

@[simp, norm_cast]
/-
**Rat.round_cast** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：round_cast (x : Rat) : round (x : α) = round x
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `round_eq`：round_eq (x : α) : round x = ⌊x + 1 / 2⌋
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
-/
theorem round_cast (x : ℚ) : round (x : α) = round x := by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]

@[simp, norm_cast]
/-
**Rat.cast_fract** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：cast_fract (x : Rat) : (↑(fract x) : α) = fract (x : α)
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

@[simp]
/-
**Rat.den_intFract** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：den_intFract (x : Rat) : (fract x).den = x.den
参数：x : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.sub_intCast_den`：sub_intCast_den (q : Rat) (n : Int) : (q - n).den =
 q.den
-/
theorem den_intFract (x : ℚ) : (fract x).den = x.den :=
  Rat.sub_intCast_den _ _

section NormNum

open Mathlib.Meta.NormNum Qq

/-
**Rat.isNat_intFloor** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [Floor
Ring R] (r : R) (m : Nat) : IsNat r m -> IsNat ⌊r⌋ m
参数：r : R；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_natCast`：floor_natCast (n : Nat) : ⌊(n : R)⌋ = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isInt_intFloor** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isInt_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [Floor
Ring R] (r : R) (m : Int) : IsInt r m -> IsInt ⌊r⌋ m
参数：r : R；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isNat_intFloor_ofIsNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intFloor_ofIsNNRat (r : α) (n : Nat) (d : Nat) : IsNNRat r n d -> Is
Nat ⌊r⌋ (n / d)
参数：r : α；n : Nat；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_ediv_ofNat`：∀ {a b : ℕ}, ↑a / ↑b = ↑(a / b)
· 使用定理 `Rat.floor_natCast_div_natCast`：floor_natCast_div_natCast (n d : Nat) : ⌊
(↑n / ↑d : Rat)⌋ = n / d
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem isNat_intFloor_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌊r⌋ (n / d) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← Int.ofNat_ediv_ofNat, ← floor_natCast_div_natCast n d,
    ← floor_cast (α := α), Rat.cast_div, cast_natCast, cast_natCast]
/-
**Rat.isInt_intFloor_ofIsRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isInt_intFloor_ofIsRat_neg (r : α) (n : Nat) (d : Nat) : IsRat r (.negOfNa
t n) d -> IsInt ⌊r⌋ (.negOfNat (-(-n / d) : Int).toNat)
参数：r : α；n : Nat；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.ceil_intCast_div_natCast`：ceil_intCast_div_natCast (n : Int) (d : Na
t) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int))
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_toNat_eq_self`：∀ {a : ℤ}, ↑a.toNat = a ↔ 0 ≤ a
· 使用定理 `Int.ceil_nonneg`：ceil_nonneg (ha : 0 <= a) : 0 <= ⌈a⌉
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Rat.floor_intCast_div_natCast`：floor_intCast_div_natCast (n : Int) (d : 
Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
· 使用定理 `Rat.floor_cast`：floor_cast (x : Rat) : ⌊(x : α)⌋ = ⌊x⌋
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem isInt_intFloor_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌊r⌋ (.negOfNat (-(-n / d) : ℤ).toNat) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← ceil_intCast_div_natCast n d, Int.cast_natCast]
  rw [@negOfNat_eq (toNat _), ofNat_eq_natCast,
    natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg)),
    ← Int.cast_natCast n, ceil_intCast_div_natCast n d, neg_neg, ← ofNat_eq_natCast, ← negOfNat_eq,
    ← floor_intCast_div_natCast (.negOfNat n) d, ← floor_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast]

/-- `norm_num` extension for `Int.floor` -/
@[norm_num ⌊_⌋]
meta def evalIntFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intFloor $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- floor always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intFloor _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit q.floor.toNat
      letI : $z =Q $n / $d := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intFloor_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-q.floor).toNat
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intFloor_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

/-
**Rat.isNat_intCeil** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorR
ing R] (r : R) (m : Nat) : IsNat r m -> IsNat ⌈r⌉ m
参数：r : R；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉ = n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isInt_intCeil** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isInt_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorR
ing R] (r : R) (m : Int) : IsInt r m -> IsInt ⌈r⌉ m
参数：r : R；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isNat_intCeil_ofIsNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intCeil_ofIsNNRat (r : α) (n : Nat) (d : Nat) : IsNNRat r n d -> IsN
at ⌈r⌉ (-(-n / d) : Int).toNat
参数：r : α；n : Nat；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.ceil_intCast_div_natCast`：ceil_intCast_div_natCast (n : Int) (d : Na
t) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int))
· 使用定理 `Rat.ceil_cast`：ceil_cast (x : Rat) : ⌈(x : α)⌉ = ⌈x⌉
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_toNat_eq_self`：∀ {a : ℤ}, ↑a.toNat = a ↔ 0 ≤ a
· 使用定理 `Int.ceil_nonneg`：ceil_nonneg (ha : 0 <= a) : 0 <= ⌈a⌉
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem isNat_intCeil_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌈r⌉ (-(-n / d) : ℤ).toNat := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← ceil_intCast_div_natCast n d, ← ceil_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast, Int.cast_natCast,
    Int.natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]
/-
**Rat.isInt_intCeil_ofIsRat_neg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isInt_intCeil_ofIsRat_neg (r : α) (n : Nat) (d : Nat) : IsRat r (.negOfNat
 n) d -> IsInt ⌈r⌉ (.negOfNat (n / d))
参数：r : α；n : Nat；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_ediv_ofNat`：∀ {a b : ℕ}, ↑a / ↑b = ↑(a / b)
· 使用定理 `Rat.floor_natCast_div_natCast`：floor_natCast_div_natCast (n d : Nat) : ⌊
(↑n / ↑d : Rat)⌋ = n / d
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Rat.ceil_intCast_div_natCast`：ceil_intCast_div_natCast (n : Int) (d : Na
t) : ⌈(↑n / ↑d : Rat)⌉ = -((-n) / (↑d : Int))
· 使用定理 `Rat.ceil_cast`：ceil_cast (x : Rat) : ⌈(x : α)⌉ = ⌈x⌉
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem isInt_intCeil_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌈r⌉ (.negOfNat (n / d)) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [@negOfNat_eq (n / d), ofNat_eq_natCast, ← ofNat_ediv_ofNat, ← floor_natCast_div_natCast n d,
    floor_natCast_div_natCast n d, ← neg_neg (n : ℤ), ← ofNat_eq_natCast, ← negOfNat_eq,
    ← ceil_intCast_div_natCast (.negOfNat n) d, ← ceil_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast]

/-- `norm_num` extension for `Int.ceil` -/
@[norm_num ⌈_⌉]
meta def evalIntCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intCeil $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- ceil always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit q.ceil.toNat
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intCeil_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-q.ceil).toNat
      letI : $z =Q $n / $d := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intCeil_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

/-
**Rat.isNat_intFract_of_isNat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intFract_of_isNat (r : R) (m : Nat) : IsNat r m -> IsNat (Int.fract 
r) 0
参数：r : R；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract_natCast`：fract_natCast (n : Nat) : fract (n : R) = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_intFract_of_isNat (r : R) (m : ℕ) : IsNat r m → IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isNat_intFract_of_isInt** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_intFract_of_isInt (r : R) (m : Int) : IsInt r m -> IsNat (Int.fract 
r) 0
参数：r : R；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract_intCast`：fract_intCast (z : Int) : fract (z : R) = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_intFract_of_isInt (r : R) (m : ℤ) : IsInt r m → IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isNNRat_intFract_of_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNNRat_intFract_of_isNNRat (r : α) (n d : Nat) : IsNNRat r n d -> IsNNRat
 (Int.fract r) (n % d) d
参数：r : α；n d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Int.fract_div_natCast_eq_div_natCast_mod`：fract_div_natCast_eq_div_natCa
st_mod {m n : Nat} : fract ((m : k) / n) = ↑(m % n) / n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_intFract_of_isNNRat (r : α) (n d : ℕ) :
    IsNNRat r n d → IsNNRat (Int.fract r) (n % d) d := by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_natCast_eq_div_natCast_mod]
/-
**Rat.isRat_intFract_of_isRat_negOfNat** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isRat_intFract_of_isRat_negOfNat (r : α) (n d : Nat) : IsRat r (negOfNat n
) d -> IsRat (Int.fract r) (-n % d) d
参数：r : α；n d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Int.fract_div_intCast_eq_div_intCast_mod`：fract_div_intCast_eq_div_intCa
st_mod {m : Int} {n : Nat} : fract ((m : k) / n) = ↑(m % n) / n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isRat_intFract_of_isRat_negOfNat (r : α) (n d : ℕ) :
    IsRat r (negOfNat n) d → IsRat (Int.fract r) (-n % d) d := by
  rintro ⟨inv, rfl⟩
  refine ⟨inv, ?_⟩
  simp only [invOf_eq_inv, ← div_eq_mul_inv, fract_div_intCast_eq_div_intCast_mod,
    negOfNat_eq, ofNat_eq_natCast]

/-- `norm_num` extension for `Int.fract` -/
@[norm_num (Int.fract _)]
meta def evalIntFract : NormNumExt where eval {u α} e := do
  match e with
  | ~q(@Int.fract _ $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit 0
      letI : $z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isNat $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit 0
      letI : $z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isInt _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(ℕ) := Lean.mkRawNatLit (q.num.natAbs % q.den)
      letI : $n' =Q $n % $d := ⟨⟩
      return .isNNRat _ (q - Rat.floor q) n' d q(isNNRat_intFract_of_isNNRat _ $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(ℤ) := mkRawIntLit (q.num % q.den)
      letI : $n' =Q -$n % $d := ⟨⟩
      return .isRat _ (q - Rat.floor q) n' d q(isRat_intFract_of_isRat_negOfNat _ $n $d $h)
  | _, _, _ => failure

/-!
### `norm_num` extension for `round`
-/

/-
**Rat.isNat_round** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isNat_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [
FloorRing R] (r : R) (m : Nat) : IsNat r m -> IsNat (round r) m
参数：r : R；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `round_natCast`：round_natCast (n : Nat) : round (n : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### `norm_num` extension for `round`
-/
theorem isNat_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) : IsNat r m → IsNat (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.isInt_round** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：isInt_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [
FloorRing R] (r : R) (m : Int) : IsInt r m -> IsInt (round r) m
参数：r : R；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `round_intCast`：round_intCast (n : Int) : round (n : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isInt_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) : IsInt r m → IsInt (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩
/-
**Rat.IsRat.isInt_round** 是 Mathlib 中的一个定理，位于命名空间 `Rat.IsRat`。
形式化陈述：∀ {R : Type u_3} [inst : Field R] [inst_1 : LinearOrder R] [IsStrictOrdere
dRing R] [inst_3 : FloorRing R] (r : R)   (n : ℤ) (d : ℕ) (res : ℤ),   round (↑n
 / ↑d) = res → Mathlib.Meta.NormNum.IsRat r n d → Mathlib.Meta.NormNum.IsInt (ro
und r) res
参数：r : R；n : ℤ；d : ℕ；res : ℤ；↑n / ↑d；round r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.round_cast`：round_cast (x : Rat) : round (x : α) = round x
-/
theorem IsRat.isInt_round {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (r : R) (n : ℤ) (d : ℕ) (res : ℤ) (hres : round (n / d : ℚ) = res) :
    IsRat r n d → IsInt (round r) res := by
  rintro ⟨inv, rfl⟩
  subst res
  constructor
  rw [invOf_eq_inv, ← div_eq_mul_inv]
  norm_cast

/-- local copy tagged `meta` for evaluation of `round` below -/
private meta local instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/-- `norm_num` extension for `round` -/
@[norm_num round _]
meta def evalRound : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@round $α $instRing $instLinearOrder $instFloorRing $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(isNat_round $x _ $pb)
    | .isNegNat sα nb pb => do
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNegNat q(inferInstance) nb q(isInt_round _ _ $pb)
    | .isNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℤ) := mkRawIntLit (round q)
      haveI : $z =Q round (Int.ofNat $n / $d : ℚ) := ⟨⟩
      return .isInt q(inferInstance) z (round q)
        q(IsRat.isInt_round $x $n $d $z rfl (IsNNRat.to_isRat $h))
    | .isNegNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℤ) := mkRawIntLit (round q)
      haveI : $z =Q round ((Int.negOfNat $n) / $d : ℚ) := ⟨⟩
      return .isInt q(inferInstance) z (round q) q(IsRat.isInt_round $x (.negOfNat $n) $d $z rfl $h)
  | _, _, _ => failure

end NormNum

end Rat

/-
**Int.mod_nat_eq_sub_mul_floor_rat_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.mod_nat_eq_sub_mul_floor_rat_div {n : Int} {d : Nat} : n % d = n - d *
 ⌊(n : Rat) / d⌋
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.emod_def`：∀ (a b : ℤ), a % b = a - b * (a / b)
· 使用定理 `Rat.floor_intCast_div_natCast`：floor_intCast_div_natCast (n : Int) (d : 
Nat) : ⌊(↑n / ↑d : Rat)⌋ = n / (↑d : Int)
-/
theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [Int.emod_def, Rat.floor_intCast_div_natCast]
/-
**Nat.coprime_sub_mul_floor_rat_div_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : Nat} (n_coprime_d : n.
Coprime d) : ((n : Int) - d * ⌊(n : Rat) / d⌋).natAbs.Coprime d
参数：n_coprime_d : n.Coprime d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.mod_nat_eq_sub_mul_floor_rat_div`：Int.mod_nat_eq_sub_mul_floor_rat_d
iv {n : Int} {d : Nat} : n % d = n - d * ⌊(n : Rat) / d⌋
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
· 使用定理 `Nat.Coprime.eq_1`：∀ (m n : ℕ), m.Coprime n = (m.gcd n = 1)
-/
theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.Coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.Coprime d := by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

namespace Rat

/-
**Rat.num_lt_succ_floor_mul_den** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：num_lt_succ_floor_mul_den (q : Rat) : q.num < (⌊q⌋ + 1) * q.den
参数：q : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
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
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 64 条，此处仅展示前 30 条）
-/
theorem num_lt_succ_floor_mul_den (q : ℚ) : q.num < (⌊q⌋ + 1) * q.den := by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : ℚ) < (q - fract q + 1) * q.den by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * q.den = q.num + (1 - fract q) * q.den := by
      calc
        (q - fract q + 1) * q.den = (q + (1 - fract q)) * q.den := by ring
        _ = q * q.den + (1 - fract q) * q.den := by rw [add_mul]
        _ = q.num + (1 - fract q) * q.den := by simp
    rwa [this]
  suffices 0 < (1 - fract q) * q.den by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact mod_cast q.pos)
/-
**Rat.fract_inv_num_lt_num_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：fract_inv_num_lt_num_of_pos {q : Rat} (q_pos : 0 < q) : (fract q⁻¹).num < 
q.num
参数：q_pos : 0 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.num_pos`：∀ {a : ℚ}, 0 < a.num ↔ 0 < a
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.inv_def`：∀ (a : ℚ), a⁻¹ = Rat.divInt (↑a.den) a.num
· 使用定理 `Rat.divInt_eq_div`：∀ (a b : ℤ), Rat.divInt a b = ↑a / ↑b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Rat.num_lt_succ_floor_mul_den`：num_lt_succ_floor_mul_den (q : Rat) : q.n
um < (⌊q⌋ + 1) * q.den
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.num_div_eq_of_coprime`：num_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : (a / b : Rat).num = a
· 使用定理 `Rat.den_div_eq_of_coprime`：den_div_eq_of_coprime {a b : Int} (hb0 : 0 < 
b) (h : Nat.Coprime a.natAbs b.natAbs) : ((a / b : Rat).den : Int) = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.coprime_sub_mul_floor_rat_div_of_coprime`：Nat.coprime_sub_mul_floor_
rat_div_of_coprime {n d : Nat} (n_coprime_d : n.Coprime d) : ((n : Int) - d * ⌊(
n : Rat) / d⌋).natAbs.Coprime d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 58 条，此处仅展示前 30 条）
-/
theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num := by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos.mpr q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_inv : ℚ := q.den / q.num with q_inv_def
  have q_inv_eq : q⁻¹ = q_inv := by rw [q_inv_def, inv_def, divInt_eq_div, Int.cast_natCast]
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  suffices ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num by
    simp only [gt_iff_lt, q_inv]
    field_simp
    simp [q_inv, this]
  suffices (q.den : ℤ) - q.num * ⌊q_inv⌋ < q.num by
    -- use that `q.num` and `q.den` are coprime to show that the numerator stays unreduced
    have : ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.den - q.num * ⌊q_inv⌋ := by
      suffices ((q.den : ℤ) - q.num * ⌊q_inv⌋).natAbs.Coprime q.num.natAbs from
        mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.reduced.symm
      simpa only [Nat.cast_natAbs, abs_of_nonneg q_num_pos.le] using! tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.den < q⁻¹.den := by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.den := Rat.num_lt_succ_floor_mul_den q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.den + q⁻¹.den := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.den` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.den ∧ q_inv.den = q.num.natAbs := by
    have coprime_q_denom_q_num : q.den.Coprime q.num.natAbs := q.reduced.symm
    have : Int.natAbs q.den = q.den := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.den : ℚ) / q.num).den : ℤ) = q.num.natAbs by exact mod_cast this
      rw [q_num_abs_eq_q_num]
      exact mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq

end Rat

