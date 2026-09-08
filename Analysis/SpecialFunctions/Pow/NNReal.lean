/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Tactic.Rify
public import Qq

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

@[expose] public section

noncomputable section

open Real NNReal ENNReal ComplexConjugate Finset Function Set

namespace NNReal
variable {x : ℝ≥0} {w y z : ℝ}

/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
/-
**NNReal.rpow** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：rpow (x : Real>=0) (y : Real) : Real>=0
参数：x : Real>=0；y : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ` as 
the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log 
x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`.
-/
noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg x.2 y⟩
/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

@[simp]
/-
**NNReal.rpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_pow (x : Real>=0) (y : Real) : rpow x y = x ^ y
参数：x : Real>=0；y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp, norm_cast]
/-
**NNReal.coe_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) : Real) = (x : Real
) ^ y
参数：x : Real>=0；y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl

@[simp]
/-
**NNReal.rpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
-/
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  NNReal.eq <| Real.rpow_zero _
/-
**NNReal.rpow_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_zero_pos (x : Real>=0) : 0 < x ^ (0 : Real)
参数：x : Real>=0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem rpow_zero_pos (x : ℝ≥0) : 0 < x ^ (0 : ℝ) := by rw [rpow_zero]; exact one_pos

@[simp]
/-
**NNReal.rpow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_zero_iff {x : Real>=0} {y : Real} : x ^ y = 0 ↔ x = 0 ∧ y != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_rpow`：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) 
: Real) = (x : Real) ^ y
· 使用定理 `NNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `Real.rpow_eq_zero_iff_of_nonneg`：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x
) : x ^ y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_eq_zero_iff {x : ℝ≥0} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  rw [← NNReal.coe_inj, coe_rpow, ← NNReal.coe_eq_zero]
  exact Real.rpow_eq_zero_iff_of_nonneg x.2
/-
**NNReal.rpow_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_zero (hy : y != 0) : x ^ y = 0 ↔ x = 0
参数：hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rpow_eq_zero (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by simp [hy]

@[simp]
/-
**NNReal.zero_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x = 0
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
-/
theorem zero_rpow {x : ℝ} (h : x ≠ 0) : (0 : ℝ≥0) ^ x = 0 :=
  NNReal.eq <| Real.zero_rpow h
/-
**NNReal.zero_rpow_def** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：zero_rpow_def (y : Real) : (0 : Real>=0) ^ y = if y = 0 then 1 else 0
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0) ^ y = if y = 0 then 1 else 0 := by
  split_ifs with h <;> simp [h]

@[simp]
/-
**NNReal.rpow_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
-/
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  NNReal.eq <| Real.rpow_one _
/-
**NNReal.rpow_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻¹
参数：x : Real>=0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.rpow_neg x.2 _

@[simp, norm_cast]
/-
**NNReal.rpow_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Real) = x ^ n
参数：x : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
lemma rpow_natCast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  NNReal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]
/-
**NNReal.rpow_intCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Real) = x ^ n
参数：x : Real>=0；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma rpow_intCast (x : ℝ≥0) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]
/-
**NNReal.one_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
-/
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  NNReal.eq <| Real.one_rpow _
/-
**NNReal.rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add {x : Real>=0} (hx : x != 0) (y z : Real) : x ^ (y + z) = x ^ y * 
x ^ z
参数：hx : x != 0；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem rpow_add {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) _ _
/-
**NNReal.rpow_add'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z) = x ^ y * x ^ z
参数：h : y + z != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_add'`：rpow_add' (hx : 0 <= x) (h : y + z != 0) : x ^ (y + z) =
 x ^ y * x ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_add' (h : y + z ≠ 0) (x : ℝ≥0) : x ^ (y + z) = x ^ y * x ^ z :=
  NNReal.eq <| Real.rpow_add' x.2 h
/-
**NNReal.rpow_add_intCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_intCast (hx : x != 0) (y : Real) (n : Int) : x ^ (y + n) = x ^ y 
* x ^ n
参数：hx : x != 0；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_add_intCast`：rpow_add_intCast {x : Real} (hx : x != 0) (y : Re
al) (n : Int) : x ^ (y + n) = x ^ y * x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma rpow_add_intCast (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _
/-
**NNReal.rpow_add_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_natCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y + n) = x ^ y 
* x ^ n
参数：hx : x != 0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_add_natCast`：rpow_add_natCast {x : Real} (hx : x != 0) (y : Re
al) (n : Nat) : x ^ (y + n) = x ^ y * x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma rpow_add_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _
/-
**NNReal.rpow_sub_intCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_intCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y - n) = x ^ y 
/ x ^ n
参数：hx : x != 0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_sub_intCast`：rpow_sub_intCast {x : Real} (hx : x != 0) (y : Re
al) (n : Int) : x ^ (y - n) = x ^ y / x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma rpow_sub_intCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _
/-
**NNReal.rpow_sub_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_natCast (hx : x != 0) (y : Real) (n : Nat) : x ^ (y - n) = x ^ y 
/ x ^ n
参数：hx : x != 0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_sub_natCast`：rpow_sub_natCast {x : Real} (hx : x != 0) (y : Re
al) (n : Nat) : x ^ (y - n) = x ^ y / x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma rpow_sub_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _
/-
**NNReal.rpow_add_intCast'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_intCast' {n : Int} (h : y + n != 0) (x : Real>=0) : x ^ (y + n) =
 x ^ y * x ^ n
参数：h : y + n != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_add_intCast'`：rpow_add_intCast' (hx : 0 <= x) {n : Int} (h : y
 + n != 0) : x ^ (y + n) = x ^ y * x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_add_intCast' {n : ℤ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h
/-
**NNReal.rpow_add_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_natCast' {n : Nat} (h : y + n != 0) (x : Real>=0) : x ^ (y + n) =
 x ^ y * x ^ n
参数：h : y + n != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_add_natCast'`：rpow_add_natCast' (hx : 0 <= x) (h : y + n != 0)
 : x ^ (y + n) = x ^ y * x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_add_natCast' {n : ℕ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h
/-
**NNReal.rpow_sub_intCast'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_intCast' {n : Int} (h : y - n != 0) (x : Real>=0) : x ^ (y - n) =
 x ^ y / x ^ n
参数：h : y - n != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_sub_intCast'`：rpow_sub_intCast' (hx : 0 <= x) {n : Int} (h : y
 - n != 0) : x ^ (y - n) = x ^ y / x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_sub_intCast' {n : ℤ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h
/-
**NNReal.rpow_sub_natCast'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_natCast' {n : Nat} (h : y - n != 0) (x : Real>=0) : x ^ (y - n) =
 x ^ y / x ^ n
参数：h : y - n != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `Real.rpow_sub_natCast'`：rpow_sub_natCast' (hx : 0 <= x) (h : y - n != 0)
 : x ^ (y - n) = x ^ y / x ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_sub_natCast' {n : ℕ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h
/-
**NNReal.rpow_add_one** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_one (hx : x != 0) (y : Real) : x ^ (y + 1) = x ^ y * x
参数：hx : x != 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `NNReal.rpow_add_natCast`：rpow_add_natCast (hx : x != 0) (y : Real) (n : 
Nat) : x ^ (y + n) = x ^ y * x ^ n
-/
lemma rpow_add_one (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1
/-
**NNReal.rpow_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_one (hx : x != 0) (y : Real) : x ^ (y - 1) = x ^ y / x
参数：hx : x != 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `NNReal.rpow_sub_natCast`：rpow_sub_natCast (hx : x != 0) (y : Real) (n : 
Nat) : x ^ (y - n) = x ^ y / x ^ n
-/
lemma rpow_sub_one (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1
/-
**NNReal.rpow_add_one'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_one' (h : y + 1 != 0) (x : Real>=0) : x ^ (y + 1) = x ^ y * x
参数：h : y + 1 != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_add'`：rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z)
 = x ^ y * x ^ z
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
lemma rpow_add_one' (h : y + 1 ≠ 0) (x : ℝ≥0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' h, rpow_one]
/-
**NNReal.rpow_one_add'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_one_add' (h : 1 + y != 0) (x : Real>=0) : x ^ (1 + y) = x * x ^ y
参数：h : 1 + y != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_add'`：rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z)
 = x ^ y * x ^ z
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
lemma rpow_one_add' (h : 1 + y ≠ 0) (x : ℝ≥0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' h, rpow_one]
/-
**NNReal.rpow_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_add_of_nonneg (x : Real>=0) {y z : Real} (hy : 0 <= y) (hz : 0 <= z) 
: x ^ (y + z) = x ^ y * x ^ z
参数：x : Real>=0；hy : 0 <= y；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_add_of_nonneg`：rpow_add_of_nonneg (hx : 0 <= x) (hy : 0 <= y) 
(hz : 0 <= z) : x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

/-- Variant of `NNReal.rpow_add'` that avoids having to prove `y + z = w` twice. -/
/-
**NNReal.rpow_of_add_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_of_add_eq (x : Real>=0) (hw : w != 0) (h : y + z = w) : x ^ w = x ^ y
 * x ^ z
参数：x : Real>=0；hw : w != 0；h : y + z = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_add'`：rpow_add' (h : y + z != 0) (x : Real>=0) : x ^ (y + z)
 = x ^ y * x ^ z

--- 原说明 ---
Variant of `NNReal.rpow_add'` that avoids having to prove `y + z = w` twice.
-/
lemma rpow_of_add_eq (x : ℝ≥0) (hw : w ≠ 0) (h : y + z = w) : x ^ w = x ^ y * x ^ z := by
  rw [← h, rpow_add']; rwa [h]
/-
**NNReal.rpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x ^ y) ^ z
参数：x : Real>=0；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  NNReal.eq <| Real.rpow_mul x.2 y z
/-
**NNReal.rpow_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_natCast_mul (x : Real>=0) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ n
) ^ z
参数：x : Real>=0；n : Nat；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
lemma rpow_natCast_mul (x : ℝ≥0) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]
/-
**NNReal.rpow_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_mul_natCast (x : Real>=0) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ y
) ^ n
参数：x : Real>=0；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
lemma rpow_mul_natCast (x : ℝ≥0) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]
/-
**NNReal.rpow_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_intCast_mul (x : Real>=0) (n : Int) (z : Real) : x ^ (n * z) = (x ^ n
) ^ z
参数：x : Real>=0；n : Int；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `NNReal.rpow_intCast`：rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Rea
l) = x ^ n
-/
lemma rpow_intCast_mul (x : ℝ≥0) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]
/-
**NNReal.rpow_mul_intCast** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_mul_intCast (x : Real>=0) (y : Real) (n : Int) : x ^ (y * n) = (x ^ y
) ^ n
参数：x : Real>=0；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `NNReal.rpow_intCast`：rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Rea
l) = x ^ n
-/
lemma rpow_mul_intCast (x : ℝ≥0) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]
/-
**NNReal.rpow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_neg_one (x : Real>=0) : x ^ (-1 : Real) = x⁻¹
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
/-
**NNReal.rpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub {x : Real>=0} (hx : x != 0) (y z : Real) : x ^ (y - z) = x ^ y / 
x ^ z
参数：hx : x != 0；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_sub`：rpow_sub {x : Real} (hx : 0 < x) (y z : Real) : x ^ (y - 
z) = x ^ y / x ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem rpow_sub {x : ℝ≥0} (hx : x ≠ 0) (y z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hx) y z
/-
**NNReal.rpow_sub'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z) = x ^ y / x ^ z
参数：h : y - z != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.rpow_sub'`：rpow_sub' {x : Real} (hx : 0 <= x) {y z : Real} (h : y -
 z != 0) : x ^ (y - z) = x ^ y / x ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_sub' (h : y - z ≠ 0) (x : ℝ≥0) : x ^ (y - z) = x ^ y / x ^ z :=
  NNReal.eq <| Real.rpow_sub' x.2 h
/-
**NNReal.rpow_sub_one'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_sub_one' (h : y - 1 != 0) (x : Real>=0) : x ^ (y - 1) = x ^ y / x
参数：h : y - 1 != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_sub'`：rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z)
 = x ^ y / x ^ z
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
lemma rpow_sub_one' (h : y - 1 ≠ 0) (x : ℝ≥0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' h, rpow_one]
/-
**NNReal.rpow_one_sub'** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_one_sub' (h : 1 - y != 0) (x : Real>=0) : x ^ (1 - y) = x / x ^ y
参数：h : 1 - y != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_sub'`：rpow_sub' (h : y - z != 0) (x : Real>=0) : x ^ (y - z)
 = x ^ y / x ^ z
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
lemma rpow_one_sub' (h : 1 - y ≠ 0) (x : ℝ≥0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' h, rpow_one]
/-
**NNReal.rpow_inv_rpow_self** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_rpow_self {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ y) ^ (1 /
 y) = x
参数：hy : y != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
（共 31 条，此处仅展示前 30 条）
-/
theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ (1 / y) = x := by
  rw [← rpow_mul]
  field_simp
  simp
/-
**NNReal.rpow_self_rpow_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_self_rpow_inv {y : Real} (hy : y != 0) (x : Real>=0) : (x ^ (1 / y)) 
^ y = x
参数：hy : y != 0；x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_of_pow_eq_zero`：eval_cons_of_pow_e
q_zero [CommGroupWithZero M] {r : Int} (hr : r = 0) {x : M} (hx : x != 0) (l : N
F M) : ((r, x) ::ᵣ l).eval = NF.eval l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
（共 31 条，此处仅展示前 30 条）
-/
theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ (1 / y)) ^ y = x := by
  rw [← rpow_mul]
  field_simp
  simp
/-
**NNReal.inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：inv_rpow (x : Real>=0) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
参数：x : Real>=0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.inv_rpow`：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.inv_rpow x.2 y
/-
**NNReal.div_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^ z / y ^ z
参数：x y : Real>=0；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.div_rpow`：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y)
 ^ z = x ^ z / y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  NNReal.eq <| Real.div_rpow x.2 y.2 z
/-
**NNReal.sqrt_eq_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 : Real))
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
-/
theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

@[simp]
/-
**NNReal.rpow_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] : x ^ (ofNat(n) : Real) 
= x ^ (OfNat.ofNat n : Nat)
参数：x : Real>=0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
lemma rpow_ofNat (x : ℝ≥0) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (OfNat.ofNat n : ℕ) :=
  rpow_natCast x n
/-
**NNReal.rpow_two** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_two (x : Real>=0) : x ^ (2 : Real) = x ^ 2
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] : x
 ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n : Nat)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
/-
**NNReal.mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^ z * y ^ z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  NNReal.eq <| Real.mul_rpow x.2 y.2

/-- `rpow` as a `MonoidHom` -/
@[simps]
/-
**NNReal.rpowMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：rpowMonoidHom (r : Real) : Real>=0 ->* Real>=0 where toFun
参数：r : Real。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z

--- 原说明 ---
`rpow` as a `MonoidHom`
-/
def rpowMonoidHom (r : ℝ) : ℝ≥0 →* ℝ≥0 where
  toFun := (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

/-- `rpow` variant of `List.prod_map_pow` for `ℝ≥0` -/
/-
**NNReal.list_prod_map_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：list_prod_map_rpow (l : List Real>=0) (r : Real) : (l.map (· ^ r)).prod = 
l.prod ^ r
参数：l : List Real>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.prod_hom`：prod_hom (l : List M) {F : Type*} [FunLike F M N] [Monoid
HomClass F M N] (f : F) : (l.map f).prod = f l.prod

--- 原说明 ---
`rpow` variant of `List.prod_map_pow` for `ℝ≥0`
-/
theorem list_prod_map_rpow (l : List ℝ≥0) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r :=
  l.prod_hom (rpowMonoidHom r)
/-
**NNReal.list_prod_map_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：list_prod_map_rpow' {ι} (l : List ι) (f : ι -> Real>=0) (r : Real) : (l.ma
p (f · ^ r)).prod = (l.map f).prod ^ r
参数：l : List ι；f : ι -> Real>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.list_prod_map_rpow`：list_prod_map_rpow (l : List Real>=0) (r : Re
al) : (l.map (· ^ r)).prod = l.prod ^ r
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ≥0) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← list_prod_map_rpow, List.map_map]; rfl

/-- `rpow` version of `Multiset.prod_map_pow` for `ℝ≥0`. -/
/-
**NNReal.multiset_prod_map_rpow** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι -> Real>=0) (r : Real) 
: (s.map (f · ^ r)).prod = (s.map f).prod ^ r
参数：s : Multiset ι；f : ι -> Real>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_hom'`：prod_hom' (s : Multiset ι) {F : Type*} [FunLike F M 
N] [MonoidHomClass F M N] (f : F) (g : ι -> M) : (s.map fun i => f <| g i).prod 
= f (s.m…

--- 原说明 ---
`rpow` version of `Multiset.prod_map_pow` for `ℝ≥0`.
-/
lemma multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r :=
  s.prod_hom' (rpowMonoidHom r) _

/-- `rpow` version of `Finset.prod_pow` for `ℝ≥0`. -/
/-
**NNReal.finsetProd_rpow** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：finsetProd_rpow {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real) : (∏ i in
 s, f i ^ r) = (∏ i in s, f i) ^ r
参数：s : Finset ι；f : ι -> Real>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.multiset_prod_map_rpow`：multiset_prod_map_rpow {ι} (s : Multiset 
ι) (f : ι -> Real>=0) (r : Real) : (s.map (f · ^ r)).prod = (s.map f).prod ^ r

--- 原说明 ---
`rpow` version of `Finset.prod_pow` for `ℝ≥0`.
-/
lemma finsetProd_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
  multiset_prod_map_rpow _ _ _

@[deprecated (since := "2026-04-08")] alias finset_prod_rpow := finsetProd_rpow

-- note: these don't really belong here, but they're much easier to prove in terms of the above

section Real

/-- `rpow` version of `List.prod_map_pow` for `Real`. -/
/-
**NNReal._root_.Real.list_prod_map_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rpow` version of `List.prod_map_pow` for `Real`.
-/
theorem _root_.Real.list_prod_map_rpow (l : List ℝ) (hl : ∀ x ∈ l, (0 : ℝ) ≤ x) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r := by
  lift l to List ℝ≥0 using hl
  have := congr_arg ((↑) : ℝ≥0 → ℝ) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this
/-
**NNReal._root_.Real.list_prod_map_rpow'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ)
    (hl : ∀ i ∈ l, (0 : ℝ) ≤ f i) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← Real.list_prod_map_rpow (l.map f) _ r, List.map_map]
  · rfl
  simpa using hl

/-- `rpow` version of `Multiset.prod_map_pow`. -/
/-
**NNReal._root_.Real.multiset_prod_map_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rpow` version of `Multiset.prod_map_pow`.
-/
theorem _root_.Real.multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ)
    (hs : ∀ i ∈ s, (0 : ℝ) ≤ f i) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r := by
  obtain ⟨l⟩ := s
  simpa using Real.list_prod_map_rpow' l f hs r

/-- `rpow` version of `Finset.prod_pow`. -/
/-
**NNReal._root_.Real.finsetProd_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rpow` version of `Finset.prod_pow`.
-/
theorem _root_.Real.finsetProd_rpow
    {ι} (s : Finset ι) (f : ι → ℝ) (hs : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
  Real.multiset_prod_map_rpow s.val f hs r

@[deprecated (since := "2026-04-08")] alias _root_.Real.finset_prod_rpow := Real.finsetProd_rpow

end Real

/-
**NNReal.rpow_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂
/-
**NNReal.rpow_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x y : NNReal} {z : ℝ}, x < y → 0 < z → x ^ z < y ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂
/-
**NNReal.rpow_lt_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_rpow_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z < y ^ z ↔
 x < y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_rpow_iff`：rpow_lt_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z < y ^ z ↔ x < y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz
/-
**NNReal.rpow_le_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z <= y ^ z 
↔ x <= y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz
/-
**NNReal.le_rpow_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x
 ^ z <= y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz
 : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_self_rpow_inv`：rpow_self_rpow_inv {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ (1 / y)) ^ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']
/-
**NNReal.rpow_inv_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x
 <= y ^ z
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz
 : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_self_rpow_inv`：rpow_self_rpow_inv {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ (1 / y)) ^ y = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_inv_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']
/-
**NNReal.lt_rpow_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：lt_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x 
^ z < y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  simp only [← not_le, rpow_inv_le_iff hz]
/-
**NNReal.rpow_inv_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_lt_iff {x y : Real>=0} {z : Real} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x 
< y ^ z
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rpow_inv_lt_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

section
variable {y : ℝ≥0}

/-
**NNReal.rpow_lt_rpow_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ 
z
参数：hx : 0 < x；hxy : x < y；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_lt_rpow_of_neg`：rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y)
 (hz : z < 0) : y ^ z < x ^ z
-/
lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z :=
  Real.rpow_lt_rpow_of_neg hx hxy hz
/-
**NNReal.rpow_le_rpow_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x <= y) (hz : z <= 0) : y ^ z <
= x ^ z
参数：hx : 0 < x；hxy : x <= y；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
-/
lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z :=
  Real.rpow_le_rpow_of_nonpos hx hxy hz
/-
**NNReal.rpow_lt_rpow_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y
 ^ z ↔ y < x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_lt_rpow_iff_of_neg`：rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x
-/
lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  Real.rpow_lt_rpow_iff_of_neg hx hy hz
/-
**NNReal.rpow_le_rpow_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z <= 
y ^ z ↔ y <= x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_le_rpow_iff_of_neg`：rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy :
 0 < y) (hz : z < 0) : x ^ z <= y ^ z ↔ y <= x
-/
lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  Real.rpow_le_rpow_iff_of_neg hx hy hz
/-
**NNReal.le_rpow_inv_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：le_rpow_inv_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x <= y ^
 z⁻¹ ↔ x ^ z <= y
参数：hy : 0 <= y；hz : 0 < z；x : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.le_rpow_inv_iff_of_pos`：le_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma le_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y :=
  Real.le_rpow_inv_iff_of_pos x.2 hy hz
/-
**NNReal.rpow_inv_le_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_le_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x ^ z⁻¹ 
<= y ↔ x <= y ^ z
参数：hy : 0 <= y；hz : 0 < z；x : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_inv_le_iff_of_pos`：rpow_inv_le_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_inv_le_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z :=
  Real.rpow_inv_le_iff_of_pos x.2 hy hz
/-
**NNReal.lt_rpow_inv_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：lt_rpow_inv_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x < y ^ 
z⁻¹ ↔ x ^ z < y
参数：hy : 0 <= y；hz : 0 < z；x : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.lt_rpow_inv_iff_of_pos`：lt_rpow_inv_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma lt_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  Real.lt_rpow_inv_iff_of_pos x.2 hy hz
/-
**NNReal.rpow_inv_lt_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_lt_iff_of_pos (hy : 0 <= y) (hz : 0 < z) (x : Real>=0) : x ^ z⁻¹ 
< y ↔ x < y ^ z
参数：hy : 0 <= y；hz : 0 < z；x : Real>=0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.rpow_inv_lt_iff_of_pos`：rpow_inv_lt_iff_of_pos (hx : 0 <= x) (hy : 
0 <= y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rpow_inv_lt_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  Real.rpow_inv_lt_iff_of_pos x.2 hy hz
/-
**NNReal.le_rpow_inv_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x <= y ^ z
⁻¹ ↔ y <= x ^ z
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_rpow_inv_iff_of_neg`：le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0
 < y) (hz : z < 0) : x <= y ^ z⁻¹ ↔ y <= x ^ z
-/
lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  Real.le_rpow_inv_iff_of_neg hx hy hz
/-
**NNReal.lt_rpow_inv_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻
¹ ↔ y < x ^ z
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.lt_rpow_inv_iff_of_neg`：lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0
 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z
-/
lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  Real.lt_rpow_inv_iff_of_neg hx hy hz
/-
**NNReal.rpow_inv_lt_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < 
y ↔ y ^ z < x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_inv_lt_iff_of_neg`：rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0
 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x
-/
lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  Real.rpow_inv_lt_iff_of_neg hx hy hz
/-
**NNReal.rpow_inv_le_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ <=
 y ↔ y ^ z <= x
参数：hx : 0 < x；hy : 0 < y；hz : z < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_inv_le_iff_of_neg`：rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0
 < y) (hz : z < 0) : x ^ z⁻¹ <= y ↔ y ^ z <= x
-/
lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  Real.rpow_inv_le_iff_of_neg hx hy hz

end

/-
**NNReal.rpow_lt_rpow_of_exponent_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal} {y z : ℝ}, 1 < x → y < z → x ^ y < x ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_rpow_of_exponent_lt`：rpow_lt_rpow_of_exponent_lt (hx : 1 < 
x) (hyz : y < z) : x ^ y < x ^ z
-/
@[gcongr] theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz
/-
**NNReal.rpow_le_rpow_of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {x : NNReal} {y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz
/-
**NNReal.rpow_lt_rpow_of_exponent_gt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_rpow_of_exponent_gt {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 
: x < 1) (hyz : z < y) : x ^ y < x ^ z
参数：hx0 : 0 < x；hx1 : x < 1；hyz : z < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt (hx0 : 0 <
 x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
-/
theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz
/-
**NNReal.rpow_le_rpow_of_exponent_ge** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_rpow_of_exponent_ge {x : Real>=0} {y z : Real} (hx0 : 0 < x) (hx1 
: x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
参数：hx0 : 0 < x；hx1 : x <= 1；hyz : z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
-/
theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz
/-
**NNReal.rpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_pos {p : Real} {x : Real>=0} (hx_pos : 0 < x) : 0 < x ^ p
参数：hx_pos : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.rpow_lt_rpow`：∀ {x y : NNReal} {z : ℝ}, x < y → 0 < z → x ^ z < y
 ^ z
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x ^ p := by
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : ℝ) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)
/-
**NNReal.rpow_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_one {x : Real>=0} {z : Real} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 
1
参数：hx1 : x < 1；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_one`：rpow_lt_one {x z : Real} (hx1 : 0 <= x) (hx2 : x < 1) 
(hz : 0 < z) : x ^ z < 1
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz
/-
**NNReal.rpow_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_one {x : Real>=0} {z : Real} (hx2 : x <= 1) (hz : 0 <= z) : x ^ z 
<= 1
参数：hx2 : x <= 1；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_one`：rpow_le_one {x z : Real} (hx1 : 0 <= x) (hx2 : x <= 1)
 (hz : 0 <= z) : x ^ z <= 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz
/-
**NNReal.rpow_lt_one_of_one_lt_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_lt_one_of_one_lt_of_neg {x : Real>=0} {z : Real} (hx : 1 < x) (hz : z
 < 0) : x ^ z < 1
参数：hx : 1 < x；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_lt_one_of_one_lt_of_neg`：rpow_lt_one_of_one_lt_of_neg {x z : R
eal} (hx : 1 < x) (hz : z < 0) : x ^ z < 1
-/
theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz
/-
**NNReal.rpow_le_one_of_one_le_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_one_of_one_le_of_nonpos {x : Real>=0} {z : Real} (hx : 1 <= x) (hz
 : z <= 0) : x ^ z <= 1
参数：hx : 1 <= x；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_le_one_of_one_le_of_nonpos`：rpow_le_one_of_one_le_of_nonpos {x
 z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1
-/
theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz
/-
**NNReal.one_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：one_lt_rpow {x : Real>=0} {z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z
参数：hx : 1 < x；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.one_lt_rpow`：one_lt_rpow {x z : Real} (hx : 1 < x) (hz : 0 < z) : 1
 < x ^ z
-/
theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz
/-
**NNReal.one_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：one_le_rpow {x : Real>=0} {z : Real} (h : 1 <= x) (h₁ : 0 <= z) : 1 <= x ^
 z
参数：h : 1 <= x；h₁ : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.one_le_rpow`：one_le_rpow {x z : Real} (hx : 1 <= x) (hz : 0 <= z) :
 1 <= x ^ z
-/
theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁
/-
**NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：one_lt_rpow_of_pos_of_lt_one_of_neg {x : Real>=0} {z : Real} (hx1 : 0 < x)
 (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z
参数：hx1 : 0 < x；hx2 : x < 1；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.one_lt_rpow_of_pos_of_lt_one_of_neg`：one_lt_rpow_of_pos_of_lt_one_o
f_neg (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz
/-
**NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `NNRea
l`。
形式化陈述：one_le_rpow_of_pos_of_le_one_of_nonpos {x : Real>=0} {z : Real} (hx1 : 0 <
 x) (hx2 : x <= 1) (hz : z <= 0) : 1 <= x ^ z
参数：hx1 : 0 < x；hx2 : x <= 1；hz : z <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.one_le_rpow_of_pos_of_le_one_of_nonpos`：one_le_rpow_of_pos_of_le_on
e_of_nonpos (hx1 : 0 < x) (hx2 : x <= 1) (hz : z <= 0) : 1 <= x ^ z
-/
theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz
/-
**NNReal.rpow_le_self_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_le_self_of_le_one {x : Real>=0} {z : Real} (hx : x <= 1) (h_one_le : 
1 <= z) : x ^ z <= x
参数：hx : x <= 1；h_one_le : 1 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_or_bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Order
Bot α] (a : α), a = ⊥ ∨ ⊥ < a
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 48 条，此处仅展示前 30 条）
-/
theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le
/-
**NNReal.rpow_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_left_injective {x : Real} (hx : x != 0) : Function.Injective fun y : 
Real>=0 => y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_inv_rpow_self`：rpow_inv_rpow_self {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ y) ^ (1 / y) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Function.Injective fun y : ℝ≥0 => y ^ x :=
  fun y z hyz => by simpa only [rpow_inv_rpow_self hx] using congr_arg (fun y => y ^ (1 / x)) hyz
/-
**NNReal.rpow_eq_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_rpow_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x ^ z = y ^ z 
↔ x = y
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NNReal.rpow_left_injective`：rpow_left_injective {x : Real} (hx : x != 0)
 : Function.Injective fun y : Real>=0 => y ^ x
-/
theorem rpow_eq_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y :=
  (rpow_left_injective hz).eq_iff
/-
**NNReal.rpow_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_left_surjective {x : Real} (hx : x != 0) : Function.Surjective fun y 
: Real>=0 => y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0 => y ^ x :=
  fun y => ⟨y ^ x⁻¹, by simp_rw [← rpow_mul, inv_mul_cancel₀ hx, rpow_one]⟩
/-
**NNReal.rpow_left_bijective** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_left_bijective {x : Real} (hx : x != 0) : Function.Bijective fun y : 
Real>=0 => y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.rpow_left_injective`：rpow_left_injective {x : Real} (hx : x != 0)
 : Function.Injective fun y : Real>=0 => y ^ x
· 使用定理 `NNReal.rpow_left_surjective`：rpow_left_surjective {x : Real} (hx : x != 
0) : Function.Surjective fun y : Real>=0 => y ^ x
-/
theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0 => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
/-
**NNReal.rpow_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_right_inj {y z : Real} (hx₀ : x != 0) (hx₁ : x != 1) : x ^ y = x ^ z 
↔ y = z
参数：hx₀ : x != 0；hx₁ : x != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma rpow_right_inj {y z : ℝ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  rw [← pos_iff_ne_zero] at hx₀
  rify at *
  grind [Real.rpow_right_inj]
/-
**NNReal.rpow_eq_rpow_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_rpow_right_iff {y z : Real} : x ^ y = x ^ z ↔ y = z ∨ x = 1 ∨ (x =
 0 ∧ (y = 0 ↔ z = 0))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.zero_rpow_def`：zero_rpow_def (y : Real) : (0 : Real>=0) ^ y = if 
y = 0 then 1 else 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `NNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `NNReal.rpow_right_inj`：rpow_right_inj {y z : Real} (hx₀ : x != 0) (hx₁ :
 x != 1) : x ^ y = x ^ z ↔ y = z
-/
lemma rpow_eq_rpow_right_iff {y z : ℝ} :
    x ^ y = x ^ z ↔ y = z ∨ x = 1 ∨ (x = 0 ∧ (y = 0 ↔ z = 0)) := by
  obtain rfl | hx₀ := eq_or_ne x 0
  · obtain rfl | hz := eq_or_ne z 0
    · simp [zero_rpow_def]
    · simp +contextual [hz]
  obtain rfl | hx₁ := eq_or_ne x 1
  · simp
  simpa [hx₀, hx₁] using rpow_right_inj (y := y) (z := z) hx₀ hx₁

@[simp]
/-
**NNReal.rpow_eq_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_eq_left_iff {y : Real} : x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y != 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用引理 `NNReal.rpow_eq_rpow_right_iff`：rpow_eq_rpow_right_iff {y z : Real} : x ^
 y = x ^ z ↔ y = z ∨ x = 1 ∨ (x = 0 ∧ (y = 0 ↔ z = 0))
-/
lemma rpow_eq_left_iff {y : ℝ} : x ^ y = x ↔ x = 1 ∨ y = 1 ∨ (x = 0 ∧ y ≠ 0) := by
  simpa [or_left_comm] using rpow_eq_rpow_right_iff (x := x) (y := y) (z := 1)
/-
**NNReal.eq_rpow_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：eq_rpow_inv_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x = y ^ z⁻¹ ↔ x
 ^ z = y
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_eq_rpow_iff`：rpow_eq_rpow_iff {x y : Real>=0} {z : Real} (hz
 : z != 0) : x ^ z = y ^ z ↔ x = y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_self_rpow_inv`：rpow_self_rpow_inv {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ (1 / y)) ^ y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x = y ^ z⁻¹ ↔ x ^ z = y := by
  rw [← rpow_eq_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz]
/-
**NNReal.rpow_inv_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_eq_iff {x y : Real>=0} {z : Real} (hz : z != 0) : x ^ z⁻¹ = y ↔ x
 = y ^ z
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_eq_rpow_iff`：rpow_eq_rpow_iff {x y : Real>=0} {z : Real} (hz
 : z != 0) : x ^ z = y ^ z ↔ x = y
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_self_rpow_inv`：rpow_self_rpow_inv {y : Real} (hy : y != 0) (
x : Real>=0) : (x ^ (1 / y)) ^ y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_inv_eq_iff {x y : ℝ≥0} {z : ℝ} (hz : z ≠ 0) : x ^ z⁻¹ = y ↔ x = y ^ z := by
  rw [← rpow_eq_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz]
/-
**NNReal.rpow_rpow_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {y : ℝ}, y ≠ 0 → ∀ (x : NNReal), (x ^ y) ^ y⁻¹ = x
参数：x : NNReal；x ^ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul, mul_inv_cancel₀ hy, rpow_one]
/-
**NNReal.rpow_inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {y : ℝ}, y ≠ 0 → ∀ (x : NNReal), (x ^ y⁻¹) ^ y = x
参数：x : NNReal；x ^ y⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_inv_rpow {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul, inv_mul_cancel₀ hy, rpow_one]

@[simp]
/-
**NNReal.rpow_rpow_inv_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_rpow_inv_eq_iff {y : Real} : (x ^ y) ^ y⁻¹ = x ↔ y != 0 ∨ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rpow_rpow_inv_eq_iff {y : ℝ} : (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1 := by
  grind only [rpow_rpow_inv, rpow_zero]

@[simp]
/-
**NNReal.rpow_inv_rpow_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_rpow_eq_iff {y : Real} : (x ^ y⁻¹) ^ y = x ↔ y != 0 ∨ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rpow_inv_rpow_eq_iff {y : ℝ} : (x ^ y⁻¹) ^ y = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]
/-
**NNReal.pow_rpow_inv_natCast** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：pow_rpow_inv_natCast (x : Real>=0) {n : Nat} (hn : n != 0) : (x ^ n) ^ (n⁻
¹ : Real) = x
参数：x : Real>=0；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_rpow`：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) 
: Real) = (x : Real) ^ y
· 使用定理 `NNReal.coe_pow`：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : R
eal) = (r : Real) ^ n
· 使用定理 `Real.pow_rpow_inv_natCast`：pow_rpow_inv_natCast (hx : 0 <= x) (hn : n !=
 0) : (x ^ n) ^ (n⁻¹ : Real) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem pow_rpow_inv_natCast (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← NNReal.coe_inj, coe_rpow, NNReal.coe_pow]
  exact Real.pow_rpow_inv_natCast x.2 hn
/-
**NNReal.rpow_inv_natCast_pow** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：rpow_inv_natCast_pow (x : Real>=0) {n : Nat} (hn : n != 0) : (x ^ (n⁻¹ : R
eal)) ^ n = x
参数：x : Real>=0；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_pow`：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : R
eal) = (r : Real) ^ n
· 使用定理 `NNReal.coe_rpow`：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) 
: Real) = (x : Real) ^ y
· 使用定理 `Real.rpow_inv_natCast_pow`：rpow_inv_natCast_pow (hx : 0 <= x) (hn : n !=
 0) : (x ^ (n⁻¹ : Real)) ^ n = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rpow_inv_natCast_pow (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← NNReal.coe_inj, NNReal.coe_pow, coe_rpow]
  exact Real.rpow_inv_natCast_pow x.2 hn
/-
**NNReal._root_.Real.toNNReal_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y := by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow, Real.toNNReal_coe]
/-
**NNReal.strictMono_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：strictMono_rpow_of_pos {z : Real} (h : 0 < z) : StrictMono fun x : Real>=0
 => x ^ z
参数：h : 0 < z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.rpow_lt_rpow`：∀ {x y : NNReal} {z : ℝ}, x < y → 0 < z → x ^ z < y
 ^ z
-/
theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0 => x ^ z :=
  fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h]
/-
**NNReal.monotone_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：monotone_rpow_of_nonneg {z : Real} (h : 0 <= z) : Monotone fun x : Real>=0
 => x ^ z
参数：h : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `NNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0 
< z) : StrictMono fun x : Real>=0 => x ^ z
-/
theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0 => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0 => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0 => x ^ (1 / y)`. -/
@[simps! apply]
/-
**NNReal.orderIsoRpow** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：orderIsoRpow (y : Real) (hy : 0 < y) : Real>=0 ≃o Real>=0
参数：y : Real；hy : 0 < y。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0 
< z) : StrictMono fun x : Real>=0 => x ^ z

--- 原说明 ---
Bundles `fun x : ℝ≥0 => x ^ y` into an order isomorphism when `y : ℝ` is positiv
e,
where the inverse is `fun x : ℝ≥0 => x ^ (1 / y)`.
-/
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0 ≃o ℝ≥0 :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]
/-
**NNReal.orderIsoRpow_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：orderIsoRpow_symm_eq (y : Real) (hy : 0 < y) : (orderIsoRpow y hy).symm = 
orderIsoRpow (1 / y) (one_div_pos.2 hy)
参数：y : Real；hy : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0 
< z) : StrictMono fun x : Real>=0 => x ^ z
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div_one_div`：one_div_one_div : 1 / (1 / a) = a
· 使用定理 `StrictMono.orderIsoOfRightInverse.congr_simp`：∀ {α : Type u_2} {β : Type
 u_3} [inst : LinearOrder α] [inst_1 : Preorder β] (f f_1 : α → β) (e_f : f = f_
1)   (h_mono : StrictMono f) (g g_…
-/
theorem orderIsoRpow_symm_eq (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]; rfl
/-
**NNReal._root_.Real.nnnorm_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.nnnorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

end NNReal

namespace ENNReal

/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
/-
**ENNReal.rpow** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ENNReal → ℝ → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real power function `x^y` on extended nonnegative reals, defined for `x : ℝ≥
0∞` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with t
he natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x <
 0`, and
`⊤ ^ x = 1 / 0 ^ x`).
-/
noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

@[simp]
/-
**ENNReal.rpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_pow (x : Real>=0∞) (y : Real) : rpow x y = x ^ y
参数：x : Real>=0∞；y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp]
/-
**ENNReal.rpow_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
-/
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [← none_eq_top]
/-
**ENNReal.rpow_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_zero_pos (x : Real>=0∞) : 0 < x ^ (0 : Real)
参数：x : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem rpow_zero_pos (x : ℝ≥0∞) : 0 < x ^ (0 : ℝ) := by rw [rpow_zero]; exact one_pos
/-
**ENNReal.top_rpow_def** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_rpow_def (y : Real) : (⊤ : Real>=0∞) ^ y = if 0 < y then ⊤ else if y =
 0 then 1 else 0
参数：y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl

@[simp]
/-
**ENNReal.top_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : Real>=0∞) ^ y = ⊤
参数：h : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]

@[simp]
/-
**ENNReal.top_rpow_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : Real>=0∞) ^ y = 0
参数：h : y < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]
/-
**ENNReal.zero_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 : Real>=0∞) ^ y = 0
参数：h : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.some_eq_coe`：∀ (a : NNReal), some a = ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [asymm h, ne_of_gt h]

@[simp]
/-
**ENNReal.zero_rpow_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 : Real>=0∞) ^ y = ⊤
参数：h : y < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.some_eq_coe`：∀ (a : NNReal), some a = ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h]
/-
**ENNReal.zero_rpow_def** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zero_rpow_def (y : Real) : (0 : Real>=0∞) ^ y = if 0 < y then 0 else if y 
= 0 then 1 else ⊤
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
-/
theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ := by
  rcases lt_trichotomy (0 : ℝ) y with (H | rfl | H)
  · simp [H, zero_rpow_of_pos]
  · simp
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]
/-
**ENNReal.zero_rpow_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：zero_rpow_mul_self (y : Real) : (0 : Real>=0∞) ^ y * (0 : Real>=0∞) ^ y = 
(0 : Real>=0∞) ^ y
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_def`：zero_rpow_def (y : Real) : (0 : Real>=0∞) ^ y = i
f 0 < y then 0 else if y = 0 then 1 else ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.top_mul_top`：top_mul_top : ∞ * ∞ = ∞
-/
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * (0 : ℝ≥0∞) ^ y = (0 : ℝ≥0∞) ^ y := by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

@[norm_cast]
/-
**ENNReal.coe_rpow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_rpow_of_ne_zero {x : Real>=0} (h : x != 0) (y : Real) : (↑(x ^ y) : Re
al>=0∞) = x ^ y
参数：h : x != 0；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.some_eq_coe`：∀ (a : NNReal), some a = ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_rpow_of_ne_zero {x : ℝ≥0} (h : x ≠ 0) (y : ℝ) : (↑(x ^ y) : ℝ≥0∞) = x ^ y := by
  rw [← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), Pow.pow, rpow]
  simp [h]

@[norm_cast]
/-
**ENNReal.coe_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_rpow_of_nonneg (x : Real>=0) {y : Real} (h : 0 <= y) : ↑(x ^ y) = (x :
 Real>=0∞) ^ y
参数：x : Real>=0；h : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
-/
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : ↑(x ^ y) = (x : ℝ≥0∞) ^ y := by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _
/-
**ENNReal.coe_rpow_def** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_rpow_def (x : Real>=0) (y : Real) : (x : Real>=0∞) ^ y = if x = 0 ∧ y 
< 0 then ⊤ else ↑(x ^ y)
参数：x : Real>=0；y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else ↑(x ^ y) :=
  rfl
/-
**ENNReal.rpow_ofNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_ofNNReal {M : Real>=0} {P : Real} (hP : 0 <= P) : (M : Real>=0∞) ^ P 
= ↑(M ^ P)
参数：hP : 0 <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_eq_pow`：rpow_eq_pow (x : Real>=0∞) (y : Real) : rpow x y = 
x ^ y
-/
theorem rpow_ofNNReal {M : ℝ≥0} {P : ℝ} (hP : 0 ≤ P) : (M : ℝ≥0∞) ^ P = ↑(M ^ P) := by
  rw [ENNReal.coe_rpow_of_nonneg _ hP, ← ENNReal.rpow_eq_pow]

@[simp]
/-
**ENNReal.rpow_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_gt

@[simp]
/-
**ENNReal.one_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_one`：↑1 = 1
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 := by
  rw [← coe_one, ← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]
/-
**ENNReal.rpow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_zero_iff {x : Real>=0∞} {y : Real} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x
 = ⊤ ∧ y < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]
/-
**ENNReal.rpow_eq_zero_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_zero_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y = 0
 ↔ x = 0
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rpow_eq_zero_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = 0 ↔ x = 0 := by
  simp [hy, hy.not_gt]

@[simp]
/-
**ENNReal.rpow_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_top_iff {x : Real>=0∞} {y : Real} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x 
= ⊤ ∧ 0 < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]
/-
**ENNReal.rpow_eq_top_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_top_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y = ⊤ 
↔ x = ⊤
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]
/-
**ENNReal.rpow_lt_top_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_top_iff_of_pos {x : Real>=0∞} {y : Real} (hy : 0 < y) : x ^ y < ∞ 
↔ x < ∞
参数：hy : 0 < y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_eq_top_iff_of_pos`：rpow_eq_top_iff_of_pos {x : Real>=0∞} {y
 : Real} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rpow_lt_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y < ∞ ↔ x < ∞ := by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]
/-
**ENNReal.rpow_eq_top_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_eq_top_of_nonneg (x : Real>=0∞) {y : Real} (hy0 : 0 <= y) : x ^ y = ⊤
 -> x = ⊤
参数：x : Real>=0∞；hy0 : 0 <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ := by
  simp +contextual [ENNReal.rpow_eq_top_iff, hy0.not_gt]

-- This is an unsafe rule since we want to try `rpow_ne_top_of_ne_zero` if `y < 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**ENNReal.rpow_ne_top_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_ne_top_of_nonneg {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤
) : x ^ y != ⊤
参数：hy0 : 0 <= y；h : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ENNReal.rpow_eq_top_of_nonneg`：rpow_eq_top_of_nonneg (x : Real>=0∞) {y :
 Real} (hy0 : 0 <= y) : x ^ y = ⊤ -> x = ⊤
-/
theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg'` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**ENNReal.rpow_ne_top_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_ne_top_of_nonneg' {y : Real} {x : Real>=0∞} (hx : 0 < x) (hx' : x != 
⊤) : x ^ y != ⊤
参数：hx : 0 < x；hx' : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem rpow_ne_top_of_nonneg' {y : ℝ} {x : ℝ≥0∞} (hx : 0 < x) (hx' : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  fun h ↦ by simp [rpow_eq_top_iff, hx.ne', hx'] at h
/-
**ENNReal.rpow_lt_top_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_top_of_nonneg {x : Real>=0∞} {y : Real} (hy0 : 0 <= y) (h : x != ⊤
) : x ^ y < ⊤
参数：hy0 : 0 <= y；h : x != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg`：rpow_ne_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y != ⊤
-/
theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

-- This is an unsafe rule since we want to try `rpow_ne_top_of_nonneg` if `x = 0`.
@[aesop (rule_sets := [finiteness]) unsafe apply]
/-
**ENNReal.rpow_ne_top_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_ne_top_of_ne_zero {x : Real>=0∞} {y : Real} (hx : x != 0) (hx' : x !=
 ⊤) : x ^ y != ⊤
参数：hx : x != 0；hx' : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem rpow_ne_top_of_ne_zero {x : ℝ≥0∞} {y : ℝ} (hx : x ≠ 0) (hx' : x ≠ ⊤) : x ^ y ≠ ⊤ := by
  simp [rpow_eq_top_iff, hx, hx']
/-
**ENNReal.rpow_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤) : x ^ (y
 + z) = x ^ y * x ^ z
参数：y z : Real；hx : x != 0；h'x : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `NNReal.rpow_add`：rpow_add {x : Real>=0} (hx : x != 0) (y z : Real) : x ^
 (y + z) = x ^ y * x ^ z
-/
theorem rpow_add {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z := by
  cases x with
  | top => exact (h'x rfl).elim
  | coe x =>
    have : x ≠ 0 := fun h => by simp [h] at hx
    simp [← coe_rpow_of_ne_zero this, NNReal.rpow_add this]
/-
**ENNReal.rpow_add_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_of_nonneg {x : Real>=0∞} (y z : Real) (hy : 0 <= y) (hz : 0 <= z)
 : x ^ (y + z) = x ^ y * x ^ z
参数：y z : Real；hy : 0 <= y；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `NNReal.rpow_add_of_nonneg`：rpow_add_of_nonneg (x : Real>=0) {y z : Real}
 (hy : 0 <= y) (hz : 0 <= z) : x ^ (y + z) = x ^ y * x ^ z
-/
theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl | hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl | hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]
/-
**ENNReal.rpow_add_of_add_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_add_of_add_pos {x : Real>=0∞} (hx : x != ⊤) (y z : Real) (hyz : 0 < y
 + z) : x ^ (y + z) = x ^ y * x ^ z
参数：hx : x != ⊤；y z : Real；hyz : 0 < y + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 41 条，此处仅展示前 30 条）
-/
lemma rpow_add_of_add_pos {x : ℝ≥0∞} (hx : x ≠ ⊤) (y z : ℝ) (hyz : 0 < y + z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  obtain (rfl | hx') := eq_or_ne x 0
  · by_cases hy' : 0 < y
    · simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hy']
    · have hz' : 0 < z := by linarith
      simp [ENNReal.zero_rpow_of_pos hyz, ENNReal.zero_rpow_of_pos hz']
  · rw [ENNReal.rpow_add _ _ hx' hx]
/-
**ENNReal.rpow_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y)⁻¹
参数：x : Real>=0∞；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
-/
theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]
/-
**ENNReal.rpow_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_sub {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'x : x != ⊤) : x ^ (y
 - z) = x ^ y / x ^ z
参数：y z : Real；hx : x != 0；h'x : x != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ENNReal.rpow_add`：rpow_add {x : Real>=0∞} (y z : Real) (hx : x != 0) (h'
x : x != ⊤) : x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem rpow_sub {x : ℝ≥0∞} (y z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, rpow_add _ _ hx h'x, rpow_neg, div_eq_mul_inv]
/-
**ENNReal.rpow_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_neg_one (x : Real>=0∞) : x ^ (-1 : Real) = x⁻¹
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]
/-
**ENNReal.rpow_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (x ^ y) ^ z
参数：x : Real>=0∞；y z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）
-/
theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  cases x with
  | top =>
    rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  | coe x =>
    by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero, h, this, NNReal.rpow_mul]

@[simp, norm_cast]
/-
**ENNReal.rpow_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : Real) = x ^ n
参数：x : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.top_pow`：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
theorem rpow_natCast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_ne_zero _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

@[simp]
/-
**ENNReal.rpow_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_ofNat (x : Real>=0∞) (n : Nat) [n.AtLeastTwo] : x ^ (ofNat(n) : Real)
 = x ^ (OfNat.ofNat n)
参数：x : Real>=0∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
-/
lemma rpow_ofNat (x : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℝ) = x ^ (OfNat.ofNat n) :=
  rpow_natCast x n

@[simp, norm_cast]
/-
**ENNReal.rpow_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_intCast (x : Real>=0∞) (n : Int) : x ^ (n : Real) = x ^ n
参数：x : Real>=0∞；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma rpow_intCast (x : ℝ≥0∞) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_natCast, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]
/-
**ENNReal.rpow_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_two (x : Real>=0∞) : x ^ (2 : Real) = x ^ 2
参数：x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0∞) (n : Nat) [n.AtLeastTwo] :
 x ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2
/-
**ENNReal.mul_rpow_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_rpow_eq_ite (x y : Real>=0∞) (z : Real) : (x * y) ^ z = if (x = 0 ∧ y 
= ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z
参数：x y : Real>=0∞；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
（共 47 条，此处仅展示前 30 条）
-/
theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_gt
  wlog hxy : x ≤ y
  · convert! this y x z hz (le_of_not_ge hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> rcases hz with hz | hz <;> simp [*, hz.not_gt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x
  · rcases hz with hz | hz <;> simp [hz, top_unique hxy]
  induction y
  · rw [ne_eq, coe_eq_zero] at hx0
    rcases hz with hz | hz <;> simp [*]
  simp only [*]
  norm_cast at *
  rw [← coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_rpow]
  norm_cast
/-
**ENNReal.mul_rpow_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_rpow_of_ne_top {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) (z : Real)
 : (x * y) ^ z = x ^ z * y ^ z
参数：hx : x != ⊤；hy : y != ⊤；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_rpow_eq_ite`：mul_rpow_eq_ite (x y : Real>=0∞) (z : Real) : (
x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ 
z
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

@[norm_cast]
/-
**ENNReal.coe_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_mul_rpow (x y : Real>=0) (z : Real) : ((x : Real>=0∞) * y) ^ z = (x : 
Real>=0∞) ^ z * (y : Real>=0∞) ^ z
参数：x y : Real>=0；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_rpow_of_ne_top`：mul_rpow_of_ne_top {x y : Real>=0∞} (hx : x 
!= ⊤) (hy : y != ⊤) (z : Real) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = (x : ℝ≥0∞) ^ z * (y : ℝ≥0∞) ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z
/-
**ENNReal.prod_coe_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：prod_coe_rpow {ι} (s : Finset ι) (f : ι -> Real>=0) (r : Real) : ∏ i in s,
 (f i : Real>=0∞) ^ r = ((∏ i in s, f i : Real>=0) : Real>=0∞) ^ r
参数：s : Finset ι；f : ι -> Real>=0；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i ∈ s, (f i : ℝ≥0∞) ^ r = ((∏ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]
/-
**ENNReal.mul_rpow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_rpow_of_ne_zero {x y : Real>=0∞} (hx : x != 0) (hy : y != 0) (z : Real
) : (x * y) ^ z = x ^ z * y ^ z
参数：hx : x != 0；hy : y != 0；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_rpow_eq_ite`：mul_rpow_eq_ite (x y : Real>=0∞) (z : Real) : (
x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ 
z
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]
/-
**ENNReal.mul_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Real} (hz : 0 <= z) : (x * y) ^ z
 = x ^ z * y ^ z
参数：x y : Real>=0∞；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_rpow_eq_ite`：mul_rpow_eq_ite (x y : Real>=0∞) (z : Real) : (
x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ 
z
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_gt, mul_rpow_eq_ite]
/-
**ENNReal.prod_rpow_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι -> Real>=0∞} (hf : forall i 
in s, f i != ∞) (r : Real) : ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r
参数：hf : forall i in s, f i != ∞；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_rpow_of_ne_top`：mul_rpow_of_ne_top {x y : Real>=0∞} (hx : x 
!= ⊤) (hy : y != ⊤) (z : Real) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `ENNReal.prod_ne_top`：prod_ne_top (h : forall a in s, f a != ∞) : ∏ a in 
s, f a != ∞
-/
theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_ne_top h2f
/-
**ENNReal.prod_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι -> Real>=0∞} {r : Real} (hr 
: 0 <= r) : ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
-/
theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]
/-
**ENNReal.inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：inv_rpow (x : Real>=0∞) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
参数：x : Real>=0∞；y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.eq_inv_of_mul_eq_one_left`：∀ {a b : ENNReal}, a * b = 1 → a = b⁻
¹
· 使用定理 `ENNReal.mul_rpow_of_ne_zero`：mul_rpow_of_ne_zero {x y : Real>=0∞} (hx : 
x != 0) (hy : y != 0) (z : Real) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_zero`：∀ {a : ENNReal}, a⁻¹ ≠ 0 ↔ a ≠ ⊤
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `ENNReal.one_rpow`：one_rpow (x : Real) : (1 : Real>=0∞) ^ x = 1
-/
theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_gt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_rpow]
/-
**ENNReal.div_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：div_rpow_of_nonneg (x y : Real>=0∞) {z : Real} (hz : 0 <= z) : (x / y) ^ z
 = x ^ z / y ^ z
参数：x y : Real>=0∞；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用定理 `ENNReal.inv_rpow`：inv_rpow (x : Real>=0∞) (y : Real) : x⁻¹ ^ y = (x ^ y)
⁻¹
-/
theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]
/-
**ENNReal.strictMono_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：strictMono_rpow_of_pos {z : Real} (h : 0 < z) : StrictMono fun x : Real>=0
∞ => x ^ z
参数：h : 0 < z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_lt_rpow`：∀ {x y : NNReal} {z : ℝ}, x < y → 0 < z → x ^ z < y
 ^ z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z := by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]
/-
**ENNReal.monotone_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：monotone_rpow_of_nonneg {z : Real} (h : 0 <= z) : Monotone fun x : Real>=0
∞ => x ^ z
参数：h : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
-/
theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

/-- Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positive,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`. -/
@[simps! apply]
/-
**ENNReal.orderIsoRpow** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：orderIsoRpow (y : Real) (hy : 0 < y) : Real>=0∞ ≃o Real>=0∞
参数：y : Real；hy : 0 < y。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z

--- 原说明 ---
Bundles `fun x : ℝ≥0∞ => x ^ y` into an order isomorphism when `y : ℝ` is positi
ve,
where the inverse is `fun x : ℝ≥0∞ => x ^ (1 / y)`.
-/
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]
/-
**ENNReal.orderIsoRpow_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：orderIsoRpow_symm_apply (y : Real) (hy : 0 < y) : (orderIsoRpow y hy).symm
 = orderIsoRpow (1 / y) (one_div_pos.2 hy)
参数：y : Real；hy : 0 < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div_one_div`：one_div_one_div : 1 / (1 / a) = a
· 使用定理 `StrictMono.orderIsoOfRightInverse.congr_simp`：∀ {α : Type u_2} {β : Type
 u_3} [inst : LinearOrder α] [inst_1 : Preorder β] (f f_1 : α → β) (e_f : f = f_
1)   (h_mono : StrictMono f) (g g_…
-/
theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]
  rfl
/-
**ENNReal.rpow_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.monotone_rpow_of_nonneg`：monotone_rpow_of_nonneg {z : Real} (h :
 0 <= z) : Monotone fun x : Real>=0∞ => x ^ z
-/
@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁
/-
**ENNReal.rpow_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x y : ENNReal} {z : ℝ}, x < y → 0 < z → x ^ z < y ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
-/
@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁
/-
**ENNReal.rpow_le_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z <= y ^ z
 ↔ x <= y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
-/
theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le
/-
**ENNReal.rpow_lt_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_rpow_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z < y ^ z 
↔ x < y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
-/
theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt
/-
**ENNReal.max_rpow** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：max_rpow {x y : Real>=0∞} {p : Real} (hp : 0 <= p) : max x y ^ p = max (x 
^ p) (y ^ p)
参数：hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
lemma max_rpow {x y : ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) : max x y ^ p = max (x ^ p) (y ^ p) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, max_eq_right (rpow_le_rpow hxy hp)]
  · rw [max_eq_left hxy, max_eq_left (rpow_le_rpow hxy hp)]
/-
**ENNReal.le_rpow_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x <= y ^ z⁻¹ ↔ 
x ^ z <= y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul, @rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]
/-
**ENNReal.rpow_inv_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_inv_lt_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x
 < y ^ z
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rpow_inv_lt_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]
/-
**ENNReal.lt_rpow_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x
 ^ z < y
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_lt_rpow_iff`：rpow_lt_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z < y ^ z ↔ x < y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, @rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]
/-
**ENNReal.rpow_inv_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_inv_le_iff {x y : Real>=0∞} {z : Real} (hz : 0 < z) : x ^ z⁻¹ <= y ↔ 
x <= y ^ z
参数：hz : 0 < z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0∞} {z : Real} (
hz : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rpow_inv_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

@[gcongr]
/-
**ENNReal.rpow_lt_rpow_of_exponent_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_rpow_of_exponent_lt {x : Real>=0∞} {y z : Real} (hx : 1 < x) (hx' 
: x != ⊤) (hyz : y < z) : x ^ y < x ^ z
参数：hx : 1 < x；hx' : x != ⊤；hyz : y < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ENNReal.one_lt_coe_iff`：one_lt_coe_iff : 1 < (↑p : Real>=0∞) ↔ 1 < p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_lt_rpow_of_exponent_lt`：∀ {x : NNReal} {y z : ℝ}, 1 < x → y 
< z → x ^ y < x ^ z
-/
theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (lt_trans zero_lt_one hx).ne',
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]
/-
**ENNReal.rpow_le_rpow_of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {x : ENNReal} {y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 54 条，此处仅展示前 30 条）
-/
@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos] <;>
    linarith
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]
/-
**ENNReal.rpow_lt_rpow_of_exponent_gt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_rpow_of_exponent_gt {x : Real>=0∞} {y z : Real} (hx0 : 0 < x) (hx1
 : x < 1) (hyz : z < y) : x ^ y < x ^ z
参数：hx0 : 0 < x；hx1 : x < 1；hyz : z < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt {x : Rea
l>=0} {y z : Real} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
-/
theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]
/-
**ENNReal.rpow_le_rpow_of_exponent_ge** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_le_rpow_of_exponent_ge {x : Real>=0∞} {y z : Real} (hx1 : x <= 1) (hy
z : z <= y) : x ^ y <= x ^ z
参数：hx1 : x <= 1；hyz : z <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 56 条，此处仅展示前 30 条）
-/
theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [← coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]
/-
**ENNReal.rpow_le_self_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_le_self_of_le_one {x : Real>=0∞} {z : Real} (hx : x <= 1) (h_one_le :
 1 <= z) : x ^ z <= x
参数：hx : x <= 1；h_one_le : 1 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge {x : Re
al>=0∞} {y z : Real} (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
-/
theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le
/-
**ENNReal.le_rpow_self_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_rpow_self_of_one_le {x : Real>=0∞} {z : Real} (hx : 1 <= x) (h_one_le :
 1 <= z) : x <= x ^ z
参数：hx : 1 <= x；h_one_le : 1 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.rpow_le_rpow_of_exponent_le`：∀ {x : ENNReal} {y z : ℝ}, 1 ≤ x → 
y ≤ z → x ^ y ≤ x ^ z
-/
theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z := by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le
/-
**ENNReal.rpow_pos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_pos_of_nonneg {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hp_nonneg :
 0 <= p) : 0 < x ^ p
参数：hx_pos : 0 < x；hp_nonneg : 0 <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.rpow_lt_rpow`：∀ {x y : ENNReal} {z : ℝ}, x < y → 0 < z → x ^ z <
 y ^ z
-/
theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos
/-
**ENNReal.rpow_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_pos {p : Real} {x : Real>=0∞} (hx_pos : 0 < x) (hx_ne_top : x != ⊤) :
 0 < x ^ p
参数：hx_pos : 0 < x；hx_ne_top : x != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `ENNReal.rpow_pos_of_nonneg`：rpow_pos_of_nonneg {p : Real} {x : Real>=0∞}
 (hx_pos : 0 < x) (hp_nonneg : 0 <= p) : 0 < x ^ p
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `ENNReal.rpow_neg`：rpow_neg (x : Real>=0∞) (y : Real) : x ^ (-y) = (x ^ y
)⁻¹
· 使用定理 `ENNReal.inv_pos`：∀ {a : ENNReal}, 0 < a⁻¹ ↔ a ≠ ⊤
· 使用定理 `ENNReal.rpow_ne_top_of_nonneg`：rpow_ne_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p := by
  rcases lt_or_ge 0 p with hp_pos | hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top
/-
**ENNReal.rpow_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_one {x : Real>=0∞} {z : Real} (hx : x < 1) (hz : 0 < z) : x ^ z < 
1
参数：hx : x < 1；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_lt_one`：rpow_lt_one {x : Real>=0} {z : Real} (hx1 : x < 1) (
hz : 0 < z) : x ^ z < 1
-/
theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]
/-
**ENNReal.rpow_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_le_one {x : Real>=0∞} {z : Real} (hx : x <= 1) (hz : 0 <= z) : x ^ z 
<= 1
参数：hx : x <= 1；hz : 0 <= z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_le_one`：rpow_le_one {x : Real>=0} {z : Real} (hx2 : x <= 1) 
(hz : 0 <= z) : x ^ z <= 1
-/
theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]
/-
**ENNReal.rpow_lt_one_of_one_lt_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_lt_one_of_one_lt_of_neg {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : 
z < 0) : x ^ z < 1
参数：hx : 1 < x；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_lt_one_of_one_lt_of_neg`：rpow_lt_one_of_one_lt_of_neg {x : R
eal>=0} {z : Real} (hx : 1 < x) (hz : z < 0) : x ^ z < 1
-/
theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]
/-
**ENNReal.rpow_le_one_of_one_le_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_le_one_of_one_le_of_neg {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz :
 z < 0) : x ^ z <= 1
参数：hx : 1 <= x；hz : z < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.rpow_le_one_of_one_le_of_nonpos`：rpow_le_one_of_one_le_of_nonpos 
{x : Real>=0} {z : Real} (hx : 1 <= x) (hz : z <= 0) : x ^ z <= 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := by
  cases x
  · simp [top_rpow_of_neg hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]
/-
**ENNReal.one_lt_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_lt_rpow {x : Real>=0∞} {z : Real} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ 
z
参数：hx : 1 < x；hz : 0 < z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.one_lt_rpow`：one_lt_rpow {x : Real>=0} {z : Real} (hx : 1 < x) (h
z : 0 < z) : 1 < x ^ z
-/
theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]
/-
**ENNReal.one_le_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_le_rpow {x : Real>=0∞} {z : Real} (hx : 1 <= x) (hz : 0 < z) : 1 <= x 
^ z
参数：hx : 1 <= x；hz : 0 < z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.one_le_rpow`：one_le_rpow {x : Real>=0} {z : Real} (h : 1 <= x) (h
₁ : 0 <= z) : 1 <= x ^ z
-/
theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]
/-
**ENNReal.one_lt_rpow_of_pos_of_lt_one_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：one_lt_rpow_of_pos_of_lt_one_of_neg {x : Real>=0∞} {z : Real} (hx1 : 0 < x
) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z
参数：hx1 : 0 < x；hx2 : x < 1；hz : z < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg`：one_lt_rpow_of_pos_of_lt_one
_of_neg {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < 
x ^ z
-/
theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]
/-
**ENNReal.one_le_rpow_of_pos_of_le_one_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：one_le_rpow_of_pos_of_le_one_of_neg {x : Real>=0∞} {z : Real} (hx1 : 0 < x
) (hx2 : x <= 1) (hz : z < 0) : 1 <= x ^ z
参数：hx1 : 0 < x；hx2 : x <= 1；hz : z < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos`：one_le_rpow_of_pos_of_le_
one_of_nonpos {x : Real>=0} {z : Real} (hx1 : 0 < x) (hx2 : x <= 1) (hz : z <= 0
) : 1 <= x ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]
/-
**ENNReal.toNNReal_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : ENNReal) (z : ℝ), (x ^ z).toNNReal = x.toNNReal ^ z
参数：x : ENNReal；z : ℝ；x ^ z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_rpow_of_neg`：top_rpow_of_neg {y : Real} (h : y < 0) : (⊤ : R
eal>=0∞) ^ y = 0
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.zero_rpow_of_neg`：zero_rpow_of_neg {y : Real} (h : y < 0) : (0 :
 Real>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[simp] lemma toNNReal_rpow (x : ℝ≥0∞) (z : ℝ) : (x ^ z).toNNReal = x.toNNReal ^ z := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases x with
    | top => simp [H, ne_of_lt]
    | coe x =>
      by_cases hx : x = 0
      · simp [hx, H, ne_of_lt]
      · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt H)]
/-
**ENNReal.toReal_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_rpow (x : Real>=0∞) (z : Real) : x.toReal ^ z = (x ^ z).toReal
参数：x : Real>=0∞；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal.eq_1`：∀ (a : ENNReal), a.toReal = ↑a.toNNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_rpow`：coe_rpow (x : Real>=0) (y : Real) : ((x ^ y : Real>=0) 
: Real) = (x : Real) ^ y
· 使用定理 `ENNReal.toNNReal_rpow`：∀ (x : ENNReal) (z : ℝ), (x ^ z).toNNReal = x.toN
NReal ^ z
-/
theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_rpow, ENNReal.toNNReal_rpow]
/-
**ENNReal.ofReal_rpow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_rpow_of_pos {x p : Real} (hx_pos : 0 < x) : ENNReal.ofReal x ^ p = 
ENNReal.ofReal (x ^ p)
参数：hx_pos : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_ne_zero`：coe_rpow_of_ne_zero {x : Real>=0} (h : x !=
 0) (y : Real) : (↑(x ^ y) : Real>=0∞) = x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `Real.toNNReal_rpow_of_nonneg`：∀ {x y : ℝ}, 0 ≤ x → (x ^ y).toNNReal = x.
toNNReal ^ y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero, coe_inj, Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]
/-
**ENNReal.ofReal_rpow_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_rpow_of_nonneg {x p : Real} (hx_nonneg : 0 <= x) (hp_nonneg : 0 <= 
p) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p)
参数：hx_nonneg : 0 <= x；hp_nonneg : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_zero`：rpow_zero {x : Real>=0∞} : x ^ (0 : Real) = 1
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.ofReal_rpow_of_pos`：ofReal_rpow_of_pos {x p : Real} (hx_pos : 0 
< x) : ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p)
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)
/-
**ENNReal.rpow_rpow_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y) ^ y⁻¹ = x
参数：x : ENNReal；x ^ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y) ^ y⁻¹ = x := by
  rw [← rpow_mul, mul_inv_cancel₀ hy, rpow_one]
/-
**ENNReal.rpow_inv_rpow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y⁻¹) ^ y = x
参数：x : ENNReal；x ^ y⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
@[simp] lemma rpow_inv_rpow {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y⁻¹) ^ y = x := by
  rw [← rpow_mul, inv_mul_cancel₀ hy, rpow_one]

@[simp]
/-
**ENNReal.rpow_rpow_inv_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_rpow_inv_eq_iff {x : Real>=0∞} {y : Real} : (x ^ y) ^ y⁻¹ = x ↔ y != 
0 ∨ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rpow_rpow_inv_eq_iff {x : ℝ≥0∞} {y : ℝ} : (x ^ y) ^ y⁻¹ = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_zero, rpow_rpow_inv]

@[simp]
/-
**ENNReal.rpow_inv_rpow_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_inv_rpow_eq_iff {x : Real>=0∞} {y : Real} : (x ^ y⁻¹) ^ y = x ↔ y != 
0 ∨ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rpow_inv_rpow_eq_iff {x : ℝ≥0∞} {y : ℝ} : (x ^ y⁻¹) ^ y = x ↔ y ≠ 0 ∨ x = 1 := by
  grind [rpow_rpow_inv_eq_iff]
/-
**ENNReal.pow_rpow_inv_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：pow_rpow_inv_natCast {n : Nat} (hn : n != 0) (x : Real>=0∞) : (x ^ n) ^ (n
⁻¹ : Real) = x
参数：hn : n != 0；x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
lemma pow_rpow_inv_natCast {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  rw [← rpow_natCast, ← rpow_mul, mul_inv_cancel₀ (by positivity), rpow_one]
/-
**ENNReal.rpow_inv_natCast_pow** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_inv_natCast_pow {n : Nat} (hn : n != 0) (x : Real>=0∞) : (x ^ (n⁻¹ : 
Real)) ^ n = x
参数：hn : n != 0；x : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
-/
lemma rpow_inv_natCast_pow {n : ℕ} (hn : n ≠ 0) (x : ℝ≥0∞) : (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  rw [← rpow_natCast, ← rpow_mul, inv_mul_cancel₀ (by positivity), rpow_one]
/-
**ENNReal.rpow_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_natCast_mul (x : Real>=0∞) (n : Nat) (z : Real) : x ^ (n * z) = (x ^ 
n) ^ z
参数：x : Real>=0∞；n : Nat；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
-/
lemma rpow_natCast_mul (x : ℝ≥0∞) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]
/-
**ENNReal.rpow_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_mul_natCast (x : Real>=0∞) (y : Real) (n : Nat) : x ^ (y * n) = (x ^ 
y) ^ n
参数：x : Real>=0∞；y : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
-/
lemma rpow_mul_natCast (x : ℝ≥0∞) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]
/-
**ENNReal.rpow_intCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_intCast_mul (x : Real>=0∞) (n : Int) (z : Real) : x ^ (n * z) = (x ^ 
n) ^ z
参数：x : Real>=0∞；n : Int；z : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `ENNReal.rpow_intCast`：rpow_intCast (x : Real>=0∞) (n : Int) : x ^ (n : R
eal) = x ^ n
-/
lemma rpow_intCast_mul (x : ℝ≥0∞) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]
/-
**ENNReal.rpow_mul_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_mul_intCast (x : Real>=0∞) (y : Real) (n : Int) : x ^ (y * n) = (x ^ 
y) ^ n
参数：x : Real>=0∞；y : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用引理 `ENNReal.rpow_intCast`：rpow_intCast (x : Real>=0∞) (n : Int) : x ^ (n : R
eal) = x ^ n
-/
lemma rpow_mul_intCast (x : ℝ≥0∞) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]
/-
**ENNReal.rpow_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：rpow_left_injective {x : Real} (hx : x != 0) : Injective fun y : Real>=0∞ 
=> y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `ENNReal.rpow_rpow_inv`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y) ^ y⁻¹
 = x
-/
lemma rpow_left_injective {x : ℝ} (hx : x ≠ 0) : Injective fun y : ℝ≥0∞ ↦ y ^ x :=
  HasLeftInverse.injective ⟨fun y ↦ y ^ x⁻¹, rpow_rpow_inv hx⟩
/-
**ENNReal.rpow_left_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_left_surjective {x : Real} (hx : x != 0) : Function.Surjective fun y 
: Real>=0∞ => y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
· 使用定理 `ENNReal.rpow_inv_rpow`：∀ {y : ℝ}, y ≠ 0 → ∀ (x : ENNReal), (x ^ y⁻¹) ^ y
 = x
-/
theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : Function.Surjective fun y : ℝ≥0∞ => y ^ x :=
  HasRightInverse.surjective ⟨fun y ↦ y ^ x⁻¹, rpow_inv_rpow hx⟩
/-
**ENNReal.rpow_left_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：rpow_left_bijective {x : Real} (hx : x != 0) : Function.Bijective fun y : 
Real>=0∞ => y ^ x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.rpow_left_injective`：rpow_left_injective {x : Real} (hx : x != 0
) : Injective fun y : Real>=0∞ => y ^ x
· 使用定理 `ENNReal.rpow_left_surjective`：rpow_left_surjective {x : Real} (hx : x !=
 0) : Function.Surjective fun y : Real>=0∞ => y ^ x
-/
theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : Function.Bijective fun y : ℝ≥0∞ => y ^ x :=
  ⟨rpow_left_injective hx, rpow_left_surjective hx⟩
/-
**ENNReal._root_.Real.enorm_rpow_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.enorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖x ^ y‖ₑ = ‖x‖ₑ ^ y := by simp [enorm, nnnorm_rpow_of_nonneg hx, coe_rpow_of_nonneg _ hy]
/-
**ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow** 是 Mathlib 中的一个引理，位于命名空间 `ENNR
eal`。
形式化陈述：add_rpow_le_two_rpow_mul_rpow_add_rpow {p : Real} (a b : Real>=0∞) (hp : 0
 <= p) : (a + b) ^ p <= 2 ^ p * (a ^ p + b ^ p)
参数：a b : Real>=0∞；hp : 0 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ENNReal.mul_rpow_of_nonneg`：mul_rpow_of_nonneg (x y : Real>=0∞) {z : Rea
l} (hz : 0 <= z) : (x * y) ^ z = x ^ z * y ^ z
· 使用引理 `ENNReal.max_rpow`：max_rpow {x y : Real>=0∞} {p : Real} (hp : 0 <= p) : m
ax x y ^ p = max (x ^ p) (y ^ p)
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `max_le_add_of_nonneg`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : 
AddZeroClass α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ b → ma
x a b ≤ a …
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma add_rpow_le_two_rpow_mul_rpow_add_rpow {p : ℝ} (a b : ℝ≥0∞) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := calc
  (a + b) ^ p ≤ (2 * max a b) ^ p := by rw [two_mul]; gcongr <;> simp
  _ = 2 ^ p * (max a b) ^ p := mul_rpow_of_nonneg _ _ hp
  _ = 2 ^ p * max (a ^ p) (b ^ p) := by rw [max_rpow hp]
  _ ≤ 2 ^ p * (a ^ p + b ^ p) := by gcongr; apply max_le_add_of_nonneg <;> simp

end ENNReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
-- section Tactics

-- /-!
-- ## Tactic extensions for powers on `ℝ≥0` and `ℝ≥0∞`
-- -/


-- namespace NormNum

-- theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, NNReal.rpow_natCast]

-- theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_natCast]

-- theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
--     a ^ b = c := by rw [← h, hb, ENNReal.rpow_natCast]

-- theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
--     (hc : c⁻¹ = c') : a ^ (-b) = c' := by
--   rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_natCast]

-- /-- Evaluate `NNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))

-- /-- Evaluate `ENNReal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))

-- /-- Evaluates expressions of the form `rpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_nnrpow_ennrpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
--   | _ => tactic.failed

-- end NormNum

-- namespace Tactic

-- namespace Positivity

-- private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
--   NNReal.rpow_pos ha

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals.
-- -/
-- unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   match strictness_a with
--     | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
--     | _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0`
-- private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
--   ENNReal.rpow_pos_of_nonneg ha hb.le

-- /-- Auxiliary definition for the `positivity` tactic to handle real powers of extended
-- nonnegative reals. -/
-- unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
--   let strictness_a ← core a
--   let strictness_b ← core b
--   match strictness_a, strictness_b with
--     | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
--     | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
--     | _, _ => failed

-- -- We already know `0 ≤ x` for all `x : ℝ≥0∞`
-- end Positivity

-- open Positivity

-- /-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
-- the base is nonnegative and positive when the base is positive. -/
-- @[positivity]
-- unsafe def positivity_nnrpow_ennrpow : expr → tactic strictness
--   | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
--   | q(NNReal.rpow $(a) $(b)) => prove_nnrpow a b
--   | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
--   | q(ENNReal.rpow $(a) $(b)) => prove_ennrpow a b
--   | _ => failed

-- end Tactic

-- end Tactics

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `NNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : ℝ≥0) ^ (_ : ℝ)]
meta def evalNNRealRpow : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(NNReal.rpow_zero_pos $a))
  | 0, ~q(ℝ≥0), ~q($a ^ ($b : ℝ)) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa =>
      pure (.positive q(NNReal.rpow_pos $pa))
    | _ =>
      pure (.nonnegative q(zero_le (a := $e)))
  | _, _, _ => throwError "not NNReal.rpow"

private meta def isFiniteM? (x : Q(ℝ≥0∞)) : MetaM (Option Q($x ≠ (⊤ : ℝ≥0∞))) := do
  let mvar ← mkFreshExprMVar q($x ≠ (⊤ : ℝ≥0∞))
  let save ← saveState
  let (goals, _) ← Elab.runTactic mvar.mvarId! <|← `(tactic| finiteness)
  if goals.isEmpty then
    pure <| some <|← instantiateMVars mvar
  else
    restoreState save
    pure none

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when
the base is nonnegative and positive when the base is positive.
This is the `ENNReal` analogue of `evalRpow` for `Real`. -/
@[positivity (_ : ℝ≥0∞) ^ (_ : ℝ)]
meta def evalENNRealRpow : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q($a ^ (0 : ℝ)) =>
    assertInstancesCommute
    pure (.positive q(ENNReal.rpow_zero_pos $a))
  | 0, ~q(ℝ≥0∞), ~q($a ^ ($b : ℝ)) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    let rb ← catchNone <| core q(inferInstance) (some q(inferInstance)) b
    match ra, rb with
    | .positive pa, .positive pb =>
      pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa <| le_of_lt $pb))
    | .positive pa, .nonnegative pb =>
      pure (.positive q(ENNReal.rpow_pos_of_nonneg $pa $pb))
    | .positive pa, _ =>
      let some ha ← isFiniteM? a | pure <| .nonnegative q(zero_le (a := $e))
      pure <| .positive q(ENNReal.rpow_pos $pa $ha)
    | _, _ =>
      pure <| .nonnegative q(zero_le (a := $e))
  | _, _, _ => throwError "not ENNReal.rpow"

end Mathlib.Meta.Positivity

/-!
## NormNum extension for NNReal powers
-/

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/-
**Mathlib.Meta.NormNum.IsNat.nnreal_rpow_eq_nnreal_pow** 是 Mathlib 中的一个定理，位于命名空间
 `Mathlib.Meta.NormNum.IsNat`。
形式化陈述：∀ {b : ℝ} {n : ℕ}, Mathlib.Meta.NormNum.IsNat b n → ∀ (a : NNReal), a ^ b 
= a ^ n
参数：a : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
-/
theorem IsNat.nnreal_rpow_eq_nnreal_pow {b : ℝ} {n : ℕ} (h : IsNat b n) (a : ℝ≥0) :
    a ^ b = a ^ n := by
  rw [h.1, NNReal.rpow_natCast]
/-
**Mathlib.Meta.NormNum.IsInt.nnreal_rpow_eq_inv_nnreal_pow** 是 Mathlib 中的一个定理，位于
命名空间 `Mathlib.Meta.NormNum.IsInt`。
形式化陈述：∀ {b : ℝ} {n : ℕ}, Mathlib.Meta.NormNum.IsInt b (Int.negOfNat n) → ∀ (a : 
NNReal), a ^ b = (a ^ n)⁻¹
参数：Int.negOfNat n；a : NNReal；a ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用引理 `NNReal.rpow_intCast`：rpow_intCast (x : Real>=0) (n : Int) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `Int.negOfNat_eq`：∀ {n : ℕ}, Int.negOfNat n = -Int.ofNat n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem IsInt.nnreal_rpow_eq_inv_nnreal_pow {b : ℝ} {n : ℕ} (h : IsInt b (.negOfNat n)) (a : ℝ≥0) :
    a ^ b = (a ^ n)⁻¹ := by
  rw [h.1, NNReal.rpow_intCast, Int.negOfNat_eq, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast]
/-
**Mathlib.Meta.NormNum.IsNat.nnreal_rpow_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Meta.NormNum.IsNat`。
形式化陈述：∀ {a : NNReal} {b : ℝ} {m n d r : ℕ},   Mathlib.Meta.NormNum.IsNat a m →  
   Mathlib.Meta.NormNum.IsNNRat b n d →       ∀ (k : ℕ), r ^ d = k → ∀ (l : ℕ), 
m ^ n = l → k = l → Mathlib.Meta.NormNum.IsNat (a ^ b) r
参数：k : ℕ；l : ℕ；a ^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `NNReal.rpow_natCast_mul`：rpow_natCast_mul (x : Real>=0) (n : Nat) (z : R
eal) : x ^ (n * z) = (x ^ n) ^ z
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `NNReal.pow_rpow_inv_natCast`：pow_rpow_inv_natCast (x : Real>=0) {n : Nat
} (hn : n != 0) : (x ^ n) ^ (n⁻¹ : Real) = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem IsNat.nnreal_rpow_isNNRat {a : ℝ≥0} {b : ℝ} {m n d r : ℕ} (ha : IsNat a m)
    (hb : IsNNRat b n d) (k : ℕ) (hr : r ^ d = k) (l : ℕ) (hm : m ^ n = l) (hkl : k = l) :
    IsNat (a ^ b) r := by
  rcases ha with ⟨rfl⟩
  constructor
  have : d ≠ 0 := mod_cast hb.den_nz
  rw [hb.to_eq rfl rfl, div_eq_mul_inv, NNReal.rpow_natCast_mul, ← Nat.cast_pow, hm, ← hkl, ← hr,
    Nat.cast_pow, NNReal.pow_rpow_inv_natCast]
  positivity
/-
**Mathlib.Meta.NormNum.IsNNRat.nnreal_rpow_isNNRat** 是 Mathlib 中的一个定理，位于命名空间 `Ma
thlib.Meta.NormNum.IsNNRat`。
形式化陈述：∀ (a : NNReal) (b : ℝ) (na da : ℕ),   Mathlib.Meta.NormNum.IsNNRat a na da
 →     ∀ (nr dr : ℕ),       Mathlib.Meta.NormNum.IsNat (↑na ^ b) nr →         Ma
thlib.Meta.NormNum.IsNat (↑da ^ b) dr → Mathlib.Meta.NormNum.IsNNRat (a ^ b) nr 
dr
参数：a : NNReal；b : ℝ；na da : ℕ；nr dr : ℕ；↑na ^ b；↑da ^ b；a ^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `NNReal.div_rpow`：div_rpow (x y : Real>=0) (z : Real) : (x / y) ^ z = x ^
 z / y ^ z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem IsNNRat.nnreal_rpow_isNNRat (a : ℝ≥0) (b : ℝ) (na da : ℕ) (ha : IsNNRat a na da)
    (nr dr : ℕ) (hnum : IsNat ((na : ℝ≥0) ^ b) nr) (hden : IsNat ((da : ℝ≥0) ^ b) dr) :
    IsNNRat (a ^ b) nr dr := by
  suffices IsNNRat (nr / dr : ℝ≥0) nr dr by
    simpa [ha.to_eq, NNReal.div_rpow, hnum.1, hden.1]
  apply IsNNRat.of_raw
  simp [← hden.1, ha.den_nz]
/-
**Mathlib.Meta.NormNum.nnreal_rpow_isRat_eq_inv_nnreal_rpow** 是 Mathlib 中的一个定理，位
于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：nnreal_rpow_isRat_eq_inv_nnreal_rpow (a : Real>=0) (b : Real) (n d : Nat) 
(hb : IsRat b (Int.negOfNat n) d) : a ^ b = (a⁻¹) ^ (n / d : Real)
参数：a : Real>=0；b : Real；n d : Nat；hb : IsRat b (Int.negOfNat n) d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.inv_rpow`：inv_rpow (x : Real>=0) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNReal.rpow_neg`：rpow_neg (x : Real>=0) (y : Real) : x ^ (-y) = (x ^ y)⁻
¹
· 使用定理 `Mathlib.Meta.NormNum.IsRat.neg_to_eq`：∀ {α : Type u_1} [inst : DivisionR
ing α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsRat a (Int.negOfNat n) 
d → ↑n = n' → ↑d = d' → a …
-/
theorem nnreal_rpow_isRat_eq_inv_nnreal_rpow (a : ℝ≥0) (b : ℝ) (n d : ℕ)
    (hb : IsRat b (Int.negOfNat n) d) : a ^ b = (a⁻¹) ^ (n / d : ℝ) := by
  rw [NNReal.inv_rpow, ← NNReal.rpow_neg, hb.neg_to_eq rfl rfl]

open Lean

/-- Given proofs
- that `a` is a natural number `na`;
- that `b` is a nonnegative rational number `nb / db`;

returns a tuple of
- a natural number `r` (result);
- the same number, as an expression;
- a proof that `a ^ b = r`.

Fails if `na` is not a `db`th power of a natural number.
-/
meta def proveIsNatNNRealRPowIsNNRat
    (a : Q(ℝ≥0)) (na : Q(ℕ)) (pa : Q(IsNat $a $na))
    (b : Q(ℝ)) (nb db : Q(ℕ)) (pb : Q(IsNNRat $b $nb $db)) :
    MetaM (ℕ × Σ r : Q(ℕ), Q(IsNat ($a ^ $b) $r)) := do
  let r := (Nat.nthRoot db.natLit! na.natLit!) ^ nb.natLit!
  have er : Q(ℕ) := mkRawNatLit r
  -- avoid evaluating powers in kernel
  let .some ⟨c, pc⟩ ← liftM <| OptionT.run <| evalNatPow er db | failure
  let .some ⟨d, pd⟩ ← liftM <| OptionT.run <| evalNatPow na nb | failure
  guard (c.natLit! = d.natLit!)
  have hcd : Q($c = $d) := (q(Eq.refl $c) : Expr)
  return (r, ⟨er, q(IsNat.nnreal_rpow_isNNRat $pa $pb $c $pc $d $pd $hcd)⟩)

/-- Evaluates expressions of the form `a ^ b` when `a : ℝ≥0` and `b : ℝ`.
Works if `a`, `b`, and `a ^ b` are in fact rational numbers.
-/
@[norm_num (_ : ℝ≥0) ^ (_ : ℝ)]
meta def evalNNRealRPow : NormNumExt where eval {u αR} e := do
  match u, αR, e with
  | 0, ~q(ℝ≥0), ~q(($a : ℝ≥0)^($b : ℝ)) =>
    match ← derive b with
    | .isNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsNat.nnreal_rpow_eq_nnreal_pow $pb _) (← derive q($a ^ $nb))
    | .isNegNat sβ nb pb =>
      assumeInstancesCommute
      return .eqTrans q(IsInt.nnreal_rpow_eq_inv_nnreal_pow $pb _) (← derive q(($a ^ $nb)⁻¹))
    | .isNNRat _ qb nb db pb => do
      assumeInstancesCommute
      match ← derive a with
      | .isNat sa na pa => do
        let ⟨_, r, pr⟩ ← proveIsNatNNRealRPowIsNNRat a na pa b nb db pb
        return .isNat sa r pr
      | .isNNRat _ qα na da pa => do
        assumeInstancesCommute
        let ⟨rnum, ernum, pnum⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $na) na q(IsNat.of_raw _ _) b nb db pb
        let ⟨rden, erden, pden⟩ ←
          proveIsNatNNRealRPowIsNNRat q(Nat.rawCast $da) da q(IsNat.of_raw _ _) b nb db pb
        return .isNNRat q(inferInstance) (rnum / rden) ernum erden
          q(IsNNRat.nnreal_rpow_isNNRat $a $b $na $da $pa $ernum $erden $pnum $pden)
      | _ => failure
    | .isNegNNRat _ qb nb db pb => do
      let r ← derive q(($a⁻¹) ^ ($nb / $db : ℝ))
      assumeInstancesCommute
      return .eqTrans q(nnreal_rpow_isRat_eq_inv_nnreal_rpow $a $b $nb $db $pb) r
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum

