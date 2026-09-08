/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Alex Keizer
-/
module

public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Bits
public import Mathlib.Order.Basic
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.Common
public import Batteries.Data.Nat.Bitwise
import all Init.Data.Nat.Bitwise.Basic  -- for unfolding `bitwise`

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `xor`, which are defined in core.

## Main results
* `eq_of_testBit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_testBit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/

public section

open Function

namespace Nat

section
variable {f : Bool → Bool → Bool}

@[simp]
/-
**Nat.bitwise_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 
0
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_1`：∀ (f : Bool → Bool
 → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = tr
ue then m else 0     else       if m = 0 t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 0 := by
  simp [bitwise]

@[simp]
/-
**Nat.bitwise_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_zero_right (n : Nat) : bitwise f n 0 = if f true false then n else
 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_def`：∀ (f : Bool → Bo
ol → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = 
true then m else 0     else       if m = 0 t…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma bitwise_zero_right (n : Nat) : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl
/-
**Nat.bitwise_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_zero : bitwise f 0 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bitwise_zero : bitwise f 0 0 = 0 := by
  simp only [bitwise_zero_right, ite_self]
/-
**Nat.bitwise_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_of_ne_zero {n m : Nat} (hn : n != 0) (hm : m != 0) : bitwise f n m
 = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2))
参数：hn : n != 0；hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_def`：∀ (f : Bool → Bo
ol → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = 
true then m else 0     else       if m = 0 t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用引理 `Nat.mod_two_of_bodd`：mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bitwise_of_ne_zero {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0) :
    bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2)) := by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd]; cases bodd x <;> rfl
  simp [hn, hm, mod_two_iff_bod, bit, two_mul]
/-
**Nat.binaryRec_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binaryRec_of_ne_zero {C : Nat -> Sort*} (z : C 0) (f : forall b n, C n -> 
C (bit b n)) {n} (h : n != 0) : binaryRec z f n = n.bit_bodd_div2 ▸ f n.bodd n.d
iv2 (binaryRec z f n.div2)
参数：z : C 0；f : forall b n, C n -> C (bit b n)；h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.bit_bodd_div2`：bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binaryRec.eq_1`：∀ {motive : ℕ → Sort u} (zero : motive 0) (bit : (b 
: Bool) → (n : ℕ) → motive n → motive (Nat.bit b n)) (n : ℕ),   Nat.binaryRec ze
ro bit n…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eqRec_eq_cast`：∀ {α : Sort u_1} {a : α} {motive : (a' : α) → a = a' → So
rt u_2} (x : motive a ⋯) {a' : α} (e : a = a'),   e ▸ x = cast ⋯ x
-/
theorem binaryRec_of_ne_zero {C : Nat → Sort*} (z : C 0) (f : ∀ b n, C n → C (bit b n)) {n}
    (h : n ≠ 0) :
    binaryRec z f n = n.bit_bodd_div2 ▸ f n.bodd n.div2 (binaryRec z f n.div2) := by
  rw [binaryRec, dif_neg h, eqRec_eq_cast, eqRec_eq_cast]; rfl

@[simp]
/-
**Nat.bitwise_bit** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false false = false
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_def`：∀ (f : Bool → Bo
ol → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = 
true then m else 0     else       if m = 0 t…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.cond_eq_ite`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif b then t e
lse e) = if b = true then t else e
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.add_mul_div_left`：∀ (x z : ℕ) {y : ℕ}, 0 < y → (x + y * z) / y = x /
 y + z
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Bool.true_eq_false`：(true = false) = False
（共 42 条，此处仅展示前 30 条）
-/
lemma bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false := by rfl) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  simp only [bit, Bool.cond_eq_ite]
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp <;> split_ifs
    <;> simp_all +decide [two_mul]
/-
**Nat.bit_mod_two_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bit_mod_two_eq_zero_iff (a x) : bit a x % 2 = 0 ↔ !a
参数：a x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.bit_mod_two`：bit_mod_two (b n) : bit b n % 2 = b.toNat
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bit_mod_two_eq_zero_iff (a x) :
    bit a x % 2 = 0 ↔ !a := by
  simp
/-
**Nat.bit_mod_two_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bit_mod_two_eq_one_iff (a x) : bit a x % 2 = 1 ↔ a
参数：a x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.bit_mod_two`：bit_mod_two (b n) : bit b n % 2 = b.toNat
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bit_mod_two_eq_one_iff (a x) :
    bit a x % 2 = 1 ↔ a := by
  simp

@[simp]
/-
**Nat.lor_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lor_bit : forall a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
-/
theorem lor_bit : ∀ a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n) :=
  bitwise_bit

@[simp]
/-
**Nat.land_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：land_bit : forall a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
-/
theorem land_bit : ∀ a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n) :=
  bitwise_bit

@[simp]
/-
**Nat.ldiff_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ldiff_bit : forall a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (
ldiff m n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
-/
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit

@[simp]
/-
**Nat.xor_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_bit : forall a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.bitwise_bit`：bitwise_bit {f : Bool -> Bool -> Bool} (h : f false fal
se = false
-/
theorem xor_bit : ∀ a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n) :=
  bitwise_bit

attribute [simp] Nat.testBit_bitwise
/-
**Nat.testBit_lor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_lor : forall m n k, testBit (m ||| n) k = (testBit m k || testBit 
n k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.testBit_bitwise`：∀ {f : Bool → Bool → Bool},   f false false = false
 → ∀ (x y i : ℕ), (Nat.bitwise f x y).testBit i = f (x.testBit i) (y.testBit i)
-/
theorem testBit_lor : ∀ m n k, testBit (m ||| n) k = (testBit m k || testBit n k) :=
  testBit_bitwise rfl
/-
**Nat.testBit_land** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_land : forall m n k, testBit (m &&& n) k = (testBit m k && testBit
 n k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.testBit_bitwise`：∀ {f : Bool → Bool → Bool},   f false false = false
 → ∀ (x y i : ℕ), (Nat.bitwise f x y).testBit i = f (x.testBit i) (y.testBit i)
-/
theorem testBit_land : ∀ m n k, testBit (m &&& n) k = (testBit m k && testBit n k) :=
  testBit_bitwise rfl

@[simp]
/-
**Nat.testBit_ldiff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_ldiff : forall m n k, testBit (ldiff m n) k = (testBit m k && not 
(testBit n k))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.testBit_bitwise`：∀ {f : Bool → Bool → Bool},   f false false = false
 → ∀ (x y i : ℕ), (Nat.bitwise f x y).testBit i = f (x.testBit i) (y.testBit i)
-/
theorem testBit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise rfl

end

/-- An alternative for `bitwise_bit` which replaces the `f false false = false` assumption
with assumptions that neither `bit a m` nor `bit b n` are `0`
(albeit, phrased as the implications `m = 0 → a = true` and `n = 0 → b = true`) -/
/-
**Nat.bitwise_bit'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_bit' {f : Bool -> Bool -> Bool} (a : Bool) (m : Nat) (b : Bool) (n
 : Nat) (ham : m = 0 -> a = true) (hbn : n = 0 -> b = true) : bitwise f (bit a m
) (bit b n) = bit (f a b) (bitwise f m n)
参数：a : Bool；m : Nat；b : Bool；n : Nat；ham : m = 0 -> a = true；hbn : n = 0 -> b = 
true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_def`：∀ (f : Bool → Bo
ol → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = 
true then m else 0     else       if m = 0 t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bit_ne_zero_iff`：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0
 ↔ n = 0 -> b = true
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Bool.decide_coe`：∀ (b : Bool) [inst : Decidable (b = true)], decide (b =
 true) = b
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Bool.cond_eq_ite`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif b then t e
lse e) = if b = true then t else e

--- 原说明 ---
An alternative for `bitwise_bit` which replaces the `f false false = false` assu
mption
with assumptions that neither `bit a m` nor `bit b n` are `0`
(albeit, phrased as the implications `m = 0 → a = true` and `n = 0 → b = true`)
-/
lemma bitwise_bit' {f : Bool → Bool → Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
    (ham : m = 0 → a = true) (hbn : n = 0 → b = true) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit,
    ite_false]
  conv_rhs => simp only [bit, two_mul, Bool.cond_eq_ite]
/-
**Nat.bitwise_eq_binaryRec** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：bitwise_eq_binaryRec (f : Bool -> Bool -> Bool) : bitwise f = binaryRec (f
un n => cond (f false true) n 0) fun a m Ia => binaryRec (cond (f true false) (b
it a m) 0) fun b n _ => bit (f a b) (Ia n)
参数：f : Bool -> Bool -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.bitwise_zero_left`：bitwise_zero_left (m : Nat) : bitwise f 0 m = if 
f false true then m else 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.cond_eq_ite`：∀ {α : Sort u_1} (b : Bool) (t e : α), (bif b then t e
lse e) = if b = true then t else e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.bit_bodd_div2`：bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.binaryRec_of_ne_zero`：binaryRec_of_ne_zero {C : Nat -> Sort*} (z : C
 0) (f : forall b n, C n -> C (bit b n)) {n} (h : n != 0) : binaryRec z f n = n.
bit_bodd_div2 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.bit_ne_zero_iff`：bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b != 0
 ↔ n = 0 -> b = true
· 使用引理 `Nat.bodd_bit`：bodd_bit (b n) : bodd (bit b n) = b
· 使用引理 `Nat.div2_bit`：div2_bit (b n) : div2 (bit b n) = n
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
· 使用引理 `Nat.bitwise_of_ne_zero`：bitwise_of_ne_zero {n m : Nat} (hn : n != 0) (hm
 : m != 0) : bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2
))
· 使用定理 `Nat.bit_div_two`：bit_div_two (b n) : bit b n / 2 = n
-/
lemma bitwise_eq_binaryRec (f : Bool → Bool → Bool) :
    bitwise f =
    binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
      binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n) := by
  funext x y
  induction x using binaryRec' generalizing y with
  | zero => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | bit xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y using binaryRec' with
    | zero => simp only [bitwise_zero_right, binaryRec_zero, Bool.cond_eq_ite]
    | bit yb y hyb =>
      rw [← bit_ne_zero_iff] at hyb
      simp_rw [binaryRec_of_ne_zero _ _ hyb, bitwise_of_ne_zero hxb hyb, bodd_bit, div2_bit,
        bit_div_two, eq_rec_constant, ih]
/-
**Nat.zero_of_testBit_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：zero_of_testBit_eq_false {n : Nat} (h : forall i, testBit n i = false) : n
 = 0
参数：h : forall i, testBit n i = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Nat.bit_mod_two`：bit_mod_two (b n) : bit b n % 2 = b.toNat
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
· 使用定理 `Nat.bit_false`：bit_false : bit false = (2 * ·)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
-/
theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 := by
  induction n using Nat.binaryRec with | zero => rfl | bit b n hn => ?_
  have : b = false := by simpa using h 0
  rw [this, bit_false, hn fun i => by rw [← h (i + 1), testBit_bit_succ]]
/-
**Nat.testBit_eq_false_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i = false
参数：h : n < 2 ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftRight_eq_div_pow`：∀ (m n : ℕ), m >>> n = m / 2 ^ n
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.and_zero`：∀ (x : ℕ), x &&& 0 = 0
· 使用定理 `bne_self_eq_false`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α)
, (a != a) = false
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/-- The ith bit is the ith element of `n.bits`. -/
/-
**Nat.testBit_eq_inth** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：testBit_eq_inth (n i : Nat) : n.testBit i = n.bits.getI i
参数：n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.one_and_eq_mod_two`：∀ (n : ℕ), 1 &&& n = n % 2
· 使用引理 `Nat.mod_two_of_bodd`：mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat
· 使用定理 `Nat.bodd_eq_bits_head`：bodd_eq_bits_head (n : Nat) : n.bodd = n.bits.hea
dI
· 使用定理 `List.getI_zero_eq_headI`：getI_zero_eq_headI : l.getI 0 = l.headI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.bit_bodd_div2`：bit_bodd_div2 (n : Nat) : bit (bodd n) (div2 n) = n
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
· 使用定理 `Nat.div2_bits_eq_tail`：div2_bits_eq_tail (n : Nat) : n.div2.bits = n.bit
s.tail
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The ith bit is the ith element of `n.bits`.
-/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i := by
  induction i generalizing n with
  | zero =>
    simp only [testBit, shiftRight_zero, one_and_eq_mod_two, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  | succ i ih =>
    conv_lhs => rw [← bit_bodd_div2 n]
    rw [testBit_bit_succ, ih n.div2, div2_bits_eq_tail]
    cases n.bits <;> simp
/-
**Nat.exists_most_significant_bit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_most_significant_bit {n : Nat} (h : n != 0) : exists i, testBit n i
 = true ∧ forall j, i < j -> testBit n j = false
参数：h : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
· 使用定理 `Nat.zero_testBit`：∀ (i : ℕ), Nat.testBit 0 i = false
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
-/
theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = true ∧ ∀ j, i < j → testBit n j = false := by
  induction n using Nat.binaryRec with | zero => exact False.elim (h rfl) | bit b n hn => ?_
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [testBit_bit_succ, zero_testBit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine ⟨k + 1, ⟨by rw [testBit_bit_succ, hk], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by intro x; subst x; simp at hj)
    exact (testBit_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))
/-
**Nat.lt_of_testBit** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_of_testBit {n m : Nat} (i : Nat) (hn : testBit n i = false) (hm : testB
it m i = true) (hnm : forall j, i < j -> testBit n j = testBit m j) : n < m
参数：i : Nat；hn : testBit n i = false；hm : testBit m i = true；hnm : forall j, i < 
j -> testBit n j = testBit m j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_testBit`：∀ (i : ℕ), Nat.testBit 0 i = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.false_ne_true`：false ≠ true
· 使用定理 `Nat.eq_of_testBit_eq`：∀ {x y : ℕ}, (∀ (i : ℕ), x.testBit i = y.testBit i
) → x = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Nat.testBit_bit_succ`：testBit_bit_succ (m b n) : testBit (bit b n) (succ
 m) = testBit n m
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.testBit_bit_zero`：testBit_bit_zero (b n) : (bit b n).testBit 0 = b
· 使用定理 `Nat.bit_false`：bit_false : bit false = (2 * ·)
· 使用定理 `Nat.bit_true`：bit_true : bit true = (2 * · + 1)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用引理 `Nat.bit_lt_bit`：bit_lt_bit (a b) (h : m < n) : bit a m < bit b n
-/
theorem lt_of_testBit {n m : ℕ} (i : ℕ) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m := by
  induction n using Nat.binaryRec generalizing i m with
  | zero =>
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  | bit b n hn' =>
    induction m using Nat.binaryRec generalizing i with
    | zero => exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
    | bit b' m hm' =>
      by_cases hi : i = 0
      · subst hi
        simp only [testBit_bit_zero] at hn hm
        have : n = m :=
          eq_of_testBit_eq fun i => by convert! hnm (i + 1) (Nat.zero_lt_succ _) using 1
          <;> rw [testBit_bit_succ]
        rw [hn, hm, this, bit_false, bit_true]
        exact Nat.lt_succ_self _
      · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
        simp only [testBit_bit_succ] at hn hm
        have := hn' _ hn hm fun j hj => by
          convert! hnm j.succ (succ_lt_succ hj) using 1 <;> rw [testBit_bit_succ]
        exact bit_lt_bit b b' this
/-
**Nat.bitwise_swap** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitwise_swap {f : Bool -> Bool -> Bool} : bitwise (Function.swap f) = Func
tion.swap (bitwise f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.bitwise_zero_left`：bitwise_zero_left (m : Nat) : bitwise f 0 m = if 
f false true then m else 0
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.bitwise_bit'`：bitwise_bit' {f : Bool -> Bool -> Bool} (a : Bool) (m 
: Nat) (b : Bool) (n : Nat) (ham : m = 0 -> a = true) (hbn : n = 0 -> b = true) 
: bitw…
-/
theorem bitwise_swap {f : Bool → Bool → Bool} :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n
  simp only [Function.swap]
  induction m using Nat.binaryRec' generalizing n with
  | zero => simp
  | bit bm m hm ihm =>
    induction n using Nat.binaryRec' with
    | zero => simp
    | bit bn n hn => rw [bitwise_bit' _ _ _ _ hm hn, bitwise_bit' _ _ _ _ hn hm, ihm]

/-- If `f` is a commutative operation on bools such that `f false false = false`, then `bitwise f`
is also commutative. -/
/-
**Nat.bitwise_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：bitwise_comm {f : Bool -> Bool -> Bool} (hf : forall b b', f b b' = f b' b
) (n m : Nat) : bitwise f n m = bitwise f m n
参数：hf : forall b b', f b b' = f b' b；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.bitwise_swap`：bitwise_swap {f : Bool -> Bool -> Bool} : bitwise (Fun
ction.swap f) = Function.swap (bitwise f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
If `f` is a commutative operation on bools such that `f false false = false`, th
en `bitwise f`
is also commutative.
-/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b) (n m : ℕ) :
    bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
    bitwise f = bitwise (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise f) := bitwise_swap
/-
**Nat.lor_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lor_comm (n m : Nat) : n ||| m = m ||| n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitwise_comm`：bitwise_comm {f : Bool -> Bool -> Bool} (hf : forall b
 b', f b b' = f b' b) (n m : Nat) : bitwise f n m = bitwise f m n
· 使用定理 `Bool.or_comm`：∀ (x y : Bool), (x || y) = (y || x)
-/
theorem lor_comm (n m : ℕ) : n ||| m = m ||| n :=
  bitwise_comm Bool.or_comm n m
/-
**Nat.land_comm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：land_comm (n m : Nat) : n &&& m = m &&& n
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitwise_comm`：bitwise_comm {f : Bool -> Bool -> Bool} (hf : forall b
 b', f b b' = f b' b) (n m : Nat) : bitwise f n m = bitwise f m n
· 使用定理 `Bool.and_comm`：∀ (x y : Bool), (x && y) = (y && x)
-/
theorem land_comm (n m : ℕ) : n &&& m = m &&& n :=
  bitwise_comm Bool.and_comm n m
/-
**Nat.and_two_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：and_two_pow (n i : Nat) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i
参数：n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_of_testBit_eq`：∀ {x y : ℕ}, (∀ (i : ℕ), x.testBit i = y.testBit i
) → x = y
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.testBit_and`：∀ (x y i : ℕ), (x &&& y).testBit i = (x.testBit i && y.
testBit i)
· 使用定理 `Nat.testBit_two_pow_self`：∀ {n : ℕ}, (2 ^ n).testBit n = true
· 使用定理 `Bool.and_true`：∀ (b : Bool), (b && true) = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.zero_testBit`：∀ (i : ℕ), Nat.testBit 0 i = false
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.and_self`：∀ (b : Bool), (b && b) = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.testBit_two_pow_of_ne`：∀ {n m : ℕ}, n ≠ m → (2 ^ n).testBit m = fals
e
· 使用定理 `Bool.and_false`：∀ (b : Bool), (b && false) = false
-/
lemma and_two_pow (n i : ℕ) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i := by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [testBit_two_pow_of_ne hij]
  · simp [testBit_two_pow_of_ne hij]
/-
**Nat.two_pow_and** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_pow_and (n i : Nat) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat
参数：n i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.land_comm`：land_comm (n m : Nat) : n &&& m = m &&& n
· 使用引理 `Nat.and_two_pow`：and_two_pow (n i : Nat) : n &&& 2 ^ i = (n.testBit i).t
oNat * 2 ^ i
-/
lemma two_pow_and (n i : ℕ) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat := by
  rw [mul_comm, land_comm, and_two_pow]

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
macro "bitwise_assoc_tac" : tactic => set_option hygiene false in `(tactic| (
  induction n using Nat.binaryRec generalizing m k with | zero => simp | bit b n hn => ?_
  induction m using Nat.binaryRec with | zero => simp | bit b' m hm => ?_
  induction k using Nat.binaryRec <;>
    simp [hn, Bool.or_assoc, Bool.and_assoc, Bool.bne_eq_xor]))

/-
**Nat.land_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：land_assoc (n m k : Nat) : (n &&& m) &&& k = n &&& (m &&& k)
参数：n m k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_and`：∀ (x : ℕ), 0 &&& x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.and_zero`：∀ (x : ℕ), x &&& 0 = 0
· 使用定理 `Nat.land_bit`：land_bit : forall a m b n, bit a m &&& bit b n = bit (a &&
 b) (m &&& n)
· 使用定理 `Bool.and_assoc`：∀ (a b c : Bool), (a && b && c) = (a && (b && c))
-/
theorem land_assoc (n m k : ℕ) : (n &&& m) &&& k = n &&& (m &&& k) := by bitwise_assoc_tac
/-
**Nat.lor_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lor_assoc (n m k : Nat) : (n ||| m) ||| k = n ||| (m ||| k)
参数：n m k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_or`：∀ (x : ℕ), 0 ||| x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.or_zero`：∀ (x : ℕ), x ||| 0 = x
· 使用定理 `Nat.lor_bit`：lor_bit : forall a m b n, bit a m ||| bit b n = bit (a || b
) (m ||| n)
· 使用定理 `Bool.or_assoc`：∀ (a b c : Bool), (a || b || c) = (a || (b || c))
-/
theorem lor_assoc (n m k : ℕ) : (n ||| m) ||| k = n ||| (m ||| k) := by bitwise_assoc_tac
/-
**Nat.xor_trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_trichotomy {a b c : Nat} (h : a ^^^ b ^^^ c != 0) : b ^^^ c < a ∨ c ^^
^ a < b ∨ a ^^^ b < c
参数：h : a ^^^ b ^^^ c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.xor_comm`：∀ (x y : ℕ), x ^^^ y = y ^^^ x
· 使用定理 `Nat.xor_xor_cancel_right`：∀ (x y : ℕ), x ^^^ y ^^^ y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.xor_assoc`：∀ (x y z : ℕ), x ^^^ y ^^^ z = x ^^^ (y ^^^ z)
· 使用定理 `Nat.xor_xor_cancel_left`：∀ (x y : ℕ), x ^^^ (x ^^^ y) = y
· 使用定理 `Nat.exists_most_significant_bit`：exists_most_significant_bit {n : Nat} (
h : n != 0) : exists i, testBit n i = true ∧ forall j, i < j -> testBit n j = fa
lse
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.eq_false_eq_not_eq_true`：eq_false_eq_not_eq_true (b : Bool) : (¬(b 
= true)) = (b = false)
· 使用定理 `Nat.testBit_xor`：∀ (x y i : ℕ), (x ^^^ y).testBit i = (x.testBit i ^^ y.
testBit i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.lt_of_testBit`：lt_of_testBit {n m : Nat} (i : Nat) (hn : testBit n i
 = false) (hm : testBit m i = true) (hnm : forall j, i < j -> testBit n j = test
Bit m j…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Bool.bne_false`：∀ (b : Bool), (b != false) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem xor_trichotomy {a b c : ℕ} (h : a ^^^ b ^^^ c ≠ 0) :
    b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c := by
  set v := a ^^^ b ^^^ c with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [Nat.xor_comm c, Nat.xor_xor_cancel_right]
  have hbc : b ^^^ c = a ^^^ v := by
    rw [← Nat.xor_assoc, Nat.xor_xor_cancel_left]
  have hca : c ^^^ a = b ^^^ v := by
    rw [hv, Nat.xor_assoc, Nat.xor_comm a, ← Nat.xor_assoc, Nat.xor_xor_cancel_left]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit h
  have : testBit a i ∨ testBit b i ∨ testBit c i := by
    contrapose! hi
    simp_rw [Bool.eq_false_eq_not_eq_true] at hi ⊢
    rw [testBit_xor, testBit_xor, hi.1, hi.2.1, hi.2.2]
    rfl
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
  -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
  obtain h | h | h := this
  on_goal 1 => left; rw [hbc]
  on_goal 2 => right; left; rw [hca]
  on_goal 3 => right; right; rw [hab]
  all_goals
    refine lt_of_testBit i ?_ h fun j hj => ?_
    · rw [testBit_xor, h, hi]
      rfl
    · simp only [testBit_xor, hi' _ hj, Bool.bne_false]
/-
**Nat.lt_xor_cases** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：lt_xor_cases {a b c : Nat} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c
参数：h : a < b ^^^ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.xor_trichotomy`：xor_trichotomy {a b c : Nat} (h : a ^^^ b ^^^ c != 0
) : b ^^^ c < a ∨ c ^^^ a < b ∨ a ^^^ b < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.xor_ne_zero_iff`：∀ {x y : ℕ}, x ^^^ y ≠ 0 ↔ x ≠ y
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.xor_assoc`：∀ (x y z : ℕ), x ^^^ y ^^^ z = x ^^^ (y ^^^ z)
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用定理 `Nat.xor_comm`：∀ (x y : ℕ), x ^^^ y = y ^^^ x
-/
theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c := by
  obtain ha | hb | hc := xor_trichotomy <| Nat.xor_assoc _ _ _ ▸ xor_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| Nat.xor_comm _ _ ▸ hb, Or.inr hc]

@[simp]
/-
**Nat.xor_mod_two_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_mod_two_eq {m n : Nat} : (m ^^^ n) % 2 = (m + n) % 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.testBit_zero`：∀ (x : ℕ), x.testBit 0 = decide (x % 2 = 1)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `Bool.decide_iff_dist`：∀ (p q : Prop) [dpq : Decidable (p ↔ q)] [dp : Dec
idable p] [dq : Decidable q], decide (p ↔ q) = (decide p == decide q)
· 使用定理 `Bool.not_eq_false'`：∀ (b : Bool), ((!b) = false) = (b = true)
· 使用定理 `instLawfulBEqBool`：LawfulBEq Bool
-/
theorem xor_mod_two_eq {m n : ℕ} : (m ^^^ n) % 2 = (m + n) % 2 := by
  by_cases h : (m + n) % 2 = 0
  · simp only [h, mod_two_eq_zero_iff_testBit_zero, testBit_zero, xor_mod_two_eq_one, decide_not,
      Bool.decide_iff_dist, Bool.not_eq_false', beq_iff_eq, decide_eq_decide]
    lia
  · simp only [mod_two_ne_zero] at h
    simp only [h, xor_mod_two_eq_one]
    lia

@[simp]
/-
**Nat.even_xor** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：even_xor {m n : Nat} : Even (m ^^^ n) ↔ (Even m ↔ Even n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.xor_mod_two_eq`：xor_mod_two_eq {m n : Nat} : (m ^^^ n) % 2 = (m + n)
 % 2
-/
theorem even_xor {m n : ℕ} : Even (m ^^^ n) ↔ (Even m ↔ Even n) := by
  simp only [even_iff, xor_mod_two_eq]
  lia

@[simp]
/-
**Nat.xor_one_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_one_of_even {n : Nat} (h : Even n) : n ^^^ 1 = n + 1
参数：h : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_1`：∀ (f : Bool → Bool
 → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = tr
ue then m else 0     else       if m = 0 t…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `Bool.bne_true`：∀ (b : Bool), (b != true) = !b
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
· 使用定理 `Bool.bne_false`：∀ (b : Bool), (b != false) = b
· 使用引理 `Nat.div_two_mul_two_of_even`：div_two_mul_two_of_even : Even n -> n / 2 *
 2 = n
-/
theorem xor_one_of_even {n : ℕ} (h : Even n) : n ^^^ 1 = n + 1 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp +instances [HXor.hXor, instXorOp, xor, bitwise, even_iff.mp h, ← mul_two,
      div_two_mul_two_of_even h]

@[simp]
/-
**Nat.xor_one_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_one_of_odd {n : Nat} (h : Odd n) : n ^^^ 1 = n - 1
参数：h : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_odd_zero`：¬Odd 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.Data.Nat.Bitwise.0.Nat.bitwise.eq_1`：∀ (f : Bool → Bool
 → Bool) (n m : ℕ),   Nat.bitwise f n m =     if n = 0 then if f false true = tr
ue then m else 0     else       if m = 0 t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bitwise_zero_right`：bitwise_zero_right (n : Nat) : bitwise f n 0 = i
f f true false then n else 0
-/
theorem xor_one_of_odd {n : ℕ} (h : Odd n) : n ^^^ 1 = n - 1 := by
  cases n with
  | zero =>
    exact not_odd_zero h |>.elim
  | succ n =>
    simp +instances only [HXor.hXor, instXorOp, xor, bitwise, reduceDiv, bitwise_zero_right]
    grind

/-- The xor of the numbers from 0 to n can be easily calculated using `n mod 4`. -/
/-
**Nat.xor_range** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：xor_range (n : Nat) : (List.range (n + 1)).foldl (· ^^^ ·) 0 = match Fin.o
fNat 4 n with | 0 => n | 1 => 1 | 2 => n + 1 | 3 => 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.xor_self`：∀ (x : ℕ), x ^^^ x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.val_ofNat`：∀ (n : ℕ) [inst : NeZero n] (a : ℕ), ↑(Fin.ofNat n a) = a
 % n
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `Fin.ofNat_add`：∀ {n : ℕ} [inst : NeZero n] (x : ℕ) (y : Fin n), Fin.ofNa
t n x + y = Fin.ofNat n (x + ↑y)
· 使用定理 `List.foldl_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : β
 → α → β} {b : β},   List.foldl f b (a :: l) = List.foldl f (f b a) l
· 使用定理 `List.foldl_nil`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → α} {b : α},
 List.foldl f b [] = b
· 使用定理 `Fin.zero_add`：∀ {n : ℕ} [inst : NeZero n] (k : Fin n), 0 + k = k
· 使用定理 `Nat.xor_one_of_even`：xor_one_of_even {n : Nat} (h : Even n) : n ^^^ 1 = 
n + 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `Nat.dvd_eq_true_of_mod_eq_zero`：∀ {m n : ℕ}, (n % m == 0) = true → (m ∣ 
n) = True
· 使用定理 `Nat.xor_xor_cancel_left`：∀ (x y : ℕ), x ^^^ (x ^^^ y) = y
· 使用定理 `Nat.xor_comm`：∀ (x y : ℕ), x ^^^ y = y ^^^ x
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.zero_xor`：∀ (x : ℕ), 0 ^^^ x = x

--- 原说明 ---
The xor of the numbers from 0 to n can be easily calculated using `n mod 4`.
-/
theorem xor_range (n : ℕ) : (List.range (n + 1)).foldl (· ^^^ ·) 0 =
    match Fin.ofNat 4 n with | 0 => n | 1 => 1 | 2 => n + 1 | 3 => 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    nth_rw 3 [← show Fin.ofNat 4 1 = (1 : ℕ) from Fin.val_ofNat ..]
    rw [List.range_succ, List.foldl_append, ih, ← Fin.ofNat_add, List.foldl_cons, List.foldl_nil]
    match h : Fin.ofNat 4 n with
    | 0 =>
      rw [Fin.zero_add, ← xor_one_of_even <| even_iff.mpr ?_, xor_xor_cancel_left]
      rw [← @mod_mod_of_dvd _ 4 _ <| by simp, ← Fin.val_ofNat 4, h]
      rfl
    | 1 =>
      rw [Nat.xor_comm]
      refine xor_one_of_even <| even_iff.mpr ?_
      rw [add_mod, ← @mod_mod_of_dvd _ 4 n <| by simp, ← Fin.val_ofNat 4, h]
      rfl
    | 2 =>
      apply Nat.xor_self
    | 3 =>
      apply zero_xor
/-
**Nat.shiftLeft_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：shiftLeft_lt {x n m : Nat} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m)
参数：h : x < 2 ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.shiftLeft_eq`：∀ (a b : ℕ), a <<< b = a * 2 ^ b
· 使用定理 `Nat.pow_add`：∀ (a m n : ℕ), a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Nat.mul_lt_mul_right`：∀ {a b c : ℕ}, 0 < a → (b * a < c * a ↔ b < c)
· 使用定理 `Nat.two_pow_pos`：∀ (w : ℕ), 0 < 2 ^ w
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma shiftLeft_lt {x n m : ℕ} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m) := by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

/-- Note that the LHS is the expression used within `Std.BitVec.append`, hence the name. -/
/-
**Nat.append_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：append_lt {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m) : y <<< n ||| x < 2 
^ (n + m)
参数：hx : x < 2 ^ n；hy : y < 2 ^ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.bitwise_lt_two_pow`：∀ {x n y : ℕ} {f : Bool → Bool → Bool}, x < 2 ^ 
n → y < 2 ^ n → Nat.bitwise f x y < 2 ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Nat.shiftLeft_lt`：shiftLeft_lt {x n m : Nat} (h : x < 2 ^ n) : x <<< m <
 2 ^ (n + m)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
Note that the LHS is the expression used within `Std.BitVec.append`, hence the n
ame.
-/
lemma append_lt {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m) : y <<< n ||| x < 2 ^ (n + m) := by
  apply bitwise_lt_two_pow
  · rw [add_comm]; apply shiftLeft_lt hy
  · apply lt_of_lt_of_le hx <| Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

end Nat

