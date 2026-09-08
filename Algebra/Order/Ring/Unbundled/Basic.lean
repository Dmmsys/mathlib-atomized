/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Monoid.NatCast
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Tauto

/-!
# Basic facts for ordered rings and semirings

This file develops the basics of ordered (semi)rings in an unbundled fashion for later use with
the bundled classes from `Mathlib/Algebra/Order/Ring/Defs.lean`.

## Generality

Each section is labelled with a corresponding bundled ordered ring typeclass in mind. Mixins for
relating the order structures and ring structures are added as needed.

## TODO

The mixin assumptions can be relaxed in most cases.
-/

public section

assert_not_exists IsOrderedMonoid MonoidHom

open Function

universe u

variable {R : Type u} {α : Type*}

/-! Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/


/-
**add_one_le_two_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R} (a1
 : 1 <= a) : a + 1 <= 2 * a
参数：a1 : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n

--- 原说明 ---
Note that `OrderDual` does not satisfy any of the ordered ring typeclasses due t
o the
`zero_le_one` field.
-/
theorem add_one_le_two_mul [LE R] [NonAssocSemiring R] [AddLeftMono R] {a : R}
    (a1 : 1 ≤ a) : a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := by gcongr
    _ = 2 * a := (two_mul _).symm

section OrderedSemiring

variable [Semiring R] [Preorder R] {a b c d : R}

/-
**add_le_mul_two_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R] (a2 :
 2 <= a) (b0 : 0 <= b) : a + (2 + b) <= a * (2 + b)
参数：a2 : 2 <= a；b0 : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) := by
      gcongr; exact le_mul_of_one_le_left b0 <| one_le_two.trans a2
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]
/-
**mul_le_mul_of_nonpos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R] [AddRightMono R
] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) : c * a <= c * b
参数：h : b <= a；hc : c <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `add_le_of_nonpos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, b ≤ 0 → b + a ≤ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := d * b + d * a) ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ ≤ d * a := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]
/-
**mul_le_mul_of_nonpos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R] [AddRightMono 
R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) : a * c <= b * c
参数：h : b <= a；hc : c <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `add_le_of_nonpos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, b ≤ 0 → b + a ≤ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_le_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc
  refine le_of_add_le_add_right (a := b * d + a * d) ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ ≤ a * d := by gcongr; exact hcd.trans_le <| add_le_of_nonpos_left hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]
/-
**mul_nonneg_of_nonpos_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [AddRightM
ono R] [AddRightReflectLE R] (ha : a <= 0) (hb : b <= 0) : 0 <= a * b
参数：ha : a <= 0；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
-/
theorem mul_nonneg_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonpos_right ha hb
/-
**mul_le_mul_of_nonneg_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMon
o R] [AddRightMono R] [AddRightReflectLE R] (hca : c <= a) (hbd : b <= d) (hc : 
0 <= c) (hb : b <= 0) : a * b <= c * d
参数：hca : c <= a；hbd : b <= d；hc : 0 <= c；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
theorem mul_le_mul_of_nonneg_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (hc : 0 ≤ c) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| by gcongr; assumption
/-
**mul_le_mul_of_nonneg_of_nonpos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMo
no R] [AddRightMono R] [AddRightReflectLE R] (hca : c <= a) (hbd : b <= d) (ha :
 0 <= a) (hd : d <= 0) : a * b <= c * d
参数：hca : c <= a；hbd : b <= d；ha : 0 <= a；hd : d <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
-/
theorem mul_le_mul_of_nonneg_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd
/-
**mul_le_mul_of_nonpos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMon
o R] [AddRightMono R] [AddRightReflectLE R] (hac : a <= c) (hdb : d <= b) (hc : 
c <= 0) (hb : 0 <= b) : a * b <= c * d
参数：hac : a <= c；hdb : d <= b；hc : c <= 0；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
-/
theorem mul_le_mul_of_nonpos_of_nonneg [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hac : a ≤ c) (hdb : d ≤ b) (hc : c ≤ 0) (hb : 0 ≤ b) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_right hac hb).trans <| mul_le_mul_of_nonpos_left hdb hc
/-
**mul_le_mul_of_nonpos_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMo
no R] [AddRightMono R] [AddRightReflectLE R] (hca : c <= a) (hbd : b <= d) (ha :
 0 <= a) (hd : d <= 0) : a * b <= c * d
参数：hca : c <= a；hbd : b <= d；ha : 0 <= a；hd : d <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
-/
theorem mul_le_mul_of_nonpos_of_nonneg' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonneg_left hbd ha).trans <| mul_le_mul_of_nonpos_right hca hd
/-
**mul_le_mul_of_nonpos_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMon
o R] [AddRightMono R] [AddRightReflectLE R] (hca : c <= a) (hdb : d <= b) (hc : 
c <= 0) (hb : b <= 0) : a * b <= c * d
参数：hca : c <= a；hdb : d <= b；hc : c <= 0；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
-/
theorem mul_le_mul_of_nonpos_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≤ 0) (hb : b ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_right hca hb).trans <| mul_le_mul_of_nonpos_left hdb hc
/-
**mul_le_mul_of_nonpos_of_nonpos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMo
no R] [AddRightMono R] [AddRightReflectLE R] (hca : c <= a) (hdb : d <= b) (ha :
 a <= 0) (hd : d <= 0) : a * b <= c * d
参数：hca : c <= a；hdb : d <= b；ha : a <= 0；hd : d <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
-/
theorem mul_le_mul_of_nonpos_of_nonpos' [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≤ 0) (hd : d ≤ 0) : a * b ≤ c * d :=
  (mul_le_mul_of_nonpos_left hdb ha).trans <| mul_le_mul_of_nonpos_right hca hd

/-- Variant of `mul_le_of_le_one_left` for `b` non-positive instead of non-negative. -/
/-
**le_mul_of_le_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMono R] [AddRightMono R] [A
ddRightReflectLE R] (hb : b <= 0) (h : a <= 1) : b <= a * b
参数：hb : b <= 0；h : a <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…

--- 原说明 ---
Variant of `mul_le_of_le_one_left` for `b` non-positive instead of non-negative.
-/
theorem le_mul_of_le_one_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : a ≤ 1) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative. -/
/-
**mul_le_of_one_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R] [AddRightMono R] [A
ddRightReflectLE R] (hb : b <= 0) (h : 1 <= a) : a * b <= b
参数：hb : b <= 0；h : 1 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…

--- 原说明 ---
Variant of `le_mul_of_one_le_left` for `b` non-positive instead of non-negative.
-/
theorem mul_le_of_one_le_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hb : b ≤ 0) (h : 1 ≤ a) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonpos_right h hb

/-- Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative. -/
/-
**le_mul_of_le_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R] [AddRightMono R] [
AddRightReflectLE R] (ha : a <= 0) (h : b <= 1) : a <= a * b
参数：ha : a <= 0；h : b <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …

--- 原说明 ---
Variant of `mul_le_of_le_one_right` for `a` non-positive instead of non-negative
.
-/
theorem le_mul_of_le_one_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : b ≤ 1) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

/-- Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative. -/
/-
**mul_le_of_one_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R] [AddRightMono R] [
AddRightReflectLE R] (ha : a <= 0) (h : 1 <= b) : a * b <= a
参数：ha : a <= 0；h : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …

--- 原说明 ---
Variant of `le_mul_of_one_le_right` for `a` non-positive instead of non-negative
.
-/
theorem mul_le_of_one_le_right [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (ha : a ≤ 0) (h : 1 ≤ b) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonpos_left h ha

section Monotone

variable [Preorder α] {f g : α → R}

/-
**antitone_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_mul_left [ExistsAddOfLE R] [PosMulMono R] [AddRightMono R] [AddRi
ghtReflectLE R] {a : R} (ha : a <= 0) : Antitone (a * ·)
参数：ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonpos_left`：mul_le_mul_of_nonpos_left [ExistsAddOfLE R] [
PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0) 
: c * a <= c * …
-/
theorem antitone_mul_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone (a * ·) := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha
/-
**antitone_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_mul_right [ExistsAddOfLE R] [MulPosMono R] [AddRightMono R] [AddR
ightReflectLE R] {a : R} (ha : a <= 0) : Antitone fun x => x * a
参数：ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonpos_right`：mul_le_mul_of_nonpos_right [ExistsAddOfLE R]
 [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (h : b <= a) (hc : c <= 0
) : a * c <= b *…
-/
theorem antitone_mul_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a : R} (ha : a ≤ 0) : Antitone fun x => x * a := fun _ _ b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha
/-
**Monotone.const_mul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R] [AddRightMon
o R] [AddRightReflectLE R] (hf : Monotone f) (ha : a <= 0) : Antitone fun x => a
 * f x
参数：hf : Monotone f；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `antitone_mul_left`：antitone_mul_left [ExistsAddOfLE R] [PosMulMono R] [A
ddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone (a * ·)
-/
theorem Monotone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => a * f x :=
  (antitone_mul_left ha).comp_monotone hf
/-
**Monotone.mul_const_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [AddRightMon
o R] [AddRightReflectLE R] (hf : Monotone f) (ha : a <= 0) : Antitone fun x => f
 x * a
参数：hf : Monotone f；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `antitone_mul_right`：antitone_mul_right [ExistsAddOfLE R] [MulPosMono R] 
[AddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone fun x =>
 x * a
-/
theorem Monotone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (ha : a ≤ 0) : Antitone fun x => f x * a :=
  (antitone_mul_right ha).comp_monotone hf
/-
**Antitone.const_mul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R] [AddRightMon
o R] [AddRightReflectLE R] (hf : Antitone f) (ha : a <= 0) : Monotone fun x => a
 * f x
参数：hf : Antitone f；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `antitone_mul_left`：antitone_mul_left [ExistsAddOfLE R] [PosMulMono R] [A
ddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone (a * ·)
-/
theorem Antitone.const_mul_of_nonpos [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => a * f x :=
  (antitone_mul_left ha).comp hf
/-
**Antitone.mul_const_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R] [AddRightMon
o R] [AddRightReflectLE R] (hf : Antitone f) (ha : a <= 0) : Monotone fun x => f
 x * a
参数：hf : Antitone f；ha : a <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Antit
one…
· 使用定理 `antitone_mul_right`：antitone_mul_right [ExistsAddOfLE R] [MulPosMono R] 
[AddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone fun x =>
 x * a
-/
theorem Antitone.mul_const_of_nonpos [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (ha : a ≤ 0) : Monotone fun x => f x * a :=
  (antitone_mul_right ha).comp hf
/-
**Antitone.mul_monotone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R] [Add
RightMono R] [AddRightReflectLE R] (hf : Antitone f) (hg : Monotone g) (hf₀ : fo
rall x, f x <= 0) (hg₀ : forall x, 0 <= g x) : Antitone (f * g)
参数：hf : Antitone f；hg : Monotone g；hf₀ : forall x, f x <= 0；hg₀ : forall x, 0 <=
 g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonpos_of_nonneg`：mul_le_mul_of_nonpos_of_nonneg [ExistsAd
dOfLE R] [MulPosMono R] [PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h
ac : a <= c) (hdb : …
-/
theorem Antitone.mul_monotone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Monotone g) (hf₀ : ∀ x, f x ≤ 0)
    (hg₀ : ∀ x, 0 ≤ g x) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonpos_of_nonneg (hf h) (hg h) (hf₀ _) (hg₀ _)
/-
**Monotone.mul_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.mul_antitone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R] [Add
RightMono R] [AddRightReflectLE R] (hf : Monotone f) (hg : Antitone g) (hf₀ : fo
rall x, 0 <= f x) (hg₀ : forall x, g x <= 0) : Antitone (f * g)
参数：hf : Monotone f；hg : Antitone g；hf₀ : forall x, 0 <= f x；hg₀ : forall x, g x 
<= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_of_nonpos`：mul_le_mul_of_nonneg_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h
ca : c <= a) (hbd : …
-/
theorem Monotone.mul_antitone [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Monotone f) (hg : Antitone g) (hf₀ : ∀ x, 0 ≤ f x)
    (hg₀ : ∀ x, g x ≤ 0) : Antitone (f * g) := fun _ _ h =>
  mul_le_mul_of_nonneg_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)
/-
**Antitone.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R] [AddRightMono
 R] [AddRightReflectLE R] (hf : Antitone f) (hg : Antitone g) (hf₀ : forall x, f
 x <= 0) (hg₀ : forall x, g x <= 0) : Monotone (f * g)
参数：hf : Antitone f；hg : Antitone g；hf₀ : forall x, f x <= 0；hg₀ : forall x, g x 
<= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonpos_of_nonpos`：mul_le_mul_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [PosMulMono R] [AddRightMono R] [AddRightReflectLE R] (h
ca : c <= a) (hdb : …
-/
theorem Antitone.mul [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hf : Antitone f) (hg : Antitone g) (hf₀ : ∀ x, f x ≤ 0) (hg₀ : ∀ x, g x ≤ 0) :
    Monotone (f * g) := fun _ _ h => mul_le_mul_of_nonpos_of_nonpos (hf h) (hg h) (hf₀ _) (hg₀ _)

end Monotone
end OrderedSemiring

section OrderedCommRing

section StrictOrderedSemiring

variable [Semiring R] [PartialOrder R] {a b c d : R}

/-
**lt_two_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_two_mul_self [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)] [
AddLeftStrictMono R] (ha : 0 < a) : a < 2 * a
参数：1 : R；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_mul_of_one_lt_left`：lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 
0 < b) (h : 1 < a) : b < a * b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
-/
theorem lt_two_mul_self [ZeroLEOneClass R] [MulPosStrictMono R] [NeZero (1 : R)]
    [AddLeftStrictMono R] (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha one_lt_two
/-
**mul_lt_mul_of_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightStr
ictMono R] [AddRightReflectLT R] (h : b < a) (hc : c < 0) : c * a < c * b
参数：h : b < a；hc : c < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `add_lt_of_neg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, b < 0 → b + a < a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : c * a < c * b := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (d * b + d * a)).1 ?_
  calc
    _ = d * b := by rw [add_left_comm, ← add_mul, ← hcd, zero_mul, add_zero]
    _ < d * a := mul_lt_mul_of_pos_left h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← add_mul, ← hcd, zero_mul, zero_add]
/-
**mul_lt_mul_of_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightSt
rictMono R] [AddRightReflectLT R] (h : b < a) (hc : c < 0) : a * c < b * c
参数：h : b < a；hc : c < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `add_lt_of_neg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : L
T α] [AddRightStrictMono α] (a : α) {b : α}, b < 0 → b + a < a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (h : b < a) (hc : c < 0) : a * c < b * c := by
  obtain ⟨d, hcd⟩ := exists_add_of_le hc.le
  refine (add_lt_add_iff_right (b * d + a * d)).1 ?_
  calc
    _ = b * d := by rw [add_left_comm, ← mul_add, ← hcd, mul_zero, add_zero]
    _ < a * d := mul_lt_mul_of_pos_right h <| hcd.trans_lt <| add_lt_of_neg_left _ hc
    _ = _ := by rw [← add_assoc, ← mul_add, ← hcd, mul_zero, zero_add]
/-
**mul_pos_of_neg_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightStri
ctMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b
参数：ha : a < 0；hb : b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_lt_mul_of_neg_right`：mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulP
osStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c
 < 0) : a * c…
-/
theorem mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b : R} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_neg_right ha hb

/-- Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive. -/
/-
**lt_mul_of_lt_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightStri
ctMono R] [AddRightReflectLT R] (hb : b < 0) (h : a < 1) : b < a * b
参数：hb : b < 0；h : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_neg_right`：mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulP
osStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c
 < 0) : a * c…

--- 原说明 ---
Variant of `mul_lt_of_lt_one_left` for `b` negative instead of positive.
-/
theorem lt_mul_of_lt_one_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : a < 1) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive. -/
/-
**mul_lt_of_one_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightStri
ctMono R] [AddRightReflectLT R] (hb : b < 0) (h : 1 < a) : a * b < b
参数：hb : b < 0；h : 1 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_neg_right`：mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulP
osStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c
 < 0) : a * c…

--- 原说明 ---
Variant of `lt_mul_of_one_lt_left` for `b` negative instead of positive.
-/
theorem mul_lt_of_one_lt_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hb : b < 0) (h : 1 < a) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_neg_right h hb

/-- Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive. -/
/-
**lt_mul_of_lt_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightStr
ictMono R] [AddRightReflectLT R] (ha : a < 0) (h : b < 1) : a < a * b
参数：ha : a < 0；h : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_neg_left`：mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMul
StrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c <
 0) : c * a …

--- 原说明 ---
Variant of `mul_lt_of_lt_one_right` for `a` negative instead of positive.
-/
theorem lt_mul_of_lt_one_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : b < 1) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

/-- Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive. -/
/-
**mul_lt_of_one_lt_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightStr
ictMono R] [AddRightReflectLT R] (ha : a < 0) (h : 1 < b) : a * b < a
参数：ha : a < 0；h : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_lt_mul_of_neg_left`：mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMul
StrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c <
 0) : c * a …

--- 原说明 ---
Variant of `lt_mul_of_lt_one_right` for `a` negative instead of positive.
-/
theorem mul_lt_of_one_lt_right [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (ha : a < 0) (h : 1 < b) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_neg_left h ha

section Monotone

variable [Preorder α] {f : α → R}

/-
**strictAnti_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightStrict
Mono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : StrictAnti (a * ·)
参数：ha : a < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_neg_left`：mul_lt_mul_of_neg_left [ExistsAddOfLE R] [PosMul
StrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c <
 0) : c * a …
-/
theorem strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti (a * ·) := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha
/-
**strictAnti_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightStric
tMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : StrictAnti fun x => x * a
参数：ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_neg_right`：mul_lt_mul_of_neg_right [ExistsAddOfLE R] [MulP
osStrictMono R] [AddRightStrictMono R] [AddRightReflectLT R] (h : b < a) (hc : c
 < 0) : a * c…
-/
theorem strictAnti_mul_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a : R} (ha : a < 0) : StrictAnti fun x => x * a := fun _ _ b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha
/-
**StrictMono.const_mul_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R] [AddRig
htStrictMono R] [AddRightReflectLT R] (hf : StrictMono f) (ha : a < 0) : StrictA
nti fun x => a * f x
参数：hf : StrictMono f；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.comp_strictMono`：StrictAnti.comp_strictMono (hg : StrictAnti 
g) (hf : StrictMono f) : StrictAnti (g ∘ f)
· 使用定理 `strictAnti_mul_left`：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrict
Mono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : Stri
ctAnti (a…
-/
theorem StrictMono.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => a * f x :=
  (strictAnti_mul_left ha).comp_strictMono hf
/-
**StrictMono.mul_const_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R] [AddRig
htStrictMono R] [AddRightReflectLT R] (hf : StrictMono f) (ha : a < 0) : StrictA
nti fun x => f x * a
参数：hf : StrictMono f；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.comp_strictMono`：StrictAnti.comp_strictMono (hg : StrictAnti 
g) (hf : StrictMono f) : StrictAnti (g ∘ f)
· 使用定理 `strictAnti_mul_right`：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStri
ctMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : St
rictAnti f…
-/
theorem StrictMono.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictMono f) (ha : a < 0) : StrictAnti fun x => f x * a :=
  (strictAnti_mul_right ha).comp_strictMono hf
/-
**StrictAnti.const_mul_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R] [AddRig
htStrictMono R] [AddRightReflectLT R] (hf : StrictAnti f) (ha : a < 0) : StrictM
ono fun x => a * f x
参数：hf : StrictAnti f；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictAn…
· 使用定理 `strictAnti_mul_left`：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrict
Mono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : Stri
ctAnti (a…
-/
theorem StrictAnti.const_mul_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => a * f x :=
  (strictAnti_mul_left ha).comp hf
/-
**StrictAnti.mul_const_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictAnti.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R] [AddRig
htStrictMono R] [AddRightReflectLT R] (hf : StrictAnti f) (ha : a < 0) : StrictM
ono fun x => f x * a
参数：hf : StrictAnti f；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictAn…
· 使用定理 `strictAnti_mul_right`：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStri
ctMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : St
rictAnti f…
-/
theorem StrictAnti.mul_const_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    (hf : StrictAnti f) (ha : a < 0) : StrictMono fun x => f x * a :=
  (strictAnti_mul_right ha).comp hf

end Monotone

/-- Binary **rearrangement inequality**. -/
/-
**mul_add_mul_le_mul_add_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R] [AddLeftMono R
] [AddLeftReflectLE R] (hab : a <= b) (hcd : c <= d) : a * d + b * c <= a * c + 
b * d
参数：hab : a <= b；hcd : c <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonneg_add_of_le`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 
: Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLE α],   a ≤ b → ∃ c, 0
 ≤ c ∧ a + c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a

--- 原说明 ---
Binary **rearrangement inequality**.
-/
lemma mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  assumption

/-- Binary **rearrangement inequality**. -/
/-
**mul_add_mul_le_mul_add_mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R] [AddLeftMono 
R] [AddLeftReflectLE R] (hba : b <= a) (hdc : d <= c) : a * d + b * c <= a * c +
 b * d
参数：hba : b <= a；hdc : d <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `mul_add_mul_le_mul_add_mul`：mul_add_mul_le_mul_add_mul [ExistsAddOfLE R]
 [MulPosMono R] [AddLeftMono R] [AddLeftReflectLE R] (hab : a <= b) (hcd : c <= 
d) : a * d + b *…

--- 原说明 ---
Binary **rearrangement inequality**.
-/
lemma mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

variable [AddLeftReflectLT R]

/-- Binary strict **rearrangement inequality**. -/
/-
**mul_add_mul_lt_mul_add_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R] [AddLeft
StrictMono R] (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d
参数：hab : a < b；hcd : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pos_add_of_lt'`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLT α],   a < b → ∃ c, 0 <
 c ∧ a + c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a

--- 原说明 ---
Binary strict **rearrangement inequality**.
-/
lemma mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  exact hd

/-- Binary **rearrangement inequality**. -/
/-
**mul_add_mul_lt_mul_add_mul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE R] [MulPosStrictMono R] [AddLef
tStrictMono R] (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d
参数：hba : b < a；hdc : d < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `mul_add_mul_lt_mul_add_mul`：mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R]
 [MulPosStrictMono R] [AddLeftStrictMono R] (hab : a < b) (hcd : c < d) : a * d 
+ b * c < a * c …

--- 原说明 ---
Binary **rearrangement inequality**.
-/
lemma mul_add_mul_lt_mul_add_mul' [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hba : b < a) (hdc : d < c) : a * d + b * c < a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end StrictOrderedSemiring

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] {a b c : R}

/-
**nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg [MulPosStrictMono R] 
[PosMulStrictMono R] (hab : 0 <= a * b) : 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
参数：hab : 0 <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Decidable.or_iff_not_not_and_not`：∀ {a b : Prop} [Decidable a] [Decidabl
e b], a ∨ b ↔ ¬(¬a ∧ ¬b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mul_neg_of_neg_of_pos`：mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : 
a < 0) (hb : 0 < b) : a * b < 0
-/
theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg
    [MulPosStrictMono R] [PosMulStrictMono R]
    (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine Decidable.or_iff_not_not_and_not.2 ?_
  simp only [not_and, not_le]; intro ab nab; apply not_lt_of_ge hab _
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · exact mul_neg_of_pos_of_neg ha (ab ha.le)
  · exact ((ab le_rfl).asymm (nab le_rfl)).elim
  · exact mul_neg_of_neg_of_pos ha (nab ha.le)
/-
**nonneg_of_mul_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonneg_of_mul_nonneg_left [MulPosStrictMono R] (h : 0 <= a * b) (hb : 0 < 
b) : 0 <= a
参数：h : 0 <= a * b；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_neg_of_neg_of_pos`：mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : 
a < 0) (hb : 0 < b) : a * b < 0
-/
theorem nonneg_of_mul_nonneg_left [MulPosStrictMono R]
    (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gt fun ha => (mul_neg_of_neg_of_pos ha hb).not_ge h
/-
**nonneg_of_mul_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonneg_of_mul_nonneg_right [PosMulStrictMono R] (h : 0 <= a * b) (ha : 0 <
 a) : 0 <= b
参数：h : 0 <= a * b；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
-/
theorem nonneg_of_mul_nonneg_right [PosMulStrictMono R]
    (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gt fun hb => (mul_neg_of_pos_of_neg ha hb).not_ge h
/-
**nonpos_of_mul_nonpos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonpos_of_mul_nonpos_left [PosMulStrictMono R] (h : a * b <= 0) (hb : 0 < 
b) : a <= 0
参数：h : a * b <= 0；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
theorem nonpos_of_mul_nonpos_left [PosMulStrictMono R]
    (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gt fun ha : a > 0 => (mul_pos ha hb).not_ge h
/-
**nonpos_of_mul_nonpos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonpos_of_mul_nonpos_right [PosMulStrictMono R] (h : a * b <= 0) (ha : 0 <
 a) : b <= 0
参数：h : a * b <= 0；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
theorem nonpos_of_mul_nonpos_right [PosMulStrictMono R]
    (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gt fun hb : b > 0 => (mul_pos ha hb).not_ge h

@[simp]
/-
**mul_nonneg_iff_of_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_of_pos_left [PosMulStrictMono R] (h : 0 < c) : 0 <= c * b ↔
 0 <= b
参数：h : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
-/
theorem mul_nonneg_iff_of_pos_left [PosMulStrictMono R]
    (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert! mul_le_mul_iff_right₀ h
  simp

@[simp]
/-
**mul_nonneg_iff_of_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_of_pos_right [MulPosStrictMono R] (h : 0 < c) : 0 <= b * c 
↔ 0 <= b
参数：h : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
-/
theorem mul_nonneg_iff_of_pos_right [MulPosStrictMono R]
    (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  simpa using (mul_le_mul_iff_left₀ h : 0 * c ≤ b * c ↔ 0 ≤ b)
/-
**add_le_mul_of_left_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_mul_of_left_le_right [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStr
ictMono R] [AddLeftMono R] (a2 : 2 <= a) (ab : a <= b) : a + b <= a * b
参数：1 : R；a2 : 2 <= a；ab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
-/
theorem add_le_mul_of_left_le_right [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
  have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
  calc
    a + b ≤ b + b := by gcongr
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_iff_left₀ this).mpr a2
/-
**add_le_mul_of_right_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_mul_of_right_le_left [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftMo
no R] [PosMulStrictMono R] (b2 : 2 <= b) (ba : b <= a) : a + b <= a * b
参数：1 : R；b2 : 2 <= b；ba : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
-/
theorem add_le_mul_of_right_le_left [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftMono R] [PosMulStrictMono R]
    (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
  have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
  calc
    a + b ≤ a + a := by gcongr
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_iff_right₀ this).mpr b2
/-
**add_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosMu
lStrictMono R] [AddLeftMono R] (a2 : 2 <= a) (b2 : 2 <= b) : a + b <= a * b
参数：1 : R；a2 : 2 <= a；b2 : 2 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_le_mul_of_left_le_right`：add_le_mul_of_left_le_right [ZeroLEOneClass
 R] [NeZero (1 : R)] [MulPosStrictMono R] [AddLeftMono R] (a2 : 2 <= a) (ab : a 
<= b) : a + b <= …
· 使用定理 `add_le_mul_of_right_le_left`：add_le_mul_of_right_le_left [ZeroLEOneClass
 R] [NeZero (1 : R)] [AddLeftMono R] [PosMulStrictMono R] (b2 : 2 <= b) (ba : b 
<= a) : a + b <= …
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
  if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
  else add_le_mul_of_right_le_left b2 (le_of_not_ge hab)
/-
**add_le_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_le_mul' [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosM
ulStrictMono R] [AddLeftMono R] (a2 : 2 <= a) (b2 : 2 <= b) : a + b <= b * a
参数：1 : R；a2 : 2 <= a；b2 : 2 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_le_mul`：add_le_mul [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrict
Mono R] [PosMulStrictMono R] [AddLeftMono R] (a2 : 2 <= a) (b2 : 2 <= b) : a + b
…
-/
theorem add_le_mul' [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
  (le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)
/-
**mul_nonneg_iff_right_nonneg_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono R] (ha : 0 < a) : 0 <
= a * b ↔ 0 <= b
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_of_mul_nonneg_right`：nonneg_of_mul_nonneg_right [PosMulStrictMono
 R] (h : 0 <= a * b) (ha : 0 < a) : 0 <= b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_nonneg_iff_right_nonneg_of_pos [PosMulStrictMono R]
    (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, mul_nonneg ha.le⟩
/-
**mul_nonneg_iff_left_nonneg_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono R] [MulPosStrictMono R
] (hb : 0 < b) : 0 <= a * b ↔ 0 <= a
参数：hb : 0 < b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_of_mul_nonneg_left`：nonneg_of_mul_nonneg_left [MulPosStrictMono R
] (h : 0 <= a * b) (hb : 0 < b) : 0 <= a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_nonneg_iff_left_nonneg_of_pos [PosMulStrictMono R] [MulPosStrictMono R]
    (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => mul_nonneg h hb.le⟩
/-
**nonpos_of_mul_nonneg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonpos_of_mul_nonneg_left [PosMulStrictMono R] (h : 0 <= a * b) (hb : b < 
0) : a <= 0
参数：h : 0 <= a * b；hb : b < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
-/
theorem nonpos_of_mul_nonneg_left [PosMulStrictMono R]
    (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gt fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_ge
/-
**nonpos_of_mul_nonneg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonpos_of_mul_nonneg_right [MulPosStrictMono R] (h : 0 <= a * b) (ha : a <
 0) : b <= 0
参数：h : 0 <= a * b；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_neg_of_neg_of_pos`：mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : 
a < 0) (hb : 0 < b) : a * b < 0
-/
theorem nonpos_of_mul_nonneg_right [MulPosStrictMono R]
    (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gt fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_ge

@[simp]
/-
**Units.inv_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.inv_pos [ZeroLEOneClass R] [NeZero (1 : R)] [PosMulStrictMono R] {u 
: Rˣ} : (0 : R) < ↑u⁻¹ ↔ (0 : R) < u
参数：1 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_pos_iff_of_pos_left`：mul_pos_iff_of_pos_left [PosMulStrictMono α] [P
osMulReflectLT α] (h : 0 < a) : 0 < a * b ↔ 0 < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
theorem Units.inv_pos
    [ZeroLEOneClass R] [NeZero (1 : R)] [PosMulStrictMono R]
    {u : Rˣ} : (0 : R) < ↑u⁻¹ ↔ (0 : R) < u :=
  have : ∀ {u : Rˣ}, (0 : R) < u → (0 : R) < ↑u⁻¹ := @fun u h =>
    (mul_pos_iff_of_pos_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]
/-
**Units.inv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.inv_neg [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosMono R] [PosMulMo
no R] {u : Rˣ} : ↑u⁻¹ < (0 : R) ↔ ↑u < (0 : R)
参数：1 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_of_mul_pos_right`：neg_of_mul_pos_right [PosMulMono α] [MulPosMono α]
 (h : 0 < a * b) (ha : a <= 0) : b < 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Units.inv_neg
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosMono R] [PosMulMono R]
    {u : Rˣ} : ↑u⁻¹ < (0 : R) ↔ ↑u < (0 : R) :=
  have : ∀ {u : Rˣ}, ↑u < (0 : R) → ↑u⁻¹ < (0 : R) := @fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩
/-
**cmp_mul_pos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_pos_left [PosMulStrictMono R] (ha : 0 < a) (b c : R) : cmp (a * b)
 (a * c) = cmp b c
参数：ha : 0 < a；b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.cmp_map_eq`：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : 
α) : cmp (f x) (f y) = cmp x y
· 使用引理 `strictMono_mul_left_of_pos`：strictMono_mul_left_of_pos [PosMulStrictMono
 M₀] (ha : 0 < a) : StrictMono fun x => a * x
-/
theorem cmp_mul_pos_left [PosMulStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_mul_left_of_pos ha).cmp_map_eq b c
/-
**cmp_mul_pos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_pos_right [MulPosStrictMono R] (ha : 0 < a) (b c : R) : cmp (b * a
) (c * a) = cmp b c
参数：ha : 0 < a；b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.cmp_map_eq`：StrictMono.cmp_map_eq (hf : StrictMono f) (x y : 
α) : cmp (f x) (f y) = cmp x y
· 使用引理 `strictMono_mul_right_of_pos`：strictMono_mul_right_of_pos [MulPosStrictMo
no M₀] (ha : 0 < a) : StrictMono fun x => x * a
-/
theorem cmp_mul_pos_right [MulPosStrictMono R]
    (ha : 0 < a) (b c : R) : cmp (b * a) (c * a) = cmp b c :=
  (strictMono_mul_right_of_pos ha).cmp_map_eq b c
/-
**mul_max_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <= a) : a * max b c = m
ax (a * b) (a * c)
参数：b c : R；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
-/
theorem mul_max_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max
/-
**mul_min_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_min_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <= a) : a * min b c = m
in (a * b) (a * c)
参数：b c : R；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
-/
theorem mul_min_of_nonneg [PosMulMono R]
    (b c : R) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min
/-
**max_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <= c) : max a b * c = m
ax (a * c) (b * c)
参数：a b : R；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `monotone_mul_right_of_nonneg`：monotone_mul_right_of_nonneg [MulPosMono M
₀] (ha : 0 <= a) : Monotone fun x => x * a
-/
theorem max_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max
/-
**min_mul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <= c) : min a b * c = m
in (a * c) (b * c)
参数：a b : R；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用引理 `monotone_mul_right_of_nonneg`：monotone_mul_right_of_nonneg [MulPosMono M
₀] (ha : 0 <= a) : Monotone fun x => x * a
-/
theorem min_mul_of_nonneg [MulPosMono R]
    (a b : R) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min
/-
**le_of_mul_le_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_of_one_le [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMo
no R] [PosMulMono R] {a b c : R} (h : a * c <= b) (hb : 0 <= b) (hc : 1 <= c) : 
a <= b
参数：1 : R；h : a * c <= b；hb : 0 <= b；hc : 1 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
theorem le_of_mul_le_of_one_le
    [ZeroLEOneClass R] [NeZero (1 : R)] [MulPosStrictMono R] [PosMulMono R]
    {a b c : R} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  le_of_mul_le_mul_right (h.trans <| le_mul_of_one_le_right hb hc) <| zero_lt_one.trans_le hc
/-
**nonneg_le_nonneg_of_sq_le_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono R] [MulPosMono R] {a b : R}
 (hb : 0 <= b) (h : a * a <= b * b) : a <= b
参数：hb : 0 <= b；h : a * a <= b * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `mul_self_lt_mul_self`：mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPos
Mono M₀] (ha : 0 <= a) (hab : a < b) : a * a < b * b
-/
theorem nonneg_le_nonneg_of_sq_le_sq [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gt fun hab => (mul_self_lt_mul_self hb hab).not_ge h
/-
**mul_self_le_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_le_mul_self_iff [PosMulStrictMono R] [MulPosMono R] {a b : R} (h1
 : 0 <= a) (h2 : 0 <= b) : a <= b ↔ a * a <= b * b
参数：h1 : 0 <= a；h2 : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_self_le_mul_self`：mul_self_le_mul_self [PosMulMono α] [MulPosMono α]
 (ha : 0 <= a) (hab : a <= b) : a * a <= b * b
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `nonneg_le_nonneg_of_sq_le_sq`：nonneg_le_nonneg_of_sq_le_sq [PosMulStrict
Mono R] [MulPosMono R] {a b : R} (hb : 0 <= b) (h : a * a <= b * b) : a <= b
-/
theorem mul_self_le_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  ⟨mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩
/-
**mul_self_lt_mul_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_lt_mul_self_iff [PosMulStrictMono R] [MulPosMono R] {a b : R} (h1
 : 0 <= a) (h2 : 0 <= b) : a < b ↔ a * a < b * b
参数：h1 : 0 <= a；h2 : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `StrictMonoOn.lt_iff_lt`：StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a < f b ↔ a < b
· 使用引理 `strictMonoOn_mul_self`：strictMonoOn_mul_self [PosMulStrictMono M₀] [MulP
osMono M₀] : StrictMonoOn (fun x => x * x) {x : M₀ | 0 <= x}
-/
theorem mul_self_lt_mul_self_iff [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  ((@strictMonoOn_mul_self R _).lt_iff_lt h1 h2).symm
/-
**mul_self_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_inj [PosMulStrictMono R] [MulPosMono R] {a b : R} (h1 : 0 <= a) (
h2 : 0 <= b) : a * a = b * b ↔ a = b
参数：h1 : 0 <= a；h2 : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.eq_iff_eq`：StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {
a b : α} (ha : a in s) (hb : b in s) : f a = f b ↔ a = b
· 使用引理 `strictMonoOn_mul_self`：strictMonoOn_mul_self [PosMulStrictMono M₀] [MulP
osMono M₀] : StrictMonoOn (fun x => x * x) {x : M₀ | 0 <= x}
-/
theorem mul_self_inj [PosMulStrictMono R] [MulPosMono R]
    {a b : R} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  (@strictMonoOn_mul_self R _).eq_iff_eq h1 h2
/-
**sign_cases_of_C_mul_pow_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono R] (h : forall n, 0 <= a 
* b ^ n) : a = 0 ∨ 0 < a ∧ 0 <= b
参数：h : forall n, 0 <= a * b ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `nonneg_of_mul_nonneg_right`：nonneg_of_mul_nonneg_right [PosMulStrictMono
 R] (h : 0 <= a * b) (ha : 0 < a) : 0 <= b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
-/
lemma sign_cases_of_C_mul_pow_nonneg [PosMulStrictMono R]
    (h : ∀ n, 0 ≤ a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 ≤ b := by
  have : 0 ≤ a := by simpa only [pow_zero, mul_one] using h 0
  refine this.eq_or_lt'.imp_right fun ha ↦ ⟨ha, nonneg_of_mul_nonneg_right ?_ ha⟩
  simpa only [pow_one] using h 1
/-
**mul_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R] [A
ddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b
 < 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_and_pos_or_neg_and_neg_of_mul_pos`：pos_and_pos_or_neg_and_neg_of_mul
_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : 0 < a ∧ 0 < b ∨ a < 0 ∧ b
 < 0
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R] :
    0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h =>
    h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩
/-
**mul_nonneg_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
 [AddLeftReflectLE R] [AddLeftMono R] : 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ 
b <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg`：nonneg_and_nonneg_
or_nonpos_and_nonpos_of_mul_nonneg [MulPosStrictMono R] [PosMulStrictMono R] (ha
b : 0 <= a * b) : 0 <= a ∧ 0 <= b ∨ a <= 0…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
-/
theorem mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nonneg, fun h =>
    h.elim (and_imp.2 mul_nonneg) (and_imp.2 mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a linearly ordered semiring, two must have the same sign. -/
/-
**mul_nonneg_of_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_nonneg_of_three [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMo
no R] [AddLeftMono R] [AddLeftReflectLE R] (a b c : R) : 0 <= a * b ∨ 0 <= b * c
 ∨ 0 <= c * a
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_nonneg_iff`：mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [P
osMulStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] : 0 <= a * b ↔ 0 <= a ∧ 
0 <=…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
Out of three elements of a linearly ordered semiring, two must have the same sig
n.
-/
theorem mul_nonneg_of_three [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (a b c : R) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop
/-
**mul_nonneg_iff_pos_imp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE R] [PosMulStrictMono R] [MulP
osStrictMono R] [AddLeftMono R] [AddLeftReflectLE R] : 0 <= a * b ↔ (0 < a -> 0 
<= b) ∧ (0 < b -> 0 <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mul_nonneg_iff`：mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [P
osMulStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] : 0 <= a * b ↔ 0 <= a ∧ 
0 <=…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
lemma mul_nonneg_iff_pos_imp_nonneg [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (0 < a → 0 ≤ b) ∧ (0 < b → 0 ≤ a) := by
  refine mul_nonneg_iff.trans ?_
  simp_rw [← not_le, ← or_iff_not_imp_left]
  have := le_total a 0
  have := le_total b 0
  tauto

@[simp]
/-
**mul_le_mul_left_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightMon
o R] [AddRightReflectLE R] {a b c : R} (h : c < 0) : c * a <= c * b ↔ b <= a
参数：h : c < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `strictAnti_mul_left`：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrict
Mono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : Stri
ctAnti (a…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
-/
theorem mul_le_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  (strictAnti_mul_left h).le_iff_ge

@[simp]
/-
**mul_le_mul_right_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_le_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightMo
no R] [AddRightReflectLE R] {a b c : R} (h : c < 0) : a * c <= b * c ↔ b <= a
参数：h : c < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `strictAnti_mul_right`：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStri
ctMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : St
rictAnti f…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
-/
theorem mul_le_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b c : R} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  (strictAnti_mul_right h).le_iff_ge

@[simp]
/-
**mul_lt_mul_left_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightStr
ictMono R] [AddRightReflectLT R] {a b c : R} (h : c < 0) : c * a < c * b ↔ b < a
参数：h : c < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `strictAnti_mul_left`：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrict
Mono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : Stri
ctAnti (a…
-/
theorem mul_lt_mul_left_of_neg [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strictAnti_mul_left h).lt_iff_gt

@[simp]
/-
**mul_lt_mul_right_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_lt_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightSt
rictMono R] [AddRightReflectLT R] {a b c : R} (h : c < 0) : a * c < b * c ↔ b < 
a
参数：h : c < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `strictAnti_mul_right`：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStri
ctMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : St
rictAnti f…
-/
theorem mul_lt_mul_right_of_neg [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightStrictMono R] [AddRightReflectLT R]
    {a b c : R} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strictAnti_mul_right h).lt_iff_gt
/-
**lt_of_mul_lt_mul_of_nonpos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R] [AddRight
Mono R] [AddRightReflectLE R] (h : c * a < c * b) (hc : c <= 0) : b < a
参数：h : c * a < c * b；hc : c <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.reflect_lt`：Antitone.reflect_lt (hf : Antitone f) {a b : α} (h 
: f a < f b) : b < a
· 使用定理 `antitone_mul_left`：antitone_mul_left [ExistsAddOfLE R] [PosMulMono R] [A
ddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone (a * ·)
-/
theorem lt_of_mul_lt_mul_of_nonpos_left [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
  (antitone_mul_left hc).reflect_lt h
/-
**lt_of_mul_lt_mul_of_nonpos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R] [AddRigh
tMono R] [AddRightReflectLE R] (h : a * c < b * c) (hc : c <= 0) : b < a
参数：h : a * c < b * c；hc : c <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.reflect_lt`：Antitone.reflect_lt (hf : Antitone f) {a b : α} (h 
: f a < f b) : b < a
· 使用定理 `antitone_mul_right`：antitone_mul_right [ExistsAddOfLE R] [MulPosMono R] 
[AddRightMono R] [AddRightReflectLE R] {a : R} (ha : a <= 0) : Antitone fun x =>
 x * a
-/
theorem lt_of_mul_lt_mul_of_nonpos_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * c < b * c) (hc : c ≤ 0) : b < a :=
  (antitone_mul_right hc).reflect_lt h
/-
**cmp_mul_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_neg_left [ExistsAddOfLE R] [PosMulStrictMono R] [AddRightReflectLT
 R] [AddRightStrictMono R] {a : R} (ha : a < 0) (b c : R) : cmp (a * b) (a * c) 
= cmp c b
参数：ha : a < 0；b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.cmp_map_eq`：StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : 
α) : cmp (f x) (f y) = cmp y x
· 使用定理 `strictAnti_mul_left`：strictAnti_mul_left [ExistsAddOfLE R] [PosMulStrict
Mono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : Stri
ctAnti (a…
-/
theorem cmp_mul_neg_left [ExistsAddOfLE R] [PosMulStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (a * b) (a * c) = cmp c b :=
  (strictAnti_mul_left ha).cmp_map_eq b c
/-
**cmp_mul_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cmp_mul_neg_right [ExistsAddOfLE R] [MulPosStrictMono R] [AddRightReflectL
T R] [AddRightStrictMono R] {a : R} (ha : a < 0) (b c : R) : cmp (b * a) (c * a)
 = cmp c b
参数：ha : a < 0；b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.cmp_map_eq`：StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : 
α) : cmp (f x) (f y) = cmp y x
· 使用定理 `strictAnti_mul_right`：strictAnti_mul_right [ExistsAddOfLE R] [MulPosStri
ctMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a : R} (ha : a < 0) : St
rictAnti f…
-/
theorem cmp_mul_neg_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightReflectLT R] [AddRightStrictMono R]
    {a : R} (ha : a < 0) (b c : R) : cmp (b * a) (c * a) = cmp c b :=
  (strictAnti_mul_right ha).cmp_map_eq b c

@[simp]
/-
**mul_self_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R] [
AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
theorem mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftStrictMono R] [AddLeftReflectLT R]
    {a : R} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
  · intro h
    rcases h.lt_or_gt with h | h
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h]
/-
**nonneg_of_mul_nonpos_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonneg_of_mul_nonpos_left [ExistsAddOfLE R] [MulPosStrictMono R] [AddRight
Mono R] [AddRightReflectLE R] {a b : R} (h : a * b <= 0) (hb : b < 0) : 0 <= a
参数：h : a * b <= 0；hb : b < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
-/
theorem nonneg_of_mul_nonpos_left [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gt fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge
/-
**nonneg_of_mul_nonpos_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonneg_of_mul_nonpos_right [ExistsAddOfLE R] [MulPosStrictMono R] [AddRigh
tMono R] [AddRightReflectLE R] {a b : R} (h : a * b <= 0) (ha : a < 0) : 0 <= b
参数：h : a * b <= 0；ha : a < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
-/
theorem nonneg_of_mul_nonpos_right [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gt fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_ge
/-
**pos_of_mul_neg_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R] [AddRightMono R] [Add
RightReflectLE R] {a b : R} (h : a * b < 0) (hb : b <= 0) : 0 < a
参数：h : a * b < 0；hb : b <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
-/
theorem pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  lt_of_not_ge fun ha => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt
/-
**pos_of_mul_neg_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono R] [AddRightMono R] [Ad
dRightReflectLE R] {a b : R} (h : a * b < 0) (ha : a <= 0) : 0 < b
参数：h : a * b < 0；ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
-/
theorem pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    {a b : R} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  lt_of_not_ge fun hb => absurd h (mul_nonneg_of_nonpos_of_nonpos ha hb).not_gt
/-
**neg_iff_pos_of_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_iff_pos_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R] [Ad
dRightMono R] [AddRightReflectLE R] (hab : a * b < 0) : a < 0 ↔ 0 < b
参数：hab : a * b < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pos_of_mul_neg_right`：pos_of_mul_neg_right [ExistsAddOfLE R] [MulPosMono
 R] [AddRightMono R] [AddRightReflectLE R] {a b : R} (h : a * b < 0) (ha : a <= 
0) : 0 < b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_of_mul_neg_left`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} 
[inst_1 : LinearOrder α] [PosMulMono α], a * b < 0 → 0 ≤ b → a < 0
-/
theorem neg_iff_pos_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_left hab ∘ le_of_lt⟩
/-
**pos_iff_neg_of_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_iff_neg_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R] [Ad
dRightMono R] [AddRightReflectLE R] (hab : a * b < 0) : 0 < a ↔ b < 0
参数：hab : a * b < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_of_mul_neg_right`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α}
 [inst_1 : LinearOrder α] [PosMulMono α], a * b < 0 → 0 ≤ a → b < 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pos_of_mul_neg_left`：pos_of_mul_neg_left [ExistsAddOfLE R] [MulPosMono R
] [AddRightMono R] [AddRightReflectLE R] {a b : R} (h : a * b < 0) (hb : b <= 0)
 : 0 < a
-/
theorem pos_iff_neg_of_mul_neg [ExistsAddOfLE R] [PosMulMono R] [MulPosMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩
/-
**sq_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R) : 0 <= 
a ^ 2
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `pow_succ_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : 
Preorder M₀] {a : M₀} [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ (n + 1)
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `add_neg_of_neg_of_nonpos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftMono α] {a b : α}, a < 0 → b ≤ 0 → a + b < 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
lemma sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a ^ 2 := by
  obtain ha | ha := le_or_gt 0 a
  · exact pow_succ_nonneg ha _
  obtain ⟨b, hab⟩ := exists_add_of_le ha.le
  have hb : 0 < b := not_le.1 fun hb ↦ (add_neg_of_neg_of_nonpos ha hb).ne' hab
  calc
    0 ≤ b ^ 2 := pow_succ_nonneg hb.le _
    _ = b ^ 2 + a * (a + b) := by rw [← hab, mul_zero, add_zero]
    _ = a ^ 2 + (a + b) * b := by rw [add_mul, mul_add, sq, sq, add_comm, add_assoc]
    _ = a ^ 2 := by rw [← hab, zero_mul, add_zero]

@[simp]
/-
**sq_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sq_nonpos_iff [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] [NoZeroDivi
sors R] (r : R) : r ^ 2 <= 0 ↔ r = 0
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
-/
lemma sq_nonpos_iff [ExistsAddOfLE R]
    [PosMulMono R] [AddLeftMono R] [NoZeroDivisors R] (r : R) :
    r ^ 2 ≤ 0 ↔ r = 0 := by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg
/-
**mul_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R) :
 0 <= a * a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
-/
lemma mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a * a := by simpa only [sq] using sq_nonneg a
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    ZeroLEOneClass R where
  zero_le_one := by simpa only [one_mul] using mul_self_nonneg (1 : R)

/-- The sum of two squares is zero iff both elements are zero. -/
/-
**mul_self_add_mul_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_self_add_mul_self_eq_zero [NoZeroDivisors R] [ExistsAddOfLE R] [PosMul
Mono R] [AddLeftMono R] : a * a + b * b = 0 ↔ a = 0 ∧ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The sum of two squares is zero iff both elements are zero.
-/
lemma mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg, mul_self_eq_zero (M₀ := R), mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg
/-
**eq_zero_of_mul_self_add_mul_self_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_zero_of_mul_self_add_mul_self_eq_zero [NoZeroDivisors R] [ExistsAddOfLE
 R] [PosMulMono R] [AddLeftMono R] (h : a * a + b * b = 0) : a = 0
参数：h : a * a + b * b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_self_add_mul_self_eq_zero`：mul_self_add_mul_self_eq_zero [NoZeroDivi
sors R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] : a * a + b * b = 0 ↔ a
 = 0 ∧ b = 0
-/
lemma eq_zero_of_mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left
/-
**pos_of_right_mul_lt_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_right_mul_lt_le [ExistsAddOfLE R] [PosMulMono R] [AddRightMono R] [
AddRightReflectLE R] (h : a * b < a * c) (hbc : b <= c) : 0 < a
参数：h : a * b < a * c；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pos_of_right_mul_lt_le [ExistsAddOfLE R] [PosMulMono R]
    [AddRightMono R] [AddRightReflectLE R]
    (h : a * b < a * c) (hbc : b ≤ c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_left hbc ha]
/-
**pos_of_left_mul_lt_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pos_of_left_mul_lt_le [ExistsAddOfLE R] [MulPosMono R] [AddLeftMono R] [Ad
dRightReflectLE R] (h : b * a < c * a) (hbc : b <= c) : 0 < a
参数：h : b * a < c * a；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pos_of_left_mul_lt_le [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddRightReflectLE R]
    (h : b * a < c * a) (hbc : b ≤ c) :
    0 < a := by
  by_cases! ha : 0 < a
  · exact ha
  · grind [mul_le_mul_of_nonpos_right hbc ha]

end LinearOrderedSemiring

section LinearOrderedCommSemiring

variable [CommSemiring R] [LinearOrder R] {a d : R}

/-
**max_mul_mul_le_max_mul_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：max_mul_mul_le_max_mul_max [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0
 <= a) (hd : 0 <= d) : max (a * b) (d * c) <= max a c * max d b
参数：b c : R；ha : 0 <= a；hd : 0 <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
lemma max_mul_mul_le_max_mul_max [PosMulMono R] [MulPosMono R] (b c : R) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    max (a * b) (d * c) ≤ max a c * max d b :=
  have ba : b * a ≤ max d b * max c a := by
    gcongr
    exacts [ha, hd.trans <| le_max_left d b, le_max_right d b, le_max_right c a]
  have cd : c * d ≤ max a c * max b d :=
    mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c))
  max_le (by simpa [mul_comm, max_comm] using ba) (by simpa [mul_comm, max_comm] using cd)

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
/-
**two_mul_le_add_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono R] [AddLeftReflectLE
 R] [AddLeftMono R] (a b : R) : 2 * a * b <= a ^ 2 + b ^ 2
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `min_mul_max`：min_mul_max (a b : α) : min a b * max a b = a * b
· 使用引理 `max_mul_min`：max_mul_min (a b : α) : max a b * min a b = a * b
· 使用定理 `fn_min_add_fn_max`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α
] [inst_1 : AddCommSemigroup β] (f : α → β) (a b : α),   f (min a b) + f (max a 
b) = f …
· 使用引理 `mul_add_mul_le_mul_add_mul`：mul_add_mul_le_mul_add_mul [ExistsAddOfLE R]
 [MulPosMono R] [AddLeftMono R] [AddLeftReflectLE R] (hab : a <= b) (hcd : c <= 
d) : a * d + b *…
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `min_le_max`：min_le_max : min a b <= max a b

--- 原说明 ---
Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings.
-/
lemma two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  simpa [fn_min_add_fn_max (fun x ↦ x * x), sq, two_mul, add_mul]
    using mul_add_mul_le_mul_add_mul (@min_le_max _ _ a b) (@min_le_max _ _ a b)

alias two_mul_le_add_pow_two := two_mul_le_add_sq

/-- Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
/-
**four_mul_le_sq_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMono R] [AddLeftReflectL
E R] [AddLeftMono R] (a b : R) : 4 * a * b <= (a + b) ^ 2
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_add_two_eq_four`：two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = 
(4 : R)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `two_mul_le_add_sq`：two_mul_le_add_sq [ExistsAddOfLE R] [MulPosStrictMono
 R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) : 2 * a * b <= a ^ 2 + b ^ 2
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用引理 `add_sq`：add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2

--- 原说明 ---
Binary, squared, and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings.
-/
lemma four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 4 * a * b ≤ (a + b) ^ 2 := by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

/-- Binary and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings. -/
/-
**two_mul_le_add_of_sq_le_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_mul_le_add_of_sq_le_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMul
StrictMono R] [AddLeftReflectLE R] [AddLeftMono R] {a b r : R} (ha : 0 <= a) (hb
 : 0 <= b) (ht : r ^ 2 <= a * b) : 2 * r <= a + b
参数：ha : 0 <= a；hb : 0 <= b；ht : r ^ 2 <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonneg_le_nonneg_of_sq_le_sq`：nonneg_le_nonneg_of_sq_le_sq [PosMulStrict
Mono R] [MulPosMono R] {a b : R} (hb : 0 <= b) (h : a * a <= b * b) : a <= b
· 使用定理 `MulPosStrictMono.toMulPosMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [MulPosStrictMono α], MulPosMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Left.add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preo
rder α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `two_add_two_eq_four`：two_add_two_eq_four [AddMonoidWithOne R] : 2 + 2 = 
(4 : R)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `PosMulStrictMono.toPosMulMono`：∀ {α : Type u_1} [inst : MulZeroClass α] 
[inst_1 : PartialOrder α] [PosMulStrictMono α], PosMulMono α
· 使用引理 `zero_le_four`：zero_le_four [Preorder α] [ZeroLEOneClass α] [AddLeftMono 
α] : (0 : α) <= 4
· 使用定理 `instZeroLEOneClassOfExistsAddOfLEOfPosMulMonoOfAddLeftMono`：∀ {R : Type 
u} [inst : Semiring R] [inst_1 : LinearOrder R] [ExistsAddOfLE R] [PosMulMono R]
 [AddLeftMono R],   ZeroLEOneClass R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `four_mul_le_sq_add`：four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMo
no R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) : 4 * a * b <= (a + b) ^ 2
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
Binary and division-free **arithmetic mean-geometric mean inequality**
(aka AM-GM inequality) for linearly ordered commutative semirings.
-/
lemma two_mul_le_add_of_sq_le_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 ≤ a * b) : 2 * r ≤ a + b := by
  apply nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg ha hb)
  rw [mul_mul_mul_comm, ← pow_two r, two_mul, two_add_two_eq_four]
  grw [mul_le_mul_of_nonneg_left ht zero_le_four, ← mul_assoc, four_mul_le_sq_add a b, sq]

@[deprecated two_mul_le_add_of_sq_le_mul (since := "2026-04-20")]
/-
**two_mul_le_add_of_sq_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：two_mul_le_add_of_sq_eq_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMul
StrictMono R] [AddLeftReflectLE R] [AddLeftMono R] {a b r : R} (ha : 0 <= a) (hb
 : 0 <= b) (ht : r ^ 2 = a * b) : 2 * r <= a + b
参数：ha : 0 <= a；hb : 0 <= b；ht : r ^ 2 = a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `two_mul_le_add_of_sq_le_mul`：two_mul_le_add_of_sq_le_mul [ExistsAddOfLE 
R] [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftReflectLE R] [AddLeftMono R
] {a b r : R} (ha…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma two_mul_le_add_of_sq_eq_mul [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] {a b r : R}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : r ^ 2 = a * b) : 2 * r ≤ a + b :=
  two_mul_le_add_of_sq_le_mul ha hb ht.le

end LinearOrderedCommSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] {a b : R}

-- TODO: Can the following five lemmas be generalised to
-- `[Semiring R] [LinearOrder R] [ExistsAddOfLE R] ..`?

/-
**mul_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R] [AddLeftReflectLT R]
 [AddLeftStrictMono R] : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `mul_pos_iff`：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosS
trictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 
<…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftReflectLT R] [AddLeftStrictMono R] :
    a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff (R := R), neg_pos, neg_lt_zero]
/-
**mul_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftReflectLE
 R] [AddLeftMono R] : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `neg_mul_eq_mul_neg`：neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b
· 使用定理 `mul_nonneg_iff`：mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [P
osMulStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] : 0 <= a * b ↔ 0 <= a ∧ 
0 <=…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R] :
    a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff (R := R), neg_nonneg, neg_nonpos]
/-
**mul_nonneg_iff_neg_imp_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R] [A
ddLeftMono R] [AddLeftReflectLE R] : 0 <= a * b ↔ (a < 0 -> b <= 0) ∧ (b < 0 -> 
a <= 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用引理 `mul_nonneg_iff_pos_imp_nonneg`：mul_nonneg_iff_pos_imp_nonneg [ExistsAddO
fLE R] [PosMulStrictMono R] [MulPosStrictMono R] [AddLeftMono R] [AddLeftReflect
LE R] : 0 <= a * b …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mul_nonneg_iff_neg_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    0 ≤ a * b ↔ (a < 0 → b ≤ 0) ∧ (b < 0 → a ≤ 0) := by
  rw [← neg_mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]; simp only [neg_pos, neg_nonneg]
/-
**mul_nonpos_iff_pos_imp_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R] [A
ddLeftMono R] [AddLeftReflectLE R] : a * b <= 0 ↔ (0 < a -> b <= 0) ∧ (b < 0 -> 
0 <= a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `mul_nonneg_iff_pos_imp_nonneg`：mul_nonneg_iff_pos_imp_nonneg [ExistsAddO
fLE R] [PosMulStrictMono R] [MulPosStrictMono R] [AddLeftMono R] [AddLeftReflect
LE R] : 0 <= a * b …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mul_nonpos_iff_pos_imp_nonpos [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (0 < a → b ≤ 0) ∧ (b < 0 → 0 ≤ a) := by
  rw [← neg_nonneg, ← mul_neg, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]
/-
**mul_nonpos_iff_neg_imp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono R] [MulPosStrictMono R] [A
ddLeftMono R] [AddLeftReflectLE R] : a * b <= 0 ↔ (a < 0 -> 0 <= b) ∧ (0 < b -> 
a <= 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `mul_nonneg_iff_pos_imp_nonneg`：mul_nonneg_iff_pos_imp_nonneg [ExistsAddO
fLE R] [PosMulStrictMono R] [MulPosStrictMono R] [AddLeftMono R] [AddLeftReflect
LE R] : 0 <= a * b …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mul_nonpos_iff_neg_imp_nonneg [PosMulStrictMono R] [MulPosStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R] :
    a * b ≤ 0 ↔ (a < 0 → 0 ≤ b) ∧ (0 < b → a ≤ 0) := by
  rw [← neg_nonneg, ← neg_mul, mul_nonneg_iff_pos_imp_nonneg (R := R)]
  simp only [neg_pos, neg_nonneg]
/-
**neg_one_lt_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] 
: -1 < (0 : R)
参数：1 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
-/
lemma neg_one_lt_zero
    [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] :
    -1 < (0 : R) := neg_lt_zero.2 zero_lt_one
/-
**sub_one_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStrictMono R] (a : 
R) : a - 1 < a
参数：1 : R；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
· 使用定理 `addRightStrictMono_of_addRightReflectLE`：∀ (N : Type u_2) [inst : Add N]
 [inst_1 : LinearOrder N] [AddRightReflectLE N], AddRightStrictMono N
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddGroup.covconv`：∀ {N : Type u_2} {r : N → N → Prop} [inst : AddGroup N
] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   ContravariantClass N N (fun x
1 x2 =…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
-/
lemma sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftStrictMono R]
    (a : R) : a - 1 < a := sub_lt_iff_lt_add.2 <| lt_add_one a
/-
**mul_self_le_mul_self_of_le_of_neg_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_self_le_mul_self_of_le_of_neg_le [MulPosMono R] [PosMulMono R] [AddLef
tMono R] (h₁ : a <= b) (h₂ : -a <= b) : a * a <= b * b
参数：h₁ : a <= b；h₂ : -a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `mul_self_le_mul_self`：mul_self_le_mul_self [PosMulMono α] [MulPosMono α]
 (ha : 0 <= a) (hab : a <= b) : a * a <= b * b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma mul_self_le_mul_self_of_le_of_neg_le
    [MulPosMono R] [PosMulMono R] [AddLeftMono R]
    (h₁ : a ≤ b) (h₂ : -a ≤ b) : a * a ≤ b * b :=
  (le_total 0 a).elim (mul_self_le_mul_self · h₁) fun h ↦
    (neg_mul_neg a a).symm.trans_le <|
      mul_le_mul h₂ h₂ (neg_nonneg.2 h) <| (neg_nonneg.2 h).trans h₂
/-
**sub_mul_sub_nonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_mul_sub_nonneg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftM
ono R] (x : R) (h : a <= b) : 0 <= (x - a) * (x - b) ↔ x <= a ∨ b <= x
参数：x : R；h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_nonneg_iff`：mul_nonneg_iff [ExistsAddOfLE R] [MulPosStrictMono R] [P
osMulStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] : 0 <= a * b ↔ 0 <= a ∧ 
0 <=…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sub_mul_sub_nonneg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
  rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
    and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]
/-
**sub_mul_sub_nonpos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_mul_sub_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftM
ono R] (x : R) (h : a <= b) : (x - a) * (x - b) <= 0 ↔ a <= x ∧ x <= b
参数：x : R；h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_nonpos_iff`：mul_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R]
 [AddLeftReflectLE R] [AddLeftMono R] : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 
0 <=…
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `or_iff_left_iff_imp`：∀ {a b : Prop}, (a ∨ b ↔ a) ↔ b → a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
lemma sub_mul_sub_nonpos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : (x - a) * (x - b) ≤ 0 ↔ a ≤ x ∧ x ≤ b := by
  rw [mul_nonpos_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans h.trans'
/-
**sub_mul_sub_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_mul_sub_pos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono
 R] (x : R) (h : a <= b) : 0 < (x - a) * (x - b) ↔ x < a ∨ b < x
参数：x : R；h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_pos_iff`：mul_pos_iff [ExistsAddOfLE R] [PosMulStrictMono R] [MulPosS
trictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] : 0 < a * b ↔ 0 < a ∧ 0 
<…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sub_mul_sub_pos_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : 0 < (x - a) * (x - b) ↔ x < a ∨ b < x := by
  rw [mul_pos_iff, sub_pos, sub_pos, sub_neg, sub_neg, and_iff_right_of_imp h.trans_lt,
    and_iff_left_of_imp h.trans_lt', or_comm]
/-
**sub_mul_sub_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_mul_sub_neg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono
 R] (x : R) (h : a <= b) : (x - a) * (x - b) < 0 ↔ a < x ∧ x < b
参数：x : R；h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_neg_iff`：mul_neg_iff [PosMulStrictMono R] [MulPosStrictMono R] [AddL
eftReflectLT R] [AddLeftStrictMono R] : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < 
b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
· 使用定理 `or_iff_left_iff_imp`：∀ {a b : Prop}, (a ∨ b ↔ a) ↔ b → a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
-/
lemma sub_mul_sub_neg_iff [MulPosStrictMono R] [PosMulStrictMono R] [AddLeftMono R]
    (x : R) (h : a ≤ b) : (x - a) * (x - b) < 0 ↔ a < x ∧ x < b := by
  rw [mul_neg_iff, sub_pos, sub_pos, sub_neg, sub_neg, or_iff_left_iff_imp, and_comm]
  exact And.imp h.trans_lt h.trans_lt'

end LinearOrderedRing
end OrderedCommRing

