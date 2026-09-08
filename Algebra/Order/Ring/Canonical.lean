/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Ring.Parity

/-!
# Canonically ordered rings and semirings.
-/

public section


open Function

universe u

variable {R : Type u}

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass R] [One R] [LE R] [CanonicallyOrderedAdd R] : ZeroLEOneClass R where
  zero_le_one := zero_le

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
/-
**Odd.pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivia
l R] {a : R} : Odd a -> 0 < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
/-
**CanonicallyOrderedAdd.** 是 Mathlib 中的一个实例，位于命名空间 `CanonicallyOrderedAdd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toMulLeftMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulLeftMono R := by
  refine ⟨fun a b c h => ?_⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

-- see Note [lower instance priority]
/-
**CanonicallyOrderedAdd.** 是 Mathlib 中的一个实例，位于命名空间 `CanonicallyOrderedAdd`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toMulRightMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulRightMono R := by
  refine ⟨fun a b c h => ?_⟩
  dsimp [swap]
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [add_mul]
  apply self_le_add_right

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

-- TODO: make it an instance
/-
**CanonicallyOrderedAdd.toIsOrderedMonoid** 是 Mathlib 中的一个引理，位于命名空间 `Canonically
OrderedAdd`。
形式化陈述：toIsOrderedMonoid : IsOrderedMonoid R where mul_le_mul_left _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
-/
lemma toIsOrderedMonoid : IsOrderedMonoid R where
  mul_le_mul_left _ _ := mul_le_mul_left

-- TODO: make it an instance
/-
**CanonicallyOrderedAdd.toIsOrderedRing** 是 Mathlib 中的一个引理，位于命名空间 `CanonicallyOr
deredAdd`。
形式化陈述：toIsOrderedRing : IsOrderedRing R where add_le_add_left _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `MulLeftMono.toPosMulMono`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero
 α] [inst_2 : Preorder α] [MulLeftMono α], PosMulMono α
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `MulRightMono.toMulPosMono`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zer
o α] [inst_2 : Preorder α] [MulRightMono α], MulPosMono α
-/
lemma toIsOrderedRing : IsOrderedRing R where
  add_le_add_left _ _ := add_le_add_left

@[simp]
/-
**CanonicallyOrderedAdd.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `CanonicallyOrderedAdd
`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : PartialOrder R] [Canonica
llyOrderedAdd R] [NoZeroDivisors R] {a b : R},   0 < a * b ↔ 0 < a ∧ 0 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem mul_pos [NoZeroDivisors R] {a b : R} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
/-
**CanonicallyOrderedAdd.pow_pos** 是 Mathlib 中的一个引理，位于命名空间 `CanonicallyOrderedAdd
`。
形式化陈述：pow_pos [IsReduced R] {a : R} (ha : 0 < a) (n : Nat) : 0 < a ^ n
参数：ha : 0 < a；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
lemma pow_pos [IsReduced R] {a : R} (ha : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ ha.ne'
/-
**CanonicallyOrderedAdd.mul_lt_mul_of_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Canoni
callyOrderedAdd`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : PartialOrder R] [Canonica
llyOrderedAdd R] [PosMulStrictMono R]   {a b c d : R}, a < b → c < d → a * c < b
 * d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `posMulStrictMono_iff_mulPosStrictMono`：posMulStrictMono_iff_mulPosStrict
Mono : PosMulStrictMono α ↔ MulPosStrictMono α
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_lt_mul_of_pos'`：mul_lt_mul_of_pos' [PosMulStrictMono α] [MulPosStric
tMono α] (h₁ : a < b) (h₂ : c < d) (c0 : 0 < c) (b0 : 0 < b) : a * c < b * d
-/
protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono R] {a b c d : R} (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos hab.pos hcd
  · exact mul_lt_mul_of_pos' hab hcd hc hab.pos

end CanonicallyOrderedAdd

section Sub

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

namespace AddLECancellable

/-
**AddLECancellable.mul_tsub** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R] [inst_1 : PartialOrder
 R] [CanonicallyOrderedAdd R] [inst_3 : Sub R]   [OrderedSub R] [Std.Total fun x
1 x2 => x1 ≤ x2] {a b c : R}, AddLECancellable (a * c) → a * (b - c) = a * b - a
 * c
参数：a * c；b - c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
-/
protected theorem mul_tsub {a b c : R}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  obtain (hbc | hcb) := total_of (· ≤ ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]
/-
**AddLECancellable.tsub_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddLECancellable`。
形式化陈述：∀ {R : Type u} [inst : NonUnitalNonAssocSemiring R] [inst_1 : PartialOrder
 R] [CanonicallyOrderedAdd R] [inst_3 : Sub R]   [OrderedSub R] [Std.Total fun x
1 x2 => x1 ≤ x2] [MulRightMono R] {a b c : R},   AddLECancellable (b * c) → (a -
 b) * c = a * c - b * c
参数：b * c；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `AddLECancellable.eq_tsub_of_add_eq`：∀ {α : Type u_1} [inst : PartialOrde
r α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}, 
  AddLECancellable c → a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
-/
protected theorem tsub_mul [MulRightMono R] {a b c : R}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  obtain (hab | hba) := total_of (· ≤ ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul, tsub_add_cancel_of_le hba]

end AddLECancellable

variable [AddLeftReflectLE R]

/-
**mul_tsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_tsub (a b c : R) : a * (b - c) = a * b - a * c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.mul_tsub`：∀ {R : Type u} [inst : NonUnitalNonAssocSemir
ing R] [inst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [inst_3 : Sub R]   [O
rderedSub R] [S…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem mul_tsub (a b c : R) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub
/-
**tsub_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - b * c
参数：a b c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_mul`：∀ {R : Type u} [inst : NonUnitalNonAssocSemir
ing R] [inst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [inst_3 : Sub R]   [O
rderedSub R] [S…
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
-/
theorem tsub_mul [MulRightMono R] (a b c : R) :
    (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

/-
**mul_tsub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_tsub_one [AddLeftReflectLE R] (a b : R) : a * (b - 1) = a * b - a
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_tsub`：mul_tsub (a b c : R) : a * (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma mul_tsub_one [AddLeftReflectLE R] (a b : R) :
    a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
/-
**tsub_one_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsub_one_mul [MulRightMono R] [AddLeftReflectLE R] (a b : R) : (a - 1) * b
 = a * b - b
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_mul`：tsub_mul [MulRightMono R] (a b c : R) : (a - b) * c = a * c - 
b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma tsub_one_mul [MulRightMono R] [AddLeftReflectLE R] (a b : R) :
    (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end NonAssocSemiring

section CommSemiring

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)] [AddLeftReflectLE R]

/-- The `tsub` version of `mul_self_sub_mul_self`. Notably, this holds for `Nat` and `NNReal`. -/
/-
**mul_self_tsub_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_tsub_mul_self (a b : R) : a * a - b * b = (a + b) * (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_tsub`：mul_tsub (a b c : R) : a * (b - c) = a * b - a * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `tsub_add_eq_tsub_tsub`：tsub_add_eq_tsub_tsub (a b c : α) : a - (b + c) =
 a - b - c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a

--- 原说明 ---
The `tsub` version of `mul_self_sub_mul_self`. Notably, this holds for `Nat` and
 `NNReal`.
-/
theorem mul_self_tsub_mul_self (a b : R) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub, add_mul, add_mul, tsub_add_eq_tsub_tsub, mul_comm b a, add_tsub_cancel_right]

/-- The `tsub` version of `sq_sub_sq`. Notably, this holds for `Nat` and `NNReal`. -/
/-
**sq_tsub_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sq_tsub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_self_tsub_mul_self`：mul_self_tsub_mul_self (a b : R) : a * a - b * b
 = (a + b) * (a - b)

--- 原说明 ---
The `tsub` version of `sq_sub_sq`. Notably, this holds for `Nat` and `NNReal`.
-/
theorem sq_tsub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_tsub_mul_self]
/-
**mul_self_tsub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_tsub_one (a : R) : a * a - 1 = (a + 1) * (a - 1)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_self_tsub_mul_self`：mul_self_tsub_mul_self (a b : R) : a * a - b * b
 = (a + b) * (a - b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_self_tsub_one (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self, mul_one]

end CommSemiring

end Sub

