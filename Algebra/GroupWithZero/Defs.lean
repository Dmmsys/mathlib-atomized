/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Basic
public import Batteries.Tactic.SeqFocus

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/

public section

assert_not_exists DenselyOrdered Ring

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ : Type*}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
/-
**MulZeroClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for expressing that a type `M₀` with multiplication and a zero satisfi
es
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`.
-/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/-- A mixin for left cancellative multiplication by nonzero elements. -/
/-
**IsLeftCancelMulZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u) → [Mul M₀] → [Zero M₀] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin for left cancellative multiplication by nonzero elements.
-/
@[mk_iff] class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsLeftRegular a

section IsLeftCancelMulZero
section Mul
variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

/-
**mul_left_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_cancel : a * b = a * c -> b = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftCancelMul.mul_left_cancel`：∀ {G : Type u} {inst : Mul G} [self : I
sLeftCancelMul G] (a : G), IsLeftRegular a
-/
theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h
/-
**mul_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_injective (a : G) : Injective (a * ·)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
-/
theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha
/-
**mul_right_inj'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
-/
lemma mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := (mul_right_injective₀ ha).eq_iff

end Mul

variable [MulZeroClass M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

/-
**mul_eq_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsLeftCancelMulZero M₀] {a b c
 : M₀}, a * b = a * c ↔ b = c ∨ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
@[simp] lemma mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp only [ha, zero_mul, or_true]; simp [mul_right_inj', ha]]

end IsLeftCancelMulZero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
/-
**IsRightCancelMulZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u) → [Mul M₀] → [Zero M₀] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin for right cancellative multiplication by nonzero elements.
-/
@[mk_iff] class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsRightRegular a

section IsRightCancelMulZero
section Mul
variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

/-
**mul_right_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_cancel : a * b = c * b -> a = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRightCancelMul.mul_right_cancel`：∀ {G : Type u} {inst : Mul G} [self :
 IsRightCancelMul G] (a : G), IsRightRegular a
-/
theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h
/-
**mul_left_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_injective (a : G) : Function.Injective (· * a)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
-/
theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb
/-
**mul_left_inj'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
-/
lemma mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := (mul_left_injective₀ hc).eq_iff

end Mul

variable [MulZeroClass M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

/-
**mul_eq_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [IsRightCancelMulZero M₀] {a b 
c : M₀}, a * c = b * c ↔ a = b ∨ c = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
@[simp] lemma mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp only [hc, mul_zero, or_true]; simp [mul_left_inj', hc]]

end IsRightCancelMulZero

/-- A mixin for cancellative multiplication by nonzero elements. -/
/-
**IsCancelMulZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u) → [Mul M₀] → [Zero M₀] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A mixin for cancellative multiplication by nonzero elements.
-/
@[mk_iff] class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀
/-
**isCancelMulZero_iff_forall_isRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] : IsCancelMul
Zero M₀ ↔ forall {a : M₀}, a != 0 -> IsRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isRegular_iff`：isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ I
sRightRegular c
-/
theorem isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] :
    IsCancelMulZero M₀ ↔ ∀ {a : M₀}, a ≠ 0 → IsRegular a := by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ ↦ isRegular_iff.symm

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general,
but equivalent to it if `M₀` is a (not necessarily unital or associative) ring. -/
/-
**NoZeroDivisors** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u_2) → [Mul M₀] → [Zero M₀] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general
,
but equivalent to it if `M₀` is a (not necessarily unital or associative) ring.
-/
@[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
/-
**SemigroupWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, a
nd `0` is left
and right absorbing.
-/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/-- A typeclass for non-associative monoids with zero elements. -/
/-
**MulZeroOneClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for non-associative monoids with zero elements.
-/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
/-
**MonoidWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0`
 is left
and right absorbing.
-/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

section MonoidWithZero

variable [MonoidWithZero M₀]

/-- If `x` is multiplicative with respect to `f`, then so is any `x^n`. -/
/-
**pow_mul_apply_eq_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ -> M) {x : M₀} (hx
 : forall y : M₀, f (x * y) = f x * f y) (n : Nat) : forall (y : M₀), f (x ^ n *
 y) = f x ^ n * f y
参数：f : M₀ -> M；hx : forall y : M₀, f (x * y) = f x * f y；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
If `x` is multiplicative with respect to `f`, then so is any `x^n`.
-/
theorem pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ → M) {x : M₀}
    (hx : ∀ y : M₀, f (x * y) = f x * f y) (n : ℕ) :
    ∀ (y : M₀), f (x ^ n * y) = f x ^ n * f y := by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

end MonoidWithZero

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[deprecated "Use `[MonoidWithZero M₀] [IsCancelMulZero M₀].`" (since := "2026-01-11")]
/-
**CancelMonoidWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` 
is left
and right absorbing, and left/right multiplication by a non-zero element is inje
ctive.
-/
structure CancelMonoidWithZero (M₀ : Type*) extends MonoidWithZero M₀, IsCancelMulZero M₀

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
/-
**CommMonoidWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `M` is a commutative “monoid with zero” if it is a commutative monoid wit
h zero
element, and `0` is left and right absorbing.
-/
class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀

section MulZeroClass

variable (M₀) [MulZeroClass M₀]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) IsLeftCancelMulZero.to_noZeroDivisors [IsLeftCancelMulZero M₀] :
    NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {x _} h :=
    or_iff_not_imp_left.mpr fun ne ↦ mul_left_cancel₀ ne ((mul_zero x).symm ▸ h)

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) IsRightCancelMulZero.to_noZeroDivisors [IsRightCancelMulZero M₀] :
    NoZeroDivisors M₀ where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ y} h :=
    or_iff_not_imp_right.mpr fun ne ↦ mul_right_cancel₀ ne ((zero_mul y).symm ▸ h)

end MulZeroClass

section CommMagma

variable [CommMagma M₀] [Zero M₀]

/-
**IsLeftCancelMulZero.to_isRightCancelMulZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] : IsR
ightCancelMulZero M₀ where mul_right_cancel_of_ne_zero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero :=
    fun hb _ _ h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _))
/-
**IsRightCancelMulZero.to_isLeftCancelMulZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] : Is
LeftCancelMulZero M₀ where mul_left_cancel_of_ne_zero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero :=
    fun hb _ _ h => mul_right_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _))
/-
**IsLeftCancelMulZero.to_isCancelMulZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] : IsCancel
MulZero M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLeftCancelMulZero.to_isRightCancelMulZero`：IsLeftCancelMulZero.to_isRi
ghtCancelMulZero [IsLeftCancelMulZero M₀] : IsRightCancelMulZero M₀ where mul_ri
ght_cancel_of_ne_zero
-/
lemma IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsLeftCancelMulZero.to_isRightCancelMulZero with }
/-
**IsRightCancelMulZero.to_isCancelMulZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] : IsCanc
elMulZero M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsRightCancelMulZero.to_isLeftCancelMulZero`：IsRightCancelMulZero.to_isL
eftCancelMulZero [IsRightCancelMulZero M₀] : IsLeftCancelMulZero M₀ where mul_le
ft_cancel_of_ne_zero
-/
lemma IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsRightCancelMulZero.to_isLeftCancelMulZero with }

end CommMagma

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
`0` is left and right absorbing,
and left/right multiplication by a non-zero element is injective. -/
@[deprecated "Use `[CommMonoidWithZero M₀] [IsCancelMulZero M₀].`" (since := "2026-01-11")]
/-
**CancelCommMonoidWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with ze
ro element,
`0` is left and right absorbing,
and left/right multiplication by a non-zero element is injective.
-/
structure CancelCommMonoidWithZero (M₀ : Type*)
    extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀

/-- Prop-valued mixin for a monoid with zero to be equipped with a cancelling division.

The obvious use case is groups with zero, but this condition is also satisfied by `ℕ`, `ℤ` and, more
generally, any Euclidean domain. -/
/-
**MulDivCancelClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M₀ : Type u_2) → [MonoidWithZero M₀] → [Div M₀] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prop-valued mixin for a monoid with zero to be equipped with a cancelling divisi
on.

The obvious use case is groups with zero, but this condition is also satisfied b
y `ℕ`, `ℤ` and, more
generally, any Euclidean domain.
-/
class MulDivCancelClass (M₀ : Type*) [MonoidWithZero M₀] [Div M₀] : Prop where
  protected mul_div_cancel (a b : M₀) : b ≠ 0 → a * b / b = a

section MulDivCancelClass
variable [MonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

/-
**mul_div_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel_right (a b : G) : a * b / b = a
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
@[simp] lemma mul_div_cancel_right₀ (a : M₀) {b : M₀} (hb : b ≠ 0) : a * b / b = a :=
  MulDivCancelClass.mul_div_cancel _ _ hb

end MulDivCancelClass

section MulDivCancelClass
variable [CommMonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

/-
**mul_div_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_div_cancel_left (a b : G) : a * b / a = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
@[simp] lemma mul_div_cancel_left₀ (b : M₀) {a : M₀} (ha : a ≠ 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_right₀ _ ha]

end MulDivCancelClass

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory. -/
/-
**GroupWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct
 from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` 
must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.
-/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  protected inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  protected mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

section GroupWithZero
variable [GroupWithZero G₀] {a : G₀}

/-
**inv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
-/
@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 := GroupWithZero.inv_zero

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel`
/-
**mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_cancel (a : G) : a * a⁻¹ = 1
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `_private.Mathlib.Algebra.Group.Defs.0.inv_eq_of_mul`：∀ {G : Type u_1} [i
nst : Group G] {a b : G}, a * b = 1 → a⁻¹ = b
-/
lemma mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GroupWithZero.toMulDivCancelClass : MulDivCancelClass G₀ where
  mul_div_cancel a b hb := by rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hb, mul_one]

end GroupWithZero

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
/-
**CommGroupWithZero** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` 
must be `0`.
-/
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀
/-
**eq_zero_or_one_of_sq_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eq_zero_or_one_of_sq_eq_self [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
 {x : M₀} (hx : x ^ 2 = x) : x = 0 ∨ x = 1
参数：hx : x ^ 2 = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
lemma eq_zero_or_one_of_sq_eq_self [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
    {x : M₀} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

section GroupWithZero

variable [GroupWithZero G₀] {a b : G₀}

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`
/-
**mul_inv_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`
/-
**mul_inv_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

end GroupWithZero

section MulZeroClass

variable [MulZeroClass M₀]

/-
**mul_eq_zero_of_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0
参数：h : a = 0；b : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b
/-
**mul_eq_zero_of_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0
参数：a : M₀；h : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a
/-
**noZeroDivisors_iff_right_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_iff_right_eq_zero_of_mul : NoZeroDivisors M₀ ↔ forall x : M
₀, x != 0 -> forall y, x * y = 0 -> y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma noZeroDivisors_iff_right_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, x * y = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq ↦ h eq ha, fun h a b eq ha ↦ h a ha b eq⟩
/-
**noZeroDivisors_iff_left_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_iff_left_eq_zero_of_mul : NoZeroDivisors M₀ ↔ forall x : M₀
, x != 0 -> forall y, y * x = 0 -> y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma noZeroDivisors_iff_left_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, y * x = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq ↦ h eq hb, fun h a b eq hb ↦ h b hb a eq⟩
/-
**noZeroDivisors_iff_eq_zero_of_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：noZeroDivisors_iff_eq_zero_of_mul : NoZeroDivisors M₀ ↔ forall x : M₀, x !
= 0 -> (forall y, x * y = 0 -> y = 0) ∧ (forall y, y * x = 0 -> y = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma noZeroDivisors_iff_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → (∀ y, x * y = 0 → y = 0) ∧ (∀ y, y * x = 0 → y = 0) := by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
/-
**mul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0

--- 原说明 ---
If `α` has no zero divisors, then the product of two elements equals zero iff on
e of them
equals zero.
-/
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o ↦ o.elim (fun h ↦ mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
/-
**zero_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm_eq`：eq_comm_eq {α : Sort*} (a b : α) : (a = b) = (b = a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `α` has no zero divisors, then the product of two elements equals zero iff on
e of them
equals zero.
-/
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by simp [eqComm]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
/-
**mul_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q

--- 原说明 ---
If `α` has no zero divisors, then the product of two elements is nonzero iff bot
h of them
are nonzero.
-/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := mul_eq_zero.not.trans not_or

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
/-
**mul_eq_zero_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_comm : a * b = 0 ↔ b * a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)

--- 原说明 ---
If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero i
ff so is
`b * a`.
-/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
/-
**mul_ne_zero_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_zero_comm : a * b != 0 ↔ b * a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mul_eq_zero_comm`：mul_eq_zero_comm : a * b = 0 ↔ b * a = 0

--- 原说明 ---
If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero if
f so is
`b * a`.
-/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 := mul_eq_zero_comm.not
/-
**mul_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_eq_zero : a * a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
/-
**zero_eq_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_eq_mul_self : 0 = a * a ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
/-
**mul_self_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_self_ne_zero : a * a != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
-/
theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not
/-
**zero_ne_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_ne_mul_self : 0 != a * a ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `zero_eq_mul_self`：zero_eq_mul_self : 0 = a * a ↔ a = 0
-/
theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not
/-
**mul_eq_zero_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_iff_left (ha : a != 0) : a * b = 0 ↔ b = 0
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_eq_zero_iff_left (ha : a ≠ 0) : a * b = 0 ↔ b = 0 := by simp [ha]
/-
**mul_eq_zero_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_zero_iff_right (hb : b != 0) : a * b = 0 ↔ a = 0
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_eq_zero_iff_right (hb : b ≠ 0) : a * b = 0 ↔ a = 0 := by simp [hb]
/-
**mul_ne_zero_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_zero_iff_left (ha : a != 0) : a * b != 0 ↔ b != 0
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_ne_zero_iff_left (ha : a ≠ 0) : a * b ≠ 0 ↔ b ≠ 0 := by simp [ha]
/-
**mul_ne_zero_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_ne_zero_iff_right (hb : b != 0) : a * b != 0 ↔ a != 0
参数：hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mul_ne_zero_iff_right (hb : b ≠ 0) : a * b ≠ 0 ↔ a ≠ 0 := by simp [hb]

end MulZeroClass

