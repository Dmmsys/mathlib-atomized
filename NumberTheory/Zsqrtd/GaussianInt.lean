/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Gaussian integers

The Gaussian integers are complex integer, complex numbers whose real and imaginary parts are both
integers.

## Main definitions

The Euclidean domain structure on `ℤ[i]` is defined in this file.

The homomorphism `GaussianInt.toComplex` into the complex numbers is also defined in this file.

## See also

See `NumberTheory.Zsqrtd.QuadraticReciprocity` for:
* `prime_iff_mod_four_eq_three_of_nat_prime`:
  A prime natural number is prime in `ℤ[i]` if and only if it is `3` mod `4`

## Notation

This file uses the local notation `ℤ[i]` for `GaussianInt`

## Implementation notes

Gaussian integers are implemented using the more general definition `Zsqrtd`, the type of integers
adjoined a square root of `d`, in this case `-1`. The definition is reducible, so that properties
and definitions about `Zsqrtd` can easily be used.
-/

@[expose] public section


open Zsqrtd Complex

open scoped ComplexConjugate

/-- The Gaussian integers, defined as `ℤ√(-1)`. -/
/-
**GaussianInt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GaussianInt : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Gaussian integers, defined as `ℤ√(-1)`.
-/
abbrev GaussianInt : Type :=
  Zsqrtd (-1)

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

/-
**GaussianInt.** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr ℤ[i] :=
  ⟨fun x _ => "⟨" ++ repr x.re ++ ", " ++ repr x.im ++ "⟩"⟩
/-
**GaussianInt.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
形式化陈述：instCommRing : CommRing Int[i]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing ℤ[i] :=
  Zsqrtd.commRing

section

attribute [-instance] Complex.instField -- Avoid making things noncomputable unnecessarily.

/-- The embedding of the Gaussian integers into the complex numbers, as a ring homomorphism. -/
/-
**GaussianInt.toComplex** 是 Mathlib 中的一个定义，位于命名空间 `GaussianInt`。
形式化陈述：toComplex : Int[i] ->+* Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the Gaussian integers into the complex numbers, as a ring homom
orphism.
-/
def toComplex : ℤ[i] →+* ℂ :=
  Zsqrtd.lift ⟨I, by simp⟩

end

/-
**GaussianInt.** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe ℤ[i] ℂ :=
  ⟨toComplex⟩
/-
**GaussianInt.toComplex_def** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_def (x : Int[i]) : (x : Complex) = x.re + x.im * I
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toComplex_def (x : ℤ[i]) : (x : ℂ) = x.re + x.im * I :=
  rfl
/-
**GaussianInt.toComplex_def'** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_def' (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex) = x + y * I
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toComplex_def' (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ) = x + y * I := by simp [toComplex_def]
/-
**GaussianInt.toComplex_def** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_def (x : Int[i]) : (x : Complex) = x.re + x.im * I
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toComplex_def₂ (x : ℤ[i]) : (x : ℂ) = ⟨x.re, x.im⟩ := by
  apply Complex.ext <;> simp [toComplex_def]

@[simp]
/-
**GaussianInt.intCast_re** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：intCast_re (x : Int[i]) : ((x.re : Int) : Real) = (x : Complex).re
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_re (x : ℤ[i]) : ((x.re : ℤ) : ℝ) = (x : ℂ).re := by simp [toComplex_def]

@[simp]
/-
**GaussianInt.intCast_im** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：intCast_im (x : Int[i]) : ((x.im : Int) : Real) = (x : Complex).im
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_im (x : ℤ[i]) : ((x.im : ℤ) : ℝ) = (x : ℂ).im := by simp [toComplex_def]

@[simp]
/-
**GaussianInt.re_toComplex** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：re_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex).re = x
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem re_toComplex (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).re = x := by simp [toComplex_def]

@[simp]
/-
**GaussianInt.im_toComplex** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：im_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) : Complex).im = y
参数：x y : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem im_toComplex (x y : ℤ) : ((⟨x, y⟩ : ℤ[i]) : ℂ).im = y := by simp [toComplex_def]
/-
**GaussianInt.toComplex_add** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_add (x y : Int[i]) : ((x + y : Int[i]) : Complex) = x + y
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
-/
theorem toComplex_add (x y : ℤ[i]) : ((x + y : ℤ[i]) : ℂ) = x + y :=
  toComplex.map_add _ _
/-
**GaussianInt.toComplex_mul** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_mul (x y : Int[i]) : ((x * y : Int[i]) : Complex) = x * y
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
-/
theorem toComplex_mul (x y : ℤ[i]) : ((x * y : ℤ[i]) : ℂ) = x * y :=
  toComplex.map_mul _ _
/-
**GaussianInt.toComplex_one** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_one : ((1 : Int[i]) : Complex) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem toComplex_one : ((1 : ℤ[i]) : ℂ) = 1 :=
  toComplex.map_one
/-
**GaussianInt.toComplex_zero** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_zero : ((0 : Int[i]) : Complex) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
-/
theorem toComplex_zero : ((0 : ℤ[i]) : ℂ) = 0 :=
  toComplex.map_zero
/-
**GaussianInt.toComplex_neg** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_neg (x : Int[i]) : ((-x : Int[i]) : Complex) = -x
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_neg`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x : α), f (-x) = -f x
-/
theorem toComplex_neg (x : ℤ[i]) : ((-x : ℤ[i]) : ℂ) = -x :=
  toComplex.map_neg _
/-
**GaussianInt.toComplex_sub** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_sub (x y : Int[i]) : ((x - y : Int[i]) : Complex) = x - y
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
theorem toComplex_sub (x y : ℤ[i]) : ((x - y : ℤ[i]) : ℂ) = x - y :=
  toComplex.map_sub _ _

@[simp]
/-
**GaussianInt.toComplex_star** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_star (x : Int[i]) : ((star x : Int[i]) : Complex) = conj (x : Co
mplex)
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaussianInt.toComplex_def₂`：toComplex_def₂ (x : Int[i]) : (x : Complex) 
= ⟨x.re, x.im⟩
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
theorem toComplex_star (x : ℤ[i]) : ((star x : ℤ[i]) : ℂ) = conj (x : ℂ) := by
  rw [toComplex_def₂, toComplex_def₂]
  exact congr_arg₂ _ rfl (Int.cast_neg _)

@[simp]
/-
**GaussianInt.toComplex_inj** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_inj {x y : Int[i]} : (x : Complex) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaussianInt.toComplex_def₂`：toComplex_def₂ (x : Int[i]) : (x : Complex) 
= ⟨x.re, x.im⟩
· 使用定理 `Complex.mk.injEq`：∀ (re im re_1 im_1 : ℝ), ({ re := re, im := im } = { r
e := re_1, im := im_1 }) = (re = re_1 ∧ im = im_1)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Zsqrtd.mk.injEq`：∀ {d : ℤ} (re im re_1 im_1 : ℤ), ({ re := re, im := im 
} = { re := re_1, im := im_1 }) = (re = re_1 ∧ im = im_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toComplex_inj {x y : ℤ[i]} : (x : ℂ) = y ↔ x = y := by
  cases x; cases y; simp [toComplex_def₂]
/-
**GaussianInt.toComplex_injective** 是 Mathlib 中的一个引理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_injective : Function.Injective GaussianInt.toComplex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GaussianInt.toComplex_inj`：toComplex_inj {x y : Int[i]} : (x : Complex) 
= y ↔ x = y
-/
lemma toComplex_injective : Function.Injective GaussianInt.toComplex :=
  fun ⦃_ _⦄ ↦ toComplex_inj.mp

@[simp]
/-
**GaussianInt.toComplex_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_eq_zero {x : Int[i]} : (x : Complex) = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaussianInt.toComplex_zero`：toComplex_zero : ((0 : Int[i]) : Complex) = 
0
· 使用定理 `GaussianInt.toComplex_inj`：toComplex_inj {x y : Int[i]} : (x : Complex) 
= y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toComplex_eq_zero {x : ℤ[i]} : (x : ℂ) = 0 ↔ x = 0 := by
  rw [← toComplex_zero, toComplex_inj]

@[simp]
/-
**GaussianInt.intCast_real_norm** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：intCast_real_norm (x : Int[i]) : (x.norm : Real) = Complex.normSq (x : Com
plex)
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm.eq_1`：∀ {d : ℤ} (n : ℤ√d), n.norm = n.re * n.re - d * n.im *
 n.im
· 使用定理 `Complex.normSq.eq_1`：Complex.normSq =   { toFun := fun z => z.re * z.re 
+ z.im * z.im, map_zero' := Complex.normSq._proof_1,     map_one' := Complex.nor
mSq._proo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `GaussianInt.intCast_re`：intCast_re (x : Int[i]) : ((x.re : Int) : Real) 
= (x : Complex).re
· 使用定理 `GaussianInt.intCast_im`：intCast_im (x : Int[i]) : ((x.im : Int) : Real) 
= (x : Complex).im
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_real_norm (x : ℤ[i]) : (x.norm : ℝ) = Complex.normSq (x : ℂ) := by
  rw [Zsqrtd.norm, normSq]; simp

@[simp]
/-
**GaussianInt.intCast_complex_norm** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：intCast_complex_norm (x : Int[i]) : (x.norm : Complex) = Complex.normSq (x
 : Complex)
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm.eq_1`：∀ {d : ℤ} (n : ℤ√d), n.norm = n.re * n.re - d * n.im *
 n.im
· 使用定理 `Complex.normSq.eq_1`：Complex.normSq =   { toFun := fun z => z.re * z.re 
+ z.im * z.im, map_zero' := Complex.normSq._proof_1,     map_one' := Complex.nor
mSq._proo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `GaussianInt.re_toComplex`：re_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) 
: Complex).re = x
· 使用定理 `GaussianInt.im_toComplex`：im_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) 
: Complex).im = y
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem intCast_complex_norm (x : ℤ[i]) : (x.norm : ℂ) = Complex.normSq (x : ℂ) := by
  cases x; rw [Zsqrtd.norm, normSq]; simp
/-
**GaussianInt.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：norm_nonneg (x : Int[i]) : 0 <= norm x
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zsqrtd.norm_nonneg`：norm_nonneg (hd : d <= 0) (n : Int√d) : 0 <= n.norm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem norm_nonneg (x : ℤ[i]) : 0 ≤ norm x :=
  Zsqrtd.norm_nonneg (by simp) _

@[simp]
/-
**GaussianInt.norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：norm_eq_zero {x : Int[i]} : norm x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_inj`：cast_inj : (m : α) = n ↔ m = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GaussianInt.intCast_real_norm`：intCast_real_norm (x : Int[i]) : (x.norm 
: Real) = Complex.normSq (x : Complex)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_eq_zero {x : ℤ[i]} : norm x = 0 ↔ x = 0 := by rw [← Int.cast_inj (α := ℝ)]; simp
/-
**GaussianInt.norm_pos** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：norm_pos {x : Int[i]} : 0 < norm x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `GaussianInt.norm_eq_zero`：norm_eq_zero {x : Int[i]} : norm x = 0 ↔ x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_pos {x : ℤ[i]} : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, Ne, eq_comm, norm_eq_zero]; simp [norm_nonneg]
/-
**GaussianInt.abs_natCast_norm** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：abs_natCast_norm (x : Int[i]) : (x.norm.natAbs : Int) = x.norm
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用定理 `GaussianInt.norm_nonneg`：norm_nonneg (x : Int[i]) : 0 <= norm x
-/
theorem abs_natCast_norm (x : ℤ[i]) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)
/-
**GaussianInt.natCast_natAbs_norm** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：natCast_natAbs_norm {α : Type*} [AddGroupWithOne α] (x : Int[i]) : (x.norm
.natAbs : α) = x.norm
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `Zsqrtd.abs_norm`：abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_natAbs_norm {α : Type*} [AddGroupWithOne α] (x : ℤ[i]) :
    (x.norm.natAbs : α) = x.norm := by
  simp
/-
**GaussianInt.natAbs_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：natAbs_norm_eq (x : Int[i]) : x.norm.natAbs = x.re.natAbs * x.re.natAbs + 
x.im.natAbs * x.im.natAbs
参数：x : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Zsqrtd.abs_norm`：abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `abs_mul_abs_self`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder
 α] (a : α), |a| * |a| = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natAbs_norm_eq (x : ℤ[i]) :
    x.norm.natAbs = x.re.natAbs * x.re.natAbs + x.im.natAbs * x.im.natAbs := by
  zify
  rw [abs_norm (by simp)]
  simp [Zsqrtd.norm]
/-
**GaussianInt.** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div ℤ[i] :=
  ⟨fun x y =>
    let n := (norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n : ℚ), round ((x * c).im * n : ℚ)⟩⟩
/-
**GaussianInt.div_def** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：div_def (x y : Int[i]) : x / y = ⟨round ((x * star y).re / norm y : Rat), 
round ((x * star y).im / norm y : Rat)⟩
参数：x y : Int[i]。
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
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div_def (x y : ℤ[i]) :
    x / y = ⟨round ((x * star y).re / norm y : ℚ), round ((x * star y).im / norm y : ℚ)⟩ :=
  show Zsqrtd.mk _ _ = _ by simp [div_eq_mul_inv]
/-
**GaussianInt.toComplex_re_div** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_re_div (x y : Int[i]) : ((x / y : Int[i]) : Complex).re = round 
(x / y : Complex).re
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaussianInt.div_def`：div_def (x y : Int[i]) : x / y = ⟨round ((x * star 
y).re / norm y : Rat), round ((x * star y).im / norm y : Rat)⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.round_cast`：round_cast (x : Rat) : round (x : α) = round x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `GaussianInt.intCast_re`：intCast_re (x : Int[i]) : ((x.re : Int) : Real) 
= (x : Complex).re
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `GaussianInt.intCast_real_norm`：intCast_real_norm (x : Int[i]) : (x.norm 
: Real) = Complex.normSq (x : Complex)
· 使用定理 `GaussianInt.intCast_im`：intCast_im (x : Int[i]) : ((x.im : Int) : Real) 
= (x : Complex).im
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `GaussianInt.re_toComplex`：re_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) 
: Complex).re = x
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
（共 33 条，此处仅展示前 30 条）
-/
theorem toComplex_re_div (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).re = round (x / y : ℂ).re := by
  rw [div_def, ← @Rat.round_cast ℝ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]
/-
**GaussianInt.toComplex_im_div** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：toComplex_im_div (x y : Int[i]) : ((x / y : Int[i]) : Complex).im = round 
(x / y : Complex).im
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaussianInt.div_def`：div_def (x y : Int[i]) : x / y = ⟨round ((x * star 
y).re / norm y : Rat), round ((x * star y).im / norm y : Rat)⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.round_cast`：round_cast (x : Rat) : round (x : α) = round x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `GaussianInt.intCast_re`：intCast_re (x : Int[i]) : ((x.re : Int) : Real) 
= (x : Complex).re
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `GaussianInt.intCast_real_norm`：intCast_real_norm (x : Int[i]) : (x.norm 
: Real) = Complex.normSq (x : Complex)
· 使用定理 `GaussianInt.intCast_im`：intCast_im (x : Int[i]) : ((x.im : Int) : Real) 
= (x : Complex).im
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
· 使用定理 `GaussianInt.im_toComplex`：im_toComplex (x y : Int) : ((⟨x, y⟩ : Int[i]) 
: Complex).im = y
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
（共 33 条，此处仅展示前 30 条）
-/
theorem toComplex_im_div (x y : ℤ[i]) : ((x / y : ℤ[i]) : ℂ).im = round (x / y : ℂ).im := by
  rw [div_def, ← @Rat.round_cast ℝ _ _, ← @Rat.round_cast ℝ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]
/-
**GaussianInt.normSq_le_normSq_of_re_le_of_im_le** 是 Mathlib 中的一个定理，位于命名空间 `Gaus
sianInt`。
形式化陈述：normSq_le_normSq_of_re_le_of_im_le {x y : Complex} (hre : |x.re| <= |y.re|
) (him : |x.im| <= |y.im|) : normSq x <= normSq y
参数：hre : |x.re| <= |y.re|；him : |x.im| <= |y.im|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 50 条，此处仅展示前 30 条）
-/
theorem normSq_le_normSq_of_re_le_of_im_le {x y : ℂ} (hre : |x.re| ≤ |y.re|)
    (him : |x.im| ≤ |y.im|) : normSq x ≤ normSq y := by
  simp only [normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]
/-
**GaussianInt.normSq_div_sub_div_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：normSq_div_sub_div_lt_one (x y : Int[i]) : Complex.normSq ((x / y : Comple
x) - ((x / y : Int[i]) : Complex)) < 1
参数：x y : Int[i]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.mul_re`：mul_re (z w : Complex) : (z * w).re = z.re * w.re - z.im
 * w.im
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.mul_im`：mul_im (z w : Complex) : (z * w).im = z.re * w.im + z.im
 * w.re
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `GaussianInt.normSq_le_normSq_of_re_le_of_im_le`：normSq_le_normSq_of_re_l
e_of_im_le {x y : Complex} (hre : |x.re| <= |y.re|) (him : |x.im| <= |y.im|) : n
ormSq x <= normSq y
· 使用定理 `GaussianInt.toComplex_re_div`：toComplex_re_div (x y : Int[i]) : ((x / y 
: Int[i]) : Complex).re = round (x / y : Complex).re
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Complex.inv_re`：inv_re (z : Complex) : z⁻¹.re = z.re / normSq z
· 使用定理 `div_self_mul_self'`：div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹
· 使用定理 `Complex.inv_im`：inv_im (z : Complex) : z⁻¹.im = -z.im / normSq z
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
（共 41 条，此处仅展示前 30 条）
-/
theorem normSq_div_sub_div_lt_one (x y : ℤ[i]) :
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ)) < 1 :=
  calc
    Complex.normSq ((x / y : ℂ) - ((x / y : ℤ[i]) : ℂ))
    _ = Complex.normSq
      ((x / y : ℂ).re - ((x / y : ℤ[i]) : ℂ).re + ((x / y : ℂ).im - ((x / y : ℤ[i]) : ℂ).im) *
        I : ℂ) :=
      congr_arg _ <| by apply Complex.ext <;> simp
    _ ≤ Complex.normSq (1 / 2 + 1 / 2 * I) := by
      have : |(2⁻¹ : ℝ)| = 2⁻¹ := abs_of_nonneg (by simp)
      exact normSq_le_normSq_of_re_le_of_im_le
        (by rw [toComplex_re_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).re)
        (by rw [toComplex_im_div]; simp [normSq, this]; simpa using abs_sub_round (x / y : ℂ).im)
    _ < 1 := by simp [normSq]; norm_num
/-
**GaussianInt.** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mod ℤ[i] :=
  ⟨fun x y => x - y * (x / y)⟩
/-
**GaussianInt.mod_def** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：mod_def (x y : Int[i]) : x % y = x - y * (x / y)
参数：x y : Int[i]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mod_def (x y : ℤ[i]) : x % y = x - y * (x / y) :=
  rfl
/-
**GaussianInt.norm_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：norm_mod_lt (x : Int[i]) {y : Int[i]} (hy : y != 0) : (x % y).norm < y.nor
m
参数：x : Int[i]；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaussianInt.toComplex_zero`：toComplex_zero : ((0 : Int[i]) : Complex) = 
0
· 使用定理 `GaussianInt.toComplex_inj`：toComplex_inj {x y : Int[i]} : (x : Complex) 
= y ↔ x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GaussianInt.intCast_real_norm`：intCast_real_norm (x : Int[i]) : (x.norm 
: Real) = Complex.normSq (x : Complex)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.normSq_mul`：normSq_mul (z w : Complex) : normSq (z * w) = normSq
 z * normSq w
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `GaussianInt.normSq_div_sub_div_lt_one`：normSq_div_sub_div_lt_one (x y : 
Int[i]) : Complex.normSq ((x / y : Complex) - ((x / y : Int[i]) : Complex)) < 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.normSq_pos`：normSq_pos {z : Complex} : 0 < normSq z ↔ z != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) : (x % y).norm < y.norm :=
  have : (y : ℂ) ≠ 0 := by rwa [Ne, ← toComplex_zero, toComplex_inj]
  (@Int.cast_lt ℝ _ _ _ _).1 <|
    calc
      ↑(Zsqrtd.norm (x % y)) = Complex.normSq (x - y * (x / y : ℤ[i]) : ℂ) := by simp [mod_def]
      _ = Complex.normSq (y : ℂ) * Complex.normSq (x / y - (x / y : ℤ[i]) : ℂ) := by
        rw [← normSq_mul, mul_sub, mul_div_cancel₀ _ this]
      _ < Complex.normSq (y : ℂ) * 1 :=
        (mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one _ _) (normSq_pos.2 this))
      _ = Zsqrtd.norm y := by simp
/-
**GaussianInt.natAbs_norm_mod_lt** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：natAbs_norm_mod_lt (x : Int[i]) {y : Int[i]} (hy : y != 0) : (x % y).norm.
natAbs < y.norm.natAbs
参数：x : Int[i]；hy : y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `Zsqrtd.abs_norm`：abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `GaussianInt.norm_mod_lt`：norm_mod_lt (x : Int[i]) {y : Int[i]} (hy : y !
= 0) : (x % y).norm < y.norm
-/
theorem natAbs_norm_mod_lt (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 <| by simp [norm_mod_lt x hy]
/-
**GaussianInt.norm_le_norm_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `GaussianInt`。
形式化陈述：norm_le_norm_mul_left (x : Int[i]) {y : Int[i]} (hy : y != 0) : (norm x).n
atAbs <= (norm (x * y)).natAbs
参数：x : Int[i]；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_mul`：norm_mul (n m : Int√d) : norm (n * m) = norm n * norm m
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `GaussianInt.abs_natCast_norm`：abs_natCast_norm (x : Int[i]) : (x.norm.na
tAbs : Int) = x.norm
· 使用定理 `Int.add_one_le_of_lt`：∀ {a b : ℤ}, a < b → a + 1 ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GaussianInt.norm_pos`：norm_pos {x : Int[i]} : 0 < norm x ↔ x != 0
-/
theorem norm_le_norm_mul_left (x : ℤ[i]) {y : ℤ[i]} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.1 (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.2 hy)))
/-
**GaussianInt.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
形式化陈述：instNontrivial : Nontrivial Int[i]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
instance instNontrivial : Nontrivial ℤ[i] :=
  ⟨⟨0, 1, by decide⟩⟩
/-
**GaussianInt.** 是 Mathlib 中的一个实例，位于命名空间 `GaussianInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EuclideanDomain ℤ[i] :=
  { GaussianInt.instCommRing,
    GaussianInt.instNontrivial with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun _ _ => by simp [mod_def]
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a _ hb0 => not_lt_of_ge <| norm_le_norm_mul_left a hb0 }

open PrincipalIdealRing
/-
**GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible** 是 Mathlib 中的一个定理，位于命名空
间 `GaussianInt`。
形式化陈述：sq_add_sq_of_nat_prime_of_not_irreducible (p : Nat) [hp : Fact p.Prime] (h
pi : ¬Irreducible (p : Int[i])) : exists a b, a ^ 2 + b ^ 2 = p
参数：p : Nat；hpi : ¬Irreducible (p : Int[i])。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Zsqrtd.norm_eq_one_iff`：norm_eq_one_iff {x : Int√d} : x.norm.natAbs = 1 
↔ IsUnit x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Zsqrtd.norm_natCast`：norm_natCast (n : Nat) : norm (n : Int√d) = n * n
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `mul_eq_one`：mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.mul_eq_prime_sq_iff`：∀ {x y p : ℕ}, Nat.Prime p → x ≠ 1 → y ≠ 
1 → (x * y = p ^ 2 ↔ x = p ∧ y = p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用定理 `Int.natCast_pow`：∀ (m n : ℕ), ↑(m ^ n) = ↑m ^ n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `Zsqrtd.abs_norm`：abs_norm (hd : d <= 0) (n : Int√d) : |n.norm| = n.norm
（共 33 条，此处仅展示前 30 条）
-/
theorem sq_add_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ℤ[i])) : ∃ a b, a ^ 2 + b ^ 2 = p :=
  have hpu : ¬IsUnit (p : ℤ[i]) :=
    mt norm_eq_one_iff.2 <| by
      rw [norm_natCast, Int.natAbs_mul, mul_eq_one]
      exact fun h => (ne_of_lt hp.1.one_lt).symm h.1
  have hab : ∃ a b, (p : ℤ[i]) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  let ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : (norm a).natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt norm_eq_one_iff.1 hau) (mt norm_eq_one_iff.1 hbu)).1 <| by
        rw [← Int.natCast_inj, Int.natCast_pow, sq, ← @norm_natCast (-1), hpab]; simp).1
  ⟨a.re.natAbs, a.im.natAbs, by simpa [natAbs_norm_eq, sq] using hnap⟩

end GaussianInt

