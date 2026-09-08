/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Equiv

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

ring aut
-/

@[expose] public section

variable (R : Type*) [Mul R] [Add R]

/-- The group of ring automorphisms. -/
/-
**RingAut** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：RingAut
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of ring automorphisms.
-/
abbrev RingAut := RingEquiv R R

namespace RingAut

/-- The group operation on automorphisms of a ring is defined by
`fun g h => RingEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`. -/
/-
**RingAut.** 是 Mathlib 中的一个实例，位于命名空间 `RingAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group operation on automorphisms of a ring is defined by
`fun g h => RingEquiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Group (RingAut R) where
  mul g h := RingEquiv.trans h g
  one := RingEquiv.refl R
  inv := RingEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := RingEquiv.self_trans_symm
/-
**RingAut.** 是 Mathlib 中的一个实例，位于命名空间 `RingAut`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RingAut R) :=
  ⟨1⟩

/-- Monoid homomorphism from ring automorphisms to additive automorphisms. -/
/-
**RingAut.toAddAut** 是 Mathlib 中的一个定义，位于命名空间 `RingAut`。
形式化陈述：toAddAut : RingAut R ->* Multiplicative (AddAut R) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid homomorphism from ring automorphisms to additive automorphisms.
-/
def toAddAut : RingAut R →* Multiplicative (AddAut R) where
  toFun := RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism from ring automorphisms to multiplicative automorphisms. -/
/-
**RingAut.toMulAut** 是 Mathlib 中的一个定义，位于命名空间 `RingAut`。
形式化陈述：toMulAut : RingAut R ->* MulAut R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid homomorphism from ring automorphisms to multiplicative automorphisms.
-/
def toMulAut : RingAut R →* MulAut R where
  toFun := RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Monoid homomorphism from ring automorphisms to permutations. -/
/-
**RingAut.toPerm** 是 Mathlib 中的一个定义，位于命名空间 `RingAut`。
形式化陈述：toPerm : RingAut R ->* Equiv.Perm R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoid homomorphism from ring automorphisms to permutations.
-/
def toPerm : RingAut R →* Equiv.Perm R where
  toFun := RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

variable {R}
/-
**RingAut.one_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：one_eq_refl : (1 : R ≃+* R) = RingEquiv.refl R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq_refl : (1 : R ≃+* R) = RingEquiv.refl R := rfl

@[simp]
/-
**RingAut.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：one_apply (x : R) : (1 : R ≃+* R) x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : R) : (1 : R ≃+* R) x = x := rfl

@[simp]
/-
**RingAut.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：coe_one : ⇑(1 : R ≃+* R) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : R ≃+* R) = id := rfl

@[simp]
/-
**RingAut.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x)
参数：f g : R ≃+* R；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : R ≃+* R) (x : R) : (f * g) x = f (g x) := rfl

@[simp]
/-
**RingAut.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：inv_apply (f : R ≃+* R) (x : R) : f⁻¹ x = f.symm x
参数：f : R ≃+* R；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply (f : R ≃+* R) (x : R) : f⁻¹ x = f.symm x := rfl

@[simp]
/-
**RingAut.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `RingAut`。
形式化陈述：coe_pow (f : R ≃+* R) (n : Nat) : ⇑(f ^ n) = f^[n]
参数：f : R ≃+* R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem coe_pow (f : R ≃+* R) (n : ℕ) : ⇑(f ^ n) = f^[n] := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ext
    simp [pow_succ, ih]

end RingAut

