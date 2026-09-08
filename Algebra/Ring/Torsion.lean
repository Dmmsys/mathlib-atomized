/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Ring.Commute

/-!
# Torsion-free rings

A characteristic zero domain is torsion-free.
-/

public section

namespace IsDomain

-- This instance is potentially expensive, and is known to slow down grind.
-- Please keep it as a scoped instance.
/-
**IsDomain.** 是 Mathlib 中的一个实例，位于命名空间 `IsDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (R : Type*) [Semiring R] [IsDomain R] [CharZero R] :
    IsAddTorsionFree R where
  nsmul_right_injective n h a b w := by
    simp only [nsmul_eq_mul, mul_eq_mul_left_iff, Nat.cast_eq_zero] at w
    grind

end IsDomain

namespace MonoidHom
variable {R M : Type*} [Ring R] [Monoid M] [IsMulTorsionFree M] (f : R →* M)

/-
**MonoidHom.map_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：map_neg_one : f (-1) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pow_eq_one_iff_left`：pow_eq_one_iff_left (hn : n != 0) : a ^ n = 1 ↔ a =
 1
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff_left (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]
/-
**MonoidHom.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : Monoid M] [IsMul
TorsionFree M] (f : R →* M) (x : R),   f (-x) = f x
参数：f : R →* M；x : R；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `MonoidHom.map_neg_one`：map_neg_one : f (-1) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[simp] lemma map_neg (x : R) : f (-x) = f x := by rw [← neg_one_mul, map_mul, map_neg_one, one_mul]
/-
**MonoidHom.map_sub_swap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：map_sub_swap (x y : R) : f (x - y) = f (y - x)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_neg`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst
_1 : Monoid M] [IsMulTorsionFree M] (f : R →* M) (x : R),   f (-x) = f x
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
lemma map_sub_swap (x y : R) : f (x - y) = f (y - x) := by rw [← map_neg, neg_sub]

end MonoidHom

