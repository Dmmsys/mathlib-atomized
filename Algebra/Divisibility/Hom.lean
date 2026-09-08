/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Mapping divisibility across multiplication-preserving homomorphisms

## Main definitions

* `map_dvd`

## Tags

divisibility, divides
-/

public section

attribute [local simp] mul_assoc mul_comm mul_left_comm

variable {M N : Type*}

@[gcongr]
/-
**map_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : Semigroup N
] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f : F) {a b : M
}, a ∣ b → f a ∣ f b
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_dvd [Semigroup M] [Semigroup N] {F : Type*} [FunLike F M N] [MulHomClass F M N]
    (f : F) {a b} : a ∣ b → f a ∣ f b
  | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩
/-
**MulHom.map_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulHom.map_dvd [Semigroup M] [Semigroup N] (f : M ->ₙ* N) {a b} : a ∣ b ->
 f a ∣ f b
参数：f : M ->ₙ* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
-/
theorem MulHom.map_dvd [Semigroup M] [Semigroup N] (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f
/-
**MonoidHom.map_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M ->* N) {a b} : a ∣ b -> f a
 ∣ f b
参数：f : M ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem MonoidHom.map_dvd [Monoid M] [Monoid N] (f : M →* N) {a b} : a ∣ b → f a ∣ f b :=
  _root_.map_dvd f
