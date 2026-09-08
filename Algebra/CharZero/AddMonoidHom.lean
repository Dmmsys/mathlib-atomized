/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Transporting `CharZero` across injective `AddMonoidHom`s

This file exists in order to avoid adding extra imports to other files in this subdirectory.
-/

public section

/-
**CharZero.of_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMo
noidWithOne N] [CharZero M] (e : M ->+ N) (he : e 1 = 1) (he' : Function.Injecti
ve e) : CharZero N where cast_injective n m h
参数：e : M ->+ N；he : e 1 = 1；he' : Function.Injective e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast'`：map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [Add
MonoidHomClass F A B] (f : F) (h : f 1 = 1) : forall n : Nat, f n = n
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem CharZero.of_addMonoidHom {M N : Type*} [AddCommMonoidWithOne M] [AddCommMonoidWithOne N]
    [CharZero M] (e : M →+ N) (he : e 1 = 1) (he' : Function.Injective e) : CharZero N where
  cast_injective n m h := by
    rwa [← map_natCast' _ he, ← map_natCast' _ he, he'.eq_iff, Nat.cast_inj] at h
