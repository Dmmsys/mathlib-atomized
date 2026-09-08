/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Push.Attr

/-!
# Cast of integers to function types

This file provides a (pointwise) cast from `ℤ` to function types.

## Main declarations

* `Pi.instIntCast`: map `n : ℤ` to the constant function `n : ∀ i, π i`
-/

@[expose] public section

assert_not_exists IsOrderedMonoid RingHom

namespace Pi

variable {ι : Type*} {π : ι → Type*} [∀ i, IntCast (π i)]

/-
**Pi.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：instIntCast : IntCast (forall i, π i) where intCast n _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast (∀ i, π i) where intCast n _ := n

@[simp]
/-
**Pi.intCast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：intCast_apply (n : Int) (i : ι) : (n : forall i, π i) i = n
参数：n : Int；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_apply (n : ℤ) (i : ι) : (n : ∀ i, π i) i = n :=
  rfl

@[push ←]
/-
**Pi.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：intCast_def (n : Int) : (n : forall i, π i) = fun _ => ↑n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_def (n : ℤ) : (n : ∀ i, π i) = fun _ => ↑n :=
  rfl

end Pi

@[simp]
/-
**Sum.elim_intCast_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : Int) : Sum.elim 
(n : α -> γ) (n : β -> γ) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.elim_lam_const_lam_const`：∀ {γ : Sort u_1} {α : Type u_2} {β : Type 
u_3} (c : γ), (Sum.elim (fun x => c) fun x => c) = fun x => c
-/
theorem Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : ℤ) :
    Sum.elim (n : α → γ) (n : β → γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
