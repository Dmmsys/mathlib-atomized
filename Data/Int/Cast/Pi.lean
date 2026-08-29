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

variable {ι : Type*} {π : ι -> Type*} [forall i, IntCast (π i)]

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: : IntCast (forall i, π i) where intCast n _
  body: n

@[simp]

中文:
实例 inst整数Cast
  签名: : 整数嵌入 (对任意 i, π i) where intCast n _
  定义体: n

@[simp]
-/
instance instIntCast : IntCast (forall i, π i) where intCast n _ := n

@[simp]
/--
theorem `intCast_apply` / 定理 `intCast_apply`

English:
theorem intCast_apply
  given: (n : Int) (i : ι)
  statement: (n : forall i, π i) i = n
  proof: rfl

@[push ←]

中文:
定理 intCast_apply
  条件: (n : 整数) (i : ι)
  结论: (n : 对任意 i, π i) i = n
  证明: rfl

@[push ←]
-/
theorem intCast_apply (n : Int) (i : ι) : (n : forall i, π i) i = n :=
  rfl

@[push ←]
/--
theorem `intCast_def` / 定理 `intCast_def`

English:
theorem intCast_def
  given: (n : Int)
  statement: (n : forall i, π i) = fun _ => ↑n
  proof: rfl

中文:
定理 intCast_def
  条件: (n : 整数)
  结论: (n : 对任意 i, π i) = fun _ => ↑n
  证明: rfl
-/
theorem intCast_def (n : Int) : (n : forall i, π i) = fun _ => ↑n :=
  rfl

end Pi

@[simp]
/--
theorem `Sum.elim_intCast_intCast` / 定理 `Sum.elim_intCast_intCast`

English:
theorem Sum.elim_intCast_intCast
  given: {α β γ : Type*} [IntCast γ] (n : Int)
  proof: Sum.elim_lam_const_lam_const (γ := γ) n

中文:
定理 和.elim_intCast_intCast
  条件: {α β γ : 类型} [整数嵌入 γ] (n : 整数)
  证明: Sum.elim_lam_const_lam_const (γ := γ) n

Depends on / 依赖: Sum.elim_lam_const_lam_const, elim_lam_const_lam_const
-/
theorem Sum.elim_intCast_intCast {α β γ : Type*} [IntCast γ] (n : Int) :
    Sum.elim (n : α -> γ) (n : β -> γ) = n :=
  Sum.elim_lam_const_lam_const (γ := γ) n
