/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# `ZMod p` is a field
-/

@[expose] public section

namespace ZMod
variable (p : Nat) [hp : Fact p.Prime]

set_option backward.privateInPublic true in
/--
theorem `mul_inv_cancel_aux` / 定理 `mul_inv_cancel_aux`

English:
theorem mul_inv_cancel_aux
  given: (a : ZMod p) (h : a != 0)
  statement: a * a⁻¹ = 1
  proof: by
  obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]

中文:
定理 mul_inv_cancel_aux
  条件: (a : ZMod p) (h : a != 0)
  结论: a * a⁻¹ = 1
  证明: by
  obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]
-/
private theorem mul_inv_cancel_aux (a : ZMod p) (h : a != 0) : a * a⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field (ZMod p)
  body: mul_inv_cancel_aux p
  inv_zero := inv_zero p
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
实例 :
  签名: 域 (ZMod p)
  定义体: mul_inv_cancel_aux p
  inv_zero := inv_zero p
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: mul_inv_cancel_aux
-/
instance : Field (ZMod p) where
  mul_inv_cancel := mul_inv_cancel_aux p
  inv_zero := inv_zero p
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDomain (ZMod p)
  body: by constructor

中文:
实例 :
  签名: 是整环 (ZMod p)
  定义体: by constructor
-/
instance : IsDomain (ZMod p) := by constructor

end ZMod
