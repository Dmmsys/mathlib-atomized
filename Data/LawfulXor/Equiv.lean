/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Algebra.Group.End

/-!
# LawfulXor equivalences
-/

@[expose] public section

namespace Equiv

open LawfulXor

variable {α β : Type*} [XorOp α] [Zero α] [LawfulXor α] {a b c : α}

/--
Definition of `xor` / `xor` 的定义

English:
definition xor
  signature: (a : α)
  body: (a ^^^ ·)
  invFun := (a ^^^ ·)
  left_inv := xor_cancel_left a
  right_inv := xor_cancel_left a

中文:
定义 xor
  签名: (a : α)
  定义体: (a ^^^ ·)
  invFun := (a ^^^ ·)
  left_inv := xor_cancel_left a
  right_inv := xor_cancel_left a
-/
@[simps! apply] protected def xor (a : α) : Perm α where
  toFun := (a ^^^ ·)
  invFun := (a ^^^ ·)
  left_inv := xor_cancel_left a
  right_inv := xor_cancel_left a

/--
theorem `xor_symm` / 定理 `xor_symm`

English:
theorem xor_symm
  statement: (Equiv.xor a).symm = Equiv.xor a
  proof: rfl

中文:
定理 xor_symm
  结论: (Equiv.xor a).symm = Equiv.xor a
  证明: rfl
-/
@[simp] theorem xor_symm : (Equiv.xor a).symm = Equiv.xor a := rfl

/--
theorem `xor_involutive` / 定理 `xor_involutive`

English:
theorem xor_involutive
  given: (a : α)
  statement: Function.Involutive (Equiv.xor a)
  proof: xor_right_involutive a

中文:
定理 xor_involutive
  条件: (a : α)
  结论: Function.Involutive (Equiv.xor a)
  证明: xor_right_involutive a

Depends on / 依赖: xor_right_involutive
-/
theorem xor_involutive (a : α) : Function.Involutive (Equiv.xor a) := xor_right_involutive a

/--
theorem `xor_zero` / 定理 `xor_zero`

English:
theorem xor_zero
  statement: Equiv.xor (0 : α) = 1
  proof: Equiv.ext zero_xor

中文:
定理 xor_zero
  结论: Equiv.xor (0 : α) = 1
  证明: Equiv.ext zero_xor
-/
@[simp] theorem xor_zero : Equiv.xor (0 : α) = 1 := Equiv.ext zero_xor

/--
theorem `xor_eq_one_iff` / 定理 `xor_eq_one_iff`

English:
theorem xor_eq_one_iff
  statement: Equiv.xor a = 1 ↔ a = 0
  proof: Equiv.coe_inj.symm.trans xor_left_eq_id_iff

中文:
定理 xor_eq_one_iff
  结论: Equiv.xor a = 1 ↔ a = 0
  证明: Equiv.coe_inj.symm.trans xor_left_eq_id_iff
-/
@[simp] theorem xor_eq_one_iff : Equiv.xor a = 1 ↔ a = 0 :=
  Equiv.coe_inj.symm.trans xor_left_eq_id_iff

/--
theorem `isFixedPt_xor` / 定理 `isFixedPt_xor`

English:
theorem isFixedPt_xor
  statement: Function.IsFixedPt (Equiv.xor a) b ↔ a = 0
  proof: isFixedPt_xor_left_iff

中文:
定理 isFixedPt_xor
  结论: Function.IsFixedPt (Equiv.xor a) b ↔ a = 0
  证明: isFixedPt_xor_left_iff

Depends on / 依赖: isFixedPt_xor_left_iff
-/
theorem isFixedPt_xor : Function.IsFixedPt (Equiv.xor a) b ↔ a = 0 := isFixedPt_xor_left_iff

/--
theorem `xor_trans_xor` / 定理 `xor_trans_xor`

English:
theorem xor_trans_xor
  statement: (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b)
  proof: Equiv.ext (.symm <| xor_assoc a b ·)

中文:
定理 xor_trans_xor
  结论: (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b)
  证明: Equiv.ext (.symm <| xor_assoc a b ·)
-/
@[simp] theorem xor_trans_xor : (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b) :=
Equiv.ext (.symm <| xor_assoc a b ·)

end Equiv
