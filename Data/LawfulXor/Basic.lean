/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

module
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fin.Init

/-!
# The `LawfulXor` typeclass

This file generalizes basic lemmas about the `^^^` operator across numeric types.
-/

@[expose] public section

/--
Definition of `LawfulXor` / `LawfulXor` 的定义

English:
class LawfulXor
  parameters: (α : Type*) [XorOp α] [Zero α]
  axioms and operations (4):
    - xor_assoc((a b c : α)) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
    - xor_self((a : α)) : a ^^^ a = 0
    - xor_zero((a : α)) : a ^^^ 0 = a
    - xor_comm((a b : α)) : a ^^^ b = b ^^^ a

中文:
类 LawfulXor
  参数: (α : 类型) [XorOp α] [Zero α]
  公理与运算 (4 个):
    - xor_assoc((a b c : α)) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
    - xor_self((a : α)) : a ^^^ a = 0
    - xor_zero((a : α)) : a ^^^ 0 = a
    - xor_comm((a b : α)) : a ^^^ b = b ^^^ a
-/
class LawfulXor (α : Type*) [XorOp α] [Zero α] where
  xor_assoc (a b c : α) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c)
  xor_self (a : α) : a ^^^ a = 0
  xor_zero (a : α) : a ^^^ 0 = a
  xor_comm (a b : α) : a ^^^ b = b ^^^ a

export LawfulXor (xor_assoc xor_self xor_zero xor_comm)

variable {α : Type*} [XorOp α] [Zero α] [LawfulXor α]

attribute [simp] xor_zero LawfulXor.xor_self

@[simp]
/--
theorem `zero_xor` / 定理 `zero_xor`

English:
theorem zero_xor
  given: (a : α)
  statement: 0 ^^^ a = a
  proof: by rw [LawfulXor.xor_comm, xor_zero]

中文:
定理 zero_xor
  条件: (a : α)
  结论: 0 ^^^ a = a
  证明: by rw [LawfulXor.xor_comm, xor_zero]

Depends on / 依赖: LawfulXor, LawfulXor.xor_comm, xor_comm, xor_zero
-/
theorem zero_xor (a : α) : 0 ^^^ a = a := by rw [LawfulXor.xor_comm, xor_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Commutative (α := α) XorOp.xor
  body: xor_comm

中文:
实例 :
  签名: Std.Commutative (α := α) XorOp.xor
  定义体: xor_comm

Depends on / 依赖: XorOp.xor, xor_comm
-/
instance : Std.Commutative (α := α) XorOp.xor where comm := xor_comm
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Associative (α := α) XorOp.xor
  body: xor_assoc

中文:
实例 :
  签名: Std.Associative (α := α) XorOp.xor
  定义体: xor_assoc

Depends on / 依赖: XorOp.xor, xor_assoc
-/
instance : Std.Associative (α := α) XorOp.xor where assoc := xor_assoc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.LawfulCommIdentity (α := α) XorOp.xor 0
  body: zero_xor
  right_id := xor_zero

@[simp]

中文:
实例 :
  签名: Std.LawfulCommIdentity (α := α) XorOp.xor 0
  定义体: zero_xor
  right_id := xor_zero

@[simp]

Depends on / 依赖: XorOp.xor
-/
instance : Std.LawfulCommIdentity (α := α) XorOp.xor 0 where
  left_id := zero_xor
  right_id := xor_zero

@[simp]
/--
theorem `xor_cancel_left` / 定理 `xor_cancel_left`

English:
theorem xor_cancel_left
  given: (a b : α)
  statement: a ^^^ (a ^^^ b) = b
  proof: by
  rw [← xor_assoc]; rw [LawfulXor.xor_self]; rw [zero_xor]

@[simp]

中文:
定理 xor_cancel_left
  条件: (a b : α)
  结论: a ^^^ (a ^^^ b) = b
  证明: by
  rw [← xor_assoc]; rw [LawfulXor.xor_self]; rw [zero_xor]

@[simp]

Depends on / 依赖: LawfulXor, LawfulXor.xor_self, xor_assoc, xor_self, zero_xor
-/
theorem xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b := by
  rw [← xor_assoc]; rw [LawfulXor.xor_self]; rw [zero_xor]

@[simp]
/--
theorem `xor_cancel_right` / 定理 `xor_cancel_right`

English:
theorem xor_cancel_right
  given: (a b : α)
  statement: (a ^^^ b) ^^^ b = a
  proof: by
  rw [xor_assoc]; rw [LawfulXor.xor_self]; rw [xor_zero]

中文:
定理 xor_cancel_right
  条件: (a b : α)
  结论: (a ^^^ b) ^^^ b = a
  证明: by
  rw [xor_assoc]; rw [LawfulXor.xor_self]; rw [xor_zero]

Depends on / 依赖: LawfulXor, LawfulXor.xor_self, xor_assoc, xor_self, xor_zero
-/
theorem xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a := by
  rw [xor_assoc]; rw [LawfulXor.xor_self]; rw [xor_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor Nat
  body: Nat.xor_assoc
  xor_comm := Nat.xor_comm
  xor_self := Nat.xor_self
  xor_zero := Nat.xor_zero

中文:
实例 :
  签名: LawfulXor 自然数
  定义体: Nat.xor_assoc
  xor_comm := Nat.xor_comm
  xor_self := Nat.xor_self
  xor_zero := Nat.xor_zero
-/
instance : LawfulXor Nat where
  xor_assoc := Nat.xor_assoc
  xor_comm := Nat.xor_comm
  xor_self := Nat.xor_self
  xor_zero := Nat.xor_zero

instance {w : Nat} : LawfulXor (Fin (2 ^ w)) where
  xor_assoc := Fin.xor_assoc rfl
  xor_comm := Fin.xor_comm
  xor_self := Fin.xor_self
  xor_zero := Fin.xor_zero

instance {w : Nat} : LawfulXor (BitVec w) where
  xor_assoc := BitVec.xor_assoc
  xor_comm := BitVec.xor_comm
  xor_self _ := BitVec.xor_self
  xor_zero _ := BitVec.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor UInt8
  body: UInt8.xor_assoc
  xor_comm := UInt8.xor_comm
  xor_self _ := UInt8.xor_self
  xor_zero _ := UInt8.xor_zero

中文:
实例 :
  签名: LawfulXor U整数8
  定义体: UInt8.xor_assoc
  xor_comm := UInt8.xor_comm
  xor_self _ := UInt8.xor_self
  xor_zero _ := UInt8.xor_zero

Depends on / 依赖: UInt8.xor_assoc, xor_assoc
-/
instance : LawfulXor UInt8 where
  xor_assoc := UInt8.xor_assoc
  xor_comm := UInt8.xor_comm
  xor_self _ := UInt8.xor_self
  xor_zero _ := UInt8.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor UInt16
  body: UInt16.xor_assoc
  xor_comm := UInt16.xor_comm
  xor_self _ := UInt16.xor_self
  xor_zero _ := UInt16.xor_zero

中文:
实例 :
  签名: LawfulXor U整数16
  定义体: UInt16.xor_assoc
  xor_comm := UInt16.xor_comm
  xor_self _ := UInt16.xor_self
  xor_zero _ := UInt16.xor_zero

Depends on / 依赖: UInt16, UInt16.xor_assoc, xor_assoc
-/
instance : LawfulXor UInt16 where
  xor_assoc := UInt16.xor_assoc
  xor_comm := UInt16.xor_comm
  xor_self _ := UInt16.xor_self
  xor_zero _ := UInt16.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor UInt32
  body: UInt32.xor_assoc
  xor_comm := UInt32.xor_comm
  xor_self _ := UInt32.xor_self
  xor_zero _ := UInt32.xor_zero

中文:
实例 :
  签名: LawfulXor U整数32
  定义体: UInt32.xor_assoc
  xor_comm := UInt32.xor_comm
  xor_self _ := UInt32.xor_self
  xor_zero _ := UInt32.xor_zero

Depends on / 依赖: UInt32, UInt32.xor_assoc, xor_assoc
-/
instance : LawfulXor UInt32 where
  xor_assoc := UInt32.xor_assoc
  xor_comm := UInt32.xor_comm
  xor_self _ := UInt32.xor_self
  xor_zero _ := UInt32.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor UInt64
  body: UInt64.xor_assoc
  xor_comm := UInt64.xor_comm
  xor_self _ := UInt64.xor_self
  xor_zero _ := UInt64.xor_zero

中文:
实例 :
  签名: LawfulXor U整数64
  定义体: UInt64.xor_assoc
  xor_comm := UInt64.xor_comm
  xor_self _ := UInt64.xor_self
  xor_zero _ := UInt64.xor_zero

Depends on / 依赖: UInt64, UInt64.xor_assoc, xor_assoc
-/
instance : LawfulXor UInt64 where
  xor_assoc := UInt64.xor_assoc
  xor_comm := UInt64.xor_comm
  xor_self _ := UInt64.xor_self
  xor_zero _ := UInt64.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor USize
  body: USize.xor_assoc
  xor_comm := USize.xor_comm
  xor_self _ := USize.xor_self
  xor_zero _ := USize.xor_zero

中文:
实例 :
  签名: LawfulXor USize
  定义体: USize.xor_assoc
  xor_comm := USize.xor_comm
  xor_self _ := USize.xor_self
  xor_zero _ := USize.xor_zero

Depends on / 依赖: USize.xor_assoc, xor_assoc
-/
instance : LawfulXor USize where
  xor_assoc := USize.xor_assoc
  xor_comm := USize.xor_comm
  xor_self _ := USize.xor_self
  xor_zero _ := USize.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor Int8
  body: Int8.xor_assoc
  xor_comm := Int8.xor_comm
  xor_self _ := Int8.xor_self
  xor_zero _ := Int8.xor_zero

中文:
实例 :
  签名: LawfulXor 整数8
  定义体: Int8.xor_assoc
  xor_comm := Int8.xor_comm
  xor_self _ := Int8.xor_self
  xor_zero _ := Int8.xor_zero
-/
instance : LawfulXor Int8 where
  xor_assoc := Int8.xor_assoc
  xor_comm := Int8.xor_comm
  xor_self _ := Int8.xor_self
  xor_zero _ := Int8.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor Int16
  body: Int16.xor_assoc
  xor_comm := Int16.xor_comm
  xor_self _ := Int16.xor_self
  xor_zero _ := Int16.xor_zero

中文:
实例 :
  签名: LawfulXor 整数16
  定义体: Int16.xor_assoc
  xor_comm := Int16.xor_comm
  xor_self _ := Int16.xor_self
  xor_zero _ := Int16.xor_zero
-/
instance : LawfulXor Int16 where
  xor_assoc := Int16.xor_assoc
  xor_comm := Int16.xor_comm
  xor_self _ := Int16.xor_self
  xor_zero _ := Int16.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor Int32
  body: Int32.xor_assoc
  xor_comm := Int32.xor_comm
  xor_self _ := Int32.xor_self
  xor_zero _ := Int32.xor_zero

中文:
实例 :
  签名: LawfulXor 整数32
  定义体: Int32.xor_assoc
  xor_comm := Int32.xor_comm
  xor_self _ := Int32.xor_self
  xor_zero _ := Int32.xor_zero

Depends on / 依赖: Int32.xor_assoc, xor_assoc
-/
instance : LawfulXor Int32 where
  xor_assoc := Int32.xor_assoc
  xor_comm := Int32.xor_comm
  xor_self _ := Int32.xor_self
  xor_zero _ := Int32.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor Int64
  body: Int64.xor_assoc
  xor_comm := Int64.xor_comm
  xor_self _ := Int64.xor_self
  xor_zero _ := Int64.xor_zero

中文:
实例 :
  签名: LawfulXor 整数64
  定义体: Int64.xor_assoc
  xor_comm := Int64.xor_comm
  xor_self _ := Int64.xor_self
  xor_zero _ := Int64.xor_zero

Depends on / 依赖: Int64.xor_assoc, xor_assoc
-/
instance : LawfulXor Int64 where
  xor_assoc := Int64.xor_assoc
  xor_comm := Int64.xor_comm
  xor_self _ := Int64.xor_self
  xor_zero _ := Int64.xor_zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulXor ISize
  body: ISize.xor_assoc
  xor_comm := ISize.xor_comm
  xor_self _ := ISize.xor_self
  xor_zero _ := ISize.xor_zero

中文:
实例 :
  签名: LawfulXor ISize
  定义体: ISize.xor_assoc
  xor_comm := ISize.xor_comm
  xor_self _ := ISize.xor_self
  xor_zero _ := ISize.xor_zero

Depends on / 依赖: ISize.xor_assoc, xor_assoc
-/
instance : LawfulXor ISize where
  xor_assoc := ISize.xor_assoc
  xor_comm := ISize.xor_comm
  xor_self _ := ISize.xor_self
  xor_zero _ := ISize.xor_zero

/--
lemma `xor_right_eq` / 引理 `xor_right_eq`

English:
lemma xor_right_eq
  given: {a : α}
  statement: (· ^^^ a) = (a ^^^ ·)
  proof: funext (xor_comm · a)

中文:
引理 xor_right_eq
  条件: {a : α}
  结论: (· ^^^ a) = (a ^^^ ·)
  证明: funext (xor_comm · a)

Depends on / 依赖: xor_comm
-/
lemma xor_right_eq {a : α} : (· ^^^ a) = (a ^^^ ·) := funext (xor_comm · a)

/--
lemma `xor_left_involutive` / 引理 `xor_left_involutive`

English:
lemma xor_left_involutive
  given: (a : α)
  statement: Function.Involutive (· ^^^ a)
  proof: (xor_cancel_right · a)

中文:
引理 xor_left_involutive
  条件: (a : α)
  结论: Function.Involutive (· ^^^ a)
  证明: (xor_cancel_right · a)

Depends on / 依赖: xor_cancel_right
-/
lemma xor_left_involutive (a : α) : Function.Involutive (· ^^^ a) := (xor_cancel_right · a)
/--
lemma `xor_right_involutive` / 引理 `xor_right_involutive`

English:
lemma xor_right_involutive
  given: (a : α)
  statement: Function.Involutive (a ^^^ ·)
  proof: xor_cancel_left a

中文:
引理 xor_right_involutive
  条件: (a : α)
  结论: Function.Involutive (a ^^^ ·)
  证明: xor_cancel_left a

Depends on / 依赖: xor_cancel_left
-/
lemma xor_right_involutive (a : α) : Function.Involutive (a ^^^ ·) := xor_cancel_left a

/--
lemma `xor_eq_iff_left_eq` / 引理 `xor_eq_iff_left_eq`

English:
lemma xor_eq_iff_left_eq
  given: (a b c : α)
  proof: xor_left_involutive _

中文:
引理 xor_eq_iff_left_eq
  条件: (a b c : α)
  证明: xor_left_involutive _

Depends on / 依赖: xor_left_involutive
-/
lemma xor_eq_iff_left_eq (a b c : α) :
.eq_iff a ^^^ b = c ↔ a = c ^^^ b := xor_left_involutive _
/--
lemma `xor_eq_iff_right_eq` / 引理 `xor_eq_iff_right_eq`

English:
lemma xor_eq_iff_right_eq
  given: (a b c : α)
  proof: xor_right_involutive _

中文:
引理 xor_eq_iff_right_eq
  条件: (a b c : α)
  证明: xor_right_involutive _

Depends on / 依赖: xor_right_involutive
-/
lemma xor_eq_iff_right_eq (a b c : α) :
.eq_iff a ^^^ b = c ↔ b = a ^^^ c := xor_right_involutive _

/--
lemma `xor_eq_zero_iff` / 引理 `xor_eq_zero_iff`

English:
lemma xor_eq_zero_iff
  given: {a b : α}
  statement: a ^^^ b = 0 ↔ a = b
  proof: by
  rw [xor_eq_iff_left_eq]; rw [zero_xor]

中文:
引理 xor_eq_zero_iff
  条件: {a b : α}
  结论: a ^^^ b = 0 ↔ a = b
  证明: by
  rw [xor_eq_iff_left_eq]; rw [zero_xor]
-/
@[simp] lemma xor_eq_zero_iff {a b : α} : a ^^^ b = 0 ↔ a = b := by
  rw [xor_eq_iff_left_eq]; rw [zero_xor]

/--
lemma `xor_xor_cancel_comm` / 引理 `xor_xor_cancel_comm`

English:
lemma xor_xor_cancel_comm
  given: (a b : α)
  statement: a ^^^ b ^^^ a = b
  proof: by
  rw [xor_comm a]; rw [xor_cancel_right]

中文:
引理 xor_xor_cancel_comm
  条件: (a b : α)
  结论: a ^^^ b ^^^ a = b
  证明: by
  rw [xor_comm a]; rw [xor_cancel_right]
-/
@[simp] lemma xor_xor_cancel_comm (a b : α) : a ^^^ b ^^^ a = b := by
  rw [xor_comm a]; rw [xor_cancel_right]

/--
lemma `xor_xor_cancel_comm_assoc` / 引理 `xor_xor_cancel_comm_assoc`

English:
lemma xor_xor_cancel_comm_assoc
  given: (a b : α)
  statement: a ^^^ (b ^^^ a) = b
  proof: by
  rw [xor_comm a]; rw [xor_cancel_right]

中文:
引理 xor_xor_cancel_comm_assoc
  条件: (a b : α)
  结论: a ^^^ (b ^^^ a) = b
  证明: by
  rw [xor_comm a]; rw [xor_cancel_right]
-/
@[simp] lemma xor_xor_cancel_comm_assoc (a b : α) : a ^^^ (b ^^^ a) = b := by
  rw [xor_comm a]; rw [xor_cancel_right]

/--
lemma `xor_left_eq_self_iff` / 引理 `xor_left_eq_self_iff`

English:
lemma xor_left_eq_self_iff
  given: {a b : α}
  statement: a ^^^ b = a ↔ b = 0
  proof: by
   rw [xor_eq_iff_right_eq]; rw [xor_self a]

中文:
引理 xor_left_eq_self_iff
  条件: {a b : α}
  结论: a ^^^ b = a ↔ b = 0
  证明: by
   rw [xor_eq_iff_right_eq]; rw [xor_self a]
-/
@[simp] lemma xor_left_eq_self_iff {a b : α} : a ^^^ b = a ↔ b = 0 := by
   rw [xor_eq_iff_right_eq]; rw [xor_self a]
/--
lemma `xor_right_eq_self_iff` / 引理 `xor_right_eq_self_iff`

English:
lemma xor_right_eq_self_iff
  given: {a b : α}
  statement: b ^^^ a = a ↔ b = 0
  proof: by
   rw [xor_eq_iff_left_eq]; rw [xor_self a]

中文:
引理 xor_right_eq_self_iff
  条件: {a b : α}
  结论: b ^^^ a = a ↔ b = 0
  证明: by
   rw [xor_eq_iff_left_eq]; rw [xor_self a]
-/
@[simp] lemma xor_right_eq_self_iff {a b : α} : b ^^^ a = a ↔ b = 0 := by
   rw [xor_eq_iff_left_eq]; rw [xor_self a]

/--
lemma `xor_left_eq_id_iff` / 引理 `xor_left_eq_id_iff`

English:
lemma xor_left_eq_id_iff
  given: {a : α}
  statement: (a ^^^ ·) = id ↔ a = 0
  proof: ⟨((xor_zero a).symm.trans <| congrFun · 0), (· ▸ funext zero_xor)⟩

中文:
引理 xor_left_eq_id_iff
  条件: {a : α}
  结论: (a ^^^ ·) = id ↔ a = 0
  证明: ⟨((xor_zero a).symm.trans <| congrFun · 0), (· ▸ funext zero_xor)⟩
-/
@[simp] lemma xor_left_eq_id_iff {a : α} : (a ^^^ ·) = id ↔ a = 0 :=
  ⟨((xor_zero a).symm.trans <| congrFun · 0), (· ▸ funext zero_xor)⟩
/--
lemma `xor_right_eq_id_iff` / 引理 `xor_right_eq_id_iff`

English:
lemma xor_right_eq_id_iff
  given: {a : α}
  statement: (· ^^^ a) = id ↔ a = 0
  proof: by
  rw [xor_right_eq]; rw [xor_left_eq_id_iff]

中文:
引理 xor_right_eq_id_iff
  条件: {a : α}
  结论: (· ^^^ a) = id ↔ a = 0
  证明: by
  rw [xor_right_eq]; rw [xor_left_eq_id_iff]
-/
@[simp] lemma xor_right_eq_id_iff {a : α} : (· ^^^ a) = id ↔ a = 0 := by
  rw [xor_right_eq]; rw [xor_left_eq_id_iff]

/--
lemma `isFixedPt_xor_left_iff` / 引理 `isFixedPt_xor_left_iff`

English:
lemma isFixedPt_xor_left_iff
  given: {a b : α}
  statement: Function.IsFixedPt (a ^^^ ·) b ↔ a = 0
  proof: xor_right_eq_self_iff

中文:
引理 isFixedPt_xor_left_iff
  条件: {a b : α}
  结论: Function.IsFixedPt (a ^^^ ·) b ↔ a = 0
  证明: xor_right_eq_self_iff
-/
@[simp] lemma isFixedPt_xor_left_iff {a b : α} : Function.IsFixedPt (a ^^^ ·) b ↔ a = 0 :=
  xor_right_eq_self_iff
/--
lemma `isFixedPt_xor_right_iff` / 引理 `isFixedPt_xor_right_iff`

English:
lemma isFixedPt_xor_right_iff
  given: {a b : α}
  statement: Function.IsFixedPt (· ^^^ a) b ↔ a = 0
  proof: by
  rw [xor_right_eq]; rw [isFixedPt_xor_left_iff]

中文:
引理 isFixedPt_xor_right_iff
  条件: {a b : α}
  结论: Function.IsFixedPt (· ^^^ a) b ↔ a = 0
  证明: by
  rw [xor_right_eq]; rw [isFixedPt_xor_left_iff]
-/
@[simp] lemma isFixedPt_xor_right_iff {a b : α} : Function.IsFixedPt (· ^^^ a) b ↔ a = 0 := by
  rw [xor_right_eq]; rw [isFixedPt_xor_left_iff]
