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

/-- A typeclass indicating that the xor operation, `^^^`, is lawful. -/
/-
**LawfulXor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [XorOp α] → [Zero α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass indicating that the xor operation, `^^^`, is lawful.
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
/-
**zero_xor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_xor (a : α) : 0 ^^^ a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulXor.xor_comm`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a b : α), a ^^^ b = b ^^^ a
· 使用定理 `LawfulXor.xor_zero`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ 0 = a
-/
theorem zero_xor (a : α) : 0 ^^^ a = a := by rw [LawfulXor.xor_comm, xor_zero]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Commutative (α := α) XorOp.xor where comm := xor_comm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Associative (α := α) XorOp.xor where assoc := xor_assoc
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.LawfulCommIdentity (α := α) XorOp.xor 0 where
  left_id := zero_xor
  right_id := xor_zero

@[simp]
/-
**xor_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulXor.xor_assoc`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α}
 [self : LawfulXor α] (a b c : α), a ^^^ b ^^^ c = a ^^^ (b ^^^ c)
· 使用定理 `LawfulXor.xor_self`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ a = 0
· 使用定理 `zero_xor`：zero_xor (a : α) : 0 ^^^ a = a
-/
theorem xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b := by
  rw [← xor_assoc, LawfulXor.xor_self, zero_xor]

@[simp]
/-
**xor_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulXor.xor_assoc`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α}
 [self : LawfulXor α] (a b c : α), a ^^^ b ^^^ c = a ^^^ (b ^^^ c)
· 使用定理 `LawfulXor.xor_self`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ a = 0
· 使用定理 `LawfulXor.xor_zero`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ 0 = a
-/
theorem xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a := by
  rw [xor_assoc, LawfulXor.xor_self, xor_zero]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor Nat where
  xor_assoc := Nat.xor_assoc
  xor_comm := Nat.xor_comm
  xor_self := Nat.xor_self
  xor_zero := Nat.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {w : ℕ} : LawfulXor (Fin (2 ^ w)) where
  xor_assoc := Fin.xor_assoc rfl
  xor_comm := Fin.xor_comm
  xor_self := Fin.xor_self
  xor_zero := Fin.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {w : Nat} : LawfulXor (BitVec w) where
  xor_assoc := BitVec.xor_assoc
  xor_comm := BitVec.xor_comm
  xor_self _ := BitVec.xor_self
  xor_zero _ := BitVec.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor UInt8 where
  xor_assoc := UInt8.xor_assoc
  xor_comm := UInt8.xor_comm
  xor_self _ := UInt8.xor_self
  xor_zero _ := UInt8.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor UInt16 where
  xor_assoc := UInt16.xor_assoc
  xor_comm := UInt16.xor_comm
  xor_self _ := UInt16.xor_self
  xor_zero _ := UInt16.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor UInt32 where
  xor_assoc := UInt32.xor_assoc
  xor_comm := UInt32.xor_comm
  xor_self _ := UInt32.xor_self
  xor_zero _ := UInt32.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor UInt64 where
  xor_assoc := UInt64.xor_assoc
  xor_comm := UInt64.xor_comm
  xor_self _ := UInt64.xor_self
  xor_zero _ := UInt64.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor USize where
  xor_assoc := USize.xor_assoc
  xor_comm := USize.xor_comm
  xor_self _ := USize.xor_self
  xor_zero _ := USize.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor Int8 where
  xor_assoc := Int8.xor_assoc
  xor_comm := Int8.xor_comm
  xor_self _ := Int8.xor_self
  xor_zero _ := Int8.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor Int16 where
  xor_assoc := Int16.xor_assoc
  xor_comm := Int16.xor_comm
  xor_self _ := Int16.xor_self
  xor_zero _ := Int16.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor Int32 where
  xor_assoc := Int32.xor_assoc
  xor_comm := Int32.xor_comm
  xor_self _ := Int32.xor_self
  xor_zero _ := Int32.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor Int64 where
  xor_assoc := Int64.xor_assoc
  xor_comm := Int64.xor_comm
  xor_self _ := Int64.xor_self
  xor_zero _ := Int64.xor_zero
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulXor ISize where
  xor_assoc := ISize.xor_assoc
  xor_comm := ISize.xor_comm
  xor_self _ := ISize.xor_self
  xor_zero _ := ISize.xor_zero
/-
**xor_right_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：xor_right_eq {a : α} : (· ^^^ a) = (a ^^^ ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulXor.xor_comm`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a b : α), a ^^^ b = b ^^^ a
-/
lemma xor_right_eq {a : α} : (· ^^^ a) = (a ^^^ ·) := funext (xor_comm · a)
/-
**xor_left_involutive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：xor_left_involutive (a : α) : Function.Involutive (· ^^^ a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `xor_cancel_right`：xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a
-/
lemma xor_left_involutive (a : α) : Function.Involutive (· ^^^ a) := (xor_cancel_right · a)
/-
**xor_right_involutive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：xor_right_involutive (a : α) : Function.Involutive (a ^^^ ·)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `xor_cancel_left`：xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b
-/
lemma xor_right_involutive (a : α) : Function.Involutive (a ^^^ ·) := xor_cancel_left a
/-
**xor_eq_iff_left_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：xor_eq_iff_left_eq (a b c : α) : .eq_iff a ^^^ b = c ↔ a = c ^^^ b
参数：a b c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用引理 `xor_left_involutive`：xor_left_involutive (a : α) : Function.Involutive (
· ^^^ a)
-/
lemma xor_eq_iff_left_eq (a b c : α) :
    a ^^^ b = c ↔ a = c ^^^ b := xor_left_involutive _ |>.eq_iff
/-
**xor_eq_iff_right_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：xor_eq_iff_right_eq (a b c : α) : .eq_iff a ^^^ b = c ↔ b = a ^^^ c
参数：a b c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用引理 `xor_right_involutive`：xor_right_involutive (a : α) : Function.Involutive
 (a ^^^ ·)
-/
lemma xor_eq_iff_right_eq (a b c : α) :
    a ^^^ b = c ↔ b = a ^^^ c := xor_right_involutive _ |>.eq_iff
/-
**xor_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a b : α
}, a ^^^ b = 0 ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `xor_eq_iff_left_eq`：xor_eq_iff_left_eq (a b c : α) : .eq_iff a ^^^ b = c
 ↔ a = c ^^^ b
· 使用定理 `zero_xor`：zero_xor (a : α) : 0 ^^^ a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma xor_eq_zero_iff {a b : α} : a ^^^ b = 0 ↔ a = b := by
  rw [ xor_eq_iff_left_eq, zero_xor]
/-
**xor_xor_cancel_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] (a b : α
), a ^^^ b ^^^ a = b
参数：a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulXor.xor_comm`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a b : α), a ^^^ b = b ^^^ a
· 使用定理 `xor_cancel_right`：xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a
-/
@[simp] lemma xor_xor_cancel_comm (a b : α) : a ^^^ b ^^^ a = b := by
  rw [xor_comm a, xor_cancel_right]
/-
**xor_xor_cancel_comm_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] (a b : α
), a ^^^ (b ^^^ a) = b
参数：a b : α；b ^^^ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulXor.xor_comm`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a b : α), a ^^^ b = b ^^^ a
· 使用定理 `xor_cancel_right`：xor_cancel_right (a b : α) : (a ^^^ b) ^^^ b = a
-/
@[simp] lemma xor_xor_cancel_comm_assoc (a b : α) : a ^^^ (b ^^^ a) = b := by
  rw [xor_comm a, xor_cancel_right]
/-
**xor_left_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a b : α
}, a ^^^ b = a ↔ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `xor_eq_iff_right_eq`：xor_eq_iff_right_eq (a b c : α) : .eq_iff a ^^^ b =
 c ↔ b = a ^^^ c
· 使用定理 `LawfulXor.xor_self`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma xor_left_eq_self_iff {a b : α} : a ^^^ b = a ↔ b = 0 := by
   rw [xor_eq_iff_right_eq, xor_self a]
/-
**xor_right_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a b : α
}, b ^^^ a = a ↔ b = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `xor_eq_iff_left_eq`：xor_eq_iff_left_eq (a b c : α) : .eq_iff a ^^^ b = c
 ↔ a = c ^^^ b
· 使用定理 `LawfulXor.xor_self`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma xor_right_eq_self_iff {a b : α} : b ^^^ a = a ↔ b = 0 := by
   rw [xor_eq_iff_left_eq, xor_self a]
/-
**xor_left_eq_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a : α},
 (fun x => a ^^^ x) = id ↔ a = 0
参数：fun x => a ^^^ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulXor.xor_zero`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α} 
[self : LawfulXor α] (a : α), a ^^^ 0 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_xor`：zero_xor (a : α) : 0 ^^^ a = a
-/
@[simp] lemma xor_left_eq_id_iff {a : α} : (a ^^^ ·) = id ↔ a = 0 :=
  ⟨((xor_zero a).symm.trans <| congrFun · 0), (· ▸ funext zero_xor)⟩
/-
**xor_right_eq_id_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a : α},
 (fun x => x ^^^ a) = id ↔ a = 0
参数：fun x => x ^^^ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `xor_right_eq`：xor_right_eq {a : α} : (· ^^^ a) = (a ^^^ ·)
· 使用定理 `xor_left_eq_id_iff`：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] 
[LawfulXor α] {a : α}, (fun x => a ^^^ x) = id ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma xor_right_eq_id_iff {a : α} : (· ^^^ a) = id ↔ a = 0 := by
  rw [xor_right_eq, xor_left_eq_id_iff]
/-
**isFixedPt_xor_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a b : α
},   Function.IsFixedPt (fun x => a ^^^ x) b ↔ a = 0
参数：fun x => a ^^^ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `xor_right_eq_self_iff`：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero 
α] [LawfulXor α] {a b : α}, b ^^^ a = a ↔ b = 0
-/
@[simp] lemma isFixedPt_xor_left_iff {a b : α} : Function.IsFixedPt (a ^^^ ·) b ↔ a = 0 :=
  xor_right_eq_self_iff
/-
**isFixedPt_xor_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [LawfulXor α] {a b : α
},   Function.IsFixedPt (fun x => x ^^^ a) b ↔ a = 0
参数：fun x => x ^^^ a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `xor_right_eq`：xor_right_eq {a : α} : (· ^^^ a) = (a ^^^ ·)
· 使用定理 `isFixedPt_xor_left_iff`：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero
 α] [LawfulXor α] {a b : α},   Function.IsFixedPt (fun x => a ^^^ x) b ↔ a = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isFixedPt_xor_right_iff {a b : α} : Function.IsFixedPt (· ^^^ a) b ↔ a = 0 := by
  rw [xor_right_eq, isFixedPt_xor_left_iff]
