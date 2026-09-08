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

/-- `XorOp.xor` as a permutation. -/
/-
**Equiv.xor** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → [inst : XorOp α] → [inst_1 : Zero α] → [LawfulXor α] → α 
→ Equiv.Perm α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `xor_cancel_left`：xor_cancel_left (a b : α) : a ^^^ (a ^^^ b) = b

--- 原说明 ---
`XorOp.xor` as a permutation.
-/
@[simps! apply] protected def xor (a : α) : Perm α where
  toFun := (a ^^^ ·)
  invFun := (a ^^^ ·)
  left_inv := xor_cancel_left a
  right_inv := xor_cancel_left a
/-
**Equiv.xor_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [inst_2 : LawfulXor α]
 {a : α},   Equiv.symm (Equiv.xor a) = Equiv.xor a
参数：Equiv.xor a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem xor_symm : (Equiv.xor a).symm = Equiv.xor a := rfl
/-
**Equiv.xor_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：xor_involutive (a : α) : Function.Involutive (Equiv.xor a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `xor_right_involutive`：xor_right_involutive (a : α) : Function.Involutive
 (a ^^^ ·)
-/
theorem xor_involutive (a : α) : Function.Involutive (Equiv.xor a) := xor_right_involutive a
/-
**Equiv.xor_zero** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [inst_2 : LawfulXor α]
, Equiv.xor 0 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `zero_xor`：zero_xor (a : α) : 0 ^^^ a = a
-/
@[simp] theorem xor_zero : Equiv.xor (0 : α) = 1 := Equiv.ext zero_xor
/-
**Equiv.xor_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [inst_2 : LawfulXor α]
 {a : α}, Equiv.xor a = 1 ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.coe_inj`：∀ {α : Sort u} {β : Sort v} {e₁ e₂ : α ≃ β}, ⇑e₁ = ⇑e₂ ↔ 
e₁ = e₂
· 使用定理 `xor_left_eq_id_iff`：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] 
[LawfulXor α] {a : α}, (fun x => a ^^^ x) = id ↔ a = 0
-/
@[simp] theorem xor_eq_one_iff : Equiv.xor a = 1 ↔ a = 0 :=
  Equiv.coe_inj.symm.trans xor_left_eq_id_iff
/-
**Equiv.isFixedPt_xor** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：isFixedPt_xor : Function.IsFixedPt (Equiv.xor a) b ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isFixedPt_xor_left_iff`：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero
 α] [LawfulXor α] {a b : α},   Function.IsFixedPt (fun x => a ^^^ x) b ↔ a = 0
-/
theorem isFixedPt_xor : Function.IsFixedPt (Equiv.xor a) b ↔ a = 0 := isFixedPt_xor_left_iff
/-
**Equiv.xor_trans_xor** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {α : Type u_1} [inst : XorOp α] [inst_1 : Zero α] [inst_2 : LawfulXor α]
 {a b : α},   Equiv.trans (Equiv.xor b) (Equiv.xor a) = Equiv.xor (a ^^^ b)
参数：Equiv.xor b；Equiv.xor a；a ^^^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulXor.xor_assoc`：∀ {α : Type u_1} {inst : XorOp α} {inst_1 : Zero α}
 [self : LawfulXor α] (a b c : α), a ^^^ b ^^^ c = a ^^^ (b ^^^ c)
-/
@[simp] theorem xor_trans_xor : (Equiv.xor b).trans (Equiv.xor a) = Equiv.xor (a ^^^ b) :=
  Equiv.ext <| (.symm <| xor_assoc a b ·)

end Equiv

