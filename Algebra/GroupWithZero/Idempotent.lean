/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Idempotent elements of a group with zero
-/

public section

assert_not_exists Ring

variable {M₀ : Type*}

namespace IsIdempotentElem
section MulZeroClass
variable [MulZeroClass M₀]

/-
**IsIdempotentElem.zero** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：zero : IsIdempotentElem (0 : M₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma zero : IsIdempotentElem (0 : M₀) := mul_zero _
/-
**IsIdempotentElem.** 是 Mathlib 中的一个实例，位于命名空间 `IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩
/-
**IsIdempotentElem.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {M₀ : Type u_1} [inst : MulZeroClass M₀], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) := rfl

end MulZeroClass

section CancelMonoidWithZero
variable {G₀ : Type*} [MonoidWithZero G₀] [IsLeftCancelMulZero G₀]

@[simp]
/-
**IsIdempotentElem.iff_eq_zero_or_one** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentEle
m`。
形式化陈述：iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 where mp 
h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `IsIdempotentElem.zero`：zero : IsIdempotentElem (0 : M₀)
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
-/
lemma iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 where
  mp h := or_iff_not_imp_left.mpr fun hp ↦ mul_left_cancel₀ hp (h.trans (mul_one p).symm)
  mpr h := h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one

end CancelMonoidWithZero
end IsIdempotentElem

