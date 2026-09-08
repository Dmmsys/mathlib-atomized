/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Congruence modulo multiples and congruence modulo `AddSubgroup.zmultiples _`

In this file we show that in an additive commutative group, the congruence relation `a ≡ b [PMOD p]`
is equivalent to the coercions of `a` and `b` to `G ⧸ AddSubgroup.zmultiples p` being equal.
-/

public section

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {a b p : G}

/-
**AddCommGroup.modEq_iff_eq_mod_zmultiples** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGro
up`。
形式化陈述：modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmulti
ples p) = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCommGroup.modEq_comm`：modEq_comm : a ≡ b [PMOD p] ↔ b ≡ a [PMOD p]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem modEq_iff_eq_mod_zmultiples : a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b := by
  rw [modEq_comm]
  simp_rw [modEq_iff_eq_add_zsmul, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff,
    eq_sub_iff_add_eq', eq_comm]
/-
**AddCommGroup.not_modEq_iff_ne_mod_zmultiples** 是 Mathlib 中的一个定理，位于命名空间 `AddCom
mGroup`。
形式化陈述：not_modEq_iff_ne_mod_zmultiples : ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.z
multiples p) != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AddCommGroup.modEq_iff_eq_mod_zmultiples`：modEq_iff_eq_mod_zmultiples : 
a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) = b
-/
theorem not_modEq_iff_ne_mod_zmultiples :
    ¬a ≡ b [PMOD p] ↔ (a : G ⧸ AddSubgroup.zmultiples p) ≠ b :=
  modEq_iff_eq_mod_zmultiples.not

end AddCommGroup

