/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Units in multiplicative and additive opposites
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {α : Type*}

open MulOpposite

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      /-- The additive units of the additive opposites are equivalent to the additive opposites
      of the additive units. -/]
/-
**Units.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where toFun u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' _ _ := unop_injective <| Units.ext <| rfl

@[to_additive (attr := simp)]
/-
**Units.coe_unop_opEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) : ((Units.opEquiv u).uno
p : M) = unop (u : Mᵐᵒᵖ)
参数：u : Mᵐᵒᵖˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl

@[to_additive (attr := simp)]
/-
**Units.coe_opEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) : (Units.opEquiv.symm u 
: Mᵐᵒᵖ) = op (u.unop : M)
参数：u : Mˣᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) :
    (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl

@[to_additive]
nonrec theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩

@[to_additive]
nonrec theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (Units.opEquiv u), rfl⟩

@[to_additive (attr := simp)]
/-
**isUnit_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.unop`：∀ {M : Type u_2} [inst : Monoid M] {m : Mᵐᵒᵖ}, IsUnit m → I
sUnit (MulOpposite.unop m)
· 使用定理 `IsUnit.op`：∀ {M : Type u_2} [inst : Monoid M] {m : M}, IsUnit m → IsUnit
 (MulOpposite.op m)
-/
theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m :=
  ⟨IsUnit.unop, IsUnit.op⟩

@[to_additive (attr := simp)]
/-
**isUnit_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.op`：∀ {M : Type u_2} [inst : Monoid M] {m : M}, IsUnit m → IsUnit
 (MulOpposite.op m)
· 使用定理 `IsUnit.unop`：∀ {M : Type u_2} [inst : Monoid M] {m : Mᵐᵒᵖ}, IsUnit m → I
sUnit (MulOpposite.unop m)
-/
theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m :=
  ⟨IsUnit.op, IsUnit.unop⟩
