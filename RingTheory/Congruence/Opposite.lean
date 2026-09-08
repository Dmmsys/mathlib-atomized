/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Congruence.Basic
public import Mathlib.GroupTheory.Congruence.Opposite

/-!
# Congruences on the opposite ring

This file defines the order isomorphism between the congruences on a ring `R` and the congruences on
the opposite ring `Rᵐᵒᵖ`.

-/

@[expose] public section

variable {R : Type*} [Add R] [Mul R]

namespace RingCon

/--
If `c` is a `RingCon R`, then `(a, b) ↦ c b.unop a.unop` is a `RingCon Rᵐᵒᵖ`.
-/
/-
**RingCon.op** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：op (c : RingCon R) : RingCon Rᵐᵒᵖ where __
参数：c : RingCon R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a `RingCon R`, then `(a, b) ↦ c b.unop a.unop` is a `RingCon Rᵐᵒᵖ`.
-/
def op (c : RingCon R) : RingCon Rᵐᵒᵖ where
  __ := c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2
/-
**RingCon.op_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingCon`。
形式化陈述：op_iff {c : RingCon R} {x y : Rᵐᵒᵖ} : c.op x y ↔ c y.unop x.unop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma op_iff {c : RingCon R} {x y : Rᵐᵒᵖ} : c.op x y ↔ c y.unop x.unop := Iff.rfl

/--
If `c` is a `RingCon Rᵐᵒᵖ`, then `(a, b) ↦ c b.op a.op` is a `RingCon R`.
-/
/-
**RingCon.unop** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：unop (c : RingCon Rᵐᵒᵖ) : RingCon R where __
参数：c : RingCon Rᵐᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c` is a `RingCon Rᵐᵒᵖ`, then `(a, b) ↦ c b.op a.op` is a `RingCon R`.
-/
def unop (c : RingCon Rᵐᵒᵖ) : RingCon R where
  __ := c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2
/-
**RingCon.unop_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingCon`。
形式化陈述：unop_iff {c : RingCon Rᵐᵒᵖ} {x y : R} : c.unop x y ↔ c (.op y) (.op x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma unop_iff {c : RingCon Rᵐᵒᵖ} {x y : R} : c.unop x y ↔ c (.op y) (.op x) := Iff.rfl

/--
The congruences of a ring `R` biject to the congruences of the opposite ring `Rᵐᵒᵖ`.
-/
@[simps]
/-
**RingCon.opOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：opOrderIso : RingCon R ≃o RingCon Rᵐᵒᵖ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruences of a ring `R` biject to the congruences of the opposite ring `Rᵐ
ᵒᵖ`.
-/
def opOrderIso : RingCon R ≃o RingCon Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

end RingCon

