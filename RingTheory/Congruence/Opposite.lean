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
Definition of `op` / `op` 的定义

English:
definition op
  signature: (c : RingCon R)
  body: c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2

中文:
定义 op
  签名: (c : RingCon R)
  定义体: c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2

Depends on / 依赖: c.toCon.op
-/
def op (c : RingCon R) : RingCon Rᵐᵒᵖ where
  __ := c.toCon.op
  mul' h1 h2 := c.toCon.op.mul h1 h2
  add' h1 h2 := c.add h1 h2

/--
lemma `op_iff` / 引理 `op_iff`

English:
lemma op_iff
  given: {c : RingCon R} {x y : Rᵐᵒᵖ}
  statement: c.op x y ↔ c y.unop x.unop
  proof: Iff.rfl

中文:
引理 op_iff
  条件: {c : RingCon R} {x y : Rᵐᵒᵖ}
  结论: c.op x y ↔ c y.unop x.unop
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma op_iff {c : RingCon R} {x y : Rᵐᵒᵖ} : c.op x y ↔ c y.unop x.unop := Iff.rfl

/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (c : RingCon Rᵐᵒᵖ)
  body: c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

中文:
定义 unop
  签名: (c : RingCon Rᵐᵒᵖ)
  定义体: c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

Depends on / 依赖: c.toCon.unop
-/
def unop (c : RingCon Rᵐᵒᵖ) : RingCon R where
  __ := c.toCon.unop
  mul' h1 h2 := c.toCon.unop.mul h1 h2
  add' h1 h2 := c.add h1 h2

/--
lemma `unop_iff` / 引理 `unop_iff`

English:
lemma unop_iff
  given: {c : RingCon Rᵐᵒᵖ} {x y : R}
  statement: c.unop x y ↔ c (.op y) (.op x)
  proof: Iff.rfl

中文:
引理 unop_iff
  条件: {c : RingCon Rᵐᵒᵖ} {x y : R}
  结论: c.unop x y ↔ c (.op y) (.op x)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma unop_iff {c : RingCon Rᵐᵒᵖ} {x y : R} : c.unop x y ↔ c (.op y) (.op x) := Iff.rfl

/--
The congruences of a ring `R` biject to the congruences of the opposite ring `Rᵐᵒᵖ`.
-/
@[simps]
/--
Definition of `opOrderIso` / `opOrderIso` 的定义

English:
definition opOrderIso
  signature: : RingCon R ≃o RingCon Rᵐᵒᵖ where
  body: op
  invFun := unop
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

中文:
定义 opOrderIso
  签名: : RingCon R ≃o RingCon Rᵐᵒᵖ where
  定义体: op
  invFun := unop
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'
-/
def opOrderIso : RingCon R ≃o RingCon Rᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_rel_iff' {c d} := by rw [le_def, le_def]; constructor <;> intro h _ _ h' <;> exact h h'

end RingCon
