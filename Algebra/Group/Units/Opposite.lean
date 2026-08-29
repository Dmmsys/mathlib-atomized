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
/--
Definition of `Units.opEquiv` / `Units.opEquiv` 的定义

English:
definition Units.opEquiv
  signature: {M} [Monoid M]
  body: op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective u.4, unop_injective u.3⟩
map_mul' _ _ := unop_injective Units.ext rfl

@[to_additive (attr := simp)]

中文:
定义 Units.opEquiv
  签名: {M} [Monoid M]
  定义体: op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective u.4, unop_injective u.3⟩
map_mul' _ _ := unop_injective Units.ext rfl

@[to_additive (attr := simp)]

Depends on / 依赖: op_injective
-/
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective u.4, unop_injective u.3⟩
map_mul' _ _ := unop_injective Units.ext rfl

@[to_additive (attr := simp)]
/--
theorem `Units.coe_unop_opEquiv` / 定理 `Units.coe_unop_opEquiv`

English:
theorem Units.coe_unop_opEquiv
  given: {M} [Monoid M] (u : Mᵐᵒᵖˣ)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 Units.coe_unop_opEquiv
  条件: {M} [Monoid M] (u : Mᵐᵒᵖˣ)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `Units.coe_opEquiv_symm` / 定理 `Units.coe_opEquiv_symm`

English:
theorem Units.coe_opEquiv_symm
  given: {M} [Monoid M] (u : Mˣᵐᵒᵖ)
  proof: rfl

@[to_additive]
nonrec theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩

@[to_additive]
nonrec theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (U

中文:
定理 Units.coe_opEquiv_symm
  条件: {M} [Monoid M] (u : Mˣᵐᵒᵖ)
  证明: rfl

@[to_additive]
nonrec theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩

@[to_additive]
nonrec theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (U
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
/--
theorem `isUnit_op` / 定理 `isUnit_op`

English:
theorem isUnit_op
  given: {M} [Monoid M] {m : M}
  statement: IsUnit (op m) ↔ IsUnit m
  proof: ⟨IsUnit.unop, IsUnit.op⟩

@[to_additive (attr := simp)]

中文:
定理 isUnit_op
  条件: {M} [Monoid M] {m : M}
  结论: IsUnit (op m) ↔ IsUnit m
  证明: ⟨IsUnit.unop, IsUnit.op⟩

@[to_additive (attr := simp)]

Depends on / 依赖: IsUnit, IsUnit.op, IsUnit.unop
-/
theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m :=
  ⟨IsUnit.unop, IsUnit.op⟩

@[to_additive (attr := simp)]
/--
theorem `isUnit_unop` / 定理 `isUnit_unop`

English:
theorem isUnit_unop
  given: {M} [Monoid M] {m : Mᵐᵒᵖ}
  statement: IsUnit (unop m) ↔ IsUnit m
  proof: ⟨IsUnit.op, IsUnit.unop⟩

中文:
定理 isUnit_unop
  条件: {M} [Monoid M] {m : Mᵐᵒᵖ}
  结论: IsUnit (unop m) ↔ IsUnit m
  证明: ⟨IsUnit.op, IsUnit.unop⟩

Depends on / 依赖: IsUnit, IsUnit.op, IsUnit.unop
-/
theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m :=
  ⟨IsUnit.op, IsUnit.unop⟩
