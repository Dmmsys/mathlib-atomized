/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Inverse and multiplication as order isomorphisms in ordered groups

-/

@[expose] public section

open Function

universe u

variable {α : Type u}

section Group

variable [Group α]

section TypeclassesLeftRightLE

variable [LE α] [MulLeftMono α] [MulRightMono α] {a b : α}

section

variable (α)

/-- `x ↦ x⁻¹` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ -x` as an order-reversing equivalence. -/]
/--
Definition of `OrderIso.inv` / `OrderIso.inv` 的定义

English:
definition OrderIso.inv
  signature: : α ≃o αᵒᵈ where
  body: (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := inv_le_inv_iff (α := α)

中文:
定义 OrderIso.inv
  签名: : α ≃o αᵒᵈ where
  定义体: (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := inv_le_inv_iff (α := α)

Depends on / 依赖: Equiv.inv, OrderDual, OrderDual.toDual, toDual
-/
def OrderIso.inv : α ≃o αᵒᵈ where
  toEquiv := (Equiv.inv α).trans OrderDual.toDual
  map_rel_iff' {_ _} := inv_le_inv_iff (α := α)

end

@[to_additive neg_le]
/--
theorem `inv_le'` / 定理 `inv_le'`

English:
theorem inv_le'
  statement: a⁻¹ <= b ↔ b⁻¹ <= a
  proof: (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

中文:
定理 inv_le'
  结论: a⁻¹ <= b ↔ b⁻¹ <= a
  证明: (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

Depends on / 依赖: OrderIso, OrderIso.inv, symm_apply_le
-/
theorem inv_le' : a⁻¹ <= b ↔ b⁻¹ <= a :=
  (OrderIso.inv α).symm_apply_le

alias ⟨inv_le_of_inv_le', _⟩ := inv_le'

attribute [to_additive neg_le_of_neg_le] inv_le_of_inv_le'

@[to_additive le_neg]
/--
theorem `le_inv'` / 定理 `le_inv'`

English:
theorem le_inv'
  statement: a <= b⁻¹ ↔ b <= a⁻¹
  proof: (OrderIso.inv α).le_symm_apply

中文:
定理 le_inv'
  结论: a <= b⁻¹ ↔ b <= a⁻¹
  证明: (OrderIso.inv α).le_symm_apply

Depends on / 依赖: OrderIso, OrderIso.inv, le_symm_apply
-/
theorem le_inv' : a <= b⁻¹ ↔ b <= a⁻¹ :=
  (OrderIso.inv α).le_symm_apply

/-- `x ↦ a / x` as an order-reversing equivalence. -/
@[to_additive (attr := simps!) /-- `x ↦ a - x` as an order-reversing equivalence. -/]
/--
Definition of `OrderIso.divLeft` / `OrderIso.divLeft` 的定义

English:
definition OrderIso.divLeft
  signature: (a : α)
  body: (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := div_le_div_iff_left (α := α) _

中文:
定义 OrderIso.divLeft
  签名: (a : α)
  定义体: (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := div_le_div_iff_left (α := α) _

Depends on / 依赖: Equiv.divLeft, OrderDual, OrderDual.toDual, divLeft, toDual
-/
def OrderIso.divLeft (a : α) : α ≃o αᵒᵈ where
  toEquiv := (Equiv.divLeft a).trans OrderDual.toDual
  map_rel_iff' {_ _} := div_le_div_iff_left (α := α) _

end TypeclassesLeftRightLE

end Group

alias ⟨le_inv_of_le_inv, _⟩ := le_inv'

attribute [to_additive] le_inv_of_le_inv

section Group

variable [Group α] [LE α]

section Right

variable [MulRightMono α] {a : α}

/-- `Equiv.mulRight` as an `OrderIso`. See also `OrderEmbedding.mulRight`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addRight` as an `OrderIso`. See also `OrderEmbedding.addRight`. -/]
/--
Definition of `OrderIso.mulRight` / `OrderIso.mulRight` 的定义

English:
definition OrderIso.mulRight
  signature: (a : α)
  body: mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a

@[to_additive (attr := simp)]

中文:
定义 OrderIso.mulRight
  签名: (a : α)
  定义体: mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a

@[to_additive (attr := simp)]

Depends on / 依赖: mul_le_mul_iff_right
-/
def OrderIso.mulRight (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_right a
  toEquiv := Equiv.mulRight a

@[to_additive (attr := simp)]
/--
theorem `OrderIso.mulRight_symm` / 定理 `OrderIso.mulRight_symm`

English:
theorem OrderIso.mulRight_symm
  given: (a : α)
  statement: (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹
  proof: by
  ext x
  rfl

中文:
定理 OrderIso.mulRight_symm
  条件: (a : α)
  结论: (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹
  证明: by
  ext x
  rfl
-/
theorem OrderIso.mulRight_symm (a : α) : (OrderIso.mulRight a).symm = OrderIso.mulRight a⁻¹ := by
  ext x
  rfl

/-- `x ↦ x / a` as an order isomorphism. -/
@[to_additive (attr := simps!) /-- `x ↦ x - a` as an order isomorphism. -/]
/--
Definition of `OrderIso.divRight` / `OrderIso.divRight` 的定义

English:
definition OrderIso.divRight
  signature: (a : α)
  body: Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

中文:
定义 OrderIso.divRight
  签名: (a : α)
  定义体: Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

Depends on / 依赖: Equiv.divRight, divRight
-/
def OrderIso.divRight (a : α) : α ≃o α where
  toEquiv := Equiv.divRight a
  map_rel_iff' {_ _} := div_le_div_iff_right a

end Right

section Left

variable [MulLeftMono α]

/-- `Equiv.mulLeft` as an `OrderIso`. See also `OrderEmbedding.mulLeft`. -/
@[to_additive (attr := simps! +simpRhs toEquiv apply)
  /-- `Equiv.addLeft` as an `OrderIso`. See also `OrderEmbedding.addLeft`. -/]
/--
Definition of `OrderIso.mulLeft` / `OrderIso.mulLeft` 的定义

English:
definition OrderIso.mulLeft
  signature: (a : α)
  body: mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a

@[to_additive (attr := simp)]

中文:
定义 OrderIso.mulLeft
  签名: (a : α)
  定义体: mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a

@[to_additive (attr := simp)]

Depends on / 依赖: mul_le_mul_iff_left
-/
def OrderIso.mulLeft (a : α) : α ≃o α where
  map_rel_iff' {_ _} := mul_le_mul_iff_left a
  toEquiv := Equiv.mulLeft a

@[to_additive (attr := simp)]
/--
theorem `OrderIso.mulLeft_symm` / 定理 `OrderIso.mulLeft_symm`

English:
theorem OrderIso.mulLeft_symm
  given: (a : α)
  statement: (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹
  proof: by
  ext x
  rfl

中文:
定理 OrderIso.mulLeft_symm
  条件: (a : α)
  结论: (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹
  证明: by
  ext x
  rfl
-/
theorem OrderIso.mulLeft_symm (a : α) : (OrderIso.mulLeft a).symm = OrderIso.mulLeft a⁻¹ := by
  ext x
  rfl

end Left

end Group
