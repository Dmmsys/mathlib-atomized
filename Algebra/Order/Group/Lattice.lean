/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942]. They form the algebraic
underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

A lattice ordered group is a type `α` satisfying:
* `Lattice α`
* `CommGroup α`
* `MulLeftMono α`
* `MulRightMono α`

This file establishes basic properties of lattice ordered groups. It is shown that when the group is
commutative, the lattice is distributive. This also holds in the non-commutative case
([Birkhoff][birkhoff1942],[Fuchs][fuchs1963]) but we do not yet have the machinery to establish this
in mathlib.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, order, group
-/

@[expose] public section

open Function

variable {α : Type*}

section Group
variable [Lattice α] [Group α]

-- Special case of Bourbaki A.VI.9 (1)
@[to_additive]
/--
lemma `mul_sup` / 引理 `mul_sup`

English:
lemma mul_sup
  given: [MulLeftMono α] (a b c : α)
  proof: (OrderIso.mulLeft _).map_sup _ _

@[to_additive]

中文:
引理 mul_sup
  条件: [MulLeftMono α] (a b c : α)
  证明: (OrderIso.mulLeft _).map_sup _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_sup, mulLeft
-/
lemma mul_sup [MulLeftMono α] (a b c : α) :
    c * (a ⊔ b) = c * a ⊔ c * b :=
  (OrderIso.mulLeft _).map_sup _ _

@[to_additive]
/--
lemma `sup_mul` / 引理 `sup_mul`

English:
lemma sup_mul
  given: [MulRightMono α] (a b c : α)
  proof: (OrderIso.mulRight _).map_sup _ _

@[to_additive]

中文:
引理 sup_mul
  条件: [MulRightMono α] (a b c : α)
  证明: (OrderIso.mulRight _).map_sup _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulRight, map_sup, mulRight
-/
lemma sup_mul [MulRightMono α] (a b c : α) :
    (a ⊔ b) * c = a * c ⊔ b * c :=
  (OrderIso.mulRight _).map_sup _ _

@[to_additive]
/--
lemma `mul_inf` / 引理 `mul_inf`

English:
lemma mul_inf
  given: [MulLeftMono α] (a b c : α)
  proof: (OrderIso.mulLeft _).map_inf _ _

@[to_additive]

中文:
引理 mul_inf
  条件: [MulLeftMono α] (a b c : α)
  证明: (OrderIso.mulLeft _).map_inf _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_inf, mulLeft
-/
lemma mul_inf [MulLeftMono α] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b :=
  (OrderIso.mulLeft _).map_inf _ _

@[to_additive]
/--
lemma `inf_mul` / 引理 `inf_mul`

English:
lemma inf_mul
  given: [MulRightMono α] (a b c : α)
  proof: (OrderIso.mulRight _).map_inf _ _

@[to_additive]

中文:
引理 inf_mul
  条件: [MulRightMono α] (a b c : α)
  证明: (OrderIso.mulRight _).map_inf _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.mulRight, map_inf, mulRight
-/
lemma inf_mul [MulRightMono α] (a b c : α) :
    (a ⊓ b) * c = a * c ⊓ b * c :=
  (OrderIso.mulRight _).map_inf _ _

@[to_additive]
/--
lemma `sup_div` / 引理 `sup_div`

English:
lemma sup_div
  given: [MulRightMono α] (a b c : α)
  proof: (OrderIso.divRight _).map_sup _ _

@[to_additive]

中文:
引理 sup_div
  条件: [MulRightMono α] (a b c : α)
  证明: (OrderIso.divRight _).map_sup _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.divRight, divRight, map_sup
-/
lemma sup_div [MulRightMono α] (a b c : α) :
    (a ⊔ b) / c = a / c ⊔ b / c :=
  (OrderIso.divRight _).map_sup _ _

@[to_additive]
/--
lemma `inf_div` / 引理 `inf_div`

English:
lemma inf_div
  given: [MulRightMono α] (a b c : α)
  proof: (OrderIso.divRight _).map_inf _ _

中文:
引理 inf_div
  条件: [MulRightMono α] (a b c : α)
  证明: (OrderIso.divRight _).map_inf _ _

Depends on / 依赖: OrderIso, OrderIso.divRight, divRight, map_inf
-/
lemma inf_div [MulRightMono α] (a b c : α) :
    (a ⊓ b) / c = a / c ⊓ b / c :=
  (OrderIso.divRight _).map_inf _ _

section
variable [MulLeftMono α] [MulRightMono α]

/--
lemma `inv_sup` / 引理 `inv_sup`

English:
lemma inv_sup
  given: (a b : α)
  statement: (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
  proof: (OrderIso.inv α).map_sup _ _

中文:
引理 inv_sup
  条件: (a b : α)
  结论: (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹
  证明: (OrderIso.inv α).map_sup _ _
-/
@[to_additive] lemma inv_sup (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := (OrderIso.inv α).map_sup _ _

/--
lemma `inv_inf` / 引理 `inv_inf`

English:
lemma inv_inf
  given: (a b : α)
  statement: (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
  proof: (OrderIso.inv α).map_inf _ _

@[to_additive]

中文:
引理 inv_inf
  条件: (a b : α)
  结论: (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹
  证明: (OrderIso.inv α).map_inf _ _

@[to_additive]
-/
@[to_additive] lemma inv_inf (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ := (OrderIso.inv α).map_inf _ _

@[to_additive]
/--
lemma `div_sup` / 引理 `div_sup`

English:
lemma div_sup
  given: (a b c : α)
  statement: c / (a ⊔ b) = c / a ⊓ c / b
  proof: (OrderIso.divLeft c).map_sup _ _

@[to_additive]

中文:
引理 div_sup
  条件: (a b c : α)
  结论: c / (a ⊔ b) = c / a ⊓ c / b
  证明: (OrderIso.divLeft c).map_sup _ _

@[to_additive]

Depends on / 依赖: OrderIso, OrderIso.divLeft, divLeft, map_sup
-/
lemma div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b := (OrderIso.divLeft c).map_sup _ _

@[to_additive]
/--
lemma `div_inf` / 引理 `div_inf`

English:
lemma div_inf
  given: (a b c : α)
  statement: c / (a ⊓ b) = c / a ⊔ c / b
  proof: (OrderIso.divLeft c).map_inf _ _

中文:
引理 div_inf
  条件: (a b c : α)
  结论: c / (a ⊓ b) = c / a ⊔ c / b
  证明: (OrderIso.divLeft c).map_inf _ _

Depends on / 依赖: OrderIso, OrderIso.divLeft, divLeft, map_inf
-/
lemma div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b := (OrderIso.divLeft c).map_inf _ _

-- In fact 0 ≤ n•a implies 0 ≤ a, see L. Fuchs, "Partially ordered algebraic systems"
-- Chapter V, 1.E
-- See also `one_le_pow_iff` for the existing version in linear orders
@[to_additive]
/--
lemma `pow_two_semiclosed` / 引理 `pow_two_semiclosed`

English:
lemma pow_two_semiclosed
  proof: by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_eq_left]
  rw [mul_inf]; rw [inf_mul]; rw [← pow_two]; rw [mul_one]; rw [one_mul]; rw [inf_assoc]; rw [inf_left_idem]; rw [inf_comm]; rw [inf_assoc]; rw [inf_of_le_left ha]

中文:
引理 pow_two_semiclosed
  证明: by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_eq_left]
  rw [mul_inf]; rw [inf_mul]; rw [← pow_two]; rw [mul_one]; rw [one_mul]; rw [inf_assoc]; rw [inf_left_idem]; rw [inf_comm]; rw [inf_assoc]; rw [inf_of_le_left ha]

Depends on / 依赖: inf_assoc, inf_comm, inf_eq_right, inf_left_idem, inf_mul, inf_of_le_left, mul_eq_left, mul_inf, mul_one, one_mul, pow_two
-/
lemma pow_two_semiclosed
    {a : α} (ha : 1 <= a ^ 2) : 1 <= a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_eq_left]
  rw [mul_inf]; rw [inf_mul]; rw [← pow_two]; rw [mul_one]; rw [one_mul]; rw [inf_assoc]; rw [inf_left_idem]; rw [inf_comm]; rw [inf_assoc]; rw [inf_of_le_left ha]

end

end Group

variable [Lattice α] [CommGroup α]

-- Fuchs p67
-- Bourbaki A.VI.10 Prop 7
@[to_additive]
/--
lemma `inf_mul_sup` / 引理 `inf_mul_sup`

English:
lemma inf_mul_sup
  given: [MulLeftMono α] (a b : α)
  statement: (a ⊓ b) * (a ⊔ b) = a * b
  proof: calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b)]; rw [mul_inv_cancel_right]; rw [mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]

中文:
引理 inf_mul_sup
  条件: [MulLeftMono α] (a b : α)
  结论: (a ⊓ b) * (a ⊔ b) = a * b
  证明: calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b)]; rw [mul_inv_cancel_right]; rw [mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]

Depends on / 依赖: inv_inf, inv_mul_cancel_right, mul_comm, mul_inv_cancel_comm, mul_inv_cancel_right, mul_sup, sup_comm
-/
lemma inf_mul_sup [MulLeftMono α] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b)]; rw [mul_inv_cancel_right]; rw [mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]

/-- Every lattice ordered commutative group is a distributive lattice. -/
-- Non-comm case needs cancellation law https://ncatlab.org/nlab/show/distributive+lattice
@[to_additive (attr := instance_reducible)
  /-- Every lattice ordered commutative additive group is a distributive lattice -/]
/--
Definition of `CommGroup.toDistribLattice` / `CommGroup.toDistribLattice` 的定义

English:
definition CommGroup.toDistribLattice
  signature: (α : Type*) [Lattice α] [CommGroup α]
  body: by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z))]; rw [inf_mul_sup x (y ⊓ z)]; rw [← inv_mul_le_iff_le_mul]; rw [le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mu

中文:
定义 交换群.toDistribLattice
  签名: (α : 类型) [格 α] [交换群 α]
  定义体: by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z))]; rw [inf_mul_sup x (y ⊓ z)]; rw [← inv_mul_le_iff_le_mul]; rw [le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mu

Depends on / 依赖: inf_le_inf_left, inf_le_left, inf_le_right, inf_mul_sup, inv_mul_le_iff_le_mul, le_inf_iff, mul_le_mul, mul_le_mul_iff_left
-/
def CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α]
    [MulLeftMono α] : DistribLattice α where
  le_sup_inf x y z := by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z))]; rw [inf_mul_sup x (y ⊓ z)]; rw [← inv_mul_le_iff_le_mul]; rw [le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_right) inf_le_right
