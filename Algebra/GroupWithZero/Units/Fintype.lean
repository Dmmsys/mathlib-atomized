/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Fintype instances relating to units
-/

public section

assert_not_exists Field

variable {α : Type*}

/--
Instance `UnitsInt.fintype` / 实例 `UnitsInt.fintype`

English:
instance UnitsInt.fintype
  signature: : Fintype Intˣ
  body: ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]

中文:
实例 UnitsInt.fintype
  签名: : Fintype 整数ˣ
  定义体: ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
instance UnitsInt.fintype : Fintype Intˣ :=
  ⟨{1, -1}, fun x => by cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]
/--
theorem `UnitsInt.univ` / 定理 `UnitsInt.univ`

English:
theorem UnitsInt.univ
  statement: (Finset.univ : Finset Intˣ) = {1, -1}
  proof: rfl

@[simp]

中文:
定理 UnitsInt.univ
  结论: (Finset.univ : Finset 整数ˣ) = {1, -1}
  证明: rfl

@[simp]
-/
theorem UnitsInt.univ : (Finset.univ : Finset Intˣ) = {1, -1} := rfl

@[simp]
/--
theorem `Fintype.card_units_int` / 定理 `Fintype.card_units_int`

English:
theorem Fintype.card_units_int
  statement: Fintype.card Intˣ = 2
  proof: rfl

中文:
定理 Fintype.card_units_int
  结论: Fintype.card 整数ˣ = 2
  证明: rfl
-/
theorem Fintype.card_units_int : Fintype.card Intˣ = 2 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [Fintype α] [DecidableEq α] : Fintype αˣ
  body: Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

中文:
实例 [Monoid
  签名: α] [Fintype α] [DecidableEq α] : Fintype αˣ
  定义体: Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, ofEquiv, unitsEquivProdSubtype
-/
instance [Monoid α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] [Finite α] : Finite αˣ
  body: .of_injective _ Units.val_injective

中文:
实例 [Monoid
  签名: α] [Finite α] : Finite αˣ
  定义体: .of_injective _ Units.val_injective

Depends on / 依赖: Units.val_injective, of_injective, val_injective
-/
instance [Monoid α] [Finite α] : Finite αˣ := .of_injective _ Units.val_injective

variable (α)

/--
theorem `Nat.card_units` / 定理 `Nat.card_units`

English:
theorem Nat.card_units
  given: [GroupWithZero α]
  proof: by
  classical
  rw [Nat.card_congr unitsEquivNeZero]; rw [eq_comm]; rw [← Nat.card_congr (Equiv.sumCompl (· = (0 : α)))]
  rcases finite_or_infinite {a : α // a != 0}
  · rw [Nat.card_sum, Nat.card_unique, add_tsub_cancel_left]
  · rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zer

中文:
定理 Nat.card_units
  条件: [GroupWithZero α]
  证明: by
  classical
  rw [Nat.card_congr unitsEquivNeZero]; rw [eq_comm]; rw [← Nat.card_congr (Equiv.sumCompl (· = (0 : α)))]
  rcases finite_or_infinite {a : α // a != 0}
  · rw [Nat.card_sum, Nat.card_unique, add_tsub_cancel_left]
  · rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zer

Depends on / 依赖: Equiv.sumCompl, Nat.card_congr, Nat.card_eq_zero_of_infinite, Nat.card_sum, Nat.card_unique, add_tsub_cancel_left, card_congr, card_eq_zero_of_infinite, card_sum, card_unique, classical, eq_comm, finite_or_infinite, sumCompl, unitsEquivNeZero, zero_tsub
-/
theorem Nat.card_units [GroupWithZero α] :
    Nat.card αˣ = Nat.card α - 1 := by
  classical
  rw [Nat.card_congr unitsEquivNeZero]; rw [eq_comm]; rw [← Nat.card_congr (Equiv.sumCompl (· = (0 : α)))]
  rcases finite_or_infinite {a : α // a != 0}
  · rw [Nat.card_sum, Nat.card_unique, add_tsub_cancel_left]
  · rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_tsub]

/--
theorem `Nat.card_eq_card_units_add_one` / 定理 `Nat.card_eq_card_units_add_one`

English:
theorem Nat.card_eq_card_units_add_one
  given: [GroupWithZero α] [Finite α]
  proof: by
  rw [Nat.card_units]; rw [tsub_add_cancel_of_le Nat.card_pos]

中文:
定理 Nat.card_eq_card_units_add_one
  条件: [GroupWithZero α] [Finite α]
  证明: by
  rw [Nat.card_units]; rw [tsub_add_cancel_of_le Nat.card_pos]

Depends on / 依赖: Nat.card_pos, Nat.card_units, card_pos, card_units, tsub_add_cancel_of_le
-/
theorem Nat.card_eq_card_units_add_one [GroupWithZero α] [Finite α] :
    Nat.card α = Nat.card αˣ + 1 := by
  rw [Nat.card_units]; rw [tsub_add_cancel_of_le Nat.card_pos]

/--
theorem `Fintype.card_units` / 定理 `Fintype.card_units`

English:
theorem Fintype.card_units
  given: [GroupWithZero α] [Fintype α] [DecidableEq α]
  proof: by
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_units]; rw [Nat.card_eq_fintype_card]

中文:
定理 Fintype.card_units
  条件: [GroupWithZero α] [Fintype α] [DecidableEq α]
  证明: by
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_units]; rw [Nat.card_eq_fintype_card]

Depends on / 依赖: Nat.card_eq_fintype_card, Nat.card_units, card_eq_fintype_card, card_units
-/
theorem Fintype.card_units [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card αˣ = Fintype.card α - 1 := by
  rw [← Nat.card_eq_fintype_card]; rw [Nat.card_units]; rw [Nat.card_eq_fintype_card]

/--
theorem `Fintype.card_eq_card_units_add_one` / 定理 `Fintype.card_eq_card_units_add_one`

English:
theorem Fintype.card_eq_card_units_add_one
  given: [GroupWithZero α] [Fintype α] [DecidableEq α]
  proof: by
  rw [Fintype.card_units]; rw [tsub_add_cancel_of_le Fintype.card_pos]

中文:
定理 Fintype.card_eq_card_units_add_one
  条件: [GroupWithZero α] [Fintype α] [DecidableEq α]
  证明: by
  rw [Fintype.card_units]; rw [tsub_add_cancel_of_le Fintype.card_pos]

Depends on / 依赖: Fintype, Fintype.card_pos, Fintype.card_units, card_pos, card_units, tsub_add_cancel_of_le
-/
theorem Fintype.card_eq_card_units_add_one [GroupWithZero α] [Fintype α] [DecidableEq α] :
    Fintype.card α = Fintype.card αˣ + 1 := by
  rw [Fintype.card_units]; rw [tsub_add_cancel_of_le Fintype.card_pos]
