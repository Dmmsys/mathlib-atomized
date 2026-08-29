/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Logic.Unique

/-!
# The unit of the natural numbers
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat


/--
lemma `units_eq_one` / 引理 `units_eq_one`

English:
lemma units_eq_one
  given: (u : Natˣ)
  statement: u = 1
  proof: Units.ext Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

中文:
引理 units_eq_one
  条件: (u : 自然数ˣ)
  结论: u = 1
  证明: Units.ext Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

Depends on / 依赖: Nat.eq_one_of_dvd_one, Units.ext, eq_one_of_dvd_one, u.inv, u.val_inv.symm, val_inv
-/
lemma units_eq_one (u : Natˣ) : u = 1 := Units.ext Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩

/--
lemma `addUnits_eq_zero` / 引理 `addUnits_eq_zero`

English:
lemma addUnits_eq_zero
  given: (u : AddUnits Nat)
  statement: u = 0
  proof: AddUnits.ext (Nat.eq_zero_of_add_eq_zero u.val_neg).1

中文:
引理 addUnits_eq_zero
  条件: (u : 加法单位群 自然数)
  结论: u = 0
  证明: AddUnits.ext (Nat.eq_zero_of_add_eq_zero u.val_neg).1

Depends on / 依赖: AddUnits, AddUnits.ext, Nat.eq_zero_of_add_eq_zero, eq_zero_of_add_eq_zero, u.val_neg, val_neg
-/
lemma addUnits_eq_zero (u : AddUnits Nat) : u = 0 :=
AddUnits.ext (Nat.eq_zero_of_add_eq_zero u.val_neg).1

/--
Instance `unique_units` / 实例 `unique_units`

English:
instance unique_units
  signature: : Unique Natˣ where
  body: 1
  uniq := Nat.units_eq_one

中文:
实例 unique_units
  签名: : 唯一 自然数ˣ where
  定义体: 1
  uniq := Nat.units_eq_one
-/
instance unique_units : Unique Natˣ where
  default := 1
  uniq := Nat.units_eq_one

/--
Instance `unique_addUnits` / 实例 `unique_addUnits`

English:
instance unique_addUnits
  signature: : Unique (AddUnits Nat) where
  body: 0
  uniq := Nat.addUnits_eq_zero

中文:
实例 unique_addUnits
  签名: : 唯一 (加法单位群 自然数) where
  定义体: 0
  uniq := Nat.addUnits_eq_zero
-/
instance unique_addUnits : Unique (AddUnits Nat) where
  default := 0
  uniq := Nat.addUnits_eq_zero

/--
lemma `isUnit_iff` / 引理 `isUnit_iff`

English:
lemma isUnit_iff
  given: {n : Nat}
  statement: IsUnit n ↔ n = 1
  proof: isUnit_iff_eq_one

中文:
引理 isUnit_iff
  条件: {n : 自然数}
  结论: 是单位 n ↔ n = 1
  证明: isUnit_iff_eq_one
-/
protected lemma isUnit_iff {n : Nat} : IsUnit n ↔ n = 1 := isUnit_iff_eq_one

/--
lemma `isAddUnit_iff` / 引理 `isAddUnit_iff`

English:
lemma isAddUnit_iff
  given: {n : Nat}
  statement: IsAddUnit n ↔ n = 0
  proof: isAddUnit_iff_eq_zero

中文:
引理 isAddUnit_iff
  条件: {n : 自然数}
  结论: IsAddUnit n ↔ n = 0
  证明: isAddUnit_iff_eq_zero
-/
protected lemma isAddUnit_iff {n : Nat} : IsAddUnit n ↔ n = 0 := isAddUnit_iff_eq_zero

end Nat
