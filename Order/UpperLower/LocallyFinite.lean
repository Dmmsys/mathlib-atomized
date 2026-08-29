/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.UpperLower.Closure

/-!
# Upper and lower sets in a locally finite order

In this file we characterise the interaction of `UpperSet`/`LowerSet` and `LocallyFiniteOrder`.
-/

public section


namespace Set

variable {α : Type*} [Preorder α] {s : Set α}

/--
theorem `Finite.upperClosure` / 定理 `Finite.upperClosure`

English:
theorem Finite.upperClosure
  given: [LocallyFiniteOrderTop α] (hs : s.Finite)
  proof: by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _

中文:
定理 有限.upperClosure
  条件: [LocallyFiniteOrderTop α] (hs : s.有限)
  证明: by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _
-/
protected theorem Finite.upperClosure [LocallyFiniteOrderTop α] (hs : s.Finite) :
    (upperClosure s : Set α).Finite := by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _

/--
theorem `Finite.lowerClosure` / 定理 `Finite.lowerClosure`

English:
theorem Finite.lowerClosure
  given: [LocallyFiniteOrderBot α] (hs : s.Finite)
  proof: by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _

中文:
定理 有限.lowerClosure
  条件: [LocallyFiniteOrderBot α] (hs : s.有限)
  证明: by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _
-/
protected theorem Finite.lowerClosure [LocallyFiniteOrderBot α] (hs : s.Finite) :
    (lowerClosure s : Set α).Finite := by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _

end Set
