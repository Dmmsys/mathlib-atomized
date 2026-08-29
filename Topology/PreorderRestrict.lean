/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Order.Restriction
public import Mathlib.Topology.Constructions

/-!
# Continuity of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
continuous.
-/

public section

namespace Preorder

variable {α : Type*} [Preorder α] {X : α -> Type*} [forall i, TopologicalSpace (X i)]

@[continuity, fun_prop]
/--
theorem `continuous_restrictLe` / 定理 `continuous_restrictLe`

English:
theorem continuous_restrictLe
  given: (a : α)
  statement: Continuous (restrictLe (π := X) a)
  proof: Pi.continuous_domRestrict _

@[continuity, fun_prop]

中文:
定理 continuous_restrictLe
  条件: (a : α)
  结论: 连续 (restrictLe (π := X) a)
  证明: Pi.continuous_domRestrict _

@[continuity, fun_prop]
-/
theorem continuous_restrictLe (a : α) : Continuous (restrictLe (π := X) a) :=
  Pi.continuous_domRestrict _

@[continuity, fun_prop]
/--
theorem `continuous_restrictLe₂` / 定理 `continuous_restrictLe₂`

English:
theorem continuous_restrictLe₂
  given: {a b : α} (hab : a <= b)
  statement: Continuous (restrictLe₂ (π := X) hab)
  proof: Pi.continuous_domRestrict₂ _

中文:
定理 continuous_restrictLe₂
  条件: {a b : α} (hab : a <= b)
  结论: 连续 (restrictLe₂ (π := X) hab)
  证明: Pi.continuous_domRestrict₂ _
-/
theorem continuous_restrictLe₂ {a b : α} (hab : a <= b) : Continuous (restrictLe₂ (π := X) hab) :=
  Pi.continuous_domRestrict₂ _

variable [LocallyFiniteOrderBot α]

@[continuity, fun_prop]
/--
theorem `continuous_frestrictLe` / 定理 `continuous_frestrictLe`

English:
theorem continuous_frestrictLe
  given: (a : α)
  statement: Continuous (frestrictLe (π := X) a)
  proof: Finset.continuous_restrict _

@[continuity, fun_prop]

中文:
定理 continuous_frestrictLe
  条件: (a : α)
  结论: 连续 (frestrictLe (π := X) a)
  证明: Finset.continuous_restrict _

@[continuity, fun_prop]
-/
theorem continuous_frestrictLe (a : α) : Continuous (frestrictLe (π := X) a) :=
  Finset.continuous_restrict _

@[continuity, fun_prop]
/--
theorem `continuous_frestrictLe₂` / 定理 `continuous_frestrictLe₂`

English:
theorem continuous_frestrictLe₂
  given: {a b : α} (hab : a <= b)
  proof: Finset.continuous_restrict₂ _

中文:
定理 continuous_frestrictLe₂
  条件: {a b : α} (hab : a <= b)
  证明: Finset.continuous_restrict₂ _
-/
theorem continuous_frestrictLe₂ {a b : α} (hab : a <= b) :
    Continuous (frestrictLe₂ (π := X) hab) :=
  Finset.continuous_restrict₂ _

end Preorder
