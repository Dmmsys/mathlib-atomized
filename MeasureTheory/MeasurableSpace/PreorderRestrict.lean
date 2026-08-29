/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Restriction

/-!
# Measurability of the restriction function for functions indexed by a preorder

We prove that the map which restricts a function `f : (i : α) → X i` to elements `≤ a` is
measurable.
-/

public section

open MeasureTheory

namespace Preorder

variable {α : Type*} [Preorder α] {X : α -> Type*} [forall a, MeasurableSpace (X a)]

@[fun_prop]
/--
theorem `measurable_restrictLe` / 定理 `measurable_restrictLe`

English:
theorem measurable_restrictLe
  given: (a : α)
  statement: Measurable (restrictLe (π := X) a)
  proof: Set.measurable_restrict _

@[fun_prop]

中文:
定理 measurable_restrictLe
  条件: (a : α)
  结论: Measurable (restrictLe (π := X) a)
  证明: Set.measurable_restrict _

@[fun_prop]
-/
theorem measurable_restrictLe (a : α) : Measurable (restrictLe (π := X) a) :=
    Set.measurable_restrict _

@[fun_prop]
/--
theorem `measurable_restrictLe₂` / 定理 `measurable_restrictLe₂`

English:
theorem measurable_restrictLe₂
  given: {a b : α} (hab : a <= b)
  statement: Measurable (restrictLe₂ (π := X) hab)
  proof: Set.measurable_restrict₂ _

中文:
定理 measurable_restrictLe₂
  条件: {a b : α} (hab : a <= b)
  结论: Measurable (restrictLe₂ (π := X) hab)
  证明: Set.measurable_restrict₂ _
-/
theorem measurable_restrictLe₂ {a b : α} (hab : a <= b) : Measurable (restrictLe₂ (π := X) hab) :=
  Set.measurable_restrict₂ _

variable [LocallyFiniteOrderBot α]

@[fun_prop]
/--
theorem `measurable_frestrictLe` / 定理 `measurable_frestrictLe`

English:
theorem measurable_frestrictLe
  given: (a : α)
  statement: Measurable (frestrictLe (π := X) a)
  proof: Finset.measurable_restrict _

@[fun_prop]

中文:
定理 measurable_frestrictLe
  条件: (a : α)
  结论: Measurable (frestrictLe (π := X) a)
  证明: Finset.measurable_restrict _

@[fun_prop]
-/
theorem measurable_frestrictLe (a : α) : Measurable (frestrictLe (π := X) a) :=
  Finset.measurable_restrict _

@[fun_prop]
/--
theorem `measurable_frestrictLe₂` / 定理 `measurable_frestrictLe₂`

English:
theorem measurable_frestrictLe₂
  given: {a b : α} (hab : a <= b)
  statement: Measurable (frestrictLe₂ (π := X) hab)
  proof: Finset.measurable_restrict₂ _

中文:
定理 measurable_frestrictLe₂
  条件: {a b : α} (hab : a <= b)
  结论: Measurable (frestrictLe₂ (π := X) hab)
  证明: Finset.measurable_restrict₂ _
-/
theorem measurable_frestrictLe₂ {a b : α} (hab : a <= b) : Measurable (frestrictLe₂ (π := X) hab) :=
  Finset.measurable_restrict₂ _

end Preorder
