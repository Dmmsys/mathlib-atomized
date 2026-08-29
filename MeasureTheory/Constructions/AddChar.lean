/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurable space instance for additive characters

This file endows `AddChar A M` with the discrete measurable space structure whenever `A` is a finite
discrete measurable space.

## TODO

Give the definition in the correct generality.
-/

public section

namespace AddChar
variable {A M : Type*} [AddMonoid A] [Monoid M] [MeasurableSpace A] [MeasurableSpace M]

@[nolint unusedArguments]
/--
Instance `instMeasurableSpace` / 实例 `instMeasurableSpace`

English:
instance instMeasurableSpace
  signature: [DiscreteMeasurableSpace A] [Finite A]
  body: ⊤

中文:
实例 instMeasurableSpace
  签名: [DiscreteMeasurableSpace A] [Finite A]
  定义体: ⊤
-/
instance instMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    MeasurableSpace (AddChar A M) :=
  ⊤

/--
Instance `instDiscreteMeasurableSpace` / 实例 `instDiscreteMeasurableSpace`

English:
instance instDiscreteMeasurableSpace
  signature: [DiscreteMeasurableSpace A] [Finite A]
  body: ⟨fun _ => trivial⟩

中文:
实例 instDiscreteMeasurableSpace
  签名: [DiscreteMeasurableSpace A] [Finite A]
  定义体: ⟨fun _ => trivial⟩
-/
instance instDiscreteMeasurableSpace [DiscreteMeasurableSpace A] [Finite A] :
    DiscreteMeasurableSpace (AddChar A M) :=
  ⟨fun _ => trivial⟩

end AddChar
