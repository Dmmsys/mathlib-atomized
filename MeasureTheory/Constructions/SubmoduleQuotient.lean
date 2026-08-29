/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability on the quotient of a module by a submodule
-/

public section

namespace Submodule.Quotient
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MeasurableSpace
  signature: M] : MeasurableSpace (M ⧸ p)
  body: Quotient.instMeasurableSpace

中文:
实例 [可测空间
  签名: M] : 可测空间 (M ⧸ p)
  定义体: Quotient.instMeasurableSpace

Depends on / 依赖: Quotient, Quotient.instMeasurableSpace, instMeasurableSpace
-/
instance [MeasurableSpace M] : MeasurableSpace (M ⧸ p) := Quotient.instMeasurableSpace
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MeasurableSpace
  signature: M] [DiscreteMeasurableSpace M] : DiscreteMeasurableSpace (M ⧸ p)
  body: Quotient.instDiscreteMeasurableSpace

中文:
实例 [可测空间
  签名: M] [DiscreteMeasurable空间 M] : DiscreteMeasurable空间 (M ⧸ p)
  定义体: Quotient.instDiscreteMeasurableSpace

Depends on / 依赖: Quotient, Quotient.instDiscreteMeasurableSpace, instDiscreteMeasurableSpace
-/
instance [MeasurableSpace M] [DiscreteMeasurableSpace M] : DiscreteMeasurableSpace (M ⧸ p) :=
  Quotient.instDiscreteMeasurableSpace

end Submodule.Quotient
