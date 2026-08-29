/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of arctan

-/

public section


namespace Real

/--
theorem `measurable_arctan` / 定理 `measurable_arctan`

English:
theorem measurable_arctan
  statement: Measurable arctan
  proof: continuous_arctan.measurable

中文:
定理 measurable_arctan
  结论: 可测 arctan
  证明: continuous_arctan.measurable

Depends on / 依赖: continuous_arctan, continuous_arctan.measurable, measurable
-/
theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable

end Real

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α -> Real}

@[fun_prop]
/--
theorem `Measurable.arctan` / 定理 `Measurable.arctan`

English:
theorem Measurable.arctan
  given: (hf : Measurable f)
  statement: Measurable fun x => arctan (f x)
  proof: measurable_arctan.comp hf

中文:
定理 可测.arctan
  条件: (hf : 可测 f)
  结论: 可测 fun x => arctan (f x)
  证明: measurable_arctan.comp hf

Depends on / 依赖: measurable_arctan, measurable_arctan.comp
-/
theorem Measurable.arctan (hf : Measurable f) : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf

end RealComposition
