/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of scalar products
-/

public section


variable {α : Type*} {𝕜 : Type*} {E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

@[fun_prop]
/--
theorem `Measurable.inner` / 定理 `Measurable.inner`

English:
theorem Measurable.inner
  statement: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: Continuous.measurable2 continuous_inner hf hg

@[fun_prop]

中文:
定理 Measurable.inner
  结论: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: Continuous.measurable2 continuous_inner hf hg

@[fun_prop]

Depends on / 依赖: Continuous, Continuous.measurable2, continuous_inner, measurable2
-/
theorem Measurable.inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {f g : α -> E} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun t => ⟪f t, g t⟫ :=
  Continuous.measurable2 continuous_inner hf hg

@[fun_prop]
/--
theorem `Measurable.const_inner` / 定理 `Measurable.const_inner`

English:
theorem Measurable.const_inner
  statement: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: Measurable.inner measurable_const hf

@[fun_prop]

中文:
定理 Measurable.const_inner
  结论: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: Measurable.inner measurable_const hf

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.inner, measurable_const
-/
theorem Measurable.const_inner {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α -> E} (hf : Measurable f) :
    Measurable fun t => ⟪c, f t⟫ :=
  Measurable.inner measurable_const hf

@[fun_prop]
/--
theorem `Measurable.inner_const` / 定理 `Measurable.inner_const`

English:
theorem Measurable.inner_const
  statement: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: Measurable.inner hf measurable_const

@[fun_prop]

中文:
定理 Measurable.inner_const
  结论: {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: Measurable.inner hf measurable_const

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.inner, measurable_const
-/
theorem Measurable.inner_const {_ : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {c : E} {f : α -> E} (hf : Measurable f) :
    Measurable fun t => ⟪f t, c⟫ :=
  Measurable.inner hf measurable_const

@[fun_prop]
/--
theorem `AEMeasurable.inner` / 定理 `AEMeasurable.inner`

English:
theorem AEMeasurable.inner
  statement: {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  proof: by
  fun_prop

@[fun_prop]

中文:
定理 AEMeasurable.inner
  结论: {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
  证明: by
  fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem AEMeasurable.inner {m : MeasurableSpace α} [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {μ : MeasureTheory.Measure α} {f g : α -> E}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => ⟪f x, g x⟫) μ := by
  fun_prop

@[fun_prop]
/--
theorem `AEMeasurable.const_inner` / 定理 `AEMeasurable.const_inner`

English:
theorem AEMeasurable.const_inner
  statement: {m : MeasurableSpace α} [MeasurableSpace E]
  proof: AEMeasurable.inner aemeasurable_const hf

@[fun_prop]

中文:
定理 AEMeasurable.const_inner
  结论: {m : MeasurableSpace α} [MeasurableSpace E]
  证明: AEMeasurable.inner aemeasurable_const hf

@[fun_prop]

Depends on / 依赖: AEMeasurable, AEMeasurable.inner, aemeasurable_const
-/
theorem AEMeasurable.const_inner {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α -> E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪c, f x⟫) μ :=
  AEMeasurable.inner aemeasurable_const hf

@[fun_prop]
/--
theorem `AEMeasurable.inner_const` / 定理 `AEMeasurable.inner_const`

English:
theorem AEMeasurable.inner_const
  statement: {m : MeasurableSpace α} [MeasurableSpace E]
  proof: AEMeasurable.inner hf aemeasurable_const

中文:
定理 AEMeasurable.inner_const
  结论: {m : MeasurableSpace α} [MeasurableSpace E]
  证明: AEMeasurable.inner hf aemeasurable_const

Depends on / 依赖: AEMeasurable, AEMeasurable.inner, aemeasurable_const
-/
theorem AEMeasurable.inner_const {m : MeasurableSpace α} [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure α} {f : α -> E} {c : E} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ⟪f x, c⟫) μ :=
  AEMeasurable.inner hf aemeasurable_const
