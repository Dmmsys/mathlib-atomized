/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Inner products of strongly measurable functions are strongly measurable.

-/

public section

variable {α 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace MeasureTheory

/-! ## Strongly measurable functions -/


local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace StronglyMeasurable

@[fun_prop]
/--
theorem `inner` / 定理 `inner`

English:
theorem inner
  statement: {_ : MeasurableSpace α} {f g : α -> E} (hf : StronglyMeasurable f)
  proof: Continuous.comp_stronglyMeasurable continuous_inner (hf.prodMk hg)

中文:
定理 inner
  结论: {_ : 可测空间 α} {f g : α -> E} (hf : StronglyMeasurable f)
  证明: Continuous.comp_stronglyMeasurable continuous_inner (hf.prodMk hg)
-/
protected theorem inner {_ : MeasurableSpace α} {f g : α -> E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => ⟪f t, g t⟫ :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prodMk hg)

end StronglyMeasurable

namespace AEStronglyMeasurable
variable {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α -> E} {c : E}

@[fun_prop]
/--
theorem `re` / 定理 `re`

English:
theorem re
  given: {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ)
  proof: RCLike.continuous_re.comp_aestronglyMeasurable hf

@[fun_prop]

中文:
定理 re
  条件: {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ)
  证明: RCLike.continuous_re.comp_aestronglyMeasurable hf

@[fun_prop]
-/
protected theorem re {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.re (f x)) μ :=
  RCLike.continuous_re.comp_aestronglyMeasurable hf

@[fun_prop]
/--
theorem `im` / 定理 `im`

English:
theorem im
  given: {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ)
  proof: RCLike.continuous_im.comp_aestronglyMeasurable hf

@[fun_prop]

中文:
定理 im
  条件: {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ)
  证明: RCLike.continuous_im.comp_aestronglyMeasurable hf

@[fun_prop]
-/
protected theorem im {f : α -> 𝕜} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => RCLike.im (f x)) μ :=
  RCLike.continuous_im.comp_aestronglyMeasurable hf

@[fun_prop]
/--
theorem `inner` / 定理 `inner`

English:
theorem inner
  statement: {_ : MeasurableSpace α} {μ : Measure α} {f g : α -> E}
  proof: continuous_inner.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]

中文:
定理 inner
  结论: {_ : 可测空间 α} {μ : 测度 α} {f g : α -> E}
  证明: continuous_inner.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
-/
protected theorem inner {_ : MeasurableSpace α} {μ : Measure α} {f g : α -> E}
    (hf : AEStronglyMeasurable[m] f μ) (hg : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/--
lemma `inner_const` / 引理 `inner_const`

English:
lemma inner_const
  given: (hf : AEStronglyMeasurable[m] f μ)
  statement: AEStronglyMeasurable[m] (⟪f ·, c⟫) μ
  proof: hf.inner aestronglyMeasurable_const

@[fun_prop]

中文:
引理 inner_const
  条件: (hf : AEStronglyMeasurable[m] f μ)
  结论: AEStronglyMeasurable[m] (⟪f ·, c⟫) μ
  证明: hf.inner aestronglyMeasurable_const

@[fun_prop]

Depends on / 依赖: aestronglyMeasurable_const, hf.inner
-/
lemma inner_const (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] (⟪f ·, c⟫) μ :=
  hf.inner aestronglyMeasurable_const

@[fun_prop]
/--
lemma `const_inner` / 引理 `const_inner`

English:
lemma const_inner
  given: (hg : AEStronglyMeasurable[m] g μ)
  statement: AEStronglyMeasurable[m] (⟪c, g ·⟫) μ
  proof: aestronglyMeasurable_const.inner hg

中文:
引理 const_inner
  条件: (hg : AEStronglyMeasurable[m] g μ)
  结论: AEStronglyMeasurable[m] (⟪c, g ·⟫) μ
  证明: aestronglyMeasurable_const.inner hg

Depends on / 依赖: aestronglyMeasurable_const, aestronglyMeasurable_const.inner
-/
lemma const_inner (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (⟪c, g ·⟫) μ :=
  aestronglyMeasurable_const.inner hg

end AEStronglyMeasurable

end MeasureTheory
