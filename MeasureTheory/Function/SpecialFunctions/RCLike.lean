/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of the basic `RCLike` functions

-/

public section


noncomputable section

open NNReal ENNReal

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/--
theorem `measurable_re` / 定理 `measurable_re`

English:
theorem measurable_re
  statement: Measurable (re : 𝕜 -> Real)
  proof: continuous_re.measurable

中文:
定理 measurable_re
  结论: 可测 (re : 𝕜 -> 实数)
  证明: continuous_re.measurable

Depends on / 依赖: continuous_re, continuous_re.measurable, measurable
-/
theorem measurable_re : Measurable (re : 𝕜 -> Real) :=
  continuous_re.measurable

/--
theorem `measurable_im` / 定理 `measurable_im`

English:
theorem measurable_im
  statement: Measurable (im : 𝕜 -> Real)
  proof: continuous_im.measurable

中文:
定理 measurable_im
  结论: 可测 (im : 𝕜 -> 实数)
  证明: continuous_im.measurable

Depends on / 依赖: continuous_im, continuous_im.measurable, measurable
-/
theorem measurable_im : Measurable (im : 𝕜 -> Real) :=
  continuous_im.measurable

end RCLike

section RCLikeComposition

variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {f : α -> 𝕜}
  {μ : MeasureTheory.Measure α}

@[fun_prop]
/--
theorem `Measurable.re` / 定理 `Measurable.re`

English:
theorem Measurable.re
  given: (hf : Measurable f)
  statement: Measurable fun x => RCLike.re (f x)
  proof: RCLike.measurable_re.comp hf

@[fun_prop]

中文:
定理 可测.re
  条件: (hf : 可测 f)
  结论: 可测 fun x => RCLike.re (f x)
  证明: RCLike.measurable_re.comp hf

@[fun_prop]

Depends on / 依赖: RCLike, RCLike.measurable_re.comp, measurable_re
-/
theorem Measurable.re (hf : Measurable f) : Measurable fun x => RCLike.re (f x) :=
  RCLike.measurable_re.comp hf

@[fun_prop]
/--
theorem `AEMeasurable.re` / 定理 `AEMeasurable.re`

English:
theorem AEMeasurable.re
  given: (hf : AEMeasurable f μ)
  statement: AEMeasurable (fun x => RCLike.re (f x)) μ
  proof: RCLike.measurable_re.comp_aemeasurable hf

@[fun_prop]

中文:
定理 几乎处处可测.re
  条件: (hf : 几乎处处可测 f μ)
  结论: 几乎处处可测 (fun x => RCLike.re (f x)) μ
  证明: RCLike.measurable_re.comp_aemeasurable hf

@[fun_prop]

Depends on / 依赖: RCLike, RCLike.measurable_re.comp_aemeasurable, comp_aemeasurable, measurable_re
-/
theorem AEMeasurable.re (hf : AEMeasurable f μ) : AEMeasurable (fun x => RCLike.re (f x)) μ :=
  RCLike.measurable_re.comp_aemeasurable hf

@[fun_prop]
/--
theorem `Measurable.im` / 定理 `Measurable.im`

English:
theorem Measurable.im
  given: (hf : Measurable f)
  statement: Measurable fun x => RCLike.im (f x)
  proof: RCLike.measurable_im.comp hf

@[fun_prop]

中文:
定理 可测.im
  条件: (hf : 可测 f)
  结论: 可测 fun x => RCLike.im (f x)
  证明: RCLike.measurable_im.comp hf

@[fun_prop]

Depends on / 依赖: RCLike, RCLike.measurable_im.comp, measurable_im
-/
theorem Measurable.im (hf : Measurable f) : Measurable fun x => RCLike.im (f x) :=
  RCLike.measurable_im.comp hf

@[fun_prop]
/--
theorem `AEMeasurable.im` / 定理 `AEMeasurable.im`

English:
theorem AEMeasurable.im
  given: (hf : AEMeasurable f μ)
  statement: AEMeasurable (fun x => RCLike.im (f x)) μ
  proof: RCLike.measurable_im.comp_aemeasurable hf

中文:
定理 几乎处处可测.im
  条件: (hf : 几乎处处可测 f μ)
  结论: 几乎处处可测 (fun x => RCLike.im (f x)) μ
  证明: RCLike.measurable_im.comp_aemeasurable hf

Depends on / 依赖: RCLike, RCLike.measurable_im.comp_aemeasurable, comp_aemeasurable, measurable_im
-/
theorem AEMeasurable.im (hf : AEMeasurable f μ) : AEMeasurable (fun x => RCLike.im (f x)) μ :=
  RCLike.measurable_im.comp_aemeasurable hf

end RCLikeComposition

section

variable {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {f : α -> 𝕜} {μ : MeasureTheory.Measure α}

@[fun_prop]
/--
theorem `RCLike.measurable_ofReal` / 定理 `RCLike.measurable_ofReal`

English:
theorem RCLike.measurable_ofReal
  statement: Measurable ((↑) : Real -> 𝕜)
  proof: RCLike.continuous_ofReal.measurable

中文:
定理 RCLike.measurable_of实数
  结论: 可测 ((↑) : 实数 -> 𝕜)
  证明: RCLike.continuous_ofReal.measurable

Depends on / 依赖: RCLike, RCLike.continuous_ofReal.measurable, continuous_ofReal, measurable
-/
theorem RCLike.measurable_ofReal : Measurable ((↑) : Real -> 𝕜) :=
  RCLike.continuous_ofReal.measurable

/--
theorem `measurable_of_re_im` / 定理 `measurable_of_re_im`

English:
theorem measurable_of_re_im
  statement: (hre : Measurable fun x => RCLike.re (f x))
  proof: by
  convert!
    Measurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp hre)
      ((RCLike.measurable_ofReal.comp him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

中文:
定理 measurable_of_re_im
  结论: (hre : 可测 fun x => RCLike.re (f x))
  证明: by
  convert!
    Measurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp hre)
      ((RCLike.measurable_ofReal.comp him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

Depends on / 依赖: Measurable, Measurable.fun_add, RCLike, RCLike.I, RCLike.measurable_ofReal.comp, RCLike.re_add_im, convert, fun_add, measurable_ofReal, mul_const, re_add_im
-/
theorem measurable_of_re_im (hre : Measurable fun x => RCLike.re (f x))
    (him : Measurable fun x => RCLike.im (f x)) : Measurable f := by
  convert!
    Measurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp hre)
      ((RCLike.measurable_ofReal.comp him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

/--
theorem `aemeasurable_of_re_im` / 定理 `aemeasurable_of_re_im`

English:
theorem aemeasurable_of_re_im
  statement: (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
  proof: by
  convert!
    AEMeasurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

中文:
定理 aemeasurable_of_re_im
  结论: (hre : 几乎处处可测 (fun x => RCLike.re (f x)) μ)
  证明: by
  convert!
    AEMeasurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

Depends on / 依赖: AEMeasurable, AEMeasurable.fun_add, RCLike, RCLike.I, RCLike.measurable_ofReal.comp_aemeasurable, RCLike.re_add_im, comp_aemeasurable, convert, fun_add, measurable_ofReal, mul_const, re_add_im
-/
theorem aemeasurable_of_re_im (hre : AEMeasurable (fun x => RCLike.re (f x)) μ)
    (him : AEMeasurable (fun x => RCLike.im (f x)) μ) : AEMeasurable f μ := by
  convert!
    AEMeasurable.fun_add (M := 𝕜) (RCLike.measurable_ofReal.comp_aemeasurable hre)
      ((RCLike.measurable_ofReal.comp_aemeasurable him).mul_const RCLike.I)
  exact (RCLike.re_add_im _).symm

end
