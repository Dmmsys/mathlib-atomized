/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Measurability of real and complex functions

We show that most standard real and complex functions are measurable, notably `exp`, `cos`, `sin`,
`cosh`, `sinh`, `log`, `pow`, `arcsin`, `arccos`.

See also `MeasureTheory.Function.SpecialFunctions.Arctan` and
`MeasureTheory.Function.SpecialFunctions.Inner`, which have been split off to minimize imports.
-/

public section

-- Guard against import creep:
assert_not_exists InnerProductSpace Real.arctan FiniteDimensional.proper

noncomputable section

open NNReal ENNReal MeasureTheory

namespace Real

variable {α : Type*} {_ : MeasurableSpace α} {f : α -> Real} {μ : MeasureTheory.Measure α}

/--
theorem `measurable_exp` / 定理 `measurable_exp`

English:
theorem measurable_exp
  statement: Measurable exp
  proof: continuous_exp.measurable

中文:
定理 measurable_exp
  结论: 可测 exp
  证明: continuous_exp.measurable

Depends on / 依赖: continuous_exp, continuous_exp.measurable, measurable
-/
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable

/--
theorem `measurable_log` / 定理 `measurable_log`

English:
theorem measurable_log
  statement: Measurable log
  proof: measurable_of_measurable_on_compl_singleton 0
Continuous.measurable continuousOn_iff_continuous_domRestrict.1 continuousOn_log

中文:
定理 measurable_log
  结论: 可测 log
  证明: measurable_of_measurable_on_compl_singleton 0
Continuous.measurable continuousOn_iff_continuous_domRestrict.1 continuousOn_log

Depends on / 依赖: Continuous, Continuous.measurable, continuousOn_iff_continuous_domRestrict, continuousOn_log, measurable, measurable_of_measurable_on_compl_singleton
-/
theorem measurable_log : Measurable log :=
measurable_of_measurable_on_compl_singleton 0
Continuous.measurable continuousOn_iff_continuous_domRestrict.1 continuousOn_log

/--
lemma `measurable_of_measurable_exp` / 引理 `measurable_of_measurable_exp`

English:
lemma measurable_of_measurable_exp
  given: (hf : Measurable (fun x => exp (f x)))
  proof: by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

中文:
引理 measurable_of_measurable_exp
  条件: (hf : 可测 (fun x => exp (f x)))
  证明: by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

Depends on / 依赖: log_exp, measurable_log, measurable_log.comp
-/
lemma measurable_of_measurable_exp (hf : Measurable (fun x => exp (f x))) :
    Measurable f := by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp hf

/--
lemma `aemeasurable_of_aemeasurable_exp` / 引理 `aemeasurable_of_aemeasurable_exp`

English:
lemma aemeasurable_of_aemeasurable_exp
  given: (hf : AEMeasurable (fun x => exp (f x)) μ)
  proof: by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

中文:
引理 aemeasurable_of_aemeasurable_exp
  条件: (hf : 几乎处处可测 (fun x => exp (f x)) μ)
  证明: by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

Depends on / 依赖: LiesOver, LiesOver.over, coe_mk_comp, comp_aemeasurable, log_exp, measurable_log, measurable_log.comp_aemeasurable
-/
lemma aemeasurable_of_aemeasurable_exp (hf : AEMeasurable (fun x => exp (f x)) μ) :
    AEMeasurable f μ := by
  have : f = fun x => log (exp (f x)) := by ext; rw [log_exp]
  rw [this]
  exact measurable_log.comp_aemeasurable hf

/--
lemma `aemeasurable_of_aemeasurable_exp_mul` / 引理 `aemeasurable_of_aemeasurable_exp_mul`

English:
lemma aemeasurable_of_aemeasurable_exp_mul
  statement: {t : Real}
  proof: by
  simpa only [mul_div_cancel_left₀ _ ht]
    using (aemeasurable_of_aemeasurable_exp hf).fun_div (aemeasurable_const (b := t))

中文:
引理 aemeasurable_of_aemeasurable_exp_mul
  结论: {t : 实数}
  证明: by
  simpa only [mul_div_cancel_left₀ _ ht]
    using (aemeasurable_of_aemeasurable_exp hf).fun_div (aemeasurable_const (b := t))

Depends on / 依赖: aemeasurable_const, aemeasurable_of_aemeasurable_exp, fun_div
-/
lemma aemeasurable_of_aemeasurable_exp_mul {t : Real}
    (ht : t != 0) (hf : AEMeasurable (fun x => exp (t * f x)) μ) :
    AEMeasurable f μ := by
  simpa only [mul_div_cancel_left₀ _ ht]
    using (aemeasurable_of_aemeasurable_exp hf).fun_div (aemeasurable_const (b := t))

/--
theorem `measurable_sin` / 定理 `measurable_sin`

English:
theorem measurable_sin
  statement: Measurable sin
  proof: continuous_sin.measurable

中文:
定理 measurable_sin
  结论: 可测 sin
  证明: continuous_sin.measurable

Depends on / 依赖: continuous_sin, continuous_sin.measurable, measurable
-/
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable

/--
theorem `measurable_cos` / 定理 `measurable_cos`

English:
theorem measurable_cos
  statement: Measurable cos
  proof: continuous_cos.measurable

中文:
定理 measurable_cos
  结论: 可测 cos
  证明: continuous_cos.measurable

Depends on / 依赖: continuous_cos, continuous_cos.measurable, measurable
-/
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable

/--
theorem `measurable_sinh` / 定理 `measurable_sinh`

English:
theorem measurable_sinh
  statement: Measurable sinh
  proof: continuous_sinh.measurable

中文:
定理 measurable_sinh
  结论: 可测 sinh
  证明: continuous_sinh.measurable

Depends on / 依赖: continuous_sinh, continuous_sinh.measurable, measurable
-/
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable

/--
theorem `measurable_cosh` / 定理 `measurable_cosh`

English:
theorem measurable_cosh
  statement: Measurable cosh
  proof: continuous_cosh.measurable

@[fun_prop]

中文:
定理 measurable_cosh
  结论: 可测 cosh
  证明: continuous_cosh.measurable

@[fun_prop]

Depends on / 依赖: continuous_cosh, continuous_cosh.measurable, measurable
-/
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable

@[fun_prop]
/--
theorem `measurable_arcsin` / 定理 `measurable_arcsin`

English:
theorem measurable_arcsin
  statement: Measurable arcsin
  proof: continuous_arcsin.measurable

@[fun_prop]

中文:
定理 measurable_arcsin
  结论: 可测 arcsin
  证明: continuous_arcsin.measurable

@[fun_prop]

Depends on / 依赖: continuous_arcsin, continuous_arcsin.measurable, measurable
-/
theorem measurable_arcsin : Measurable arcsin :=
  continuous_arcsin.measurable

@[fun_prop]
/--
theorem `measurable_arccos` / 定理 `measurable_arccos`

English:
theorem measurable_arccos
  statement: Measurable arccos
  proof: continuous_arccos.measurable

中文:
定理 measurable_arccos
  结论: 可测 arccos
  证明: continuous_arccos.measurable

Depends on / 依赖: continuous_arccos, continuous_arccos.measurable, measurable
-/
theorem measurable_arccos : Measurable arccos :=
  continuous_arccos.measurable

end Real

namespace Complex

@[fun_prop]
/--
theorem `measurable_re` / 定理 `measurable_re`

English:
theorem measurable_re
  statement: Measurable re
  proof: continuous_re.measurable

@[fun_prop]

中文:
定理 measurable_re
  结论: 可测 re
  证明: continuous_re.measurable

@[fun_prop]

Depends on / 依赖: continuous_re, continuous_re.measurable, measurable
-/
theorem measurable_re : Measurable re :=
  continuous_re.measurable

@[fun_prop]
/--
theorem `measurable_im` / 定理 `measurable_im`

English:
theorem measurable_im
  statement: Measurable im
  proof: continuous_im.measurable

中文:
定理 measurable_im
  结论: 可测 im
  证明: continuous_im.measurable

Depends on / 依赖: continuous_im, continuous_im.measurable, measurable
-/
theorem measurable_im : Measurable im :=
  continuous_im.measurable

/--
theorem `measurable_ofReal` / 定理 `measurable_ofReal`

English:
theorem measurable_ofReal
  statement: Measurable ((↑) : Real -> Complex)
  proof: continuous_ofReal.measurable

中文:
定理 measurable_of实数
  结论: 可测 ((↑) : 实数 -> 复形)
  证明: continuous_ofReal.measurable

Depends on / 依赖: continuous_ofReal, continuous_ofReal.measurable, measurable
-/
theorem measurable_ofReal : Measurable ((↑) : Real -> Complex) :=
  continuous_ofReal.measurable

/--
theorem `measurable_exp` / 定理 `measurable_exp`

English:
theorem measurable_exp
  statement: Measurable exp
  proof: continuous_exp.measurable

中文:
定理 measurable_exp
  结论: 可测 exp
  证明: continuous_exp.measurable

Depends on / 依赖: continuous_exp, continuous_exp.measurable, measurable
-/
theorem measurable_exp : Measurable exp :=
  continuous_exp.measurable

/--
theorem `measurable_sin` / 定理 `measurable_sin`

English:
theorem measurable_sin
  statement: Measurable sin
  proof: continuous_sin.measurable

中文:
定理 measurable_sin
  结论: 可测 sin
  证明: continuous_sin.measurable

Depends on / 依赖: continuous_sin, continuous_sin.measurable, measurable
-/
theorem measurable_sin : Measurable sin :=
  continuous_sin.measurable

/--
theorem `measurable_cos` / 定理 `measurable_cos`

English:
theorem measurable_cos
  statement: Measurable cos
  proof: continuous_cos.measurable

中文:
定理 measurable_cos
  结论: 可测 cos
  证明: continuous_cos.measurable

Depends on / 依赖: continuous_cos, continuous_cos.measurable, measurable
-/
theorem measurable_cos : Measurable cos :=
  continuous_cos.measurable

/--
theorem `measurable_sinh` / 定理 `measurable_sinh`

English:
theorem measurable_sinh
  statement: Measurable sinh
  proof: continuous_sinh.measurable

中文:
定理 measurable_sinh
  结论: 可测 sinh
  证明: continuous_sinh.measurable

Depends on / 依赖: continuous_sinh, continuous_sinh.measurable, measurable
-/
theorem measurable_sinh : Measurable sinh :=
  continuous_sinh.measurable

/--
theorem `measurable_cosh` / 定理 `measurable_cosh`

English:
theorem measurable_cosh
  statement: Measurable cosh
  proof: continuous_cosh.measurable

中文:
定理 measurable_cosh
  结论: 可测 cosh
  证明: continuous_cosh.measurable

Depends on / 依赖: continuous_cosh, continuous_cosh.measurable, measurable
-/
theorem measurable_cosh : Measurable cosh :=
  continuous_cosh.measurable

/--
theorem `measurable_arg` / 定理 `measurable_arg`

English:
theorem measurable_arg
  statement: Measurable arg
  proof: Measurable.ite (by measurability) (by fun_prop)
    Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

中文:
定理 measurable_arg
  结论: 可测 arg
  证明: Measurable.ite (by measurability) (by fun_prop)
    Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

Depends on / 依赖: Measurable, Measurable.ite, fun_prop, measurability
-/
theorem measurable_arg : Measurable arg :=
Measurable.ite (by measurability) (by fun_prop)
    Measurable.ite (by measurability) (by fun_prop) (by fun_prop)

/--
theorem `measurable_log` / 定理 `measurable_log`

English:
theorem measurable_log
  statement: Measurable log
  proof: (measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add
    (measurable_ofReal.comp measurable_arg).mul_const I

中文:
定理 measurable_log
  结论: 可测 log
  证明: (measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add
    (measurable_ofReal.comp measurable_arg).mul_const I

Depends on / 依赖: Real.measurable_log.comp, measurable_arg, measurable_log, measurable_norm, measurable_ofReal, measurable_ofReal.comp, mul_const
-/
theorem measurable_log : Measurable log :=
(measurable_ofReal.comp <| Real.measurable_log.comp measurable_norm).add
    (measurable_ofReal.comp measurable_arg).mul_const I

end Complex

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α -> Real} (hf : Measurable f)
include hf

@[fun_prop]
/--
theorem `Measurable.exp` / 定理 `Measurable.exp`

English:
theorem Measurable.exp
  statement: Measurable fun x => Real.exp (f x)
  proof: Real.measurable_exp.comp hf

@[fun_prop]

中文:
定理 可测.exp
  结论: 可测 fun x => 实数.exp (f x)
  证明: Real.measurable_exp.comp hf

@[fun_prop]
-/
protected theorem Measurable.exp : Measurable fun x => Real.exp (f x) :=
  Real.measurable_exp.comp hf

@[fun_prop]
/--
theorem `Measurable.log` / 定理 `Measurable.log`

English:
theorem Measurable.log
  statement: Measurable fun x => log (f x)
  proof: measurable_log.comp hf

@[fun_prop]

中文:
定理 可测.log
  结论: 可测 fun x => log (f x)
  证明: measurable_log.comp hf

@[fun_prop]
-/
protected theorem Measurable.log : Measurable fun x => log (f x) :=
  measurable_log.comp hf

@[fun_prop]
/--
theorem `Measurable.cos` / 定理 `Measurable.cos`

English:
theorem Measurable.cos
  statement: Measurable fun x => cos (f x)
  proof: measurable_cos.comp hf

@[fun_prop]

中文:
定理 可测.cos
  结论: 可测 fun x => cos (f x)
  证明: measurable_cos.comp hf

@[fun_prop]
-/
protected theorem Measurable.cos : Measurable fun x => cos (f x) := measurable_cos.comp hf

@[fun_prop]
/--
theorem `Measurable.sin` / 定理 `Measurable.sin`

English:
theorem Measurable.sin
  statement: Measurable fun x => sin (f x)
  proof: measurable_sin.comp hf

@[fun_prop]

中文:
定理 可测.sin
  结论: 可测 fun x => sin (f x)
  证明: measurable_sin.comp hf

@[fun_prop]
-/
protected theorem Measurable.sin : Measurable fun x => sin (f x) := measurable_sin.comp hf

@[fun_prop]
/--
theorem `Measurable.cosh` / 定理 `Measurable.cosh`

English:
theorem Measurable.cosh
  statement: Measurable fun x => cosh (f x)
  proof: measurable_cosh.comp hf

@[fun_prop]

中文:
定理 可测.cosh
  结论: 可测 fun x => cosh (f x)
  证明: measurable_cosh.comp hf

@[fun_prop]
-/
protected theorem Measurable.cosh : Measurable fun x => cosh (f x) := measurable_cosh.comp hf

@[fun_prop]
/--
theorem `Measurable.sinh` / 定理 `Measurable.sinh`

English:
theorem Measurable.sinh
  statement: Measurable fun x => sinh (f x)
  proof: measurable_sinh.comp hf

@[fun_prop]

中文:
定理 可测.sinh
  结论: 可测 fun x => sinh (f x)
  证明: measurable_sinh.comp hf

@[fun_prop]
-/
protected theorem Measurable.sinh : Measurable fun x => sinh (f x) := measurable_sinh.comp hf

@[fun_prop]
/--
theorem `Measurable.sqrt` / 定理 `Measurable.sqrt`

English:
theorem Measurable.sqrt
  statement: Measurable fun x => √(f x)
  proof: continuous_sqrt.measurable.comp hf

中文:
定理 可测.sqrt
  结论: 可测 fun x => √(f x)
  证明: continuous_sqrt.measurable.comp hf
-/
protected theorem Measurable.sqrt : Measurable fun x => √(f x) := continuous_sqrt.measurable.comp hf

end RealComposition

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α -> Real} (hf : AEMeasurable f μ)
include hf

@[fun_prop]
/--
lemma `AEMeasurable.exp` / 引理 `AEMeasurable.exp`

English:
lemma AEMeasurable.exp
  statement: AEMeasurable (fun x => exp (f x)) μ
  proof: measurable_exp.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.exp
  结论: 几乎处处可测 (fun x => exp (f x)) μ
  证明: measurable_exp.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.exp : AEMeasurable (fun x => exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.log` / 引理 `AEMeasurable.log`

English:
lemma AEMeasurable.log
  statement: AEMeasurable (fun x => log (f x)) μ
  proof: measurable_log.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.log
  结论: 几乎处处可测 (fun x => log (f x)) μ
  证明: measurable_log.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.log : AEMeasurable (fun x => log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.cos` / 引理 `AEMeasurable.cos`

English:
lemma AEMeasurable.cos
  statement: AEMeasurable (fun x => cos (f x)) μ
  proof: measurable_cos.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.cos
  结论: 几乎处处可测 (fun x => cos (f x)) μ
  证明: measurable_cos.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.cos : AEMeasurable (fun x => cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.sin` / 引理 `AEMeasurable.sin`

English:
lemma AEMeasurable.sin
  statement: AEMeasurable (fun x => sin (f x)) μ
  proof: measurable_sin.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.sin
  结论: 几乎处处可测 (fun x => sin (f x)) μ
  证明: measurable_sin.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.sin : AEMeasurable (fun x => sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.cosh` / 引理 `AEMeasurable.cosh`

English:
lemma AEMeasurable.cosh
  statement: AEMeasurable (fun x => cosh (f x)) μ
  proof: measurable_cosh.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.cosh
  结论: 几乎处处可测 (fun x => cosh (f x)) μ
  证明: measurable_cosh.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.cosh : AEMeasurable (fun x => cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.sinh` / 引理 `AEMeasurable.sinh`

English:
lemma AEMeasurable.sinh
  statement: AEMeasurable (fun x => sinh (f x)) μ
  proof: measurable_sinh.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.sinh
  结论: 几乎处处可测 (fun x => sinh (f x)) μ
  证明: measurable_sinh.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.sinh : AEMeasurable (fun x => sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.sqrt` / 引理 `AEMeasurable.sqrt`

English:
lemma AEMeasurable.sqrt
  statement: AEMeasurable (fun x => √(f x)) μ
  proof: continuous_sqrt.measurable.comp_aemeasurable hf

中文:
引理 几乎处处可测.sqrt
  结论: 几乎处处可测 (fun x => √(f x)) μ
  证明: continuous_sqrt.measurable.comp_aemeasurable hf
-/
protected lemma AEMeasurable.sqrt : AEMeasurable (fun x => √(f x)) μ :=
  continuous_sqrt.measurable.comp_aemeasurable hf

end RealComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {f : α -> Complex} (hf : Measurable f)
include hf

@[fun_prop]
/--
theorem `Measurable.cexp` / 定理 `Measurable.cexp`

English:
theorem Measurable.cexp
  statement: Measurable fun x => Complex.exp (f x)
  proof: Complex.measurable_exp.comp hf

@[fun_prop]

中文:
定理 可测.cexp
  结论: 可测 fun x => 复形.exp (f x)
  证明: Complex.measurable_exp.comp hf

@[fun_prop]
-/
protected theorem Measurable.cexp : Measurable fun x => Complex.exp (f x) :=
  Complex.measurable_exp.comp hf

@[fun_prop]
/--
theorem `Measurable.ccos` / 定理 `Measurable.ccos`

English:
theorem Measurable.ccos
  statement: Measurable fun x => Complex.cos (f x)
  proof: Complex.measurable_cos.comp hf

@[fun_prop]

中文:
定理 可测.ccos
  结论: 可测 fun x => 复形.cos (f x)
  证明: Complex.measurable_cos.comp hf

@[fun_prop]
-/
protected theorem Measurable.ccos : Measurable fun x => Complex.cos (f x) :=
  Complex.measurable_cos.comp hf

@[fun_prop]
/--
theorem `Measurable.csin` / 定理 `Measurable.csin`

English:
theorem Measurable.csin
  statement: Measurable fun x => Complex.sin (f x)
  proof: Complex.measurable_sin.comp hf

@[fun_prop]

中文:
定理 可测.csin
  结论: 可测 fun x => 复形.sin (f x)
  证明: Complex.measurable_sin.comp hf

@[fun_prop]
-/
protected theorem Measurable.csin : Measurable fun x => Complex.sin (f x) :=
  Complex.measurable_sin.comp hf

@[fun_prop]
/--
theorem `Measurable.ccosh` / 定理 `Measurable.ccosh`

English:
theorem Measurable.ccosh
  statement: Measurable fun x => Complex.cosh (f x)
  proof: Complex.measurable_cosh.comp hf

@[fun_prop]

中文:
定理 可测.ccosh
  结论: 可测 fun x => 复形.cosh (f x)
  证明: Complex.measurable_cosh.comp hf

@[fun_prop]
-/
protected theorem Measurable.ccosh : Measurable fun x => Complex.cosh (f x) :=
  Complex.measurable_cosh.comp hf

@[fun_prop]
/--
theorem `Measurable.csinh` / 定理 `Measurable.csinh`

English:
theorem Measurable.csinh
  statement: Measurable fun x => Complex.sinh (f x)
  proof: Complex.measurable_sinh.comp hf

@[fun_prop]

中文:
定理 可测.csinh
  结论: 可测 fun x => 复形.sinh (f x)
  证明: Complex.measurable_sinh.comp hf

@[fun_prop]
-/
protected theorem Measurable.csinh : Measurable fun x => Complex.sinh (f x) :=
  Complex.measurable_sinh.comp hf

@[fun_prop]
/--
theorem `Measurable.carg` / 定理 `Measurable.carg`

English:
theorem Measurable.carg
  statement: Measurable fun x => arg (f x)
  proof: measurable_arg.comp hf

@[fun_prop]

中文:
定理 可测.carg
  结论: 可测 fun x => arg (f x)
  证明: measurable_arg.comp hf

@[fun_prop]
-/
protected theorem Measurable.carg : Measurable fun x => arg (f x) :=
  measurable_arg.comp hf

@[fun_prop]
/--
theorem `Measurable.clog` / 定理 `Measurable.clog`

English:
theorem Measurable.clog
  statement: Measurable fun x => Complex.log (f x)
  proof: measurable_log.comp hf

中文:
定理 可测.clog
  结论: 可测 fun x => 复形.log (f x)
  证明: measurable_log.comp hf
-/
protected theorem Measurable.clog : Measurable fun x => Complex.log (f x) :=
  measurable_log.comp hf

end ComplexComposition

section ComplexComposition

open Complex

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α -> Complex} (hf : AEMeasurable f μ)
include hf

@[fun_prop]
/--
lemma `AEMeasurable.cexp` / 引理 `AEMeasurable.cexp`

English:
lemma AEMeasurable.cexp
  statement: AEMeasurable (fun x => exp (f x)) μ
  proof: measurable_exp.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.cexp
  结论: 几乎处处可测 (fun x => exp (f x)) μ
  证明: measurable_exp.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.cexp : AEMeasurable (fun x => exp (f x)) μ :=
  measurable_exp.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.ccos` / 引理 `AEMeasurable.ccos`

English:
lemma AEMeasurable.ccos
  statement: AEMeasurable (fun x => cos (f x)) μ
  proof: measurable_cos.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.ccos
  结论: 几乎处处可测 (fun x => cos (f x)) μ
  证明: measurable_cos.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.ccos : AEMeasurable (fun x => cos (f x)) μ :=
  measurable_cos.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.csin` / 引理 `AEMeasurable.csin`

English:
lemma AEMeasurable.csin
  statement: AEMeasurable (fun x => sin (f x)) μ
  proof: measurable_sin.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.csin
  结论: 几乎处处可测 (fun x => sin (f x)) μ
  证明: measurable_sin.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.csin : AEMeasurable (fun x => sin (f x)) μ :=
  measurable_sin.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.ccosh` / 引理 `AEMeasurable.ccosh`

English:
lemma AEMeasurable.ccosh
  statement: AEMeasurable (fun x => cosh (f x)) μ
  proof: measurable_cosh.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.ccosh
  结论: 几乎处处可测 (fun x => cosh (f x)) μ
  证明: measurable_cosh.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.ccosh : AEMeasurable (fun x => cosh (f x)) μ :=
  measurable_cosh.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.csinh` / 引理 `AEMeasurable.csinh`

English:
lemma AEMeasurable.csinh
  statement: AEMeasurable (fun x => sinh (f x)) μ
  proof: measurable_sinh.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.csinh
  结论: 几乎处处可测 (fun x => sinh (f x)) μ
  证明: measurable_sinh.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.csinh : AEMeasurable (fun x => sinh (f x)) μ :=
  measurable_sinh.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.carg` / 引理 `AEMeasurable.carg`

English:
lemma AEMeasurable.carg
  statement: AEMeasurable (fun x => arg (f x)) μ
  proof: measurable_arg.comp_aemeasurable hf

@[fun_prop]

中文:
引理 几乎处处可测.carg
  结论: 几乎处处可测 (fun x => arg (f x)) μ
  证明: measurable_arg.comp_aemeasurable hf

@[fun_prop]
-/
protected lemma AEMeasurable.carg : AEMeasurable (fun x => arg (f x)) μ :=
  measurable_arg.comp_aemeasurable hf

@[fun_prop]
/--
lemma `AEMeasurable.clog` / 引理 `AEMeasurable.clog`

English:
lemma AEMeasurable.clog
  statement: AEMeasurable (fun x => log (f x)) μ
  proof: measurable_log.comp_aemeasurable hf

中文:
引理 几乎处处可测.clog
  结论: 几乎处处可测 (fun x => log (f x)) μ
  证明: measurable_log.comp_aemeasurable hf
-/
protected lemma AEMeasurable.clog : AEMeasurable (fun x => log (f x)) μ :=
  measurable_log.comp_aemeasurable hf

end ComplexComposition

@[fun_prop]
/--
theorem `Measurable.complex_ofReal` / 定理 `Measurable.complex_ofReal`

English:
theorem Measurable.complex_ofReal
  statement: {α : Type*} {m : MeasurableSpace α} {f : α -> Real}
  proof: by fun_prop

@[fun_prop]

中文:
定理 可测.complex_of实数
  结论: {α : 类型} {m : 可测空间 α} {f : α -> 实数}
  证明: by fun_prop

@[fun_prop]
-/
protected theorem Measurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {f : α -> Real}
    (hf : Measurable f) :
    Measurable fun x => (f x : Complex) := by fun_prop

@[fun_prop]
/--
theorem `AEMeasurable.complex_ofReal` / 定理 `AEMeasurable.complex_ofReal`

English:
theorem AEMeasurable.complex_ofReal
  statement: {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  proof: by
  fun_prop

中文:
定理 几乎处处可测.complex_of实数
  结论: {α : 类型} {m : 可测空间 α} {μ : 测度 α}
  证明: by
  fun_prop
-/
protected theorem AEMeasurable.complex_ofReal {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α -> Real} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : Complex)) μ := by
  fun_prop

section PowInstances

/--
Instance `Complex.hasMeasurablePow` / 实例 `Complex.hasMeasurablePow`

English:
instance Complex.hasMeasurablePow
  signature: : MeasurablePow Complex Complex
  body: ⟨Measurable.ite (by measurability)
    (Measurable.ite (by measurability) measurable_one measurable_zero) (by fun_prop)⟩

中文:
实例 复形.hasMeasurablePow
  签名: : MeasurablePow 复形 复形
  定义体: ⟨Measurable.ite (by measurability)
    (Measurable.ite (by measurability) measurable_one measurable_zero) (by fun_prop)⟩

Depends on / 依赖: Measurable, Measurable.ite, fun_prop, measurability, measurable_one, measurable_zero
-/
instance Complex.hasMeasurablePow : MeasurablePow Complex Complex :=
  ⟨Measurable.ite (by measurability)
    (Measurable.ite (by measurability) measurable_one measurable_zero) (by fun_prop)⟩

/--
Instance `Real.hasMeasurablePow` / 实例 `Real.hasMeasurablePow`

English:
instance Real.hasMeasurablePow
  signature: : MeasurablePow Real Real
  body: ⟨Complex.measurable_re.comp by fun_prop⟩

中文:
实例 实数.hasMeasurablePow
  签名: : MeasurablePow 实数 实数
  定义体: ⟨Complex.measurable_re.comp by fun_prop⟩

Depends on / 依赖: Complex.measurable_re.comp, fun_prop, measurable_re
-/
instance Real.hasMeasurablePow : MeasurablePow Real Real := ⟨Complex.measurable_re.comp by fun_prop⟩

/--
Instance `NNReal.hasMeasurablePow` / 实例 `NNReal.hasMeasurablePow`

English:
instance NNReal.hasMeasurablePow
  signature: : MeasurablePow Real>=0 Real
  body: ⟨Measurable.subtype_mk (by fun_prop)⟩

中文:
实例 非负实数.hasMeasurablePow
  签名: : MeasurablePow 实数>=0 实数
  定义体: ⟨Measurable.subtype_mk (by fun_prop)⟩

Depends on / 依赖: Measurable, Measurable.subtype_mk, fun_prop, subtype_mk
-/
instance NNReal.hasMeasurablePow : MeasurablePow Real>=0 Real := ⟨Measurable.subtype_mk (by fun_prop)⟩

/--
Instance `ENNReal.hasMeasurablePow` / 实例 `ENNReal.hasMeasurablePow`

English:
instance ENNReal.hasMeasurablePow
  signature: : MeasurablePow Real>=0∞ Real
  body: by
  refine ⟨ENNReal.measurable_of_measurable_nnreal_prod ?_ ?_⟩
  · simp_rw [ENNReal.coe_rpow_def]
    exact Measurable.ite (by measurability) measurable_const (by fun_prop)
  · simp_rw [ENNReal.top_rpow_def]
    refine Measurable.ite measurableSet_Ioi measurable_const ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

中文:
实例 广义非负实数.hasMeasurablePow
  签名: : MeasurablePow 实数>=0∞ 实数
  定义体: by
  refine ⟨ENNReal.measurable_of_measurable_nnreal_prod ?_ ?_⟩
  · simp_rw [ENNReal.coe_rpow_def]
    exact Measurable.ite (by measurability) measurable_const (by fun_prop)
  · simp_rw [ENNReal.top_rpow_def]
    refine Measurable.ite measurableSet_Ioi measurable_const ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

Depends on / 依赖: ENNReal, ENNReal.coe_rpow_def, ENNReal.measurable_of_measurable_nnreal_prod, ENNReal.top_rpow_def, Measurable, Measurable.ite, coe_rpow_def, fun_prop, measurability, measurableSet_Ioi, measurableSet_singleton, measurable_const, measurable_of_measurable_nnreal_prod, simp_rw, top_rpow_def
-/
instance ENNReal.hasMeasurablePow : MeasurablePow Real>=0∞ Real := by
  refine ⟨ENNReal.measurable_of_measurable_nnreal_prod ?_ ?_⟩
  · simp_rw [ENNReal.coe_rpow_def]
    exact Measurable.ite (by measurability) measurable_const (by fun_prop)
  · simp_rw [ENNReal.top_rpow_def]
    refine Measurable.ite measurableSet_Ioi measurable_const ?_
    exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

end PowInstances
