/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Complex and real exponential

In this file we prove that `Complex.exp` and `Real.exp` are analytic functions.

## Tags

exp, derivative
-/

public section

assert_not_exists IsConformalMap Conformal

noncomputable section

open Filter Asymptotics Set Function
open scoped Topology

/-! ## `Complex.exp` -/

section

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {f g : E -> Complex} {z : Complex} {x : E} {s : Set E}

/--
theorem `analyticOnNhd_cexp` / 定理 `analyticOnNhd_cexp`

English:
theorem analyticOnNhd_cexp
  statement: AnalyticOnNhd Complex exp univ
  proof: by
  rw [Complex.exp_eq_exp_Complex]
  exact fun x _ => NormedSpace.exp_analytic x

中文:
定理 analyticOnNhd_cexp
  结论: AnalyticOnNhd 复形 exp univ
  证明: by
  rw [Complex.exp_eq_exp_Complex]
  exact fun x _ => NormedSpace.exp_analytic x

Depends on / 依赖: Complex.exp_eq_exp_Complex, NormedSpace, NormedSpace.exp_analytic, exp_analytic, exp_eq_exp_Complex
-/
theorem analyticOnNhd_cexp : AnalyticOnNhd Complex exp univ := by
  rw [Complex.exp_eq_exp_Complex]
  exact fun x _ => NormedSpace.exp_analytic x

/--
theorem `analyticOn_cexp` / 定理 `analyticOn_cexp`

English:
theorem analyticOn_cexp
  statement: AnalyticOn Complex exp univ
  proof: analyticOnNhd_cexp.analyticOn

中文:
定理 analyticOn_cexp
  结论: AnalyticOn 复形 exp univ
  证明: analyticOnNhd_cexp.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_cexp, analyticOnNhd_cexp.analyticOn
-/
theorem analyticOn_cexp : AnalyticOn Complex exp univ := analyticOnNhd_cexp.analyticOn

/-- The function `Complex.exp` is complex analytic. -/
@[fun_prop]
/--
theorem `analyticAt_cexp` / 定理 `analyticAt_cexp`

English:
theorem analyticAt_cexp
  statement: AnalyticAt Complex exp z
  proof: analyticOnNhd_cexp z (mem_univ _)

中文:
定理 analyticAt_cexp
  结论: AnalyticAt 复形 exp z
  证明: analyticOnNhd_cexp z (mem_univ _)

Depends on / 依赖: analyticOnNhd_cexp, mem_univ
-/
theorem analyticAt_cexp : AnalyticAt Complex exp z :=
  analyticOnNhd_cexp z (mem_univ _)

/--
lemma `analyticWithinAt_cexp` / 引理 `analyticWithinAt_cexp`

English:
lemma analyticWithinAt_cexp
  given: {s : Set Complex} {x : Complex}
  proof: by
  exact analyticAt_cexp.analyticWithinAt

中文:
引理 analyticWithinAt_cexp
  条件: {s : 集合 复形} {x : 复形}
  证明: by
  exact analyticAt_cexp.analyticWithinAt

Depends on / 依赖: analyticAt_cexp, analyticAt_cexp.analyticWithinAt, analyticWithinAt
-/
lemma analyticWithinAt_cexp {s : Set Complex} {x : Complex} :
    AnalyticWithinAt Complex Complex.exp s x := by
  exact analyticAt_cexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/--
theorem `AnalyticAt.cexp` / 定理 `AnalyticAt.cexp`

English:
theorem AnalyticAt.cexp
  given: (fa : AnalyticAt Complex f x)
  statement: AnalyticAt Complex (exp ∘ f) x
  proof: analyticAt_cexp.comp fa

中文:
定理 AnalyticAt.cexp
  条件: (fa : AnalyticAt 复形 f x)
  结论: AnalyticAt 复形 (exp ∘ f) x
  证明: analyticAt_cexp.comp fa

Depends on / 依赖: analyticAt_cexp, analyticAt_cexp.comp
-/
theorem AnalyticAt.cexp (fa : AnalyticAt Complex f x) : AnalyticAt Complex (exp ∘ f) x :=
  analyticAt_cexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/--
theorem `AnalyticAt.cexp'` / 定理 `AnalyticAt.cexp'`

English:
theorem AnalyticAt.cexp'
  given: (fa : AnalyticAt Complex f x)
  statement: AnalyticAt Complex (fun z => exp (f z)) x
  proof: fa.cexp

中文:
定理 AnalyticAt.cexp'
  条件: (fa : AnalyticAt 复形 f x)
  结论: AnalyticAt 复形 (fun z => exp (f z)) x
  证明: fa.cexp

Depends on / 依赖: fa.cexp
-/
theorem AnalyticAt.cexp' (fa : AnalyticAt Complex f x) : AnalyticAt Complex (fun z => exp (f z)) x :=
  fa.cexp

/--
theorem `AnalyticWithinAt.cexp` / 定理 `AnalyticWithinAt.cexp`

English:
theorem AnalyticWithinAt.cexp
  given: (fa : AnalyticWithinAt Complex f s x)
  proof: analyticAt_cexp.comp_analyticWithinAt fa

中文:
定理 AnalyticWithinAt.cexp
  条件: (fa : AnalyticWithinAt 复形 f s x)
  证明: analyticAt_cexp.comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_cexp, analyticAt_cexp.comp_analyticWithinAt, comp_analyticWithinAt
-/
theorem AnalyticWithinAt.cexp (fa : AnalyticWithinAt Complex f s x) :
    AnalyticWithinAt Complex (fun z => exp (f z)) s x :=
  analyticAt_cexp.comp_analyticWithinAt fa

/--
theorem `AnalyticOnNhd.cexp` / 定理 `AnalyticOnNhd.cexp`

English:
theorem AnalyticOnNhd.cexp
  given: (fs : AnalyticOnNhd Complex f s)
  statement: AnalyticOnNhd Complex (fun z => exp (f z)) s
  proof: fun z n => analyticAt_cexp.comp (fs z n)

中文:
定理 AnalyticOnNhd.cexp
  条件: (fs : AnalyticOnNhd 复形 f s)
  结论: AnalyticOnNhd 复形 (fun z => exp (f z)) s
  证明: fun z n => analyticAt_cexp.comp (fs z n)

Depends on / 依赖: analyticAt_cexp, analyticAt_cexp.comp
-/
theorem AnalyticOnNhd.cexp (fs : AnalyticOnNhd Complex f s) : AnalyticOnNhd Complex (fun z => exp (f z)) s :=
  fun z n => analyticAt_cexp.comp (fs z n)

/--
theorem `AnalyticOn.cexp` / 定理 `AnalyticOn.cexp`

English:
theorem AnalyticOn.cexp
  given: (fs : AnalyticOn Complex f s)
  statement: AnalyticOn Complex (fun z => exp (f z)) s
  proof: analyticOnNhd_cexp.comp_analyticOn fs (mapsTo_univ _ _)

中文:
定理 AnalyticOn.cexp
  条件: (fs : AnalyticOn 复形 f s)
  结论: AnalyticOn 复形 (fun z => exp (f z)) s
  证明: analyticOnNhd_cexp.comp_analyticOn fs (mapsTo_univ _ _)

Depends on / 依赖: analyticOnNhd_cexp, analyticOnNhd_cexp.comp_analyticOn, comp_analyticOn, mapsTo_univ
-/
theorem AnalyticOn.cexp (fs : AnalyticOn Complex f s) : AnalyticOn Complex (fun z => exp (f z)) s :=
  analyticOnNhd_cexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Complex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 Complex]

/--
theorem `hasDerivAt_exp` / 定理 `hasDerivAt_exp`

English:
theorem hasDerivAt_exp
  given: (x : Complex)
  statement: HasDerivAt exp (exp x) x
  proof: by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : Nat) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : Complex) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => 

中文:
定理 hasDerivAt_exp
  条件: (x : 复形)
  结论: 在点处可导 exp (exp x) x
  证明: by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : Nat) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : Complex) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => 

Depends on / 依赖: Action, Action.functorCategoryEquivalence, HasLimit, IsBigO, IsBigO.of_bound, Metric, Metric.ball_mem_nhds, Metric.mem_ball, PreservesLimit, SingleObj, SingleObj.star, ball_mem_nhds, dist_zero_right, evaluation, exp_bound_sq, filter_upwards, flip.obj, forget, functor, functorCategoryEquivalence
-/
theorem hasDerivAt_exp (x : Complex) : HasDerivAt exp (exp x) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have : (1 : Nat) < 2 := by simp
  refine (IsBigO.of_bound ‖exp x‖ ?_).trans_isLittleO (isLittleO_pow_id this)
  filter_upwards [Metric.ball_mem_nhds (0 : Complex) zero_lt_one]
  simp only [Metric.mem_ball, dist_zero_right, norm_pow]
  exact fun z hz => exp_bound_sq x z hz.le

@[simp]
/--
theorem `differentiable_exp` / 定理 `differentiable_exp`

English:
theorem differentiable_exp
  statement: Differentiable 𝕜 exp
  proof: fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

@[simp]

中文:
定理 differentiable_exp
  结论: 可微 𝕜 exp
  证明: fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

@[simp]

Depends on / 依赖: Action, Action.functorCategoryEquivalence, HasColimit, PreservesColimit, SingleObj, SingleObj.star, evaluation, flip.obj, forget, functor, functorCategoryEquivalence, infer_instance
-/
theorem differentiable_exp : Differentiable 𝕜 exp := fun x =>
  (hasDerivAt_exp x).differentiableAt.restrictScalars 𝕜

@[simp]
/--
theorem `differentiableAt_exp` / 定理 `differentiableAt_exp`

English:
theorem differentiableAt_exp
  given: {x : Complex}
  statement: DifferentiableAt 𝕜 exp x
  proof: differentiable_exp x

@[simp]

中文:
定理 differentiableAt_exp
  条件: {x : 复形}
  结论: DifferentiableAt 𝕜 exp x
  证明: differentiable_exp x

@[simp]

Depends on / 依赖: differentiable_exp
-/
theorem differentiableAt_exp {x : Complex} : DifferentiableAt 𝕜 exp x :=
  differentiable_exp x

@[simp]
/--
theorem `deriv_exp` / 定理 `deriv_exp`

English:
theorem deriv_exp
  statement: deriv exp = exp
  proof: funext fun x => (hasDerivAt_exp x).deriv

@[simp]

中文:
定理 deriv_exp
  结论: deriv exp = exp
  证明: funext fun x => (hasDerivAt_exp x).deriv

@[simp]

Depends on / 依赖: hasDerivAt_exp
-/
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
/--
theorem `iter_deriv_exp` / 定理 `iter_deriv_exp`

English:
theorem iter_deriv_exp
  statement: forall n : Nat, deriv^[n] exp = exp

中文:
定理 iter_deriv_exp
  结论: 对任意 n : 自然数, deriv^[n] exp = exp

Depends on / 依赖: Action, Action.functorCategoryEquivalence, evaluationJointlyReflectsLimits, functor, functorCategoryEquivalence, isLimitOfReflects
-/
theorem iter_deriv_exp : forall n : Nat, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

@[fun_prop]
/--
theorem `contDiff_exp` / 定理 `contDiff_exp`

English:
theorem contDiff_exp
  given: {n : WithTop Nat∞}
  statement: ContDiff 𝕜 n exp
  proof: analyticOnNhd_cexp.restrictScalars.contDiff

中文:
定理 contDiff_exp
  条件: {n : WithTop 自然数∞}
  结论: 连续可微 𝕜 n exp
  证明: analyticOnNhd_cexp.restrictScalars.contDiff

Depends on / 依赖: Action, Action.functorCategoryEquivalence, analyticOnNhd_cexp, analyticOnNhd_cexp.restrictScalars.contDiff, contDiff, evaluationJointlyReflectsColimits, functor, functorCategoryEquivalence, isColimitOfReflects, restrictScalars
-/
theorem contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp :=
  analyticOnNhd_cexp.restrictScalars.contDiff

/--
theorem `hasStrictDerivAt_exp` / 定理 `hasStrictDerivAt_exp`

English:
theorem hasStrictDerivAt_exp
  given: (x : Complex)
  statement: HasStrictDerivAt exp (exp x) x
  proof: contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) one_ne_zero

中文:
定理 hasStrictDerivAt_exp
  条件: (x : 复形)
  结论: HasStrictDerivAt exp (exp x) x
  证明: contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) one_ne_zero

Depends on / 依赖: contDiffAt, contDiff_exp, contDiff_exp.contDiffAt.hasStrictDerivAt, hasDerivAt_exp, hasStrictDerivAt, one_ne_zero
-/
theorem hasStrictDerivAt_exp (x : Complex) : HasStrictDerivAt exp (exp x) x :=
  contDiff_exp.contDiffAt.hasStrictDerivAt' (hasDerivAt_exp x) one_ne_zero

/--
theorem `hasStrictFDerivAt_exp_real` / 定理 `hasStrictFDerivAt_exp_real`

English:
theorem hasStrictFDerivAt_exp_real
  given: (x : Complex)
  statement: HasStrictFDerivAt exp (exp x • (1 : Complex ->L[Real] Complex)) x
  proof: (hasStrictDerivAt_exp x).complexToReal_fderiv

中文:
定理 hasStrictFDerivAt_exp_real
  条件: (x : 复形)
  结论: HasStrictFDerivAt exp (exp x • (1 : 复形 ->L[实数] 复形)) x
  证明: (hasStrictDerivAt_exp x).complexToReal_fderiv

Depends on / 依赖: complexToReal_fderiv, hasStrictDerivAt_exp
-/
theorem hasStrictFDerivAt_exp_real (x : Complex) : HasStrictFDerivAt exp (exp x • (1 : Complex ->L[Real] Complex)) x :=
  (hasStrictDerivAt_exp x).complexToReal_fderiv

end Complex

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 Complex] {f : 𝕜 -> Complex} {f' : Complex} {x : 𝕜}
  {s : Set 𝕜}

/--
theorem `HasStrictDerivAt.cexp` / 定理 `HasStrictDerivAt.cexp`

English:
theorem HasStrictDerivAt.cexp
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_exp (f x)).comp x hf

中文:
定理 HasStrictDerivAt.cexp
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_exp (f x)).comp x hf

Depends on / 依赖: Complex.hasStrictDerivAt_exp, hasStrictDerivAt_exp
-/
theorem HasStrictDerivAt.cexp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp x hf

/--
theorem `HasDerivAt.cexp` / 定理 `HasDerivAt.cexp`

English:
theorem HasDerivAt.cexp
  given: (hf : HasDerivAt f f' x)
  proof: (Complex.hasDerivAt_exp (f x)).comp x hf

中文:
定理 在点处可导.cexp
  条件: (hf : 在点处可导 f f' x)
  证明: (Complex.hasDerivAt_exp (f x)).comp x hf

Depends on / 依赖: Complex.hasDerivAt_exp, hasDerivAt_exp
-/
theorem HasDerivAt.cexp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') x :=
  (Complex.hasDerivAt_exp (f x)).comp x hf

/--
theorem `HasDerivWithinAt.cexp` / 定理 `HasDerivWithinAt.cexp`

English:
theorem HasDerivWithinAt.cexp
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.cexp
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_exp, comp_hasDerivWithinAt, hasDerivAt_exp
-/
theorem HasDerivWithinAt.cexp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) * f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_cexp` / 定理 `derivWithin_cexp`

English:
theorem derivWithin_cexp
  given: (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x)
  proof: hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]

中文:
定理 derivWithin_cexp
  条件: (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x)
  证明: hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.cexp.derivWithin
-/
theorem derivWithin_cexp (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    derivWithin (fun x => Complex.exp (f x)) s x = Complex.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.cexp.derivWithin hxs

@[simp]
/--
theorem `deriv_cexp` / 定理 `deriv_cexp`

English:
theorem deriv_cexp
  given: (hc : DifferentiableAt 𝕜 f x)
  proof: hc.hasDerivAt.cexp.deriv

中文:
定理 deriv_cexp
  条件: (hc : DifferentiableAt 𝕜 f x)
  证明: hc.hasDerivAt.cexp.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.cexp.deriv
-/
theorem deriv_cexp (hc : DifferentiableAt 𝕜 f x) :
    deriv (fun x => Complex.exp (f x)) x = Complex.exp (f x) * deriv f x :=
  hc.hasDerivAt.cexp.deriv

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 Complex] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E -> Complex} {f' : E ->L[𝕜] Complex} {x : E} {s : Set E}

/--
theorem `HasStrictFDerivAt.cexp` / 定理 `HasStrictFDerivAt.cexp`

English:
theorem HasStrictFDerivAt.cexp
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.cexp
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Complex.hasStrictDerivAt_exp, comp_hasStrictFDerivAt, hasStrictDerivAt_exp
-/
theorem HasStrictFDerivAt.cexp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
  (Complex.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `HasFDerivWithinAt.cexp` / 定理 `HasFDerivWithinAt.cexp`

English:
theorem HasFDerivWithinAt.cexp
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.cexp
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Complex.hasDerivAt_exp, comp_hasFDerivWithinAt, hasDerivAt_exp
-/
theorem HasFDerivWithinAt.cexp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') s x :=
  (Complex.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `HasFDerivAt.cexp` / 定理 `HasFDerivAt.cexp`

English:
theorem HasFDerivAt.cexp
  given: (hf : HasFDerivAt f f' x)
  proof: hasFDerivWithinAt_univ.1 hf.hasFDerivWithinAt.cexp

中文:
定理 在点处Fréchet可导.cexp
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: hasFDerivWithinAt_univ.1 hf.hasFDerivWithinAt.cexp

Depends on / 依赖: hasFDerivWithinAt, hasFDerivWithinAt_univ, hf.hasFDerivWithinAt.cexp
-/
theorem HasFDerivAt.cexp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Complex.exp (f x)) (Complex.exp (f x) • f') x :=
hasFDerivWithinAt_univ.1 hf.hasFDerivWithinAt.cexp

/--
theorem `DifferentiableWithinAt.cexp` / 定理 `DifferentiableWithinAt.cexp`

English:
theorem DifferentiableWithinAt.cexp
  given: (hf : DifferentiableWithinAt 𝕜 f s x)
  proof: hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.cexp
  条件: (hf : DifferentiableWithinAt 𝕜 f s x)
  证明: hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.cexp.differentiableWithinAt
-/
theorem DifferentiableWithinAt.cexp (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun x => Complex.exp (f x)) s x :=
  hf.hasFDerivWithinAt.cexp.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.cexp` / 定理 `DifferentiableAt.cexp`

English:
theorem DifferentiableAt.cexp
  given: (hc : DifferentiableAt 𝕜 f x)
  proof: hc.hasFDerivAt.cexp.differentiableAt

中文:
定理 DifferentiableAt.cexp
  条件: (hc : DifferentiableAt 𝕜 f x)
  证明: hc.hasFDerivAt.cexp.differentiableAt

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.cexp.differentiableAt
-/
theorem DifferentiableAt.cexp (hc : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun x => Complex.exp (f x)) x :=
  hc.hasFDerivAt.cexp.differentiableAt

/--
theorem `DifferentiableOn.cexp` / 定理 `DifferentiableOn.cexp`

English:
theorem DifferentiableOn.cexp
  given: (hc : DifferentiableOn 𝕜 f s)
  proof: fun x h => (hc x h).cexp

@[simp, fun_prop]

中文:
定理 DifferentiableOn.cexp
  条件: (hc : DifferentiableOn 𝕜 f s)
  证明: fun x h => (hc x h).cexp

@[simp, fun_prop]
-/
theorem DifferentiableOn.cexp (hc : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun x => Complex.exp (f x)) s := fun x h => (hc x h).cexp

@[simp, fun_prop]
/--
theorem `Differentiable.cexp` / 定理 `Differentiable.cexp`

English:
theorem Differentiable.cexp
  given: (hc : Differentiable 𝕜 f)
  proof: fun x => (hc x).cexp

@[fun_prop]

中文:
定理 可微.cexp
  条件: (hc : 可微 𝕜 f)
  证明: fun x => (hc x).cexp

@[fun_prop]
-/
theorem Differentiable.cexp (hc : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun x => Complex.exp (f x) := fun x => (hc x).cexp

@[fun_prop]
/--
theorem `ContDiff.cexp` / 定理 `ContDiff.cexp`

English:
theorem ContDiff.cexp
  given: {n} (h : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x => Complex.exp (f x)
  proof: Complex.contDiff_exp.comp h

@[fun_prop]

中文:
定理 连续可微.cexp
  条件: {n} (h : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x => 复形.exp (f x)
  证明: Complex.contDiff_exp.comp h

@[fun_prop]

Depends on / 依赖: Complex.contDiff_exp.comp, contDiff_exp
-/
theorem ContDiff.cexp {n} (h : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => Complex.exp (f x) :=
  Complex.contDiff_exp.comp h

@[fun_prop]
/--
theorem `ContDiffAt.cexp` / 定理 `ContDiffAt.cexp`

English:
theorem ContDiffAt.cexp
  given: {n} (hf : ContDiffAt 𝕜 n f x)
  proof: Complex.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]

中文:
定理 ContDiffAt.cexp
  条件: {n} (hf : ContDiffAt 𝕜 n f x)
  证明: Complex.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]

Depends on / 依赖: Complex.contDiff_exp.contDiffAt.comp, contDiffAt, contDiff_exp
-/
theorem ContDiffAt.cexp {n} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => Complex.exp (f x)) x :=
  Complex.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
/--
theorem `ContDiffOn.cexp` / 定理 `ContDiffOn.cexp`

English:
theorem ContDiffOn.cexp
  given: {n} (hf : ContDiffOn 𝕜 n f s)
  proof: Complex.contDiff_exp.comp_contDiffOn hf

@[fun_prop]

中文:
定理 ContDiffOn.cexp
  条件: {n} (hf : ContDiffOn 𝕜 n f s)
  证明: Complex.contDiff_exp.comp_contDiffOn hf

@[fun_prop]

Depends on / 依赖: Complex.contDiff_exp.comp_contDiffOn, comp_contDiffOn, contDiff_exp
-/
theorem ContDiffOn.cexp {n} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => Complex.exp (f x)) s :=
  Complex.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.cexp` / 定理 `ContDiffWithinAt.cexp`

English:
theorem ContDiffWithinAt.cexp
  given: {n} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.cexp
  条件: {n} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_exp
-/
theorem ContDiffWithinAt.cexp {n} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => Complex.exp (f x)) s x :=
  Complex.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

end

open Complex in
@[simp]
/--
theorem `iteratedDeriv_cexp_const_mul` / 定理 `iteratedDeriv_cexp_const_mul`

English:
theorem iteratedDeriv_cexp_const_mul
  given: (n : Nat) (c : Complex)
  proof: by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]

中文:
定理 iteratedDeriv_cexp_const_mul
  条件: (n : 自然数) (c : 复形)
  证明: by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]

Depends on / 依赖: contDiff_exp, iter_deriv_exp, iteratedDeriv_comp_const_mul, iteratedDeriv_eq_iterate
-/
theorem iteratedDeriv_cexp_const_mul (n : Nat) (c : Complex) :
    (iteratedDeriv n fun s : Complex => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]

/-! ## `Real.exp` -/

section

open Real

variable {x : Real} {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {s : Set E}

/--
theorem `analyticOnNhd_rexp` / 定理 `analyticOnNhd_rexp`

English:
theorem analyticOnNhd_rexp
  statement: AnalyticOnNhd Real exp univ
  proof: by
  rw [Real.exp_eq_exp_Real]
  exact fun x _ => NormedSpace.exp_analytic x

中文:
定理 analyticOnNhd_rexp
  结论: AnalyticOnNhd 实数 exp univ
  证明: by
  rw [Real.exp_eq_exp_Real]
  exact fun x _ => NormedSpace.exp_analytic x

Depends on / 依赖: NormedSpace, NormedSpace.exp_analytic, Real.exp_eq_exp_Real, exp_analytic, exp_eq_exp_Real
-/
theorem analyticOnNhd_rexp : AnalyticOnNhd Real exp univ := by
  rw [Real.exp_eq_exp_Real]
  exact fun x _ => NormedSpace.exp_analytic x

/--
theorem `analyticOn_rexp` / 定理 `analyticOn_rexp`

English:
theorem analyticOn_rexp
  statement: AnalyticOn Real exp univ
  proof: analyticOnNhd_rexp.analyticOn

中文:
定理 analyticOn_rexp
  结论: AnalyticOn 实数 exp univ
  证明: analyticOnNhd_rexp.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_rexp, analyticOnNhd_rexp.analyticOn
-/
theorem analyticOn_rexp : AnalyticOn Real exp univ := analyticOnNhd_rexp.analyticOn

/-- The function `Real.exp` is real analytic. -/
@[fun_prop]
/--
theorem `analyticAt_rexp` / 定理 `analyticAt_rexp`

English:
theorem analyticAt_rexp
  statement: AnalyticAt Real exp x
  proof: analyticOnNhd_rexp x (mem_univ _)

中文:
定理 analyticAt_rexp
  结论: AnalyticAt 实数 exp x
  证明: analyticOnNhd_rexp x (mem_univ _)

Depends on / 依赖: analyticOnNhd_rexp, mem_univ
-/
theorem analyticAt_rexp : AnalyticAt Real exp x :=
  analyticOnNhd_rexp x (mem_univ _)

/--
lemma `analyticWithinAt_rexp` / 引理 `analyticWithinAt_rexp`

English:
lemma analyticWithinAt_rexp
  given: {s : Set Real}
  statement: AnalyticWithinAt Real Real.exp s x
  proof: analyticAt_rexp.analyticWithinAt

中文:
引理 analyticWithinAt_rexp
  条件: {s : 集合 实数}
  结论: AnalyticWithinAt 实数 实数.exp s x
  证明: analyticAt_rexp.analyticWithinAt

Depends on / 依赖: analyticAt_rexp, analyticAt_rexp.analyticWithinAt, analyticWithinAt
-/
lemma analyticWithinAt_rexp {s : Set Real} : AnalyticWithinAt Real Real.exp s x :=
  analyticAt_rexp.analyticWithinAt

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/--
theorem `AnalyticAt.rexp` / 定理 `AnalyticAt.rexp`

English:
theorem AnalyticAt.rexp
  given: {x : E} (fa : AnalyticAt Real f x)
  statement: AnalyticAt Real (exp ∘ f) x
  proof: analyticAt_rexp.comp fa

中文:
定理 AnalyticAt.rexp
  条件: {x : E} (fa : AnalyticAt 实数 f x)
  结论: AnalyticAt 实数 (exp ∘ f) x
  证明: analyticAt_rexp.comp fa

Depends on / 依赖: analyticAt_rexp, analyticAt_rexp.comp
-/
theorem AnalyticAt.rexp {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (exp ∘ f) x :=
  analyticAt_rexp.comp fa

/-- `exp ∘ f` is analytic -/
@[fun_prop]
/--
theorem `AnalyticAt.rexp'` / 定理 `AnalyticAt.rexp'`

English:
theorem AnalyticAt.rexp'
  given: {x : E} (fa : AnalyticAt Real f x)
  statement: AnalyticAt Real (fun z => exp (f z)) x
  proof: fa.rexp

中文:
定理 AnalyticAt.rexp'
  条件: {x : E} (fa : AnalyticAt 实数 f x)
  结论: AnalyticAt 实数 (fun z => exp (f z)) x
  证明: fa.rexp

Depends on / 依赖: fa.rexp
-/
theorem AnalyticAt.rexp' {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (fun z => exp (f z)) x :=
  fa.rexp

/--
theorem `AnalyticWithinAt.rexp` / 定理 `AnalyticWithinAt.rexp`

English:
theorem AnalyticWithinAt.rexp
  given: {x : E} (fa : AnalyticWithinAt Real f s x)
  proof: analyticAt_rexp.comp_analyticWithinAt fa

中文:
定理 AnalyticWithinAt.rexp
  条件: {x : E} (fa : AnalyticWithinAt 实数 f s x)
  证明: analyticAt_rexp.comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_rexp, analyticAt_rexp.comp_analyticWithinAt, comp_analyticWithinAt
-/
theorem AnalyticWithinAt.rexp {x : E} (fa : AnalyticWithinAt Real f s x) :
    AnalyticWithinAt Real (fun z => exp (f z)) s x :=
  analyticAt_rexp.comp_analyticWithinAt fa

/--
theorem `AnalyticOnNhd.rexp` / 定理 `AnalyticOnNhd.rexp`

English:
theorem AnalyticOnNhd.rexp
  given: {s : Set E} (fs : AnalyticOnNhd Real f s)
  proof: fun z n => analyticAt_rexp.comp (fs z n)

中文:
定理 AnalyticOnNhd.rexp
  条件: {s : 集合 E} (fs : AnalyticOnNhd 实数 f s)
  证明: fun z n => analyticAt_rexp.comp (fs z n)

Depends on / 依赖: analyticAt_rexp, analyticAt_rexp.comp
-/
theorem AnalyticOnNhd.rexp {s : Set E} (fs : AnalyticOnNhd Real f s) :
    AnalyticOnNhd Real (fun z => exp (f z)) s :=
  fun z n => analyticAt_rexp.comp (fs z n)

/--
theorem `AnalyticOn.rexp` / 定理 `AnalyticOn.rexp`

English:
theorem AnalyticOn.rexp
  given: (fs : AnalyticOn Real f s)
  statement: AnalyticOn Real (fun z => exp (f z)) s
  proof: analyticOnNhd_rexp.comp_analyticOn fs (mapsTo_univ _ _)

中文:
定理 AnalyticOn.rexp
  条件: (fs : AnalyticOn 实数 f s)
  结论: AnalyticOn 实数 (fun z => exp (f z)) s
  证明: analyticOnNhd_rexp.comp_analyticOn fs (mapsTo_univ _ _)

Depends on / 依赖: analyticOnNhd_rexp, analyticOnNhd_rexp.comp_analyticOn, comp_analyticOn, mapsTo_univ
-/
theorem AnalyticOn.rexp (fs : AnalyticOn Real f s) : AnalyticOn Real (fun z => exp (f z)) s :=
  analyticOnNhd_rexp.comp_analyticOn fs (mapsTo_univ _ _)

end

namespace Real

/--
theorem `hasStrictDerivAt_exp` / 定理 `hasStrictDerivAt_exp`

English:
theorem hasStrictDerivAt_exp
  given: (x : Real)
  statement: HasStrictDerivAt exp (exp x) x
  proof: (Complex.hasStrictDerivAt_exp x).real_of_complex

中文:
定理 hasStrictDerivAt_exp
  条件: (x : 实数)
  结论: HasStrictDerivAt exp (exp x) x
  证明: (Complex.hasStrictDerivAt_exp x).real_of_complex

Depends on / 依赖: Complex.hasStrictDerivAt_exp, hasStrictDerivAt_exp, real_of_complex
-/
theorem hasStrictDerivAt_exp (x : Real) : HasStrictDerivAt exp (exp x) x :=
  (Complex.hasStrictDerivAt_exp x).real_of_complex

/--
theorem `hasDerivAt_exp` / 定理 `hasDerivAt_exp`

English:
theorem hasDerivAt_exp
  given: (x : Real)
  statement: HasDerivAt exp (exp x) x
  proof: (Complex.hasDerivAt_exp x).real_of_complex

@[fun_prop]

中文:
定理 hasDerivAt_exp
  条件: (x : 实数)
  结论: 在点处可导 exp (exp x) x
  证明: (Complex.hasDerivAt_exp x).real_of_complex

@[fun_prop]

Depends on / 依赖: Complex.hasDerivAt_exp, hasDerivAt_exp, real_of_complex
-/
theorem hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) x :=
  (Complex.hasDerivAt_exp x).real_of_complex

@[fun_prop]
/--
theorem `contDiff_exp` / 定理 `contDiff_exp`

English:
theorem contDiff_exp
  given: {n : WithTop Nat∞}
  statement: ContDiff Real n exp
  proof: Complex.contDiff_exp.real_of_complex

@[simp]

中文:
定理 contDiff_exp
  条件: {n : WithTop 自然数∞}
  结论: 连续可微 实数 n exp
  证明: Complex.contDiff_exp.real_of_complex

@[simp]

Depends on / 依赖: Complex.contDiff_exp.real_of_complex, contDiff_exp, real_of_complex
-/
theorem contDiff_exp {n : WithTop Nat∞} : ContDiff Real n exp :=
  Complex.contDiff_exp.real_of_complex

@[simp]
/--
theorem `differentiable_exp` / 定理 `differentiable_exp`

English:
theorem differentiable_exp
  statement: Differentiable Real exp
  proof: fun x => (hasDerivAt_exp x).differentiableAt

@[simp]

中文:
定理 differentiable_exp
  结论: 可微 实数 exp
  证明: fun x => (hasDerivAt_exp x).differentiableAt

@[simp]

Depends on / 依赖: differentiableAt, hasDerivAt_exp
-/
theorem differentiable_exp : Differentiable Real exp := fun x => (hasDerivAt_exp x).differentiableAt

@[simp]
/--
theorem `differentiableAt_exp` / 定理 `differentiableAt_exp`

English:
theorem differentiableAt_exp
  given: {x : Real}
  statement: DifferentiableAt Real exp x
  proof: differentiable_exp x

@[simp]

中文:
定理 differentiableAt_exp
  条件: {x : 实数}
  结论: DifferentiableAt 实数 exp x
  证明: differentiable_exp x

@[simp]

Depends on / 依赖: differentiable_exp
-/
theorem differentiableAt_exp {x : Real} : DifferentiableAt Real exp x :=
  differentiable_exp x

@[simp]
/--
theorem `deriv_exp` / 定理 `deriv_exp`

English:
theorem deriv_exp
  statement: deriv exp = exp
  proof: funext fun x => (hasDerivAt_exp x).deriv

@[simp]

中文:
定理 deriv_exp
  结论: deriv exp = exp
  证明: funext fun x => (hasDerivAt_exp x).deriv

@[simp]

Depends on / 依赖: hasDerivAt_exp
-/
theorem deriv_exp : deriv exp = exp :=
  funext fun x => (hasDerivAt_exp x).deriv

@[simp]
/--
theorem `iter_deriv_exp` / 定理 `iter_deriv_exp`

English:
theorem iter_deriv_exp
  statement: forall n : Nat, deriv^[n] exp = exp

中文:
定理 iter_deriv_exp
  结论: 对任意 n : 自然数, deriv^[n] exp = exp
-/
theorem iter_deriv_exp : forall n : Nat, deriv^[n] exp = exp
  | 0 => rfl
  | n + 1 => by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end Real

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {f : Real -> Real} {f' x : Real} {s : Set Real}

/--
theorem `HasStrictDerivAt.exp` / 定理 `HasStrictDerivAt.exp`

English:
theorem HasStrictDerivAt.exp
  given: (hf : HasStrictDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_exp (f x)).comp x hf

中文:
定理 HasStrictDerivAt.exp
  条件: (hf : HasStrictDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_exp (f x)).comp x hf

Depends on / 依赖: Real.hasStrictDerivAt_exp, hasStrictDerivAt_exp
-/
theorem HasStrictDerivAt.exp (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp x hf

/--
theorem `HasDerivAt.exp` / 定理 `HasDerivAt.exp`

English:
theorem HasDerivAt.exp
  given: (hf : HasDerivAt f f' x)
  proof: (Real.hasDerivAt_exp (f x)).comp x hf

中文:
定理 在点处可导.exp
  条件: (hf : 在点处可导 f f' x)
  证明: (Real.hasDerivAt_exp (f x)).comp x hf

Depends on / 依赖: Real.hasDerivAt_exp, hasDerivAt_exp
-/
theorem HasDerivAt.exp (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x :=
  (Real.hasDerivAt_exp (f x)).comp x hf

/--
theorem `HasDerivWithinAt.exp` / 定理 `HasDerivWithinAt.exp`

English:
theorem HasDerivWithinAt.exp
  given: (hf : HasDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

中文:
定理 HasDerivWithinAt.exp
  条件: (hf : HasDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_exp, comp_hasDerivWithinAt, hasDerivAt_exp
-/
theorem HasDerivWithinAt.exp (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasDerivWithinAt x hf

/--
theorem `derivWithin_exp` / 定理 `derivWithin_exp`

English:
theorem derivWithin_exp
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]

中文:
定理 derivWithin_exp
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt, hf.hasDerivWithinAt.exp.derivWithin
-/
theorem derivWithin_exp (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    derivWithin (fun x => Real.exp (f x)) s x = Real.exp (f x) * derivWithin f s x :=
  hf.hasDerivWithinAt.exp.derivWithin hxs

@[simp]
/--
theorem `deriv_exp` / 定理 `deriv_exp`

English:
theorem deriv_exp
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasDerivAt.exp.deriv

中文:
定理 deriv_exp
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasDerivAt.exp.deriv

Depends on / 依赖: hasDerivAt, hc.hasDerivAt.exp.deriv
-/
theorem deriv_exp (hc : DifferentiableAt Real f x) :
    deriv (fun x => Real.exp (f x)) x = Real.exp (f x) * deriv f x :=
  hc.hasDerivAt.exp.deriv

end

section

/-! Register lemmas for the derivatives of the composition of `Real.exp` with a differentiable
function, for standalone use and use with `simp`. -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {f' : StrongDual Real E}
  {x : E} {s : Set E}

@[fun_prop]
/--
theorem `ContDiff.exp` / 定理 `ContDiff.exp`

English:
theorem ContDiff.exp
  given: {n} (hf : ContDiff Real n f)
  statement: ContDiff Real n fun x => Real.exp (f x)
  proof: Real.contDiff_exp.comp hf

@[fun_prop]

中文:
定理 连续可微.exp
  条件: {n} (hf : 连续可微 实数 n f)
  结论: 连续可微 实数 n fun x => 实数.exp (f x)
  证明: Real.contDiff_exp.comp hf

@[fun_prop]

Depends on / 依赖: Real.contDiff_exp.comp, contDiff_exp
-/
theorem ContDiff.exp {n} (hf : ContDiff Real n f) : ContDiff Real n fun x => Real.exp (f x) :=
  Real.contDiff_exp.comp hf

@[fun_prop]
/--
theorem `ContDiffAt.exp` / 定理 `ContDiffAt.exp`

English:
theorem ContDiffAt.exp
  given: {n} (hf : ContDiffAt Real n f x)
  statement: ContDiffAt Real n (fun x => Real.exp (f x)) x
  proof: Real.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]

中文:
定理 ContDiffAt.exp
  条件: {n} (hf : ContDiffAt 实数 n f x)
  结论: ContDiffAt 实数 n (fun x => 实数.exp (f x)) x
  证明: Real.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]

Depends on / 依赖: Real.contDiff_exp.contDiffAt.comp, contDiffAt, contDiff_exp
-/
theorem ContDiffAt.exp {n} (hf : ContDiffAt Real n f x) : ContDiffAt Real n (fun x => Real.exp (f x)) x :=
  Real.contDiff_exp.contDiffAt.comp x hf

@[fun_prop]
/--
theorem `ContDiffOn.exp` / 定理 `ContDiffOn.exp`

English:
theorem ContDiffOn.exp
  given: {n} (hf : ContDiffOn Real n f s)
  statement: ContDiffOn Real n (fun x => Real.exp (f x)) s
  proof: Real.contDiff_exp.comp_contDiffOn hf

@[fun_prop]

中文:
定理 ContDiffOn.exp
  条件: {n} (hf : ContDiffOn 实数 n f s)
  结论: ContDiffOn 实数 n (fun x => 实数.exp (f x)) s
  证明: Real.contDiff_exp.comp_contDiffOn hf

@[fun_prop]

Depends on / 依赖: Real.contDiff_exp.comp_contDiffOn, comp_contDiffOn, contDiff_exp
-/
theorem ContDiffOn.exp {n} (hf : ContDiffOn Real n f s) : ContDiffOn Real n (fun x => Real.exp (f x)) s :=
  Real.contDiff_exp.comp_contDiffOn hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.exp` / 定理 `ContDiffWithinAt.exp`

English:
theorem ContDiffWithinAt.exp
  given: {n} (hf : ContDiffWithinAt Real n f s x)
  proof: Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

中文:
定理 ContDiffWithinAt.exp
  条件: {n} (hf : ContDiffWithinAt 实数 n f s x)
  证明: Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

Depends on / 依赖: Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt, comp_contDiffWithinAt, contDiffAt, contDiff_exp
-/
theorem ContDiffWithinAt.exp {n} (hf : ContDiffWithinAt Real n f s x) :
    ContDiffWithinAt Real n (fun x => Real.exp (f x)) s x :=
  Real.contDiff_exp.contDiffAt.comp_contDiffWithinAt x hf

/--
theorem `HasFDerivWithinAt.exp` / 定理 `HasFDerivWithinAt.exp`

English:
theorem HasFDerivWithinAt.exp
  given: (hf : HasFDerivWithinAt f f' s x)
  proof: (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

中文:
定理 HasFDerivWithinAt.exp
  条件: (hf : HasFDerivWithinAt f f' s x)
  证明: (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

Depends on / 依赖: Real.hasDerivAt_exp, comp_hasFDerivWithinAt, hasDerivAt_exp
-/
theorem HasFDerivWithinAt.exp (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') s x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivWithinAt x hf

/--
theorem `HasFDerivAt.exp` / 定理 `HasFDerivAt.exp`

English:
theorem HasFDerivAt.exp
  given: (hf : HasFDerivAt f f' x)
  proof: (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf

中文:
定理 在点处Fréchet可导.exp
  条件: (hf : 在点处Fréchet可导 f f' x)
  证明: (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf

Depends on / 依赖: Real.hasDerivAt_exp, comp_hasFDerivAt, hasDerivAt_exp
-/
theorem HasFDerivAt.exp (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasDerivAt_exp (f x)).comp_hasFDerivAt x hf

/--
theorem `HasStrictFDerivAt.exp` / 定理 `HasStrictFDerivAt.exp`

English:
theorem HasStrictFDerivAt.exp
  given: (hf : HasStrictFDerivAt f f' x)
  proof: (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

中文:
定理 HasStrictFDerivAt.exp
  条件: (hf : HasStrictFDerivAt f f' x)
  证明: (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

Depends on / 依赖: Real.hasStrictDerivAt_exp, comp_hasStrictFDerivAt, hasStrictDerivAt_exp
-/
theorem HasStrictFDerivAt.exp (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) • f') x :=
  (Real.hasStrictDerivAt_exp (f x)).comp_hasStrictFDerivAt x hf

/--
theorem `DifferentiableWithinAt.exp` / 定理 `DifferentiableWithinAt.exp`

English:
theorem DifferentiableWithinAt.exp
  given: (hf : DifferentiableWithinAt Real f s x)
  proof: hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp, fun_prop]

中文:
定理 DifferentiableWithinAt.exp
  条件: (hf : DifferentiableWithinAt 实数 f s x)
  证明: hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp, fun_prop]

Depends on / 依赖: differentiableWithinAt, hasFDerivWithinAt, hf.hasFDerivWithinAt.exp.differentiableWithinAt
-/
theorem DifferentiableWithinAt.exp (hf : DifferentiableWithinAt Real f s x) :
    DifferentiableWithinAt Real (fun x => Real.exp (f x)) s x :=
  hf.hasFDerivWithinAt.exp.differentiableWithinAt

@[simp, fun_prop]
/--
theorem `DifferentiableAt.exp` / 定理 `DifferentiableAt.exp`

English:
theorem DifferentiableAt.exp
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.exp.differentiableAt

@[fun_prop]

中文:
定理 DifferentiableAt.exp
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.exp.differentiableAt

@[fun_prop]

Depends on / 依赖: differentiableAt, hasFDerivAt, hc.hasFDerivAt.exp.differentiableAt
-/
theorem DifferentiableAt.exp (hc : DifferentiableAt Real f x) :
    DifferentiableAt Real (fun x => Real.exp (f x)) x :=
  hc.hasFDerivAt.exp.differentiableAt

@[fun_prop]
/--
theorem `DifferentiableOn.exp` / 定理 `DifferentiableOn.exp`

English:
theorem DifferentiableOn.exp
  given: (hc : DifferentiableOn Real f s)
  proof: fun x h => (hc x h).exp

@[simp, fun_prop]

中文:
定理 DifferentiableOn.exp
  条件: (hc : DifferentiableOn 实数 f s)
  证明: fun x h => (hc x h).exp

@[simp, fun_prop]
-/
theorem DifferentiableOn.exp (hc : DifferentiableOn Real f s) :
    DifferentiableOn Real (fun x => Real.exp (f x)) s := fun x h => (hc x h).exp

@[simp, fun_prop]
/--
theorem `Differentiable.exp` / 定理 `Differentiable.exp`

English:
theorem Differentiable.exp
  given: (hc : Differentiable Real f)
  statement: Differentiable Real fun x => Real.exp (f x)
  proof: fun x => (hc x).exp

中文:
定理 可微.exp
  条件: (hc : 可微 实数 f)
  结论: 可微 实数 fun x => 实数.exp (f x)
  证明: fun x => (hc x).exp
-/
theorem Differentiable.exp (hc : Differentiable Real f) : Differentiable Real fun x => Real.exp (f x) :=
  fun x => (hc x).exp

/--
theorem `fderivWithin_exp` / 定理 `fderivWithin_exp`

English:
theorem fderivWithin_exp
  given: (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x)
  proof: hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]

中文:
定理 fderivWithin_exp
  条件: (hf : DifferentiableWithinAt 实数 f s x) (hxs : UniqueDiffWithinAt 实数 s x)
  证明: hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]

Depends on / 依赖: fderivWithin, hasFDerivWithinAt, hf.hasFDerivWithinAt.exp.fderivWithin
-/
theorem fderivWithin_exp (hf : DifferentiableWithinAt Real f s x) (hxs : UniqueDiffWithinAt Real s x) :
    fderivWithin Real (fun x => Real.exp (f x)) s x = Real.exp (f x) • fderivWithin Real f s x :=
  hf.hasFDerivWithinAt.exp.fderivWithin hxs

@[simp]
/--
theorem `fderiv_exp` / 定理 `fderiv_exp`

English:
theorem fderiv_exp
  given: (hc : DifferentiableAt Real f x)
  proof: hc.hasFDerivAt.exp.fderiv

中文:
定理 fderiv_exp
  条件: (hc : DifferentiableAt 实数 f x)
  证明: hc.hasFDerivAt.exp.fderiv

Depends on / 依赖: fderiv, hasFDerivAt, hc.hasFDerivAt.exp.fderiv
-/
theorem fderiv_exp (hc : DifferentiableAt Real f x) :
    fderiv Real (fun x => Real.exp (f x)) x = Real.exp (f x) • fderiv Real f x :=
  hc.hasFDerivAt.exp.fderiv

end

open Real in
@[simp]
/--
theorem `iteratedDeriv_exp_const_mul` / 定理 `iteratedDeriv_exp_const_mul`

English:
theorem iteratedDeriv_exp_const_mul
  given: (n : Nat) (c : Real)
  proof: by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]

中文:
定理 iteratedDeriv_exp_const_mul
  条件: (n : 自然数) (c : 实数)
  证明: by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]

Depends on / 依赖: contDiff_exp, iter_deriv_exp, iteratedDeriv_comp_const_mul, iteratedDeriv_eq_iterate
-/
theorem iteratedDeriv_exp_const_mul (n : Nat) (c : Real) :
    (iteratedDeriv n fun s => exp (c * s)) = fun s => c ^ n * exp (c * s) := by
  rw [iteratedDeriv_comp_const_mul contDiff_exp]; rw [iteratedDeriv_eq_iterate]; rw [iter_deriv_exp]
