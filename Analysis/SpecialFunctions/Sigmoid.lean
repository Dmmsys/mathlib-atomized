/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Sigmoid function

In this file we define the sigmoid function `x : ℝ ↦ (1 + exp (-x))⁻¹` and prove some of
its analytic properties.

We then show that the sigmoid function can be seen as an order embedding from `ℝ` to `I = [0, 1]`
and that this embedding is both a topological embedding and a measurable embedding. We also prove
that the composition of this embedding with the measurable embedding from a standard Borel space
`α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

### Sigmoid as a function from `ℝ` to `ℝ`
* `Real.sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `Real.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `Real.continuous_sigmoid` : the sigmoid function is continuous.
* `Real.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `Real.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.
* `Real.hasDerivAt_sigmoid` : the derivative of the sigmoid function.
* `Real.analyticAt_sigmoid` : the sigmoid function is analytic at every point.

### Sigmoid as a function from `ℝ` to `I`
* `unitInterval.sigmoid` : the sigmoid function from `ℝ` to `I`.
* `unitInterval.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `unitInterval.continuous_sigmoid` : the sigmoid function is continuous.
* `unitInterval.tendsto_sigmoid_atTop` : the sigmoid function tends to `1` at `+∞`.
* `unitInterval.tendsto_sigmoid_atBot` : the sigmoid function tends to `0` at `-∞`.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `OrderEmbedding.sigmoid` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `Topology.isEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a topological
  embedding.
* `measurableEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a
  measurable embedding.
* `measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of the
  sigmoid function from `ℝ` to `I` with the measurable embedding from a standard Borel
  space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/

@[expose] public section

namespace Real

/--
Definition of `sigmoid` / `sigmoid` 的定义

English:
definition sigmoid
  signature: (x : Real)
  body: (1 + exp (-x))⁻¹

中文:
定义 sigmoid
  签名: (x : 实数)
  定义体: (1 + exp (-x))⁻¹
-/
noncomputable def sigmoid (x : Real) := (1 + exp (-x))⁻¹

/--
lemma `sigmoid_def` / 引理 `sigmoid_def`

English:
lemma sigmoid_def
  given: (x : Real)
  statement: sigmoid x = (1 + exp (-x))⁻¹
  proof: rfl

@[simp]

中文:
引理 sigmoid_def
  条件: (x : 实数)
  结论: sigmoid x = (1 + exp (-x))⁻¹
  证明: rfl

@[simp]

Depends on / 依赖: Unique, subsingleton, unique_iff_subsingleton_and_nonempty
-/
lemma sigmoid_def (x : Real) : sigmoid x = (1 + exp (-x))⁻¹ := rfl

@[simp]
/--
lemma `sigmoid_zero` / 引理 `sigmoid_zero`

English:
lemma sigmoid_zero
  statement: sigmoid 0 = 2⁻¹
  proof: by norm_num [sigmoid]

@[bound]

中文:
引理 sigmoid_zero
  结论: sigmoid 0 = 2⁻¹
  证明: by norm_num [sigmoid]

@[bound]

Depends on / 依赖: sigmoid
-/
lemma sigmoid_zero : sigmoid 0 = 2⁻¹ := by norm_num [sigmoid]

@[bound]
/--
lemma `sigmoid_pos` / 引理 `sigmoid_pos`

English:
lemma sigmoid_pos
  given: (x : Real)
  statement: 0 < sigmoid x
  proof: by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]

中文:
引理 sigmoid_pos
  条件: (x : 实数)
  结论: 0 < sigmoid x
  证明: by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]
-/
lemma sigmoid_pos (x : Real) : 0 < sigmoid x := by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]
/--
lemma `sigmoid_nonneg` / 引理 `sigmoid_nonneg`

English:
lemma sigmoid_nonneg
  given: (x : Real)
  statement: 0 <= sigmoid x
  proof: (sigmoid_pos x).le

@[bound]

中文:
引理 sigmoid_nonneg
  条件: (x : 实数)
  结论: 0 <= sigmoid x
  证明: (sigmoid_pos x).le

@[bound]

Depends on / 依赖: sigmoid_pos
-/
lemma sigmoid_nonneg (x : Real) : 0 <= sigmoid x := (sigmoid_pos x).le

@[bound]
/--
lemma `sigmoid_lt_one` / 引理 `sigmoid_lt_one`

English:
lemma sigmoid_lt_one
  given: (x : Real)
  statement: sigmoid x < 1
  proof: inv_lt_one_of_one_lt₀ (lt_add_iff_pos_right 1).mpr exp_pos _

@[bound]

中文:
引理 sigmoid_lt_one
  条件: (x : 实数)
  结论: sigmoid x < 1
  证明: inv_lt_one_of_one_lt₀ (lt_add_iff_pos_right 1).mpr exp_pos _

@[bound]

Depends on / 依赖: exp_pos, lt_add_iff_pos_right
-/
lemma sigmoid_lt_one (x : Real) : sigmoid x < 1 :=
inv_lt_one_of_one_lt₀ (lt_add_iff_pos_right 1).mpr exp_pos _

@[bound]
/--
lemma `sigmoid_le_one` / 引理 `sigmoid_le_one`

English:
lemma sigmoid_le_one
  given: (x : Real)
  statement: sigmoid x <= 1
  proof: (sigmoid_lt_one x).le

@[gcongr, mono]

中文:
引理 sigmoid_le_one
  条件: (x : 实数)
  结论: sigmoid x <= 1
  证明: (sigmoid_lt_one x).le

@[gcongr, mono]

Depends on / 依赖: sigmoid_lt_one
-/
lemma sigmoid_le_one (x : Real) : sigmoid x <= 1 := (sigmoid_lt_one x).le

@[gcongr, mono]
/--
lemma `sigmoid_strictMono` / 引理 `sigmoid_strictMono`

English:
lemma sigmoid_strictMono
  statement: StrictMono sigmoid
  proof: fun a b hab => by
  simp only [sigmoid]
  gcongr

中文:
引理 sigmoid_strictMono
  结论: StrictMono sigmoid
  证明: fun a b hab => by
  simp only [sigmoid]
  gcongr

Depends on / 依赖: sigmoid
-/
lemma sigmoid_strictMono : StrictMono sigmoid := fun a b hab => by
  simp only [sigmoid]
  gcongr

/--
lemma `sigmoid_le_iff` / 引理 `sigmoid_le_iff`

English:
lemma sigmoid_le_iff
  given: {a b : Real}
  statement: sigmoid a <= sigmoid b ↔ a <= b
  proof: sigmoid_strictMono.le_iff_le

@[gcongr]

中文:
引理 sigmoid_le_iff
  条件: {a b : 实数}
  结论: sigmoid a <= sigmoid b ↔ a <= b
  证明: sigmoid_strictMono.le_iff_le

@[gcongr]

Depends on / 依赖: le_iff_le, sigmoid_strictMono, sigmoid_strictMono.le_iff_le
-/
lemma sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid b ↔ a <= b := sigmoid_strictMono.le_iff_le

@[gcongr]
/--
lemma `sigmoid_le` / 引理 `sigmoid_le`

English:
lemma sigmoid_le
  given: {a b : Real}
  statement: a <= b -> sigmoid a <= sigmoid b
  proof: sigmoid_le_iff.mpr

中文:
引理 sigmoid_le
  条件: {a b : 实数}
  结论: a <= b -> sigmoid a <= sigmoid b
  证明: sigmoid_le_iff.mpr

Depends on / 依赖: sigmoid_le_iff, sigmoid_le_iff.mpr
-/
lemma sigmoid_le {a b : Real} : a <= b -> sigmoid a <= sigmoid b := sigmoid_le_iff.mpr

/--
lemma `sigmoid_lt_iff` / 引理 `sigmoid_lt_iff`

English:
lemma sigmoid_lt_iff
  given: {a b : Real}
  statement: sigmoid a < sigmoid b ↔ a < b
  proof: sigmoid_strictMono.lt_iff_lt

@[gcongr]

中文:
引理 sigmoid_lt_iff
  条件: {a b : 实数}
  结论: sigmoid a < sigmoid b ↔ a < b
  证明: sigmoid_strictMono.lt_iff_lt

@[gcongr]

Depends on / 依赖: lt_iff_lt, sigmoid_strictMono, sigmoid_strictMono.lt_iff_lt
-/
lemma sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b ↔ a < b := sigmoid_strictMono.lt_iff_lt

@[gcongr]
/--
lemma `sigmoid_lt` / 引理 `sigmoid_lt`

English:
lemma sigmoid_lt
  given: {a b : Real}
  statement: a < b -> sigmoid a < sigmoid b
  proof: sigmoid_lt_iff.mpr

@[mono]

中文:
引理 sigmoid_lt
  条件: {a b : 实数}
  结论: a < b -> sigmoid a < sigmoid b
  证明: sigmoid_lt_iff.mpr

@[mono]

Depends on / 依赖: sigmoid_lt_iff, sigmoid_lt_iff.mpr
-/
lemma sigmoid_lt {a b : Real} : a < b -> sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
/--
lemma `sigmoid_monotone` / 引理 `sigmoid_monotone`

English:
lemma sigmoid_monotone
  statement: Monotone sigmoid
  proof: sigmoid_strictMono.monotone

中文:
引理 sigmoid_monotone
  结论: Monotone sigmoid
  证明: sigmoid_strictMono.monotone

Depends on / 依赖: monotone, sigmoid_strictMono, sigmoid_strictMono.monotone
-/
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

/--
lemma `sigmoid_injective` / 引理 `sigmoid_injective`

English:
lemma sigmoid_injective
  statement: Function.Injective sigmoid
  proof: sigmoid_strictMono.injective

@[simp]

中文:
引理 sigmoid_injective
  结论: Function.Injective sigmoid
  证明: sigmoid_strictMono.injective

@[simp]

Depends on / 依赖: injective, sigmoid_strictMono, sigmoid_strictMono.injective
-/
lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
/--
lemma `sigmoid_inj` / 引理 `sigmoid_inj`

English:
lemma sigmoid_inj
  given: {a b : Real}
  statement: sigmoid a = sigmoid b ↔ a = b
  proof: sigmoid_injective.eq_iff

中文:
引理 sigmoid_inj
  条件: {a b : 实数}
  结论: sigmoid a = sigmoid b ↔ a = b
  证明: sigmoid_injective.eq_iff

Depends on / 依赖: eq_iff, sigmoid_injective, sigmoid_injective.eq_iff
-/
lemma sigmoid_inj {a b : Real} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

/--
lemma `sigmoid_neg` / 引理 `sigmoid_neg`

English:
lemma sigmoid_neg
  given: (x : Real)
  statement: sigmoid (-x) = 1 - sigmoid x
  proof: by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : Real)]

中文:
引理 sigmoid_neg
  条件: (x : 实数)
  结论: sigmoid (-x) = 1 - sigmoid x
  证明: by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : Real)]

Depends on / 依赖: Real.exp_add, add_comm, add_mul, exp_add, sigmoid_def
-/
lemma sigmoid_neg (x : Real) : sigmoid (-x) = 1 - sigmoid x := by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : Real)]

/--
lemma `sigmoid_mul_rexp_neg` / 引理 `sigmoid_mul_rexp_neg`

English:
lemma sigmoid_mul_rexp_neg
  given: (x : Real)
  statement: sigmoid x * exp (-x) = sigmoid (-x)
  proof: by
  rw [sigmoid_neg]; rw [sigmoid_def]
  field

中文:
引理 sigmoid_mul_rexp_neg
  条件: (x : 实数)
  结论: sigmoid x * exp (-x) = sigmoid (-x)
  证明: by
  rw [sigmoid_neg]; rw [sigmoid_def]
  field

Depends on / 依赖: sigmoid_def, sigmoid_neg
-/
lemma sigmoid_mul_rexp_neg (x : Real) : sigmoid x * exp (-x) = sigmoid (-x) := by
  rw [sigmoid_neg]; rw [sigmoid_def]
  field

open Set in
/--
lemma `range_sigmoid` / 引理 `range_sigmoid`

English:
lemma range_sigmoid
  statement: range Real.sigmoid = Ioo 0 1
  proof: by
  refine subset_antisymm ?_ fun x hx => ?_
  · rintro - ⟨x, rfl⟩
    push _ in _
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

中文:
引理 range_sigmoid
  结论: range 实数.sigmoid = Ioo 0 1
  证明: by
  refine subset_antisymm ?_ fun x hx => ?_
  · rintro - ⟨x, rfl⟩
    push _ in _
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

Depends on / 依赖: exp_log, replace, sigmoid_def, sub_pos, subset_antisymm
-/
lemma range_sigmoid : range Real.sigmoid = Ioo 0 1 := by
  refine subset_antisymm ?_ fun x hx => ?_
  · rintro - ⟨x, rfl⟩
    push _ in _
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

open Topology Filter

/--
lemma `tendsto_sigmoid_atTop` / 引理 `tendsto_sigmoid_atTop`

English:
lemma tendsto_sigmoid_atTop
  statement: Tendsto sigmoid atTop (𝓝 1)
  proof: by
.inv₀ .const_add 1 simpa using! Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot
    by norm_num

中文:
引理 tendsto_sigmoid_atTop
  结论: Tendsto sigmoid atTop (𝓝 1)
  证明: by
.inv₀ .const_add 1 simpa using! Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot
    by norm_num

Depends on / 依赖: Real.tendsto_exp_comp_nhds_zero.mpr, const_add, tendsto_exp_comp_nhds_zero, tendsto_neg_atTop_atBot
-/
lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) := by
.inv₀ .const_add 1 simpa using! Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot
    by norm_num

/--
lemma `tendsto_sigmoid_atBot` / 引理 `tendsto_sigmoid_atBot`

English:
lemma tendsto_sigmoid_atBot
  statement: Tendsto sigmoid atBot (𝓝 0)
  proof: tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
.inv_tendsto_atTop

中文:
引理 tendsto_sigmoid_atBot
  结论: Tendsto sigmoid atBot (𝓝 0)
  证明: tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
.inv_tendsto_atTop

Depends on / 依赖: add_atTop, inv_tendsto_atTop, tendsto_const_nhds, tendsto_const_nhds.add_atTop, tendsto_exp_comp_atTop, tendsto_exp_comp_atTop.mpr, tendsto_neg_atBot_atTop
-/
lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
.inv_tendsto_atTop

/--
lemma `hasDerivAt_sigmoid` / 引理 `hasDerivAt_sigmoid`

English:
lemma hasDerivAt_sigmoid
  given: (x : Real)
  proof: by
  convert! (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg]; rw [← sigmoid_mul_rexp_neg x]; rw [sigmoid_def]
  field [sq]

中文:
引理 hasDerivAt_sigmoid
  条件: (x : 实数)
  证明: by
  convert! (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg]; rw [← sigmoid_mul_rexp_neg x]; rw [sigmoid_def]
  field [sq]

Depends on / 依赖: const_add, convert, exp.const_add, hasDerivAt_neg, sigmoid_def, sigmoid_mul_rexp_neg, sigmoid_neg
-/
lemma hasDerivAt_sigmoid (x : Real) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  convert! (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg]; rw [← sigmoid_mul_rexp_neg x]; rw [sigmoid_def]
  field [sq]

/--
lemma `deriv_sigmoid` / 引理 `deriv_sigmoid`

English:
lemma deriv_sigmoid
  statement: deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x)
  proof: funext fun x => (hasDerivAt_sigmoid x).deriv

中文:
引理 deriv_sigmoid
  结论: deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x)
  证明: funext fun x => (hasDerivAt_sigmoid x).deriv

Depends on / 依赖: hasDerivAt_sigmoid
-/
lemma deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) :=
  funext fun x => (hasDerivAt_sigmoid x).deriv

end Real

open Set Real

variable {x : Real} {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {f : E -> Real} {s : Set E}

@[fun_prop]
/--
lemma `analyticAt_sigmoid` / 引理 `analyticAt_sigmoid`

English:
lemma analyticAt_sigmoid
  statement: AnalyticAt Real sigmoid x
  proof: AnalyticAt.fun_inv (by fun_prop) (by positivity)

@[fun_prop]

中文:
引理 analyticAt_sigmoid
  结论: AnalyticAt 实数 sigmoid x
  证明: AnalyticAt.fun_inv (by fun_prop) (by positivity)

@[fun_prop]

Depends on / 依赖: AnalyticAt, AnalyticAt.fun_inv, fun_inv, fun_prop
-/
lemma analyticAt_sigmoid : AnalyticAt Real sigmoid x :=
  AnalyticAt.fun_inv (by fun_prop) (by positivity)

@[fun_prop]
/--
lemma `AnalyticAt.sigmoid` / 引理 `AnalyticAt.sigmoid`

English:
lemma AnalyticAt.sigmoid
  given: {x : E} (fa : AnalyticAt Real f x)
  statement: AnalyticAt Real (sigmoid ∘ f) x
  proof: analyticAt_sigmoid.comp fa

@[fun_prop]

中文:
引理 AnalyticAt.sigmoid
  条件: {x : E} (fa : AnalyticAt 实数 f x)
  结论: AnalyticAt 实数 (sigmoid ∘ f) x
  证明: analyticAt_sigmoid.comp fa

@[fun_prop]

Depends on / 依赖: analyticAt_sigmoid, analyticAt_sigmoid.comp
-/
lemma AnalyticAt.sigmoid {x : E} (fa : AnalyticAt Real f x) : AnalyticAt Real (sigmoid ∘ f) x :=
  analyticAt_sigmoid.comp fa

@[fun_prop]
/--
lemma `AnalyticAt.sigmoid'` / 引理 `AnalyticAt.sigmoid'`

English:
lemma AnalyticAt.sigmoid'
  given: {x : E} (fa : AnalyticAt Real f x)
  proof: fa.sigmoid

中文:
引理 AnalyticAt.sigmoid'
  条件: {x : E} (fa : AnalyticAt 实数 f x)
  证明: fa.sigmoid

Depends on / 依赖: fa.sigmoid, sigmoid
-/
lemma AnalyticAt.sigmoid' {x : E} (fa : AnalyticAt Real f x) :
    AnalyticAt Real (fun z => Real.sigmoid (f z)) x := fa.sigmoid

/--
lemma `analyticOnNhd_sigmoid` / 引理 `analyticOnNhd_sigmoid`

English:
lemma analyticOnNhd_sigmoid
  statement: AnalyticOnNhd Real sigmoid Set.univ
  proof: fun _ _ => analyticAt_sigmoid

中文:
引理 analyticOnNhd_sigmoid
  结论: AnalyticOnNhd 实数 sigmoid Set.univ
  证明: fun _ _ => analyticAt_sigmoid

Depends on / 依赖: analyticAt_sigmoid
-/
lemma analyticOnNhd_sigmoid : AnalyticOnNhd Real sigmoid Set.univ :=
  fun _ _ => analyticAt_sigmoid

/--
lemma `AnalyticOnNhd.sigmoid` / 引理 `AnalyticOnNhd.sigmoid`

English:
lemma AnalyticOnNhd.sigmoid
  given: (fs : AnalyticOnNhd Real f s)
  statement: AnalyticOnNhd Real (sigmoid ∘ f) s
  proof: fun z n => analyticAt_sigmoid.comp (fs z n)

中文:
引理 AnalyticOnNhd.sigmoid
  条件: (fs : AnalyticOnNhd 实数 f s)
  结论: AnalyticOnNhd 实数 (sigmoid ∘ f) s
  证明: fun z n => analyticAt_sigmoid.comp (fs z n)

Depends on / 依赖: analyticAt_sigmoid, analyticAt_sigmoid.comp
-/
lemma AnalyticOnNhd.sigmoid (fs : AnalyticOnNhd Real f s) : AnalyticOnNhd Real (sigmoid ∘ f) s :=
  fun z n => analyticAt_sigmoid.comp (fs z n)

/--
lemma `analyticOn_sigmoid` / 引理 `analyticOn_sigmoid`

English:
lemma analyticOn_sigmoid
  statement: AnalyticOn Real sigmoid Set.univ
  proof: analyticOnNhd_sigmoid.analyticOn

中文:
引理 analyticOn_sigmoid
  结论: AnalyticOn 实数 sigmoid Set.univ
  证明: analyticOnNhd_sigmoid.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd_sigmoid, analyticOnNhd_sigmoid.analyticOn
-/
lemma analyticOn_sigmoid : AnalyticOn Real sigmoid Set.univ :=
  analyticOnNhd_sigmoid.analyticOn

/--
lemma `AnalyticOn.sigmoid` / 引理 `AnalyticOn.sigmoid`

English:
lemma AnalyticOn.sigmoid
  given: (fs : AnalyticOn Real f s)
  statement: AnalyticOn Real (sigmoid ∘ f) s
  proof: analyticOnNhd_sigmoid.comp_analyticOn fs (mapsTo_univ _ _)

中文:
引理 AnalyticOn.sigmoid
  条件: (fs : AnalyticOn 实数 f s)
  结论: AnalyticOn 实数 (sigmoid ∘ f) s
  证明: analyticOnNhd_sigmoid.comp_analyticOn fs (mapsTo_univ _ _)

Depends on / 依赖: analyticOnNhd_sigmoid, analyticOnNhd_sigmoid.comp_analyticOn, comp_analyticOn, mapsTo_univ
-/
lemma AnalyticOn.sigmoid (fs : AnalyticOn Real f s) : AnalyticOn Real (sigmoid ∘ f) s :=
  analyticOnNhd_sigmoid.comp_analyticOn fs (mapsTo_univ _ _)

/--
lemma `analyticWithinAt_sigmoid` / 引理 `analyticWithinAt_sigmoid`

English:
lemma analyticWithinAt_sigmoid
  given: {s : Set Real}
  statement: AnalyticWithinAt Real sigmoid s x
  proof: analyticAt_sigmoid.analyticWithinAt

中文:
引理 analyticWithinAt_sigmoid
  条件: {s : Set 实数}
  结论: AnalyticWithinAt 实数 sigmoid s x
  证明: analyticAt_sigmoid.analyticWithinAt

Depends on / 依赖: analyticAt_sigmoid, analyticAt_sigmoid.analyticWithinAt, analyticWithinAt
-/
lemma analyticWithinAt_sigmoid {s : Set Real} : AnalyticWithinAt Real sigmoid s x :=
  analyticAt_sigmoid.analyticWithinAt

/--
lemma `AnalyticWithinAt.sigmoid` / 引理 `AnalyticWithinAt.sigmoid`

English:
lemma AnalyticWithinAt.sigmoid
  given: {x : E} (fa : AnalyticWithinAt Real f s x)
  proof: analyticAt_sigmoid.comp_analyticWithinAt fa

中文:
引理 AnalyticWithinAt.sigmoid
  条件: {x : E} (fa : AnalyticWithinAt 实数 f s x)
  证明: analyticAt_sigmoid.comp_analyticWithinAt fa

Depends on / 依赖: analyticAt_sigmoid, analyticAt_sigmoid.comp_analyticWithinAt, comp_analyticWithinAt
-/
lemma AnalyticWithinAt.sigmoid {x : E} (fa : AnalyticWithinAt Real f s x) :
  AnalyticWithinAt Real (sigmoid ∘ f) s x := analyticAt_sigmoid.comp_analyticWithinAt fa

open ContDiff in
@[fun_prop]
/--
lemma `contDiff_sigmoid` / 引理 `contDiff_sigmoid`

English:
lemma contDiff_sigmoid
  statement: ContDiff Real ω sigmoid
  proof: analyticOn_sigmoid.contDiff

中文:
引理 contDiff_sigmoid
  结论: ContDiff 实数 ω sigmoid
  证明: analyticOn_sigmoid.contDiff

Depends on / 依赖: analyticOn_sigmoid, analyticOn_sigmoid.contDiff, contDiff
-/
lemma contDiff_sigmoid : ContDiff Real ω sigmoid := analyticOn_sigmoid.contDiff

open ContDiff in
@[fun_prop]
/--
lemma `ContDiff.sigmoid` / 引理 `ContDiff.sigmoid`

English:
lemma ContDiff.sigmoid
  given: (hf : ContDiff Real ω f)
  statement: ContDiff Real ω (sigmoid ∘ f)
  proof: contDiff_sigmoid.comp hf

@[fun_prop]

中文:
引理 ContDiff.sigmoid
  条件: (hf : ContDiff 实数 ω f)
  结论: ContDiff 实数 ω (sigmoid ∘ f)
  证明: contDiff_sigmoid.comp hf

@[fun_prop]

Depends on / 依赖: contDiff_sigmoid, contDiff_sigmoid.comp
-/
lemma ContDiff.sigmoid (hf : ContDiff Real ω f) : ContDiff Real ω (sigmoid ∘ f) :=
  contDiff_sigmoid.comp hf

@[fun_prop]
/--
lemma `differentiable_sigmoid` / 引理 `differentiable_sigmoid`

English:
lemma differentiable_sigmoid
  statement: Differentiable Real sigmoid
  proof: .differentiable_one contDiff_sigmoid.of_le le_top

@[fun_prop]

中文:
引理 differentiable_sigmoid
  结论: Differentiable 实数 sigmoid
  证明: .differentiable_one contDiff_sigmoid.of_le le_top

@[fun_prop]

Depends on / 依赖: contDiff_sigmoid, contDiff_sigmoid.of_le, differentiable_one, le_top, of_le
-/
lemma differentiable_sigmoid : Differentiable Real sigmoid :=
.differentiable_one contDiff_sigmoid.of_le le_top

@[fun_prop]
/--
lemma `Differentiable.sigmoid` / 引理 `Differentiable.sigmoid`

English:
lemma Differentiable.sigmoid
  given: (hf : Differentiable Real f)
  statement: Differentiable Real (sigmoid ∘ f)
  proof: differentiable_sigmoid.comp hf

@[fun_prop]

中文:
引理 Differentiable.sigmoid
  条件: (hf : Differentiable 实数 f)
  结论: Differentiable 实数 (sigmoid ∘ f)
  证明: differentiable_sigmoid.comp hf

@[fun_prop]

Depends on / 依赖: differentiable_sigmoid, differentiable_sigmoid.comp
-/
lemma Differentiable.sigmoid (hf : Differentiable Real f) : Differentiable Real (sigmoid ∘ f) :=
  differentiable_sigmoid.comp hf

@[fun_prop]
/--
lemma `differentiableAt_sigmoid` / 引理 `differentiableAt_sigmoid`

English:
lemma differentiableAt_sigmoid
  statement: DifferentiableAt Real sigmoid x
  proof: differentiable_sigmoid x

@[fun_prop]

中文:
引理 differentiableAt_sigmoid
  结论: DifferentiableAt 实数 sigmoid x
  证明: differentiable_sigmoid x

@[fun_prop]

Depends on / 依赖: differentiable_sigmoid
-/
lemma differentiableAt_sigmoid : DifferentiableAt Real sigmoid x :=
  differentiable_sigmoid x

@[fun_prop]
/--
lemma `DifferentiableAt.sigmoid` / 引理 `DifferentiableAt.sigmoid`

English:
lemma DifferentiableAt.sigmoid
  given: {x : E} (hf : DifferentiableAt Real f x)
  proof: differentiableAt_sigmoid.comp x hf

@[fun_prop]

中文:
引理 DifferentiableAt.sigmoid
  条件: {x : E} (hf : DifferentiableAt 实数 f x)
  证明: differentiableAt_sigmoid.comp x hf

@[fun_prop]

Depends on / 依赖: differentiableAt_sigmoid, differentiableAt_sigmoid.comp
-/
lemma DifferentiableAt.sigmoid {x : E} (hf : DifferentiableAt Real f x) :
    DifferentiableAt Real (sigmoid ∘ f) x := differentiableAt_sigmoid.comp x hf

@[fun_prop]
/--
lemma `continuous_sigmoid` / 引理 `continuous_sigmoid`

English:
lemma continuous_sigmoid
  statement: Continuous sigmoid
  proof: by
  apply Differentiable.continuous (𝕜 := Real) -- fun_prop can't choose `𝕜`
  fun_prop

omit [NormedSpace Real E] in
@[fun_prop]

中文:
引理 continuous_sigmoid
  结论: Continuous sigmoid
  证明: by
  apply Differentiable.continuous (𝕜 := Real) -- fun_prop can't choose `𝕜`
  fun_prop

omit [NormedSpace Real E] in
@[fun_prop]

Depends on / 依赖: Differentiable, Differentiable.continuous, continuous, fun_prop
-/
lemma continuous_sigmoid : Continuous sigmoid := by
  apply Differentiable.continuous (𝕜 := Real) -- fun_prop can't choose `𝕜`
  fun_prop

omit [NormedSpace Real E] in
@[fun_prop]
/--
lemma `Continuous.sigmoid` / 引理 `Continuous.sigmoid`

English:
lemma Continuous.sigmoid
  given: (hf : Continuous f)
  statement: Continuous (sigmoid ∘ f)
  proof: continuous_sigmoid.comp hf

中文:
引理 Continuous.sigmoid
  条件: (hf : Continuous f)
  结论: Continuous (sigmoid ∘ f)
  证明: continuous_sigmoid.comp hf

Depends on / 依赖: continuous_sigmoid, continuous_sigmoid.comp
-/
lemma Continuous.sigmoid (hf : Continuous f) : Continuous (sigmoid ∘ f) :=
  continuous_sigmoid.comp hf

namespace unitInterval

/--
Definition of `sigmoid` / `sigmoid` 的定义

English:
definition sigmoid
  signature: : Real -> I
  body: Subtype.coind Real.sigmoid (fun _ => ⟨by bound, by bound⟩)

@[bound]

中文:
定义 sigmoid
  签名: : 实数 -> I
  定义体: Subtype.coind Real.sigmoid (fun _ => ⟨by bound, by bound⟩)

@[bound]

Depends on / 依赖: Real.sigmoid, Subtype, Subtype.coind, sigmoid
-/
noncomputable def sigmoid : Real -> I := Subtype.coind Real.sigmoid (fun _ => ⟨by bound, by bound⟩)

@[bound]
/--
lemma `sigmoid_pos` / 引理 `sigmoid_pos`

English:
lemma sigmoid_pos
  given: (x : Real)
  statement: 0 < sigmoid x
  proof: Real.sigmoid_pos x

@[bound]

中文:
引理 sigmoid_pos
  条件: (x : 实数)
  结论: 0 < sigmoid x
  证明: Real.sigmoid_pos x

@[bound]

Depends on / 依赖: Real.sigmoid_pos, sigmoid_pos
-/
lemma sigmoid_pos (x : Real) : 0 < sigmoid x := Real.sigmoid_pos x

@[bound]
/--
lemma `sigmoid_lt_one` / 引理 `sigmoid_lt_one`

English:
lemma sigmoid_lt_one
  given: (x : Real)
  statement: sigmoid x < 1
  proof: Real.sigmoid_lt_one x

@[gcongr, mono]

中文:
引理 sigmoid_lt_one
  条件: (x : 实数)
  结论: sigmoid x < 1
  证明: Real.sigmoid_lt_one x

@[gcongr, mono]

Depends on / 依赖: Real.sigmoid_lt_one, sigmoid_lt_one
-/
lemma sigmoid_lt_one (x : Real) : sigmoid x < 1 := Real.sigmoid_lt_one x

@[gcongr, mono]
/--
lemma `sigmoid_strictMono` / 引理 `sigmoid_strictMono`

English:
lemma sigmoid_strictMono
  statement: StrictMono sigmoid
  proof: Real.sigmoid_strictMono

中文:
引理 sigmoid_strictMono
  结论: StrictMono sigmoid
  证明: Real.sigmoid_strictMono

Depends on / 依赖: Real.sigmoid_strictMono, sigmoid_strictMono
-/
lemma sigmoid_strictMono : StrictMono sigmoid := Real.sigmoid_strictMono

/--
lemma `sigmoid_le_iff` / 引理 `sigmoid_le_iff`

English:
lemma sigmoid_le_iff
  given: {a b : Real}
  statement: sigmoid a <= sigmoid b ↔ a <= b
  proof: Real.sigmoid_le_iff

@[gcongr]

中文:
引理 sigmoid_le_iff
  条件: {a b : 实数}
  结论: sigmoid a <= sigmoid b ↔ a <= b
  证明: Real.sigmoid_le_iff

@[gcongr]

Depends on / 依赖: Real.sigmoid_le_iff, sigmoid_le_iff
-/
lemma sigmoid_le_iff {a b : Real} : sigmoid a <= sigmoid b ↔ a <= b := Real.sigmoid_le_iff

@[gcongr]
/--
lemma `sigmoid_le` / 引理 `sigmoid_le`

English:
lemma sigmoid_le
  given: {a b : Real}
  statement: a <= b -> sigmoid a <= sigmoid b
  proof: sigmoid_le_iff.mpr

中文:
引理 sigmoid_le
  条件: {a b : 实数}
  结论: a <= b -> sigmoid a <= sigmoid b
  证明: sigmoid_le_iff.mpr

Depends on / 依赖: sigmoid_le_iff, sigmoid_le_iff.mpr
-/
lemma sigmoid_le {a b : Real} : a <= b -> sigmoid a <= sigmoid b := sigmoid_le_iff.mpr

/--
lemma `sigmoid_lt_iff` / 引理 `sigmoid_lt_iff`

English:
lemma sigmoid_lt_iff
  given: {a b : Real}
  statement: sigmoid a < sigmoid b ↔ a < b
  proof: Real.sigmoid_lt_iff

@[gcongr]

中文:
引理 sigmoid_lt_iff
  条件: {a b : 实数}
  结论: sigmoid a < sigmoid b ↔ a < b
  证明: Real.sigmoid_lt_iff

@[gcongr]

Depends on / 依赖: Real.sigmoid_lt_iff, sigmoid_lt_iff
-/
lemma sigmoid_lt_iff {a b : Real} : sigmoid a < sigmoid b ↔ a < b := Real.sigmoid_lt_iff

@[gcongr]
/--
lemma `sigmoid_lt` / 引理 `sigmoid_lt`

English:
lemma sigmoid_lt
  given: {a b : Real}
  statement: a < b -> sigmoid a < sigmoid b
  proof: sigmoid_lt_iff.mpr

@[mono]

中文:
引理 sigmoid_lt
  条件: {a b : 实数}
  结论: a < b -> sigmoid a < sigmoid b
  证明: sigmoid_lt_iff.mpr

@[mono]

Depends on / 依赖: sigmoid_lt_iff, sigmoid_lt_iff.mpr
-/
lemma sigmoid_lt {a b : Real} : a < b -> sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
/--
lemma `sigmoid_monotone` / 引理 `sigmoid_monotone`

English:
lemma sigmoid_monotone
  statement: Monotone sigmoid
  proof: sigmoid_strictMono.monotone

中文:
引理 sigmoid_monotone
  结论: Monotone sigmoid
  证明: sigmoid_strictMono.monotone

Depends on / 依赖: monotone, sigmoid_strictMono, sigmoid_strictMono.monotone
-/
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

/--
lemma `sigmoid_injective` / 引理 `sigmoid_injective`

English:
lemma sigmoid_injective
  statement: Function.Injective sigmoid
  proof: sigmoid_strictMono.injective

@[simp]

中文:
引理 sigmoid_injective
  结论: Function.Injective sigmoid
  证明: sigmoid_strictMono.injective

@[simp]

Depends on / 依赖: injective, sigmoid_strictMono, sigmoid_strictMono.injective
-/
lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
/--
lemma `sigmoid_inj` / 引理 `sigmoid_inj`

English:
lemma sigmoid_inj
  given: {a b : Real}
  statement: sigmoid a = sigmoid b ↔ a = b
  proof: sigmoid_injective.eq_iff

@[fun_prop]

中文:
引理 sigmoid_inj
  条件: {a b : 实数}
  结论: sigmoid a = sigmoid b ↔ a = b
  证明: sigmoid_injective.eq_iff

@[fun_prop]

Depends on / 依赖: eq_iff, sigmoid_injective, sigmoid_injective.eq_iff
-/
lemma sigmoid_inj {a b : Real} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[fun_prop]
/--
lemma `continuous_sigmoid` / 引理 `continuous_sigmoid`

English:
lemma continuous_sigmoid
  statement: Continuous sigmoid
  proof: _root_.continuous_sigmoid.subtype_mk _

中文:
引理 continuous_sigmoid
  结论: Continuous sigmoid
  证明: _root_.continuous_sigmoid.subtype_mk _

Depends on / 依赖: _root_, _root_.continuous_sigmoid.subtype_mk, continuous_sigmoid, subtype_mk
-/
lemma continuous_sigmoid : Continuous sigmoid := _root_.continuous_sigmoid.subtype_mk _

/--
lemma `sigmoid_neg` / 引理 `sigmoid_neg`

English:
lemma sigmoid_neg
  given: (x : Real)
  statement: sigmoid (-x) = σ (sigmoid x)
  proof: by
  ext
  exact Real.sigmoid_neg x

中文:
引理 sigmoid_neg
  条件: (x : 实数)
  结论: sigmoid (-x) = σ (sigmoid x)
  证明: by
  ext
  exact Real.sigmoid_neg x

Depends on / 依赖: Real.sigmoid_neg, sigmoid_neg
-/
lemma sigmoid_neg (x : Real) : sigmoid (-x) = σ (sigmoid x) := by
  ext
  exact Real.sigmoid_neg x

set_option backward.isDefEq.respectTransparency false in
open Set in
/--
lemma `range_sigmoid` / 引理 `range_sigmoid`

English:
lemma range_sigmoid
  statement: range unitInterval.sigmoid = Ioo 0 1
  proof: by
  rw [sigmoid]; rw [Subtype.range_coind]; rw [Real.range_sigmoid]
  ext
  simp

中文:
引理 range_sigmoid
  结论: range unit整数erval.sigmoid = Ioo 0 1
  证明: by
  rw [sigmoid]; rw [Subtype.range_coind]; rw [Real.range_sigmoid]
  ext
  simp

Depends on / 依赖: Real.range_sigmoid, Subtype, Subtype.range_coind, range_coind, range_sigmoid, sigmoid
-/
lemma range_sigmoid : range unitInterval.sigmoid = Ioo 0 1 := by
  rw [sigmoid]; rw [Subtype.range_coind]; rw [Real.range_sigmoid]
  ext
  simp

open Topology Filter

/--
lemma `tendsto_sigmoid_atTop` / 引理 `tendsto_sigmoid_atTop`

English:
lemma tendsto_sigmoid_atTop
  statement: Tendsto sigmoid atTop (𝓝 1)
  proof: tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop

中文:
引理 tendsto_sigmoid_atTop
  结论: Tendsto sigmoid atTop (𝓝 1)
  证明: tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop

Depends on / 依赖: Real.tendsto_sigmoid_atTop, tendsto_sigmoid_atTop, tendsto_subtype_rng, tendsto_subtype_rng.mpr
-/
lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop

/--
lemma `tendsto_sigmoid_atBot` / 引理 `tendsto_sigmoid_atBot`

English:
lemma tendsto_sigmoid_atBot
  statement: Tendsto sigmoid atBot (𝓝 0)
  proof: tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

中文:
引理 tendsto_sigmoid_atBot
  结论: Tendsto sigmoid atBot (𝓝 0)
  证明: tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

Depends on / 依赖: Real.tendsto_sigmoid_atBot, tendsto_sigmoid_atBot, tendsto_subtype_rng, tendsto_subtype_rng.mpr
-/
lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

end unitInterval

section Embedding

open unitInterval Function Set

/--
Definition of `OrderEmbedding.sigmoid` / `OrderEmbedding.sigmoid` 的定义

English:
definition OrderEmbedding.sigmoid
  signature: : Real ↪o I
  body: OrderEmbedding.ofStrictMono unitInterval.sigmoid unitInterval.sigmoid_strictMono

中文:
定义 OrderEmbedding.sigmoid
  签名: : 实数 ↪o I
  定义体: OrderEmbedding.ofStrictMono unitInterval.sigmoid unitInterval.sigmoid_strictMono

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, ofStrictMono, sigmoid, sigmoid_strictMono, unitInterval, unitInterval.sigmoid, unitInterval.sigmoid_strictMono
-/
noncomputable def OrderEmbedding.sigmoid : Real ↪o I :=
  OrderEmbedding.ofStrictMono unitInterval.sigmoid unitInterval.sigmoid_strictMono

/--
lemma `Topology.isEmbedding_sigmoid` / 引理 `Topology.isEmbedding_sigmoid`

English:
lemma Topology.isEmbedding_sigmoid
  statement: IsEmbedding unitInterval.sigmoid
  proof: OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => unitInterval.range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

中文:
引理 Topology.isEmbedding_sigmoid
  结论: IsEmbedding unit整数erval.sigmoid
  证明: OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => unitInterval.range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

Depends on / 依赖: Ioo_subset_Ioo, OrderEmbedding, OrderEmbedding.sigmoid.isEmbedding_of_ordConnected, isEmbedding_of_ordConnected, ordConnected_of_Ioo, range_sigmoid, sigmoid, unitInterval, unitInterval.range_sigmoid
-/
lemma Topology.isEmbedding_sigmoid : IsEmbedding unitInterval.sigmoid :=
  OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => unitInterval.range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

/--
lemma `measurableEmbedding_sigmoid` / 引理 `measurableEmbedding_sigmoid`

English:
lemma measurableEmbedding_sigmoid
  statement: MeasurableEmbedding unitInterval.sigmoid
  proof: Topology.isEmbedding_sigmoid.measurableEmbedding unitInterval.range_sigmoid ▸ measurableSet_Ioo

中文:
引理 measurableEmbedding_sigmoid
  结论: MeasurableEmbedding unit整数erval.sigmoid
  证明: Topology.isEmbedding_sigmoid.measurableEmbedding unitInterval.range_sigmoid ▸ measurableSet_Ioo

Depends on / 依赖: Topology, Topology.isEmbedding_sigmoid.measurableEmbedding, isEmbedding_sigmoid, measurableEmbedding, measurableSet_Ioo, range_sigmoid, unitInterval, unitInterval.range_sigmoid
-/
lemma measurableEmbedding_sigmoid : MeasurableEmbedding unitInterval.sigmoid :=
Topology.isEmbedding_sigmoid.measurableEmbedding unitInterval.range_sigmoid ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

/--
lemma `measurableEmbedding_sigmoid_comp_embeddingReal` / 引理 `measurableEmbedding_sigmoid_comp_embeddingReal`

English:
lemma measurableEmbedding_sigmoid_comp_embeddingReal
  proof: measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

中文:
引理 measurableEmbedding_sigmoid_comp_embeddingReal
  证明: measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

Depends on / 依赖: MeasureTheory, MeasureTheory.measurableEmbedding_embeddingReal, measurableEmbedding_embeddingReal, measurableEmbedding_sigmoid, measurableEmbedding_sigmoid.comp
-/
lemma measurableEmbedding_sigmoid_comp_embeddingReal :
    MeasurableEmbedding (unitInterval.sigmoid ∘ MeasureTheory.embeddingReal α) :=
  measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end Embedding
