/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen, Patrick Massot
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Tactic.CrossRefAttribute

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of an exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (exponentialPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.

## Main results
* `cdf_expMeasure_eq`: Proof that the CDF of the exponential measure equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPDF

/-- The pdf of the exponential distribution depending on its rate -/
noncomputable
/-
**ProbabilityTheory.exponentialPDFReal** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：exponentialPDFReal (r x : Real) : Real
参数：r x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def exponentialPDFReal (r x : ℝ) : ℝ :=
  gammaPDFReal 1 r x

/-- The pdf of the exponential distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
/-
**ProbabilityTheory.exponentialPDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`
。
形式化陈述：exponentialPDF (r x : Real) : Real>=0∞
参数：r x : Real。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def exponentialPDF (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPDFReal r x)
/-
**ProbabilityTheory.exponentialPDF_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：exponentialPDF_eq (r x : Real) : exponentialPDF r x = ENNReal.ofReal (if 0
 <= x then r * exp (-(r * x)) else 0)
参数：r x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.exponentialPDF.eq_1`：∀ (r x : ℝ), ProbabilityTheory.ex
ponentialPDF r x = ENNReal.ofReal (ProbabilityTheory.exponentialPDFReal r x)
· 使用定理 `ProbabilityTheory.exponentialPDFReal.eq_1`：∀ (r x : ℝ), ProbabilityTheor
y.exponentialPDFReal r x = ProbabilityTheory.gammaPDFReal 1 r x
· 使用定理 `ProbabilityTheory.gammaPDFReal.eq_1`：∀ (a r x : ℝ),   ProbabilityTheory.
gammaPDFReal a r x = if 0 ≤ x then r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp
 (-(r * x)) else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Real.Gamma_one`：Gamma_one : Gamma 1 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exponentialPDF_eq (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (if 0 ≤ x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPDF, exponentialPDFReal, gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]
/-
**ProbabilityTheory.exponentialPDF_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Probability
Theory`。
形式化陈述：exponentialPDF_of_neg {r x : Real} (hx : x < 0) : exponentialPDF r x = 0
参数：hx : x < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.gammaPDF_of_neg`：gammaPDF_of_neg {a r x : Real} (hx : 
x < 0) : gammaPDF a r x = 0
-/
lemma exponentialPDF_of_neg {r x : ℝ} (hx : x < 0) : exponentialPDF r x = 0 := gammaPDF_of_neg hx
/-
**ProbabilityTheory.exponentialPDF_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：exponentialPDF_of_nonneg {r x : Real} (hx : 0 <= x) : exponentialPDF r x =
 ENNReal.ofReal (r * rexp (-(r * x)))
参数：hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.exponentialPDF_eq`：exponentialPDF_eq (r x : Real) : ex
ponentialPDF r x = ENNReal.ofReal (if 0 <= x then r * exp (-(r * x)) else 0)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exponentialPDF_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDF r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPDF_eq, if_pos hx]

/-- The Lebesgue integral of the exponential pdf over nonpositive reals equals 0 -/
/-
**ProbabilityTheory.lintegral_exponentialPDF_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：lintegral_exponentialPDF_of_nonpos {x r : Real} (hx : x <= 0) : ∫⁻ y in Ii
o x, exponentialPDF r y = 0
参数：hx : x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.lintegral_gammaPDF_of_nonpos`：lintegral_gammaPDF_of_no
npos {x a r : Real} (hx : x <= 0) : ∫⁻ y in Iio x, gammaPDF a r y = 0

--- 原说明 ---
The Lebesgue integral of the exponential pdf over nonpositive reals equals 0
-/
lemma lintegral_exponentialPDF_of_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, exponentialPDF r y = 0 := lintegral_gammaPDF_of_nonpos hx

/-- The exponential pdf is measurable. -/
@[fun_prop]
/-
**ProbabilityTheory.measurable_exponentialPDFReal** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：measurable_exponentialPDFReal (r : Real) : Measurable (exponentialPDFReal 
r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.measurable_gammaPDFReal`：measurable_gammaPDFReal (a r 
: Real) : Measurable (gammaPDFReal a r)

--- 原说明 ---
The exponential pdf is measurable.
-/
lemma measurable_exponentialPDFReal (r : ℝ) : Measurable (exponentialPDFReal r) :=
  measurable_gammaPDFReal 1 r

-- The exponential pdf is strongly measurable -/
@[fun_prop]
/-
**ProbabilityTheory.stronglyMeasurable_exponentialPDFReal** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_exponentialPDFReal (r : Real) : StronglyMeasurable (exp
onentialPDFReal r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.stronglyMeasurable_gammaPDFReal`：stronglyMeasurable_ga
mmaPDFReal (a r : Real) : StronglyMeasurable (gammaPDFReal a r)

--- 原说明 ---
The exponential pdf is measurable. - /
@[fun_prop]
lemma measurable_exponentialPDFReal (r : ℝ) : Measurable (exponentialPDFReal r) 
:=
  measurable_gammaPDFReal 1 r

-- The exponential pdf is strongly measurable
-/
lemma stronglyMeasurable_exponentialPDFReal (r : ℝ) :
    StronglyMeasurable (exponentialPDFReal r) := stronglyMeasurable_gammaPDFReal 1 r

/-- The exponential pdf is positive for all positive reals -/
/-
**ProbabilityTheory.exponentialPDFReal_pos** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：exponentialPDFReal_pos {x r : Real} (hr : 0 < r) (hx : 0 < x) : 0 < expone
ntialPDFReal r x
参数：hr : 0 < r；hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.gammaPDFReal_pos`：gammaPDFReal_pos {x a r : Real} (ha 
: 0 < a) (hr : 0 < r) (hx : 0 < x) : 0 < gammaPDFReal a r x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The exponential pdf is positive for all positive reals
-/
lemma exponentialPDFReal_pos {x r : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < exponentialPDFReal r x := gammaPDFReal_pos zero_lt_one hr hx

/-- The exponential pdf is nonnegative -/
/-
**ProbabilityTheory.exponentialPDFReal_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：exponentialPDFReal_nonneg {r : Real} (hr : 0 < r) (x : Real) : 0 <= expone
ntialPDFReal r x
参数：hr : 0 < r；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.gammaPDFReal_nonneg`：gammaPDFReal_nonneg {a r : Real} 
(ha : 0 < a) (hr : 0 < r) (x : Real) : 0 <= gammaPDFReal a r x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The exponential pdf is nonnegative
-/
lemma exponentialPDFReal_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 ≤ exponentialPDFReal r x := gammaPDFReal_nonneg zero_lt_one hr x

open Measure

/-- The pdf of the exponential distribution integrates to 1 -/
@[simp]
/-
**ProbabilityTheory.lintegral_exponentialPDF_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：lintegral_exponentialPDF_eq_one {r : Real} (hr : 0 < r) : ∫⁻ x, exponentia
lPDF r x = 1
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.lintegral_gammaPDF_eq_one`：lintegral_gammaPDF_eq_one {
a r : Real} (ha : 0 < a) (hr : 0 < r) : ∫⁻ x, gammaPDF a r x = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The pdf of the exponential distribution integrates to 1
-/
lemma lintegral_exponentialPDF_eq_one {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPDF r x = 1 :=
  lintegral_gammaPDF_eq_one zero_lt_one hr

end ExponentialPDF

open MeasureTheory

/-- Measure defined by the exponential distribution -/
@[wikidata Q237193]
noncomputable
/-
**ProbabilityTheory.expMeasure** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：expMeasure (r : Real) : Measure Real
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def expMeasure (r : ℝ) : Measure ℝ := gammaMeasure 1 r
/-
**ProbabilityTheory.isProbabilityMeasure_expMeasure** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：isProbabilityMeasure_expMeasure {r : Real} (hr : 0 < r) : IsProbabilityMea
sure (expMeasure r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isProbabilityMeasure_gammaMeasure`：isProbabilityMeasur
e_gammaMeasure {a r : Real} (ha : 0 < a) (hr : 0 < r) : IsProbabilityMeasure (ga
mmaMeasure a r) where measure_univ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma isProbabilityMeasure_expMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_gammaMeasure zero_lt_one hr

section ExponentialCDF

/-
**ProbabilityTheory.cdf_expMeasure_eq_integral** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：cdf_expMeasure_eq_integral {r : Real} (hr : 0 < r) (x : Real) : cdf (expMe
asure r) x = ∫ x in Iic x, exponentialPDFReal r x
参数：hr : 0 < r；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.cdf_gammaMeasure_eq_integral`：cdf_gammaMeasure_eq_inte
gral {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real) : cdf (gammaMeasure a r) 
x = ∫ x in Iic x, gammaPDFReal a r x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma cdf_expMeasure_eq_integral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = ∫ x in Iic x, exponentialPDFReal r x :=
  cdf_gammaMeasure_eq_integral zero_lt_one hr x
/-
**ProbabilityTheory.cdf_expMeasure_eq_lintegral** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：cdf_expMeasure_eq_lintegral {r : Real} (hr : 0 < r) (x : Real) : cdf (expM
easure r) x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPDF r x)
参数：hr : 0 < r；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.cdf_gammaMeasure_eq_lintegral`：cdf_gammaMeasure_eq_lin
tegral {a r : Real} (ha : 0 < a) (hr : 0 < r) (x : Real) : cdf (gammaMeasure a r
) x = ENNReal.toReal (∫⁻ x in Iic x, …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma cdf_expMeasure_eq_lintegral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPDF r x) :=
  cdf_gammaMeasure_eq_lintegral zero_lt_one hr x

open Topology
/-
**ProbabilityTheory.hasDerivAt_neg_exp_mul_exp** 是 Mathlib 中的一个引理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：hasDerivAt_neg_exp_mul_exp {r x : Real} : HasDerivAt (fun a => -exp (-(r *
 a))) (r * exp (-(r * x))) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `HasDerivAt.exp`：HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.exp (f x)) (Real.exp (f x) * f') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
-/
lemma hasDerivAt_neg_exp_mul_exp {r x : ℝ} :
    HasDerivAt (fun a ↦ -exp (-(r * a))) (r * exp (-(r * x))) x := by
  convert! (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

/-- A negative exponential function is integrable on intervals in `R≥0` -/
/-
**ProbabilityTheory.exp_neg_integrableOn_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Probabil
ityTheory`。
形式化陈述：exp_neg_integrableOn_Ioc {b x : Real} (hb : 0 < b) : IntegrableOn (fun x =
> rexp (-(b * x))) (Ioc 0 x)
参数：hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `exp_neg_integrableOn_Ioi`：exp_neg_integrableOn_Ioi (a : Real) {b : Real}
 (h : 0 < b) : IntegrableOn (fun x : Real => exp (-b * x)) (Ioi a)
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b

--- 原说明 ---
A negative exponential function is integrable on intervals in `R≥0`
-/
lemma exp_neg_integrableOn_Ioc {b x : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x ↦ rexp (-(b * x))) (Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self
/-
**ProbabilityTheory.lintegral_exponentialPDF_eq_antiDeriv** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：lintegral_exponentialPDF_eq_antiDeriv {r : Real} (hr : 0 < r) (x : Real) :
 ∫⁻ y in Iic x, exponentialPDF r y = ENNReal.ofReal (if 0 <= x then 1 - exp (-(r
 * x)) else 0)
参数：hr : 0 < r；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `lintegral_Iic_eq_lintegral_Iio_add_Icc`：lintegral_Iic_eq_lintegral_Iio_a
dd_Icc {y z : Real} (f : Real -> Real>=0∞) (hzy : z <= y) : ∫⁻ x in Iic y, f x =
 (∫⁻ x in Iio z, f x) + ∫⁻ x…
· 使用引理 `ProbabilityTheory.lintegral_exponentialPDF_of_nonpos`：lintegral_exponent
ialPDF_of_nonpos {x r : Real} (hx : x <= 0) : ∫⁻ y in Iio x, exponentialPDF r y 
= 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.exponentialPDF_eq`：exponentialPDF_eq (r x : Real) : ex
ponentialPDF r x = ENNReal.ofReal (if 0 <= x then r * exp (-(r * x)) else 0)
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.IntegrableOn.setLIntegral_lt_top`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α} {f : α → ℝ} {s : Set α},   Measu
reTheory.IntegrableOn f s μ → ∫⁻ (x …
· 使用定理 `integrableOn_Icc_iff_integrableOn_Ioc`：integrableOn_Icc_iff_integrableOn
_Ioc (ha : ‖f a‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
（共 142 条，此处仅展示前 30 条）
-/
lemma lintegral_exponentialPDF_eq_antiDeriv {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫⁻ y in Iic x, exponentialPDF r y
    = ENNReal.ofReal (if 0 ≤ x then 1 - exp (-(r * x)) else 0) := by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic, lintegral_zero, ENNReal.ofReal_zero]
    exact fun a (_ : a ≤ _) ↦ by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ h, lintegral_exponentialPDF_of_nonpos (le_refl 0),
      zero_add]
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun x ↦ ENNReal.ofReal (r * rexp (-(r * x))))
      (by intro a ha; simp [ha.1])]
    rw [← ENNReal.toReal_eq_toReal_iff' _ ENNReal.ofReal_ne_top,
        ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ le_of_lt
        (mul_pos hr (exp_pos _)))]
    · have : ∫ a in uIoc 0 x, r * rexp (-(r * a)) = ∫ a in 0..x, r * rexp (-(r * a)) := by
        rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
      rw [integral_Icc_eq_integral_Ioc, ← uIoc_of_le h, this]
      rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
        (f := fun a ↦ -1 * rexp (-(r * a))) _ _]
      · rw [ENNReal.toReal_ofReal_eq_iff.2
          (sub_nonneg.2 (Real.exp_le_one_iff.2 <| by nlinarith))]
        norm_num; ring
      · simp only [intervalIntegrable_iff, uIoc_of_le h]
        exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _
      · have : Continuous (fun a ↦ rexp (-(r * a))) := by
          simp only [← neg_mul]; exact (continuous_const_mul (-r)).rexp
        exact Continuous.continuousOn (Continuous.comp' (continuous_const_mul (-1)) this)
      · simp only [neg_mul, one_mul]
        exact fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_neg_exp_mul_exp
    · refine Integrable.aestronglyMeasurable (Integrable.const_mul ?_ _)
      rw [← IntegrableOn, integrableOn_Icc_iff_integrableOn_Ioc]
      exact exp_neg_integrableOn_Ioc hr
    · refine ne_of_lt (IntegrableOn.setLIntegral_lt_top ?_)
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _

/-- The CDF of the exponential distribution equals ``1 - exp (-(r * x))`` -/
/-
**ProbabilityTheory.cdf_expMeasure_eq** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：cdf_expMeasure_eq {r : Real} (hr : 0 < r) (x : Real) : cdf (expMeasure r) 
x = if 0 <= x then 1 - exp (-(r * x)) else 0
参数：hr : 0 < r；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.cdf_expMeasure_eq_lintegral`：cdf_expMeasure_eq_lintegr
al {r : Real} (hr : 0 < r) (x : Real) : cdf (expMeasure r) x = ENNReal.toReal (∫
⁻ x in Iic x, exponentialPDF r x)
· 使用引理 `ProbabilityTheory.lintegral_exponentialPDF_eq_antiDeriv`：lintegral_expon
entialPDF_eq_antiDeriv {r : Real} (hr : 0 < r) (x : Real) : ∫⁻ y in Iic x, expon
entialPDF r y = ENNReal.ofReal (if 0 <= x the…
· 使用定理 `ENNReal.toReal_ofReal_eq_iff`：toReal_ofReal_eq_iff {a : Real} : (ENNReal
.ofReal a).toReal = a ↔ 0 <= a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The CDF of the exponential distribution equals ``1 - exp (-(r * x))``
-/
lemma cdf_expMeasure_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = if 0 ≤ x then 1 - exp (-(r * x)) else 0 := by
  rw [cdf_expMeasure_eq_lintegral hr, lintegral_exponentialPDF_eq_antiDeriv hr x,
    ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

end ExponentialCDF

end ProbabilityTheory

