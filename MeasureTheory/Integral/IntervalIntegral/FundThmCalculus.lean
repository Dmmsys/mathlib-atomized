/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Fundamental Theorem of Calculus

We prove various versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for interval integrals in `ℝ`.

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `intervalIntegral` namespace. Many of them follow
the naming scheme `integral_has(Strict?)(F?)Deriv(Within?)At(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `Has(Strict?)(F?)Deriv(Within?)At`.
Let us explain the meaning of each part of the name:

* `Strict` means that the theorem is about strict differentiability, see `HasStrictDerivAt` and
  `HasStrictFDerivAt`;
* `F` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `Within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(Within?)`. These theorems are named
`(f?)deriv(Within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae` states that
`(u, v) ↦ ∫ x in u..v, f x` has a derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t`
at `(a, b)` provided that `f` tends to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where
possible values of `s`, `t`, and corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `intervalIntegral.FTCFilter` to make Lean automatically find `la`/`lb` based on
`s`/`t`. This way we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial
ones not covered by `integral_hasDerivWithinAt_of_tendsto_ae_(left|right)` and
`integral_hasFDerivAt_of_tendsto_ae`). Similarly, `integral_hasDerivWithinAt_of_tendsto_ae_right`
works for both one-sided derivatives using the same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae`, states the following.
Let `(la, la')` be an `intervalIntegral.FTCFilter` pair of filters around `a` (i.e.,
`intervalIntegral.FTCFilter a la la'`) and let `(lb, lb')` be an `intervalIntegral.FTCFilter` pair
of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at `la'` and `lb'`,
respectively, then
$$
  \int_{va}^{vb} f ∂μ - \int_{ua}^{ub} f ∂μ =
  \int_{ub}^{vb} cb ∂μ - \int_{ua}^{va} ca ∂μ + o(‖∫_{ua}^{va} 1 ∂μ‖ + ‖∫_{ub}^{vb} (1:ℝ) ∂μ‖)
$$
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` - most general version, for functions
  with a right derivative
* `intervalIntegral.integral_eq_sub_of_hasDerivAt` - version for functions with a derivative on
  an open set
* `intervalIntegral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

Many applications of these theorems can be found in the directory
`Mathlib/Analysis/SpecialFunctions/Integrals/`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`ContinuousOn.intervalIntegrable` or `ContinuousOn.integrableOn_Icc` or
`ContinuousOn.integrableOn_uIcc`.

Versions of FTC-2 under the simpler assumption that the function is `C^1` are given in the
file `Mathlib/MeasureTheory/Integral/IntervalIntegral/ContDiff.lean`.

Applications to integration by parts are in the file
`Mathlib.MeasureTheory.Integral.IntegrationByParts`.

### `intervalIntegral.FTCFilter` class

As explained above, many theorems in this file rely on the typeclass
`intervalIntegral.FTCFilter (a : ℝ) (l l' : Filter ℝ)` to avoid code duplication. This typeclass
combines four assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `intervalIntegral.FTCFilter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Set.Icc a b] x, 𝓝[Set.Icc a b] x)` (resp.
`(x, 𝓝[Set.uIcc a b] x, 𝓝[Set.uIcc a b] x)`), with `x ∈ Icc a b` (resp. `x ∈ uIcc a b`). This
results in a two-sided derivatives for `x ∈ Set.Ioo a b` and one-sided derivatives for `x ∈ {a, b}`.
Other instances could be added when needed (in that case, one also needs to add instances for
`Filter.IsMeasurablyGenerated` and `Filter.TendstoIxxClass`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2
-/

public section

assert_not_exists HasDerivAt.mul -- guard against import creep

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace intervalIntegral

section FTC1

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`intervalIntegral.FTCFilter a l l'`. This typeclass has exactly four “real” instances:
`(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` can be
seen as a generalization of lemma `integral_hasStrictFDerivAt` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right-hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`. -/
/-
**intervalIntegral.FTCFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 `intervalIntegral`。
形式化陈述：outParam ℝ → Filter ℝ → outParam (Filter ℝ) → Prop
参数：Filter ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is us
ed to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫
 x in u..v, f x`.
-/
class FTCFilter (a : outParam ℝ) (outer : Filter ℝ) (inner : outParam <| Filter ℝ) : Prop
    extends TendstoIxxClass Ioc outer inner where
  pure_le : pure a ≤ outer
  le_nhds : inner ≤ 𝓝 a
  [meas_gen : IsMeasurablyGenerated inner]

namespace FTCFilter


/-
**intervalIntegral.FTCFilter.pure** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegral.FT
CFilter`。
形式化陈述：pure (a : Real) : FTCFilter a (pure a) ⊥ where pure_le
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
instance pure (a : ℝ) : FTCFilter a (pure a) ⊥ where
  pure_le := le_rfl
  le_nhds := bot_le
/-
**intervalIntegral.FTCFilter.nhdsWithinSingleton** 是 Mathlib 中的一个实例，位于命名空间 `inte
rvalIntegral.FTCFilter`。
形式化陈述：nhdsWithinSingleton (a : Real) : FTCFilter a (𝓝[{a}] a) ⊥
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (s
 : Set X), nhdsWithin x s = nhds x ⊓ Filter.principal s
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
-/
instance nhdsWithinSingleton (a : ℝ) : FTCFilter a (𝓝[{a}] a) ⊥ := by
  rw [nhdsWithin, principal_singleton, inf_eq_right.2 (pure_le_nhds a)]; infer_instance
/-
**intervalIntegral.FTCFilter.finiteAt_inner** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral.FTCFilter`。
形式化陈述：finiteAt_inner {a : Real} (l : Filter Real) {l'} [h : FTCFilter a l l'] {μ
 : Measure Real} [IsLocallyFiniteMeasure μ] : μ.FiniteAtFilter l'
参数：l : Filter Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.filter_mono`：filter_mono (h : f <= 
g) : μ.FiniteAtFilter g -> μ.FiniteAtFilter f
· 使用定理 `intervalIntegral.FTCFilter.le_nhds`：∀ {a : outParam ℝ} (outer : Filter ℝ
) {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inner
],   inner ≤ nhds a
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
-/
theorem finiteAt_inner {a : ℝ} (l : Filter ℝ) {l'} [h : FTCFilter a l l'] {μ : Measure ℝ}
    [IsLocallyFiniteMeasure μ] : μ.FiniteAtFilter l' :=
  (μ.finiteAt_nhds a).filter_mono h.le_nhds
/-
**intervalIntegral.FTCFilter.nhds** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegral.FT
CFilter`。
形式化陈述：nhds (a : Real) : FTCFilter a (𝓝 a) (𝓝 a) where pure_le
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
instance nhds (a : ℝ) : FTCFilter a (𝓝 a) (𝓝 a) where
  pure_le := pure_le_nhds a
  le_nhds := le_rfl
/-
**intervalIntegral.FTCFilter.nhdsUniv** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegra
l.FTCFilter`。
形式化陈述：nhdsUniv (a : Real) : FTCFilter a (𝓝[univ] a) (𝓝 a)
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
instance nhdsUniv (a : ℝ) : FTCFilter a (𝓝[univ] a) (𝓝 a) := by rw [nhdsWithin_univ]; infer_instance
/-
**intervalIntegral.FTCFilter.nhdsLeft** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegra
l.FTCFilter`。
形式化陈述：nhdsLeft (a : Real) : FTCFilter a (𝓝[<=] a) (𝓝[<=] a) where pure_le
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
instance nhdsLeft (a : ℝ) : FTCFilter a (𝓝[≤] a) (𝓝[≤] a) where
  pure_le := pure_le_nhdsWithin self_mem_Iic
  le_nhds := inf_le_left
/-
**intervalIntegral.FTCFilter.nhdsRight** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegr
al.FTCFilter`。
形式化陈述：nhdsRight (a : Real) : FTCFilter a (𝓝[>=] a) (𝓝[>] a) where pure_le
参数：a : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
instance nhdsRight (a : ℝ) : FTCFilter a (𝓝[≥] a) (𝓝[>] a) where
  pure_le := pure_le_nhdsWithin self_mem_Ici
  le_nhds := inf_le_left
/-
**intervalIntegral.FTCFilter.nhdsIcc** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegral
.FTCFilter`。
形式化陈述：nhdsIcc {x a b : Real} [h : Fact (x in Icc a b)] : FTCFilter x (𝓝[Icc a b]
 x) (𝓝[Icc a b] x) where pure_le
参数：x in Icc a b。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
instance nhdsIcc {x a b : ℝ} [h : Fact (x ∈ Icc a b)] :
    FTCFilter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) where
  pure_le := pure_le_nhdsWithin h.out
  le_nhds := inf_le_left
/-
**intervalIntegral.FTCFilter.nhdsUIcc** 是 Mathlib 中的一个实例，位于命名空间 `intervalIntegra
l.FTCFilter`。
形式化陈述：nhdsUIcc {x a b : Real} [h : Fact (x in [[a, b]])] : FTCFilter x (𝓝[[[a, b
]]] x) (𝓝[[[a, b]]] x)
参数：x in [[a, b]]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nhdsUIcc {x a b : ℝ} [h : Fact (x ∈ [[a, b]])] :
    FTCFilter x (𝓝[[[a, b]]] x) (𝓝[[[a, b]]] x) :=
  .nhdsIcc (h := h)

end FTCFilter

section

variable {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι}
  {μ : Measure ℝ} {u v ua va ub vb : ι → ℝ}

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l' ⊓ ae μ`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.  The primed version
also works, e.g., for `l = l' = atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae'** 是 Math
lib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerate
d l'] [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ) (hf :
 Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l) (
hv : Tendsto v lt l) : (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c 
∂μ) =o[lt] fun t => ∫ _ in u t..v t, (1 : Real) ∂μ
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hl :
 μ.FiniteAtFilter l'；hu : Tendsto u lt l；hv : Tendsto v lt l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.integral_sub_linear_isLittleO_ae`：Filter.Tendsto.integral
_sub_linear_isLittleO_ae {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated
] {f : X -> E} {b : E} (h : Tendsto f…
· 使用定理 `Filter.Tendsto.Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
{l₁ l₂ : Filter α} [Filter.TendstoIxxClass Set.Ioc l₁ l₂]   {lb : Filter β} {u₁ 
u₂ : β →…
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const'`：integral_const' [CompleteSpace E] (c :
 E) : ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.IsLittleO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsLittleO.trans_le`：∀ {α : Type u_1} {E : Type u_3} {F : Typ
e u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {f :
 α → E} {g : α → F} …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
.0.intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae'._abel_1
_1`：∀ {ι : Type u_2} {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Norm
edSpace ℝ E] {f : ℝ → E} {c : E}   {μ : MeasureTheory.Measure ℝ}…
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l' ⊓ ae μ`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1
 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae` for a version ass
uming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure
 μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. 
 The primed version
also works, e.g., for `l = l' = atTop`.

We use integrals of constants instead of measures because this way it is easier 
to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  by_cases hE : CompleteSpace E; swap
  · simp [intervalIntegral, integral, hE]
  have A := hf.integral_sub_linear_isLittleO_ae hfm hl (hu.Ioc hv)
  have B := hf.integral_sub_linear_isLittleO_ae hfm hl (hv.Ioc hu)
  simp_rw [integral_const', sub_smul]
  refine ((A.trans_le fun t ↦ ?_).sub (B.trans_le fun t ↦ ?_)).congr_left fun t ↦ ?_
  · cases le_total (u t) (v t) <;> simp [*]
  · cases le_total (u t) (v t) <;> simp [*]
  · simp_rw [intervalIntegral]
    abel

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.  The primed version
also works, e.g., for `l = l' = Filter.atTop`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'** 
是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' [CompleteSpace 
E] [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurab
leAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l')
 (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u <=ᶠ[lt] v) : (fun t => (∫ 
x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t => μ.real (I
oc (u t) (v t))
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hl :
 μ.FiniteAtFilter l'；hu : Tendsto u lt l；hv : Tendsto v lt l；huv : u <=ᶠ[lt] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae'`：m
easure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l'] [
TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_const'`：integral_const' [CompleteSpace E] (c :
 E) : ∫ _ in a..b, c ∂μ = (μ.real (Ioc a b) - μ.real (Ioc b a)) • c
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as b
oth
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le` for a versi
on assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure
 μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. 
 The primed version
also works, e.g., for `l = l' = Filter.atTop`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf hl hu hv).congr'
    (huv.mono fun x hx => by simp [integral_const', hx])
    (huv.mono fun x hx => by simp [integral_const', hx])

/-- **Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. The primed version
also works, e.g., for `l = l' = Filter.atTop`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'** 
是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' [CompleteSpace 
E] [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurab
leAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l')
 (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v <=ᶠ[lt] u) : (fun t => (∫ 
x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t => μ.real (I
oc (v t) (u t))
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hl :
 μ.FiniteAtFilter l'；hu : Tendsto u lt l；hv : Tendsto v lt l；huv : v <=ᶠ[lt] u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_
le'`：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' [CompleteSpace E
] [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l'] (hfm : St…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.
Let filters `l` and `l'` be related by `TendstoIxxClass Ioc`.
If `f` has a finite limit `c` at `l ⊓ ae μ`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as 
both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version as
suming
`[intervalIntegral.FTCFilter a l l']` and `[MeasureTheory.IsLocallyFiniteMeasure
 μ]`. If `l` is one
of `𝓝[≥] a`, `𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version. 
The primed version
also works, e.g., for `l = l' = Filter.atTop`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'
    [CompleteSpace E] [IsMeasurablyGenerated l']
    [TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter f l' μ)
    (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hl : μ.FiniteAtFilter l') (hu : Tendsto u lt l)
    (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  (measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf hl hv hu
          huv).neg_left.congr_left
    fun t => by simp [integral_symm (u t), add_comm]

section IsLocallyFiniteMeasure

variable [IsLocallyFiniteMeasure μ]

variable [FTCFilter a la la'] [FTCFilter b lb lb']

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae'` for a version that also works, e.g.,
for `l = l' = Filter.atTop`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae** 是 Mathl
ib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l'] (hf
m : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)) (hu : 
Tendsto u lt l) (hv : Tendsto v lt l) : (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ 
_ in u t..v t, c ∂μ) =o[lt] fun t => ∫ _ in u t..v t, (1 : Real) ∂μ
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hu :
 Tendsto u lt l；hv : Tendsto v lt l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae'`：m
easure_integral_sub_linear_isLittleO_of_tendsto_ae' [IsMeasurablyGenerated l'] [
TendstoIxxClass Ioc l l'] (hfm : StronglyMeasurableAtFilter…
· 使用定理 `intervalIntegral.FTCFilter.meas_gen`：∀ {a : outParam ℝ} (outer : Filter 
ℝ) {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inne
r],   inner.IsMeasurablyG…
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `intervalIntegral.FTCFilter.finiteAt_inner`：finiteAt_inner {a : Real} (l 
: Filter Real) {l'} [h : FTCFilter a l l'] {μ : Measure Real} [IsLocallyFiniteMe
asure μ] : μ.FiniteAtFilter l'

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; le
t `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and
 `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae'` for a version th
at also works, e.g.,
for `l = l' = Filter.atTop`.

We use integrals of constants instead of measures because this way it is easier 
to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt] fun t =>
      ∫ _ in u t..v t, (1 : ℝ) ∂μ :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae' hfm hf (FTCFilter.finiteAt_inner l) hu hv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le** 是
 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le [CompleteSpace E
] [FTCFilter a l l'] (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (
l' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u <=ᶠ[lt] v
) : (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] f
un t => μ.real (Ioc (u t) (v t))
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hu :
 Tendsto u lt l；hv : Tendsto v lt l；huv : u <=ᶠ[lt] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_
le'`：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' [CompleteSpace E
] [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l'] (hfm : St…
· 使用定理 `intervalIntegral.FTCFilter.meas_gen`：∀ {a : outParam ℝ} (outer : Filter 
ℝ) {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inne
r],   inner.IsMeasurablyG…
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `intervalIntegral.FTCFilter.finiteAt_inner`：finiteAt_inner {a : Real} (l 
: Filter Real) {l'} [h : FTCFilter a l l'] {μ : Measure Real} [IsLocallyFiniteMe
asure μ] : μ.FiniteAtFilter l'

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; le
t `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend
 to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le'` for a vers
ion that also works,
e.g., for `l = l' = Filter.atTop`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
    (fun t => (∫ x in u t..v t, f x ∂μ) - μ.real (Ioc (u t) (v t)) • c) =o[lt] fun t =>
      μ.real (Ioc (u t) (v t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_le' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; let `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = -μ (Set.Ioc v u) • c + o(μ(Set.Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = Filter.atTop`. -/
/-
**intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge** 是
 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge [CompleteSpace E
] [FTCFilter a l l'] (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (
l' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v <=ᶠ[lt] u
) : (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] f
un t => μ.real (Ioc (v t) (u t))
参数：hfm : StronglyMeasurableAtFilter f l' μ；hf : Tendsto f (l' ⊓ ae μ) (𝓝 c)；hu :
 Tendsto u lt l；hv : Tendsto v lt l；huv : v <=ᶠ[lt] u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_
ge'`：measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' [CompleteSpace E
] [IsMeasurablyGenerated l'] [TendstoIxxClass Ioc l l'] (hfm : St…
· 使用定理 `intervalIntegral.FTCFilter.meas_gen`：∀ {a : outParam ℝ} (outer : Filter 
ℝ) {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inne
r],   inner.IsMeasurablyG…
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `intervalIntegral.FTCFilter.finiteAt_inner`：finiteAt_inner {a : Real} (l 
: Filter Real) {l'} [h : FTCFilter a l l'] {μ : Measure Real} [IsLocallyFiniteMe
asure μ] : μ.FiniteAtFilter l'

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version for any measure.

Let filters `l` and `l'` be related by `[intervalIntegral.FTCFilter a l l']`; le
t `μ` be a locally
finite measure.  If `f` has a finite limit `c` at `l' ⊓ ae μ`, then
`∫ x in u..v, f x ∂μ = -μ (Set.Ioc v u) • c + o(μ(Set.Ioc v u))` as both `u` and
 `v` tend to `l`.

See also `measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge'` for a vers
ion that also works,
e.g., for `l = l' = Filter.atTop`.
-/
theorem measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge
    [CompleteSpace E] [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ) (𝓝 c))
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
    (fun t => (∫ x in u t..v t, f x ∂μ) + μ.real (Ioc (v t) (u t)) • c) =o[lt] fun t =>
      μ.real (Ioc (v t) (u t)) :=
  haveI := FTCFilter.meas_gen l
  measure_integral_sub_linear_isLittleO_of_tendsto_ae_of_ge' hfm hf (FTCFilter.finiteAt_inner l) hu
    hv huv

/-- **Fundamental theorem of calculus-1**, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `intervalIntegral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and `lb' ⊓ ae μ`,
respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
/-
**intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto
_ae** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab : In
tervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f la' μ) (hmeas_
b : StronglyMeasurableAtFilter f lb' μ) (ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝 ca))
 (hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendst
o va lt la) (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) : (fun t => ((∫ x 
in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) - ((∫ _ in ub t..vb t, cb ∂μ
) - ∫ _ in ua t..va t, ca 
参数：hab : IntervalIntegrable f μ a b；hmeas_a : StronglyMeasurableAtFilter f la' μ
；hmeas_b : StronglyMeasurableAtFilter f lb' μ；ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝
 ca)；hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)；hua : Tendsto ua lt la；hva : Tendsto
 va lt la；hub : Tendsto ub lt lb；hvb : Tendsto vb lt lb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.FTCFilter.meas_gen`：∀ {a : outParam ℝ} (outer : Filter 
ℝ) {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inne
r],   inner.IsMeasurablyG…
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.add_add`：∀ {α : Type u_1} {E' : Type u_6} {F' : Ty
pe u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'] 
  {l : Filter α} {f…
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae`：me
asure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l'] (hfm : Stro
nglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ)…
· 使用定理 `Filter.Tendsto.eventually_intervalIntegrable_ae`：Filter.Tendsto.eventual
ly_intervalIntegrable_ae {f : Real -> E} {μ : Measure Real} {l l' : Filter Real}
 (hfm : StronglyMeasurableAtFilter f …
· 使用定理 `intervalIntegral.FTCFilter.toTendstoIxxClass`：∀ {a : outParam ℝ} {outer 
: Filter ℝ} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a o
uter inner],   Filter.TendstoIxxCl…
· 使用定理 `intervalIntegral.FTCFilter.finiteAt_inner`：finiteAt_inner {a : Real} (l 
: Filter Real) {l'} [h : FTCFilter a l l'] {μ : Measure Real} [IsLocallyFiniteMe
asure μ] : μ.FiniteAtFilter l'
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
· 使用定理 `intervalIntegral.FTCFilter.pure_le`：∀ {a : outParam ℝ} {outer : Filter ℝ
} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inner
],   pure a ≤ outer
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_interval_sub_interval_comm'`：integral_interval
_sub_interval_comm' (hab : IntervalIntegrable f μ a b) (hcd : IntervalIntegrable
 f μ c d) (hac : IntervalIntegrable f μ a c…
· 使用定理 `IntervalIntegrable.trans`：trans {a b c : Real} (hab : IntervalIntegrable
 f μ a b) (hbc : IntervalIntegrable f μ b c) : IntervalIntegrable f μ a c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
.0.intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_tendst
o_ae._abel_1_1`：∀ {ι : Type u_2} {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] {f : ℝ → E} {ca cb : E}   {μ : MeasureTheory.Measur…
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict derivative in both limits for a lo
cally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair
 of
`intervalIntegral.FTCFilter`s around `a`; let `(lb, lb')` be a pair of `interval
Integral.FTCFilter`s
around `b`. Suppose that `f` has finite limits `ca` and `cb` at `la' ⊓ ae μ` and
 `lb' ⊓ ae μ`,
respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(‖∫ x in ua..va, (1:ℝ) ∂μ‖ + ‖∫ x in ub..vb, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f la' μ)
    (hmeas_b : StronglyMeasurableAtFilter f lb' μ) (ha_lim : Tendsto f (la' ⊓ ae μ) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae μ) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x ∂μ) - ∫ x in ua t..ub t, f x ∂μ) -
          ((∫ _ in ub t..vb t, cb ∂μ) - ∫ _ in ua t..va t, ca ∂μ)) =o[lt]
      fun t => ‖∫ _ in ua t..va t, (1 : ℝ) ∂μ‖ + ‖∫ _ in ub t..vb t, (1 : ℝ) ∂μ‖ := by
  have := FTCFilter.meas_gen la; have := FTCFilter.meas_gen lb
  refine
    ((measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
          (measure_integral_sub_linear_isLittleO_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      ?_ EventuallyEq.rfl
  have A : ∀ᶠ t in lt, IntervalIntegrable f μ (ua t) (va t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la) hua hva
  have A' : ∀ᶠ t in lt, IntervalIntegrable f μ a (ua t) :=
    ha_lim.eventually_intervalIntegrable_ae hmeas_a (FTCFilter.finiteAt_inner la)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hua
  have B : ∀ᶠ t in lt, IntervalIntegrable f μ (ub t) (vb t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb) hub hvb
  have B' : ∀ᶠ t in lt, IntervalIntegrable f μ b (ub t) :=
    hb_lim.eventually_intervalIntegrable_ae hmeas_b (FTCFilter.finiteAt_inner lb)
      (tendsto_const_pure.mono_right FTCFilter.pure_le) hub
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub
  rw [← integral_interval_sub_interval_comm']
  · abel
  exacts [ub_vb, ua_va, b_ub.symm.trans <| hab.symm.trans a_ua]

/-- **Fundamental theorem of calculus-1**, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of
`intervalIntegral.FTCFilter`s around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ ae μ`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)` as
`u` and `v` tend to `lb`.
-/
/-
**intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto
_ae_right** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right (ha
b : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f lb' μ) (hf
 : Tendsto f (lb' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
 (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ _ in u t..v t, 
c ∂μ) =o[lt] fun t => ∫ _ in u t..v t, (1 : Real) ∂μ
参数：hab : IntervalIntegrable f μ a b；hmeas : StronglyMeasurableAtFilter f lb' μ；h
f : Tendsto f (lb' ⊓ ae μ) (𝓝 c)；hu : Tendsto u lt lb；hv : Tendsto v lt lb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_t
endsto_ae`：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab
 : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f …
· 使用定理 `stronglyMeasurableAt_bot`：stronglyMeasurableAt_bot {f : α -> β} : Strong
lyMeasurableAtFilter f ⊥ μ
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict derivative in right endpoint for a
 locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair
 of
`intervalIntegral.FTCFilter`s around `b`. Suppose that `f` has a finite limit `c
` at `lb' ⊓ ae μ`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u
..v, (1:ℝ) ∂μ)` as
`u` and `v` tend to `lb`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f lb' μ)
    (hf : Tendsto f (lb' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x ∂μ) - ∫ x in a..u t, f x ∂μ) - ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab stronglyMeasurableAt_bot
      hmeas ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hf
      (tendsto_const_pure : Tendsto _ _ (pure a)) tendsto_const_pure hu hv

/-- **Fundamental theorem of calculus-1**, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`intervalIntegral.FTCFilter`s around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ ae μ`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
/-
**intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto
_ae_left** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left (hab
 : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f la' μ) (hf 
: Tendsto f (la' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) : 
(fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ _ in u t..v t, c
 ∂μ) =o[lt] fun t => ∫ _ in u t..v t, (1 : Real) ∂μ
参数：hab : IntervalIntegrable f μ a b；hmeas : StronglyMeasurableAtFilter f la' μ；h
f : Tendsto f (la' ⊓ ae μ) (𝓝 c)；hu : Tendsto u lt la；hv : Tendsto v lt la。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_t
endsto_ae`：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab
 : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f …
· 使用定理 `stronglyMeasurableAt_bot`：stronglyMeasurableAt_bot {f : α -> β} : Strong
lyMeasurableAtFilter f ⊥ μ
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict derivative in left endpoint for a 
locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair
 of
`intervalIntegral.FTCFilter`s around `a`. Suppose that `f` has a finite limit `c
` at `la' ⊓ ae μ`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in 
u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
theorem measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter f la' μ)
    (hf : Tendsto f (la' ⊓ ae μ) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x ∂μ) - ∫ x in u t..b, f x ∂μ) + ∫ _ in u t..v t, c ∂μ) =o[lt]
      fun t => ∫ _ in u t..v t, (1 : ℝ) ∂μ := by
  simpa using
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas
      stronglyMeasurableAt_bot hf ((tendsto_bot : Tendsto _ ⊥ (𝓝 (0 : E))).mono_left inf_le_left) hu
      hv (tendsto_const_pure : Tendsto _ _ (pure b)) tendsto_const_pure

end IsLocallyFiniteMeasure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/


variable [CompleteSpace E]
  {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : Filter ℝ} {lt : Filter ι} {a b : ℝ}
  {u v ua ub va vb : ι → ℝ} [FTCFilter a la la'] [FTCFilter b lb lb']

/-!
#### Auxiliary `Asymptotics.IsLittleO` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use
`Asymptotics.isLittleO` because we have no definition of `HasStrict(F)DerivAtFilter` in the library.
-/


/-- **Fundamental theorem of calculus-1**, local version.

If `f` has a finite limit `c` almost surely at `l'`, where `(l, l')` is an
`intervalIntegral.FTCFilter` pair around `a`, then `∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)`
as both `u` and `v` tend to `l`. -/
/-
**intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae** 是 Mathlib 中的一个定
理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l'] (hfm : Stro
nglyMeasurableAtFilter f l') (hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)) {u v : ι ->
 Real} (hu : Tendsto u lt l) (hv : Tendsto v lt l) : (fun t => (∫ x in u t..v t,
 f x) - (v t - u t) • c) =o[lt] (v - u)
参数：hfm : StronglyMeasurableAtFilter f l'；hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)；h
u : Tendsto u lt l；hv : Tendsto v lt l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.measure_integral_sub_linear_isLittleO_of_tendsto_ae`：me
asure_integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l'] (hfm : Stro
nglyMeasurableAtFilter f l' μ) (hf : Tendsto f (l' ⊓ ae μ)…

--- 原说明 ---
**Fundamental theorem of calculus-1**, local version.

If `f` has a finite limit `c` almost surely at `l'`, where `(l, l')` is an
`intervalIntegral.FTCFilter` pair around `a`, then `∫ x in u..v, f x ∂μ = (v - u
) • c + o (v - u)`
as both `u` and `v` tend to `l`.
-/
theorem integral_sub_linear_isLittleO_of_tendsto_ae [FTCFilter a l l']
    (hfm : StronglyMeasurableAtFilter f l') (hf : Tendsto f (l' ⊓ ae volume) (𝓝 c)) {u v : ι → ℝ}
    (hu : Tendsto u lt l) (hv : Tendsto v lt l) :
    (fun t => (∫ x in u t..v t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa [integral_const] using! measure_integral_sub_linear_isLittleO_of_tendsto_ae hfm hf hu hv

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `intervalIntegral.FTCFilter`
pair around `a`, and `(lb, lb')` is an `intervalIntegral.FTCFilter` pair around `b`, and `f` has
finite limits `ca` and `cb` almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(‖va - ua‖ + ‖vb - ub‖)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `HasStrictFDerivAtFilter` if we had this
definition. -/
/-
**intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae** 是 
Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab : IntervalIn
tegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la') (hmeas_b : S
tronglyMeasurableAtFilter f lb') (ha_lim : Tendsto f (la' ⊓ ae volume) (𝓝 ca)) (
hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Ten
dsto va lt la) (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) : (fun t => ((∫
 x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) - ((vb t - ub t) • cb - (va t -
 ua t) • ca)) =o[lt] fun t
参数：hab : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f 
la'；hmeas_b : StronglyMeasurableAtFilter f lb'；ha_lim : Tendsto f (la' ⊓ ae volu
me) (𝓝 ca)；hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)；hua : Tendsto ua lt la；hv
a : Tendsto va lt la；hub : Tendsto ub lt lb；hvb : Tendsto vb lt lb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_t
endsto_ae`：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab
 : IntervalIntegrable f μ a b) (hmeas_a : StronglyMeasurableAtFilter f …

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability at filter in bot
h endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `interva
lIntegral.FTCFilter`
pair around `a`, and `(lb, lb')` is an `intervalIntegral.FTCFilter` pair around 
`b`, and `f` has
finite limits `ca` and `cb` almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(‖va - ua‖ + ‖vb - ub‖)` as `ua` and `va` tend to `la` while `ub` and `vb` te
nd to `lb`.

This lemma could've been formulated using `HasStrictFDerivAtFilter` if we had th
is
definition.
-/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
    (hab : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la')
    (hmeas_b : StronglyMeasurableAtFilter f lb') (ha_lim : Tendsto f (la' ⊓ ae volume) (𝓝 ca))
    (hb_lim : Tendsto f (lb' ⊓ ae volume) (𝓝 cb)) (hua : Tendsto ua lt la) (hva : Tendsto va lt la)
    (hub : Tendsto ub lt lb) (hvb : Tendsto vb lt lb) :
    (fun t =>
        ((∫ x in va t..vb t, f x) - ∫ x in ua t..ub t, f x) -
          ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt]
      fun t => ‖va t - ua t‖ + ‖vb t - ub t‖ := by
  simpa [integral_const]
    using measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hab hmeas_a hmeas_b
      ha_lim hb_lim hua hva hub hvb

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `intervalIntegral.FTCFilter`
pair around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had this definition. -/
/-
**intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_righ
t** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right (hab : Inte
rvalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f lb') (hf : Te
ndsto f (lb' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
 (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt]
 (v - u)
参数：hab : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f lb
'；hf : Tendsto f (lb' ⊓ ae volume) (𝓝 c)；hu : Tendsto u lt lb；hv : Tendsto v lt 
lb。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_t
endsto_ae_right`：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_a
e_right (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilte…

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability at filter in bot
h endpoints.

If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `interva
lIntegral.FTCFilter`
pair around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(‖v - u‖)` as `u` and `v
` tend to `lb`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had thi
s definition.
-/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f lb')
    (hf : Tendsto f (lb' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt lb) (hv : Tendsto v lt lb) :
    (fun t => ((∫ x in a..v t, f x) - ∫ x in a..u t, f x) - (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using!
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hab hmeas hf hu hv

/-- **Fundamental theorem of calculus-1**, strict differentiability at filter in both endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `intervalIntegral.FTCFilter`
pair around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had this definition. -/
/-
**intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left (hab : Inter
valIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f la') (hf : Ten
dsto f (la' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) : 
(fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] 
(v - u)
参数：hab : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f la
'；hf : Tendsto f (la' ⊓ ae volume) (𝓝 c)；hu : Tendsto u lt la；hv : Tendsto v lt 
la。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_const`：integral_const [CompleteSpace E] (c : E
) : ∫ _ in a..b, c = (b - a) • c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_t
endsto_ae_left`：measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae
_left (hab : IntervalIntegrable f μ a b) (hmeas : StronglyMeasurableAtFilter…

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability at filter in bot
h endpoints.

If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `interva
lIntegral.FTCFilter`
pair around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(‖v - u‖)` as `u` and `
v` tend to `la`.

This lemma could've been formulated using `HasStrictDerivAtFilter` if we had thi
s definition.
-/
theorem integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left
    (hab : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f la')
    (hf : Tendsto f (la' ⊓ ae volume) (𝓝 c)) (hu : Tendsto u lt la) (hv : Tendsto v lt la) :
    (fun t => ((∫ x in v t..b, f x) - ∫ x in u t..b, f x) + (v t - u t) • c) =o[lt] (v - u) := by
  simpa only [integral_const, smul_eq_mul, mul_one] using!
    measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_left hab hmeas hf hu hv

open ContinuousLinearMap (fst snd smulRight sub_apply smulRight_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_hasStrictFDerivAt_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tends to `a` and `b`,
  respectively;

* `integral_hasStrictFDerivAt`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_hasStrictDerivAt_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_hasStrictDerivAt_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_hasStrictDerivAt_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/


/-- **Fundamental theorem of calculus-1**, strict differentiability in both endpoints.

If `f : ℝ → E` is integrable on `a..b` and `f x` has finite limits `ca` and `cb` almost surely as
`x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictFDerivAt_of_tendsto_ae** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：integral_hasStrictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume
 a b) (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurab
leAtFilter f (𝓝 b)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝
 b ⊓ ae volume) (𝓝 cb)) : HasStrictFDerivAt (fun p : Real × Real => ∫ x in p.1..
p.2, f x) ((snd Real Real Real).smulRight cb - (fst Real Real Real).smulRight ca
) (a, b)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : Tendsto f (𝓝 a ⊓ ae volum
e) (𝓝 ca)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_a
e`：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab : IntervalInteg
rable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la'…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `HasStrictFDerivAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in both endpoint
s.

If `f : ℝ → E` is integrable on `a..b` and `f x` has finite limits `ca` and `cb`
 almost surely as
`x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)
`
in the sense of strict differentiability.
-/
theorem integral_hasStrictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) := by
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (continuous_snd.fst.tendsto ((a, b), (a, b)))
      (continuous_fst.fst.tendsto ((a, b), (a, b)))
      (continuous_snd.snd.tendsto ((a, b), (a, b)))
      (continuous_fst.snd.tendsto ((a, b), (a, b)))
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

/-- **Fundamental theorem of calculus-1**, strict differentiability in both endpoints.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a` and `b`, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of
strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_hasStrictFDerivAt (hf : IntervalIntegrable f volume a b) (hmeas_a
 : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (
𝓝 b)) (ha : ContinuousAt f a) (hb : ContinuousAt f b) : HasStrictFDerivAt (fun p
 : Real × Real => ∫ x in p.1..p.2, f x) ((snd Real Real Real).smulRight (f b) - 
(fst Real Real Real).smulRight (f a)) (a, b)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : ContinuousAt f a；hb : Con
tinuousAt f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_hasStrictFDerivAt_of_tendsto_ae`：integral_hasS
trictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b) (hmeas_a : St
ronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : St…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in both endpoint
s.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a` and `b`, the
n
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)
` in the sense of
strict differentiability.
-/
theorem integral_hasStrictFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `b`, then
`u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense of strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right** 是 Mathlib 中的一
个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f v
olume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ a
e volume) (𝓝 c)) : HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasFDerivAtFilter.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_a
e_right`：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right (hab : I
ntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f…
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in the right end
point.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost s
urely at `b`, then
`u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in the sense of strict differen
tiability.
-/
theorem integral_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b :=
  .of_isLittleO <|
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb continuousAt_snd
      continuousAt_fst

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `b`, then `u ↦ ∫ x in a..u, f x` has
derivative `f b` at `b` in the sense of strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictDerivAt_right** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_hasStrictDerivAt_right (hf : IntervalIntegrable f volume a b) (hm
eas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) : HasStrictDer
ivAt (fun u => ∫ x in a..u, f x) (f b) b
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : ContinuousAt f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right`：integral
_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) (hm
eas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tend…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in the right end
point.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `b`, then `u ↦ ∫
 x in a..u, f x` has
derivative `f b` at `b` in the sense of strict differentiability.
-/
theorem integral_hasStrictDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- **Fundamental theorem of calculus-1**, strict differentiability in the left endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost surely at `a`, then
`u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense of strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_left** 是 Mathlib 中的一个
定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f vo
lume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae
 volume) (𝓝 c)) : HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasStrictDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f
 : 𝕜 → F} {f' …
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right`：integral
_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) (hm
eas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tend…
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in the left endp
oint.

If `f : ℝ → E` is integrable on `a..b` and `f x` has a finite limit `c` almost s
urely at `a`, then
`u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense of strict differe
ntiability.
-/
theorem integral_hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-c) a := by
  simpa only [← integral_symm] using
    (integral_hasStrictDerivAt_of_tendsto_ae_right hf.symm hmeas ha).fun_neg

/-- **Fundamental theorem of calculus-1**, strict differentiability in the left endpoint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a`, then `u ↦ ∫ x in u..b, f x` has
derivative `-f a` at `a` in the sense of strict differentiability. -/
/-
**intervalIntegral.integral_hasStrictDerivAt_left** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：integral_hasStrictDerivAt_left (hf : IntervalIntegrable f volume a b) (hme
as : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) : HasStrictDeri
vAt (fun u => ∫ x in u..b, f x) (-f a) a
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；ha : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasStrictDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f
 : 𝕜 → F} {f' …
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_right`：integral_hasStrictDeri
vAt_right (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFi
lter f (𝓝 b)) (hb : ContinuousAt f b) …
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in the left endp
oint.

If `f : ℝ → E` is integrable on `a..b` and `f` is continuous at `a`, then `u ↦ ∫
 x in u..b, f x` has
derivative `-f a` at `a` in the sense of strict differentiability.
-/
theorem integral_hasStrictDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasStrictDerivAt (fun u => ∫ x in u..b, f x) (-f a) a := by
  simpa only [← integral_symm] using (integral_hasStrictDerivAt_right hf.symm hmeas ha).fun_neg

/-- **Fundamental theorem of calculus-1**, strict differentiability in the right endpoint.

If `f : ℝ → E` is continuous, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense
of strict differentiability. -/
/-
**intervalIntegral._root_.Continuous.integral_hasStrictDerivAt** 是 Mathlib 中的一个定
理，位于命名空间 `intervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Fundamental theorem of calculus-1**, strict differentiability in the right end
point.

If `f : ℝ → E` is continuous, then `u ↦ ∫ x in a..u, f x` has derivative `f b` a
t `b` in the sense
of strict differentiability.
-/
theorem _root_.Continuous.integral_hasStrictDerivAt {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    HasStrictDerivAt (fun u => ∫ x : ℝ in a..u, f x) (f b) b :=
  integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
    hf.continuousAt

/-- **Fundamental theorem of calculus-1**, derivative in the right endpoint.

If `f : ℝ → E` is continuous, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` is `f b`. -/
/-
**intervalIntegral._root_.Continuous.deriv_integral** 是 Mathlib 中的一个定理，位于命名空间 `i
ntervalIntegral`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Fundamental theorem of calculus-1**, derivative in the right endpoint.

If `f : ℝ → E` is continuous, then the derivative of `u ↦ ∫ x in a..u, f x` at `
b` is `f b`.
-/
theorem _root_.Continuous.deriv_integral (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u => ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `HasFDerivAt`,
`HasDerivAt`, `fderiv`, and `deriv`.
-/


/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
/-
**intervalIntegral.integral_hasFDerivAt_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：integral_hasFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b) 
(hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFi
lter f (𝓝 b)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ a
e volume) (𝓝 cb)) : HasFDerivAt (fun p : Real × Real => ∫ x in p.1..p.2, f x) ((
snd Real Real Real).smulRight cb - (fst Real Real Real).smulRight ca) (a, b)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : Tendsto f (𝓝 a ⊓ ae volum
e) (𝓝 ca)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_hasStrictFDerivAt_of_tendsto_ae`：integral_hasS
trictFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b) (hmeas_a : St
ronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : St…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectiv
ely, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)
`.
-/
theorem integral_hasFDerivAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (a, b) :=
  (integral_hasStrictFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u •
ca` at `(a, b)`. -/
/-
**intervalIntegral.integral_hasFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：integral_hasFDerivAt (hf : IntervalIntegrable f volume a b) (hmeas_a : Str
onglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)) 
(ha : ContinuousAt f a) (hb : ContinuousAt f b) : HasFDerivAt (fun p : Real × Re
al => ∫ x in p.1..p.2, f x) ((snd Real Real Real).smulRight (f b) - (fst Real Re
al Real).smulRight (f a)) (a, b)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : ContinuousAt f a；hb : Con
tinuousAt f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_hasStrictFDerivAt`：integral_hasStrictFDerivAt 
(hf : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)) (hmeas_b : StronglyMeasurab…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f` is
continuous at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, 
v) ↦ v • cb - u •
ca` at `(a, b)`.
-/
theorem integral_hasFDerivAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (a, b) :=
  (integral_hasStrictFDerivAt hf hmeas_a hmeas_b ha hb).hasFDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
/-
**intervalIntegral.fderiv_integral_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间 `inte
rvalIntegral`。
形式化陈述：fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b) (hmea
s_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter 
f (𝓝 b)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae vol
ume) (𝓝 cb)) : fderiv Real (fun p : Real × Real => ∫ x in p.1..p.2, f x) (a, b) 
= (snd Real Real Real).smulRight cb - (fst Real Real Real).smulRight ca
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : Tendsto f (𝓝 a ⊓ ae volum
e) (𝓝 ca)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `intervalIntegral.integral_hasFDerivAt_of_tendsto_ae`：integral_hasFDerivA
t_of_tendsto_ae (hf : IntervalIntegrable f volume a b) (hmeas_a : StronglyMeasur
ableAtFilter f (𝓝 a)) (hmeas_b : Strongly…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f x` has
finite limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectiv
ely, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - 
u • ca`.
-/
theorem fderiv_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 cb)) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)`
equals `(u, v) ↦ v • cb - u • ca`. -/
/-
**intervalIntegral.fderiv_integral** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegral`。
形式化陈述：fderiv_integral (hf : IntervalIntegrable f volume a b) (hmeas_a : Strongly
MeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)) (ha :
 ContinuousAt f a) (hb : ContinuousAt f b) : fderiv Real (fun p : Real × Real =>
 ∫ x in p.1..p.2, f x) (a, b) = (snd Real Real Real).smulRight (f b) - (fst Real
 Real Real).smulRight (f a)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f (
𝓝 a)；hmeas_b : StronglyMeasurableAtFilter f (𝓝 b)；ha : ContinuousAt f a；hb : Con
tinuousAt f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `intervalIntegral.integral_hasFDerivAt`：integral_hasFDerivAt (hf : Interv
alIntegrable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas
_b : StronglyMeasurableAtFi…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f` is
continuous at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f 
x` at `(a, b)`
equals `(u, v) ↦ v • cb - u • ca`.
-/
theorem fderiv_integral (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f (𝓝 a)) (hmeas_b : StronglyMeasurableAtFilter f (𝓝 b))
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) :
    fderiv ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (a, b) =
      (snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a) :=
  (integral_hasFDerivAt hf hmeas_a hmeas_b ha hb).fderiv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
/-
**intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_hasDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume 
a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volu
me) (𝓝 c)) : HasDerivAt (fun u => ∫ x in a..u, f x) c b
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_right`：integral
_hasStrictDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) (hm
eas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tend…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f x` has a
finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivativ
e `c` at `b`.
-/
theorem integral_hasDerivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in a..u, f x) c b :=
  (integral_hasStrictDerivAt_of_tendsto_ae_right hf hmeas hb).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
/-
**intervalIntegral.integral_hasDerivAt_right** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b) (hmeas : 
StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) : HasDerivAt (fun u 
=> ∫ x in a..u, f x) (f b) b
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : ContinuousAt f b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_right`：integral_hasStrictDeri
vAt_right (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFi
lter f (𝓝 b)) (hb : ContinuousAt f b) …

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f` is
continuous at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`.
-/
theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b :=
  (integral_hasStrictDerivAt_right hf hmeas hb).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
/-
**intervalIntegral.deriv_integral_of_tendsto_ae_right** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) 
(hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (
𝓝 c)) : deriv (fun u => ∫ x in a..u, f x) b = c
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right`：integral_hasDe
rivAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) (hmeas : Strong
lyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f …

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` 
has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at
 `b` equals `c`.
-/
theorem deriv_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in a..u, f x) b = c :=
  (integral_hasDerivAt_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
/-
**intervalIntegral.deriv_integral_right** 是 Mathlib 中的一个定理，位于命名空间 `intervalInteg
ral`。
形式化陈述：deriv_integral_right (hf : IntervalIntegrable f volume a b) (hmeas : Stron
glyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) : deriv (fun u => ∫ x in 
a..u, f x) b = f b
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
b)；hb : ContinuousAt f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `intervalIntegral.integral_hasDerivAt_right`：integral_hasDerivAt_right (h
f : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b)
) (hb : ContinuousAt f b) : HasD…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` 
is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`.
-/
theorem deriv_integral_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    deriv (fun u => ∫ x in a..u, f x) b = f b :=
  (integral_hasDerivAt_right hf hmeas hb).deriv

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f x` has a
finite limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
/-
**intervalIntegral.integral_hasDerivAt_of_tendsto_ae_left** 是 Mathlib 中的一个定理，位于命
名空间 `intervalIntegral`。
形式化陈述：integral_hasDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a
 b) (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volum
e) (𝓝 c)) : HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_of_tendsto_ae_left`：integral_
hasStrictDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) (hmea
s : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tends…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f x` has a
finite limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivativ
e `-c` at `a`.
-/
theorem integral_hasDerivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-c) a :=
  (integral_hasStrictDerivAt_of_tendsto_ae_left hf hmeas ha).hasDerivAt

/-- **Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` and `f` is
continuous at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
/-
**intervalIntegral.integral_hasDerivAt_left** 是 Mathlib 中的一个定理，位于命名空间 `intervalI
ntegral`。
形式化陈述：integral_hasDerivAt_left (hf : IntervalIntegrable f volume a b) (hmeas : S
tronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) : HasDerivAt (fun u =
> ∫ x in u..b, f x) (-f a) a
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；ha : ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `intervalIntegral.integral_hasStrictDerivAt_left`：integral_hasStrictDeriv
At_left (hf : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilt
er f (𝓝 a)) (ha : ContinuousAt f a) :…

--- 原说明 ---
**Fundamental theorem of calculus-1**: if `f : ℝ → E` is integrable on `a..b` an
d `f` is
continuous at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`.
-/
theorem integral_hasDerivAt_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (ha : ContinuousAt f a) :
    HasDerivAt (fun u => ∫ x in u..b, f x) (-f a) a :=
  (integral_hasStrictDerivAt_left hf hmeas ha).hasDerivAt

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
/-
**intervalIntegral.deriv_integral_of_tendsto_ae_left** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) (
hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝
 c)) : deriv (fun u => ∫ x in u..b, f x) a = -c
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `intervalIntegral.integral_hasDerivAt_of_tendsto_ae_left`：integral_hasDer
ivAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) (hmeas : Strongly
MeasurableAtFilter f (𝓝 a)) (ha : Tendsto f (…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` 
has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at
 `a` equals `-c`.
-/
theorem deriv_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : Tendsto f (𝓝 a ⊓ ae volume) (𝓝 c)) :
    deriv (fun u => ∫ x in u..b, f x) a = -c :=
  (integral_hasDerivAt_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
/-
**intervalIntegral.deriv_integral_left** 是 Mathlib 中的一个定理，位于命名空间 `intervalIntegr
al`。
形式化陈述：deriv_integral_left (hf : IntervalIntegrable f volume a b) (hmeas : Strong
lyMeasurableAtFilter f (𝓝 a)) (hb : ContinuousAt f a) : deriv (fun u => ∫ x in u
..b, f x) a = -f a
参数：hf : IntervalIntegrable f volume a b；hmeas : StronglyMeasurableAtFilter f (𝓝 
a)；hb : ContinuousAt f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `intervalIntegral.integral_hasDerivAt_left`：integral_hasDerivAt_left (hf 
: IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) 
(ha : ContinuousAt f a) : HasDe…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` 
is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`.
-/
theorem deriv_integral_left (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 a)) (hb : ContinuousAt f a) :
    deriv (fun u => ∫ x in u..b, f x) a = -f a :=
  (integral_hasDerivAt_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/


/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
/-
**intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：integral_hasFDerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume
 a b) {s t : Set Real} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (hmea
s_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f l
b) (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 
cb)) : HasFDerivWithinAt (fun p : Real × Real => ∫ x in p.1..p.2, f x) ((snd Rea
l Real Real).smulRight cb - (fst Real Real Real).smulRight ca) (s ×ˢ t) (a, b)
参数：hf : IntervalIntegrable f volume a b；𝓝[s] a；𝓝[t] b；hmeas_a : StronglyMeasurab
leAtFilter f la；hmeas_b : StronglyMeasurableAtFilter f lb；ha : Tendsto f (la ⊓ a
e volume) (𝓝 ca)；hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_a
e`：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae (hab : IntervalInteg
rable f volume a b) (hmeas_a : StronglyMeasurableAtFilter f la'…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
· 使用定理 `intervalIntegral.FTCFilter.pure_le`：∀ {a : outParam ℝ} {outer : Filter ℝ
} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inner
],   pure a ≤ outer
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `HasFDerivWithinAt.of_isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {F : Typ…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.IsLittleO.congr_left`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {g : α → F} {l : Filter α}   {f₁ f₂ :
 α → E}, f₁ =o[l] g → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)

--- 原说明 ---
Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ 
x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided tha
t `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_hasFDerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca) (s ×ˢ t) (a, b) := by
  have :=
    integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae hf hmeas_a hmeas_b ha hb
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[s] a)) tendsto_fst
      (tendsto_const_pure.mono_right FTCFilter.pure_le : Tendsto _ _ (𝓝[t] b)) tendsto_snd
  rw [← nhdsWithin_prod_eq] at this
  refine .of_isLittleO <| (this.congr_left ?_).trans_isBigO ?_
  · simp [sub_smul]
  · exact isBigO_fst_prod.norm_left.add isBigO_snd_prod.norm_left

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `ContinuousAt f _` or `ContinuousWithinAt f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
/-
**intervalIntegral.integral_hasFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_hasFDerivWithinAt (hf : IntervalIntegrable f volume a b) (hmeas_a
 : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb) 
{s t : Set Real} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tends
to f la (𝓝 <| f a)) (hb : Tendsto f lb (𝓝 <| f b)) : HasFDerivWithinAt (fun p : 
Real × Real => ∫ x in p.1..p.2, f x) ((snd Real Real Real).smulRight (f b) - (fs
t Real Real Real).smulRight (f a)) (s ×ˢ t) (a, b)
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f l
a；hmeas_b : StronglyMeasurableAtFilter f lb；𝓝[s] a；𝓝[t] b；ha : Tendsto f la (𝓝 <
| f a)；hb : Tendsto f lb (𝓝 <| f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae`：integral_hasF
DerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b) {s t : Set Re
al} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ 
x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided tha
t `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most c
ases this assumption
is definitionally equal `ContinuousAt f _` or `ContinuousWithinAt f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem integral_hasFDerivWithinAt (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (ha : Tendsto f la (𝓝 <| f a))
    (hb : Tendsto f lb (𝓝 <| f b)) :
    HasFDerivWithinAt (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x)
      ((snd ℝ ℝ ℝ).smulRight (f b) - (fst ℝ ℝ ℝ).smulRight (f a)) (s ×ˢ t) (a, b) :=
  integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
    (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `UniqueDiffWithinAt ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
macro "uniqueDiffWithinAt_Ici_Iic_univ" : tactic =>
  `(tactic| (first | exact uniqueDiffOn_Ici _ _ self_mem_Ici |
    exact uniqueDiffOn_Iic _ _ self_mem_Iic | exact uniqueDiffWithinAt_univ (𝕜 := ℝ) (E := ℝ)))

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderivWithin ℝ (fun p ↦ ∫ x in p.1..p.2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
/-
**intervalIntegral.fderivWithin_integral_of_tendsto_ae** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：fderivWithin_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
 (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilt
er f lb) {s t : Set Real} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb] (h
a : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)) 
(hs : UniqueDiffWithinAt Real s a
参数：hf : IntervalIntegrable f volume a b；hmeas_a : StronglyMeasurableAtFilter f l
a；hmeas_b : StronglyMeasurableAtFilter f lb；𝓝[s] a；𝓝[t] b；ha : Tendsto f (la ⊓ a
e volume) (𝓝 ca)；hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `intervalIntegral.integral_hasFDerivWithinAt_of_tendsto_ae`：integral_hasF
DerivWithinAt_of_tendsto_ae (hf : IntervalIntegrable f volume a b) {s t : Set Re
al} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t…
· 使用定理 `UniqueDiffWithinAt.prod`：UniqueDiffWithinAt.prod (hs : UniqueDiffWithinA
t 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) : UniqueDiffWithinAt 𝕜 (s ×ˢ t) (x, y)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…

--- 原说明 ---
Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a
, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost s
urely at the filters
`la` and `lb` from the table below. Then `fderivWithin ℝ (fun p ↦ ∫ x in p.1..p.
2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
theorem fderivWithin_integral_of_tendsto_ae (hf : IntervalIntegrable f volume a b)
    (hmeas_a : StronglyMeasurableAtFilter f la) (hmeas_b : StronglyMeasurableAtFilter f lb)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) la] [FTCFilter b (𝓝[t] b) lb]
    (ha : Tendsto f (la ⊓ ae volume) (𝓝 ca)) (hb : Tendsto f (lb ⊓ ae volume) (𝓝 cb))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ)
    (ht : UniqueDiffWithinAt ℝ t b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    fderivWithin ℝ (fun p : ℝ × ℝ => ∫ x in p.1..p.2, f x) (s ×ˢ t) (a, b) =
      (snd ℝ ℝ ℝ).smulRight cb - (fst ℝ ℝ ℝ).smulRight ca :=
  (integral_hasFDerivWithinAt_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderivWithin <| hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
/-
**intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right** 是 Mathlib 中的一
个定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f v
olume a b) {s t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMea
surableAtFilter f (𝓝[t] b)) (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) : HasDer
ivWithinAt (fun u => ∫ x in a..u, f x) c s b
参数：hf : IntervalIntegrable f volume a b；𝓝[s] b；𝓝[t] b；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] b)；hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasDerivWithinAt.of_isLittleO`：∀ {𝕜 : Type u} [inst : NontriviallyNormed
Field 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 
F] {f : 𝕜 → F} {f' …
· 使用定理 `intervalIntegral.integral_sub_integral_sub_linear_isLittleO_of_tendsto_a
e_right`：integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right (hab : I
ntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
· 使用定理 `intervalIntegral.FTCFilter.pure_le`：∀ {a : outParam ℝ} {outer : Filter ℝ
} {inner : outParam (Filter ℝ)} [self : intervalIntegral.FTCFilter a outer inner
],   pure a ≤ outer
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`.
-/
theorem integral_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in a..u, f x) c s b :=
  .of_isLittleO <| integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right hf hmeas hb
    (tendsto_const_pure.mono_right FTCFilter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
/-
**intervalIntegral.integral_hasDerivWithinAt_right** 是 Mathlib 中的一个定理，位于命名空间 `in
tervalIntegral`。
形式化陈述：integral_hasDerivWithinAt_right (hf : IntervalIntegrable f volume a b) {s 
t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilte
r f (𝓝[t] b)) (hb : ContinuousWithinAt f t b) : HasDerivWithinAt (fun u => ∫ x i
n a..u, f x) (f b) s b
参数：hf : IntervalIntegrable f volume a b；𝓝[s] b；𝓝[t] b；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] b)；hb : ContinuousWithinAt f t b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right`：integral
_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) {s 
t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (re
sp., right)
derivative `f b` at `b`.
-/
theorem integral_hasDerivWithinAt_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b) : HasDerivWithinAt (fun u => ∫ x in a..u, f x) (f b) s b :=
  integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
/-
**intervalIntegral.derivWithin_integral_of_tendsto_ae_right** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：derivWithin_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume
 a b) {s t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurab
leAtFilter f (𝓝[t] b)) (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)) (hs : UniqueD
iffWithinAt Real s b
参数：hf : IntervalIntegrable f volume a b；𝓝[s] b；𝓝[t] b；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] b)；hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right`：integral
_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) {s 
t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, the
n the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`.
-/
theorem derivWithin_integral_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : Tendsto f (𝓝[t] b ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
/-
**intervalIntegral.derivWithin_integral_right** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：derivWithin_integral_right (hf : IntervalIntegrable f volume a b) {s t : S
et Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (
𝓝[t] b)) (hb : ContinuousWithinAt f t b) (hs : UniqueDiffWithinAt Real s b
参数：hf : IntervalIntegrable f volume a b；𝓝[s] b；𝓝[t] b；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] b)；hb : ContinuousWithinAt f t b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_right`：integral_hasDerivWithi
nAt_right (hf : IntervalIntegrable f volume a b) {s t : Set Real} [FTCFilter b (
𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMea…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`.
-/
theorem derivWithin_integral_right (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] b))
    (hb : ContinuousWithinAt f t b)
    (hs : UniqueDiffWithinAt ℝ s b := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in a..u, f x) s b = f b :=
  (integral_hasDerivWithinAt_right hf hmeas hb).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
/-
**intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left** 是 Mathlib 中的一个
定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f vo
lume a b) {s t : Set Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeas
urableAtFilter f (𝓝[t] a)) (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) : HasDeri
vWithinAt (fun u => ∫ x in u..b, f x) (-c) s a
参数：hf : IntervalIntegrable f volume a b；𝓝[s] a；𝓝[t] a；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] a)；ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right`：integral
_hasDerivWithinAt_of_tendsto_ae_right (hf : IntervalIntegrable f volume a b) {s 
t : Set Real} [FTCFilter b (𝓝[s] b) (𝓝[t] b)] (hmeas…
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`.
-/
theorem integral_hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b)
    {s t : Set ℝ} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) :
    HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-c) s a := by
  simp only [integral_symm b]
  exact (integral_hasDerivWithinAt_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
/-
**intervalIntegral.integral_hasDerivWithinAt_left** 是 Mathlib 中的一个定理，位于命名空间 `int
ervalIntegral`。
形式化陈述：integral_hasDerivWithinAt_left (hf : IntervalIntegrable f volume a b) {s t
 : Set Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter
 f (𝓝[t] a)) (ha : ContinuousWithinAt f t a) : HasDerivWithinAt (fun u => ∫ x in
 u..b, f x) (-f a) s a
参数：hf : IntervalIntegrable f volume a b；𝓝[s] a；𝓝[t] a；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] a)；ha : ContinuousWithinAt f t a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left`：integral_
hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t 
: Set Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (re
sp., right)
derivative `-f a` at `a`.
-/
theorem integral_hasDerivWithinAt_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a) : HasDerivWithinAt (fun u => ∫ x in u..b, f x) (-f a) s a :=
  integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
/-
**intervalIntegral.derivWithin_integral_of_tendsto_ae_left** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：derivWithin_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume 
a b) {s t : Set Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurabl
eAtFilter f (𝓝[t] a)) (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)) (hs : UniqueDi
ffWithinAt Real s a
参数：hf : IntervalIntegrable f volume a b；𝓝[s] a；𝓝[t] a；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] a)；ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left`：integral_
hasDerivWithinAt_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t 
: Set Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas …

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, the
n the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`.
-/
theorem derivWithin_integral_of_tendsto_ae_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : Tendsto f (𝓝[t] a ⊓ ae volume) (𝓝 c))
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -c :=
  (integral_hasDerivWithinAt_of_tendsto_ae_left hf hmeas ha).derivWithin hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
/-
**intervalIntegral.derivWithin_integral_left** 是 Mathlib 中的一个定理，位于命名空间 `interval
Integral`。
形式化陈述：derivWithin_integral_left (hf : IntervalIntegrable f volume a b) {s t : Se
t Real} [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝
[t] a)) (ha : ContinuousWithinAt f t a) (hs : UniqueDiffWithinAt Real s a
参数：hf : IntervalIntegrable f volume a b；𝓝[s] a；𝓝[t] a；hmeas : StronglyMeasurable
AtFilter f (𝓝[t] a)；ha : ContinuousWithinAt f t a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `intervalIntegral.integral_hasDerivWithinAt_left`：integral_hasDerivWithin
At_left (hf : IntervalIntegrable f volume a b) {s t : Set Real} [FTCFilter a (𝓝[
s] a) (𝓝[t] a)] (hmeas : StronglyMeas…

--- 原说明 ---
Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x
` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`.
-/
theorem derivWithin_integral_left (hf : IntervalIntegrable f volume a b) {s t : Set ℝ}
    [FTCFilter a (𝓝[s] a) (𝓝[t] a)] (hmeas : StronglyMeasurableAtFilter f (𝓝[t] a))
    (ha : ContinuousWithinAt f t a)
    (hs : UniqueDiffWithinAt ℝ s a := by uniqueDiffWithinAt_Ici_Iic_univ) :
    derivWithin (fun u => ∫ x in u..b, f x) s a = -f a :=
  (integral_hasDerivWithinAt_left hf hmeas ha).derivWithin hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
/-
**intervalIntegral.differentiable_integral_of_continuous** 是 Mathlib 中的一个定理，位于命名
空间 `intervalIntegral`。
形式化陈述：differentiable_integral_of_continuous (hcont : Continuous f) : Differentia
ble Real (fun u => ∫ x in a..u, f x)
参数：hcont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `intervalIntegral.integral_hasDerivAt_right`：integral_hasDerivAt_right (h
f : IntervalIntegrable f volume a b) (hmeas : StronglyMeasurableAtFilter f (𝓝 b)
) (hb : ContinuousAt f b) : HasD…
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurableAtFilter`：∀ {α : Ty
pe u_1} {β : Type u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {l :
 Filter α} {f : α → β}   {μ : MeasureTheory.Measure…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
The integral of a continuous function is differentiable on a real set `s`.
-/
theorem differentiable_integral_of_continuous (hcont : Continuous f) :
    Differentiable ℝ (fun u => ∫ x in a..u, f x) := fun _ ↦
  (integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt).differentiableAt

/-- The integral of a continuous function is differentiable on a real set `s`. -/
/-
**intervalIntegral.differentiableOn_integral_of_continuous** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：differentiableOn_integral_of_continuous {s : Set Real} (hcont : Continuous
 f) : DifferentiableOn Real (fun u => ∫ x in a..u, f x) s
参数：hcont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `intervalIntegral.differentiable_integral_of_continuous`：differentiable_i
ntegral_of_continuous (hcont : Continuous f) : Differentiable Real (fun u => ∫ x
 in a..u, f x)

--- 原说明 ---
The integral of a continuous function is differentiable on a real set `s`.
-/
theorem differentiableOn_integral_of_continuous {s : Set ℝ} (hcont : Continuous f) :
    DifferentiableOn ℝ (fun u => ∫ x in a..u, f x) s :=
  (differentiable_integral_of_continuous hcont).differentiableOn

end FTC1

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left-hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right-hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

section FTC2

variable {g' g φ : ℝ → ℝ} {a b : ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`. -/
/-
**intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le_Ico** 是 Mathlib 中的一个定
理，位于命名空间 `intervalIntegral`。
形式化陈述：sub_le_integral_of_hasDeriv_right_of_le_Ico (hab : a <= b) (hcont : Contin
uousOn g (Icc a b)) (hderiv : forall x in Ico a b, HasDerivWithinAt g (g' x) (Io
i x) x) (φint : IntegrableOn φ (Icc a b)) (hφg : forall x in Ico a b, g' x <= φ 
x) : g b - g a <= ∫ y in a..b, φ y
参数：hab : a <= b；hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ico a b, H
asDerivWithinAt g (g' x) (Ioi x) x；φint : IntegrableOn φ (Icc a b)；hφg : forall 
x in Ico a b, g' x <= φ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `le_of_forall_pos_le_add`：∀ {α : Type u} [inst : LinearOrder α] [DenselyO
rdered α] [inst_2 : AddMonoid α] [ExistsAddOfLE α] [AddLeftReflectLT α]   {a b :
 α}, (∀ (ε : …
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt`：exists_lt_lower
Semicontinuous_integral_lt [SigmaFinite μ] (f : α -> Real) (hf : Integrable f μ)
 {ε : Real} (εpos : 0 < ε) : exists g : α -> …
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.instIsLocallyFiniteMeasureRestrict`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {s : Set α} [inst : TopologicalSpace α] (μ : MeasureTheory.M
easure α)   [hμ : MeasureTheory.IsLoca…
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
（共 123 条，此处仅展示前 30 条）

--- 原说明 ---
Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` wh
en `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`.
-/
theorem sub_le_integral_of_hasDeriv_right_of_le_Ico (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (φint : IntegrableOn φ (Icc a b)) (hφg : ∀ x ∈ Ico a b, g' x ≤ φ x) :
    g b - g a ≤ ∫ y in a..b, φ y := by
  refine le_of_forall_pos_le_add fun ε εpos => ?_
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lowerSemicontinuous_integral_lt φ φint εpos with
    ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩
  -- we will show by "induction" that `g t - g a ≤ ∫ u in a..t, G' u` for all `t ∈ [a, b]`.
  set s := {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} ∩ Icc a b
  -- the set `s` of points where this property holds is closed.
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g t - g a, ∫ u in a..t, (G' u).toReal)) (Icc a b) := by
      rw [← uIcc_of_le hab] at G'int hcont ⊢
      exact (hcont.sub continuousOn_const).prodMk (continuousOn_primitive_interval G'int)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫ u in a..t, (G' u).toReal} := by
    -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    refine s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_ofPred_eq, sub_self, le_rfl]) fun t ht v t_lt_v => ?_
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ y : ℝ, (g' t : EReal) < y ∧ (y : EReal) < G' t :=
      EReal.lt_iff_exists_real_btwn.1 ((EReal.coe_le_coe_iff.2 (hφg t ht.2)).trans_lt (f_lt_G' t))
    -- bound from below the increase of `∫ x in a..u, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).toReal := by
      have B : ∀ᶠ u in 𝓝 t, (y : EReal) < G' u := G'cont.lowerSemicontinuousAt _ _ y_lt_G'
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩
      have : Ioo t (min M b) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (lt_min hM ht.right.right)
      filter_upwards [this] with u hu
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _))
      calc
        (u - t) * y = ∫ _ in Icc t u, y := by
          simp only [MeasureTheory.integral_const, MeasurableSet.univ, measureReal_restrict_apply,
            univ_inter, hu.left.le, Real.volume_real_Icc_of_le, smul_eq_mul]
        _ ≤ ∫ w in t..u, (G' w).toReal := by
          rw [intervalIntegral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc]
          apply setIntegral_mono_ae_restrict
          · simp
          · exact IntegrableOn.mono_set G'int I
          · have C1 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), G' x < ∞ :=
              ae_mono (Measure.restrict_mono I le_rfl) G'lt_top
            have C2 : ∀ᵐ x : ℝ ∂volume.restrict (Icc t u), x ∈ Icc t u :=
              ae_restrict_mem measurableSet_Icc
            filter_upwards [C1, C2] with x G'x hx
            apply EReal.coe_le_coe_iff.1
            have : x ∈ Ioo m M := by
              simp only [hm.trans_le hx.left,
                (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self_iff]
            refine (H this).out.le.trans_eq ?_
            exact (EReal.coe_toReal G'x.ne (f_lt_G' x).ne_bot).symm
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y := by
      have g'_lt_y : g' t < y := EReal.coe_lt_coe_iff.1 g'_lt_y'
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le' (notMem_Ioi.2 le_rfl) g'_lt_y,
        self_mem_nhdsWithin] with u hu t_lt_u
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u.out).le
      rwa [← smul_eq_mul, sub_smul_slope] at this
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫ x in a..u, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).toReal := by
      filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b) := Ioc_mem_nhdsGT <| lt_min t_lt_v ht.2.2
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩
    -- we check that it belongs to `s`, essentially by construction
    refine ⟨x, ?_, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩
    calc
      g x - g a = g t - g a + (g x - g t) := by abel
      _ ≤ (∫ w in a..t, (G' w).toReal) + ∫ w in t..x, (G' w).toReal := add_le_add ht.1 hx
      _ = ∫ w in a..x, (G' w).toReal := by
        apply integral_add_adjacent_intervals
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.1]
          exact IntegrableOn.mono_set G'int
            (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le))
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x.1.le]
          apply IntegrableOn.mono_set G'int
          exact Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _)))
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc
    g b - g a ≤ ∫ y in a..b, (G' y).toReal := main (right_mem_Icc.2 hab)
    _ ≤ (∫ y in a..b, φ y) + ε := by
      convert! hG'.le <;>
        · rw [intervalIntegral.integral_of_le hab]
          simp only [integral_Icc_eq_integral_Ioc', Real.volume_singleton]

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `(a, b)`. -/
/-
**intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：sub_le_integral_of_hasDeriv_right_of_le (hab : a <= b) (hcont : Continuous
On g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivWithinAt g (g' x) (Ioi x)
 x) (φint : IntegrableOn φ (Icc a b)) (hφg : forall x in Ioo a b, g' x <= φ x) :
 g b - g a <= ∫ y in a..b, φ y
参数：hab : a <= b；hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ioo a b, H
asDerivWithinAt g (g' x) (Ioi x) x；φint : IntegrableOn φ (Icc a b)；hφg : forall 
x in Ioo a b, g' x <= φ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `intervalIntegral.integral_same`：integral_same : ∫ x in a..a, f x ∂μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `intervalIntegral.continuousOn_primitive_interval_left`：continuousOn_prim
itive_interval_left (h_int : IntegrableOn f (uIcc a b) μ) : ContinuousOn (fun x 
=> ∫ t in x..b, f t ∂μ) (uIcc a b)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `ContinuousOn.preimage_isClosed_of_isClosed`：ContinuousOn.preimage_isClos
ed_of_isClosed {t : Set β} (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClo
sed t) : IsClosed (s inter f ⁻¹'…
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `isClosed_le_prod`：isClosed_le_prod : IsClosed { p : α × α | p.1 <= p.2 }
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le_Ico`：sub_le_int
egral_of_hasDeriv_right_of_le_Ico (hab : a <= b) (hcont : ContinuousOn g (Icc a 
b)) (hderiv : forall x in Ico a b, HasDerivWithinA…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫ y in a..b, φ y` wh
en `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `(a, b)`.
-/
theorem sub_le_integral_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, g' x ≤ φ x) : g b - g a ≤ ∫ y in a..b, φ y := by
  -- This follows from the version on a closed-open interval (applied to `[t, b)` for `t` close to
  -- `a`) and a continuity argument.
  obtain rfl | a_lt_b := hab.eq_or_lt
  · simp
  set s := {t | g b - g t ≤ ∫ u in t..b, φ u} ∩ Icc a b
  have s_closed : IsClosed s := by
    have : ContinuousOn (fun t => (g b - g t, ∫ u in t..b, φ u)) (Icc a b) := by
      rw [← uIcc_of_le hab] at hcont φint ⊢
      exact (continuousOn_const.sub hcont).prodMk (continuousOn_primitive_interval_left φint)
    simp only [s, inter_comm]
    exact this.preimage_isClosed_of_isClosed isClosed_Icc isClosed_le_prod
  have A : closure (Ioc a b) ⊆ s := by
    apply s_closed.closure_subset_iff.2
    intro t ht
    refine ⟨?_, ⟨ht.1.le, ht.2⟩⟩
    exact
      sub_le_integral_of_hasDeriv_right_of_le_Ico ht.2 (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
        (fun x hx => hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩)
        (φint.mono_set (Icc_subset_Icc ht.1.le le_rfl)) fun x hx => hφg x ⟨ht.1.trans_le hx.1, hx.2⟩
  rw [closure_Ioc a_lt_b.ne] at A
  exact (A (left_mem_Icc.2 hab)).1

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`. -/
/-
**intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_le_sub_of_hasDeriv_right_of_le (hab : a <= b) (hcont : Continuous
On g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivWithinAt g (g' x) (Ioi x)
 x) (φint : IntegrableOn φ (Icc a b)) (hφg : forall x in Ioo a b, φ x <= g' x) :
 (∫ y in a..b, φ y) <= g b - g a
参数：hab : a <= b；hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ioo a b, H
asDerivWithinAt g (g' x) (Ioi x) x；φint : IntegrableOn φ (Icc a b)；hφg : forall 
x in Ioo a b, φ x <= g' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
.0.intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le._abel_1_1`：∀ {g : ℝ 
→ ℝ} {a b : ℝ}, -(g b - g a) = -g b - -g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`：sub_le_integra
l_of_hasDeriv_right_of_le (hab : a <= b) (hcont : ContinuousOn g (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt g …
· 使用定理 `ContinuousOn.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f 
: X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `HasDerivWithinAt.neg`：HasDerivWithinAt.neg (h : HasDerivWithinAt f f' s 
x) : HasDerivWithinAt (-f) (-f') s x
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a

--- 原说明 ---
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`.
-/
theorem integral_le_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (φint : IntegrableOn φ (Icc a b))
    (hφg : ∀ x ∈ Ioo a b, φ x ≤ g' x) : (∫ y in a..b, φ y) ≤ g b - g a := by
  rw [← neg_le_neg_iff]
  convert!
    sub_le_integral_of_hasDeriv_right_of_le hab hcont.fun_neg (fun x hx => (hderiv x hx).neg)
      φint.neg fun x hx => neg_le_neg (hφg x hx) using 1
  · abel
  · simp only [← integral_neg]; rfl

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`: real version -/
/-
**intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real** 是 Mathlib 中的一个
定理，位于命名空间 `intervalIntegral`。
形式化陈述：integral_eq_sub_of_hasDeriv_right_of_le_real (hab : a <= b) (hcont : Conti
nuousOn g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivWithinAt g (g' x) (I
oi x) x) (g'int : IntegrableOn g' (Icc a b)) : ∫ y in a..b, g' y = g b - g a
参数：hab : a <= b；hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ioo a b, H
asDerivWithinAt g (g' x) (Ioi x) x；g'int : IntegrableOn g' (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le`：integral_le_su
b_of_hasDeriv_right_of_le (hab : a <= b) (hcont : ContinuousOn g (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt g …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le`：sub_le_integra
l_of_hasDeriv_right_of_le (hab : a <= b) (hcont : ContinuousOn g (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt g …

--- 原说明 ---
Auxiliary lemma in the proof of `integral_eq_sub_of_hasDeriv_right_of_le`: real 
version
-/
theorem integral_eq_sub_of_hasDeriv_right_of_le_real (hab : a ≤ b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'int : IntegrableOn g' (Icc a b)) : ∫ y in a..b, g' y = g b - g a :=
  le_antisymm (integral_le_sub_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)
    (sub_le_integral_of_hasDeriv_right_of_le hab hcont hderiv g'int fun _ _ => le_rfl)

variable [CompleteSpace E] {f f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le** 是 Mathlib 中的一个定理，位于
命名空间 `intervalIntegral`。
形式化陈述：integral_eq_sub_of_hasDeriv_right_of_le (hab : a <= b) (hcont : Continuous
On f (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivWithinAt f (f' x) (Ioi x)
 x) (f'int : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a
参数：hab : a <= b；hcont : ContinuousOn f (Icc a b)；hderiv : forall x in Ioo a b, H
asDerivWithinAt f (f' x) (Ioi x) x；f'int : IntervalIntegrable f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeparatingDual.eq_iff_forall_dual_eq`：eq_iff_forall_dual_eq {x y : V} : 
x = y ↔ forall g : StrongDual R V, g x = g y
· 使用定理 `instSeparatingDualRealOfIsTopologicalAddGroupOfContinuousSMulOfLocallyCo
nvexSpaceOfT1Space`：∀ {E : Type u_1} [inst : TopologicalSpace E] [inst_1 : AddCo
mmGroup E] [IsTopologicalAddGroup E]   [inst_3 : _root_.Module ℝ E] [ContinuousS
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.intervalIntegral_comp_comm`：∀ {𝕜 : Type u_2} {E : Ty
pe u_5} {F : Type u_6} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{a b : ℝ}   {μ : MeasureTheory.Measu…
· 使用定理 `ContinuousLinearMap.map_sub`：∀ {R : Type u_1} [inst : Ring R] {R₂ : Type
 u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [inst_3 
: AddCommGroup M]…
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real`：integral_
eq_sub_of_hasDeriv_right_of_le_real (hab : a <= b) (hcont : ContinuousOn g (Icc 
a b)) (hderiv : forall x in Ioo a b, HasDerivWithin…
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `HasFDerivAt.comp_hasDerivWithinAt`：HasFDerivAt.comp_hasDerivWithinAt (hl
 : HasFDerivAt l l' (f x)) (hf : HasDerivWithinAt f f' s x) : HasDerivWithinAt (
l ∘ f) (l' f') s x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞

--- 原说明 ---
**Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` 
(where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is inte
grable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`.
-/
theorem integral_eq_sub_of_hasDeriv_right_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g => ?_
  rw [← g.intervalIntegral_comp_comm f'int, g.map_sub]
  exact integral_eq_sub_of_hasDeriv_right_of_le_real hab (g.continuous.comp_continuousOn hcont)
    (fun x hx => g.hasFDerivAt.comp_hasDerivWithinAt x (hderiv x hx))
    (g.integrable_comp ((intervalIntegrable_iff_integrableOn_Icc_of_le hab enorm_ne_top).1 f'int))

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrable on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_eq_sub_of_hasDeriv_right** 是 Mathlib 中的一个定理，位于命名空间 `
intervalIntegral`。
形式化陈述：integral_eq_sub_of_hasDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hde
riv : forall x in Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x) 
(hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a
参数：hcont : ContinuousOn f (uIcc a b)；hderiv : forall x in Ioo (min a b) (max a b
), HasDerivWithinAt f (f' x) (Ioi x) x；hint : IntervalIntegrable f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`：integral_eq_su
b_of_hasDeriv_right_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrab
le on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`.
-/
theorem integral_eq_sub_of_hasDeriv_right (hcont : ContinuousOn f (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt f (f' x) (Ioi x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, hab] at hcont hderiv hint
    apply integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint.symm, neg_sub]

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le** 是 Mathlib 中的一个定理，位于命名空间
 `intervalIntegral`。
形式化陈述：integral_eq_sub_of_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f
 (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivAt f (f' x) x) (hint : Interv
alIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a
参数：hab : a <= b；hcont : ContinuousOn f (Icc a b)；hderiv : forall x in Ioo a b, H
asDerivAt f (f' x) x；hint : IntervalIntegrable f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`：integral_eq_su
b_of_hasDeriv_right_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt f …
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (whe
re `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on 
`[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`.
-/
theorem integral_eq_sub_of_hasDerivAt_of_le (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivWithinAt)
    hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_eq_sub_of_hasDerivAt** 是 Mathlib 中的一个定理，位于命名空间 `inte
rvalIntegral`。
形式化陈述：integral_eq_sub_of_hasDerivAt (hderiv : forall x in uIcc a b, HasDerivAt f
 (f' x) x) (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b -
 f a
参数：hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x；hint : IntervalIntegrabl
e f' volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDeriv_right`：integral_eq_sub_of_h
asDeriv_right (hcont : ContinuousOn f (uIcc a b)) (hderiv : forall x in Ioo (min
 a b) (max a b), HasDerivWithinAt f (f' …
· 使用定理 `HasDerivAt.continuousOn`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 
𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {s 
: Set 𝕜} {f f…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Set.mem_Icc_of_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x 
∈ Set.Ioo a b → x ∈ Set.Icc a b

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for
 all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `
f b - f a`.
-/
theorem integral_eq_sub_of_hasDerivAt (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a :=
  integral_eq_sub_of_hasDeriv_right (HasDerivAt.continuousOn hderiv)
    (fun _x hx => (hderiv _ (mem_Icc_of_Ioo hx)).hasDerivWithinAt) hint
/-
**intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto** 是 Mathlib 中的一个定理，位
于命名空间 `intervalIntegral`。
形式化陈述：integral_eq_sub_of_hasDerivAt_of_tendsto (hab : a < b) {fa fb} (hderiv : f
orall x in Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume 
a b) (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) : ∫ y in 
a..b, f' y = fb - fa
参数：hab : a < b；hderiv : forall x in Ioo a b, HasDerivAt f (f' x) x；hint : Interv
alIntegrable f' volume a b；ha : Tendsto f (𝓝[>] a) (𝓝 fa)；hb : Tendsto f (𝓝[<] b
) (𝓝 fb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_of_eventuallyEq`：HasDerivAt.congr_of_eventuallyEq (h : 
HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `continuousOn_update_iff`：continuousOn_update_iff [T1Space X] [DecidableE
q X] [TopologicalSpace Y] {f : X -> Y} {s : Set X} {x : X} {y : Y} : ContinuousO
n (Function.u…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Ioo_mem_nhdsLT`：Ioo_mem_nhdsLT (H : a < b) : Ioo a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
（共 38 条，此处仅展示前 30 条）
-/
theorem integral_eq_sub_of_hasDerivAt_of_tendsto (hab : a < b) {fa fb}
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume a b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa)) (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    ∫ y in a..b, f' y = fb - fa := by
  set F : ℝ → E := update (update f a fa) b fb
  have Fderiv : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    refine fun x hx => (hderiv x hx).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy
    unfold F
    rw [update_of_ne hy.2.ne, update_of_ne hy.1.ne']
  have hcont : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨fun z hz => (hderiv z hz).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ => ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with _ hz using (update_of_ne hz.1.ne' _ _).symm
  simpa [F, hab.ne, hab.ne'] using integral_eq_sub_of_hasDerivAt_of_le hab.le hcont Fderiv hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`.

See also `integral_deriv_of_contDiffOn_Icc` for a similar theorem assuming that `f` is `C^1`. -/
/-
**intervalIntegral.integral_deriv_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `intervalInte
gral`。
形式化陈述：integral_deriv_eq_sub (hderiv : forall x in [[a, b]], DifferentiableAt Rea
l f x) (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y
 = f b - f a
参数：hderiv : forall x in [[a, b]], DifferentiableAt Real f x；hint : IntervalInteg
rable (deriv f) volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt`：integral_eq_sub_of_hasDe
rivAt (hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalInt
egrable f' volume a b) : ∫ y in a..b…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x`
 in `[a, b]` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `
f b - f a`.

See also `integral_deriv_of_contDiffOn_Icc` for a similar theorem assuming that 
`f` is `C^1`.
-/
theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a :=
  integral_eq_sub_of_hasDerivAt (fun x hx => (hderiv x hx).hasDerivAt) hint
/-
**intervalIntegral.integral_deriv_eq_sub'** 是 Mathlib 中的一个定理，位于命名空间 `intervalInt
egral`。
形式化陈述：integral_deriv_eq_sub' (f) (hderiv : deriv f = f') (hdiff : forall x in uI
cc a b, DifferentiableAt Real f x) (hcont : ContinuousOn f' (uIcc a b)) : ∫ y in
 a..b, f' y = f b - f a
参数：f；hderiv : deriv f = f'；hdiff : forall x in uIcc a b, DifferentiableAt Real f
 x；hcont : ContinuousOn f' (uIcc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_deriv_eq_sub`：integral_deriv_eq_sub (hderiv : 
forall x in [[a, b]], DifferentiableAt Real f x) (hint : IntervalIntegrable (der
iv f) volume a b) : ∫ y in a…
· 使用定理 `ContinuousOn.intervalIntegrable`：ContinuousOn.intervalIntegrable {u : Re
al -> E} {a b : Real} (hu : ContinuousOn u (uIcc a b)) : IntervalIntegrable u μ 
a b
-/
theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
    (hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x) (hcont : ContinuousOn f' (uIcc a b)) :
    ∫ y in a..b, f' y = f b - f a := by
  rw [← hderiv, integral_deriv_eq_sub hdiff]
  rw [hderiv]
  exact hcont.intervalIntegrable

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `(a, b)` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
/-
**intervalIntegral.integral_deriv_eq_sub_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `interva
lIntegral`。
形式化陈述：integral_deriv_eq_sub_uIoo (hcont : ContinuousOn f [[a, b]]) (hderiv : for
all x in uIoo a b, DifferentiableAt Real f x) (hint : IntervalIntegrable (deriv 
f) volume a b) : ∫ y in a..b, deriv f y = f b - f a
参数：hcont : ContinuousOn f [[a, b]]；hderiv : forall x in uIoo a b, Differentiable
At Real f x；hint : IntervalIntegrable (deriv f) volume a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：integral_eq_sub_of
_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hderiv : fo
rall x in Ioo a b, HasDerivAt f (f' x) x) …
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.uIoo_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoo a b = Set.Ioo a b
· 使用定理 `intervalIntegral.integral_symm`：integral_symm (a b) : ∫ x in b..a, f x ∂
μ = -∫ x in a..b, f x ∂μ
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `Set.uIoo_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoo a b = Set.Ioo b a
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a

--- 原说明 ---
Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x`
 in `(a, b)` and
its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `
f b - f a`.
-/
theorem integral_deriv_eq_sub_uIoo
    (hcont : ContinuousOn f [[a, b]]) (hderiv : ∀ x ∈ uIoo a b, DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, hab, uIoo_of_le] at hcont hderiv
    rw [integral_eq_sub_of_hasDerivAt_of_le hab hcont (fun x hx => (hderiv x hx).hasDerivAt) hint]
  · simp only [uIcc_of_ge, hab, uIoo_of_ge] at hcont hderiv
    rw [integral_symm, integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun x hx => (hderiv x hx).hasDerivAt) hint.symm, neg_sub]

/-- A variant of `intervalIntegral.integral_deriv_eq_sub`, the Fundamental theorem
of calculus, involving integrating over the unit interval. -/
/-
**intervalIntegral.integral_unitInterval_deriv_eq_sub** 是 Mathlib 中的一个引理，位于命名空间 
`intervalIntegral`。
形式化陈述：integral_unitInterval_deriv_eq_sub [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarT
ower Real 𝕜 E] {f f' : 𝕜 -> E} {z₀ z₁ : 𝕜} (hcont : ContinuousOn (fun t : Real =
> f' (z₀ + t • z₁)) (Set.Icc 0 1)) (hderiv : forall t in Set.Icc (0 : Real) 1, H
asDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) : z₁ • ∫ t in (0 : Real)..1, f' (z
₀ + t • z₁) = f (z₀ + z₁) - f z₀
参数：hcont : ContinuousOn (fun t : Real => f' (z₀ + t • z₁)) (Set.Icc 0 1)；hderiv 
: forall t in Set.Icc (0 : Real) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousOn.intervalIntegrable_of_Icc`：ContinuousOn.intervalIntegrable_
of_Icc {u : Real -> E} {a b : Real} (h : a <= b) (hu : ContinuousOn u (Icc a b))
 : IntervalIntegrable u μ a …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContinuousOn.const_smul`：ContinuousOn.const_smul (hg : ContinuousOn g s)
 (c : M) : ContinuousOn (c • g) s
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `HasDerivAt.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt`：integral_eq_sub_of_hasDe
rivAt (hderiv : forall x in uIcc a b, HasDerivAt f (f' x) x) (hint : IntervalInt
egrable f' volume a b) : ∫ y in a..b…

--- 原说明 ---
A variant of `intervalIntegral.integral_deriv_eq_sub`, the Fundamental theorem
of calculus, involving integrating over the unit interval.
-/
lemma integral_unitInterval_deriv_eq_sub [RCLike 𝕜] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]
    {f f' : 𝕜 → E} {z₀ z₁ : 𝕜}
    (hcont : ContinuousOn (fun t : ℝ ↦ f' (z₀ + t • z₁)) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (z₀ + t • z₁)) (z₀ + t • z₁)) :
    z₁ • ∫ t in (0 : ℝ)..1, f' (z₀ + t • z₁) = f (z₀ + z₁) - f z₀ := by
  let γ (t : ℝ) : 𝕜 := z₀ + t • z₁
  have hint : IntervalIntegrable (z₁ • (f' ∘ γ)) MeasureTheory.volume 0 1 :=
    (ContinuousOn.const_smul hcont z₁).intervalIntegrable_of_Icc zero_le_one
  have hderiv' (t) (ht : t ∈ Set.uIcc (0 : ℝ) 1) : HasDerivAt (f ∘ γ) (z₁ • (f' ∘ γ) t) t := by
    refine (hderiv t <| (Set.uIcc_of_le (α := ℝ) zero_le_one).symm ▸ ht).scomp t <| .const_add _ ?_
    simp [hasDerivAt_iff_isLittleO, sub_smul]
  convert! (integral_eq_sub_of_hasDerivAt hderiv' hint) using 1
  · simp_rw [← integral_smul, Function.comp_apply, γ]
  · simp only [γ, Function.comp_apply, one_smul, zero_smul, add_zero]

/-!
### Automatic integrability for nonnegative derivatives
-/

/-- When the right derivative of a function is nonnegative, then it is automatically integrable. -/
/-
**intervalIntegral.integrableOn_deriv_right_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：integrableOn_deriv_right_of_nonneg (hcont : ContinuousOn g (Icc a b)) (hde
riv : forall x in Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x) (g'pos : forall 
x in Ioo a b, 0 <= g' x) : IntegrableOn g' (Ioc a b)
参数：hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ioo a b, HasDerivWithin
At g (g' x) (Ioi x) x；g'pos : forall x in Ioo a b, 0 <= g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `integrableOn_Ioc_iff_integrableOn_Ioo`：integrableOn_Ioc_iff_integrableOn
_Ioo (hb : ‖f b‖ₑ != ∞
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
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `AEMeasurable.congr`：congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMe
asurable g μ
· 使用定理 `aemeasurable_derivWithin_Ioi`：aemeasurable_derivWithin_Ioi [MeasurableSp
ace F] [BorelSpace F] (μ : Measure Real) : AEMeasurable (fun x => derivWithin f 
(Ioi x) x) μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `uniqueDiffWithinAt_Ioi`：uniqueDiffWithinAt_Ioi (a : Real) : UniqueDiffWi
thinAt Real (Ioi a) a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
When the right derivative of a function is nonnegative, then it is automatically
 integrable.
-/
theorem integrableOn_deriv_right_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt g (g' x) (Ioi x) x)
    (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) : IntegrableOn g' (Ioc a b) := by
  by_cases hab : a < b; swap
  · simp [Ioc_eq_empty hab]
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have meas_g' : AEMeasurable g' (volume.restrict (Ioo a b)) := by
    apply (aemeasurable_derivWithin_Ioi g _).congr
    refine (ae_restrict_mem measurableSet_Ioo).mono fun x hx => ?_
    exact (hderiv x hx).derivWithin (uniqueDiffWithinAt_Ioi _)
  suffices H : (∫⁻ x in Ioo a b, ‖g' x‖₊) ≤ ENNReal.ofReal (g b - g a) from
    ⟨meas_g'.aestronglyMeasurable, H.trans_lt ENNReal.ofReal_lt_top⟩
  by_contra! H
  obtain ⟨f, fle, fint, hf⟩ :
    ∃ f : SimpleFunc ℝ ℝ≥0,
      (∀ x, f x ≤ ‖g' x‖₊) ∧
        (∫⁻ x : ℝ in Ioo a b, f x) < ∞ ∧ ENNReal.ofReal (g b - g a) < ∫⁻ x : ℝ in Ioo a b, f x :=
    exists_lt_lintegral_simpleFunc_of_lt_lintegral H
  let F : ℝ → ℝ := (↑) ∘ f
  have intF : IntegrableOn F (Ioo a b) := by
    refine ⟨f.measurable.coe_nnreal_real.aestronglyMeasurable, ?_⟩
    simpa only [F, hasFiniteIntegral_iff_enorm, comp_apply, NNReal.enorm_eq] using fint
  have A : ∫⁻ x : ℝ in Ioo a b, f x = ENNReal.ofReal (∫ x in Ioo a b, F x) :=
    lintegral_coe_eq_integral _ intF
  rw [A] at hf
  have B : (∫ x : ℝ in Ioo a b, F x) ≤ g b - g a := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    refine integral_le_sub_of_hasDeriv_right_of_le hab.le hcont hderiv ?_ fun x hx => ?_
    · rwa [integrableOn_Icc_iff_integrableOn_Ioo]
    · convert! NNReal.coe_le_coe.2 (fle x)
      simp only [Real.norm_of_nonneg (g'pos x hx), coe_nnnorm]
  exact lt_irrefl _ (hf.trans_le (ENNReal.ofReal_le_ofReal B))

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
Ioc version. -/
/-
**intervalIntegral.integrableOn_deriv_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `inter
valIntegral`。
形式化陈述：integrableOn_deriv_of_nonneg (hcont : ContinuousOn g (Icc a b)) (hderiv : 
forall x in Ioo a b, HasDerivAt g (g' x) x) (g'pos : forall x in Ioo a b, 0 <= g
' x) : IntegrableOn g' (Ioc a b)
参数：hcont : ContinuousOn g (Icc a b)；hderiv : forall x in Ioo a b, HasDerivAt g (
g' x) x；g'pos : forall x in Ioo a b, 0 <= g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `intervalIntegral.integrableOn_deriv_right_of_nonneg`：integrableOn_deriv_
right_of_nonneg (hcont : ContinuousOn g (Icc a b)) (hderiv : forall x in Ioo a b
, HasDerivWithinAt g (g' x) (Ioi x) x) (g…
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x

--- 原说明 ---
When the derivative of a function is nonnegative, then it is automatically integ
rable,
Ioc version.
-/
theorem integrableOn_deriv_of_nonneg (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
    IntegrableOn g' (Ioc a b) :=
  integrableOn_deriv_right_of_nonneg hcont (fun x hx => (hderiv x hx).hasDerivWithinAt) g'pos

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
interval version. -/
/-
**intervalIntegral.intervalIntegrable_deriv_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 
`intervalIntegral`。
形式化陈述：intervalIntegrable_deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b)) (hd
eriv : forall x in Ioo (min a b) (max a b), HasDerivAt g (g' x) x) (hpos : foral
l x in Ioo (min a b) (max a b), 0 <= g' x) : IntervalIntegrable g' volume a b
参数：hcont : ContinuousOn g (uIcc a b)；hderiv : forall x in Ioo (min a b) (max a b
), HasDerivAt g (g' x) x；hpos : forall x in Ioo (min a b) (max a b), 0 <= g' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioc_eq_empty_of_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, 
a ≤ b → Set.Ioc b a = ∅
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `intervalIntegral.integrableOn_deriv_of_nonneg`：integrableOn_deriv_of_non
neg (hcont : ContinuousOn g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivAt
 g (g' x) x) (g'pos : forall x in I…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a

--- 原说明 ---
When the derivative of a function is nonnegative, then it is automatically integ
rable,
interval version.
-/
theorem intervalIntegrable_deriv_of_nonneg (hcont : ContinuousOn g (uIcc a b))
    (hderiv : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ g' x) : IntervalIntegrable g' volume a b := by
  rcases le_total a b with hab | hab
  · simp only [uIcc_of_le, min_eq_left, max_eq_right, IntervalIntegrable, hab,
      Ioc_eq_empty_of_le, integrableOn_empty, and_true] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos
  · simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab, IntervalIntegrable, Ioc_eq_empty_of_le,
      integrableOn_empty, true_and] at hcont hderiv hpos ⊢
    exact integrableOn_deriv_of_nonneg hcont hderiv hpos

end FTC2

end intervalIntegral

