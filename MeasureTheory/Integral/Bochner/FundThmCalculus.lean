/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fundamental theorem of calculus for set integrals

This file proves a version of the
[Fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for set integrals. See `Filter.Tendsto.integral_sub_linear_isLittleO_ae` and its corollaries.

Namely, consider a measurably generated filter `l`, a measure `μ` finite at this filter, and
a function `f` that has a finite limit `c` at `l ⊓ ae μ`. Then `∫ x in s, f x ∂μ = μ s • c + o(μ s)`
as `s` tends to `l.smallSets`, i.e. for any `ε>0` there exists `t ∈ l` such that
`‖∫ x in s, f x ∂μ - μ s • c‖ ≤ ε * μ s` whenever `s ⊆ t`. We also formulate a version of this
theorem for a locally finite measure `μ` and a function `f` continuous at a point `a`.
-/

public section

open Filter MeasureTheory Topology Asymptotics Metric

variable {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Fundamental theorem of calculus for set integrals:
if `μ` is a measure that is finite at a filter `l` and
`f` is a measurable function that has a finite limit `b` at `l ⊓ ae μ`, then
`∫ x in s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that
`s i` tends to `l.smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
/-
**Filter.Tendsto.integral_sub_linear_isLittleO_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.integral_sub_linear_isLittleO_ae {μ : Measure X} {l : Filte
r X} [l.IsMeasurablyGenerated] {f : X -> E} {b : E} (h : Tendsto f (l ⊓ ae μ) (𝓝
 b)) (hfm : StronglyMeasurableAtFilter f l μ) (hμ : μ.FiniteAtFilter l) {s : ι -
> Set X} {li : Filter ι} (hs : Tendsto s li l.smallSets) (m : ι -> Real
参数：h : Tendsto f (l ⊓ ae μ) (𝓝 b)；hfm : StronglyMeasurableAtFilter f l μ；hμ : μ.
FiniteAtFilter l；hs : Tendsto s li l.smallSets。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.eventually_smallSets_eventually`：eventually_smallSets_eventually 
{p : α -> Prop} : (forallᶠ s in l.smallSets, forallᶠ x in l', x in s -> p x) ↔ f
orallᶠ x in l ⊓ l', p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `StronglyMeasurableAtFilter.eventually`：∀ {α : Type u_1} {β : Type u_2} {
mα : MeasurableSpace α} [inst : TopologicalSpace β] {l : Filter α} {f : α → β}  
 {μ : MeasureTheory.Measure…
· 使用定理 `MeasureTheory.IntegrableAtFilter.eventually`：∀ {α : Type u_1} {ε : Type 
u_3} {mα : MeasurableSpace α} {f : α → ε} {μ : MeasureTheory.Measure α}   [inst 
: TopologicalSpace ε] [inst_1 : C…
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.integrableAtFilter_of_tendsto_ae`：∀
 {α : Type u_1} {E : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGro
up E] {μ : MeasureTheory.Measure α}   {f : α → E} {l : Filt…
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.eventually`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : Filter α},   μ.FiniteAtFil
ter f → ∀ᶠ (s : Set α) in f.smallSets…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'`：norm_setIntegral
_le_of_norm_le_const_ae' {C : Real} (hs : μ s < ∞) (hC : forallᵐ x ∂μ, x in s ->
 ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.r…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Fundamental theorem of calculus for set integrals:
if `μ` is a measure that is finite at a filter `l` and
`f` is a measurable function that has a finite limit `b` at `l ⊓ ae μ`, then
`∫ x in s i, f x ∂μ = μ (s i) • b + o(μ (s i))` at a filter `li` provided that
`s i` tends to `l.smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual stateme
nt.

Often there is a good formula for `μ.real (s i)`, so the formalization can take 
an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`
. Without these
arguments, `m i = μ.real (s i)` is used in the output.
-/
theorem Filter.Tendsto.integral_sub_linear_isLittleO_ae
    {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated] {f : X → E} {b : E}
    (h : Tendsto f (l ⊓ ae μ) (𝓝 b)) (hfm : StronglyMeasurableAtFilter f l μ)
    (hμ : μ.FiniteAtFilter l) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li l.smallSets)
    (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • b) =o[li] m := by
  suffices
      (fun s => (∫ x in s, f x ∂μ) - μ.real s • b) =o[l.smallSets] fun s => μ.real s from
    (this.comp_tendsto hs).congr'
      (hsμ.mono fun a ha => by dsimp only [Function.comp_apply] at ha ⊢; rw [ha]) hsμ
  refine isLittleO_iff.2 fun ε ε₀ => ?_
  have : ∀ᶠ s in l.smallSets, ∀ᵐ x ∂μ, x ∈ s → f x ∈ closedBall b ε :=
    eventually_smallSets_eventually.2 (h.eventually <| closedBall_mem_nhds _ ε₀)
  filter_upwards [hμ.eventually, (hμ.integrableAtFilter_of_tendsto_ae hfm h).eventually,
    hfm.eventually, this]
  simp only [mem_closedBall, dist_eq_norm]
  intro s hμs h_integrable hfm h_norm
  rw [← setIntegral_const,
    ← integral_sub h_integrable (integrableOn_const hμs.ne),
    Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact norm_setIntegral_le_of_norm_le_const_ae' hμs h_norm

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure and `f` is an almost everywhere measurable function that is continuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.  Since `μ (s i)` is an `ℝ≥0∞`
number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
/-
**ContinuousWithinAt.integral_sub_linear_isLittleO_ae** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：ContinuousWithinAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [
OpensMeasurableSpace X] {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X} {t : 
Set X} {f : X -> E} (hx : ContinuousWithinAt f t x) (ht : MeasurableSet t) (hfm 
: StronglyMeasurableAtFilter f (𝓝[t] x) μ) {s : ι -> Set X} {li : Filter ι} (hs 
: Tendsto s li (𝓝[t] x).smallSets) (m : ι -> Real
参数：hx : ContinuousWithinAt f t x；ht : MeasurableSet t；hfm : StronglyMeasurableAt
Filter f (𝓝[t] x) μ；hs : Tendsto s li (𝓝[t] x).smallSets。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.integral_sub_linear_isLittleO_ae`：Filter.Tendsto.integral
_sub_linear_isLittleO_ae {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated
] {f : X -> E} {b : E} (h : Tendsto f…
· 使用定理 `MeasurableSet.nhdsWithin_isMeasurablyGenerated`：MeasurableSet.nhdsWithin
_isMeasurablyGenerated {s : Set α} (hs : MeasurableSet s) (a : α) : (𝓝[s] a).IsM
easurablyGenerated
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `MeasureTheory.Measure.finiteAt_nhdsWithin`：finiteAt_nhdsWithin [Topologi
calSpace α] {_m0 : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ]
 (x : α) (s : Set α) : μ.Finite…

--- 原说明 ---
Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` 
is a locally
finite measure and `f` is an almost everywhere measurable function that is conti
nuous at a point `a`
within a measurable set `t`, then `∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i
))` at a filter `li`
provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.  Since `μ (s i)` i
s an `ℝ≥0∞`
number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take 
an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`
. Without these
arguments, `m i = μ.real (s i)` is used in the output.
-/
theorem ContinuousWithinAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hx : ContinuousWithinAt f t x)
    (ht : MeasurableSet t) (hfm : StronglyMeasurableAtFilter f (𝓝[t] x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets) (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  haveI : (𝓝[t] x).IsMeasurablyGenerated := ht.nhdsWithin_isMeasurablyGenerated _
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhdsWithin x t) hs m
    hsμ

/-- Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a locally finite
measure and `f` is an almost everywhere measurable function that is continuous at a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tends to
`(𝓝 a).smallSets` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in
the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
/-
**ContinuousAt.integral_sub_linear_isLittleO_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensM
easurableSpace X] {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X} {f : X -> E
} (hx : ContinuousAt f x) (hfm : StronglyMeasurableAtFilter f (𝓝 x) μ) {s : ι ->
 Set X} {li : Filter ι} (hs : Tendsto s li (𝓝 x).smallSets) (m : ι -> Real
参数：hx : ContinuousAt f x；hfm : StronglyMeasurableAtFilter f (𝓝 x) μ；hs : Tendsto
 s li (𝓝 x).smallSets。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.integral_sub_linear_isLittleO_ae`：Filter.Tendsto.integral
_sub_linear_isLittleO_ae {μ : Measure X} {l : Filter X} [l.IsMeasurablyGenerated
] {f : X -> E} {b : E} (h : Tendsto f…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …

--- 原说明 ---
Fundamental theorem of calculus for set integrals, `nhds` version: if `μ` is a l
ocally finite
measure and `f` is an almost everywhere measurable function that is continuous a
t a point `a`, then
`∫ x in s i, f x ∂μ = μ (s i) • f a + o(μ (s i))` at `li` provided that `s` tend
s to
`(𝓝 a).smallSets` along `li`. Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.rea
l (s i)` in
the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take 
an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`
. Without these
arguments, `m i = μ.real (s i)` is used in the output.
-/
theorem ContinuousAt.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsLocallyFiniteMeasure μ] {x : X}
    {f : X → E} (hx : ContinuousAt f x) (hfm : StronglyMeasurableAtFilter f (𝓝 x) μ) {s : ι → Set X}
    {li : Filter ι} (hs : Tendsto s li (𝓝 x).smallSets) (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hx.mono_left inf_le_left).integral_sub_linear_isLittleO_ae hfm (μ.finiteAt_nhds x) hs m hsμ

/-- Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).smallSets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual statement.

Often there is a good formula for `μ.real (s i)`, so the formalization can take an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`. Without these
arguments, `m i = μ.real (s i)` is used in the output. -/
/-
**ContinuousOn.integral_sub_linear_isLittleO_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensM
easurableSpace X] [SecondCountableTopologyEither X E] {μ : Measure X} [IsLocally
FiniteMeasure μ] {x : X} {t : Set X} {f : X -> E} (hft : ContinuousOn f t) (hx :
 x in t) (ht : MeasurableSet t) {s : ι -> Set X} {li : Filter ι} (hs : Tendsto s
 li (𝓝[t] x).smallSets) (m : ι -> Real
参数：hft : ContinuousOn f t；hx : x in t；ht : MeasurableSet t；hs : Tendsto s li (𝓝[
t] x).smallSets。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.integral_sub_linear_isLittleO_ae`：ContinuousWithinAt.
integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X] {
μ : Measure X} [IsLocallyFiniteMeasure μ]…
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α

--- 原说明 ---
Fundamental theorem of calculus for set integrals, `nhdsWithin` version: if `μ` 
is a locally
finite measure, `f` is continuous on a measurable set `t`, and `a ∈ t`, then `∫ 
x in (s i), f x ∂μ =
μ (s i) • f a + o(μ (s i))` at `li` provided that `s i` tends to `(𝓝[t] a).small
Sets` along `li`.
Since `μ (s i)` is an `ℝ≥0∞` number, we use `μ.real (s i)` in the actual stateme
nt.

Often there is a good formula for `μ.real (s i)`, so the formalization can take 
an optional
argument `m` with this formula and a proof of `(fun i => μ.real (s i)) =ᶠ[li] m`
. Without these
arguments, `m i = μ.real (s i)` is used in the output.
-/
theorem ContinuousOn.integral_sub_linear_isLittleO_ae [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X E] {μ : Measure X}
    [IsLocallyFiniteMeasure μ] {x : X} {t : Set X} {f : X → E} (hft : ContinuousOn f t) (hx : x ∈ t)
    (ht : MeasurableSet t) {s : ι → Set X} {li : Filter ι} (hs : Tendsto s li (𝓝[t] x).smallSets)
    (m : ι → ℝ := fun i => μ.real (s i))
    (hsμ : (fun i => μ.real (s i)) =ᶠ[li] m := by rfl) :
    (fun i => (∫ x in s i, f x ∂μ) - m i • f x) =o[li] m :=
  (hft x hx).integral_sub_linear_isLittleO_ae ht
    ⟨t, self_mem_nhdsWithin, hft.aestronglyMeasurable ht⟩ hs m hsμ
