/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Specific results about `ContinuousMap`-valued integration

In this file, we collect a few results regarding integrability, on a measure space `(X, μ)`,
of a `C(Y, E)`-valued function, where `Y` is a compact topological space and `E` is a normed group.

These are all elementary from a mathematical point of view, but they require a bit of care in order
to be conveniently usable. In particular, to accommodate the need of families `f : X → Y → E` such
that `f x` is only continuous for *almost every* `x`, we give a variety of results about the
integrability of `fun x ↦ ContinuousMap.mkD (f x) g` whose assumptions only mention `f` (so that
users don't have to convert between `f` and `fun x ↦ ContinuousMap.mkD (f x) g` by hand).

## Main results

* `hasFiniteIntegral_of_bound`: given `f : X → C(Y, E)`, the natural way to show
  `HasFiniteIntegral f` is to give a `bound : X → ℝ`, which itself has finite integral, and such
  that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
* `hasFiniteIntegral_mkD_of_bound` is the `mkD` analog of the above: given `f : X → Y → E` such
  that `f x` is continuous for almost every `x`, as well as a bound as above, we prove
  `HasFiniteIntegral (fun x ↦ mkD (f x) g)`. Note that, conveniently, `mkD` only appears in the
  result.
* `aeStronglyMeasurable_mkD_of_uncurry`: if now `X` is a topological space with the Borel σ-algebra,
  and `f : X → Y → E` is continuous on `X × Y`, then `fun x ↦ mkD (f x) g` is
  `AEStronglyMeasurable`. Note that this is far from optimal: this function is in fact continuous,
  and one could avoid `mkD` entirely since `f x` is always continuous in that case. Nevertheless,
  this turns out to be most convenient, as we explain below.

## Implementation Note

We claim that using "constructors with default values" such as `ContinuousMap.mkD` is the right way
to approach integration valued in a functional space `ℱ`. More precisely:

- if you happen to start from a bundled `f : X → ℱ` function, you should be able to use
  the general theory without any issues.
- if instead you start with a family of bare functions `f : X → Y → E`, to integrate it in `ℱ`, you
  should always consider the family `fun x ↦ ℱ.mkD (f x) 0`, *even if your `f` always lands in `ℱ`*.
  This allows for a unified setting with the case where `f x` belongs to `ℱ` for *almost every `x`*,
  and also avoids entering dependent-types hell.

-/

public section

open MeasureTheory

namespace ContinuousMap

variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [TopologicalSpace Y]
variable {E : Type*} [NormedAddCommGroup E]

/-- A natural criterion for `HasFiniteIntegral` of a `C(Y, E)`-valued function is the existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability assumption
on `Y`). We are just using the properties of Banach-space-valued integration. -/
/-
**ContinuousMap.hasFiniteIntegral_of_bound** 是 Mathlib 中的一个引理，位于命名空间 `Continuous
Map`。
形式化陈述：hasFiniteIntegral_of_bound [CompactSpace Y] (f : X -> C(Y, E)) (bound : X 
-> Real) (bound_int : HasFiniteIntegral bound μ) (bound_ge : forallᵐ x ∂μ, foral
l y : Y, ‖f x y‖ <= bound x) : HasFiniteIntegral f μ
参数：f : X -> C(Y, E)；bound : X -> Real；bound_int : HasFiniteIntegral bound μ；boun
d_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousMap.instSubsingletonOfIsEmpty`：∀ {X : Type u_1} {Y : Type u_2}
 [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [IsEmpty X],   Subsin
gleton C(X, Y)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.HasFiniteIntegral.mono'`：∀ {α : Type u_1} {β : Type u_2} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup 
β]   {f : α → β} {g : α → ℝ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C

--- 原说明 ---
A natural criterion for `HasFiniteIntegral` of a `C(Y, E)`-valued function is th
e existence
of some positive function with finite integral such that `∀ᵐ x ∂μ, ∀ y : Y, ‖f x
 y‖ ≤ bound x`.
Note that there is no dominated convergence here (hence no first-countability as
sumption
on `Y`). We are just using the properties of Banach-space-valued integration.
-/
lemma hasFiniteIntegral_of_bound [CompactSpace Y] (f : X → C(Y, E)) (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral f μ := by
  rcases isEmpty_or_nonempty Y with (h | h)
  · simp
  · have bound_nonneg : 0 ≤ᵐ[μ] bound := by
      filter_upwards [bound_ge] with x bound_x using le_trans (norm_nonneg _) (bound_x h.some)
    refine .mono' bound_int ?_
    filter_upwards [bound_ge, bound_nonneg] with x bound_ge_x bound_nonneg_x
    exact ContinuousMap.norm_le _ bound_nonneg_x |>.mpr bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMap.mkD`. -/
/-
**ContinuousMap.hasFiniteIntegral_mkD_of_bound** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousMap`。
形式化陈述：hasFiniteIntegral_mkD_of_bound [CompactSpace Y] (f : X -> Y -> E) (g : C(Y
, E)) (f_ae_cont : forallᵐ x ∂μ, Continuous (f x)) (bound : X -> Real) (bound_in
t : HasFiniteIntegral bound μ) (bound_ge : forallᵐ x ∂μ, forall y : Y, ‖f x y‖ <
= bound x) : HasFiniteIntegral (fun x => mkD (f x) g) μ
参数：f : X -> Y -> E；g : C(Y, E)；f_ae_cont : forallᵐ x ∂μ, Continuous (f x)；bound 
: X -> Real；bound_int : HasFiniteIntegral bound μ；bound_ge : forallᵐ x ∂μ, foral
l y : Y, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ContinuousMap.hasFiniteIntegral_of_bound`：hasFiniteIntegral_of_bound [Co
mpactSpace Y] (f : X -> C(Y, E)) (bound : X -> Real) (bound_int : HasFiniteInteg
ral bound μ) (bound_ge : foral…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMap.mkD_apply_of_continuous`：mkD_apply_of_continuous {f : α ->
 β} {g : C(α, β)} {x : α} (hf : Continuous f) : mkD f g x = f x

--- 原说明 ---
A variant of `ContinuousMap.hasFiniteIntegral_of_bound` spelled in terms of
`ContinuousMap.mkD`.
-/
lemma hasFiniteIntegral_mkD_of_bound [CompactSpace Y] (f : X → Y → E) (g : C(Y, E))
    (f_ae_cont : ∀ᵐ x ∂μ, Continuous (f x))
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y : Y, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (f x) g) μ := by
  refine hasFiniteIntegral_of_bound _ bound bound_int ?_
  filter_upwards [bound_ge, f_ae_cont] with x bound_ge_x cont_x
  simpa only [mkD_apply_of_continuous cont_x] using bound_ge_x

/-- A variant of `ContinuousMap.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set. -/
/-
**ContinuousMap.hasFiniteIntegral_mkD_restrict_of_bound** 是 Mathlib 中的一个引理，位于命名空
间 `ContinuousMap`。
形式化陈述：hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s] (f : 
X -> Y -> E) (g : C(s, E)) (f_ae_contOn : forallᵐ x ∂μ, ContinuousOn (f x) s) (b
ound : X -> Real) (bound_int : HasFiniteIntegral bound μ) (bound_ge : forallᵐ x 
∂μ, forall y in s, ‖f x y‖ <= bound x) : HasFiniteIntegral (fun x => mkD (s.domR
estrict (f x)) g) μ
参数：f : X -> Y -> E；g : C(s, E)；f_ae_contOn : forallᵐ x ∂μ, ContinuousOn (f x) s；
bound : X -> Real；bound_int : HasFiniteIntegral bound μ；bound_ge : forallᵐ x ∂μ,
 forall y in s, ‖f x y‖ <= bound x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ContinuousMap.hasFiniteIntegral_mkD_of_bound`：hasFiniteIntegral_mkD_of_b
ound [CompactSpace Y] (f : X -> Y -> E) (g : C(Y, E)) (f_ae_cont : forallᵐ x ∂μ,
 Continuous (f x)) (bound : X -> R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A variant of `ContinuousMap.hasFiniteIntegral_mkD_of_bound` for a family of
functions which are continuous on a compact set.
-/
lemma hasFiniteIntegral_mkD_restrict_of_bound {s : Set Y} [CompactSpace s]
    (f : X → Y → E) (g : C(s, E))
    (f_ae_contOn : ∀ᵐ x ∂μ, ContinuousOn (f x) s)
    (bound : X → ℝ)
    (bound_int : HasFiniteIntegral bound μ)
    (bound_ge : ∀ᵐ x ∂μ, ∀ y ∈ s, ‖f x y‖ ≤ bound x) :
    HasFiniteIntegral (fun x ↦ mkD (s.domRestrict (f x)) g) μ := by
  refine hasFiniteIntegral_mkD_of_bound _ _ ?_ bound bound_int ?_
  · simpa [← continuousOn_iff_continuous_domRestrict]
  · simpa
/-
**ContinuousMap.aeStronglyMeasurable_mkD_of_uncurry** 是 Mathlib 中的一个引理，位于命名空间 `C
ontinuousMap`。
形式化陈述：aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [TopologicalSpace X] 
[OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))] (f : X -> Y
 -> E) (g : C(Y, E)) (f_cont : Continuous (Function.uncurry f)) : AEStronglyMeas
urable (fun x => mkD (f x) g) μ
参数：C(Y, E)；f : X -> Y -> E；g : C(Y, E)；f_cont : Continuous (Function.uncurry f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMap.continuous_mkD_of_uncurry`：continuous_mkD_of_uncurry (f : 
T -> X -> Y) (g : C(X, Y)) (f_cont : Continuous (Function.uncurry f)) : Continuo
us (fun x => mkD (f x) g)
-/
lemma aeStronglyMeasurable_mkD_of_uncurry [CompactSpace Y] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (f : X → Y → E) (g : C(Y, E)) (f_cont : Continuous (Function.uncurry f)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) μ :=
  continuous_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
/-
**ContinuousMap.aeStronglyMeasurable_restrict_mkD_of_uncurry** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousMap`。
形式化陈述：aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] {s : Set X} 
[TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (
C(Y, E))] (hs : MeasurableSet s) (f : X -> Y -> E) (g : C(Y, E)) (f_cont : Conti
nuousOn (Function.uncurry f) (s ×ˢ univ)) : AEStronglyMeasurable (fun x => mkD (
f x) g) (μ.restrict s)
参数：C(Y, E)；hs : MeasurableSet s；f : X -> Y -> E；g : C(Y, E)；f_cont : ContinuousO
n (Function.uncurry f) (s ×ˢ univ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMap.continuousOn_mkD_of_uncurry`：continuousOn_mkD_of_uncurry {
s : Set T} (f : T -> X -> Y) (g : C(X, Y)) (f_cont : ContinuousOn (Function.uncu
rry f) (s ×ˢ univ)) : Continuou…
-/
lemma aeStronglyMeasurable_restrict_mkD_of_uncurry [CompactSpace Y] {s : Set X}
    [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(Y, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(Y, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ univ)) :
    AEStronglyMeasurable (fun x ↦ mkD (f x) g) (μ.restrict s) :=
  continuousOn_mkD_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

open Set in
/-
**ContinuousMap.aeStronglyMeasurable_mkD_restrict_of_uncurry** 是 Mathlib 中的一个引理，
位于命名空间 `ContinuousMap`。
形式化陈述：aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] 
[TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopologyEither X (
C(t, E))] (f : X -> Y -> E) (g : C(t, E)) (f_cont : ContinuousOn (Function.uncur
ry f) (univ ×ˢ t)) : AEStronglyMeasurable (fun x => mkD (t.domRestrict (f x)) g)
 μ
参数：C(t, E)；f : X -> Y -> E；g : C(t, E)；f_cont : ContinuousOn (Function.uncurry f
) (univ ×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMap.continuous_mkD_restrict_of_uncurry`：continuous_mkD_restric
t_of_uncurry {t : Set X} (f : T -> X -> Y) (g : C(t, Y)) (f_cont : ContinuousOn 
(Function.uncurry f) (univ ×ˢ t)) : Co…
-/
lemma aeStronglyMeasurable_mkD_restrict_of_uncurry {t : Set Y} [CompactSpace t] [TopologicalSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopologyEither X (C(t, E))]
    (f : X → Y → E) (g : C(t, E)) (f_cont : ContinuousOn (Function.uncurry f) (univ ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.domRestrict (f x)) g) μ :=
  continuous_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable

open Set in
/-
**ContinuousMap.aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry** 是 Mathli
b 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set
 Y} [CompactSpace t] [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCounta
bleTopologyEither X (C(t, E))] (hs : MeasurableSet s) (f : X -> Y -> E) (g : C(t
, E)) (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) : AEStronglyMeasurab
le (fun x => mkD (t.domRestrict (f x)) g) (μ.restrict s)
参数：C(t, E)；hs : MeasurableSet s；f : X -> Y -> E；g : C(t, E)；f_cont : ContinuousO
n (Function.uncurry f) (s ×ˢ t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `ContinuousMap.continuousOn_mkD_restrict_of_uncurry`：continuousOn_mkD_res
trict_of_uncurry {s : Set T} {t : Set X} (f : T -> X -> Y) (g : C(t, Y)) (f_cont
 : ContinuousOn (Function.uncurry f) (s …
-/
lemma aeStronglyMeasurable_restrict_mkD_restrict_of_uncurry {s : Set X} {t : Set Y}
    [CompactSpace t] [TopologicalSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopologyEither X (C(t, E))]
    (hs : MeasurableSet s) (f : X → Y → E) (g : C(t, E))
    (f_cont : ContinuousOn (Function.uncurry f) (s ×ˢ t)) :
    AEStronglyMeasurable (fun x ↦ mkD (t.domRestrict (f x)) g) (μ.restrict s) :=
  continuousOn_mkD_restrict_of_uncurry _ _ f_cont |>.aestronglyMeasurable hs

end ContinuousMap

