/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `MeasureTheory.AECover`. It is a rather technical definition
whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a countably
generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable space `α`
equipped with a measure `μ`, one should think of a hypothesis `hφ : MeasureTheory.AECover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x
in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often, one
should not try too hard to use a `MeasureTheory.AECover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_tendsto` where we use `(fun x ↦ oi x)` as a
`MeasureTheory.AECover` w.r.t. `μ.restrict (Iic b)`, instead of using `(fun x ↦ Ioc x b)`.

## Main statements

- `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is a measurable
  `ENNReal`-valued function, then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`

- `MeasureTheory.AECover.integrable_of_integral_norm_tendsto` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, if `f` is measurable and
  integrable on each `φ n`, and if `∫ x in φ n, ‖f x‖ ∂μ` tends to some `I : ℝ` as n tends to `l`,
  then `f` is integrable

- `MeasureTheory.AECover.integral_tendsto_of_countably_generated` : if `φ` is a
  `MeasureTheory.AECover μ l`, where `l` is a countably generated filter, and if `f` is measurable
  and integrable (globally), then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis. In particular,

- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` is a version of FTC-2 on the interval
  `(a, +∞)`, giving the formula `∫ x in (a, +∞), g' x = l - g a` if `g'` is integrable and
  `g` tends to `l` at `+∞`.
- `MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg` gives the same result assuming that
  `g'` is nonnegative instead of integrable. Its automatic integrability in this context is proved
  in `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`.
- `MeasureTheory.integral_deriv_smul_comp_Ioi` is a version of the change of variables formula
  on semi-infinite intervals.
- `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` shows that a function whose
  derivative is integrable on `(a, +∞)` has a limit at `+∞`.
- `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` shows that an integrable function
  whose derivative is integrable on `(a, +∞)` tends to `0` at `+∞`.

Versions of these results are also given on the intervals `(-∞, a]` and `(-∞, +∞)`, as well as
the corresponding versions of integration by parts.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal

namespace MeasureTheory

section AECover

variable {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (l : Filter ι)

/-- A sequence `φ` of subsets of `α` is a `MeasureTheory.AECover` w.r.t. a measure `μ` and a filter
`l` if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
each `φ n` is measurable.  This definition is a technical way to avoid duplicating a lot of
proofs.  It should be thought of as a sufficient condition for being able to interpret
`∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.
See for example `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`,
`MeasureTheory.AECover.integrable_of_integral_norm_tendsto` and
`MeasureTheory.AECover.integral_tendsto_of_countably_generated`. -/
/-
**MeasureTheory.AECover** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {ι : Type u_2} → [inst : MeasurableSpace α] → MeasureTheo
ry.Measure α → Filter ι → (ι → Set α) → Prop
参数：ι → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence `φ` of subsets of `α` is a `MeasureTheory.AECover` w.r.t. a measure `
μ` and a filter
`l` if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t
. `l`), and if
each `φ n` is measurable.  This definition is a technical way to avoid duplicati
ng a lot of
proofs.  It should be thought of as a sufficient condition for being able to int
erpret
`∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends t
o `l`.
See for example `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`
,
`MeasureTheory.AECover.integrable_of_integral_norm_tendsto` and
`MeasureTheory.AECover.integral_tendsto_of_countably_generated`.
-/
structure AECover (φ : ι → Set α) : Prop where
  ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ φ i
  protected measurableSet : ∀ i, MeasurableSet <| φ i

variable {μ} {l}

namespace AECover

/-!
## Operations on `AECover`s
-/

/-- Elementwise intersection of two `AECover`s is an `AECover`. -/
/-
**MeasureTheory.AECover.inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：inter {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ) : AECov
er μ l (fun i => φ i inter ψ i) where ae_eventually_mem
参数：hφ : AECover μ l φ；hψ : AECover μ l ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…

--- 原说明 ---
Elementwise intersection of two `AECover`s is an `AECover`.
-/
theorem inter {φ ψ : ι → Set α} (hφ : AECover μ l φ) (hψ : AECover μ l ψ) :
    AECover μ l (fun i ↦ φ i ∩ ψ i) where
  ae_eventually_mem := hψ.1.mp <| hφ.1.mono fun _ ↦ Eventually.and
  measurableSet _ := (hφ.2 _).inter (hψ.2 _)
/-
**MeasureTheory.AECover.superset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AECove
r`。
形式化陈述：superset {φ ψ : ι -> Set α} (hφ : AECover μ l φ) (hsub : forall i, φ i sub
seteq ψ i) (hmeas : forall i, MeasurableSet (ψ i)) : AECover μ l ψ
参数：hφ : AECover μ l φ；hsub : forall i, φ i subseteq ψ i；hmeas : forall i, Measur
ableSet (ψ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
-/
theorem superset {φ ψ : ι → Set α} (hφ : AECover μ l φ) (hsub : ∀ i, φ i ⊆ ψ i)
    (hmeas : ∀ i, MeasurableSet (ψ i)) : AECover μ l ψ :=
  ⟨hφ.1.mono fun _x hx ↦ hx.mono fun i hi ↦ hsub i hi, hmeas⟩
/-
**MeasureTheory.AECover.mono_ac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AECover
`。
形式化陈述：mono_ac {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν ≪ μ
) : AECover ν l φ
参数：hφ : AECover μ l φ；hle : ν ≪ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
-/
theorem mono_ac {ν : Measure α} {φ : ι → Set α} (hφ : AECover μ l φ) (hle : ν ≪ μ) :
    AECover ν l φ := ⟨hle hφ.1, hφ.2⟩
/-
**MeasureTheory.AECover.mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：mono {ν : Measure α} {φ : ι -> Set α} (hφ : AECover μ l φ) (hle : ν <= μ) 
: AECover ν l φ
参数：hφ : AECover μ l φ；hle : ν <= μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono_ac`：mono_ac {ν : Measure α} {φ : ι -> Set α} 
(hφ : AECover μ l φ) (hle : ν ≪ μ) : AECover ν l φ
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
-/
theorem mono {ν : Measure α} {φ : ι → Set α} (hφ : AECover μ l φ) (hle : ν ≤ μ) :
    AECover ν l φ := hφ.mono_ac hle.absolutelyContinuous

end AECover

section MetricSpace

variable [PseudoMetricSpace α] [OpensMeasurableSpace α]

/-
**MeasureTheory.aecover_ball** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_ball {x : α} {r : ι -> Real} (hr : Tendsto r l atTop) : AECover μ 
l (fun i => Metric.ball x (r i)) where measurableSet _
参数：hr : Tendsto r l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
theorem aecover_ball {x : α} {r : ι → ℝ} (hr : Tendsto r l atTop) :
    AECover μ l (fun i ↦ Metric.ball x (r i)) where
  measurableSet _ := Metric.isOpen_ball.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ioi_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha
/-
**MeasureTheory.aecover_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_closedBall {x : α} {r : ι -> Real} (hr : Tendsto r l atTop) : AECo
ver μ l (fun i => Metric.closedBall x (r i)) where measurableSet _
参数：hr : Tendsto r l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
theorem aecover_closedBall {x : α} {r : ι → ℝ} (hr : Tendsto r l atTop) :
    AECover μ l (fun i ↦ Metric.closedBall x (r i)) where
  measurableSet _ := Metric.isClosed_closedBall.measurableSet
  ae_eventually_mem := by
    filter_upwards with y
    filter_upwards [hr (Ici_mem_atTop (dist x y))] with a ha using by simpa [dist_comm] using ha

end MetricSpace

section Preorderα

variable [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι → α}

/-
**MeasureTheory.aecover_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ici (ha : Tendsto a l atBot) : AECover μ l fun i => Ici (a i) wher
e ae_eventually_mem
参数：ha : Tendsto a l atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.eventually_le_atBot`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atBot → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem aecover_Ici (ha : Tendsto a l atBot) : AECover μ l fun i => Ici (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_le_atBot
  measurableSet _ := measurableSet_Ici
/-
**MeasureTheory.aecover_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Iic (hb : Tendsto b l atTop) : AECover μ l fun i => Iic b i
参数：hb : Tendsto b l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ici`：aecover_Ici (ha : Tendsto a l atBot) : AECove
r μ l fun i => Ici (a i) where ae_eventually_mem
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.opensMeasurableSpace`：∀ {α : Type u_6} [inst : TopologicalSpac
e α] [inst_1 : MeasurableSpace α] [h : OpensMeasurableSpace α],   OpensMeasurabl
eSpace αᵒᵈ
-/
theorem aecover_Iic (hb : Tendsto b l atTop) : AECover μ l fun i => Iic <| b i :=
  aecover_Ici (α := αᵒᵈ) hb
/-
**MeasureTheory.aecover_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Icc (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) : AECover μ 
l fun i => Icc (a i) (b i)
参数：ha : Tendsto a l atBot；hb : Tendsto b l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.inter`：inter {φ ψ : ι -> Set α} (hφ : AECover μ l 
φ) (hψ : AECover μ l ψ) : AECover μ l (fun i => φ i inter ψ i) where ae_eventual
ly_mem
· 使用定理 `MeasureTheory.aecover_Ici`：aecover_Ici (ha : Tendsto a l atBot) : AECove
r μ l fun i => Ici (a i) where ae_eventually_mem
· 使用定理 `MeasureTheory.aecover_Iic`：aecover_Iic (hb : Tendsto b l atTop) : AECove
r μ l fun i => Iic b i
-/
theorem aecover_Icc (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) :
    AECover μ l fun i => Icc (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iic hb)

end Preorderα

section LinearOrderα

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b : ι → α} (ha : Tendsto a l atBot) (hb : Tendsto b l atTop)

include ha in
/-
**MeasureTheory.aecover_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioi [NoMinOrder α] : AECover μ l fun i => Ioi (a i) where ae_event
ually_mem
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.eventually_lt_atBot`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoBotOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atBot → ∀ (c : β)…
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
-/
theorem aecover_Ioi [NoMinOrder α] : AECover μ l fun i => Ioi (a i) where
  ae_eventually_mem := ae_of_all μ ha.eventually_lt_atBot
  measurableSet _ := measurableSet_Ioi

include hb in
/-
**MeasureTheory.aecover_Iio** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Iio [NoMaxOrder α] : AECover μ l fun i => Iio (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioi`：aecover_Ioi [NoMinOrder α] : AECover μ l fun 
i => Ioi (a i) where ae_eventually_mem
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.opensMeasurableSpace`：∀ {α : Type u_6} [inst : TopologicalSpac
e α] [inst_1 : MeasurableSpace α] [h : OpensMeasurableSpace α],   OpensMeasurabl
eSpace αᵒᵈ
-/
theorem aecover_Iio [NoMaxOrder α] : AECover μ l fun i => Iio (b i) := aecover_Ioi (α := αᵒᵈ) hb

include ha hb
/-
**MeasureTheory.aecover_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioo [NoMinOrder α] [NoMaxOrder α] : AECover μ l fun i => Ioo (a i)
 (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.inter`：inter {φ ψ : ι -> Set α} (hφ : AECover μ l 
φ) (hψ : AECover μ l ψ) : AECover μ l (fun i => φ i inter ψ i) where ae_eventual
ly_mem
· 使用定理 `MeasureTheory.aecover_Ioi`：aecover_Ioi [NoMinOrder α] : AECover μ l fun 
i => Ioi (a i) where ae_eventually_mem
· 使用定理 `MeasureTheory.aecover_Iio`：aecover_Iio [NoMaxOrder α] : AECover μ l fun 
i => Iio (b i)
-/
theorem aecover_Ioo [NoMinOrder α] [NoMaxOrder α] : AECover μ l fun i => Ioo (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iio hb)
/-
**MeasureTheory.aecover_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioc [NoMinOrder α] : AECover μ l fun i => Ioc (a i) (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.inter`：inter {φ ψ : ι -> Set α} (hφ : AECover μ l 
φ) (hψ : AECover μ l ψ) : AECover μ l (fun i => φ i inter ψ i) where ae_eventual
ly_mem
· 使用定理 `MeasureTheory.aecover_Ioi`：aecover_Ioi [NoMinOrder α] : AECover μ l fun 
i => Ioi (a i) where ae_eventually_mem
· 使用定理 `MeasureTheory.aecover_Iic`：aecover_Iic (hb : Tendsto b l atTop) : AECove
r μ l fun i => Iic b i
-/
theorem aecover_Ioc [NoMinOrder α] : AECover μ l fun i => Ioc (a i) (b i) :=
  (aecover_Ioi ha).inter (aecover_Iic hb)
/-
**MeasureTheory.aecover_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ico [NoMaxOrder α] : AECover μ l fun i => Ico (a i) (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.inter`：inter {φ ψ : ι -> Set α} (hφ : AECover μ l 
φ) (hψ : AECover μ l ψ) : AECover μ l (fun i => φ i inter ψ i) where ae_eventual
ly_mem
· 使用定理 `MeasureTheory.aecover_Ici`：aecover_Ici (ha : Tendsto a l atBot) : AECove
r μ l fun i => Ici (a i) where ae_eventually_mem
· 使用定理 `MeasureTheory.aecover_Iio`：aecover_Iio [NoMaxOrder α] : AECover μ l fun 
i => Iio (b i)
-/
theorem aecover_Ico [NoMaxOrder α] : AECover μ l fun i => Ico (a i) (b i) :=
  (aecover_Ici ha).inter (aecover_Iio hb)

end LinearOrderα

section FiniteIntervals

variable [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] [OpensMeasurableSpace α]
  {a b c d : ι → α} {A B : α} (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
  (hc : Tendsto c l atBot) (hd : Tendsto d l atTop)

include ha in
/-
**MeasureTheory.aecover_Ioi_of_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioi_of_Ioi : AECover (μ.restrict (Ioi A)) l fun i => Ioi (a i) whe
re ae_eventually_mem
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem aecover_Ioi_of_Ioi : AECover (μ.restrict (Ioi A)) l fun i ↦ Ioi (a i) where
  ae_eventually_mem := (ae_restrict_mem measurableSet_Ioi).mono fun _x hx ↦ ha.eventually <|
    eventually_lt_nhds hx
  measurableSet _ := measurableSet_Ioi

include hb in
/-
**MeasureTheory.aecover_Iio_of_Iio** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Iio_of_Iio : AECover (μ.restrict (Iio B)) l fun i => Iio (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioi_of_Ioi`：aecover_Ioi_of_Ioi : AECover (μ.restri
ct (Ioi A)) l fun i => Ioi (a i) where ae_eventually_mem
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.opensMeasurableSpace`：∀ {α : Type u_6} [inst : TopologicalSpac
e α] [inst_1 : MeasurableSpace α] [h : OpensMeasurableSpace α],   OpensMeasurabl
eSpace αᵒᵈ
-/
theorem aecover_Iio_of_Iio : AECover (μ.restrict (Iio B)) l fun i ↦ Iio (b i) :=
  aecover_Ioi_of_Ioi (α := αᵒᵈ) hb

include ha in
/-
**MeasureTheory.aecover_Ioi_of_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioi_of_Ici : AECover (μ.restrict (Ioi A)) l fun i => Ici (a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.superset`：superset {φ ψ : ι -> Set α} (hφ : AECove
r μ l φ) (hsub : forall i, φ i subseteq ψ i) (hmeas : forall i, MeasurableSet (ψ
 i)) : AECover μ l ψ
· 使用定理 `MeasureTheory.aecover_Ioi_of_Ioi`：aecover_Ioi_of_Ioi : AECover (μ.restri
ct (Ioi A)) l fun i => Ioi (a i) where ae_eventually_mem
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem aecover_Ioi_of_Ici : AECover (μ.restrict (Ioi A)) l fun i ↦ Ici (a i) :=
  (aecover_Ioi_of_Ioi ha).superset (fun _ ↦ Ioi_subset_Ici_self) fun _ ↦ measurableSet_Ici

include hb in
/-
**MeasureTheory.aecover_Iio_of_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Iio_of_Iic : AECover (μ.restrict (Iio B)) l fun i => Iic (b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioi_of_Ici`：aecover_Ioi_of_Ici : AECover (μ.restri
ct (Ioi A)) l fun i => Ici (a i)
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `OrderDual.opensMeasurableSpace`：∀ {α : Type u_6} [inst : TopologicalSpac
e α] [inst_1 : MeasurableSpace α] [h : OpensMeasurableSpace α],   OpensMeasurabl
eSpace αᵒᵈ
-/
theorem aecover_Iio_of_Iic : AECover (μ.restrict (Iio B)) l fun i ↦ Iic (b i) :=
  aecover_Ioi_of_Ici (α := αᵒᵈ) hb

include hb hc in
/-
**MeasureTheory.aecover_Iio_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Iio_of_Ico : AECover (μ.restrict (Iio B)) l fun i => Ico (c i) (b 
i) where ae_eventually_mem
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Iio`：measurableSet_Iio [ClosedIciTopology α] : MeasurableS
et (Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
-/
theorem aecover_Iio_of_Ico : AECover (μ.restrict (Iio B)) l fun i ↦ Ico (c i) (b i) where
  ae_eventually_mem := by
    refine (ae_restrict_mem measurableSet_Iio).mono fun _x hx ↦ ?_
    simp only [mem_Ico, eventually_and]
    exact ⟨hc.eventually (eventually_le_atBot _x), hb.eventually (eventually_gt_nhds hx)⟩
  measurableSet _ := measurableSet_Ico

include hd in
/-
**MeasureTheory.aecover_Ici_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ici_of_Ico [NoMaxOrder α] : AECover (μ.restrict (Ici B)) l fun i =
> Ico B (d i) where ae_eventually_mem
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
-/
theorem aecover_Ici_of_Ico [NoMaxOrder α] : AECover (μ.restrict (Ici B)) l fun i ↦ Ico B (d i) where
  ae_eventually_mem := by
    refine (ae_restrict_mem measurableSet_Ici).mono fun _x hx ↦ ?_
    simp only [mem_Ico, eventually_and]
    exact⟨.of_forall fun i => hx, hd.eventually (eventually_gt_atTop _x)⟩
  measurableSet _ := measurableSet_Ico

include ha hb in
/-
**MeasureTheory.aecover_Ioo_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioo_of_Ioo : AECover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) 
(b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.inter`：inter {φ ψ : ι -> Set α} (hφ : AECover μ l 
φ) (hψ : AECover μ l ψ) : AECover μ l (fun i => φ i inter ψ i) where ae_eventual
ly_mem
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioi_of_Ioi`：aecover_Ioi_of_Ioi : AECover (μ.restri
ct (Ioi A)) l fun i => Ioi (a i) where ae_eventually_mem
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.aecover_Iio_of_Iio`：aecover_Iio_of_Iio : AECover (μ.restri
ct (Iio B)) l fun i => Iio (b i)
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
theorem aecover_Ioo_of_Ioo : AECover (μ.restrict <| Ioo A B) l fun i => Ioo (a i) (b i) :=
  ((aecover_Ioi_of_Ioi ha).mono <| Measure.restrict_mono Ioo_subset_Ioi_self le_rfl).inter
    ((aecover_Iio_of_Iio hb).mono <| Measure.restrict_mono Ioo_subset_Iio_self le_rfl)

include ha hb in
/-
**MeasureTheory.aecover_Ioo_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioo_of_Icc : AECover (μ.restrict <| Ioo A B) l fun i => Icc (a i) 
(b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.superset`：superset {φ ψ : ι -> Set α} (hφ : AECove
r μ l φ) (hsub : forall i, φ i subseteq ψ i) (hmeas : forall i, MeasurableSet (ψ
 i)) : AECover μ l ψ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
-/
theorem aecover_Ioo_of_Icc : AECover (μ.restrict <| Ioo A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Icc_self) fun _ ↦ measurableSet_Icc

include ha hb in
/-
**MeasureTheory.aecover_Ioo_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioo_of_Ico : AECover (μ.restrict <| Ioo A B) l fun i => Ico (a i) 
(b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.superset`：superset {φ ψ : ι -> Set α} (hφ : AECove
r μ l φ) (hsub : forall i, φ i subseteq ψ i) (hmeas : forall i, MeasurableSet (ψ
 i)) : AECover μ l ψ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem aecover_Ioo_of_Ico : AECover (μ.restrict <| Ioo A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Ico_self) fun _ ↦ measurableSet_Ico

include ha hb in
/-
**MeasureTheory.aecover_Ioo_of_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioo_of_Ioc : AECover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) 
(b i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.superset`：superset {φ ψ : ι -> Set α} (hφ : AECove
r μ l φ) (hsub : forall i, φ i subseteq ψ i) (hmeas : forall i, MeasurableSet (ψ
 i)) : AECover μ l ψ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
-/
theorem aecover_Ioo_of_Ioc : AECover (μ.restrict <| Ioo A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).superset (fun _ ↦ Ioo_subset_Ioc_self) fun _ ↦ measurableSet_Ioc

variable [NullSingletonClass μ]
/-
**MeasureTheory.aecover_Ioc_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ioc A B) l fun i => Icc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Icc`：aecover_Ioo_of_Icc : AECover (μ.restri
ct <| Ioo A B) l fun i => Icc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem aecover_Ioc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge
/-
**MeasureTheory.aecover_Ioc_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ioc A B) l fun i => Ico (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ico`：aecover_Ioo_of_Ico : AECover (μ.restri
ct <| Ioo A B) l fun i => Ico (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem aecover_Ioc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge
/-
**MeasureTheory.aecover_Ioc_of_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ioc A B) l fun i => Ioc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioc`：aecover_Ioo_of_Ioc : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem aecover_Ioc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge
/-
**MeasureTheory.aecover_Ioc_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ioc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ioc A B) l fun i => Ioo (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem aecover_Ioc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ioc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ioc).ge
/-
**MeasureTheory.aecover_Ico_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ico_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ico A B) l fun i => Icc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Icc`：aecover_Ioo_of_Icc : AECover (μ.restri
ct <| Ioo A B) l fun i => Icc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico`：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
-/
theorem aecover_Ico_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge
/-
**MeasureTheory.aecover_Ico_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ico_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ico A B) l fun i => Ico (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ico`：aecover_Ioo_of_Ico : AECover (μ.restri
ct <| Ioo A B) l fun i => Ico (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico`：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
-/
theorem aecover_Ico_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge
/-
**MeasureTheory.aecover_Ico_of_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ico_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ico A B) l fun i => Ioc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioc`：aecover_Ioo_of_Ioc : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico`：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
-/
theorem aecover_Ico_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge
/-
**MeasureTheory.aecover_Ico_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Ico_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Ico A B) l fun i => Ioo (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico`：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
-/
theorem aecover_Ico_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Ico A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Ico).ge
/-
**MeasureTheory.aecover_Icc_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Icc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Icc A B) l fun i => Icc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Icc`：aecover_Ioo_of_Icc : AECover (μ.restri
ct <| Ioo A B) l fun i => Icc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem aecover_Icc_of_Icc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Icc (a i) (b i) :=
  (aecover_Ioo_of_Icc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge
/-
**MeasureTheory.aecover_Icc_of_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Icc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Icc A B) l fun i => Ico (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ico`：aecover_Ioo_of_Ico : AECover (μ.restri
ct <| Ioo A B) l fun i => Ico (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem aecover_Icc_of_Ico (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ico (a i) (b i) :=
  (aecover_Ioo_of_Ico ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge
/-
**MeasureTheory.aecover_Icc_of_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Icc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Icc A B) l fun i => Ioc (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioc`：aecover_Ioo_of_Ioc : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioc (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem aecover_Icc_of_Ioc (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioc (a i) (b i) :=
  (aecover_Ioo_of_Ioc ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge
/-
**MeasureTheory.aecover_Icc_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：aecover_Icc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AEC
over (μ.restrict <| Icc A B) l fun i => Ioo (a i) (b i)
参数：ha : Tendsto a l (𝓝 A)；hb : Tendsto b l (𝓝 B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.aecover_Ioo_of_Ioo`：aecover_Ioo_of_Ioo : AECover (μ.restri
ct <| Ioo A B) l fun i => Ioo (a i) (b i)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem aecover_Icc_of_Ioo (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B)) :
    AECover (μ.restrict <| Icc A B) l fun i => Ioo (a i) (b i) :=
  (aecover_Ioo_of_Ioo ha hb).mono (Measure.restrict_congr_set Ioo_ae_eq_Icc).ge

end FiniteIntervals

/-
**MeasureTheory.AECover.restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AECove
r`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} {φ : ι → Set α},   MeasureTheory.AECover μ l φ → ∀
 {s : Set α}, MeasureTheory.AECover (μ.restrict s) l φ
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.mono`：mono {ν : Measure α} {φ : ι -> Set α} (hφ : 
AECover μ l φ) (hle : ν <= μ) : AECover ν l φ
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
protected theorem AECover.restrict {φ : ι → Set α} (hφ : AECover μ l φ) {s : Set α} :
    AECover (μ.restrict s) l φ :=
  hφ.mono Measure.restrict_le_self
/-
**MeasureTheory.aecover_restrict_of_ae_imp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：aecover_restrict_of_ae_imp {s : Set α} {φ : ι -> Set α} (hs : MeasurableSe
t s) (ae_eventually_mem : forallᵐ x ∂μ, x in s -> forallᶠ n in l, x in φ n) (mea
surable : forall n, MeasurableSet <| φ n) : AECover (μ.restrict s) l φ where ae_
eventually_mem
参数：hs : MeasurableSet s；ae_eventually_mem : forallᵐ x ∂μ, x in s -> forallᶠ n in
 l, x in φ n；measurable : forall n, MeasurableSet <| φ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem aecover_restrict_of_ae_imp {s : Set α} {φ : ι → Set α} (hs : MeasurableSet s)
    (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in l, x ∈ φ n)
    (measurable : ∀ n, MeasurableSet <| φ n) : AECover (μ.restrict s) l φ where
  ae_eventually_mem := by rwa [ae_restrict_iff' hs]
  measurableSet := measurable
/-
**MeasureTheory.AECover.inter_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} {φ : ι → Set α},   MeasureTheory.AECover μ l φ → ∀
 {s : Set α}, MeasurableSet s → MeasureTheory.AECover (μ.restrict s) l fun i => 
φ i ∩ s
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_restrict_of_ae_imp`：aecover_restrict_of_ae_imp {s 
: Set α} {φ : ι -> Set α} (hs : MeasurableSet s) (ae_eventually_mem : forallᵐ x 
∂μ, x in s -> forallᶠ n in l, …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
-/
theorem AECover.inter_restrict {φ : ι → Set α} (hφ : AECover μ l φ) {s : Set α}
    (hs : MeasurableSet s) : AECover (μ.restrict s) l fun i => φ i ∩ s :=
  aecover_restrict_of_ae_imp hs
    (hφ.ae_eventually_mem.mono fun _x hx hxs => hx.mono fun _i hi => ⟨hi, hxs⟩) fun i =>
    (hφ.measurableSet i).inter hs
/-
**MeasureTheory.AECover.ae_tendsto_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} {β : Type u_3}   [inst_1 : Zero β] [inst_2 : Topol
ogicalSpace β] (f : α → β) {φ : ι → Set α},   MeasureTheory.AECover μ l φ → ∀ᵐ (
x : α) ∂μ, Filter.Tendsto (fun i => (φ i).indicator f x) l (nhds (f x))
参数：f : α → β；x : α；fun i => (φ i).indicator f x；nhds (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem AECover.ae_tendsto_indicator {β : Type*} [Zero β] [TopologicalSpace β] (f : α → β)
    {φ : ι → Set α} (hφ : AECover μ l φ) :
    ∀ᵐ x ∂μ, Tendsto (fun i => (φ i).indicator f x) l (𝓝 <| f x) :=
  hφ.ae_eventually_mem.mono fun _x hx =>
    tendsto_const_nhds.congr' <| hx.mono fun _n hn => (indicator_of_mem hn _).symm
/-
**MeasureTheory.AECover.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
Cover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} {β : Type u_3}   [inst_1 : MeasurableSpace β] [l.I
sCountablyGenerated] [l.NeBot] {f : α → β} {φ : ι → Set α},   MeasureTheory.AECo
ver μ l φ → (∀ (i : ι), AEMeasurable f (μ.restrict (φ i))) → AEMeasurable f μ
参数：∀ (i : ι), AEMeasurable f (μ.restrict (φ i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aemeasurable_iUnion_iff`：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} 
{m0 : MeasurableSpace α} [inst : MeasurableSpace β] {f : α → β}   {μ : MeasureTh
eory.Measure …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
-/
theorem AECover.aemeasurable {β : Type*} [MeasurableSpace β] [l.IsCountablyGenerated] [l.NeBot]
    {f : α → β} {φ : ι → Set α} (hφ : AECover μ l φ)
    (hfm : ∀ i, AEMeasurable f (μ.restrict <| φ i)) : AEMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aemeasurable_iUnion_iff.mpr fun n : ℕ => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    mem_iUnion.mpr (hu.eventually hx).exists
/-
**MeasureTheory.AECover.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} {β : Type u_3}   [inst_1 : TopologicalSpace β] [To
pologicalSpace.PseudoMetrizableSpace β] [l.IsCountablyGenerated] [l.NeBot]   {f 
: α → β} {φ : ι → Set α},   MeasureTheory.AECover μ l φ →     (∀ (i : ι), Measur
eTheory.AEStronglyMeasurable f (μ.restrict (φ i))) → MeasureTheory.AEStronglyMea
surable f μ
参数：∀ (i : ι), MeasureTheory.AEStronglyMeasurable f (μ.restrict (φ i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `aestronglyMeasurable_iUnion_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Ty
pe u_4} [Countable ι] [inst : TopologicalSpace β] {m₀ : MeasurableSpace α}   {μ 
: MeasureTheory.Measu…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_eq_self_of_ae_mem`：restrict_eq_self_of_ae
_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄ (hs : forallᵐ x ∂μ, x
 in s) : μ.restrict s = μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
-/
theorem AECover.aestronglyMeasurable {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [l.IsCountablyGenerated] [l.NeBot] {f : α → β} {φ : ι → Set α} (hφ : AECover μ l φ)
    (hfm : ∀ i, AEStronglyMeasurable f (μ.restrict <| φ i)) : AEStronglyMeasurable f μ := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have := aestronglyMeasurable_iUnion_iff.mpr fun n : ℕ => hfm (u n)
  rwa [Measure.restrict_eq_self_of_ae_mem] at this
  filter_upwards [hφ.ae_eventually_mem] with x hx using mem_iUnion.mpr (hu.eventually hx).exists

end AECover

/-
**MeasureTheory.AECover.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
Cover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {ι' : Type u_3} [inst : MeasurableSpace α]
 {μ : MeasureTheory.Measure α} {l : Filter ι}   {l' : Filter ι'} {φ : ι → Set α}
,   MeasureTheory.AECover μ l φ → ∀ {u : ι' → ι}, Filter.Tendsto u l' l → Measur
eTheory.AECover μ l' (φ ∘ u)
参数：φ ∘ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
-/
theorem AECover.comp_tendsto {α ι ι' : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {l' : Filter ι'} {φ : ι → Set α} (hφ : AECover μ l φ) {u : ι' → ι} (hu : Tendsto u l' l) :
    AECover μ l' (φ ∘ u) where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun _x hx => hu.eventually hx
  measurableSet i := hφ.measurableSet (u i)

section AECoverUnionInterCountable

variable {α ι : Type*} [Countable ι] [MeasurableSpace α] {μ : Measure α}

/-
**MeasureTheory.AECover.biUnion_Iic_aecover** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [Countable ι] [inst : MeasurableSpace α] {
μ : MeasureTheory.Measure α}   [inst_1 : Preorder ι] {φ : ι → Set α},   MeasureT
heory.AECover μ Filter.atTop φ → MeasureTheory.AECover μ Filter.atTop fun n => ⋃
 k ∈ Set.Iic n, φ k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.superset`：superset {φ ψ : ι -> Set α} (hφ : AECove
r μ l φ) (hsub : forall i, φ i subseteq ψ i) (hmeas : forall i, MeasurableSet (ψ
 i)) : AECover μ l ψ
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
-/
theorem AECover.biUnion_Iic_aecover [Preorder ι] {φ : ι → Set α} (hφ : AECover μ atTop φ) :
    AECover μ atTop fun n : ι => ⋃ (k) (_h : k ∈ Iic n), φ k :=
  hφ.superset (fun _ ↦ subset_biUnion_of_mem self_mem_Iic) fun _ ↦ .biUnion (to_countable _)
    fun _ _ ↦ (hφ.2 _)
/-
**MeasureTheory.AECover.biInter_Ici_aecover** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [Countable ι] [inst : MeasurableSpace α] {
μ : MeasureTheory.Measure α}   [inst_1 : Preorder ι] {φ : ι → Set α},   MeasureT
heory.AECover μ Filter.atTop φ → MeasureTheory.AECover μ Filter.atTop fun n => ⋂
 k ∈ Set.Ici n, φ k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.ae_eventually_mem`：∀ {α : Type u_1} {ι : Type u_2}
 [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι 
→ Set α},   MeasureTheory.AEC…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
-/
theorem AECover.biInter_Ici_aecover [Preorder ι] {φ : ι → Set α}
    (hφ : AECover μ atTop φ) : AECover μ atTop fun n : ι => ⋂ (k) (_h : k ∈ Ici n), φ k where
  ae_eventually_mem := hφ.ae_eventually_mem.mono fun x h ↦ by
    simpa only [mem_iInter, mem_Ici, eventually_forall_ge_atTop]
  measurableSet _ := .biInter (to_countable _) fun n _ => hφ.measurableSet n

end AECoverUnionInterCountable

section Lintegral

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}

/-
**MeasureTheory.lintegral_tendsto_of_monotone_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lintegral_tendsto_of_monotone_of_nat {φ : ℕ → Set α} (hφ : AECover μ atTop φ)
    (hmono : Monotone φ) {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) :=
  let F n := (φ n).indicator f
  have key₁ : ∀ n, AEMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurableSet n)
  have key₂ : ∀ᵐ x : α ∂μ, Monotone fun n => F n x := ae_of_all _ fun x _i _j hij => by
    dsimp [F]; grw [hmono hij]
  have key₃ : ∀ᵐ x : α ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := hφ.ae_tendsto_indicator f
  (lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr fun n =>
    lintegral_indicator (hφ.measurableSet n) _
/-
**MeasureTheory.AECover.lintegral_tendsto_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} 
{φ : ℕ → Set α},   MeasureTheory.AECover μ Filter.atTop φ →     ∀ {f : α → ENNRe
al},       AEMeasurable f μ → Filter.Tendsto (fun x => ∫⁻ (x : α) in φ x, f x ∂μ
) Filter.atTop (nhds (∫⁻ (x : α), f x ∂μ))
参数：fun x => ∫⁻ (x : α) in φ x, f x ∂μ；nhds (∫⁻ (x : α), f x ∂μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntegralEqImproper.0.MeasureTheo
ry.lintegral_tendsto_of_monotone_of_nat`：∀ {α : Type u_1} [inst : MeasurableSpac
e α] {μ : MeasureTheory.Measure α} {φ : ℕ → Set α},   MeasureTheory.AECover μ Fi
lter.atTop φ →     Mo…
· 使用定理 `MeasureTheory.AECover.biInter_Ici_aecover`：∀ {α : Type u_1} {ι : Type u_
2} [Countable ι] [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [ins
t_1 : Preorder ι] {φ : ι → Set …
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `MeasureTheory.AECover.biUnion_Iic_aecover`：∀ {α : Type u_1} {ι : Type u_
2} [Countable ι] [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}   [ins
t_1 : Preorder ι] {φ : ι → Set …
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.lintegral_mono_set`：lintegral_mono_set {_ : MeasurableSpac
e α} ⦃μ : Measure α⦄ {s t : Set α} {f : α -> Real>=0∞} (hst : s subseteq t) : ∫⁻
 x in s, f x ∂μ <= ∫⁻ …
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
-/
theorem AECover.lintegral_tendsto_of_nat {φ : ℕ → Set α} (hφ : AECover μ atTop φ) {f : α → ℝ≥0∞}
    (hfm : AEMeasurable f μ) : Tendsto (∫⁻ x in φ ·, f x ∂μ) atTop (𝓝 <| ∫⁻ x, f x ∂μ) := by
  have lim₁ := lintegral_tendsto_of_monotone_of_nat hφ.biInter_Ici_aecover
    (fun i j hij => biInter_subset_biInter_left (Ici_subset_Ici.mpr hij)) hfm
  have lim₂ := lintegral_tendsto_of_monotone_of_nat hφ.biUnion_Iic_aecover
    (fun i j hij => biUnion_subset_biUnion_left (Iic_subset_Iic.mpr hij)) hfm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ (fun n ↦ ?_) fun n ↦ ?_
  exacts [lintegral_mono_set (biInter_subset_of_mem self_mem_Ici),
    lintegral_mono_set (subset_biUnion_of_mem self_mem_Iic)]
/-
**MeasureTheory.AECover.lintegral_tendsto_of_countably_generated** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [l.IsCountablyGenerated] {φ : ι → Set α},   Meas
ureTheory.AECover μ l φ →     ∀ {f : α → ENNReal},       AEMeasurable f μ → Filt
er.Tendsto (fun i => ∫⁻ (x : α) in φ i, f x ∂μ) l (nhds (∫⁻ (x : α), f x ∂μ))
参数：fun i => ∫⁻ (x : α) in φ i, f x ∂μ；nhds (∫⁻ (x : α), f x ∂μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_seq_tendsto`：tendsto_of_seq_tendsto {f : α -> β} {k : 
Filter α} {l : Filter β} [k.IsCountablyGenerated] : (forall x : Nat -> α, Tendst
o x atTop k -> Tend…
· 使用定理 `MeasureTheory.AECover.lintegral_tendsto_of_nat`：∀ {α : Type u_1} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} {φ : ℕ → Set α},   MeasureTheo
ry.AECover μ Filter.atTop φ →     ∀ …
· 使用定理 `MeasureTheory.AECover.comp_tendsto`：∀ {α : Type u_1} {ι : Type u_2} {ι' 
: Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter
 ι}   {l' : Filter ι'} {…
-/
theorem AECover.lintegral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) :
    Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 <| ∫⁻ x, f x ∂μ) :=
  tendsto_of_seq_tendsto fun _u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm
/-
**MeasureTheory.AECover.lintegral_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated] {φ : ι → Set 
α},   MeasureTheory.AECover μ l φ →     ∀ {f : α → ENNReal} (I : ENNReal),      
 AEMeasurable f μ → Filter.Tendsto (fun i => ∫⁻ (x : α) in φ i, f x ∂μ) l (nhds 
I) → ∫⁻ (x : α), f x ∂μ = I
参数：I : ENNReal；fun i => ∫⁻ (x : α) in φ i, f x ∂μ；nhds I；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`：∀ {α : T
ype u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
 {l : Filter ι}   [l.IsCountablyGenerated] {φ : ι → …
-/
theorem AECover.lintegral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → ℝ≥0∞} (I : ℝ≥0∞) (hfm : AEMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) : ∫⁻ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto
/-
**MeasureTheory.AECover.iSup_lintegral_eq_of_countably_generated** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} [Nonempty ι]   [l.NeBot] [l.IsCountablyGenerated] 
{φ : ι → Set α},   MeasureTheory.AECover μ l φ →     ∀ {f : α → ENNReal}, AEMeas
urable f μ → ⨆ i, ∫⁻ (x : α) in φ i, f x ∂μ = ∫⁻ (x : α), f x ∂μ
参数：x : α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`：∀ {α : T
ype u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
 {l : Filter ι}   [l.IsCountablyGenerated] {φ : ι → …
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
-/
theorem AECover.iSup_lintegral_eq_of_countably_generated [Nonempty ι] [l.NeBot]
    [l.IsCountablyGenerated] {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ≥0∞}
    (hfm : AEMeasurable f μ) : ⨆ i : ι, ∫⁻ x in φ i, f x ∂μ = ∫⁻ x, f x ∂μ := by
  have := hφ.lintegral_tendsto_of_countably_generated hfm
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun i => lintegral_mono' Measure.restrict_le_self le_rfl) fun w hw => ?_
  exact (this.eventually_const_lt hw).exists

end Lintegral

section Integrable

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]

/-
**MeasureTheory.AECover.integrable_of_lintegral_enorm_bounded** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : ℝ),       MeasureTheory.AEStronglyMeasurable f μ →    
     (∀ᶠ (i : ι) in l, ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal I) → Measur
eTheory.Integrable f μ
参数：I : ℝ；∀ᶠ (i : ι) in l, ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.AECover.lintegral_tendsto_of_countably_generated`：∀ {α : T
ype u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α}
 {l : Filter ι}   [l.IsCountablyGenerated] {φ : ι → …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem AECover.integrable_of_lintegral_enorm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfm : AEStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal I) : Integrable f μ := by
  refine ⟨hfm, (le_of_tendsto ?_ hbounded).trans_lt ENNReal.ofReal_lt_top⟩
  exact hφ.lintegral_tendsto_of_countably_generated hfm.enorm
/-
**MeasureTheory.AECover.integrable_of_lintegral_enorm_tendsto** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : ℝ),       MeasureTheory.AEStronglyMeasurable f μ →    
     Filter.Tendsto (fun i => ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ) l (nhds (ENNReal.ofR
eal I)) →           MeasureTheory.Integrable f μ
参数：I : ℝ；fun i => ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ；nhds (ENNReal.ofReal I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.integrable_of_lintegral_enorm_bounded`：∀ {α : Type
 u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheor
y.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ge_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x ≤ a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem AECover.integrable_of_lintegral_enorm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 <| .ofReal I)) :
    Integrable f μ := by
  refine hφ.integrable_of_lintegral_enorm_bounded (max 1 (I + 1)) hfm ?_
  refine htendsto.eventually (ge_mem_nhds ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff (lt_max_of_lt_left zero_lt_one)).2 ?_
  exact lt_max_of_lt_right (lt_add_one I)
/-
**MeasureTheory.AECover.integrable_of_lintegral_enorm_bounded'** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : NNReal),       MeasureTheory.AEStronglyMeasurable f μ 
→         (∀ᶠ (i : ι) in l, ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ ≤ ↑I) → MeasureTheory.I
ntegrable f μ
参数：I : NNReal；∀ᶠ (i : ι) in l, ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ ≤ ↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.integrable_of_lintegral_enorm_bounded`：∀ {α : Type
 u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheor
y.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem AECover.integrable_of_lintegral_enorm_bounded' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ≥0) (hfm : AEStronglyMeasurable f μ)
    (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖ₑ ∂μ ≤ I) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_bounded I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hbounded)
/-
**MeasureTheory.AECover.integrable_of_lintegral_enorm_tendsto'** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : NNReal),       MeasureTheory.AEStronglyMeasurable f μ 
→         Filter.Tendsto (fun i => ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ) l (nhds ↑I) → M
easureTheory.Integrable f μ
参数：I : NNReal；fun i => ∫⁻ (x : α) in φ i, ‖f x‖ₑ ∂μ；nhds ↑I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.integrable_of_lintegral_enorm_tendsto`：∀ {α : Type
 u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheor
y.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem AECover.integrable_of_lintegral_enorm_tendsto' [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ≥0) (hfm : AEStronglyMeasurable f μ)
    (htendsto : Tendsto (fun i => ∫⁻ x in φ i, ‖f x‖ₑ ∂μ) l (𝓝 I)) : Integrable f μ :=
  hφ.integrable_of_lintegral_enorm_tendsto I hfm
    (by simpa only [ENNReal.ofReal_coe_nnreal] using htendsto)
/-
**MeasureTheory.AECover.integrable_of_integral_norm_bounded** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : ℝ),       (∀ (i : ι), MeasureTheory.IntegrableOn f (φ 
i) μ) →         (∀ᶠ (i : ι) in l, ∫ (x : α) in φ i, ‖f x‖ ∂μ ≤ I) → MeasureTheor
y.Integrable f μ
参数：I : ℝ；∀ (i : ι), MeasureTheory.IntegrableOn f (φ i) μ；∀ᶠ (i : ι) in l, ∫ (x :
 α) in φ i, ‖f x‖ ∂μ ≤ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.aestronglyMeasurable`：∀ {α : Type u_1} {ι : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {β :
 Type u_3}   [inst_1 : Topologic…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.AECover.integrable_of_lintegral_enorm_bounded`：∀ {α : Type
 u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheor
y.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hasFiniteIntegral_iff_enorm`：hasFiniteIntegral_iff_enorm {
f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
theorem AECover.integrable_of_integral_norm_bounded [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hbounded : ∀ᶠ i in l, (∫ x in φ i, ‖f x‖ ∂μ) ≤ I) : Integrable f μ := by
  have hfm : AEStronglyMeasurable f μ :=
    hφ.aestronglyMeasurable fun i => (hfi i).aestronglyMeasurable
  refine hφ.integrable_of_lintegral_enorm_bounded I hfm ?_
  conv at hbounded in integral _ _ =>
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x))
        hfm.norm.restrict]
  conv at hbounded in ENNReal.ofReal _ =>
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  refine hbounded.mono fun i hi => ?_
  rw [← ENNReal.ofReal_toReal <| ne_top_of_lt <| hasFiniteIntegral_iff_enorm.mp (hfi i).2]
  apply ENNReal.ofReal_le_ofReal hi
/-
**MeasureTheory.AECover.integrable_of_integral_norm_tendsto** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureTheory.AECover μ l φ
 →     ∀ {f : α → E} (I : ℝ),       (∀ (i : ι), MeasureTheory.IntegrableOn f (φ 
i) μ) →         Filter.Tendsto (fun i => ∫ (x : α) in φ i, ‖f x‖ ∂μ) l (nhds I) 
→ MeasureTheory.Integrable f μ
参数：I : ℝ；∀ (i : ι), MeasureTheory.IntegrableOn f (φ i) μ；fun i => ∫ (x : α) in φ
 i, ‖f x‖ ∂μ；nhds I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
-/
theorem AECover.integrable_of_integral_norm_tendsto [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → E} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (htendsto : Tendsto (fun i => ∫ x in φ i, ‖f x‖ ∂μ) l (𝓝 I)) : Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_norm_bounded I' hfi hI'
/-
**MeasureTheory.AECover.integrable_of_integral_bounded_of_nonneg_ae** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated] {φ : ι → Set 
α},   MeasureTheory.AECover μ l φ →     ∀ {f : α → ℝ} (I : ℝ),       (∀ (i : ι),
 MeasureTheory.IntegrableOn f (φ i) μ) →         (∀ᵐ (x : α) ∂μ, 0 ≤ f x) → (∀ᶠ 
(i : ι) in l, ∫ (x : α) in φ i, f x ∂μ ≤ I) → MeasureTheory.Integrable f μ
参数：I : ℝ；∀ (i : ι), MeasureTheory.IntegrableOn f (φ i) μ；∀ᵐ (x : α) ∂μ, 0 ≤ f x；
∀ᶠ (i : ι) in l, ∫ (x : α) in φ i, f x ∂μ ≤ I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
-/
theorem AECover.integrable_of_integral_bounded_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hnng : ∀ᵐ x ∂μ, 0 ≤ f x) (hbounded : ∀ᶠ i in l, (∫ x in φ i, f x ∂μ) ≤ I) : Integrable f μ :=
  hφ.integrable_of_integral_norm_bounded I hfi <| hbounded.mono fun _i hi =>
    (integral_congr_ae <| ae_restrict_of_ae <| hnng.mono fun _ => Real.norm_of_nonneg).le.trans hi
/-
**MeasureTheory.AECover.integrable_of_integral_tendsto_of_nonneg_ae** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated] {φ : ι → Set 
α},   MeasureTheory.AECover μ l φ →     ∀ {f : α → ℝ} (I : ℝ),       (∀ (i : ι),
 MeasureTheory.IntegrableOn f (φ i) μ) →         (∀ᵐ (x : α) ∂μ, 0 ≤ f x) →     
      Filter.Tendsto (fun i => ∫ (x : α) in φ i, f x ∂μ) l (nhds I) → MeasureThe
ory.Integrable f μ
参数：I : ℝ；∀ (i : ι), MeasureTheory.IntegrableOn f (φ i) μ；∀ᵐ (x : α) ∂μ, 0 ≤ f x；
fun i => ∫ (x : α) in φ i, f x ∂μ；nhds I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_bounded_of_nonneg_ae`：∀ {α 
: Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure
 α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated]…
-/
theorem AECover.integrable_of_integral_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hfi : ∀ i, IntegrableOn f (φ i) μ)
    (hnng : ∀ᵐ x ∂μ, 0 ≤ f x) (htendsto : Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := htendsto.isBoundedUnder_le
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

end Integrable

section Integral

variable {α ι E : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-
**MeasureTheory.AECover.integral_tendsto_of_countably_generated** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
inst_2 : NormedSpace ℝ E] [l.IsCountablyGenerated] {φ : ι → Set α},   MeasureThe
ory.AECover μ l φ →     ∀ {f : α → E},       MeasureTheory.Integrable f μ → Filt
er.Tendsto (fun i => ∫ (x : α) in φ i, f x ∂μ) l (nhds (∫ (x : α), f x ∂μ))
参数：fun i => ∫ (x : α) in φ i, f x ∂μ；nhds (∫ (x : α), f x ∂μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`：tendsto_
integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsCountablyGenera
ted] {F : ι -> α -> G} {f : α -> G} (bound : α -> Re…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `norm_indicator_le_norm_self`：norm_indicator_le_norm_self : ‖indicator s 
f a‖ <= ‖f a‖
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.AECover.ae_tendsto_indicator`：∀ {α : Type u_1} {ι : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {β :
 Type u_3}   [inst_1 : Zero β] […
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
-/
theorem AECover.integral_tendsto_of_countably_generated [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → E} (hfi : Integrable f μ) :
    Tendsto (fun i => ∫ x in φ i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) :=
  suffices h : Tendsto (fun i => ∫ x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫ x : α, f x ∂μ)) from by
    convert! h using 2; rw [integral_indicator (hφ.measurableSet _)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
    (Eventually.of_forall fun i => hfi.aestronglyMeasurable.indicator <| hφ.measurableSet i)
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => norm_indicator_le_norm_self _ _) hfi.norm
    (hφ.ae_tendsto_indicator f)

/-- Slight reformulation of `MeasureTheory.AECover.integral_tendsto_of_countably_generated`. -/
/-
**MeasureTheory.AECover.integral_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} {l : Filter ι}   [inst_1 : NormedAddCommGroup E] [
inst_2 : NormedSpace ℝ E] [l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α},   
MeasureTheory.AECover μ l φ →     ∀ {f : α → E} (I : E),       MeasureTheory.Int
egrable f μ →         Filter.Tendsto (fun n => ∫ (x : α) in φ n, f x ∂μ) l (nhds
 I) → ∫ (x : α), f x ∂μ = I
参数：I : E；fun n => ∫ (x : α) in φ n, f x ∂μ；nhds I；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…

--- 原说明 ---
Slight reformulation of `MeasureTheory.AECover.integral_tendsto_of_countably_gen
erated`.
-/
theorem AECover.integral_eq_of_tendsto [l.NeBot] [l.IsCountablyGenerated] {φ : ι → Set α}
    (hφ : AECover μ l φ) {f : α → E} (I : E) (hfi : Integrable f μ)
    (h : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) : ∫ x, f x ∂μ = I :=
  tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h
/-
**MeasureTheory.AECover.integral_eq_of_tendsto_of_nonneg_ae** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.AECover`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated] {φ : ι → Set 
α},   MeasureTheory.AECover μ l φ →     ∀ {f : α → ℝ} (I : ℝ),       0 ≤ᵐ[μ] f →
         (∀ (n : ι), MeasureTheory.IntegrableOn f (φ n) μ) →           Filter.Te
ndsto (fun n => ∫ (x : α) in φ n, f x ∂μ) l (nhds I) → ∫ (x : α), f x ∂μ = I
参数：I : ℝ；∀ (n : ι), MeasureTheory.IntegrableOn f (φ n) μ；fun n => ∫ (x : α) in φ
 n, f x ∂μ；nhds I；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_tendsto_of_nonneg_ae`：∀ {α 
: Type u_1} {ι : Type u_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure
 α} {l : Filter ι} [l.NeBot]   [l.IsCountablyGenerated]…
· 使用定理 `MeasureTheory.AECover.integral_eq_of_tendsto`：∀ {α : Type u_1} {ι : Type
 u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l
 : Filter ι}   [inst_1 : NormedAdd…
-/
theorem AECover.integral_eq_of_tendsto_of_nonneg_ae [l.NeBot] [l.IsCountablyGenerated]
    {φ : ι → Set α} (hφ : AECover μ l φ) {f : α → ℝ} (I : ℝ) (hnng : 0 ≤ᵐ[μ] f)
    (hfi : ∀ n, IntegrableOn f (φ n) μ) (htendsto : Tendsto (fun n => ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
    ∫ x, f x ∂μ = I :=
  have hfi' : Integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto
  hφ.integral_eq_of_tendsto I hfi' htendsto

end Integral

section IntegrableOfIntervalIntegral

variable {ι E : Type*} {μ : Measure ℝ} {l : Filter ι} [Filter.NeBot l] [IsCountablyGenerated l]
  [NormedAddCommGroup E] {a b : ι → ℝ} {f : ℝ → E}

/-
**MeasureTheory.integrable_of_intervalIntegral_norm_bounded** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：integrable_of_intervalIntegral_norm_bounded (I : Real) (hfi : forall i, In
tegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot) (hb : Tendsto b l atT
op) (h : forallᶠ i in l, (∫ x in a i..b i, ‖f x‖ ∂μ) <= I) : Integrable f μ
参数：I : Real；hfi : forall i, IntegrableOn f (Ioc (a i) (b i)) μ；ha : Tendsto a l 
atBot；hb : Tendsto b l atTop；h : forallᶠ i in l, (∫ x in a i..b i, ‖f x‖ ∂μ) <= 
I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioc`：aecover_Ioc [NoMinOrder α] : AECover μ l fun 
i => Ioc (a i) (b i)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem integrable_of_intervalIntegral_norm_bounded (I : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : ∀ᶠ i in l, (∫ x in a i..b i, ‖f x‖ ∂μ) ≤ I) : Integrable f μ := by
  have hφ : AECover μ l _ := aecover_Ioc ha hb
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi ht
  rwa [← intervalIntegral.integral_of_le (hai.trans hbi)]

/-- If `f` is integrable on intervals `Ioc (a i) (b i)`,
where `a i` tends to -∞ and `b i` tends to ∞, and
`∫ x in a i .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, ∞) -/
/-
**MeasureTheory.integrable_of_intervalIntegral_norm_tendsto** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：integrable_of_intervalIntegral_norm_tendsto (I : Real) (hfi : forall i, In
tegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot) (hb : Tendsto b l atT
op) (h : Tendsto (fun i => ∫ x in a i..b i, ‖f x‖ ∂μ) l (𝓝 I)) : Integrable f μ
参数：I : Real；hfi : forall i, IntegrableOn f (Ioc (a i) (b i)) μ；ha : Tendsto a l 
atBot；hb : Tendsto b l atTop；h : Tendsto (fun i => ∫ x in a i..b i, ‖f x‖ ∂μ) l 
(𝓝 I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrable_of_intervalIntegral_norm_bounded`：integrable_of
_intervalIntegral_norm_bounded (I : Real) (hfi : forall i, IntegrableOn f (Ioc (
a i) (b i)) μ) (ha : Tendsto a l atBot) (hb : T…

--- 原说明 ---
If `f` is integrable on intervals `Ioc (a i) (b i)`,
where `a i` tends to -∞ and `b i` tends to ∞, and
`∫ x in a i .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, ∞)
-/
theorem integrable_of_intervalIntegral_norm_tendsto (I : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) (b i)) μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) (h : Tendsto (fun i => ∫ x in a i..b i, ‖f x‖ ∂μ) l (𝓝 I)) :
    Integrable f μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrable_of_intervalIntegral_norm_bounded I' hfi ha hb hI'
/-
**MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_bounded** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Iic_of_intervalIntegral_norm_bounded (I b : Real) (hfi : fora
ll i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot) (h : forallᶠ i in
 l, (∫ x in a i..b, ‖f x‖ ∂μ) <= I) : IntegrableOn f (Iic b) μ
参数：I b : Real；hfi : forall i, IntegrableOn f (Ioc (a i) b) μ；ha : Tendsto a l at
Bot；h : forallᶠ i in l, (∫ x in a i..b, ‖f x‖ ∂μ) <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioi`：aecover_Ioi [NoMinOrder α] : AECover μ l fun 
i => Ioi (a i) where ae_eventually_mem
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
-/
theorem integrableOn_Iic_of_intervalIntegral_norm_bounded (I b : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : ∀ᶠ i in l, (∫ x in a i..b, ‖f x‖ ∂μ) ≤ I) : IntegrableOn f (Iic b) μ := by
  have hφ : AECover (μ.restrict <| Iic b) l _ := aecover_Ioi ha
  have hfi : ∀ i, IntegrableOn f (Ioi (a i)) (μ.restrict <| Iic b) := by
    intro i
    rw [IntegrableOn, Measure.restrict_restrict (hφ.measurableSet i)]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [ha.eventually (eventually_le_atBot b)] with i hai
  rw [intervalIntegral.integral_of_le hai, Measure.restrict_restrict (hφ.measurableSet i)]
  exact id

/-- If `f` is integrable on intervals `Ioc (a i) b`,
where `a i` tends to -∞, and
`∫ x in a i .. b, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, b) -/
/-
**MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_tendsto** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Iic_of_intervalIntegral_norm_tendsto (I b : Real) (hfi : fora
ll i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot) (h : Tendsto (fun
 i => ∫ x in a i..b, ‖f x‖ ∂μ) l (𝓝 I)) : IntegrableOn f (Iic b) μ
参数：I b : Real；hfi : forall i, IntegrableOn f (Ioc (a i) b) μ；ha : Tendsto a l at
Bot；h : Tendsto (fun i => ∫ x in a i..b, ‖f x‖ ∂μ) l (𝓝 I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrableOn_Iic_of_intervalIntegral_norm_bounded`：integra
bleOn_Iic_of_intervalIntegral_norm_bounded (I b : Real) (hfi : forall i, Integra
bleOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot) (h …

--- 原说明 ---
If `f` is integrable on intervals `Ioc (a i) b`,
where `a i` tends to -∞, and
`∫ x in a i .. b, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, b)
-/
theorem integrableOn_Iic_of_intervalIntegral_norm_tendsto (I b : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc (a i) b) μ) (ha : Tendsto a l atBot)
    (h : Tendsto (fun i => ∫ x in a i..b, ‖f x‖ ∂μ) l (𝓝 I)) : IntegrableOn f (Iic b) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Iic_of_intervalIntegral_norm_bounded I' b hfi ha hI'
/-
**MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioi_of_intervalIntegral_norm_bounded (I a : Real) (hfi : fora
ll i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop) (h : forallᶠ i in
 l, (∫ x in a..b i, ‖f x‖ ∂μ) <= I) : IntegrableOn f (Ioi a) μ
参数：I a : Real；hfi : forall i, IntegrableOn f (Ioc a (b i)) μ；hb : Tendsto b l at
Top；h : forallᶠ i in l, (∫ x in a..b i, ‖f x‖ ∂μ) <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Iic`：aecover_Iic (hb : Tendsto b l atTop) : AECove
r μ l fun i => Iic b i
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
-/
theorem integrableOn_Ioi_of_intervalIntegral_norm_bounded (I a : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : ∀ᶠ i in l, (∫ x in a..b i, ‖f x‖ ∂μ) ≤ I) : IntegrableOn f (Ioi a) μ := by
  have hφ : AECover (μ.restrict <| Ioi a) l _ := aecover_Iic hb
  have hfi : ∀ i, IntegrableOn f (Iic (b i)) (μ.restrict <| Ioi a) := by
    intro i
    rw [IntegrableOn, Measure.restrict_restrict (hφ.measurableSet i), inter_comm]
    exact hfi i
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp ?_)
  filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, Measure.restrict_restrict (hφ.measurableSet i),
    inter_comm]
  exact id

/-- If `f` is integrable on intervals `Ioc a (b i)`,
where `b i` tends to ∞, and
`∫ x in a .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (a, ∞) -/
/-
**MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioi_of_intervalIntegral_norm_tendsto (I a : Real) (hfi : fora
ll i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop) (h : Tendsto (fun
 i => ∫ x in a..b i, ‖f x‖ ∂μ) l (𝓝 <| I)) : IntegrableOn f (Ioi a) μ
参数：I a : Real；hfi : forall i, IntegrableOn f (Ioc a (b i)) μ；hb : Tendsto b l at
Top；h : Tendsto (fun i => ∫ x in a..b i, ‖f x‖ ∂μ) l (𝓝 <| I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded`：integra
bleOn_Ioi_of_intervalIntegral_norm_bounded (I a : Real) (hfi : forall i, Integra
bleOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop) (h …

--- 原说明 ---
If `f` is integrable on intervals `Ioc a (b i)`,
where `b i` tends to ∞, and
`∫ x in a .. b i, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (a, ∞)
-/
theorem integrableOn_Ioi_of_intervalIntegral_norm_tendsto (I a : ℝ)
    (hfi : ∀ i, IntegrableOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop)
    (h : Tendsto (fun i => ∫ x in a..b i, ‖f x‖ ∂μ) l (𝓝 <| I)) : IntegrableOn f (Ioi a) μ :=
  let ⟨I', hI'⟩ := h.isBoundedUnder_le
  integrableOn_Ioi_of_intervalIntegral_norm_bounded I' a hfi hb hI'
/-
**MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : Real} (hfi : 
forall i, IntegrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| 𝓝 a₀) (hb : Te
ndsto b l <| 𝓝 b₀) (h : forallᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) <= I) : 
IntegrableOn f (Ioc a₀ b₀)
参数：hfi : forall i, IntegrableOn f <| Ioc (a i) (b i)；ha : Tendsto a l <| 𝓝 a₀；hb
 : Tendsto b l <| 𝓝 b₀；h : forallᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AECover.integrable_of_integral_norm_bounded`：∀ {α : Type u
_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheory.
Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.aecover_Ioc_of_Ioc`：aecover_Ioc_of_Ioc (ha : Tendsto a l (
𝓝 A)) (hb : Tendsto b l (𝓝 B)) : AECover (μ.restrict <| Ioc A B) l fun i => Ioc 
(a i) (b i)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.restrict`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `MeasureTheory.integral_mono_measure`：integral_mono_measure [OrderClosedT
opology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν) (hf : 0 <=ᵐ[ν] f) (hfi : 
Integrable f ν) : ∫ (a : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| 𝓝 a₀)
    (hb : Tendsto b l <| 𝓝 b₀) (h : ∀ᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) ≤ I) :
    IntegrableOn f (Ioc a₀ b₀) := by
  refine (aecover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (fun i => (hfi i).restrict) (h.mono fun i hi ↦ ?_)
  rw [Measure.restrict_restrict measurableSet_Ioc]
  grw [← hi]
  gcongr
  · apply ae_of_all
    simp
  · exact (hfi i).norm
  · exact inter_subset_left
/-
**MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioc_of_intervalIntegral_norm_bounded_left {I a₀ b : Real} (hf
i : forall i, IntegrableOn f <| Ioc (a i) b) (ha : Tendsto a l <| 𝓝 a₀) (h : for
allᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) <= I) : IntegrableOn f (Ioc a₀ b)
参数：hfi : forall i, IntegrableOn f <| Ioc (a i) b；ha : Tendsto a l <| 𝓝 a₀；h : fo
rallᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded`：integra
bleOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : Real} (hfi : forall i, Int
egrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_left {I a₀ b : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc (a i) b) (ha : Tendsto a l <| 𝓝 a₀)
    (h : ∀ᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) ≤ I) : IntegrableOn f (Ioc a₀ b) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi ha tendsto_const_nhds h
/-
**MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_right** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_Ioc_of_intervalIntegral_norm_bounded_right {I a b₀ : Real} (h
fi : forall i, IntegrableOn f <| Ioc a (b i)) (hb : Tendsto b l <| 𝓝 b₀) (h : fo
rallᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖) <= I) : IntegrableOn f (Ioc a b₀)
参数：hfi : forall i, IntegrableOn f <| Ioc a (b i)；hb : Tendsto b l <| 𝓝 b₀；h : fo
rallᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖) <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded`：integra
bleOn_Ioc_of_intervalIntegral_norm_bounded {I a₀ b₀ : Real} (hfi : forall i, Int
egrableOn f <| Ioc (a i) (b i)) (ha : Tendsto a l <| …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem integrableOn_Ioc_of_intervalIntegral_norm_bounded_right {I a b₀ : ℝ}
    (hfi : ∀ i, IntegrableOn f <| Ioc a (b i)) (hb : Tendsto b l <| 𝓝 b₀)
    (h : ∀ᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖) ≤ I) : IntegrableOn f (Ioc a b₀) :=
  integrableOn_Ioc_of_intervalIntegral_norm_bounded hfi tendsto_const_nhds hb h

end IntegrableOfIntervalIntegral

section IntegralOfIntervalIntegral

variable {ι E : Type*} {μ : Measure ℝ} {l : Filter ι} [IsCountablyGenerated l]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ι → ℝ} {f : ℝ → E}

/-
**MeasureTheory.intervalIntegral_tendsto_integral** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：intervalIntegral_tendsto_integral (hfi : Integrable f μ) (ha : Tendsto a l
 atBot) (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x in a i..b i, f x ∂μ) l 
(𝓝 <| ∫ x, f x ∂μ)
参数：hfi : Integrable f μ；ha : Tendsto a l atBot；hb : Tendsto b l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioc`：aecover_Ioc [NoMinOrder α] : AECover μ l fun 
i => Ioc (a i) (b i)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
-/
theorem intervalIntegral_tendsto_integral (hfi : Integrable f μ) (ha : Tendsto a l atBot)
    (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x in a i..b i, f x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  let φ i := Ioc (a i) (b i)
  have hφ : AECover μ l φ := aecover_Ioc ha hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot 0),
    hb.eventually (eventually_ge_atTop 0)] with i hai hbi
  exact (intervalIntegral.integral_of_le (hai.trans hbi)).symm
/-
**MeasureTheory.intervalIntegral_tendsto_integral_Iic** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：intervalIntegral_tendsto_integral_Iic (b : Real) (hfi : IntegrableOn f (Ii
c b) μ) (ha : Tendsto a l atBot) : Tendsto (fun i => ∫ x in a i..b, f x ∂μ) l (𝓝
 <| ∫ x in Iic b, f x ∂μ)
参数：b : Real；hfi : IntegrableOn f (Iic b) μ；ha : Tendsto a l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Ioi`：aecover_Ioi [NoMinOrder α] : AECover μ l fun 
i => Ioi (a i) where ae_eventually_mem
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
-/
theorem intervalIntegral_tendsto_integral_Iic (b : ℝ) (hfi : IntegrableOn f (Iic b) μ)
    (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in a i..b, f x ∂μ) l (𝓝 <| ∫ x in Iic b, f x ∂μ) := by
  let φ i := Ioi (a i)
  have hφ : AECover (μ.restrict <| Iic b) l φ := aecover_Ioi ha
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [ha.eventually (eventually_le_atBot <| b)] with i hai
  rw [intervalIntegral.integral_of_le hai, Measure.restrict_restrict (hφ.measurableSet i)]
  rfl
/-
**MeasureTheory.tendsto_integral_Iic_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_integral_Iic_zero (ha : Tendsto a l atBot) : Tendsto (fun i => ∫ x
 in Iic (a i), f x ∂μ) l (𝓝 0)
参数：ha : Tendsto a l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_eq_iff_comm`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}, a
 - b = c ↔ a - c = b
· 使用定理 `intervalIntegral.integral_Iic_sub_Iic`：integral_Iic_sub_Iic (ha : Integr
ableOn f (Iic a) μ) (hb : IntegrableOn f (Iic b) μ) : ((∫ x in Iic b, f x ∂μ) - 
∫ x in Iic a, f x ∂μ) = ∫ x…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Iic`：intervalIntegral_te
ndsto_integral_Iic (b : Real) (hfi : IntegrableOn f (Iic b) μ) (ha : Tendsto a l
 atBot) : Tendsto (fun i => ∫ x in a i..b…
-/
theorem tendsto_integral_Iic_zero (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Iic (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : ∀ b, ¬ IntegrableOn f (Iic b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : ∀ᶠ i in l, ∫ x in Iic b, f x ∂μ - ∫ x in a i..b, f x ∂μ = ∫ x in Iic (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Iic_mem_atBot b)] with i hi
    rw [sub_eq_iff_comm,
      intervalIntegral.integral_Iic_sub_Iic (hb.mono_set (Iic_subset_Iic.2 hi)) hb]
  rw [← sub_self (∫ x in Iic b, f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| intervalIntegral_tendsto_integral_Iic b hb ha)
/-
**MeasureTheory.tendsto_integral_Ico_integral_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：tendsto_integral_Ico_integral_Iio (b : Real) (hfi : IntegrableOn f (Iio b)
 μ) (ha : Tendsto a l atBot) : Tendsto (fun i => ∫ x in Ico (a i) b, f x ∂μ) l (
𝓝 <| ∫ x in Iio b, f x ∂μ)
参数：b : Real；hfi : IntegrableOn f (Iio b) μ；ha : Tendsto a l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ico_inter_Iio`：Ico_inter_Iio : Ico a b inter Iio c = Ico a (min b c)
· 使用定理 `min_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), min a a = a
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.aecover_Iio_of_Ico`：aecover_Iio_of_Ico : AECover (μ.restri
ct (Iio B)) l fun i => Ico (c i) (b i) where ae_eventually_mem
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem tendsto_integral_Ico_integral_Iio (b : ℝ) (hfi : IntegrableOn f (Iio b) μ)
    (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Ico (a i) b, f x ∂μ) l (𝓝 <| ∫ x in Iio b, f x ∂μ) :=
  ((aecover_Iio_of_Ico tendsto_const_nhds ha).integral_tendsto_of_countably_generated hfi).congr'
    (by simp)
/-
**MeasureTheory.tendsto_integral_Iio_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_integral_Iio_zero (ha : Tendsto a l atBot) : Tendsto (fun i => ∫ x
 in Iio (a i), f x ∂μ) l (𝓝 0)
参数：ha : Tendsto a l atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_eq_iff_comm`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}, a
 - b = c ↔ a - c = b
· 使用定理 `intervalIntegral.integral_Iio_sub_Iio`：integral_Iio_sub_Iio (hf : Integr
ableOn f (Iio b) μ) (hab : a <= b) : ∫ x in Iio b, f x ∂μ - ∫ x in Iio a, f x ∂μ
 = ∫ x in Ico a b, f x ∂μ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.tendsto_integral_Ico_integral_Iio`：tendsto_integral_Ico_in
tegral_Iio (b : Real) (hfi : IntegrableOn f (Iio b) μ) (ha : Tendsto a l atBot) 
: Tendsto (fun i => ∫ x in Ico (a i) …
-/
theorem tendsto_integral_Iio_zero (ha : Tendsto a l atBot) :
    Tendsto (fun i => ∫ x in Iio (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : ∀ b, ¬ IntegrableOn f (Iio b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : ∀ᶠ i in l, ∫ x in Iio b, f x ∂μ - ∫ x in Ico (a i) b, f x ∂μ =
      ∫ x in Iio (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Iic_mem_atBot b)] with i hi
    rw [sub_eq_iff_comm, intervalIntegral.integral_Iio_sub_Iio hb hi]
  rw [← sub_self (∫ x in Iio b, f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| tendsto_integral_Ico_integral_Iio b hb ha)
/-
**MeasureTheory.intervalIntegral_tendsto_integral_Ioi** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：intervalIntegral_tendsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Io
i a) μ) (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x in a..b i, f x ∂μ) l (𝓝
 <| ∫ x in Ioi a, f x ∂μ)
参数：a : Real；hfi : IntegrableOn f (Ioi a) μ；hb : Tendsto b l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aecover_Iic`：aecover_Iic (hb : Tendsto b l atTop) : AECove
r μ l fun i => Iic b i
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.AECover.measurableSet`：∀ {α : Type u_1} {ι : Type u_2} [in
st : MeasurableSpace α] {μ : MeasureTheory.Measure α} {l : Filter ι} {φ : ι → Se
t α},   MeasureTheory.AEC…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
-/
theorem intervalIntegral_tendsto_integral_Ioi (a : ℝ) (hfi : IntegrableOn f (Ioi a) μ)
    (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in a..b i, f x ∂μ) l (𝓝 <| ∫ x in Ioi a, f x ∂μ) := by
  let φ i := Iic (b i)
  have hφ : AECover (μ.restrict <| Ioi a) l φ := aecover_Iic hb
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' ?_
  filter_upwards [hb.eventually (eventually_ge_atTop <| a)] with i hbi
  rw [intervalIntegral.integral_of_le hbi, Measure.restrict_restrict (hφ.measurableSet i),
    inter_comm]
  rfl
/-
**MeasureTheory.tendsto_integral_Ioi_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_integral_Ioi_zero (hb : Tendsto b l atTop) : Tendsto (fun i => ∫ x
 in Ioi (b i), f x ∂μ) l (𝓝 0)
参数：hb : Tendsto b l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `intervalIntegral.integral_interval_add_Ioi`：integral_interval_add_Ioi (h
a : IntegrableOn f (Ioi a) μ) (hb : IntegrableOn f (Ioi b) μ) : ∫ (x : Real) in 
a..b, f x ∂μ + ∫ (x : Real) in I…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
-/
theorem tendsto_integral_Ioi_zero (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in Ioi (b i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : ∀ a, ¬ IntegrableOn f (Ioi a) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (b i))).symm)
  obtain ⟨a, ha⟩ := h
  have : ∀ᶠ i in l, ∫ x in Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ = ∫ x in Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ici_mem_atTop a)] with i hi
    rw [sub_eq_iff_eq_add',
      intervalIntegral.integral_interval_add_Ioi ha (ha.mono_set (Ioi_subset_Ioi hi))]
  rw [← sub_self (∫ x in Ioi a, f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| intervalIntegral_tendsto_integral_Ioi a ha hb)
/-
**MeasureTheory.tendsto_integral_Ico_integral_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：tendsto_integral_Ico_integral_Ici (b : Real) (hfi : IntegrableOn f (Ici b)
 μ) (ha : Tendsto a l atTop) : Tendsto (fun i => ∫ x in Ico b (a i), f x ∂μ) l (
𝓝 <| ∫ x in Ici b, f x ∂μ)
参数：b : Real；hfi : IntegrableOn f (Ici b) μ；ha : Tendsto a l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ico_inter_Ici`：∀ {α : Type u_1} [inst : SemilatticeSup α] (b a c : α
), Set.Ico b a ∩ Set.Ici c = Set.Ico (b ⊔ c) a
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `MeasureTheory.AECover.integral_tendsto_of_countably_generated`：∀ {α : Ty
pe u_1} {ι : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} {l : Filter ι}   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.aecover_Ici_of_Ico`：aecover_Ici_of_Ico [NoMaxOrder α] : AE
Cover (μ.restrict (Ici B)) l fun i => Ico B (d i) where ae_eventually_mem
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem tendsto_integral_Ico_integral_Ici (b : ℝ) (hfi : IntegrableOn f (Ici b) μ)
    (ha : Tendsto a l atTop) :
    Tendsto (fun i => ∫ x in Ico b (a i), f x ∂μ) l (𝓝 <| ∫ x in Ici b, f x ∂μ) :=
  ((aecover_Ici_of_Ico ha).integral_tendsto_of_countably_generated hfi).congr' (by simp)
/-
**MeasureTheory.tendsto_integral_Ici_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_integral_Ici_zero (ha : Tendsto a l atTop) : Tendsto (fun i => ∫ x
 in Ici (a i), f x ∂μ) l (𝓝 0)
参数：ha : Tendsto a l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sub_eq_iff_comm`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}, a
 - b = c ↔ a - c = b
· 使用定理 `intervalIntegral.integral_Ici_sub_Ici`：integral_Ici_sub_Ici (hf : Integr
ableOn f (Ici a) μ) (hab : a <= b) : ∫ x in Ici a, f x ∂μ - ∫ x in Ici b, f x ∂μ
 = ∫ x in Ico a b, f x ∂μ
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.tendsto_integral_Ico_integral_Ici`：tendsto_integral_Ico_in
tegral_Ici (b : Real) (hfi : IntegrableOn f (Ici b) μ) (ha : Tendsto a l atTop) 
: Tendsto (fun i => ∫ x in Ico b (a i…
-/
theorem tendsto_integral_Ici_zero (ha : Tendsto a l atTop) :
    Tendsto (fun i => ∫ x in Ici (a i), f x ∂μ) l (𝓝 0) := by
  by_cases! h : ∀ b, ¬ IntegrableOn f (Ici b) μ
  · exact tendsto_const_nhds.congr (fun i => (integral_undef (h (a i))).symm)
  obtain ⟨b, hb⟩ := h
  have : ∀ᶠ i in l, ∫ x in Ici b, f x ∂μ - ∫ x in Ico b (a i), f x ∂μ =
      ∫ x in Ici (a i), f x ∂μ := by
    filter_upwards [ha.eventually_mem (Ici_mem_atTop b)] with i hi
    rw [sub_eq_iff_comm, intervalIntegral.integral_Ici_sub_Ici hb hi]
  rw [← sub_self (∫ x in Ici b, f x ∂μ)]
  exact Tendsto.congr' this (Tendsto.const_sub _ <| tendsto_integral_Ico_integral_Ici b hb ha)

end IntegralOfIntervalIntegral

open Real

open scoped Interval

section IoiFTC

variable {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a l : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If the derivative of a function defined on the real line is integrable close to `+∞`, then
the function has a limit at `+∞`. -/
/-
**MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E] (hder
iv : forall x in Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a))
 : Tendsto f atTop (𝓝 (limUnder atTop f))
参数：hderiv : forall x in Ioi a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Io
i a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_antitone`：tendsto_setIntegral_of_an
titone {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι
 -> Set X} (hsm : forall i, Measura…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
If the derivative of a function defined on the real line is integrable close to 
`+∞`, then
the function has a limit at `+∞`.
-/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E]
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) := by
  suffices ∃ a, Tendsto f atTop (𝓝 a) from tendsto_nhds_limUnder this
  suffices CauchySeq f from cauchySeq_tendsto_of_complete this
  apply Metric.cauchySeq_iff'.2 (fun ε εpos ↦ ?_)
  have A : ∀ᶠ (n : ℕ) in atTop, ∫ (x : ℝ) in Ici ↑n, ‖f' x‖ < ε := by
    have L : Tendsto (fun (n : ℕ) ↦ ∫ x in Ici (n : ℝ), ‖f' x‖) atTop
        (𝓝 (∫ x in ⋂ (n : ℕ), Ici (n : ℝ), ‖f' x‖)) := by
      apply tendsto_setIntegral_of_antitone (fun n ↦ measurableSet_Ici)
      · intro m n hmn
        exact Ici_subset_Ici.2 (Nat.cast_le.mpr hmn)
      · rcases exists_nat_gt a with ⟨n, hn⟩
        exact ⟨n, IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 hn)⟩
    have B : ⋂ (n : ℕ), Ici (n : ℝ) = ∅ := by
      apply eq_empty_of_forall_notMem (fun x ↦ ?_)
      simpa only [mem_iInter, mem_Ici, not_forall, not_le] using exists_nat_gt x
    simp only [B, Measure.restrict_empty, integral_zero_measure] at L
    exact (tendsto_order.1 L).2 _ εpos
  have B : ∀ᶠ (n : ℕ) in atTop, a < n := by
    rcases exists_nat_gt a with ⟨n, hn⟩
    filter_upwards [Ioi_mem_atTop n] with m (hm : n < m) using hn.trans (Nat.cast_lt.mpr hm)
  rcases (A.and B).exists with ⟨N, hN, h'N⟩
  refine ⟨N, fun x hx ↦ ?_⟩
  calc
  dist (f x) (f ↑N)
    = ‖f x - f N‖ := dist_eq_norm _ _
  _ = ‖∫ t in Ioc ↑N x, f' t‖ := by
      rw [← intervalIntegral.integral_of_le hx, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · intro y hy
        simp only [hx, uIcc_of_le, mem_Icc] at hy
        exact hderiv _ (h'N.trans_le hy.1)
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
        exact f'int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h'N.le))
  _ ≤ ∫ t in Ioc ↑N x, ‖f' t‖ := norm_integral_le_integral_norm fun a ↦ f' a
  _ ≤ ∫ t in Ici ↑N, ‖f' t‖ := by
      apply setIntegral_mono_set
      · apply IntegrableOn.mono_set f'int.norm (Ici_subset_Ioi.2 h'N)
      · filter_upwards with x using norm_nonneg _
      · have : Ioc (↑N) x ⊆ Ici ↑N := Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self
        exact this.eventuallyLE
  _ < ε := hN

open UniformSpace in
/-- If a function and its derivative are integrable on `(a, +∞)`, then the function tends to zero
at `+∞`. -/
/-
**MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (hderiv : forall x in Ioi a
, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) (fint : IntegrableOn 
f (Ioi a)) : Tendsto f atTop (𝓝 0)
参数：hderiv : forall x in Ioi a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Io
i a)；fint : IntegrableOn f (Ioi a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `UniformSpace.Completion.instIsBoundedSMul`：∀ {α : Type u} [inst : Pseudo
MetricSpace α] {M : Type u_1} [inst_1 : Zero M] [inst_2 : Zero α] [inst_3 : SMul
 M α]   [inst_4 : PseudoMetricS…
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`：tendst
o_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E] (hderiv : forall 
x in Ioi a, HasDerivAt f (f' x) x) (f'int : Integrable…
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `MeasureTheory.IntegrableAtFilter.eq_zero_of_tendsto`：∀ {α : Type u_1} {E
 : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : Measure
Theory.Measure α}   {l : Filter α} {f : α…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Real.volume_Ici`：volume_Ici {a : Real} : volume (Ici a) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `UniformSpace.Completion.isUniformEmbedding_coe`：isUniformEmbedding_coe [
T0Space α] : IsUniformEmbedding ((↑) : α -> Completion α)
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
If a function and its derivative are integrable on `(a, +∞)`, then the function 
tends to zero
at `+∞`.
-/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (fint : IntegrableOn f (Ioi a)) :
    Tendsto f atTop (𝓝 0) := by
  let F : E →L[ℝ] Completion E := Completion.toComplL
  have Fderiv : ∀ x ∈ Ioi a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx ↦ F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Ioi a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Ioi a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atTop (𝓝 (limUnder atTop (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi Fderiv F'int
  have B : limUnder atTop (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atTop := by exact ⟨Ioi a, Ioi_mem_atTop _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← volume_Ici (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a
) a) (hderiv : forall x in Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f
' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a
参数：hcont : ContinuousWithinAt f (Ici a) a；hderiv : forall x in Ioi a, HasDerivAt
 f (f' x) x；f'int : IntegrableOn f' (Ioi a)；hf : Tendsto f atTop (𝓝 m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：integral_eq_sub_of
_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hderiv : fo
rall x in Ioo a b, HasDerivAt f (f' x) x) …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
**Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, t
hen the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming different
iability
on `(a, +∞)` and continuity at `a⁺`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`.
-/
theorem integral_Ioi_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a))
    (hf : Tendsto f atTop (𝓝 m)) : ∫ x in Ioi a, f' x = m - f a := by
  have hcont : ContinuousOn f (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a ≤ id x := le_of_lt hx
  symm
  apply
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x (hcont.mono Icc_subset_Ici_self)
      fun y hy => hderiv y hy.1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
  exact f'int.mono (fun y hy => hy.1) le_rfl

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `[a, +∞)`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_tendsto' (hderiv : forall x in Ici a, HasDer
ivAt f (f' x) x) (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) 
: ∫ x in Ioi a, f' x = m - f a
参数：hderiv : forall x in Ici a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Io
i a)；hf : Tendsto f atTop (𝓝 m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`：integral_Ioi_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a) (hderiv : forall x i
n Ioi a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
**Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, t
hen the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming different
iability
on `[a, +∞)`.

Note that such a function always has a limit at infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`.
-/
theorem integral_Ioi_of_hasDerivAt_of_tendsto' (hderiv : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Ioi a)) (hf : Tendsto f atTop (𝓝 m)) :
    ∫ x in Ioi a, f' x = m - f a := by
  refine integral_Ioi_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/-- A special case of `integral_Ioi_of_hasDerivAt_of_tendsto` where we assume that `f` is C^1 with
compact support. -/
/-
**MeasureTheory._root_.HasCompactSupport.integral_Ioi_deriv_eq** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `integral_Ioi_of_hasDerivAt_of_tendsto` where we assume that `
f` is C^1 with
compact support.
-/
theorem _root_.HasCompactSupport.integral_Ioi_deriv_eq (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Ioi b, deriv f x = - f b := by
  have := fun x (_ : x ∈ Ioi b) ↦ hf.differentiable one_ne_zero x |>.hasDerivAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this, zero_sub]
  · refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono _root_.atTop_le_cocompact |>.tendsto

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`. -/
/-
**MeasureTheory.integrableOn_Ioi_deriv_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integrableOn_Ioi_deriv_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a) 
(hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'pos : forall x in Ioi a, 
0 <= g' x) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a)
参数：hcont : ContinuousWithinAt g (Ici a) a；hderiv : forall x in Ioi a, HasDerivAt
 g (g' x) x；g'pos : forall x in Ioi a, 0 <= g' x；hg : Tendsto g atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_tendsto`：integra
bleOn_Ioi_of_intervalIntegral_norm_tendsto (I a : Real) (hfi : forall i, Integra
bleOn f (Ioc a (b i)) μ) (hb : Tendsto b l atTop) (h …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `intervalIntegral.integrableOn_deriv_of_nonneg`：integrableOn_deriv_of_non
neg (hcont : ContinuousOn g (Icc a b)) (hderiv : forall x in Ioo a b, HasDerivAt
 g (g' x) x) (g'pos : forall x in I…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：integral_eq_sub_of
_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hderiv : fo
rall x in Ioo a b, HasDerivAt f (f' x) x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
When a function has a limit at infinity, and its derivative is nonnegative, then
 the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`.
-/
theorem integrableOn_Ioi_deriv_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  have hcont : ContinuousOn g (Ici a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a (fun x => ?_) tendsto_id ?_
  · exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
      (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
  apply Tendsto.congr' _ (hg.sub_const _)
  filter_upwards [Ioi_mem_atTop a] with x hx
  have h'x : a ≤ id x := le_of_lt hx
  calc
    g x - g a = ∫ y in a..id x, g' y := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x
        (hcont.mono Icc_subset_Ici_self) fun y hy => hderiv y hy.1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
      exact intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
        (fun y hy => hderiv y hy.1) fun y hy => g'pos y hy.1
    _ = ∫ y in a..id x, ‖g' y‖ := by
      simp_rw [intervalIntegral.integral_of_le h'x]
      refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
      dsimp
      rw [abs_of_nonneg]
      exact g'pos _ hy.1

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
/-
**MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrableOn_Ioi_deriv_of_nonneg' (hderiv : forall x in Ici a, HasDerivAt 
g (g' x) x) (g'pos : forall x in Ioi a, 0 <= g' x) (hg : Tendsto g atTop (𝓝 l)) 
: IntegrableOn g' (Ioi a)
参数：hderiv : forall x in Ici a, HasDerivAt g (g' x) x；g'pos : forall x in Ioi a, 
0 <= g' x；hg : Tendsto g atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`：integrableOn_Ioi_deriv_o
f_nonneg (hcont : ContinuousWithinAt g (Ici a) a) (hderiv : forall x in Ioi a, H
asDerivAt g (g' x) x) (g'pos : foral…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
When a function has a limit at infinity, and its derivative is nonnegative, then
 the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`.
-/
theorem integrableOn_Ioi_deriv_of_nonneg' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity at `a⁺`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_nonneg (hcont : ContinuousWithinAt g (Ici a)
 a) (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'pos : forall x in Ioi
 a, 0 <= g' x) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a
参数：hcont : ContinuousWithinAt g (Ici a) a；hderiv : forall x in Ioi a, HasDerivAt
 g (g' x) x；g'pos : forall x in Ioi a, 0 <= g' x；hg : Tendsto g atTop (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`：integral_Ioi_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a) (hderiv : forall x i
n Ioi a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`：integrableOn_Ioi_deriv_o
f_nonneg (hcont : ContinuousWithinAt g (Ici a) a) (hderiv : forall x in Ioi a, H
asDerivAt g (g' x) x) (g'pos : foral…

--- 原说明 ---
When a function has a limit at infinity `l`, and its derivative is nonnegative, 
then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is inte
grable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a,
 +∞)` and
continuity at `a⁺`.
-/
theorem integral_Ioi_of_hasDerivAt_of_nonneg (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_nonneg' (hderiv : forall x in Ici a, HasDeri
vAt g (g' x) x) (g'pos : forall x in Ioi a, 0 <= g' x) (hg : Tendsto g atTop (𝓝 
l)) : ∫ x in Ioi a, g' x = l - g a
参数：hderiv : forall x in Ici a, HasDerivAt g (g' x) x；g'pos : forall x in Ioi a, 
0 <= g' x；hg : Tendsto g atTop (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`：integral_Ioi_of_ha
sDerivAt_of_tendsto' (hderiv : forall x in Ici a, HasDerivAt f (f' x) x) (f'int 
: IntegrableOn f' (Ioi a)) (hf : Tendsto f…
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'`：integrableOn_Ioi_deriv_
of_nonneg' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x) (g'pos : forall x
 in Ioi a, 0 <= g' x) (hg : Tendsto g…

--- 原说明 ---
When a function has a limit at infinity `l`, and its derivative is nonnegative, 
then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is inte
grable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a
, +∞)`.
-/
theorem integral_Ioi_of_hasDerivAt_of_nonneg' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonneg' hderiv g'pos hg)
    hg

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`. -/
/-
**MeasureTheory.integrableOn_Ioi_deriv_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integrableOn_Ioi_deriv_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a) 
(hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'neg : forall x in Ioi a, 
g' x <= 0) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a)
参数：hcont : ContinuousWithinAt g (Ici a) a；hderiv : forall x in Ioi a, HasDerivAt
 g (g' x) x；g'neg : forall x in Ioi a, g' x <= 0；hg : Tendsto g atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_neg_iff`：integrable_neg_iff {f : α -> β} : Inte
grable (-f) μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonneg`：integrableOn_Ioi_deriv_o
f_nonneg (hcont : ContinuousWithinAt g (Ici a) a) (hderiv : forall x in Ioi a, H
asDerivAt g (g' x) x) (g'pos : foral…
· 使用定理 `ContinuousWithinAt.neg`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {
f : X → G} {…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…

--- 原说明 ---
When a function has a limit at infinity, and its derivative is nonpositive, then
 the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity at `a⁺`.
-/
theorem integrableOn_Ioi_deriv_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0)
    (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  apply integrable_neg_iff.1
  exact integrableOn_Ioi_deriv_of_nonneg hcont.neg (fun x hx => (hderiv x hx).neg)
    (fun x hx => neg_nonneg_of_nonpos (g'neg x hx)) hg.neg

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
/-
**MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrableOn_Ioi_deriv_of_nonpos' (hderiv : forall x in Ici a, HasDerivAt 
g (g' x) x) (g'neg : forall x in Ioi a, g' x <= 0) (hg : Tendsto g atTop (𝓝 l)) 
: IntegrableOn g' (Ioi a)
参数：hderiv : forall x in Ici a, HasDerivAt g (g' x) x；g'neg : forall x in Ioi a, 
g' x <= 0；hg : Tendsto g atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonpos`：integrableOn_Ioi_deriv_o
f_nonpos (hcont : ContinuousWithinAt g (Ici a) a) (hderiv : forall x in Ioi a, H
asDerivAt g (g' x) x) (g'neg : foral…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
When a function has a limit at infinity, and its derivative is nonpositive, then
 the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`.
-/
theorem integrableOn_Ioi_deriv_of_nonpos' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : Tendsto g atTop (𝓝 l)) : IntegrableOn g' (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun x hx ↦ hderiv x hx.out.le) g'neg hg
  exact (hderiv a self_mem_Ici).continuousAt.continuousWithinAt

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity at `a⁺`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_nonpos (hcont : ContinuousWithinAt g (Ici a)
 a) (hderiv : forall x in Ioi a, HasDerivAt g (g' x) x) (g'neg : forall x in Ioi
 a, g' x <= 0) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a
参数：hcont : ContinuousWithinAt g (Ici a) a；hderiv : forall x in Ioi a, HasDerivAt
 g (g' x) x；g'neg : forall x in Ioi a, g' x <= 0；hg : Tendsto g atTop (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`：integral_Ioi_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a) (hderiv : forall x i
n Ioi a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonpos`：integrableOn_Ioi_deriv_o
f_nonpos (hcont : ContinuousWithinAt g (Ici a) a) (hderiv : forall x in Ioi a, H
asDerivAt g (g' x) x) (g'neg : foral…

--- 原说明 ---
When a function has a limit at infinity `l`, and its derivative is nonpositive, 
then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is inte
grable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a,
 +∞)` and
continuity at `a⁺`.
-/
theorem integral_Ioi_of_hasDerivAt_of_nonpos (hcont : ContinuousWithinAt g (Ici a) a)
    (hderiv : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0)
    (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
/-
**MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos'** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_Ioi_of_hasDerivAt_of_nonpos' (hderiv : forall x in Ici a, HasDeri
vAt g (g' x) x) (g'neg : forall x in Ioi a, g' x <= 0) (hg : Tendsto g atTop (𝓝 
l)) : ∫ x in Ioi a, g' x = l - g a
参数：hderiv : forall x in Ici a, HasDerivAt g (g' x) x；g'neg : forall x in Ioi a, 
g' x <= 0；hg : Tendsto g atTop (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`：integral_Ioi_of_ha
sDerivAt_of_tendsto' (hderiv : forall x in Ici a, HasDerivAt f (f' x) x) (f'int 
: IntegrableOn f' (Ioi a)) (hf : Tendsto f…
· 使用定理 `MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'`：integrableOn_Ioi_deriv_
of_nonpos' (hderiv : forall x in Ici a, HasDerivAt g (g' x) x) (g'neg : forall x
 in Ioi a, g' x <= 0) (hg : Tendsto g…

--- 原说明 ---
When a function has a limit at infinity `l`, and its derivative is nonpositive, 
then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is inte
grable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a
, +∞)`.
-/
theorem integral_Ioi_of_hasDerivAt_of_nonpos' (hderiv : ∀ x ∈ Ici a, HasDerivAt g (g' x) x)
    (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : Tendsto g atTop (𝓝 l)) : ∫ x in Ioi a, g' x = l - g a :=
  integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_deriv_of_nonpos' hderiv g'neg hg)
    hg

end IoiFTC

section IicFTC

variable {E : Type*} {f f' : ℝ → E} {a : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- If the derivative of a function defined on the real line is integrable close to `-∞`, then
the function has a limit at `-∞`. -/
/-
**MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic [CompleteSpace E] (hder
iv : forall x in Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
 : Tendsto f atBot (𝓝 (limUnder atBot f))
参数：hderiv : forall x in Iic a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Ii
c a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HasDerivAt.scomp`：HasDerivAt.scomp (hg : HasDerivAt g₁ g₁' (h x)) (hh : 
HasDerivAt h h' x) : HasDerivAt (g₁ ∘ h) (h' • g₁') x
· 使用定理 `hasDerivAt_neg'`：hasDerivAt_neg' : HasDerivAt (fun x => -x) (-1) x
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`：tendst
o_limUnder_of_hasDerivAt_of_integrableOn_Ioi [CompleteSpace E] (hderiv : forall 
x in Ioi a, HasDerivAt f (f' x) x) (f'int : Integrable…
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.MeasurePreserving.integrableOn_comp_preimage`：∀ {α : Type 
u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [inst : TopologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.Measure.measurePreserving_neg`：∀ {G : Type u_1} [inst : Me
asurableSpace G] [inst_1 : Neg G] [MeasurableNeg G] (μ : MeasureTheory.Measure G
)   [μ.IsNegInvariant], MeasureTh…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If the derivative of a function defined on the real line is integrable close to 
`-∞`, then
the function has a limit at `-∞`.
-/
theorem tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic [CompleteSpace E]
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a)) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) := by
  suffices ∃ a, Tendsto f atBot (𝓝 a) from tendsto_nhds_limUnder this
  let g := f ∘ (fun x ↦ -x)
  have hdg : ∀ x ∈ Ioi (-a), HasDerivAt g (-f' (-x)) x := by
    intro x hx
    have : -x ∈ Iic a := by grind
    simpa using HasDerivAt.scomp x (hderiv (-x) this) (hasDerivAt_neg' x)
  have L : Tendsto g atTop (𝓝 (limUnder atTop g)) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi hdg
    exact ((MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg _)
      (Homeomorph.neg ℝ).measurableEmbedding).2 f'int.neg).mono_set (by simp)
  refine ⟨limUnder atTop g, ?_⟩
  have : Tendsto (fun x ↦ g (-x)) atBot (𝓝 (limUnder atTop g)) := L.comp tendsto_neg_atBot_atTop
  simpa [g] using this

open UniformSpace in
/-- If a function and its derivative are integrable on `(-∞, a]`, then the function tends to zero
at `-∞`. -/
/-
**MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (hderiv : forall x in Iic a
, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a)) (fint : IntegrableOn 
f (Iic a)) : Tendsto f atBot (𝓝 0)
参数：hderiv : forall x in Iic a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Ii
c a)；fint : IntegrableOn f (Iic a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `UniformSpace.Completion.instIsBoundedSMul`：∀ {α : Type u} [inst : Pseudo
MetricSpace α] {M : Type u_1} [inst_1 : Zero M] [inst_2 : Zero α] [inst_3 : SMul
 M α]   [inst_4 : PseudoMetricS…
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`：tendst
o_limUnder_of_hasDerivAt_of_integrableOn_Iic [CompleteSpace E] (hderiv : forall 
x in Iic a, HasDerivAt f (f' x) x) (f'int : Integrable…
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `MeasureTheory.IntegrableAtFilter.eq_zero_of_tendsto`：∀ {α : Type u_1} {E
 : Type u_5} {mα : MeasurableSpace α} [inst : NormedAddCommGroup E] {μ : Measure
Theory.Measure α}   {l : Filter α} {f : α…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.volume_Iic`：volume_Iic {a : Real} : volume (Iic a) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用定理 `UniformSpace.Completion.isUniformEmbedding_coe`：isUniformEmbedding_coe [
T0Space α] : IsUniformEmbedding ((↑) : α -> Completion α)
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
If a function and its derivative are integrable on `(-∞, a]`, then the function 
tends to zero
at `-∞`.
-/
theorem tendsto_zero_of_hasDerivAt_of_integrableOn_Iic
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x)
    (f'int : IntegrableOn f' (Iic a)) (fint : IntegrableOn f (Iic a)) :
    Tendsto f atBot (𝓝 0) := by
  let F : E →L[ℝ] Completion E := Completion.toComplL
  have Fderiv : ∀ x ∈ Iic a, HasDerivAt (F ∘ f) (F (f' x)) x :=
    fun x hx ↦ F.hasFDerivAt.comp_hasDerivAt _ (hderiv x hx)
  have Fint : IntegrableOn (F ∘ f) (Iic a) := by apply F.integrable_comp fint
  have F'int : IntegrableOn (F ∘ f') (Iic a) := by apply F.integrable_comp f'int
  have A : Tendsto (F ∘ f) atBot (𝓝 (limUnder atBot (F ∘ f))) := by
    apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic Fderiv F'int
  have B : limUnder atBot (F ∘ f) = F 0 := by
    have : IntegrableAtFilter (F ∘ f) atBot := by exact ⟨Iic a, Iic_mem_atBot _, Fint⟩
    apply IntegrableAtFilter.eq_zero_of_tendsto this ?_ A
    intro s hs
    rcases mem_atBot_sets.1 hs with ⟨b, hb⟩
    apply le_antisymm (le_top)
    rw [← volume_Iic (a := b)]
    exact measure_mono hb
  rwa [B, ← IsEmbedding.tendsto_nhds_iff] at A
  exact (Completion.isUniformEmbedding_coe E).isEmbedding

variable [CompleteSpace E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a)` and continuity at `a⁻`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`. -/
/-
**MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：integral_Iic_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a
) a) (hderiv : forall x in Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f
' (Iic a)) (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m
参数：hcont : ContinuousWithinAt f (Iic a) a；hderiv : forall x in Iio a, HasDerivAt
 f (f' x) x；f'int : IntegrableOn f' (Iic a)；hf : Tendsto f atBot (𝓝 m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Iic`：intervalIntegral_te
ndsto_integral_Iic (b : Real) (hfi : IntegrableOn f (Iic b) μ) (ha : Tendsto a l
 atBot) : Tendsto (fun i => ∫ x in a i..b…
· 使用定理 `instIsCountablyGenerated_atBot`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α]   [TopologicalSpace.SeparableSpace
 α], Filter.atBot.Is…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Iic_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α), Set.
Iic a ∈ Filter.atBot
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`：integral_eq_sub_of
_hasDerivAt_of_le (hab : a <= b) (hcont : ContinuousOn f (Icc a b)) (hderiv : fo
rall x in Ioo a b, HasDerivAt f (f' x) x) …
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Ioc_of_le`：intervalIntegrable_iff_in
tegrableOn_Ioc_of_le (hab : a <= b) : IntervalIntegrable f μ a b ↔ IntegrableOn 
f (Ioc a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
**Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then 
the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming different
iability
on `(-∞, a)` and continuity at `a⁻`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`.
-/
theorem integral_Iic_of_hasDerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a) a)
    (hderiv : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  have hcont : ContinuousOn f (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) ?_
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a]`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`. -/
/-
**MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：integral_Iic_of_hasDerivAt_of_tendsto' (hderiv : forall x in Iic a, HasDer
ivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a)) (hf : Tendsto f atBot (𝓝 m)) 
: ∫ x in Iic a, f' x = f a - m
参数：hderiv : forall x in Iic a, HasDerivAt f (f' x) x；f'int : IntegrableOn f' (Ii
c a)；hf : Tendsto f atBot (𝓝 m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto`：integral_Iic_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a) a) (hderiv : forall x i
n Iio a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a

--- 原说明 ---
**Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then 
the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming different
iability
on `(-∞, a]`.

Note that such a function always has a limit at minus infinity,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic`.
-/
theorem integral_Iic_of_hasDerivAt_of_tendsto'
    (hderiv : ∀ x ∈ Iic a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine integral_Iic_of_hasDerivAt_of_tendsto ?_ (fun x hx => hderiv x hx.out.le)
    f'int hf
  exact (hderiv a self_mem_Iic).continuousAt.continuousWithinAt

/-- A special case of `integral_Iic_of_hasDerivAt_of_tendsto` where we assume that `f` is C^1 with
compact support. -/
/-
**MeasureTheory._root_.HasCompactSupport.integral_Iic_deriv_eq** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `integral_Iic_of_hasDerivAt_of_tendsto` where we assume that `
f` is C^1 with
compact support.
-/
theorem _root_.HasCompactSupport.integral_Iic_deriv_eq (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Iic b, deriv f x = f b := by
  have := fun x (_ : x ∈ Iio b) ↦ hf.differentiable one_ne_zero x |>.hasDerivAt
  rw [integral_Iic_of_hasDerivAt_of_tendsto hf.continuous.continuousWithinAt this, sub_zero]
  · refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono _root_.atBot_le_cocompact |>.tendsto

open UniformSpace in
/-
**MeasureTheory._root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasCompactSupport.enorm_le_lintegral_Ici_deriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ 1 f) (h'f : HasCompactSupport f) (x : ℝ) :
    ‖f x‖ₑ ≤ ∫⁻ y in Iic x, ‖deriv f y‖ₑ := by
  let I : F →L[ℝ] Completion F := Completion.toComplL
  let f' : ℝ → Completion F := I ∘ f
  have hf' : ContDiff ℝ 1 f' := hf.continuousLinearMap_comp I
  have h'f' : HasCompactSupport f' := h'f.comp_left rfl
  have : ‖f' x‖ₑ ≤ ∫⁻ y in Iic x, ‖deriv f' y‖ₑ := by
    rw [← HasCompactSupport.integral_Iic_deriv_eq hf' h'f' x]
    exact enorm_integral_le_lintegral_enorm _
  convert! this with y
  · simp [f', I, Completion.enorm_coe]
  · rw [fderiv_comp_deriv _ I.differentiableAt (hf.differentiable one_ne_zero _)]
    simp only [ContinuousLinearMap.fderiv]
    simp [I]

end IicFTC

section UnivFTC

variable {E : Type*} {f f' : ℝ → E} {m n : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **Fundamental theorem of calculus-2**, on the whole real line
When a function has a limit `m` at `-∞` and `n` at `+∞`, and its derivative is integrable, then the
integral of the derivative is `n - m`.

Note that such a function always has a limit at `-∞` and `+∞`,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic` and
`tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`. -/
/-
**MeasureTheory.integral_of_hasDerivAt_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_of_hasDerivAt_of_tendsto [CompleteSpace E] (hderiv : forall x, Ha
sDerivAt f (f' x) x) (hf' : Integrable f') (hbot : Tendsto f atBot (𝓝 m)) (htop 
: Tendsto f atTop (𝓝 n)) : ∫ x, f' x = n - m
参数：hderiv : forall x, HasDerivAt f (f' x) x；hf' : Integrable f'；hbot : Tendsto f
 atBot (𝓝 m)；htop : Tendsto f atTop (𝓝 n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
· 使用定理 `Set.Iic_disjoint_Ioi`：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (
Ioi b)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto'`：integral_Iic_of_ha
sDerivAt_of_tendsto' (hderiv : forall x in Iic a, HasDerivAt f (f' x) x) (f'int 
: IntegrableOn f' (Iic a)) (hf : Tendsto f…
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'`：integral_Ioi_of_ha
sDerivAt_of_tendsto' (hderiv : forall x in Ici a, HasDerivAt f (f' x) x) (f'int 
: IntegrableOn f' (Ioi a)) (hf : Tendsto f…
· 使用定理 `_private.Mathlib.MeasureTheory.Integral.IntegralEqImproper.0.MeasureTheo
ry.integral_of_hasDerivAt_of_tendsto._abel_1_1`：∀ {E : Type u_1} {f : ℝ → E} {m 
n : E} [inst : NormedAddCommGroup E], f 0 - m + (n - f 0) = n - m

--- 原说明 ---
**Fundamental theorem of calculus-2**, on the whole real line
When a function has a limit `m` at `-∞` and `n` at `+∞`, and its derivative is i
ntegrable, then the
integral of the derivative is `n - m`.

Note that such a function always has a limit at `-∞` and `+∞`,
see `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic` and
`tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`.
-/
theorem integral_of_hasDerivAt_of_tendsto [CompleteSpace E]
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hbot : Tendsto f atBot (𝓝 m)) (htop : Tendsto f atTop (𝓝 n)) : ∫ x, f' x = n - m := by
  rw [← setIntegral_univ, ← Set.Iic_union_Ioi (a := 0),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf'.integrableOn hf'.integrableOn,
    integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ ↦ hderiv x) hf'.integrableOn hbot,
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ ↦ hderiv x) hf'.integrableOn htop]
  abel

/-- If a function and its derivative are integrable on the real line, then the integral of the
derivative is zero. -/
/-
**MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：integral_eq_zero_of_hasDerivAt_of_integrable (hderiv : forall x, HasDerivA
t f (f' x) x) (hf' : Integrable f') (hf : Integrable f) : ∫ x, f' x = 0
参数：hderiv : forall x, HasDerivAt f (f' x) x；hf' : Integrable f'；hf : Integrable 
f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic`：tendsto_ze
ro_of_hasDerivAt_of_integrableOn_Iic (hderiv : forall x in Iic a, HasDerivAt f (
f' x) x) (f'int : IntegrableOn f' (Iic a)) (fint :…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`：tendsto_ze
ro_of_hasDerivAt_of_integrableOn_Ioi (hderiv : forall x in Ioi a, HasDerivAt f (
f' x) x) (f'int : IntegrableOn f' (Ioi a)) (fint :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MeasureTheory.integral_of_hasDerivAt_of_tendsto`：integral_of_hasDerivAt_
of_tendsto [CompleteSpace E] (hderiv : forall x, HasDerivAt f (f' x) x) (hf' : I
ntegrable f') (hbot : Tendsto f atBot…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a function and its derivative are integrable on the real line, then the integ
ral of the
derivative is zero.
-/
theorem integral_eq_zero_of_hasDerivAt_of_integrable
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f') (hf : Integrable f) :
    ∫ x, f' x = 0 := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  have A : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _hx ↦ hderiv x)
      hf'.integrableOn hf.integrableOn
  have B : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _hx ↦ hderiv x)
      hf'.integrableOn hf.integrableOn
  simpa using integral_of_hasDerivAt_of_tendsto hderiv hf' A B

end UnivFTC

section IoiChangeVariables

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Change-of-variables formula for `Ioi` integrals of vector-valued functions, proved by taking
limits from the result for finite intervals. -/
/-
**MeasureTheory.integral_deriv_smul_comp_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_deriv_smul_comp_Ioi {f f' : Real -> Real} {g : Real -> E} {a : Re
al} (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop) (hff' : forall 
x in Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x) (hg_cont : ContinuousOn g <| f 
'' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a) (hg2 : IntegrableOn (fun x => f' 
x • (g ∘ f) x) (Ici a)) : (∫ x in Ioi a, f' x • (g ∘ f) x) = ∫ u in Ioi (f a), g
 u
参数：hf : ContinuousOn f <| Ici a；hft : Tendsto f atTop atTop；hff' : forall x in I
oi a, HasDerivWithinAt f (f' x) (Ioi x) x；hg_cont : ContinuousOn g <| f '' Ioi a
；hg1 : IntegrableOn g <| f '' Ici a；hg2 : IntegrableOn (fun x => f' x • (g ∘ f) 
x) (Ici a)。
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
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `intervalIntegral.integral_deriv_smul_comp'''`：integral_deriv_smul_comp''
' (hf : ContinuousOn f [[a, b]]) (hff' : forall x in Ioo (min a b) (max a b), Ha
sDerivWithinAt f (f' x) (Ioi x) x)…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`：intervalIntegral_te
ndsto_integral_Ioi (a : Real) (hfi : IntegrableOn f (Ioi a) μ) (hb : Tendsto b l
 atTop) : Tendsto (fun i => ∫ x in a..b i…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `integrableOn_Ici_iff_integrableOn_Ioi`：integrableOn_Ici_iff_integrableOn
_Ioi (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
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
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Change-of-variables formula for `Ioi` integrals of vector-valued functions, prov
ed by taking
limits from the result for finite intervals.
-/
theorem integral_deriv_smul_comp_Ioi {f f' : ℝ → ℝ} {g : ℝ → E} {a : ℝ}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : ∀ x ∈ Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a)) :
    (∫ x in Ioi a, f' x • (g ∘ f) x) = ∫ u in Ioi (f a), g u := by
  have eq : ∀ b : ℝ, a < b → (∫ x in a..b, f' x • (g ∘ f) x) = ∫ u in f a..f b, g u := fun b hb ↦ by
    have i1 : Ioo (min a b) (max a b) ⊆ Ioi a := by
      rw [min_eq_left hb.le]
      exact Ioo_subset_Ioi_self
    have i2 : [[a, b]] ⊆ Ici a := by rw [uIcc_of_le hb.le]; exact Icc_subset_Ici_self
    refine
      intervalIntegral.integral_deriv_smul_comp''' (hf.mono i2)
        (fun x hx => hff' x <| mem_of_mem_of_subset hx i1) (hg_cont.mono <| image_mono ?_)
        (hg1.mono_set <| image_mono ?_) (hg2.mono_set i2) <;> assumption
  rw [integrableOn_Ici_iff_integrableOn_Ioi] at hg2
  have t2 := intervalIntegral_tendsto_integral_Ioi _ hg2 tendsto_id
  have : Ioi (f a) ⊆ f '' Ici a :=
    Ioi_subset_Ici_self.trans <|
      IsPreconnected.intermediate_value_Ici isPreconnected_Ici self_mem_Ici
        (le_principal_iff.mpr <| Ici_mem_atTop _) hf hft
  have t1 := (intervalIntegral_tendsto_integral_Ioi _ (hg1.mono_set this) tendsto_id).comp hft
  exact tendsto_nhds_unique (Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop a) eq) t2) t1

@[deprecated (since := "2026-03-19")]
alias integral_comp_smul_deriv_Ioi := integral_deriv_smul_comp_Ioi

/-- Change-of-variables formula for `Ioi` integrals of scalar-valued functions -/
/-
**MeasureTheory.integral_comp_mul_deriv_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integral_comp_mul_deriv_Ioi {f f' : Real -> Real} {g : Real -> Real} {a : 
Real} (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop) (hff' : foral
l x in Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x) (hg_cont : ContinuousOn g <| 
f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a) (hg2 : IntegrableOn (fun x => (
g ∘ f) x * f' x) (Ici a)) : (∫ x in Ioi a, (g ∘ f) x * f' x) = ∫ u in Ioi (f a),
 g u
参数：hf : ContinuousOn f <| Ici a；hft : Tendsto f atTop atTop；hff' : forall x in I
oi a, HasDerivWithinAt f (f' x) (Ioi x) x；hg_cont : ContinuousOn g <| f '' Ioi a
；hg1 : IntegrableOn g <| f '' Ici a；hg2 : IntegrableOn (fun x => (g ∘ f) x * f' 
x) (Ici a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.integral_deriv_smul_comp_Ioi`：integral_deriv_smul_comp_Ioi
 {f f' : Real -> Real} {g : Real -> E} {a : Real} (hf : ContinuousOn f <| Ici a)
 (hft : Tendsto f atTop atTop) (…

--- 原说明 ---
Change-of-variables formula for `Ioi` integrals of scalar-valued functions
-/
theorem integral_comp_mul_deriv_Ioi {f f' : ℝ → ℝ} {g : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f <| Ici a) (hft : Tendsto f atTop atTop)
    (hff' : ∀ x ∈ Ioi a, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hg_cont : ContinuousOn g <| f '' Ioi a) (hg1 : IntegrableOn g <| f '' Ici a)
    (hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici a)) :
    (∫ x in Ioi a, (g ∘ f) x * f' x) = ∫ u in Ioi (f a), g u := by
  have hg2' : IntegrableOn (fun x => f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2
  simpa [mul_comm] using integral_deriv_smul_comp_Ioi hf hft hff' hg_cont hg1 hg2'

/-- Substitution `y = x ^ p` in integrals over `Ioi 0` -/
/-
**MeasureTheory.integral_comp_rpow_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_comp_rpow_Ioi (g : Real -> E) {p : Real} (hp : p != 0) : ∫ x in I
oi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y
参数：g : Real -> E；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`：integral_image_
eq_integral_abs_deriv_smul (hs : MeasurableSet s) (hf' : forall x in s, HasDeriv
WithinAt f (f' x) s x) (hf : InjOn f s) (g : …
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Real.rpow_left_injOn`：rpow_left_injOn {x : Real} (hx : x != 0) : InjOn (
fun y : Real => y ^ x) { y : Real | 0 <= y }
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Substitution `y = x ^ p` in integrals over `Ioi 0`
-/
theorem integral_comp_rpow_Ioi (g : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y := by
  have a : (· ^ p) '' (Ioi 0) = Ioi (0 : ℝ) := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · exact fun hx ↦ ⟨x ^ (1 / p), rpow_pos_of_pos hx _, by simp [← rpow_mul (le_of_lt hx), hp]⟩
  have := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x hx ↦ (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt)
    ((rpow_left_injOn hp).mono (by grind)) g
  rw [a] at this; rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
  rw [abs_mul, abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]
/-
**MeasureTheory.integral_comp_rpow_Ioi_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_comp_rpow_Ioi_of_pos {g : Real -> E} {p : Real} (hp : 0 < p) : ∫ 
x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y
参数：hp : 0 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.integral_comp_rpow_Ioi`：integral_comp_rpow_Ioi (g : Real -
> E) {p : Real} (hp : p != 0) : ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = 
∫ y in Ioi 0, g y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem integral_comp_rpow_Ioi_of_pos {g : ℝ → E} {p : ℝ} (hp : 0 < p) :
    ∫ x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y := by
  simpa [abs_of_nonneg hp.le] using integral_comp_rpow_Ioi g hp.ne'
/-
**MeasureTheory.integral_comp_rpow_Ioi_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：integral_comp_rpow_Ioi_of_pos' {g : Real -> E} {p : Real} (hp : 0 < p) {c 
: Real} (hc : 0 <= c) : ∫ x in Ioi (c ^ p⁻¹), (p * x ^ (p - 1)) • g (x ^ p) = ∫ 
y in Ioi c, g y
参数：hp : 0 < p；hc : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.image_Ioi_of_strictMonoOn`：ContinuousOn.image_Ioi_of_strict
MonoOn (hf : ContinuousOn f (Ici a)) (hmono : StrictMonoOn f (Ici a)) (htop : Te
ndsto f atTop atTop) : f '' …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `StrictMonoOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f s → s₂ ⊆ s → S
trictMo…
· 使用定理 `Real.strictMonoOn_rpow_Ici_of_exponent_pos`：strictMonoOn_rpow_Ici_of_exp
onent_pos {r : Real} (hr : 0 < r) : StrictMonoOn (fun (x : Real) => x ^ r) (Set.
Ici 0)
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`：integral_image_
eq_integral_abs_deriv_smul (hs : MeasurableSet s) (hf' : forall x in s, HasDeriv
WithinAt f (f' x) s x) (hf : InjOn f s) (g : …
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
（共 42 条，此处仅展示前 30 条）
-/
theorem integral_comp_rpow_Ioi_of_pos' {g : ℝ → E} {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) :
    ∫ x in Ioi (c ^ p⁻¹), (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi c, g y := by
  have : 0 ≤ c ^ p⁻¹ := by positivity
  have : Ioi c = (· ^ p) '' Ioi (c ^ p⁻¹) := by
    rw [(continuous_rpow_const hp.le).continuousOn.image_Ioi_of_strictMonoOn
          ((strictMonoOn_rpow_Ici_of_exponent_pos hp).mono (by grind)) (tendsto_rpow_atTop hp)]
    simp [← rpow_mul hc, hp.ne.symm]
  rw [this, integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := c ^ p⁻¹))
      (fun _ _ ↦ (hasDerivAt_rpow_const (by grind)).hasDerivWithinAt)
      ((rpow_left_injOn hp.ne.symm).mono (Set.Ioi_subset_Ici (by positivity)))]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ ?_)
  have : 0 ≤ x := by grind
  rw [abs_of_nonneg (by positivity)]

/-- Substitution `y = exp x` in integrals over `Ioi a` -/
/-
**MeasureTheory.integral_comp_exp_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_comp_exp_Ioi (g : Real -> E) (a : Real) : ∫ x in Ioi a, exp x • g
 (exp x) = ∫ y in Ioi (exp a), g y
参数：g : Real -> E；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.image_exp_Ioi`：image_exp_Ioi (a : Real) : exp '' Ioi a = Ioi (exp a
)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`：integral_image_
eq_integral_abs_deriv_smul (hs : MeasurableSet s) (hf' : forall x in s, HasDeriv
WithinAt f (f' x) s x) (hf : InjOn f s) (g : …
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp

--- 原说明 ---
Substitution `y = exp x` in integrals over `Ioi a`
-/
theorem integral_comp_exp_Ioi (g : ℝ → E) (a : ℝ) :
    ∫ x in Ioi a, exp x • g (exp x) = ∫ y in Ioi (exp a), g y := by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy ↦ exp_injective hxy) g
/-
**MeasureTheory.integrableOn_comp_exp_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrableOn_comp_exp_Ioi (g : Real -> E) (a : Real) : IntegrableOn (fun x
 => exp x • g (exp x)) (Ioi a) ↔ IntegrableOn g (Ioi (exp a))
参数：g : Real -> E；a : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.image_exp_Ioi`：image_exp_Ioi (a : Real) : exp '' Ioi a = Ioi (exp a
)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul`：integr
ableOn_image_iff_integrableOn_abs_deriv_smul (hs : MeasurableSet s) (hf' : foral
l x in s, HasDerivWithinAt f (f' x) s x) (hf : InjOn f…
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_exp`：hasDerivAt_exp (x : Real) : HasDerivAt exp (exp x) 
x
· 使用定理 `Real.exp_injective`：exp_injective : Function.Injective exp
-/
theorem integrableOn_comp_exp_Ioi (g : ℝ → E) (a : ℝ) :
    IntegrableOn (fun x ↦ exp x • g (exp x)) (Ioi a) ↔ IntegrableOn g (Ioi (exp a)) := by
  symm; rw [← image_exp_Ioi]
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ioi (a := a)) (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt)
      (fun x _ y _ hxy ↦ exp_injective hxy) g

/-- Substitution `y = log x` in integrals over `Ioi a` -/
/-
**MeasureTheory.integral_comp_log_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_comp_log_Ioi (g : Real -> E) {a : Real} (ha : 0 < a) : ∫ x in Ioi
 a, x⁻¹ • g (log x) = ∫ y in Ioi (log a), g y
参数：g : Real -> E；ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_comp_exp_Ioi`：integral_comp_exp_Ioi (g : Real -> 
E) (a : Real) : ∫ x in Ioi a, exp x • g (exp x) = ∫ y in Ioi (exp a), g y

--- 原说明 ---
Substitution `y = log x` in integrals over `Ioi a`
-/
theorem integral_comp_log_Ioi (g : ℝ → E) {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi a, x⁻¹ • g (log x) = ∫ y in Ioi (log a), g y := by
  simpa [exp_log ha] using (integral_comp_exp_Ioi (fun x ↦ x⁻¹ • g (log x)) (log a)).symm
/-
**MeasureTheory.integrableOn_comp_log_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrableOn_comp_log_Ioi (g : Real -> E) {a : Real} (ha : 0 < a) : Integr
ableOn (fun x => x⁻¹ • g (log x)) (Ioi a) ↔ IntegrableOn g (Ioi (log a))
参数：g : Real -> E；ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `MeasureTheory.integrableOn_comp_exp_Ioi`：integrableOn_comp_exp_Ioi (g : 
Real -> E) (a : Real) : IntegrableOn (fun x => exp x • g (exp x)) (Ioi a) ↔ Inte
grableOn g (Ioi (exp a))
-/
theorem integrableOn_comp_log_Ioi (g : ℝ → E) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x ↦ x⁻¹ • g (log x)) (Ioi a) ↔ IntegrableOn g (Ioi (log a)) := by
  symm
  simpa  [exp_log ha] using integrableOn_comp_exp_Ioi (fun x ↦ x⁻¹ • g (log x)) (log a)
/-
**MeasureTheory.integral_comp_mul_left_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：integral_comp_mul_left_Ioi (g : Real -> E) (a : Real) {b : Real} (hb : 0 <
 b) : ∫ x in Ioi a, g (b * x) = b⁻¹ • ∫ x in Ioi (b * a), g x
参数：g : Real -> E；a : Real；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MeasureTheory.Measure.integral_comp_mul_left`：integral_comp_mul_left (g 
: Real -> F) (a : Real) : (∫ x : Real, g (a * x)) = |a⁻¹| • ∫ y : Real, g y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_comp_right`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_3}
 [inst : Zero M] {s : Set α} (f : β → α) {g : α → M} {x : β},   (f ⁻¹' s).indica
tor (g ∘ f) x …
· 使用定理 `Set.preimage_const_mul_Ioi₀`：preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c
) : (c * ·) ⁻¹' Ioi a = Ioi (a / c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem integral_comp_mul_left_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi a, g (b * x) = b⁻¹ • ∫ x in Ioi (b * a), g x := by
  have : ∀ c : ℝ, MeasurableSet (Ioi c) := fun c => measurableSet_Ioi
  rw [← integral_indicator (this _), ← integral_indicator (this _),
    ← abs_of_pos (inv_pos.mpr hb), ← Measure.integral_comp_mul_left]
  congr
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Ioi₀ _ hb, mul_div_cancel_left₀ _ hb.ne',
    Function.comp_def]
/-
**MeasureTheory.integral_comp_mul_left_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integral_comp_mul_left_Ioi' (g : Real -> E) (a : Real) {b : Real} (hb : 0 
< b) : b • ∫ x in Ioi a, g (b * x) = ∫ x in Ioi (b * a), g x
参数：g : Real -> E；a : Real；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_comp_mul_left_Ioi`：integral_comp_mul_left_Ioi (g 
: Real -> E) (a : Real) {b : Real} (hb : 0 < b) : ∫ x in Ioi a, g (b * x) = b⁻¹ 
• ∫ x in Ioi (b * a), g x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_mul_left_Ioi' (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    b • ∫ x in Ioi a, g (b * x) = ∫ x in Ioi (b * a), g x := by
  simp [integral_comp_mul_left_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']
/-
**MeasureTheory.integral_comp_mul_right_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integral_comp_mul_right_Ioi (g : Real -> E) (a : Real) {b : Real} (hb : 0 
< b) : ∫ x in Ioi a, g (x * b) = b⁻¹ • ∫ x in Ioi (a * b), g x
参数：g : Real -> E；a : Real；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.integral_comp_mul_left_Ioi`：integral_comp_mul_left_Ioi (g 
: Real -> E) (a : Real) {b : Real} (hb : 0 < b) : ∫ x in Ioi a, g (b * x) = b⁻¹ 
• ∫ x in Ioi (b * a), g x
-/
theorem integral_comp_mul_right_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi a, g (x * b) = b⁻¹ • ∫ x in Ioi (a * b), g x := by
  simpa [mul_comm] using integral_comp_mul_left_Ioi g a hb
/-
**MeasureTheory.integral_comp_mul_right_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_comp_mul_right_Ioi' (g : Real -> E) (a : Real) {b : Real} (hb : 0
 < b) : b • ∫ x in Ioi a, g (x * b) = ∫ x in Ioi (a * b), g x
参数：g : Real -> E；a : Real；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_comp_mul_right_Ioi`：integral_comp_mul_right_Ioi (
g : Real -> E) (a : Real) {b : Real} (hb : 0 < b) : ∫ x in Ioi a, g (x * b) = b⁻
¹ • ∫ x in Ioi (a * b), g x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_mul_right_Ioi' (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
    b • ∫ x in Ioi a, g (x * b) = ∫ x in Ioi (a * b), g x := by
  simp [integral_comp_mul_right_Ioi g a hb, smul_smul, mul_inv_cancel₀ hb.ne']

end IoiChangeVariables

section IoiIntegrability

open Real

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E]

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability. -/
/-
**MeasureTheory.integrableOn_Ioi_comp_rpow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：integrableOn_Ioi_comp_rpow_iff [NormedSpace Real E] (f : Real -> E) {p : R
eal} (hp : p != 0) : IntegrableOn (fun x => (|p| * x ^ (p - 1)) • f (x ^ p)) (Io
i 0) ↔ IntegrableOn f (Ioi 0)
参数：f : Real -> E；hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_rpow_const`：hasDerivAt_rpow_const {x p : Real} (h : x !=
 0 ∨ 1 <= p) : HasDerivAt (fun x => x ^ p) (p * x ^ (p - 1)) x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_lt_rpow`：rpow_lt_rpow (hx : 0 <= x) (hxy : x < y) (hz : 0 < z)
 : x ^ z < y ^ z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability.
-/
theorem integrableOn_Ioi_comp_rpow_iff [NormedSpace ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => (|p| * x ^ (p - 1)) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  let S := Ioi (0 : ℝ)
  have a1 : ∀ x : ℝ, x ∈ S → HasDerivWithinAt (fun t : ℝ => t ^ p) (p * x ^ (p - 1)) S x :=
    fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
  have a2 : InjOn (fun x : ℝ => x ^ p) S := by
    rcases lt_or_gt_of_ne hp with (h | h)
    · apply StrictAntiOn.injOn
      intro x hx y hy hxy
      rw [← inv_lt_inv₀ (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p), ← rpow_neg (le_of_lt hx), ←
        rpow_neg (le_of_lt hy)]
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h)
    exact StrictMonoOn.injOn fun x hx y _hy hxy => rpow_lt_rpow (mem_Ioi.mp hx).le hxy h
  have a3 : (fun t : ℝ => t ^ p) '' S = S := by
    ext1 x; rw [mem_image]; constructor
    · rintro ⟨y, hy, rfl⟩; exact rpow_pos_of_pos hy p
    · intro hx; refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, ?_⟩
      rw [← rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one]
  have := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi a1 a2 f
  rw [a3] at this
  rw [this]
  refine integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp_rw [abs_mul, abs_of_nonneg (rpow_nonneg (le_of_lt hx) _)]

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability (version
without `|p|` factor) -/
/-
**MeasureTheory.integrableOn_Ioi_comp_rpow_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：integrableOn_Ioi_comp_rpow_iff' [NormedSpace Real E] (f : Real -> E) {p : 
Real} (hp : p != 0) : IntegrableOn (fun x => x ^ (p - 1) • f (x ^ p)) (Ioi 0) ↔ 
IntegrableOn f (Ioi 0)
参数：f : Real -> E；hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_Ioi_comp_rpow_iff`：integrableOn_Ioi_comp_rpow
_iff [NormedSpace Real E] (f : Real -> E) {p : Real} (hp : p != 0) : IntegrableO
n (fun x => (|p| * x ^ (p - 1)) • …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.integrable_smul_iff`：integrable_smul_iff [NormedDivisionRi
ng 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -
> β) : Integrable (c • …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [
AddLeftMono α] {a : α}, 0 < |a| ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability (
version
without `|p|` factor)
-/
theorem integrableOn_Ioi_comp_rpow_iff' [NormedSpace ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
    IntegrableOn (fun x => x ^ (p - 1) • f (x ^ p)) (Ioi 0) ↔ IntegrableOn f (Ioi 0) := by
  simpa only [← integrableOn_Ioi_comp_rpow_iff f hp, mul_smul] using!
    (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm
/-
**MeasureTheory.integrableOn_Ioi_comp_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：integrableOn_Ioi_comp_mul_left_iff (f : Real -> E) (c : Real) {a : Real} (
ha : 0 < a) : IntegrableOn (fun x => f (a * x)) (Ioi c) ↔ IntegrableOn f (Ioi <|
 a * c)
参数：f : Real -> E；c : Real；ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_comp_right`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_3}
 [inst : Zero M] {s : Set α} (f : β → α) {g : α → M} {x : β},   (f ⁻¹' s).indica
tor (g ∘ f) x …
· 使用定理 `Set.preimage_const_mul_Ioi₀`：preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c
) : (c * ·) ⁻¹' Ioi a = Ioi (a / c)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MeasureTheory.integrable_comp_mul_left_iff`：integrable_comp_mul_left_iff
 (g : Real -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (R * x)) ↔ In
tegrable g
-/
theorem integrableOn_Ioi_comp_mul_left_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (a * x)) (Ioi c) ↔ IntegrableOn f (Ioi <| a * c) := by
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi c)]
  rw [← integrable_indicator_iff (measurableSet_Ioi : MeasurableSet <| Ioi <| a * c)]
  convert! integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2
  ext1 x
  rw [← indicator_comp_right, preimage_const_mul_Ioi₀ _ ha, mul_comm a c,
    mul_div_cancel_right₀ _ ha.ne', Function.comp_def]
/-
**MeasureTheory.integrableOn_Ioi_comp_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integrableOn_Ioi_comp_mul_right_iff (f : Real -> E) (c : Real) {a : Real} 
(ha : 0 < a) : IntegrableOn (fun x => f (x * a)) (Ioi c) ↔ IntegrableOn f (Ioi <
| c * a)
参数：f : Real -> E；c : Real；ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.integrableOn_Ioi_comp_mul_left_iff`：integrableOn_Ioi_comp_
mul_left_iff (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a) : IntegrableOn (
fun x => f (a * x)) (Ioi c) ↔ Integrab…
-/
theorem integrableOn_Ioi_comp_mul_right_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => f (x * a)) (Ioi c) ↔ IntegrableOn f (Ioi <| c * a) := by
  simpa only [mul_comm, mul_zero] using integrableOn_Ioi_comp_mul_left_iff f c ha

end IoiIntegrability

/-!
## Integration by parts
-/

section IntegrationByPartsBilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {L : E →L[ℝ] F →L[ℝ] G} {u : ℝ → E} {v : ℝ → F} {u' : ℝ → E} {v' : ℝ → F}
  {m n : G}

/-
**MeasureTheory.integral_bilinear_hasDerivAt_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_bilinear_hasDerivAt_eq_sub [CompleteSpace G] (hu : forall x in ts
upport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt v (v' 
x) x) (huv : Integrable (fun x => L (u x) (v' x) + L (u' x) (v x))) (h_bot : Ten
dsto (fun x => L (u x) (v x)) atBot (𝓝 m)) (h_top : Tendsto (fun x => L (u x) (v
 x)) atTop (𝓝 n)) : ∫ (x : Real), L (u x) (v' x) + L (u' x) (v x) = n - m
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv : Integrable (fun x => L (u x) (v' x) + L (u' x) (v
 x))；h_bot : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 m)；h_top : Tendsto (fun x
 => L (u x) (v x)) atTop (𝓝 n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_of_hasDerivAt_of_tendsto`：integral_of_hasDerivAt_
of_tendsto [CompleteSpace E] (hderiv : forall x, HasDerivAt f (f' x) x) (hf' : I
ntegrable f') (hbot : Tendsto f atBot…
· 使用定理 `ContinuousLinearMap.hasDerivAt_of_bilinear`：hasDerivAt_of_bilinear (hu :
 x in tsupport v -> HasDerivAt u u' x) (hv : x in tsupport u -> HasDerivAt v v' 
x) : HasDerivAt (fun x => B (u x…
-/
theorem integral_bilinear_hasDerivAt_eq_sub [CompleteSpace G]
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv : Integrable (fun x ↦ L (u x) (v' x) + L (u' x) (v x)))
    (h_bot : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : ℝ), L (u x) (v' x) + L (u' x) (v x) = n - m :=
  integral_of_hasDerivAt_of_tendsto (fun x ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
    huv h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
With respect to a general bilinear form. For the specific case of multiplication, see
`integral_mul_deriv_eq_deriv_mul`. -/
/-
**MeasureTheory.integral_bilinear_hasDerivAt_right_eq_sub** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：integral_bilinear_hasDerivAt_right_eq_sub [CompleteSpace G] (hu : forall x
 in tsupport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt 
v (v' x) x) (huv' : Integrable (fun x => L (u x) (v' x))) (hu'v : Integrable (fu
n x => L (u' x) (v x))) (h_bot : Tendsto (fun x => L (u x) (v x)) atBot (𝓝 m)) (
h_top : Tendsto (fun x => L (u x) (v x)) atTop (𝓝 n)) : ∫ (x : Real), L (u x) (v
' x) = n - m - ∫ (x : Real), L (u' x) (v x)
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv' : Integrable (fun x => L (u x) (v' x))；hu'v : Inte
grable (fun x => L (u' x) (v x))；h_bot : Tendsto (fun x => L (u x) (v x)) atBot 
(𝓝 m)；h_top : Tendsto (fun x => L (u x) (v x)) atTop (𝓝 n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_eq_sub`：integral_bilinear_has
DerivAt_eq_sub [CompleteSpace G] (hu : forall x in tsupport v, HasDerivAt u (u' 
x) x) (hv : forall x in tsupport u, Has…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…

--- 原说明 ---
**Integration by parts on (-∞, ∞).**
With respect to a general bilinear form. For the specific case of multiplication
, see
`integral_mul_deriv_eq_deriv_mul`.
-/
theorem integral_bilinear_hasDerivAt_right_eq_sub [CompleteSpace G]
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x ↦ L (u x) (v' x))) (hu'v : Integrable (fun x ↦ L (u' x) (v x)))
    (h_bot : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 m))
    (h_top : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 n)) :
    ∫ (x : ℝ), L (u x) (v' x) = n - m - ∫ (x : ℝ), L (u' x) (v x) := by
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  exact integral_bilinear_hasDerivAt_eq_sub hu hv (huv'.add hu'v) h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
With respect to a general bilinear form, assuming moreover that the total function is integrable.
-/
/-
**MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (hu : forall 
x in tsupport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt
 v (v' x) x) (huv' : Integrable (fun x => L (u x) (v' x))) (hu'v : Integrable (f
un x => L (u' x) (v x))) (huv : Integrable (fun x => L (u x) (v x))) : ∫ (x : Re
al), L (u x) (v' x) = - ∫ (x : Real), L (u' x) (v x)
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv' : Integrable (fun x => L (u x) (v' x))；hu'v : Inte
grable (fun x => L (u' x) (v x))；huv : Integrable (fun x => L (u x) (v x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Iic`：tendsto_ze
ro_of_hasDerivAt_of_integrableOn_Iic (hderiv : forall x in Iic a, HasDerivAt f (
f' x) x) (f'int : IntegrableOn f' (Iic a)) (fint :…
· 使用定理 `ContinuousLinearMap.hasDerivAt_of_bilinear`：hasDerivAt_of_bilinear (hu :
 x in tsupport v -> HasDerivAt u u' x) (hv : x in tsupport u -> HasDerivAt v v' 
x) : HasDerivAt (fun x => B (u x…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `MeasureTheory.tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`：tendsto_ze
ro_of_hasDerivAt_of_integrableOn_Ioi (hderiv : forall x in Ioi a, HasDerivAt f (
f' x) x) (f'int : IntegrableOn f' (Ioi a)) (fint :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_right_eq_sub`：integral_biline
ar_hasDerivAt_right_eq_sub [CompleteSpace G] (hu : forall x in tsupport v, HasDe
rivAt u (u' x) x) (hv : forall x in tsupport …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0

--- 原说明 ---
**Integration by parts on (-∞, ∞).**
With respect to a general bilinear form, assuming moreover that the total functi
on is integrable.
-/
theorem integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (fun x ↦ L (u x) (v' x))) (hu'v : Integrable (fun x ↦ L (u' x) (v x)))
    (huv : Integrable (fun x ↦ L (u x) (v x))) :
    ∫ (x : ℝ), L (u x) (v' x) = - ∫ (x : ℝ), L (u' x) (v x) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have I : Tendsto (fun x ↦ L (u x) (v x)) atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _hx ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  have J : Tendsto (fun x ↦ L (u x) (v x)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _hx ↦ L.hasDerivAt_of_bilinear (hu x) (hv x))
      (huv'.add hu'v).integrableOn huv.integrableOn
  simp [integral_bilinear_hasDerivAt_right_eq_sub hu hv huv' hu'v I J]

end IntegrationByPartsBilinear

section IntegrationByPartsAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℝ} {a' b' : A} {u : ℝ → A} {v : ℝ → A} {u' : ℝ → A} {v' : ℝ → A}

/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
/-
**MeasureTheory.integral_deriv_mul_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_deriv_mul_eq_sub [CompleteSpace A] (hu : forall x in tsupport v, 
HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt v (v' x) x) (huv
 : Integrable (u' * v + u * v')) (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top :
 Tendsto (u * v) atTop (𝓝 b')) : ∫ (x : Real), u' x * v x + u x * v' x = b' - a'
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv : Integrable (u' * v + u * v')；h_bot : Tendsto (u *
 v) atBot (𝓝 a')；h_top : Tendsto (u * v) atTop (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_of_hasDerivAt_of_tendsto`：integral_of_hasDerivAt_
of_tendsto [CompleteSpace E] (hderiv : forall x, HasDerivAt f (f' x) x) (hf' : I
ntegrable f') (hbot : Tendsto f atBot…
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ContinuousLinearMap.hasDerivAt_of_bilinear`：hasDerivAt_of_bilinear (hu :
 x in tsupport v -> HasDerivAt u u' x) (hv : x in tsupport u -> HasDerivAt v v' 
x) : HasDerivAt (fun x => B (u x…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`.
-/
theorem integral_deriv_mul_eq_sub [CompleteSpace A]
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv : Integrable (u' * v + u * v'))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u' x * v x + u x * v' x = b' - a' := by
  refine integral_of_hasDerivAt_of_tendsto (fun x ↦ ?_) huv h_bot h_top
  simpa [add_comm] using! (ContinuousLinearMap.mul ℝ A).hasDerivAt_of_bilinear (hu x) (hv x)

/-- **Integration by parts on (-∞, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
/-
**MeasureTheory.integral_mul_deriv_eq_deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：integral_mul_deriv_eq_deriv_mul [CompleteSpace A] (hu : forall x in tsuppo
rt v, HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt v (v' x) x
) (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (h_bot : Tendsto (u 
* v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) : ∫ (x : Real), u x * 
v' x = b' - a' - ∫ (x : Real), u' x * v x
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv' : Integrable (u * v')；hu'v : Integrable (u' * v)；h
_bot : Tendsto (u * v) atBot (𝓝 a')；h_top : Tendsto (u * v) atTop (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_right_eq_sub`：integral_biline
ar_hasDerivAt_right_eq_sub [CompleteSpace G] (hu : forall x in tsupport v, HasDe
rivAt u (u' x) x) (hv : forall x in tsupport …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
**Integration by parts on (-∞, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
-/
theorem integral_mul_deriv_eq_deriv_mul [CompleteSpace A]
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v))
    (h_bot : Tendsto (u * v) atBot (𝓝 a')) (h_top : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ), u x * v' x = b' - a' - ∫ (x : ℝ), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_sub (L := ContinuousLinearMap.mul ℝ A)
    hu hv huv' hu'v h_bot h_top

/-- **Integration by parts on (-∞, ∞).**
Version assuming that the total function is integrable -/
/-
**MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integral_mul_deriv_eq_deriv_mul_of_integrable (hu : forall x in tsupport v
, HasDerivAt u (u' x) x) (hv : forall x in tsupport u, HasDerivAt v (v' x) x) (h
uv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v
)) : ∫ (x : Real), u x * v' x = - ∫ (x : Real), u' x * v x
参数：hu : forall x in tsupport v, HasDerivAt u (u' x) x；hv : forall x in tsupport 
u, HasDerivAt v (v' x) x；huv' : Integrable (u * v')；hu'v : Integrable (u' * v)；h
uv : Integrable (u * v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrab
le`：integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (hu : forall x 
in tsupport v, HasDerivAt u (u' x) x) (hv : forall x in tsupport…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
**Integration by parts on (-∞, ∞).**
Version assuming that the total function is integrable
-/
theorem integral_mul_deriv_eq_deriv_mul_of_integrable
    (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
    (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
    ∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x :=
  integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable (L := ContinuousLinearMap.mul ℝ A)
    hu hv huv' hu'v huv

variable [CompleteSpace A]

-- TODO: also apply `Tendsto _ (𝓝[>] a) (𝓝 a')` generalization to
-- `integral_Ioi_of_hasDerivAt_of_tendsto` and `integral_Iic_of_hasDerivAt_of_tendsto`
/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
/-
**MeasureTheory.integral_Ioi_deriv_mul_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Ioi_deriv_mul_eq_sub (hu : forall x in Ioi a, HasDerivAt u (u' x)
 x) (hv : forall x in Ioi a, HasDerivAt v (v' x) x) (huv : IntegrableOn (u' * v 
+ u * v') (Ioi a)) (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto
 (u * v) atTop (𝓝 b')) : ∫ (x : Real) in Ioi a, u' x * v x + u x * v' x = b' - a
'
参数：hu : forall x in Ioi a, HasDerivAt u (u' x) x；hv : forall x in Ioi a, HasDeri
vAt v (v' x) x；huv : IntegrableOn (u' * v + u * v') (Ioi a)；h_zero : Tendsto (u 
* v) (𝓝[>] a) (𝓝 a')；h_infty : Tendsto (u * v) atTop (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_of_eventuallyEq`：HasDerivAt.congr_of_eventuallyEq (h : 
HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_ne_nhds`：eventually_ne_nhds [T1Space X] {a b : X} (h : a != b
) : forallᶠ x in 𝓝 a, x != b
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto`：integral_Ioi_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Ici a) a) (hderiv : forall x i
n Ioi a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_update_same`：continuousWithinAt_update_same [Decidabl
eEq α] {y : β} : ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x
) (𝓝 y)
· 使用定理 `Set.Ici_sdiff_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ici a \ {a} = Set.Ioi a

--- 原说明 ---
For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`.
-/
theorem integral_Ioi_deriv_mul_eq_sub
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Ioi a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ) in Ioi a, u' x * v x + u x * v' x = b' - a' := by
  rw [← Ici_sdiff_left] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x (hx : a < x)
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx.ne.symm] with y hy
    exact Function.update_of_ne hy a' (u * v)
  have htendsto : Tendsto f atTop (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [eventually_ne_atTop a] with x hx
    exact (Function.update_of_ne hx a' (u * v)).symm
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/-- **Integration by parts on (a, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
/-
**MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_Ioi_mul_deriv_eq_deriv_mul (hu : forall x in Ioi a, HasDerivAt u 
(u' x) x) (hv : forall x in Ioi a, HasDerivAt v (v' x) x) (huv' : IntegrableOn (
u * v') (Ioi a)) (hu'v : IntegrableOn (u' * v) (Ioi a)) (h_zero : Tendsto (u * v
) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) : ∫ (x : Real) in Io
i a, u x * v' x = b' - a' - ∫ (x : Real) in Ioi a, u' x * v x
参数：hu : forall x in Ioi a, HasDerivAt u (u' x) x；hv : forall x in Ioi a, HasDeri
vAt v (v' x) x；huv' : IntegrableOn (u * v') (Ioi a)；hu'v : IntegrableOn (u' * v)
 (Ioi a)；h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')；h_infty : Tendsto (u * v) atTo
p (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用引理 `Pi.mul_def`：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.integral_Ioi_deriv_mul_eq_sub`：integral_Ioi_deriv_mul_eq_s
ub (hu : forall x in Ioi a, HasDerivAt u (u' x) x) (hv : forall x in Ioi a, HasD
erivAt v (v' x) x) (huv : Integra…
· 使用定理 `MeasureTheory.IntegrableOn.add`：∀ {α : Type u_1} {ε' : Type u_4} {mα : M
easurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topologica
lSpace ε'] [inst_1 :…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α

--- 原说明 ---
**Integration by parts on (a, ∞).**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
-/
theorem integral_Ioi_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ Ioi a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Ioi a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Ioi a)) (hu'v : IntegrableOn (u' * v) (Ioi a))
    (h_zero : Tendsto (u * v) (𝓝[>] a) (𝓝 a')) (h_infty : Tendsto (u * v) atTop (𝓝 b')) :
    ∫ (x : ℝ) in Ioi a, u x * v' x = b' - a' - ∫ (x : ℝ) in Ioi a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Ioi_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

/-- For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`. -/
/-
**MeasureTheory.integral_Iic_deriv_mul_eq_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Iic_deriv_mul_eq_sub (hu : forall x in Iio a, HasDerivAt u (u' x)
 x) (hv : forall x in Iio a, HasDerivAt v (v' x) x) (huv : IntegrableOn (u' * v 
+ u * v') (Iic a)) (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto
 (u * v) atBot (𝓝 b')) : ∫ (x : Real) in Iic a, u' x * v x + u x * v' x = a' - b
'
参数：hu : forall x in Iio a, HasDerivAt u (u' x) x；hv : forall x in Iio a, HasDeri
vAt v (v' x) x；huv : IntegrableOn (u' * v + u * v') (Iic a)；h_zero : Tendsto (u 
* v) (𝓝[<] a) (𝓝 a')；h_infty : Tendsto (u * v) atBot (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_of_eventuallyEq`：HasDerivAt.congr_of_eventuallyEq (h : 
HasDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) : HasDerivAt f₁ f' x
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Iio_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotOrder α
] (x : α), Set.Iio x ∈ Filter.atBot
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto`：integral_Iic_of_has
DerivAt_of_tendsto (hcont : ContinuousWithinAt f (Iic a) a) (hderiv : forall x i
n Iio a, HasDerivAt f (f' x) x) (f'int : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_update_same`：continuousWithinAt_update_same [Decidabl
eEq α] {y : β} : ContinuousWithinAt (update f x y) s x ↔ Tendsto f (𝓝[s \ {x}] x
) (𝓝 y)
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a

--- 原说明 ---
For finite intervals, see: `intervalIntegral.integral_deriv_mul_eq_sub`.
-/
theorem integral_Iic_deriv_mul_eq_sub
    (hu : ∀ x ∈ Iio a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Iio a, HasDerivAt v (v' x) x)
    (huv : IntegrableOn (u' * v + u * v') (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : ℝ) in Iic a, u' x * v x + u x * v' x = a' - b' := by
  rw [← Iic_sdiff_right] at h_zero
  let f := Function.update (u * v) a a'
  have hderiv : ∀ x ∈ Iio a, HasDerivAt f (u' x * v x + u x * v' x) x := by
    intro x hx
    apply ((hu x hx).mul (hv x hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with x (hx : x < a)
    exact Function.update_of_ne (ne_of_lt hx) a' (u * v)
  have htendsto : Tendsto f atBot (𝓝 b') := by
    apply h_infty.congr'
    filter_upwards [Iio_mem_atBot a] with x (hx : x < a)
    exact (Function.update_of_ne (ne_of_lt hx) a' (u * v)).symm
  simpa using integral_Iic_of_hasDerivAt_of_tendsto
    (continuousWithinAt_update_same.mpr h_zero) hderiv huv htendsto

/-- **Integration by parts on $(∞, a]$.**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
/-
**MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：integral_Iic_mul_deriv_eq_deriv_mul (hu : forall x in Iio a, HasDerivAt u 
(u' x) x) (hv : forall x in Iio a, HasDerivAt v (v' x) x) (huv' : IntegrableOn (
u * v') (Iic a)) (hu'v : IntegrableOn (u' * v) (Iic a)) (h_zero : Tendsto (u * v
) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) : ∫ (x : Real) in Ii
c a, u x * v' x = a' - b' - ∫ (x : Real) in Iic a, u' x * v x
参数：hu : forall x in Iio a, HasDerivAt u (u' x) x；hv : forall x in Iio a, HasDeri
vAt v (v' x) x；huv' : IntegrableOn (u * v') (Iic a)；hu'v : IntegrableOn (u' * v)
 (Iic a)；h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')；h_infty : Tendsto (u * v) atBo
t (𝓝 b')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add`：integral_add {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用引理 `Pi.mul_def`：mul_def (f g : forall i, M i) : f * g = fun i => f i * g i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.integral_Iic_deriv_mul_eq_sub`：integral_Iic_deriv_mul_eq_s
ub (hu : forall x in Iio a, HasDerivAt u (u' x) x) (hv : forall x in Iio a, HasD
erivAt v (v' x) x) (huv : Integra…
· 使用定理 `MeasureTheory.IntegrableOn.add`：∀ {α : Type u_1} {ε' : Type u_4} {mα : M
easurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topologica
lSpace ε'] [inst_1 :…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α

--- 原说明 ---
**Integration by parts on $(∞, a]$.**
For finite intervals, see: `intervalIntegral.integral_mul_deriv_eq_deriv_mul`.
-/
theorem integral_Iic_mul_deriv_eq_deriv_mul
    (hu : ∀ x ∈ Iio a, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Iio a, HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (u * v') (Iic a)) (hu'v : IntegrableOn (u' * v) (Iic a))
    (h_zero : Tendsto (u * v) (𝓝[<] a) (𝓝 a')) (h_infty : Tendsto (u * v) atBot (𝓝 b')) :
    ∫ (x : ℝ) in Iic a, u x * v' x = a' - b' - ∫ (x : ℝ) in Iic a, u' x * v x := by
  rw [Pi.mul_def] at huv' hu'v
  rw [eq_sub_iff_add_eq, ← integral_add huv' hu'v]
  simpa only [add_comm] using integral_Iic_deriv_mul_eq_sub hu hv (hu'v.add huv') h_zero h_infty

end IntegrationByPartsAlgebra

end MeasureTheory

