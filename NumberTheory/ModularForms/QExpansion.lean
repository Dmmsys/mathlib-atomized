/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# q-expansions of functions on the upper half plane

We show that a function on the upper half plane with strict period `n` can be written as
`τ ↦ F (𝕢 n τ)` where `F` is analytic on the open unit disc, and `𝕢 n` is the parameter
`τ ↦ exp (2 * I * π * τ / n)`. As an application, we show that cusp forms decay exponentially to 0
as `im τ → ∞`.

We also define the `q`-expansion of a function `f` on the upper half plane, either as a power series
or as a `FormalMultilinearSeries`, and show that it converges to `f` if `f` is periodic, holomorphic
and bounded at infinity.

## Main definitions and results

* `UpperHalfPlane.cuspFunction`: for a function on the upper half plane with strict period `n`,
  this is the function `F` such that `f τ = F (exp (2 * π * I * τ / n))`, extended by a choice of
  limit at `0`.
* `UpperHalfPlane.differentiableAt_cuspFunction`: when `f` is periodic, holomorphic and bounded at
  infinity, its `cuspFunction` is differentiable on the open unit disc (including at `0`).
* `UpperHalfPlane.qExpansion`: the `q`-expansion of a function on the upper half plane (defined as
  the Taylor series of its `cuspFunction`), bundled as a `PowerSeries`.
* `UpperHalfPlane.hasSum_qExpansion`: the `q`-expansion evaluated at `𝕢 n τ` sums to `f τ`, for
  `τ` in the upper half plane.
* `ModularForm.qExpansionRingHom` defines the ring homomorphism from the graded ring of
  modular forms to power series given by taking `q`-expansions.
* `UpperHalfPlane.qExpansion_coeff_unique` shows that q-expansion coefficients are uniquely
  determined.
* There are also more specialized versions of some of these lemmas in the `ModularFormClass`
  namespace.
-/

@[expose] public noncomputable section

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup Metric Set
open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup Topology Manifold

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)

local notation "I∞" => comap Complex.im atTop
local notation "𝕢" => Periodic.qParam

namespace UpperHalfPlane

/-- The value of `f` at the cusp `∞` (or an arbitrary choice of value if this limit is not
well-defined). -/
/-
**UpperHalfPlane.valueAtInfty** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：valueAtInfty (f : ℍ -> Complex) : Complex
参数：f : ℍ -> Complex。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The value of `f` at the cusp `∞` (or an arbitrary choice of value if this limit 
is not
well-defined).
-/
def valueAtInfty (f : ℍ → ℂ) : ℂ := limUnder atImInfty f
/-
**UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：∀ {f : UpperHalfPlane → ℂ}, UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPl
ane.valueAtInfty f = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `UpperHalfPlane.instNeBotAtImInfty`：UpperHalfPlane.atImInfty.NeBot
-/
lemma IsZeroAtImInfty.valueAtInfty_eq_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    valueAtInfty f = 0 :=
  hf.limUnder_eq
/-
**UpperHalfPlane.qParam_tendsto_atImInfty** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPl
ane`。
形式化陈述：qParam_tendsto_atImInfty {h : Real} (hh : 0 < h) : Tendsto (fun τ : ℍ => 𝕢
 h τ) atImInfty (nhds 0)
参数：hh : 0 < h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Function.Periodic.qParam_tendsto`：qParam_tendsto (hh : 0 < h) : Tendsto 
(qParam h) I∞ (𝓝[!=] 0)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `UpperHalfPlane.tendsto_coe_atImInfty`：tendsto_coe_atImInfty : Tendsto Up
perHalfPlane.coe atImInfty (comap Complex.im atTop)
-/
lemma qParam_tendsto_atImInfty {h : ℝ} (hh : 0 < h) :
    Tendsto (fun τ : ℍ ↦ 𝕢 h τ) atImInfty (nhds 0) :=
  ((Periodic.qParam_tendsto hh).mono_right nhdsWithin_le_nhds).comp tendsto_coe_atImInfty

variable (h) in
/--
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / h))`, extended by a choice of
limit at `0`.
-/
/-
**UpperHalfPlane.cuspFunction** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：cuspFunction (f : ℍ -> Complex) : Complex -> Complex
参数：f : ℍ -> Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The analytic function `F` such that `f τ = F (exp (2 * π * I * τ / h))`, extende
d by a choice of
limit at `0`.
-/
def cuspFunction (f : ℍ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction h (f ∘ ofComplex)
/-
**UpperHalfPlane.eq_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：eq_cuspFunction {f : ℍ -> Complex} (τ : ℍ) (hh : h != 0) (hfper : Periodic
 (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ) = f τ
参数：τ : ℍ；hh : h != 0；hfper : Periodic (f ∘ ofComplex) h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用定理 `Function.Periodic.eq_cuspFunction`：eq_cuspFunction (hh : h != 0) (hf : P
eriodic f h) (z : Complex) : (cuspFunction h f) (𝕢 h z) = f z
-/
theorem eq_cuspFunction {f : ℍ → ℂ} (τ : ℍ) (hh : h ≠ 0)
    (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ) = f τ := by
  simpa [cuspFunction] using (Periodic.eq_cuspFunction hh hfper τ)
/-
**UpperHalfPlane.differentiableAt_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `UpperH
alfPlane`。
形式化陈述：differentiableAt_cuspFunction {f : ℍ -> Complex} (hh : 0 < h) (hfper : Per
iodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) {q : C
omplex} (hq : ‖q‖ < 1) : DifferentiableAt Complex (cuspFunction h f) q
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f；hq : ‖q‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Function.Periodic.differentiableAt_cuspFunction_zero`：differentiableAt_c
uspFunction_zero (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞, Diff
erentiableAt Complex f z) (h_bd : BoundedA…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `UpperHalfPlane.mdifferentiableAt_iff`：mdifferentiableAt_iff {f : ℍ -> Co
mplex} {τ : ℍ} : MDiffAt f τ ↔ DifferentiableAt Complex (f ∘ ofComplex) ↑τ
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用引理 `UpperHalfPlane.tendsto_comap_im_ofComplex`：tendsto_comap_im_ofComplex : 
Tendsto ofComplex (comap Complex.im atTop) atImInfty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Periodic.differentiableAt_cuspFunction`：differentiableAt_cuspFu
nction (hh : h != 0) (hf : Periodic f h) {z : Complex} (hol_z : DifferentiableAt
 Complex f z) : DifferentiableAt Comp…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Function.Periodic.qParam_right_inv`：qParam_right_inv (hh : h != 0) {q : 
Complex} (hq : q != 0) : 𝕢 h (invQParam h q) = q
· 使用定理 `Function.Periodic.im_invQParam_pos_of_norm_lt_one`：Function.Periodic.im_
invQParam_pos_of_norm_lt_one {h : Real} (hh : 0 < h) {q : Complex} (hq : ‖q‖ < 1
) (hq_ne : q != 0) : 0 < im (Periodic.i…
-/
theorem differentiableAt_cuspFunction {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    {q : ℂ} (hq : ‖q‖ < 1) : DifferentiableAt ℂ (cuspFunction h f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact hfper.differentiableAt_cuspFunction_zero hh
      (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0))
        (fun z hz ↦ UpperHalfPlane.mdifferentiableAt_iff.mp (hfhol ⟨z, hz⟩)))
      (hfbdd.comp_tendsto tendsto_comap_im_ofComplex)
  · exact Periodic.qParam_right_inv hh.ne' hq' ▸
      hfper.differentiableAt_cuspFunction hh.ne' <| UpperHalfPlane.mdifferentiableAt_iff.mp <|
        hfhol ⟨_, Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq'⟩
/-
**UpperHalfPlane.differentiableOn_cuspFunction_ball** 是 Mathlib 中的一个引理，位于命名空间 `U
pperHalfPlane`。
形式化陈述：differentiableOn_cuspFunction_ball {f : ℍ -> Complex} (hh : 0 < h) (hfper 
: Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
 DifferentiableOn Complex (cuspFunction h f) (Metric.ball 0 1)
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `UpperHalfPlane.differentiableAt_cuspFunction`：differentiableAt_cuspFunct
ion {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol 
: MDiff f) (hfbdd : IsBoundedAtImI…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
-/
lemma differentiableOn_cuspFunction_ball {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    DifferentiableOn ℂ (cuspFunction h f) (Metric.ball 0 1) :=
  fun _ hz ↦ (differentiableAt_cuspFunction hh hfper hfhol hfbdd <| mem_ball_zero_iff.mp hz)
    |>.differentiableWithinAt
/-
**UpperHalfPlane.analyticAt_cuspFunction_zero** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：analyticAt_cuspFunction_zero {f : ℍ -> Complex} (hh : 0 < h) (hfper : Peri
odic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) : Analy
ticAt Complex (cuspFunction h f) 0
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticAt`：∀ {E : Type u} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}   {z : ℂ}
, DifferentiableO…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `UpperHalfPlane.differentiableOn_cuspFunction_ball`：differentiableOn_cusp
Function_ball {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) 
h) (hfhol : MDiff f) (hfbdd : IsBounded…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ball_zero_eq`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (r : ℝ), Me
tric.ball 0 r = {x | ‖x‖ < r}
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma analyticAt_cuspFunction_zero {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    AnalyticAt ℂ (cuspFunction h f) 0 :=
  DifferentiableOn.analyticAt (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
    (by simpa [ball_zero_eq] using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
/-
**UpperHalfPlane.cuspFunction_apply_zero** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：cuspFunction_apply_zero {f : ℍ -> Complex} (hh : 0 < h) (hfanalytic : Anal
yticAt Complex (cuspFunction h f) 0) (hfper : Periodic (f ∘ UpperHalfPlane.ofCom
plex) h) : cuspFunction h f 0 = valueAtInfty f
参数：hh : 0 < h；hfanalytic : AnalyticAt Complex (cuspFunction h f) 0；hfper : Perio
dic (f ∘ UpperHalfPlane.ofComplex) h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `UpperHalfPlane.instNeBotAtImInfty`：UpperHalfPlane.atImInfty.NeBot
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.eq_cuspFunction`：eq_cuspFunction {f : ℍ -> Complex} (τ : 
ℍ) (hh : h != 0) (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ)
 = f τ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用引理 `UpperHalfPlane.qParam_tendsto_atImInfty`：qParam_tendsto_atImInfty {h : R
eal} (hh : 0 < h) : Tendsto (fun τ : ℍ => 𝕢 h τ) atImInfty (nhds 0)
-/
lemma cuspFunction_apply_zero {f : ℍ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) : cuspFunction h f 0 = valueAtInfty f := by
  refine (Tendsto.limUnder_eq ?_).symm
  have : (cuspFunction h f ∘ fun τ ↦ 𝕢 h τ : ℍ → ℂ) = f := by
    funext τ
    simpa using eq_cuspFunction τ hh.ne' hfper
  simpa [this] using hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)

end UpperHalfPlane

namespace SlashInvariantFormClass

/-
**SlashInvariantFormClass.periodic_comp_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `Sla
shInvariantFormClass`。
形式化陈述：periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.stric
tPeriods) : Periodic (f ∘ ofComplex) h
参数：hΓ : h in Γ.strictPeriods。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UpperHalfPlane.ext`：∀ {x y : UpperHalfPlane}, ↑x = ↑y → x = y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SlashInvariantForm.vAdd_apply_of_mem_strictPeriods`：vAdd_apply_of_mem_st
rictPeriods {Γ : Subgroup (GL (Fin 2) Real)} {k : Int} {F : Type*} [FunLike F ℍ 
Complex] [SlashInvariantFormClass F Γ k]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_nonpos`：ofComplex_apply_of_im_nonpo
s {w : Complex} (hw : w.im <= 0) : ofComplex w = Classical.choice inferInstance
-/
theorem periodic_comp_ofComplex [SlashInvariantFormClass F Γ k] (hΓ : h ∈ Γ.strictPeriods) :
    Periodic (f ∘ ofComplex) h := by
  intro w
  by_cases! hw : 0 < im w
  · have : 0 < im (w + h) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    convert! SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f ⟨w, hw⟩ hΓ using 2
    ext
    simp [add_comm]
  · have : im (w + h) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]
/-
**SlashInvariantFormClass.eq_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvari
antFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [SlashInvariantFormClass F Γ k] (τ : UpperHal
fPlane),   h ∈ Γ.strictPeriods → h ≠ 0 → UpperHalfPlane.cuspFunction h (⇑f) (Fun
ction.Periodic.qParam h ↑τ) = f τ
参数：GL (Fin 2) ℝ；f : F；τ : UpperHalfPlane；⇑f；Function.Periodic.qParam h ↑τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.eq_cuspFunction`：eq_cuspFunction {f : ℍ -> Complex} (τ : 
ℍ) (hh : h != 0) (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ)
 = f τ
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
-/
protected theorem eq_cuspFunction [SlashInvariantFormClass F Γ k] (τ : ℍ)
    (hΓ : h ∈ Γ.strictPeriods) (hh : h ≠ 0) : cuspFunction h f (𝕢 h τ) = f τ :=
  eq_cuspFunction τ hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)

end SlashInvariantFormClass

open SlashInvariantFormClass

namespace ModularFormClass

@[deprecated ModularFormClass.bdd_at_infty (since := "2026-04-19")]
/-
**ModularFormClass.bounded_at_infty_comp_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dularFormClass`。
形式化陈述：bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] (hi : IsCusp OneP
oint.infty Γ) : BoundedAtFilter I∞ (f ∘ ofComplex)
参数：hi : IsCusp OnePoint.infty Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `OnePoint.isBoundedAt_infty_iff`：isBoundedAt_infty_iff : IsBoundedAt ∞ f 
k ↔ IsBoundedAtImInfty f
· 使用定理 `ModularFormClass.bdd_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup 
(GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : 
ModularFormClass F …
· 使用引理 `UpperHalfPlane.tendsto_comap_im_ofComplex`：tendsto_comap_im_ofComplex : 
Tendsto ofComplex (comap Complex.im atTop) atImInfty
-/
theorem bounded_at_infty_comp_ofComplex [ModularFormClass F Γ k] (hi : IsCusp OnePoint.infty Γ) :
    BoundedAtFilter I∞ (f ∘ ofComplex) :=
  (OnePoint.isBoundedAt_infty_iff.mp (bdd_at_cusps f hi)).comp_tendsto tendsto_comap_im_ofComplex
/-
**ModularFormClass.differentiableAt_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `Modu
larFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [ModularFormClass F Γ k],   0 < h → h ∈ Γ.str
ictPeriods → ∀ {q : ℂ}, ‖q‖ < 1 → DifferentiableAt ℂ (UpperHalfPlane.cuspFunctio
n h ⇑f) q
参数：GL (Fin 2) ℝ；f : F；UpperHalfPlane.cuspFunction h ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用定理 `UpperHalfPlane.differentiableAt_cuspFunction`：differentiableAt_cuspFunct
ion {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol 
: MDiff f) (hfbdd : IsBoundedAtImI…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
-/
protected theorem differentiableAt_cuspFunction [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspFunction h f) q :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  differentiableAt_cuspFunction hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) hq
/-
**ModularFormClass.analyticAt_cuspFunction_zero** 是 Mathlib 中的一个定理，位于命名空间 `Modul
arFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [ModularFormClass F Γ k], 0 < h → h ∈ Γ.stric
tPeriods → AnalyticAt ℂ (UpperHalfPlane.cuspFunction h ⇑f) 0
参数：GL (Fin 2) ℝ；f : F；UpperHalfPlane.cuspFunction h ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用引理 `UpperHalfPlane.analyticAt_cuspFunction_zero`：analyticAt_cuspFunction_zer
o {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : 
MDiff f) (hfbdd : IsBoundedAtImIn…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
-/
protected lemma analyticAt_cuspFunction_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : AnalyticAt ℂ (cuspFunction h f) 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  analyticAt_cuspFunction_zero hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

end ModularFormClass

namespace UpperHalfPlane

variable (h) in
/-- The `q`-expansion of a function on the upper half plane with strict period `h`, bundled as a
`PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunction` at `q = 0`,
where `q = exp(2πiτ/h)` is the local parameter at the cusp. -/
/-
**UpperHalfPlane.qExpansion** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：qExpansion (f : ℍ -> Complex) : PowerSeries Complex
参数：f : ℍ -> Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `q`-expansion of a function on the upper half plane with strict period `h`, 
bundled as a
`PowerSeries`. The `m`-th coefficient is the Taylor coefficient of the `cuspFunc
tion` at `q = 0`,
where `q = exp(2πiτ/h)` is the local parameter at the cusp.
-/
def qExpansion (f : ℍ → ℂ) : PowerSeries ℂ :=
  .mk fun m ↦ (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0
/-
**UpperHalfPlane.qExpansion_coeff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：qExpansion_coeff (f : ℍ -> Complex) (m : Nat) : (qExpansion h f).coeff m =
 (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0
参数：f : ℍ -> Complex；m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansion_coeff (f : ℍ → ℂ) (m : ℕ) :
    (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunction h f) 0 := by
  simp [qExpansion]
/-
**UpperHalfPlane.qExpansion_coeff_zero** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：qExpansion_coeff_zero {f : ℍ -> Complex} (hh : 0 < h) (hfanalytic : Analyt
icAt Complex (cuspFunction h f) 0) (hfper : Periodic (f ∘ UpperHalfPlane.ofCompl
ex) h) : (qExpansion h f).coeff 0 = valueAtInfty f
参数：hh : 0 < h；hfanalytic : AnalyticAt Complex (cuspFunction h f) 0；hfper : Perio
dic (f ∘ UpperHalfPlane.ofComplex) h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用引理 `UpperHalfPlane.cuspFunction_apply_zero`：cuspFunction_apply_zero {f : ℍ -
> Complex} (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (
hfper : Periodic (f ∘ UpperH…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansion_coeff_zero {f : ℍ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hfper : Periodic (f ∘ UpperHalfPlane.ofComplex) h) :
    (qExpansion h f).coeff 0 = valueAtInfty f := by
  simp [qExpansion_coeff, cuspFunction_apply_zero hh hfanalytic hfper]
/-
**UpperHalfPlane.hasSum_qExpansion_of_norm_lt** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：hasSum_qExpansion_of_norm_lt {f : ℍ -> Complex} (hh : 0 < h) (hfper : Peri
odic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) {q : Co
mplex} (hq : ‖q‖ < 1) : HasSum (fun m : Nat => (qExpansion h f).coeff m • q ^ m)
 (cuspFunction h f q)
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f；hq : ‖q‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Complex.hasSum_taylorSeries_on_ball`：hasSum_taylorSeries_on_ball : HasSu
m (fun n : Nat => (n ! : Complex)⁻¹ • (z - c) ^ n • iteratedDeriv n f c) (f z)
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `UpperHalfPlane.differentiableOn_cuspFunction_ball`：differentiableOn_cusp
Function_ball {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) 
h) (hfhol : MDiff f) (hfbdd : IsBounded…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
-/
lemma hasSum_qExpansion_of_norm_lt {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • q ^ m) (cuspFunction h f q) := by
  convert!
    hasSum_taylorSeries_on_ball (differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd)
      (by simpa using hq) using
    2 with m
  grind [qExpansion_coeff, sub_zero, smul_eq_mul]
/-
**UpperHalfPlane.hasSum_qExpansion** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：hasSum_qExpansion {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ o
fComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (τ : ℍ) : HasSum (
fun m : Nat => (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ)
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f；τ : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.norm_qParam_lt_one`：norm_qParam_lt_one (hh : 0 < h) {z
 : Complex} (hz : 0 < im z) : ‖𝕢 h z‖ < 1
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.eq_cuspFunction`：eq_cuspFunction {f : ℍ -> Complex} (τ : 
ℍ) (hh : h != 0) (hfper : Periodic (f ∘ ofComplex) h) : cuspFunction h f (𝕢 h τ)
 = f τ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `UpperHalfPlane.hasSum_qExpansion_of_norm_lt`：hasSum_qExpansion_of_norm_l
t {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : 
MDiff f) (hfbdd : IsBoundedAtImIn…
-/
lemma hasSum_qExpansion {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (τ : ℍ) : HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m • 𝕢 h τ ^ m) (f τ) := by
  have : ‖𝕢 h τ‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  simpa [eq_cuspFunction τ hh.ne' hfper] using
    hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd this

variable (h) in
/--
The `q`-expansion of a function on the upper half plane, bundled as a `FormalMultilinearSeries`.

TODO: Maybe get rid of this and instead define a general API for converting `PowerSeries` to
`FormalMultilinearSeries`.
-/
/-
**UpperHalfPlane.qExpansionFormalMultilinearSeries** 是 Mathlib 中的一个定义，位于命名空间 `Up
perHalfPlane`。
形式化陈述：qExpansionFormalMultilinearSeries : FormalMultilinearSeries Complex Comple
x Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `q`-expansion of a function on the upper half plane, bundled as a `FormalMul
tilinearSeries`.

TODO: Maybe get rid of this and instead define a general API for converting `Pow
erSeries` to
`FormalMultilinearSeries`.
-/
def qExpansionFormalMultilinearSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ fun m ↦ (qExpansion h f).coeff m

@[simp]
/-
**UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff** 是 Mathlib 中的一个引理，位于命名
空间 `UpperHalfPlane`。
形式化陈述：qExpansionFormalMultilinearSeries_coeff (m : Nat) : (qExpansionFormalMulti
linearSeries h f).coeff m = (qExpansion h f).coeff m
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansionFormalMultilinearSeries_coeff (m : ℕ) :
    (qExpansionFormalMultilinearSeries h f).coeff m = (qExpansion h f).coeff m := by
  simp [qExpansionFormalMultilinearSeries, FormalMultilinearSeries.coeff_ofScalars]
/-
**UpperHalfPlane.qExpansionFormalMultilinearSeries_apply_norm** 是 Mathlib 中的一个引理
，位于命名空间 `UpperHalfPlane`。
形式化陈述：qExpansionFormalMultilinearSeries_apply_norm (m : Nat) : ‖qExpansionFormal
MultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖
参数：m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `UpperHalfPlane.qExpansionFormalMultilinearSeries.eq_1`：∀ {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] (h : ℝ) (f : F),   UpperHalfPlane.qExpansion
FormalMultilinearSeries h f =     FormalMul…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `FormalMultilinearSeries.norm_apply_eq_norm_coef`：norm_apply_eq_norm_coef
 : ‖p n‖ = ‖coeff p n‖
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansionFormalMultilinearSeries_apply_norm (m : ℕ) :
    ‖qExpansionFormalMultilinearSeries h f m‖ = ‖(qExpansion h f).coeff m‖ := by
  rw [qExpansionFormalMultilinearSeries,
    ← (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin m) ℂ).symm.norm_map]
  simp
/-
**UpperHalfPlane.qExpansionFormalMultilinearSeries_radius** 是 Mathlib 中的一个引理，位于命
名空间 `UpperHalfPlane`。
形式化陈述：qExpansionFormalMultilinearSeries_radius (hh : 0 < h) (hfper : Periodic (f
 ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) : 1 <= (qExpan
sionFormalMultilinearSeries h f).radius
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_lt_imp_le_of_dense`：∀ {α : Type u_2} [inst : LinearOrder α]
 [DenselyOrdered α] {a₁ a₂ : α}, (∀ a < a₂, a ≤ a₁) → a₂ ≤ a₁
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `FormalMultilinearSeries.le_radius_of_summable`：le_radius_of_summable (h 
: Summable fun n => ‖p n‖ * (r : Real) ^ n) : ↑r <= p.radius
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `UpperHalfPlane.qExpansionFormalMultilinearSeries_apply_norm`：qExpansionF
ormalMultilinearSeries_apply_norm (m : Nat) : ‖qExpansionFormalMultilinearSeries
 h f m‖ = ‖(qExpansion h f).coeff m‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用引理 `UpperHalfPlane.hasSum_qExpansion_of_norm_lt`：hasSum_qExpansion_of_norm_l
t {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : 
MDiff f) (hfbdd : IsBoundedAtImIn…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
-/
lemma qExpansionFormalMultilinearSeries_radius (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    1 ≤ (qExpansionFormalMultilinearSeries h f).radius := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  lift r to NNReal using hr.ne_top
  apply FormalMultilinearSeries.le_radius_of_summable
  simp only [qExpansionFormalMultilinearSeries_apply_norm]
  rw [← r.abs_eq]
  simp_rw [← Real.norm_eq_abs, ← Complex.norm_real, ← norm_pow, ← norm_mul]
  exact (UpperHalfPlane.hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (by simpa using hr)).summable.norm
/-
**UpperHalfPlane.hasSum_cuspFunction_of_hasSum_punctured** 是 Mathlib 中的一个引理，位于命名
空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasSum_cuspFunction_of_hasSum_punctured {f : ℍ → ℂ} (hh : 0 < h) {c : ℕ → ℂ}
    (hf : ∀ (τ : ℍ), HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) {q : ℂ} (hq : ‖q‖ < 1)
    (hq1 : q ≠ 0) : HasSum (fun m ↦ c m • q ^ m) (cuspFunction h f q) := by
  have h1 := Periodic.im_invQParam_pos_of_norm_lt_one hh hq hq1
  let τ : ℍ := ⟨Periodic.invQParam h q, h1⟩
  have h2 := (Periodic.cuspFunction_eq_of_nonzero h (f ∘ ofComplex) hq1)
  have : cuspFunction h f q = f τ := by simpa [UpperHalfPlane.ofComplex_apply_of_im_pos h1]
    using! h2
  grind [hf τ, Periodic.qParam_right_inv]
/-
**UpperHalfPlane.hasFPowerSeriesOnBall_update** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasFPowerSeriesOnBall_update {f : ℍ → ℂ} (hh : 0 < h) {c : ℕ → ℂ}
    (hf : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (c m) • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    rcases eq_or_ne r 0 with rfl | hr'
    · simp
    · lift r to NNReal using hr.ne_top
      let : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
      apply FormalMultilinearSeries.le_radius_of_summable
      simpa [smul_eq_mul, norm_mul, mul_comm, mul_left_comm, mul_assoc] using
        (hasSum_cuspFunction_of_hasSum_punctured hh hf (q := r) (by simpa using hr)
          (mod_cast hr')).summable.norm
  · simp
  · intro y hy
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with rfl | hy'
    · simpa +contextual [zero_pow_eq] using hasSum_ite_eq 0 (c 0)
    · simpa [update_of_ne hy', mul_comm]
        using hasSum_cuspFunction_of_hasSum_punctured hh hf hy hy'

/-- A function on the upper half plane that is given everywhere by a convergent `q`-expansion with
non-negative exponents, `f τ = ∑' m, c m * 𝕢 h τ ^ m`, is bounded at `i∞`. This is a converse to
`hasSum_qExpansion`: there, boundedness is a hypothesis used to produce the `q`-expansion, while
here convergence of the `q`-expansion is enough to deduce boundedness. -/
/-
**UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion** 是 Mathlib 中的一个定理，位于命名
空间 `UpperHalfPlane`。
形式化陈述：isBoundedAtImInfty_of_hasSum_qExpansion {f : ℍ -> Complex} {c : Nat -> Com
plex} (hh : 0 < h) (hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) 
: IsBoundedAtImInfty f
参数：hh : 0 < h；hf : forall τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用引理 `Function.Periodic.qParam_ne_zero`：qParam_ne_zero (z : Complex) : 𝕢 h z !
= 0
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.QExpansion.0.UpperHalfPlane.h
asSum_cuspFunction_of_hasSum_punctured`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   0 
< h →     ∀ {c : ℕ → ℂ},       (∀ (τ : UpperHalfPlane), HasSum (fun m => c m • F
unction.Periodic.qPa…
· 使用定理 `Function.Periodic.norm_qParam_lt_one`：norm_qParam_lt_one (hh : 0 < h) {z
 : Complex} (hz : 0 < im z) : ‖𝕢 h z‖ < 1
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.QExpansion.0.UpperHalfPlane.h
asFPowerSeriesOnBall_update`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   0 < h →     ∀
 {c : ℕ → ℂ},       (∀ (τ : UpperHalfPlane), HasSum (fun m => c m • Function.Per
iodic.qPa…
· 使用引理 `UpperHalfPlane.qParam_tendsto_atImInfty`：qParam_tendsto_atImInfty {h : R
eal} (hh : 0 < h) : Tendsto (fun τ : ℍ => 𝕢 h τ) atImInfty (nhds 0)
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
A function on the upper half plane that is given everywhere by a convergent `q`-
expansion with
non-negative exponents, `f τ = ∑' m, c m * 𝕢 h τ ^ m`, is bounded at `i∞`. This 
is a converse to
`hasSum_qExpansion`: there, boundedness is a hypothesis used to produce the `q`-
expansion, while
here convergence of the `q`-expansion is enough to deduce boundedness.
-/
theorem isBoundedAtImInfty_of_hasSum_qExpansion {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) : IsBoundedAtImInfty f := by
  have hfeq : f = fun τ : ℍ ↦ update (cuspFunction h f) 0 (c 0) (𝕢 h τ) := by
    funext τ
    rw [update_of_ne (Periodic.qParam_ne_zero _)]
    exact (hf τ).unique (hasSum_cuspFunction_of_hasSum_punctured hh hf
      (Periodic.norm_qParam_lt_one hh τ.im_pos) (exp_ne_zero _))
  have htend : Tendsto f atImInfty (𝓝 (c 0)) := by
    rw [hfeq]
    simpa [update_self, Function.comp_def] using
      (hasFPowerSeriesOnBall_update hh hf).hasFPowerSeriesAt.continuousAt.tendsto.comp
        (qParam_tendsto_atImInfty hh)
  -- `IsBoundedAtImInfty f = BoundedAtFilter atImInfty f = (f =O[atImInfty] 1)` by definition.
  exact htend.isBigO_one ℝ
/-
**UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction** 是 Mathlib 中的一个引理，位于命名空间 `U
pperHalfPlane`。
形式化陈述：hasFPowerSeriesOnBall_cuspFunction {f : ℍ -> Complex} {c : Nat -> Complex}
 (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (hf : foral
l τ : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)) : HasFPowerSeriesOnBall (cuspF
unction h f) (.ofScalars Complex c) 0 1
参数：hh : 0 < h；hfanalytic : AnalyticAt Complex (cuspFunction h f) 0；hf : forall τ
 : ℍ, HasSum (fun m => c m • 𝕢 h τ ^ m) (f τ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.QExpansion.0.UpperHalfPlane.h
asFPowerSeriesOnBall_update`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   0 < h →     ∀
 {c : ℕ → ℂ},       (∀ (τ : UpperHalfPlane), HasSum (fun m => c m • Function.Per
iodic.qPa…
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`：ContinuousAt.eve
ntuallyEq_nhds_iff_eventuallyEq_nhdsNE [T2Space Y] {x : X} {f g : X -> Y} (hf : 
ContinuousAt f x) (hg : ContinuousAt g x) [(…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.update_eq_self_iff`：∀ {α : Sort u} {β : α → Sort v} [inst : Dec
idableEq α] {f : (a : α) → β a} {a : α} {b : β a},   Function.update f a b = f ↔
 b = f a
-/
lemma hasFPowerSeriesOnBall_cuspFunction {f : ℍ → ℂ} {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (.ofScalars ℂ c) 0 1 := by
  -- previous lemma gives result after updating at 0
  have H1 : HasFPowerSeriesOnBall (update (cuspFunction h f) 0 (c 0)) (.ofScalars ℂ c) 0 1 :=
    hasFPowerSeriesOnBall_update hh hf
  -- now just need to check values at 0 match
  -- use continuity of both functions & we know it everywhere else
  have H2 : c 0 = cuspFunction h f 0 := by
    have L1 := H1.hasFPowerSeriesAt.continuousAt
    have L2 := hfanalytic.continuousAt
    have := (L1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE L2).mp <|
      by filter_upwards [self_mem_nhdsWithin] with a ha using update_of_ne ha ..
    simpa [update_self] using this.eq_of_nhds
  rwa [update_eq_self_iff.mpr H2] at H1

/-- The `q`-expansion coefficient can be expressed as a `circleIntegral` for any radius `0 < R < 1`.
-/
/-
**UpperHalfPlane.qExpansion_coeff_eq_circleIntegral** 是 Mathlib 中的一个引理，位于命名空间 `U
pperHalfPlane`。
形式化陈述：qExpansion_coeff_eq_circleIntegral {f : ℍ -> Complex} (hh : 0 < h) (hfper 
: Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (
n : Nat) {R : Real} (hR : 0 < R) (hR' : R < 1) : (qExpansion h f).coeff n = ((2 
* π * Complex.I)⁻¹ * ∮ (z : Complex) in C(0, R), cuspFunction h f z / z ^ (n + 1
))
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f；n : Nat；hR : 0 < R；hR' : R < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`：∀ {E : Type
 u} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {
R : ℝ} {f : ℂ → E} {c : ℂ},   0 < R →     ∀ (n : …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用引理 `UpperHalfPlane.differentiableOn_cuspFunction_ball`：differentiableOn_cusp
Function_ball {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) 
h) (hfhol : MDiff f) (hfbdd : IsBounded…
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Complex.two_pi_I_ne_zero`：two_pi_I_ne_zero : (2 * π * I : Complex) != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_div_mul_eq_div`：one_div_mul_eq_div : 1 / a * b = b / a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `q`-expansion coefficient can be expressed as a `circleIntegral` for any rad
ius `0 < R < 1`.
-/
lemma qExpansion_coeff_eq_circleIntegral {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) {R : ℝ} (hR : 0 < R) (hR' : R < 1) : (qExpansion h f).coeff n =
      ((2 * π * Complex.I)⁻¹ * ∮ (z : ℂ) in C(0, R), cuspFunction h f z / z ^ (n + 1)) := by
  have := ((differentiableOn_cuspFunction_ball hh hfper hfhol hfbdd).mono
    (Metric.closedBall_subset_ball hR')).circleIntegral_one_div_sub_center_pow_smul hR n
  rw [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, ← div_eq_iff two_pi_I_ne_zero] at this
  simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div,
    div_eq_inv_mul]

/--
If `h` is a positive strict period of `f`, then the `q`-expansion coefficient can be expressed
as an integral along a horizontal line in the upper half-plane from `t * I` to `h + t * I`, for
any `0 < t`.
-/
/-
**UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral** 是 Mathlib 中的一个引理，位于命名空间 
`UpperHalfPlane`。
形式化陈述：qExpansion_coeff_eq_intervalIntegral {f : ℍ -> Complex} (hh : 0 < h) (hfpe
r : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
 (n : Nat) {t : Real} (ht : 0 < t) : (qExpansion h f).coeff n = 1 / h * ∫ u in 0
..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f；n : Nat；ht : 0 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.exp_lt_one_iff`：exp_lt_one_iff {x : Real} : exp x < 1 ↔ x < 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用引理 `UpperHalfPlane.qExpansion_coeff_eq_circleIntegral`：qExpansion_coeff_eq_c
ircleIntegral {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) 
h) (hfhol : MDiff f) (hfbdd : IsBounded…
· 使用定理 `circleIntegral.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [ins
t_1 : NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ),   circleIntegral f c R = ∫ (
θ : ℝ) in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
If `h` is a positive strict period of `f`, then the `q`-expansion coefficient ca
n be expressed
as an integral along a horizontal line in the upper half-plane from `t * I` to `
h + t * I`, for
any `0 < t`.
-/
lemma qExpansion_coeff_eq_intervalIntegral {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) {t : ℝ} (ht : 0 < t) : (qExpansion h f).coeff n =
      1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩ := by
  -- We use a circle integral in the `q`-domain of radius `R = exp (-2 * π * t / h)`.
  let R := Real.exp (-2 * π * t / h)
  have hR0 : 0 < R := Real.exp_pos _
  have hR1 : R < 1 := Real.exp_lt_one_iff.2 <| by simpa [neg_div] using div_pos (by positivity) hh
  -- First apply `qExpansion_coeff_eq_circleIntegral` and rescale from `0 .. 2 * π` to `0 .. h`.
  rw [qExpansion_coeff_eq_circleIntegral hh hfper hfhol hfbdd n hR0 hR1, circleIntegral,
    show 2 * π = h * (2 * π / h) by field_simp]
  conv => enter [1, 2, 2]; rw [show 0 = 0 * (2 * π / h) by simp]
  simp_rw [← intervalIntegral.smul_integral_comp_mul_right, real_smul, ← mul_assoc,
    ← intervalIntegral.integral_const_mul]
  -- Compare the integrands
  congr 1 with u
  let τ : ℍ := ⟨u + t * I, by simpa using ht⟩
  have : circleMap 0 R (u * (2 * π / h)) = 𝕢 h τ := by
    simp only [circleMap, ofReal_exp, ← exp_add, zero_add, τ, R]
    congr 1
    push_cast
    have := I_sq
    grind
  -- now just complex exponential arithmetic to finish
  simp_rw [deriv_circleMap, this, show ↑I = Complex.I by rfl, show u + t * Complex.I = τ by rfl,
    show ⟨↑τ, τ.2⟩ = τ by rfl, eq_cuspFunction _ hh.ne' hfper, smul_eq_mul, pow_succ]
  field_simp [(show 𝕢 h τ ≠ 0 from Complex.exp_ne_zero _), Real.pi_ne_zero, NeZero.ne]
  push_cast
  ring
/-
**UpperHalfPlane.exp_decay_sub_atImInfty** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：exp_decay_sub_atImInfty {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic 
(f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) : (fun τ => 
f τ - valueAtInfty f) =O[atImInfty] fun τ => Real.exp (-2 * π * τ.im / h)
参数：hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : MDiff f；hfbdd : IsBound
edAtImInfty f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用引理 `UpperHalfPlane.tendsto_comap_im_ofComplex`：tendsto_comap_im_ofComplex : 
Tendsto ofComplex (comap Complex.im atTop) atImInfty
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用引理 `UpperHalfPlane.cuspFunction_apply_zero`：cuspFunction_apply_zero {f : ℍ -
> Complex} (hh : 0 < h) (hfanalytic : AnalyticAt Complex (cuspFunction h f) 0) (
hfper : Periodic (f ∘ UpperH…
· 使用引理 `UpperHalfPlane.analyticAt_cuspFunction_zero`：analyticAt_cuspFunction_zer
o {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : 
MDiff f) (hfbdd : IsBoundedAtImIn…
· 使用定理 `Function.Periodic.exp_decay_sub_of_bounded_at_inf`：exp_decay_sub_of_boun
ded_at_inf (hh : 0 < h) (hf : Periodic f h) (h_hol : forallᶠ z in I∞, Differenti
ableAt Complex f z) (h_bd : BoundedAtFi…
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `UpperHalfPlane.mdifferentiableAt_iff`：mdifferentiableAt_iff {f : ℍ -> Co
mplex} {τ : ℍ} : MDiffAt f τ ↔ DifferentiableAt Complex (f ∘ ofComplex) ↑τ
· 使用引理 `UpperHalfPlane.tendsto_coe_atImInfty`：tendsto_coe_atImInfty : Tendsto Up
perHalfPlane.coe atImInfty (comap Complex.im atTop)
-/
theorem exp_decay_sub_atImInfty {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    (fun τ ↦ f τ - valueAtInfty f) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  have := hfbdd.comp_tendsto tendsto_comap_im_ofComplex
  convert!
    (hfper.exp_decay_sub_of_bounded_at_inf hh
          (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) fun z hz ↦ by
            simpa using (UpperHalfPlane.mdifferentiableAt_iff.mp <| hfhol ⟨z, hz⟩))
          this).comp_tendsto
      tendsto_coe_atImInfty
  simpa [cuspFunction] using
    (cuspFunction_apply_zero hh (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd) hfper).symm

namespace IsZeroAtImInfty

variable {f}

/-
**UpperHalfPlane.IsZeroAtImInfty.zero_at_infty_comp_ofComplex** 是 Mathlib 中的一个引理
，位于命名空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：zero_at_infty_comp_ofComplex {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) :
 ZeroAtFilter I∞ (f ∘ ofComplex)
参数：hf : IsZeroAtImInfty f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `UpperHalfPlane.tendsto_comap_im_ofComplex`：tendsto_comap_im_ofComplex : 
Tendsto ofComplex (comap Complex.im atTop) atImInfty
-/
lemma zero_at_infty_comp_ofComplex {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  hf.comp tendsto_comap_im_ofComplex
/-
**UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero** 是 Mathlib 中的一个定理，位于命名
空间 `UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：cuspFunction_apply_zero {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 
0 < h) : cuspFunction h f 0 = 0
参数：hf : IsZeroAtImInfty f；hh : 0 < h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Periodic.cuspFunction_zero_of_zero_at_inf`：cuspFunction_zero_of
_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) : cuspFunction h f 0 = 0
· 使用引理 `UpperHalfPlane.IsZeroAtImInfty.zero_at_infty_comp_ofComplex`：zero_at_inf
ty_comp_ofComplex {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) : ZeroAtFilter I∞ 
(f ∘ ofComplex)
-/
theorem cuspFunction_apply_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) (hh : 0 < h) :
    cuspFunction h f 0 = 0 :=
  Periodic.cuspFunction_zero_of_zero_at_inf hh hf.zero_at_infty_comp_ofComplex
/-
**UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty** 是 Mathlib 中的一个定理，位于命名空间 `
UpperHalfPlane.IsZeroAtImInfty`。
形式化陈述：exp_decay_atImInfty {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < 
h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtIm
Infty f) : f =O[atImInfty] fun τ => Real.exp (-2 * π * τ.im / h)
参数：hf : IsZeroAtImInfty f；hh : 0 < h；hfper : Periodic (f ∘ ofComplex) h；hfhol : 
MDiff f；hfbdd : IsBoundedAtImInfty f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero`：∀ {f : UpperHalfPla
ne → ℂ}, UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.valueAtInfty f = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `UpperHalfPlane.exp_decay_sub_atImInfty`：exp_decay_sub_atImInfty {f : ℍ -
> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (
hfbdd : IsBoundedAtImInfty f…
-/
theorem exp_decay_atImInfty {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty hh hfper hfhol hfbdd

end UpperHalfPlane.IsZeroAtImInfty

namespace ModularFormClass

/-
**ModularFormClass.qExpansion_coeff_eq_intervalIntegral** 是 Mathlib 中的一个定理，位于命名空
间 `ModularFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [ModularFormClass F Γ k],   0 < h →     h ∈ Γ
.strictPeriods →       ∀ (n : ℕ) {t : ℝ} (ht : 0 < t),         (PowerSeries.coef
f n) (UpperHalfPlane.qExpansion h ⇑f) =           1 / ↑h *             ∫ (u : ℝ)
 in 0..h,               1 / Function.Periodic.qParam h (↑u + ↑t * Complex.I) ^ n
 *                 f { coe := ↑u + ↑t * Complex.I, coe_im_pos := ⋯ }
参数：GL (Fin 2) ℝ；f : F；n : ℕ；ht : 0 < t；PowerSeries.coeff n；UpperHalfPlane.qExpan
sion h ⇑f；u : ℝ；↑u + ↑t * Complex.I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用引理 `UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral`：qExpansion_coeff_eq
_intervalIntegral {f : ℍ -> Complex} (hh : 0 < h) (hfper : Periodic (f ∘ ofCompl
ex) h) (hfhol : MDiff f) (hfbdd : IsBound…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
-/
protected lemma qExpansion_coeff_eq_intervalIntegral [ModularFormClass F Γ k]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (qExpansion h f).coeff n =
      1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f ⟨u + t * I, by simpa using ht⟩ :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  qExpansion_coeff_eq_intervalIntegral hh (periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) n ht

/-- Version of `exp_decay_sub_atImInfty` stating a less precise result but easier to apply in
practice (not specifying the growth rate precisely).

Note that the `Fact` hypothesis is automatically synthesized for arithmetic subgroups.
The discreteness hypothesis may be unnecessary, but it is satisfied in the cases of interest. -/
/-
**ModularFormClass.exp_decay_sub_atImInfty'** 是 Mathlib 中的一个定理，位于命名空间 `ModularFo
rmClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} (f : F)   [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [Disc
reteTopology ↥Γ] [Fact (IsCusp OnePoint.infty Γ)],   ∃ c > 0, (fun τ => f τ - Up
perHalfPlane.valueAtInfty ⇑f) =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (-c
 * τ.im)
参数：GL (Fin 2) ℝ；f : F；IsCusp OnePoint.infty Γ；fun τ => f τ - UpperHalfPlane.valu
eAtInfty ⇑f；-c * τ.im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subgroup.strictWidthInfty_pos_iff`：strictWidthInfty_pos_iff [DiscreteTop
ology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] : 0 < 𝒢.strictWidthInfty ↔ IsCusp 
∞ 𝒢
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `Subgroup.strictWidthInfty_mem_strictPeriods`：strictWidthInfty_mem_strict
Periods : 𝒢.strictWidthInfty in 𝒢.strictPeriods
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.two_pi_pos`：two_pi_pos : 0 < 2 * π
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 64 条，此处仅展示前 30 条）

--- 原说明 ---
Version of `exp_decay_sub_atImInfty` stating a less precise result but easier to
 apply in
practice (not specifying the growth rate precisely).

Note that the `Fact` hypothesis is automatically synthesized for arithmetic subg
roups.
The discreteness hypothesis may be unnecessary, but it is satisfied in the cases
 of interest.
-/
theorem exp_decay_sub_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] :
    ∃ c > 0, (fun τ ↦ f τ - valueAtInfty f) =O[atImInfty] (fun τ ↦ Real.exp (-c * τ.im)) := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  refine ⟨2 * π / Γ.strictWidthInfty, div_pos Real.two_pi_pos hh, ?_⟩
  convert! exp_decay_sub_atImInfty hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f) using
    3 with τ
  ring_nf

/-- Version of `exp_decay_atImInfty` stating a less precise result but easier to apply in practice
(not specifying the growth rate precisely). Note that the `Fact` hypothesis is automatically
synthesized for arithmetic subgroups. -/
/-
**ModularFormClass.exp_decay_atImInfty'** 是 Mathlib 中的一个定理，位于命名空间 `ModularFormCl
ass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} (f : F)   [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne] [Disc
reteTopology ↥Γ] [Fact (IsCusp OnePoint.infty Γ)],   UpperHalfPlane.IsZeroAtImIn
fty ⇑f → ∃ c > 0, ⇑f =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (-c * τ.im)
参数：GL (Fin 2) ℝ；f : F；IsCusp OnePoint.infty Γ；-c * τ.im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero`：∀ {f : UpperHalfPla
ne → ℂ}, UpperHalfPlane.IsZeroAtImInfty f → UpperHalfPlane.valueAtInfty f = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ModularFormClass.exp_decay_sub_atImInfty'`：∀ {k : ℤ} {F : Type u_1} [ins
t : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} (f : F)   [Modular
FormClass F Γ k] [Γ.HasDetPlusM…

--- 原说明 ---
Version of `exp_decay_atImInfty` stating a less precise result but easier to app
ly in practice
(not specifying the growth rate precisely). Note that the `Fact` hypothesis is a
utomatically
synthesized for arithmetic subgroups.
-/
theorem exp_decay_atImInfty' [ModularFormClass F Γ k] [Γ.HasDetPlusMinusOne]
    [DiscreteTopology Γ] [Fact (IsCusp OnePoint.infty Γ)] (hf : IsZeroAtImInfty f) :
    ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) := by
  simpa [hf.valueAtInfty_eq_zero] using exp_decay_sub_atImInfty' f

end ModularFormClass

open ModularFormClass

namespace CuspFormClass

include Γ k -- can't be inferred from statements but shouldn't be omitted
variable [CuspFormClass F Γ k]

/-
**CuspFormClass.zero_at_infty_comp_ofComplex** 是 Mathlib 中的一个定理，位于命名空间 `CuspForm
Class`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} (f : F) [CuspFormClass F Γ k]   [Fact (IsCusp OnePoint.infty Γ)
], (Filter.comap Complex.im Filter.atTop).ZeroAtFilter (⇑f ∘ ↑UpperHalfPlane.ofC
omplex)
参数：GL (Fin 2) ℝ；f : F；IsCusp OnePoint.infty Γ；Filter.comap Complex.im Filter.atT
op；⇑f ∘ ↑UpperHalfPlane.ofComplex。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
· 使用引理 `UpperHalfPlane.tendsto_comap_im_ofComplex`：tendsto_comap_im_ofComplex : 
Tendsto ofComplex (comap Complex.im atTop) atImInfty
-/
theorem zero_at_infty_comp_ofComplex [Fact (IsCusp OnePoint.infty Γ)] :
    ZeroAtFilter I∞ (f ∘ ofComplex) :=
  (zero_at_infty f).comp tendsto_comap_im_ofComplex
/-
**CuspFormClass.cuspFunction_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `CuspFormClass
`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [CuspFormClass F Γ k], 0 < h → h ∈ Γ.strictPe
riods → UpperHalfPlane.cuspFunction h (⇑f) 0 = 0
参数：GL (Fin 2) ℝ；f : F；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero`：cuspFunction_app
ly_zero {f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h) : cuspFunction 
h f 0 = 0
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
-/
theorem cuspFunction_apply_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    cuspFunction h f 0 = 0 :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh

/-- The zeroth coefficient of the `q`-expansion of a cusp form vanishes. -/
/-
**CuspFormClass.qExpansion_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `CuspFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [CuspFormClass F Γ k], 0 < h → h ∈ Γ.strictPe
riods → (PowerSeries.coeff 0) (UpperHalfPlane.qExpansion h ⇑f) = 0
参数：GL (Fin 2) ℝ；f : F；PowerSeries.coeff 0；UpperHalfPlane.qExpansion h ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `CuspFormClass.cuspFunction_apply_zero`：∀ {k : ℤ} {F : Type u_1} [inst : 
FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [Cus
pFormClass F Γ k], 0 < h → …
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The zeroth coefficient of the `q`-expansion of a cusp form vanishes.
-/
theorem qExpansion_coeff_zero (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (qExpansion h f).coeff 0 = 0 := by
  simp [qExpansion_coeff, cuspFunction_apply_zero f hh hΓ]
/-
**CuspFormClass.exp_decay_atImInfty** 是 Mathlib 中的一个定理，位于命名空间 `CuspFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [CuspFormClass F Γ k],   0 < h → h ∈ Γ.strict
Periods → ⇑f =O[UpperHalfPlane.atImInfty] fun τ => Real.exp (-2 * Real.pi * τ.im
 / h)
参数：GL (Fin 2) ℝ；f : F；-2 * Real.pi * τ.im / h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用定理 `UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty`：exp_decay_atImInfty 
{f : ℍ -> Complex} (hf : IsZeroAtImInfty f) (hh : 0 < h) (hfper : Periodic (f ∘ 
ofComplex) h) (hfhol : MDiff f) (hfbdd :…
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `CuspFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : CuspFormClass F Γ k…
· 使用定理 `CuspFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin 2)
 ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : CuspFormCla
ss F Γ k…
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
-/
theorem exp_decay_atImInfty (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h) :=
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty (CuspFormClass.zero_at_infty f) hh
    (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)
/-
**CuspFormClass.exp_decay_atImInfty'** 是 Mathlib 中的一个定理，位于命名空间 `CuspFormClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} (f : F) [CuspFormClass F Γ k]   [Γ.HasDetPlusMinusOne] [Discret
eTopology ↥Γ] [Fact (IsCusp OnePoint.infty Γ)],   ∃ c > 0, ⇑f =O[UpperHalfPlane.
atImInfty] fun τ => Real.exp (-c * τ.im)
参数：GL (Fin 2) ℝ；f : F；IsCusp OnePoint.infty Γ；-c * τ.im。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.exp_decay_atImInfty'`：∀ {k : ℤ} {F : Type u_1} [inst : 
FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} (f : F)   [ModularForm
Class F Γ k] [Γ.HasDetPlusM…
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用引理 `CuspFormClass.zero_at_infty`：CuspFormClass.zero_at_infty [CuspFormClass 
F Γ k] [Fact (IsCusp ∞ Γ)] : IsZeroAtImInfty f
-/
theorem exp_decay_atImInfty' [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [Fact (IsCusp OnePoint.infty Γ)] :
    ∃ c > 0, f =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) :=
  ModularFormClass.exp_decay_atImInfty' f (CuspFormClass.zero_at_infty f)

end CuspFormClass

section ring

namespace UpperHalfPlane

/-
**UpperHalfPlane.cuspFunction_mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：∀ {h : ℝ} {f g : ℂ → ℂ},   ContinuousAt (Function.Periodic.cuspFunction h 
f) 0 →     ContinuousAt (Function.Periodic.cuspFunction h g) 0 →       Function.
Periodic.cuspFunction h (f * g) 0 =         Function.Periodic.cuspFunction h f 0
 * Function.Periodic.cuspFunction h g 0
参数：Function.Periodic.cuspFunction h f；Function.Periodic.cuspFunction h g；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.cuspFunction.eq_1`：∀ (h : ℝ) (f : ℂ → ℂ),   Function.P
eriodic.cuspFunction h f =     Function.update (f ∘ Function.Periodic.invQParam 
h) 0       ((nhdsWithin 0…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `Function.Periodic.tendsto_nhds_zero`：tendsto_nhds_zero {f : Complex -> C
omplex} (hcts : ContinuousAt (cuspFunction h f) 0) : Tendsto (fun x => f (invQPa
ram h x)) (𝓝[!=] 0) (𝓝 (c…
-/
theorem cuspFunction_mul_zero {f g : ℂ → ℂ} (hfcts : ContinuousAt (Periodic.cuspFunction h f) 0)
    (hgcts : ContinuousAt (Periodic.cuspFunction h g) 0) : Periodic.cuspFunction h (f * g) 0 =
    Periodic.cuspFunction h f 0 * Periodic.cuspFunction h g 0 := by
  rw [Periodic.cuspFunction, update_self]
  exact (Periodic.tendsto_nhds_zero hfcts).mul (Periodic.tendsto_nhds_zero hgcts) |>.limUnder_eq
/-
**UpperHalfPlane.qExpansion_mul_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspF
unction h f) 0 →     ContinuousAt (UpperHalfPlane.cuspFunction h g) 0 →       (P
owerSeries.coeff 0) (UpperHalfPlane.qExpansion h (f * g)) =         (PowerSeries
.coeff 0) (UpperHalfPlane.qExpansion h f) * (PowerSeries.coeff 0) (UpperHalfPlan
e.qExpansion h g)
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；PowerSeries.c
oeff 0；UpperHalfPlane.qExpansion h (f * g)；PowerSeries.coeff 0；UpperHalfPlane.qE
xpansion h f；PowerSeries.coeff 0；UpperHalfPlane.qExpansion h g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `UpperHalfPlane.cuspFunction_mul_zero`：∀ {h : ℝ} {f g : ℂ → ℂ},   Continu
ousAt (Function.Periodic.cuspFunction h f) 0 →     ContinuousAt (Function.Period
ic.cuspFunction h g) 0 →  …
-/
lemma qExpansion_mul_coeff_zero {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    (qExpansion h (f * g)).coeff 0 = ((qExpansion h f).coeff 0) * (qExpansion h g).coeff 0 := by
  simpa [qExpansion_coeff] using! cuspFunction_mul_zero hfcts hgcts
/-
**UpperHalfPlane.cuspFunction_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspF
unction h f) 0 →     ContinuousAt (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.cuspFunction h (f * g) = UpperHalfPlane.cuspFunction h f * UpperHal
fPlane.cuspFunction h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.cuspFunction_mul_zero`：∀ {h : ℝ} {f g : ℂ → ℂ},   Continu
ousAt (Function.Periodic.cuspFunction h f) 0 →     ContinuousAt (Function.Period
ic.cuspFunction h g) 0 →  …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cuspFunction_mul {f g : ℍ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f * g) = cuspFunction h f * cuspFunction h g := by
  ext z
  by_cases H : z = 0
  · simpa [H] using! cuspFunction_mul_zero hfcts hgcts
  · simp [cuspFunction, Periodic.cuspFunction, H]
/-
**UpperHalfPlane.cuspFunction_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspFun
ction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane.cuspFunction h (a • f) = a • UpperH
alfPlane.cuspFunction h f
参数：UpperHalfPlane.cuspFunction h f；a : ℂ；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Periodic.cuspFunction_smul`：cuspFunction_smul {h} {f : Complex 
-> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : Complex) : cuspFunc
tion h (a • f) = a • cusp…
-/
lemma cuspFunction_smul {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) (a : ℂ) :
    cuspFunction h (a • f) = a • cuspFunction h f := by
  apply Periodic.cuspFunction_smul hfcts
/-
**UpperHalfPlane.cuspFunction_neg** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspFun
ction h f) 0 →     UpperHalfPlane.cuspFunction h (-f) = -UpperHalfPlane.cuspFunc
tion h f
参数：UpperHalfPlane.cuspFunction h f；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Periodic.cuspFunction_neg`：cuspFunction_neg {h} {f : Complex ->
 Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) : cuspFunction h (-f) = -c
uspFunction h f
-/
lemma cuspFunction_neg {f : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0) :
    cuspFunction h (-f) = -cuspFunction h f :=
  Periodic.cuspFunction_neg hfcts
/-
**UpperHalfPlane.cuspFunction_add** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspF
unction h f) 0 →     ContinuousAt (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.cuspFunction h (f + g) = UpperHalfPlane.cuspFunction h f + UpperHal
fPlane.cuspFunction h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Periodic.cuspFunction_add`：cuspFunction_add {h} {f g : Complex 
-> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (c
uspFunction h g) 0) : cu…
-/
lemma cuspFunction_add {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g :=
  Periodic.cuspFunction_add hfcts hgcts
/-
**UpperHalfPlane.cuspFunction_sub** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   ContinuousAt (UpperHalfPlane.cuspF
unction h f) 0 →     ContinuousAt (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.cuspFunction h (f - g) = UpperHalfPlane.cuspFunction h f - UpperHal
fPlane.cuspFunction h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Periodic.cuspFunction_sub`：cuspFunction_sub {h} {f g : Complex 
-> Complex} (hfcts : ContinuousAt (cuspFunction h f) 0) (hgcts : ContinuousAt (c
uspFunction h g) 0) : cu…
-/
lemma cuspFunction_sub {f g : ℍ → ℂ} (hfcts : ContinuousAt (cuspFunction h f) 0)
    (hgcts : ContinuousAt (cuspFunction h g) 0) :
    cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g :=
  Periodic.cuspFunction_sub hfcts hgcts
/-
**UpperHalfPlane.qExpansion_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   AnalyticAt ℂ (UpperHalfPlane.cuspF
unction h f) 0 →     AnalyticAt ℂ (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.qExpansion h (f * g) = UpperHalfPlane.qExpansion h f * UpperHalfPla
ne.qExpansion h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.cuspFunction_mul`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},  
 ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ContinuousAt (UpperHalfP
lane.cuspFunction h g…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用引理 `iteratedDeriv_mul`：iteratedDeriv_mul {f g : 𝕜 -> 𝔸} (hf : ContDiffAt 𝕜 n
 f x) (hg : ContDiffAt 𝕜 n g x) : iteratedDeriv n (f * g) x = ∑ i in .range (n +
 1), n.…
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Nat.cast_choose`：cast_choose {a b : Nat} (h : a <= b) : (b.choose a : K)
 = b ! / (a ! * (b - a)!)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 49 条，此处仅展示前 30 条）
-/
lemma qExpansion_mul {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f * g) = qExpansion h f * qExpansion h g := by
  ext
  simp only [qExpansion_coeff, cuspFunction_mul hf.continuousAt hg.continuousAt,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]
/-
**UpperHalfPlane.qExpansion_smul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   AnalyticAt ℂ (UpperHalfPlane.cuspFun
ction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane.qExpansion h (a • f) = a • UpperHal
fPlane.qExpansion h f
参数：UpperHalfPlane.cuspFunction h f；a : ℂ；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.cuspFunction_smul`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   
ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane
.cuspFunction h (a • f…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `iteratedDeriv_const_smul_field`：iteratedDeriv_const_smul_field {n : Nat}
 (c : 𝕝) (f : 𝕜 -> F) : iteratedDeriv n (c • f) x = c • iteratedDeriv n f x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansion_smul {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (a : ℂ) :
    qExpansion h (a • f) = a • qExpansion h f := by
  ext m
  simp [qExpansion_coeff, cuspFunction_smul hf.continuousAt, iteratedDeriv_const_smul_field,
    mul_left_comm]
/-
**UpperHalfPlane.qExpansion_neg** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   AnalyticAt ℂ (UpperHalfPlane.cuspFun
ction h f) 0 → UpperHalfPlane.qExpansion h (-f) = -UpperHalfPlane.qExpansion h f
参数：UpperHalfPlane.cuspFunction h f；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `UpperHalfPlane.qExpansion_smul`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   An
alyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane.q
Expansion h (a • f) …
-/
lemma qExpansion_neg {f : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    qExpansion h (-f) = -qExpansion h f := by
  simpa using qExpansion_smul hf (-1)
/-
**UpperHalfPlane.qExpansion_add** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   AnalyticAt ℂ (UpperHalfPlane.cuspF
unction h f) 0 →     AnalyticAt ℂ (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.qExpansion h (f + g) = UpperHalfPlane.qExpansion h f + UpperHalfPla
ne.qExpansion h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.cuspFunction_add`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},  
 ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ContinuousAt (UpperHalfP
lane.cuspFunction h g…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用引理 `iteratedDeriv_add`：iteratedDeriv_add (hf : ContDiffAt 𝕜 n f x) (hg : Con
tDiffAt 𝕜 n g x) : iteratedDeriv n (f + g) x = iteratedDeriv n f x + iteratedDer
iv n g …
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansion_add {f g : ℍ → ℂ}
    (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ (cuspFunction h g) 0) :
    qExpansion h (f + g) = qExpansion h f + qExpansion h g := by
  ext m
  simp [qExpansion_coeff, cuspFunction_add hf.continuousAt hg.continuousAt,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]
/-
**UpperHalfPlane.qExpansion_sub** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   AnalyticAt ℂ (UpperHalfPlane.cuspF
unction h f) 0 →     AnalyticAt ℂ (UpperHalfPlane.cuspFunction h g) 0 →       Up
perHalfPlane.qExpansion h (f - g) = UpperHalfPlane.qExpansion h f - UpperHalfPla
ne.qExpansion h g
参数：UpperHalfPlane.cuspFunction h f；UpperHalfPlane.cuspFunction h g；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.cuspFunction_neg`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   C
ontinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     UpperHalfPlane.cuspFunctio
n h (-f) = -UpperHalf…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `AnalyticAt.neg`：AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-
f) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `UpperHalfPlane.qExpansion_neg`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   Ana
lyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 → UpperHalfPlane.qExpansion h (-f)
 = -UpperHalfPlane.…
· 使用定理 `UpperHalfPlane.qExpansion_add`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   A
nalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     AnalyticAt ℂ (UpperHalfPla
ne.cuspFunction h g…
-/
lemma qExpansion_sub {f g : ℍ → ℂ} (hf : AnalyticAt ℂ (cuspFunction h f) 0) (hg : AnalyticAt ℂ
    (cuspFunction h g) 0) : qExpansion h (f - g) = qExpansion h f - qExpansion h g := by
  have hg' : AnalyticAt ℂ (cuspFunction h (-g)) 0 := by
    simpa [cuspFunction_neg hg.continuousAt] using hg.neg
  simpa [sub_eq_add_neg, qExpansion_neg hg] using (qExpansion_add hf hg')
/-
**UpperHalfPlane.qExpansion_zero** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (h : ℝ), UpperHalfPlane.qExpansion h 0 = 0
参数：h : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `iteratedDeriv_const_zero`：iteratedDeriv_const_zero : iteratedDeriv n (0 
: 𝕜 -> F) x = (0 : F)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma qExpansion_zero (h) : qExpansion h 0 = 0 := by
  suffices cuspFunction h 0 = 0 by ext; simp [qExpansion_coeff, this]
  simpa [cuspFunction, Periodic.cuspFunction]
    using! (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).limUnder_eq
/-
**UpperHalfPlane.qExpansion_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   0 < h →     Function.Periodic (f ∘ ↑
UpperHalfPlane.ofComplex) ↑h →       MDiff f → UpperHalfPlane.IsBoundedAtImInfty
 f → (UpperHalfPlane.qExpansion h f = 0 ↔ f = 0)
参数：f ∘ ↑UpperHalfPlane.ofComplex；UpperHalfPlane.qExpansion h f = 0 ↔ f = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `UpperHalfPlane.hasSum_qExpansion`：hasSum_qExpansion {f : ℍ -> Complex} (
hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBo
undedAtImInfty f) (τ :…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `UpperHalfPlane.qExpansion_zero`：∀ (h : ℝ), UpperHalfPlane.qExpansion h 0
 = 0
-/
lemma qExpansion_eq_zero_iff {f : ℍ → ℂ} (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    qExpansion h f = 0 ↔ f = 0 := by
  constructor
  · intro H
    ext z
    simp [← (hasSum_qExpansion hh hfper hfhol hfbdd z).tsum_eq, H]
  · intro H
    simpa [H] using qExpansion_zero h
/-
**UpperHalfPlane.qExpansion_one** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：∀ (h : ℝ), UpperHalfPlane.qExpansion h 1 = 1
参数：h : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Periodic.cuspFunction_eq_of_nonzero`：cuspFunction_eq_of_nonzero
 {q : Complex} (hq : q != 0) : cuspFunction h f q = f (invQParam h q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_const`：iteratedDeriv_const {n : Nat} {c : F} {x : 𝕜} : ite
ratedDeriv n (fun _ => c) x = if n = 0 then c else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
-/
lemma qExpansion_one (h) : qExpansion h (1 : ℍ → ℂ) = 1 := by
  ext m
  have h1 : cuspFunction h 1 = 1 := by
    ext q
    rcases eq_or_ne q 0 with rfl | hq
    · simpa [cuspFunction, Periodic.cuspFunction] using! tendsto_const_nhds.limUnder_eq
    · simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero h _ hq]
  have h2 : iteratedDeriv m (1 : ℂ → ℂ) 0 = if m = 0 then 1 else 0 := by
    simpa [ite_apply] using! iteratedDeriv_const
  simp +contextual [qExpansion_coeff, h1, h2]

end UpperHalfPlane

namespace ModularForm

/-
**ModularForm.cuspFunction_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ},   0 < h →     h ∈ Γ.strictPeriods →       ∀ (a : ℂ) (f
 : F) [ModularFormClass F Γ k],         UpperHalfPlane.cuspFunction h (a • ⇑f) =
 a • UpperHalfPlane.cuspFunction h ⇑f
参数：GL (Fin 2) ℝ；a : ℂ；f : F；a • ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.cuspFunction_smul`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   
ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane
.cuspFunction h (a • f…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma cuspFunction_smul (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (a : ℂ)
    (f : F) [ModularFormClass F Γ k] : cuspFunction h (a • f) = a • cuspFunction h f :=
  cuspFunction_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt a
/-
**ModularForm.cuspFunction_neg** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ},   0 < h →     h ∈ Γ.strictPeriods →       ∀ (f : F) [M
odularFormClass F Γ k], UpperHalfPlane.cuspFunction h (-⇑f) = -UpperHalfPlane.cu
spFunction h ⇑f
参数：GL (Fin 2) ℝ；f : F；-⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.cuspFunction_neg`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   C
ontinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     UpperHalfPlane.cuspFunctio
n h (-f) = -UpperHalf…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma cuspFunction_neg (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F)
    [ModularFormClass F Γ k] : cuspFunction h (-f) = -cuspFunction h f :=
  cuspFunction_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
/-
**ModularForm.cuspFunction_add** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLike G UpperHalfPlane ℂ],   0 < h
 →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : F) [ModularFormClass F Γ a] 
(g : G) [ModularFormClass G Γ b],         UpperHalfPlane.cuspFunction h (⇑f + ⇑g
) = UpperHalfPlane.cuspFunction h ⇑f + UpperHalfPlane.cuspFunction h ⇑g
参数：GL (Fin 2) ℝ；f : F；g : G；⇑f + ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.cuspFunction_add`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},  
 ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ContinuousAt (UpperHalfP
lane.cuspFunction h g…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma cuspFunction_add {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : cuspFunction h (f + g) = cuspFunction h f + cuspFunction h g :=
  cuspFunction_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
/-
**ModularForm.cuspFunction_sub** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLike G UpperHalfPlane ℂ],   0 < h
 →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : F) [ModularFormClass F Γ a] 
(g : G) [ModularFormClass G Γ b],         UpperHalfPlane.cuspFunction h (⇑f - ⇑g
) = UpperHalfPlane.cuspFunction h ⇑f - UpperHalfPlane.cuspFunction h ⇑g
参数：GL (Fin 2) ℝ；f : F；g : G；⇑f - ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.cuspFunction_sub`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},  
 ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ContinuousAt (UpperHalfP
lane.cuspFunction h g…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma cuspFunction_sub {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : cuspFunction h (f - g) = cuspFunction h f - cuspFunction h g :=
  cuspFunction_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
/-
**ModularForm.cuspFunction_mul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusOne],   0
 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : ModularForm Γ a) (g : Mo
dularForm Γ b),         UpperHalfPlane.cuspFunction h ⇑(f.mul g) = UpperHalfPlan
e.cuspFunction h ⇑f * UpperHalfPlane.cuspFunction h ⇑g
参数：GL (Fin 2) ℝ；f : ModularForm Γ a；g : ModularForm Γ b；f.mul g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.cuspFunction_mul`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},  
 ContinuousAt (UpperHalfPlane.cuspFunction h f) 0 →     ContinuousAt (UpperHalfP
lane.cuspFunction h g…
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
-/
protected lemma cuspFunction_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    cuspFunction h (f.mul g) = cuspFunction h f * cuspFunction h g :=
  cuspFunction_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ).continuousAt
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ).continuousAt
/-
**ModularForm.qExpansion_smul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ},   0 < h →     h ∈ Γ.strictPeriods →       ∀ (a : ℂ) (f
 : F) [ModularFormClass F Γ k],         UpperHalfPlane.qExpansion h (a • ⇑f) = a
 • UpperHalfPlane.qExpansion h ⇑f
参数：GL (Fin 2) ℝ；a : ℂ；f : F；a • ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_smul`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   An
alyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     ∀ (a : ℂ), UpperHalfPlane.q
Expansion h (a • f) …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma qExpansion_smul (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (a : ℂ)
    (f : F) [ModularFormClass F Γ k] : qExpansion h (a • f) = a • qExpansion h f :=
  qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) a
/-
**ModularForm.qExpansion_neg** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ},   0 < h →     h ∈ Γ.strictPeriods →       ∀ (f : F) [M
odularFormClass F Γ k], UpperHalfPlane.qExpansion h (-⇑f) = -UpperHalfPlane.qExp
ansion h ⇑f
参数：GL (Fin 2) ℝ；f : F；-⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_neg`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ},   Ana
lyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 → UpperHalfPlane.qExpansion h (-f)
 = -UpperHalfPlane.…
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma qExpansion_neg (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F)
    [ModularFormClass F Γ k] : qExpansion h (-f) = -qExpansion h f :=
  qExpansion_neg (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
/-
**ModularForm.qExpansion_add** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLike G UpperHalfPlane ℂ],   0 < h
 →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : F) [ModularFormClass F Γ a] 
(g : G) [ModularFormClass G Γ b],         UpperHalfPlane.qExpansion h (⇑f + ⇑g) 
= UpperHalfPlane.qExpansion h ⇑f + UpperHalfPlane.qExpansion h ⇑g
参数：GL (Fin 2) ℝ；f : F；g : G；⇑f + ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_add`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   A
nalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     AnalyticAt ℂ (UpperHalfPla
ne.cuspFunction h g…
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma qExpansion_add {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h (f + g) = qExpansion h f + qExpansion h g :=
    qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)
/-
**ModularForm.qExpansion_sub** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLike G UpperHalfPlane ℂ],   0 < h
 →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : F) [ModularFormClass F Γ a] 
(g : G) [ModularFormClass G Γ b],         UpperHalfPlane.qExpansion h (⇑f - ⇑g) 
= UpperHalfPlane.qExpansion h ⇑f - UpperHalfPlane.qExpansion h ⇑g
参数：GL (Fin 2) ℝ；f : F；g : G；⇑f - ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_sub`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   A
nalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     AnalyticAt ℂ (UpperHalfPla
ne.cuspFunction h g…
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma qExpansion_sub {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h (f - g) = qExpansion h f - qExpansion h g :=
  qExpansion_sub (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)

/-- The q-expansion of a pointwise product of two modular-form-class objects is the product of
their q-expansions. Works for any `ModularFormClass` (e.g. a `CuspForm` times a `ModularForm`). -/
/-
**ModularForm.qExpansion_mul_coe** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLike G UpperHalfPlane ℂ],   0 < h
 →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : F) [ModularFormClass F Γ a] 
(g : G) [ModularFormClass G Γ b],         UpperHalfPlane.qExpansion h (⇑f * ⇑g) 
= UpperHalfPlane.qExpansion h ⇑f * UpperHalfPlane.qExpansion h ⇑g
参数：GL (Fin 2) ℝ；f : F；g : G；⇑f * ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_mul`：∀ {h : ℝ} {f g : UpperHalfPlane → ℂ},   A
nalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 →     AnalyticAt ℂ (UpperHalfPla
ne.cuspFunction h g…
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…

--- 原说明 ---
The q-expansion of a pointwise product of two modular-form-class objects is the 
product of
their q-expansions. Works for any `ModularFormClass` (e.g. a `CuspForm` times a 
`ModularForm`).
-/
protected lemma qExpansion_mul_coe {G : Type*} [FunLike G ℍ ℂ] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : F) [ModularFormClass F Γ a] (g : G)
    [ModularFormClass G Γ b] : qExpansion h ((⇑f * ⇑g : ℍ → ℂ)) = qExpansion h f * qExpansion h g :=
  qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ)
    (ModularFormClass.analyticAt_cuspFunction_zero g hh hΓ)
/-
**ModularForm.qExpansion_mul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusOne],   0
 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ} (f : ModularForm Γ a) (g : Mo
dularForm Γ b),         UpperHalfPlane.qExpansion h ⇑(f.mul g) = UpperHalfPlane.
qExpansion h ⇑f * UpperHalfPlane.qExpansion h ⇑g
参数：GL (Fin 2) ℝ；f : ModularForm Γ a；g : ModularForm Γ b；f.mul g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.qExpansion_mul_coe`：∀ {F : Type u_1} [inst : FunLike F Upper
HalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : Fu
nLike G UpperHalfPla…
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
-/
protected lemma qExpansion_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h (f.mul g) = qExpansion h f * qExpansion h g :=
  ModularForm.qExpansion_mul_coe hh hΓ f g
/-
**ModularForm.qExpansion_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ},   0 < h → h ∈ Γ.strictPeriods → ∀
 {k : ℤ} (f : ModularForm Γ k), UpperHalfPlane.qExpansion h ⇑f = 0 ↔ f = 0
参数：GL (Fin 2) ℝ；f : ModularForm Γ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isCusp_of_mem_strictPeriods`：isCusp_of_mem_strictPeriods {h : R
eal} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) : IsCusp OnePoint.infty 𝒢
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.qExpansion_eq_zero_iff`：∀ {h : ℝ} {f : UpperHalfPlane → ℂ
},   0 < h →     Function.Periodic (f ∘ ↑UpperHalfPlane.ofComplex) ↑h →       MD
iff f → UpperHalfPlane.IsBo…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma qExpansion_eq_zero_iff (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ}
    (f : ModularForm Γ k) : qExpansion h f = 0 ↔ f = 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  simp [qExpansion_eq_zero_iff hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)]
/-
**ModularForm.qExpansion_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusOne], Upp
erHalfPlane.qExpansion h ⇑1 = 1
参数：GL (Fin 2) ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHalfPlane.qExpansion_one`：∀ (h : ℝ), UpperHalfPlane.qExpansion h 1 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma qExpansion_one [Γ.HasDetPlusMinusOne] :
    qExpansion h (1 : ModularForm Γ 0) = 1 := by
  simp [qExpansion_one]

@[simp]
/-
**ModularForm.qExpansion_mcast** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {a b : ℤ} {Γ' : Subgroup (GL (Fin 
2) ℝ)} (heq : a = b) (hΓ : Γ' = Γ)   (f : ModularForm Γ a), UpperHalfPlane.qExpa
nsion h ⇑(ModularForm.mcast heq f hΓ) = UpperHalfPlane.qExpansion h ⇑f
参数：GL (Fin 2) ℝ；GL (Fin 2) ℝ；heq : a = b；hΓ : Γ' = Γ；f : ModularForm Γ a；Modular
Form.mcast heq f hΓ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma qExpansion_mcast {a b : ℤ} {Γ' : Subgroup (GL (Fin 2) ℝ)}
    (heq : a = b) (hΓ : Γ' = Γ) (f : ModularForm Γ a) :
    qExpansion h (ModularForm.mcast heq f hΓ) = qExpansion h f := rfl
/-
**ModularForm.qExpansion_pow** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusO
ne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ (f : ModularForm Γ k) (n : ℕ), 
UpperHalfPlane.qExpansion h ⇑(f.pow n) = UpperHalfPlane.qExpansion h ⇑f ^ n
参数：GL (Fin 2) ℝ；f : ModularForm Γ k；n : ℕ；f.pow n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularForm.coe_pow`：coe_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetP
lusMinusOne] {k : Int} (f : ModularForm Γ k) (n : Nat) : ⇑(f.pow n) = (⇑f) ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `UpperHalfPlane.qExpansion_one`：∀ (h : ℝ), UpperHalfPlane.qExpansion h 1 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModularForm.coe_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k_1 k_2 : ℤ} [inst
 : Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1)   (g : ModularForm Γ k_2), ⇑(f.
mul g) = …
· 使用定理 `ModularForm.qExpansion_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ}
 (f : ModularFor…
-/
protected lemma qExpansion_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) :
    qExpansion h (f.pow n) = (qExpansion h f) ^ n := by
  induction n with
  | zero => simp only [coe_pow, pow_zero, qExpansion_one]
  | succ n ih =>
    rw [coe_pow, pow_succ, ← coe_pow, ← coe_mul, ModularForm.qExpansion_mul hh hΓ, ih,
      pow_succ]

/-- The product of two non-zero modular forms is non-zero. -/
/-
**ModularForm.mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} [inst : Γ.HasDetPlusMinusOne],   (∃ h ∈ Γ.
strictPeriods, 0 < h) → ∀ {a b : ℤ} {f : ModularForm Γ a} {g : ModularForm Γ b},
 f ≠ 0 → g ≠ 0 → f.mul g ≠ 0
参数：GL (Fin 2) ℝ；∃ h ∈ Γ.strictPeriods, 0 < h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModularForm.qExpansion_eq_zero_iff`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h :
 ℝ},   0 < h → h ∈ Γ.strictPeriods → ∀ {k : ℤ} (f : ModularForm Γ k), UpperHalfP
lane.qExpansion h ⇑f = 0…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModularForm.qExpansion_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ}
 (f : ModularFor…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `MvPowerSeries.instNoZeroDivisors`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] [NoZeroDivisors R], NoZeroDivisors (MvPowerSeries σ R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α

--- 原说明 ---
The product of two non-zero modular forms is non-zero.
-/
protected lemma mul_ne_zero [Γ.HasDetPlusMinusOne] (hΓ : ∃ h ∈ Γ.strictPeriods, 0 < h)
    {a b : ℤ} {f : ModularForm Γ a} {g : ModularForm Γ b} (hf : f ≠ 0) (hg : g ≠ 0) :
    f.mul g ≠ 0 := by
  obtain ⟨h, hΓ, hh⟩ := hΓ
  simp only [ne_eq, ← ModularForm.qExpansion_eq_zero_iff hh hΓ,
    ModularForm.qExpansion_mul hh hΓ] at hf hg ⊢
  exact mul_ne_zero hf hg

/-- The qExpansion map as an additive group hom. to power series over `ℂ`. -/
/-
**ModularForm.qExpansionAddHom** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} → {h : ℝ} → 0 < h → h ∈ Γ.strictPeriods → (k
 : ℤ) → ModularForm Γ k →+ PowerSeries ℂ
参数：GL (Fin 2) ℝ；k : ℤ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_zero`：∀ (h : ℝ), UpperHalfPlane.qExpansion h 0
 = 0

--- 原说明 ---
The qExpansion map as an additive group hom. to power series over `ℂ`.
-/
def qExpansionAddHom (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →+ PowerSeries ℂ where
  toFun f := qExpansion h f
  map_zero' := qExpansion_zero h
  map_add' f g := ModularForm.qExpansion_add hh hΓ f g

open scoped DirectSum in
/-- The qExpansion map as a map from the graded ring of modular forms to power series over `ℂ`. -/
/-
**ModularForm.qExpansionRingHom** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} →   (h : ℝ) →     [inst : Γ.HasDetPlusMinusO
ne] →       0 < h → h ∈ Γ.strictPeriods → (DirectSum ℤ fun k => ModularForm Γ k)
 →+* PowerSeries ℂ
参数：GL (Fin 2) ℝ；h : ℝ；DirectSum ℤ fun k => ModularForm Γ k。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.qExpansion_one`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne], UpperHalfPlane.qExpansion h ⇑1 = 1
· 使用定理 `ModularForm.qExpansion_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ}
 (f : ModularFor…

--- 原说明 ---
The qExpansion map as a map from the graded ring of modular forms to power serie
s over `ℂ`.
-/
def qExpansionRingHom (h) [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) : (⨁ k, ModularForm Γ k) →+* PowerSeries ℂ :=
  DirectSum.toSemiring (qExpansionAddHom hh hΓ) ModularForm.qExpansion_one
    (ModularForm.qExpansion_mul hh hΓ)

@[simp]
/-
**ModularForm.qExpansionRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusOne] (hh 
: 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)   (f : ModularForm Γ k),   (ModularF
orm.qExpansionRingHom h hh hΓ) ((DirectSum.of (ModularForm Γ) k) f) = UpperHalfP
lane.qExpansion h ⇑f
参数：GL (Fin 2) ℝ；hh : 0 < h；hΓ : h ∈ Γ.strictPeriods；k : ℤ；f : ModularForm Γ k；Mo
dularForm.qExpansionRingHom h hh hΓ；(DirectSum.of (ModularForm Γ) k) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toSemiring_of`：toSemiring_of (f : forall i, A i ->+ R) (hone h
mul) (i : ι) (x : A i) : toSemiring f hone hmul (of _ i x) = f _ x
· 使用定理 `ModularForm.qExpansion_one`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne], UpperHalfPlane.qExpansion h ⇑1 = 1
· 使用定理 `ModularForm.qExpansion_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ}
 (f : ModularFor…
-/
lemma qExpansionRingHom_apply [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) (f : ModularForm Γ k) :
    qExpansionRingHom h hh hΓ (DirectSum.of _ k f) = qExpansion h f :=
  DirectSum.toSemiring_of ..
/-
**ModularForm.qExpansion_of_mul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusOne],   0
 < h →     h ∈ Γ.strictPeriods →       ∀ (a b : ℤ) (f : ModularForm Γ a) (g : Mo
dularForm Γ b),         UpperHalfPlane.qExpansion h             ⇑(((DirectSum.of
 (ModularForm Γ) a) f * (DirectSum.of (ModularForm Γ) b) g) (a + b)) =          
 UpperHalfPlane.qExpansion h ⇑f * UpperHalfPlane.qExpansion h ⇑g
参数：GL (Fin 2) ℝ；a b : ℤ；f : ModularForm Γ a；g : ModularForm Γ b；((DirectSum.of (
ModularForm Γ) a) f * (DirectSum.of (ModularForm Γ) b) g) (a + b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.of_mul_of`：of_mul_of {i j} (a : A i) (b : A j) : of A i a * of
 A j b = of _ (i + j) (GradedMonoid.GMul.mul a b)
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `ModularForm.coe_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k_1 k_2 : ℤ} [inst
 : Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1)   (g : ModularForm Γ k_2), ⇑(f.
mul g) = …
· 使用定理 `ModularForm.qExpansion_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [ins
t : Γ.HasDetPlusMinusOne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ {a b : ℤ}
 (f : ModularFor…
-/
lemma qExpansion_of_mul [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (a b : ℤ) (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qExpansion h ((DirectSum.of _ a f * DirectSum.of _ b g) (a + b)) =
    qExpansion h f * qExpansion h g := by
  simpa [DirectSum.of_mul_of] using! ModularForm.qExpansion_mul hh hΓ f g
/-
**ModularForm.qExpansion_of_pow** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} [inst : Γ.HasDetPlusMinusO
ne],   0 < h →     h ∈ Γ.strictPeriods →       ∀ (f : ModularForm Γ k) (n : ℕ), 
        UpperHalfPlane.qExpansion h ⇑(((DirectSum.of (ModularForm Γ) k) f ^ n) (
↑n * k)) =           UpperHalfPlane.qExpansion h ⇑f ^ n
参数：GL (Fin 2) ℝ；f : ModularForm Γ k；n : ℕ；((DirectSum.of (ModularForm Γ) k) f ^ 
n) (↑n * k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_pow`：∀ {α : Type u_2} {β : Type u_3} [inst : Semiring α] [in
st_1 : Semiring β] (f : α →+* β) (a : α) (n : ℕ),   f (a ^ n) = f a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.ofPow`：ofPow {i} (a : A i) (n : Nat) : of _ i a ^ n = of _ (n 
• i) (GradedMonoid.GMonoid.gnpow _ a)
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModularForm.qExpansionRingHom_apply`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {h 
: ℝ} [inst : Γ.HasDetPlusMinusOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : 
ℤ)   (f : ModularForm Γ k…
-/
lemma qExpansion_of_pow [Γ.HasDetPlusMinusOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (f : ModularForm Γ k) (n : ℕ) :
    qExpansion h ((((DirectSum.of _ k f)) ^ n) (n * k)) = (qExpansion h f) ^ n := by
  have := (qExpansionRingHom h hh hΓ).map_pow (DirectSum.of _ k f) n
  simpa [DirectSum.ofPow]

/-- Specialized version of `UpperHalfPlane.hasSum_qExpansion` for modular forms, with many
arguments filled in automatically. -/
/-
**ModularForm.hasSum_qExpansion** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fi
n 2) ℝ)} {h : ℝ} (f : F),   0 < h →     ∀ {k : ℤ} [ModularFormClass F Γ k] [Fact
 (IsCusp OnePoint.infty Γ)],       h ∈ Γ.strictPeriods →         ∀ (τ : UpperHal
fPlane),           HasSum (fun m => (PowerSeries.coeff m) (UpperHalfPlane.qExpan
sion h ⇑f) * Function.Periodic.qParam h ↑τ ^ m)             (f τ)
参数：GL (Fin 2) ℝ；f : F；IsCusp OnePoint.infty Γ；τ : UpperHalfPlane；fun m => (Power
Series.coeff m) (UpperHalfPlane.qExpansion h ⇑f) * Function.Periodic.qParam h ↑τ
 ^ m；f τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UpperHalfPlane.hasSum_qExpansion`：hasSum_qExpansion {f : ℍ -> Complex} (
hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBo
undedAtImInfty f) (τ :…
· 使用定理 `SlashInvariantFormClass.periodic_comp_ofComplex`：periodic_comp_ofComplex
 [SlashInvariantFormClass F Γ k] (hΓ : h in Γ.strictPeriods) : Periodic (f ∘ ofC
omplex) h
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用引理 `ModularFormClass.bdd_at_infty`：ModularFormClass.bdd_at_infty [ModularFor
mClass F Γ k] [Fact (IsCusp ∞ Γ)] : IsBoundedAtImInfty f

--- 原说明 ---
Specialized version of `UpperHalfPlane.hasSum_qExpansion` for modular forms, wit
h many
arguments filled in automatically.
-/
lemma hasSum_qExpansion (hh : 0 < h) {k : ℤ} [ModularFormClass F Γ k]
    [Fact (IsCusp .infty Γ)] (hΓ : h ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion h f).coeff m * 𝕢 h τ ^ m) (f τ) :=
  τ.hasSum_qExpansion hh (periodic_comp_ofComplex f hΓ) (holo f) (bdd_at_infty f)

end ModularForm

namespace ModularFormClass

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_smul := ModularForm.cuspFunction_smul

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_neg := ModularForm.cuspFunction_neg

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_add := ModularForm.cuspFunction_add

@[deprecated (since := "2026-05-05")]
protected alias cuspFunction_sub := ModularForm.cuspFunction_sub

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_smul := ModularForm.qExpansion_smul

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_neg := ModularForm.qExpansion_neg

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_add := ModularForm.qExpansion_add

@[deprecated (since := "2026-05-05")]
protected alias qExpansion_sub := ModularForm.qExpansion_sub

end ModularFormClass

end ring

section uniqueness

namespace UpperHalfPlane

/-- The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`. -/
/-
**UpperHalfPlane.hasFPowerSeries_cuspFunction** 是 Mathlib 中的一个定理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {h : ℝ} (f : F) {c : 
ℕ → ℂ},   0 < h →     AnalyticAt ℂ (UpperHalfPlane.cuspFunction h ⇑f) 0 →       
(∀ (τ : UpperHalfPlane), HasSum (fun m => c m • Function.Periodic.qParam h ↑τ ^ 
m) (f τ)) →         HasFPowerSeriesOnBall (UpperHalfPlane.cuspFunction h ⇑f) (Up
perHalfPlane.qExpansionFormalMultilinearSeries h f)           0 1
参数：f : F；UpperHalfPlane.cuspFunction h ⇑f；∀ (τ : UpperHalfPlane), HasSum (fun m 
=> c m • Function.Periodic.qParam h ↑τ ^ m) (f τ)；UpperHalfPlane.cuspFunction h 
⇑f；UpperHalfPlane.qExpansionFormalMultilinearSeries h f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用引理 `UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction`：hasFPowerSeriesOnBall
_cuspFunction {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h) (hfanalytic :
 AnalyticAt Complex (cuspFunction h f) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `UpperHalfPlane.qExpansion_coeff`：qExpansion_coeff (f : ℍ -> Complex) (m 
: Nat) : (qExpansion h f).coeff m = (↑m.factorial)⁻¹ * iteratedDeriv m (cuspFunc
tion h f) 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `AnalyticAt.hasFPowerSeriesAt`：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [
NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (
h : AnalyticAt 𝕜 f…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…

--- 原说明 ---
The `q`-expansion of `f` is an `FPowerSeries` representing `cuspFunction n f`.
-/
lemma hasFPowerSeries_cuspFunction {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    HasFPowerSeriesOnBall (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 1 := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h f) (qExpansionFormalMultilinearSeries h f) 0 := by
    simpa [qExpansionFormalMultilinearSeries, qExpansion_coeff, div_eq_mul_inv, mul_comm]
      using hfanalytic.hasFPowerSeriesAt
  simpa [h1.eq_formalMultilinearSeries h2] using hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf
/-
**UpperHalfPlane.qExpansion_coeff_unique** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPla
ne`。
形式化陈述：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {h : ℝ} (f : F) {c : 
ℕ → ℂ},   0 < h →     AnalyticAt ℂ (UpperHalfPlane.cuspFunction h ⇑f) 0 →       
(∀ (τ : UpperHalfPlane), HasSum (fun m => c m • Function.Periodic.qParam h ↑τ ^ 
m) (f τ)) →         ∀ (m : ℕ), c m = (PowerSeries.coeff m) (UpperHalfPlane.qExpa
nsion h ⇑f)
参数：f : F；UpperHalfPlane.cuspFunction h ⇑f；∀ (τ : UpperHalfPlane), HasSum (fun m 
=> c m • Function.Periodic.qParam h ↑τ ^ m) (f τ)；m : ℕ；PowerSeries.coeff m；Uppe
rHalfPlane.qExpansion h ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`：HasFPowerSeriesOnBall.hasFPower
SeriesAt (hf : HasFPowerSeriesOnBall f p x r) : HasFPowerSeriesAt f p x
· 使用引理 `UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction`：hasFPowerSeriesOnBall
_cuspFunction {f : ℍ -> Complex} {c : Nat -> Complex} (hh : 0 < h) (hfanalytic :
 AnalyticAt Complex (cuspFunction h f) …
· 使用定理 `UpperHalfPlane.hasFPowerSeries_cuspFunction`：∀ {F : Type u_1} [inst : Fu
nLike F UpperHalfPlane ℂ] {h : ℝ} (f : F) {c : ℕ → ℂ},   0 < h →     AnalyticAt 
ℂ (UpperHalfPlane.cuspFunction h …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用引理 `UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff`：qExpansionFormal
MultilinearSeries_coeff (m : Nat) : (qExpansionFormalMultilinearSeries h f).coef
f m = (qExpansion h f).coeff m
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `HasFPowerSeriesAt.eq_formalMultilinearSeries`：HasFPowerSeriesAt.eq_forma
lMultilinearSeries {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} 
(h₁ : HasFPowerSeriesAt f p₁ x) (h…
-/
lemma qExpansion_coeff_unique {c : ℕ → ℂ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 := (hasFPowerSeries_cuspFunction f hh hfanalytic hf).hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

end UpperHalfPlane

/-
**ModularFormClass.qExpansion_coeff_unique** 是 Mathlib 中的一个定理，位于命名空间 `ModularFor
mClass`。
形式化陈述：∀ {k : ℤ} {F : Type u_1} [inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup
 (GL (Fin 2) ℝ)} {h : ℝ} {c : ℕ → ℂ},   0 < h →     h ∈ Γ.strictPeriods →       
∀ {f : F} [ModularFormClass F Γ k],         (∀ (τ : UpperHalfPlane), HasSum (fun
 m => c m • Function.Periodic.qParam h ↑τ ^ m) (f τ)) →           ∀ (m : ℕ), c m
 = (PowerSeries.coeff m) (UpperHalfPlane.qExpansion h ⇑f)
参数：GL (Fin 2) ℝ；∀ (τ : UpperHalfPlane), HasSum (fun m => c m • Function.Periodic
.qParam h ↑τ ^ m) (f τ)；m : ℕ；PowerSeries.coeff m；UpperHalfPlane.qExpansion h ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperHalfPlane.qExpansion_coeff_unique`：∀ {F : Type u_1} [inst : FunLike
 F UpperHalfPlane ℂ] {h : ℝ} (f : F) {c : ℕ → ℂ},   0 < h →     AnalyticAt ℂ (Up
perHalfPlane.cuspFunction h …
· 使用定理 `ModularFormClass.analyticAt_cuspFunction_zero`：∀ {k : ℤ} {F : Type u_1} 
[inst : FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F
)   [ModularFormClass F Γ k], 0 < h…
-/
protected lemma ModularFormClass.qExpansion_coeff_unique {c : ℕ → ℂ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) {f : F} [ModularFormClass F Γ k]
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion h f).coeff m :=
  qExpansion_coeff_unique f hh (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ) hf m
