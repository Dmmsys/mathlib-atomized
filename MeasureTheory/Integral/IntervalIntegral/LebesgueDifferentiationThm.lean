/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem. There are two
versions in this file.

* `LocallyIntegrable.ae_hasDerivAt_integral` is the global version. It states that if `f : ℝ → E`
  is locally integrable (`E` a Banach space), then for almost every `x`, for any `c : ℝ`, the
  derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.

* `IntervalIntegrable.ae_hasDerivAt_integral` is the local version. It states that if `f : ℝ → E`
  is interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`,
  the derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/

public section

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The (global) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → E` is
locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
/-
**LocallyIntegrable.ae_hasDerivAt_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyIntegrable.ae_hasDerivAt_integral {f : Real -> E} (hf : LocallyInte
grable f volume) : forallᵐ x, forall c, HasDerivAt (fun x => ∫ (t : Real) in c..
x, f t) (f x) x
参数：hf : LocallyIntegrable f volume。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `intervalIntegrable_iff`：intervalIntegrable_iff : IntervalIntegrable f μ 
a b ↔ IntegrableOn f (Ι a b) μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `MeasureTheory.Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure`：∀ {E :
 Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Me
asurableSpace E] [BorelSpace E]   [FiniteDimensional ℝ…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_average`：ae_tendsto_average [NormedSpace Real E]
 [CompleteSpace E] {f : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Ten
dsto (fun a => ⨍ y in…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ioc`：integral_Icc_eq_integral_Ioc
 : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasDerivAt_iff_tendsto_slope_left_right`：hasDerivAt_iff_tendsto_slope_le
ft_right [LinearOrder 𝕜] : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[<] x) (𝓝 f
') ∧ Tendsto (slope f x) (𝓝[>…
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `intervalIntegral.integral_interval_sub_left`：integral_interval_sub_left 
(hab : IntervalIntegrable f μ a b) (hac : IntervalIntegrable f μ a c) : ((∫ x in
 a..b, f x ∂μ) - ∫ x in a..c, f x…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The (global) interval version of the *Lebesgue Differentiation Theorem*: if `f :
 ℝ → E` is
locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative o
f
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/
theorem LocallyIntegrable.ae_hasDerivAt_integral {f : ℝ → E} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := hy.le
    suffices -((y - x)⁻¹ • ∫ (t : ℝ) in Icc y x, f t) = (x - y)⁻¹ • ∫ (t : ℝ) in Icc y x, f t by
      simpa [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, h]
    rw [← neg_smul, neg_inv, neg_sub]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := hy.le
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, h]

/-- The (local) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → E` is
interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`, the
derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
/-
**IntervalIntegrable.ae_hasDerivAt_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntervalIntegrable.ae_hasDerivAt_integral {f : Real -> E} {a b : Real} (hf
 : IntervalIntegrable f volume a b) : forallᵐ x, x in uIcc a b -> forall c in uI
cc a b, HasDerivAt (fun x => ∫ (t : Real) in c..x, f t) (f x) x
参数：hf : IntervalIntegrable f volume a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Integrable.locallyIntegrable`：∀ {X : Type u_1} {ε : Type u
_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : Topologic
alSpace ε]   [inst_3 : Continuou…
· 使用定理 `MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero`：∀ {α : T
ype u_1} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α} {ε' 
: Type u_7}   [inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_congr_fun`：integrableOn_congr_fun (hst : EqOn
 f g s) (hs : MeasurableSet s) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LocallyIntegrable.ae_hasDerivAt_integral`：LocallyIntegrable.ae_hasDerivA
t_integral {f : Real -> E} (hf : LocallyIntegrable f volume) : forallᵐ x, forall
 c, HasDerivAt (fun x => ∫ (t …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `intervalIntegral.integral_congr_ae'`：integral_congr_ae' (h : forallᵐ x ∂
μ, x in Ioc a b -> f x = g x) (h' : forallᵐ x ∂μ, x in Ioc b a -> f x = g x) : ∫
 x in a..b, f x ∂μ = ∫ x …
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `IntervalIntegrable.symm`：∀ {ε : Type u_3} [inst : TopologicalSpace ε] [i
nst_1 : ENormedAddMonoid ε] {f : ℝ → ε} {a b : ℝ}   {μ : MeasureTheory.Measure ℝ
}, IntervalIn…
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The (local) interval version of the *Lebesgue Differentiation Theorem*: if `f : 
ℝ → E` is
interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c 
∈ uIcc a b`, the
derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/
theorem IntervalIntegrable.ae_hasDerivAt_integral {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → ∀ c ∈ uIcc a b, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ this hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, h₁, h₂] with x hx _ _ _
  intro c hc
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind
