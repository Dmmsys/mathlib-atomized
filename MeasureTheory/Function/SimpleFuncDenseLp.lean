/-
Copyright (c) 2022 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Density of simple functions

Show that each `Lᵖ` Borel measurable function can be approximated in `Lᵖ` norm
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.Lp.simpleFunc`, the type of `Lp` simple functions
* `coeToLp`, the embedding of `Lp.simpleFunc E p μ` into `Lp E p μ`

## Main results

* `tendsto_approxOn_Lp_eLpNorm` (Lᵖ convergence): If `E` is a `NormedAddCommGroup` and `f` is
  measurable and `MemLp` (for `p < ∞`), then the simple functions
  `SimpleFunc.approxOn f hf s 0 h₀ n` may be considered as elements of `Lp E p μ`, and they tend
  in Lᵖ to `f`.
* `Lp.simpleFunc.isDenseEmbedding`: the embedding `coeToLp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simpleFunc.induction`, `Lp.induction`, `MemLp.induction`, `Integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/

@[expose] public section


noncomputable section


open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Topology ENNReal MeasureTheory

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Lp approximation by simple functions -/

section Lp

variable [MeasurableSpace β] [MeasurableSpace E] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {q : ℝ} {p : ℝ≥0∞}

/-
**MeasureTheory.SimpleFunc.nnnorm_approxOn_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：nnnorm_approxOn_le [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable 
f) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] (x : β) (n : Nat) : ‖a
pproxOn f hf s y₀ h₀ n x - f x‖₊ <= ‖f x - y₀‖₊
参数：hf : Measurable f；h₀ : y₀ in s；x : β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.edist_approxOn_le`：edist_approxOn_le {f : β -> 
α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] (x
 : β) (n : Nat) : edist (approxO…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem nnnorm_approxOn_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - f x‖₊ ≤ ‖f x - y₀‖₊ := by
  have := edist_approxOn_le hf h₀ x n
  rw [edist_comm y₀] at this
  simp only [edist_nndist, nndist_eq_nnnorm] at this
  exact mod_cast this
/-
**MeasureTheory.SimpleFunc.norm_approxOn_y** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_approxOn_y₀_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s y₀ h₀ n x - y₀‖ ≤ ‖f x - y₀‖ + ‖f x - y₀‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n
/-
**MeasureTheory.SimpleFunc.norm_approxOn_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β -> E} (hf : Measurab
le f) {s : Set E} (h₀ : (0 : E) in s) [SeparableSpace s] (x : β) (n : Nat) : ‖ap
proxOn f hf s 0 h₀ n x‖ <= ‖f x‖ + ‖f x‖
参数：hf : Measurable f；h₀ : (0 : E) in s；x : β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
· 使用定理 `MeasureTheory.SimpleFunc.edist_approxOn_y0_le`：edist_approxOn_y0_le {f :
 β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace
 s] (x : β) (n : Nat) : edist y₀ (a…
-/
theorem norm_approxOn_zero_le [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E}
    (h₀ : (0 : E) ∈ s) [SeparableSpace s] (x : β) (n : ℕ) :
    ‖approxOn f hf s 0 h₀ n x‖ ≤ ‖f x‖ + ‖f x‖ := by
  simpa [enorm, edist_eq_enorm_sub, ← ENNReal.coe_add, norm_sub_rev]
    using! edist_approxOn_y0_le hf h₀ x n
/-
**MeasureTheory.SimpleFunc.tendsto_approxOn_Lp_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SimpleFunc`。
形式化陈述：tendsto_approxOn_Lp_eLpNorm [OpensMeasurableSpace E] {f : β -> E} (hf : Me
asurable f) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] (hp_ne_top : 
p != ∞) {μ : Measure β} (hμ : forallᵐ x ∂μ, f x in closure s) (hi : eLpNorm (fun
 x => f x - y₀) p μ < ∞) : Tendsto (fun n => eLpNorm (⇑(approxOn f hf s y₀ h₀ n)
 - f) p μ) atTop (𝓝 0)
参数：hf : Measurable f；h₀ : y₀ in s；hp_ne_top : p != ∞；hμ : forallᵐ x ∂μ, f x in c
losure s；hi : eLpNorm (fun x => f x - y₀) p μ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MeasureTheory.SimpleFunc.measurable_bind`：measurable_bind [MeasurableSpa
ce γ] (f : α ->ₛ β) (g : β -> α -> γ) (hg : forall b, Measurable (g b)) : Measur
able fun a => g (f a) a
· 使用定理 `Measurable.pow_const`：Measurable.pow_const (hf : Measurable f) (c : γ) :
 Measurable fun x => f x ^ c
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_edist_right`：measurable_edist_right : Measurable (edist x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ENNReal.rpow_le_rpow`：∀ {x y : ENNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤
 y ^ z
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `MeasureTheory.SimpleFunc.nnnorm_approxOn_le`：nnnorm_approxOn_le [OpensMe
asurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E} {y₀ : E} (h₀ : y₀ 
in s) [SeparableSpace s] (x : β) …
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`：lintegral_r
pow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn`：tendsto_approxOn {f : β -> α}
 (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] {x :
 β} (hx : f x in closure s) : T…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
（共 48 条，此处仅展示前 30 条）
-/
theorem tendsto_approxOn_Lp_eLpNorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] (hp_ne_top : p ≠ ∞) {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : eLpNorm (fun x => f x - y₀) p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f hf s y₀ h₀ n) - f) p μ) atTop (𝓝 0) := by
  by_cases hp_zero : p = 0
  · simpa only [hp_zero, eLpNorm_exponent_zero] using tendsto_const_nhds
  have hp : 0 < p.toReal := toReal_pos hp_zero hp_ne_top
  suffices Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) by
    simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_ne_top]
    convert! continuous_rpow_const.continuousAt.tendsto.comp this
    simp [zero_rpow_of_pos (_root_.inv_pos.mpr hp)]
  -- We simply check the conditions of the Dominated Convergence Theorem:
  -- (1) The function "`p`-th power of distance between `f` and the approximation" is measurable
  have hF_meas n : Measurable fun x => ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal := by
    simpa only [← edist_eq_enorm_sub] using
      (approxOn f hf s y₀ h₀ n).measurable_bind (fun y x => edist y (f x) ^ p.toReal) fun y =>
        (measurable_edist_right.comp hf).pow_const p.toReal
  -- (2) The functions "`p`-th power of distance between `f` and the approximation" are uniformly
  -- bounded, at any given point, by `fun x => ‖f x - y₀‖ ^ p.toReal`
  have h_bound n :
    (fun x ↦ ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ^ p.toReal) ≤ᵐ[μ] (‖f · - y₀‖ₑ ^ p.toReal) :=
    .of_forall fun x => rpow_le_rpow (coe_mono (nnnorm_approxOn_le hf h₀ x n)) toReal_nonneg
  -- (3) The bounding function `fun x => ‖f x - y₀‖ ^ p.toReal` has finite integral
  have h_fin : (∫⁻ a : β, ‖f a - y₀‖ₑ ^ p.toReal ∂μ) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_ne_top hi).ne
  -- (4) The functions "`p`-th power of distance between `f` and the approximation" tend pointwise
  -- to zero
  have h_lim :
    ∀ᵐ a : β ∂μ, Tendsto (‖approxOn f hf s y₀ h₀ · a - f a‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    filter_upwards [hμ] with a ha
    have : Tendsto (fun n => (approxOn f hf s y₀ h₀ n) a - f a) atTop (𝓝 (f a - f a)) :=
      (tendsto_approxOn hf h₀ ha).sub tendsto_const_nhds
    convert! continuous_rpow_const.continuousAt.tendsto.comp (tendsto_coe.mpr this.nnnorm)
    simp [zero_rpow_of_pos hp]
  -- Then we apply the Dominated Convergence Theorem
  simpa using tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim
/-
**MeasureTheory.SimpleFunc.memLp_approxOn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：memLp_approxOn [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measur
able f) (hf : MemLp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s
] (hi₀ : MemLp (fun _ => y₀) p μ) (n : Nat) : MemLp (approxOn f fmeas s y₀ h₀ n)
 p μ
参数：fmeas : Measurable f；hf : MemLp f p μ；h₀ : y₀ in s；hi₀ : MemLp (fun _ => y₀) 
p μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.eLpNorm_norm`：eLpNorm_norm (f : α -> F) : eLpNorm (fun x =
> ‖f x‖) p μ = eLpNorm f p μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_add_lt_top`：eLpNorm_add_lt_top (hf : MemLp f p μ) 
(hg : MemLp g p μ) : eLpNorm (f + g) p μ < ∞
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
（共 33 条，此处仅展示前 30 条）
-/
theorem memLp_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : MemLp f p μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : MemLp (fun _ => y₀) p μ) (n : ℕ) : MemLp (approxOn f fmeas s y₀ h₀ n) p μ := by
  refine ⟨(approxOn f fmeas s y₀ h₀ n).aestronglyMeasurable, ?_⟩
  suffices eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ < ⊤ by
    have : MemLp (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ :=
      ⟨(approxOn f fmeas s y₀ h₀ n - const β y₀).aestronglyMeasurable, this⟩
    convert! eLpNorm_add_lt_top this hi₀
    ext x
    simp
  have hf' : MemLp (fun x => ‖f x - y₀‖) p μ := by
    have h_meas : Measurable fun x => ‖f x - y₀‖ := by
      simp only [← dist_eq_norm]
      fun_prop
    refine ⟨h_meas.aemeasurable.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_norm]
    convert! eLpNorm_add_lt_top hf hi₀.neg with x
    simp [sub_eq_add_neg]
  have : ∀ᵐ x ∂μ, ‖approxOn f fmeas s y₀ h₀ n x - y₀‖ ≤ ‖‖f x - y₀‖ + ‖f x - y₀‖‖ := by
    filter_upwards with x
    convert! norm_approxOn_y₀_le fmeas h₀ x n using 1
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  calc
    eLpNorm (fun x => approxOn f fmeas s y₀ h₀ n x - y₀) p μ ≤
        eLpNorm (fun x => ‖f x - y₀‖ + ‖f x - y₀‖) p μ :=
      eLpNorm_mono_ae this
    _ < ⊤ := eLpNorm_add_lt_top hf' hf'
/-
**MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：tendsto_approxOn_range_Lp_eLpNorm [BorelSpace E] {f : β -> E} (hp_ne_top :
 p != ∞) {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f union {
0} : Set E)] (hf : eLpNorm f p μ < ∞) : Tendsto (fun n => eLpNorm (⇑(approxOn f 
fmeas (range f union {0}) 0 (by simp) n) - f) p μ) atTop (𝓝 0)
参数：hp_ne_top : p != ∞；fmeas : Measurable f；range f union {0} : Set E；hf : eLpNor
m f p μ < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_Lp_eLpNorm`：tendsto_approxOn_L
p_eLpNorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E} 
{y₀ : E} (h₀ : y₀ in s) [SeparableSpace s]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem tendsto_approxOn_range_Lp_eLpNorm [BorelSpace E] {f : β → E} (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : eLpNorm f p μ < ∞) :
    Tendsto (fun n => eLpNorm (⇑(approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) - f) p μ)
      atTop (𝓝 0) := by
  refine tendsto_approxOn_Lp_eLpNorm fmeas _ hp_ne_top ?_ ?_
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf
/-
**MeasureTheory.SimpleFunc.memLp_approxOn_range** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：memLp_approxOn_range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : 
Measurable f) [SeparableSpace (range f union {0} : Set E)] (hf : MemLp f p μ) (n
 : Nat) : MemLp (approxOn f fmeas (range f union {0}) 0 (by simp) n) p μ
参数：fmeas : Measurable f；range f union {0} : Set E；hf : MemLp f p μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn`：memLp_approxOn [BorelSpace E] {
f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : MemLp f p μ) {s : Set E
} {y₀ : E} (h₀ : y₀ in s) [Se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
-/
theorem memLp_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : MemLp f p μ) (n : ℕ) :
    MemLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) p μ :=
  memLp_approxOn fmeas hf (y₀ := 0) (by simp) MemLp.zero n
/-
**MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：tendsto_approxOn_range_Lp [BorelSpace E] {f : β -> E} [hp : Fact (1 <= p)]
 (hp_ne_top : p != ∞) {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (ra
nge f union {0} : Set E)] (hf : MemLp f p μ) : Tendsto (fun n => (memLp_approxOn
_range fmeas hf n).toLp (approxOn f fmeas (range f union {0}) 0 (by simp) n)) at
Top (𝓝 (hf.toLp f))
参数：1 <= p；hp_ne_top : p != ∞；fmeas : Measurable f；range f union {0} : Set E；hf :
 MemLp f p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn_range`：memLp_approxOn_range [Bor
elSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (
range f union {0} : Set E)] (hf : M…
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm`：tendsto_appr
oxOn_range_Lp_eLpNorm [BorelSpace E] {f : β -> E} (hp_ne_top : p != ∞) {μ : Meas
ure β} (fmeas : Measurable f) [SeparableSpace (r…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_approxOn_range_Lp [BorelSpace E] {f : β → E} [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (range f ∪ {0} : Set E)]
    (hf : MemLp f p μ) :
    Tendsto
      (fun n =>
        (memLp_approxOn_range fmeas hf n).toLp (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n))
      atTop (𝓝 (hf.toLp f)) := by
  simpa only [Lp.tendsto_Lp_iff_tendsto_eLpNorm''] using
    tendsto_approxOn_range_Lp_eLpNorm hp_ne_top fmeas hf.2

/-- Any function in `ℒp` can be approximated by a simple function if `p < ∞`. -/
/-
**MeasureTheory.SimpleFunc._root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_
sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any function in `ℒp` can be approximated by a simple function if `p < ∞`.
-/
theorem _root_.MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt {E : Type*}
    [NormedAddCommGroup E] {f : β → E} {μ : Measure β} (hf : MemLp f p μ) (hp_ne_top : p ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : β →ₛ E, eLpNorm (f - ⇑g) p μ < ε ∧ MemLp g p μ := by
  borelize E
  let f' := hf.1.mk f
  rsuffices ⟨g, hg, g_mem⟩ : ∃ g : β →ₛ E, eLpNorm (f' - ⇑g) p μ < ε ∧ MemLp g p μ
  · refine ⟨g, ?_, g_mem⟩
    suffices eLpNorm (f - ⇑g) p μ = eLpNorm (f' - ⇑g) p μ by rwa [this]
    apply eLpNorm_congr_ae
    filter_upwards [hf.1.ae_eq_mk] with x hx
    simpa only [Pi.sub_apply, sub_left_inj] using hx
  have hf' : MemLp f' p μ := hf.ae_eq hf.1.ae_eq_mk
  have f'meas : Measurable f' := hf.1.measurable_mk
  have : SeparableSpace (range f' ∪ {0} : Set E) :=
    StronglyMeasurable.separableSpace_range_union_singleton hf.1.stronglyMeasurable_mk
  rcases ((tendsto_approxOn_range_Lp_eLpNorm hp_ne_top f'meas hf'.2).eventually <|
    gt_mem_nhds hε.bot_lt).exists with ⟨n, hn⟩
  rw [← eLpNorm_neg, neg_sub] at hn
  exact ⟨_, hn, memLp_approxOn_range f'meas hf' _⟩

end Lp

/-! ### L1 approximation by simple functions -/


section Integrable

variable [MeasurableSpace β]
variable [MeasurableSpace E] [NormedAddCommGroup E]

/-
**MeasureTheory.SimpleFunc.tendsto_approxOn_L1_enorm** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：tendsto_approxOn_L1_enorm [OpensMeasurableSpace E] {f : β -> E} (hf : Meas
urable f) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [SeparableSpace s] {μ : Measure β}
 (hμ : forallᵐ x ∂μ, f x in closure s) (hi : HasFiniteIntegral (fun x => f x - y
₀) μ) : Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ∂μ) atTop (𝓝 
0)
参数：hf : Measurable f；h₀ : y₀ in s；hμ : forallᵐ x ∂μ, f x in closure s；hi : HasFi
niteIntegral (fun x => f x - y₀) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_Lp_eLpNorm`：tendsto_approxOn_L
p_eLpNorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E} 
{y₀ : E} (h₀ : y₀ in s) [SeparableSpace s]…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
-/
theorem tendsto_approxOn_L1_enorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f)
    {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s] {μ : Measure β}
    (hμ : ∀ᵐ x ∂μ, f x ∈ closure s) (hi : HasFiniteIntegral (fun x => f x - y₀) μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f hf s y₀ h₀ n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
  simpa [eLpNorm_one_eq_lintegral_enorm] using!
    tendsto_approxOn_Lp_eLpNorm hf h₀ one_ne_top hμ
      (by simpa [eLpNorm_one_eq_lintegral_enorm] using! hi)
/-
**MeasureTheory.SimpleFunc.integrable_approxOn** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：integrable_approxOn [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : M
easurable f) (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ in s) [Separabl
eSpace s] (hi₀ : Integrable (fun _ => y₀) μ) (n : Nat) : Integrable (approxOn f 
fmeas s y₀ h₀ n) μ
参数：fmeas : Measurable f；hf : Integrable f μ；h₀ : y₀ in s；hi₀ : Integrable (fun _
 => y₀) μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn`：memLp_approxOn [BorelSpace E] {
f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : MemLp f p μ) {s : Set E
} {y₀ : E} (h₀ : y₀ in s) [Se…
-/
theorem integrable_approxOn [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    (hf : Integrable f μ) {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [SeparableSpace s]
    (hi₀ : Integrable (fun _ => y₀) μ) (n : ℕ) : Integrable (approxOn f fmeas s y₀ h₀ n) μ := by
  rw [← memLp_one_iff_integrable] at hf hi₀ ⊢
  exact memLp_approxOn fmeas hf h₀ hi₀ n
/-
**MeasureTheory.SimpleFunc.tendsto_approxOn_range_L1_enorm** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：tendsto_approxOn_range_L1_enorm [OpensMeasurableSpace E] {f : β -> E} {μ :
 Measure β} [SeparableSpace (range f union {0} : Set E)] (fmeas : Measurable f) 
(hf : Integrable f μ) : Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f union
 {0}) 0 (by simp) n x - f x‖ₑ ∂μ) atTop (𝓝 0)
参数：range f union {0} : Set E；fmeas : Measurable f；hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_L1_enorm`：tendsto_approxOn_L1_
enorm [OpensMeasurableSpace E] {f : β -> E} (hf : Measurable f) {s : Set E} {y₀ 
: E} (h₀ : y₀ in s) [SeparableSpace s] {…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_approxOn_range_L1_enorm [OpensMeasurableSpace E] {f : β → E} {μ : Measure β}
    [SeparableSpace (range f ∪ {0} : Set E)] (fmeas : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun n => ∫⁻ x, ‖approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ₑ ∂μ) atTop
      (𝓝 0) := by
  apply tendsto_approxOn_L1_enorm fmeas
  · filter_upwards with x using subset_closure (by simp)
  · simpa using hf.2
/-
**MeasureTheory.SimpleFunc.integrable_approxOn_range** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SimpleFunc`。
形式化陈述：integrable_approxOn_range [BorelSpace E] {f : β -> E} {μ : Measure β} (fme
as : Measurable f) [SeparableSpace (range f union {0} : Set E)] (hf : Integrable
 f μ) (n : Nat) : Integrable (approxOn f fmeas (range f union {0}) 0 (by simp) n
) μ
参数：fmeas : Measurable f；range f union {0} : Set E；hf : Integrable f μ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn`：integrable_approxOn [Borel
Space E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : Integrable f 
μ) {s : Set E} {y₀ : E} (h₀ : y₀ i…
· 使用定理 `MeasureTheory.integrable_zero`：integrable_zero (μ : Measure α) : Integra
ble (0 : α -> ε') μ
-/
theorem integrable_approxOn_range [BorelSpace E] {f : β → E} {μ : Measure β} (fmeas : Measurable f)
    [SeparableSpace (range f ∪ {0} : Set E)] (hf : Integrable f μ) (n : ℕ) :
    Integrable (approxOn f fmeas (range f ∪ {0}) 0 (by simp) n) μ :=
  integrable_approxOn fmeas hf _ (integrable_zero _ _ _) n

end Integrable

section SimpleFuncProperties

variable [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {μ : Measure α} {p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `MemLp f 0 μ` and `MemLp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `MemLp f p μ ↔ Integrable f μ ↔ f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞`.
-/


/-
**MeasureTheory.SimpleFunc.exists_forall_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：exists_forall_norm_le (f : α ->ₛ F) : exists C, forall x, ‖f x‖ <= C
参数：f : α ->ₛ F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.exists_forall_le`：exists_forall_le [Nonempty β]
 [Preorder β] [IsDirectedOrder β] (f : α ->ₛ β) : exists C, forall x, f x <= C
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R

--- 原说明 ---
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `
μ`:
- `MemLp f 0 μ` and `MemLp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `MemLp f p μ ↔ Integrable f μ ↔ f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) <
 ∞`.
-/
theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  exists_forall_le (f.map fun x => ‖x‖)
/-
**MeasureTheory.SimpleFunc.memLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.S
impleFunc`。
形式化陈述：memLp_zero (f : α ->ₛ E) (μ : Measure α) : MemLp f 0 μ
参数：f : α ->ₛ E；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_zero_iff_aestronglyMeasurable`：memLp_zero_iff_aestro
nglyMeasurable [TopologicalSpace ε] {f : α -> ε} : MemLp f 0 μ ↔ AEStronglyMeasu
rable f μ
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
-/
theorem memLp_zero (f : α →ₛ E) (μ : Measure α) : MemLp f 0 μ :=
  memLp_zero_iff_aestronglyMeasurable.mpr f.aestronglyMeasurable
/-
**MeasureTheory.SimpleFunc.memLp_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：memLp_top (f : α ->ₛ E) (μ : Measure α) : MemLp f ∞ μ
参数：f : α ->ₛ E；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.exists_forall_norm_le`：exists_forall_norm_le (f
 : α ->ₛ F) : exists C, forall x, ‖f x‖ <= C
· 使用定理 `MeasureTheory.memLp_top_of_bound`：memLp_top_of_bound {f : α -> E} (hf : 
AEStronglyMeasurable f μ) (C : Real) (hfC : forallᵐ x ∂μ, ‖f x‖ <= C) : MemLp f 
∞ μ
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem memLp_top (f : α →ₛ E) (μ : Measure α) : MemLp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  memLp_top_of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC
/-
**MeasureTheory.SimpleFunc.eLpNorm'_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {F : Type u_5} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup F] {p : ℝ}   (f : MeasureTheory.SimpleFunc α F) (μ : MeasureTheory
.Measure α),   MeasureTheory.eLpNorm' (⇑f) p μ = (∑ y ∈ f.range, ‖y‖ₑ ^ p * μ (⇑
f ⁻¹' {y})) ^ (1 / p)
参数：f : MeasureTheory.SimpleFunc α F；μ : MeasureTheory.Measure α；⇑f；∑ y ∈ f.range
, ‖y‖ₑ ^ p * μ (⇑f ⁻¹' {y})；1 / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `MeasureTheory.SimpleFunc.map_lintegral`：map_lintegral (g : β -> Real>=0∞
) (f : α ->ₛ β) : (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x})
-/
protected theorem eLpNorm'_eq {p : ℝ} (f : α →ₛ F) (μ : Measure α) :
    eLpNorm' f p μ = (∑ y ∈ f.range, ‖y‖ₑ ^ p * μ (f ⁻¹' {y})) ^ (1 / p) := by
  have h_map : (‖f ·‖ₑ ^ p) = f.map (‖·‖ₑ ^ p) := by simp; rfl
  rw [eLpNorm'_eq_lintegral_enorm, h_map, lintegral_eq_lintegral, map_lintegral]
/-
**MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_preimage_lt_top_of_memLp (hp_pos : p != 0) (hp_ne_top : p != ∞) (f
 : α ->ₛ E) (hf : MemLp f p μ) (y : E) (hy_ne : y != 0) : μ (f ⁻¹' {y}) < ∞
参数：hp_pos : p != 0；hp_ne_top : p != ∞；f : α ->ₛ E；hf : MemLp f p μ；y : E；hy_ne :
 y != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top`：of_lintegral_n
e_top {f : α ->ₛ Real>=0∞} (h : f.lintegral μ != ∞) : f.FinMeasSupp μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_eq_lintegral`：∀ {α : Type u_1} {m : M
easurableSpace α} (f : MeasureTheory.SimpleFunc α ENNReal) (μ : MeasureTheory.Me
asure α),   ∫⁻ (a : α), f a ∂μ = f.li…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top`：lintegral_r
pow_enorm_lt_top_of_eLpNorm_lt_top {f : α -> ε} (hp_ne_zero : p != 0) (hp_ne_top
 : p != ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a…
· 使用定理 `MeasureTheory.MemLp.eLpNorm_lt_top`：∀ {α : Type u_1} {ε : Type u_2} {m0 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε
]   [inst_1 : Topologica…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ENNReal.rpow_eq_zero_iff_of_pos`：rpow_eq_zero_iff_of_pos {x : Real>=0∞} 
{y : Real} (hy : 0 < y) : x ^ y = 0 ↔ x = 0
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.map_iff`：map_iff {g : β -> γ} (hg :
 forall {b}, g b = 0 ↔ b = 0) : (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero`：me
as_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y != 0) : μ (f
 ⁻¹' {y}) < ∞
-/
theorem measure_preimage_lt_top_of_memLp (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) (f : α →ₛ E)
    (hf : MemLp f p μ) (y : E) (hy_ne : y ≠ 0) : μ (f ⁻¹' {y}) < ∞ := by
  have h_fin : (f.map fun x ↦ ‖x‖ₑ ^ p.toReal).FinMeasSupp μ := by
    refine FinMeasSupp.of_lintegral_ne_top ?_
    rw [← (f.map fun x ↦ ‖x‖ₑ ^ p.toReal).lintegral_eq_lintegral μ]
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_pos hp_ne_top hf.eLpNorm_lt_top).ne
  have hf_fin : f.FinMeasSupp μ := by
    have {b : E} : (fun x ↦ ‖x‖ₑ ^ p.toReal) b = 0 ↔ b = 0 := by
      simp [rpow_eq_zero_iff_of_pos (toReal_pos hp_pos hp_ne_top)]
    rwa [FinMeasSupp.map_iff this] at h_fin
  exact hf_fin.meas_preimage_singleton_ne_zero hy_ne
/-
**MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：memLp_of_finite_measure_preimage (p : Real>=0∞) {f : α ->ₛ E} (hf : forall
 y, y != 0 -> μ (f ⁻¹' {y}) < ∞) : MemLp f p μ
参数：p : Real>=0∞；hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.memLp_zero_iff_aestronglyMeasurable`：memLp_zero_iff_aestro
nglyMeasurable [TopologicalSpace ε] {f : α -> ε} : MemLp f 0 μ ↔ AEStronglyMeasu
rable f μ
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `MeasureTheory.SimpleFunc.memLp_top`：memLp_top (f : α ->ₛ E) (μ : Measure
 α) : MemLp f ∞ μ
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `MeasureTheory.SimpleFunc.eLpNorm'_eq`：∀ {α : Type u_1} {F : Type u_5} [i
nst : MeasurableSpace α] [inst_1 : NormedAddCommGroup F] {p : ℝ}   (f : MeasureT
heory.SimpleFunc α F) (μ :…
· 使用定理 `ENNReal.rpow_lt_top_of_nonneg`：rpow_lt_top_of_nonneg {x : Real>=0∞} {y :
 Real} (hy0 : 0 <= y) (h : x != ⊤) : x ^ y < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.sum_lt_top`：∀ {α : Type u_1} {s : Finset α} {f : α → ENNReal}, ∑
 a ∈ s, f a < ⊤ ↔ ∀ a ∈ s, f a < ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem memLp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E}
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) : MemLp f p μ := by
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]; exact f.aestronglyMeasurable
  by_cases hp_top : p = ∞
  · rw [hp_top]; exact memLp_top f μ
  refine ⟨f.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top, f.eLpNorm'_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by simp) (ENNReal.sum_lt_top.mpr fun y _ => ?_).ne
  by_cases hy0 : y = 0
  · simp [hy0, ENNReal.toReal_pos hp0 hp_top]
  · refine ENNReal.mul_lt_top ?_ (hf y hy0)
    exact ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
/-
**MeasureTheory.SimpleFunc.memLp_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：memLp_iff {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) : MemLp f p
 μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
参数：hp_pos : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_memLp`：measure_preim
age_lt_top_of_memLp (hp_pos : p != 0) (hp_ne_top : p != ∞) (f : α ->ₛ E) (hf : M
emLp f p μ) (y : E) (hy_ne : y != 0) : μ (f ⁻¹'…
· 使用定理 `MeasureTheory.SimpleFunc.memLp_of_finite_measure_preimage`：memLp_of_fini
te_measure_preimage (p : Real>=0∞) {f : α ->ₛ E} (hf : forall y, y != 0 -> μ (f 
⁻¹' {y}) < ∞) : MemLp f p μ
-/
theorem memLp_iff {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_memLp hp_pos hp_ne_top f h, fun h =>
    memLp_of_finite_measure_preimage p h⟩
/-
**MeasureTheory.SimpleFunc.integrable_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：integrable_iff {f : α ->ₛ E} : Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻
¹' {y}) < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.SimpleFunc.memLp_iff`：memLp_iff {f : α ->ₛ E} (hp_pos : p 
!= 0) (hp_ne_top : p != ∞) : MemLp f p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem integrable_iff {f : α →ₛ E} : Integrable f μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ :=
  memLp_one_iff_integrable.symm.trans <| memLp_iff one_ne_zero ENNReal.coe_ne_top
/-
**MeasureTheory.SimpleFunc.memLp_iff_integrable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：memLp_iff_integrable {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) 
: MemLp f p μ ↔ Integrable f μ
参数：hp_pos : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.SimpleFunc.memLp_iff`：memLp_iff {f : α ->ₛ E} (hp_pos : p 
!= 0) (hp_ne_top : p != ∞) : MemLp f p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem memLp_iff_integrable {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ Integrable f μ :=
  (memLp_iff hp_pos hp_ne_top).trans integrable_iff.symm
/-
**MeasureTheory.SimpleFunc.memLp_iff_finMeasSupp** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：memLp_iff_finMeasSupp {f : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞)
 : MemLp f p μ ↔ f.FinMeasSupp μ
参数：hp_pos : p != 0；hp_ne_top : p != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.SimpleFunc.memLp_iff`：memLp_iff {f : α ->ₛ E} (hp_pos : p 
!= 0) (hp_ne_top : p != ∞) : MemLp f p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem memLp_iff_finMeasSupp {f : α →ₛ E} (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp f p μ ↔ f.FinMeasSupp μ :=
  (memLp_iff hp_pos hp_ne_top).trans finMeasSupp_iff.symm
/-
**MeasureTheory.SimpleFunc.integrable_iff_finMeasSupp** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SimpleFunc`。
形式化陈述：integrable_iff_finMeasSupp {f : α ->ₛ E} : Integrable f μ ↔ f.FinMeasSupp 
μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.SimpleFunc.finMeasSupp_iff`：finMeasSupp_iff : f.FinMeasSup
p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem integrable_iff_finMeasSupp {f : α →ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ :=
  integrable_iff.trans finMeasSupp_iff.symm
/-
**MeasureTheory.SimpleFunc.FinMeasSupp.integrable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.SimpleFunc.FinMeasSupp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {μ : MeasureTheory.Measure α}   {f : MeasureTheory.SimpleFunc α
 E}, f.FinMeasSupp μ → MeasureTheory.Integrable (⇑f) μ
参数：⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff_finMeasSupp`：integrable_iff_finM
easSupp {f : α ->ₛ E} : Integrable f μ ↔ f.FinMeasSupp μ
-/
theorem FinMeasSupp.integrable {f : α →ₛ E} (h : f.FinMeasSupp μ) : Integrable f μ :=
  integrable_iff_finMeasSupp.2 h
/-
**MeasureTheory.SimpleFunc.integrable_pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：integrable_pair {f : α ->ₛ E} {g : α ->ₛ F} : Integrable f μ -> Integrable
 g μ -> Integrable (pair f g) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.SimpleFunc.FinMeasSupp.pair`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} {m : MeasurableSpace α} [inst : Zero β] [inst_1 : Zero γ]   {μ
 : MeasureTheory.Measure α} {f …
-/
theorem integrable_pair {f : α →ₛ E} {g : α →ₛ F} :
    Integrable f μ → Integrable g μ → Integrable (pair f g) μ := by
  simpa only [integrable_iff_finMeasSupp] using FinMeasSupp.pair
/-
**MeasureTheory.SimpleFunc.memLp_of_isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：memLp_of_isFiniteMeasure (f : α ->ₛ E) (p : Real>=0∞) (μ : Measure α) [IsF
initeMeasure μ] : MemLp f p μ
参数：f : α ->ₛ E；p : Real>=0∞；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.exists_forall_norm_le`：exists_forall_norm_le (f
 : α ->ₛ F) : exists C, forall x, ‖f x‖ <= C
· 使用定理 `MeasureTheory.MemLp.of_bound`：∀ {α : Type u_1} {E : Type u_4} {m0 : Meas
urableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCo
mmGroup E] [Measur…
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem memLp_of_isFiniteMeasure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measure α) [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le
  MemLp.of_bound f.aestronglyMeasurable C <| Eventually.of_forall hfC

@[fun_prop]
/-
**MeasureTheory.SimpleFunc.integrable_of_isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SimpleFunc`。
形式化陈述：integrable_of_isFiniteMeasure [IsFiniteMeasure μ] (f : α ->ₛ E) : Integrab
le f μ
参数：f : α ->ₛ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.SimpleFunc.memLp_of_isFiniteMeasure`：memLp_of_isFiniteMeas
ure (f : α ->ₛ E) (p : Real>=0∞) (μ : Measure α) [IsFiniteMeasure μ] : MemLp f p
 μ
-/
theorem integrable_of_isFiniteMeasure [IsFiniteMeasure μ] (f : α →ₛ E) : Integrable f μ :=
  memLp_one_iff_integrable.mp (f.memLp_of_isFiniteMeasure 1 μ)
/-
**MeasureTheory.SimpleFunc.measure_preimage_lt_top_of_integrable** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_preimage_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) 
{x : E} (hx : x != 0) : μ (f ⁻¹' {x}) < ∞
参数：f : α ->ₛ E；hf : Integrable f μ；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) {x : E}
    (hx : x ≠ 0) : μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx
/-
**MeasureTheory.SimpleFunc.measure_support_lt_top_of_memLp** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_support_lt_top_of_memLp (f : α ->ₛ E) (hf : MemLp f p μ) (hp_ne_ze
ro : p != 0) (hp_ne_top : p != ∞) : μ (support f) < ∞
参数：f : α ->ₛ E；hf : MemLp f p μ；hp_ne_zero : p != 0；hp_ne_top : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.SimpleFunc.measure_support_lt_top`：measure_support_lt_top 
(f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞) : μ (support f) < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.memLp_iff`：memLp_iff {f : α ->ₛ E} (hp_pos : p 
!= 0) (hp_ne_top : p != ∞) : MemLp f p μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem measure_support_lt_top_of_memLp (f : α →ₛ E) (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : μ (support f) < ∞ :=
  f.measure_support_lt_top ((memLp_iff hp_ne_zero hp_ne_top).mp hf)
/-
**MeasureTheory.SimpleFunc.measure_support_lt_top_of_integrable** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_support_lt_top_of_integrable (f : α ->ₛ E) (hf : Integrable f μ) :
 μ (support f) < ∞
参数：f : α ->ₛ E；hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.SimpleFunc.measure_support_lt_top`：measure_support_lt_top 
(f : α ->ₛ β) (hf : forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞) : μ (support f) < ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
-/
theorem measure_support_lt_top_of_integrable (f : α →ₛ E) (hf : Integrable f μ) :
    μ (support f) < ∞ :=
  f.measure_support_lt_top (integrable_iff.mp hf)
/-
**MeasureTheory.SimpleFunc.measure_lt_top_of_memLp_indicator** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.SimpleFunc`。
形式化陈述：measure_lt_top_of_memLp_indicator (hp_pos : p != 0) (hp_ne_top : p != ∞) {
c : E} (hc : c != 0) {s : Set α} (hs : MeasurableSet s) (hcs : MemLp ((const α c
).piecewise s hs (const α 0)) p μ) : μ s < ⊤
参数：hp_pos : p != 0；hp_ne_top : p != ∞；hc : c != 0；hs : MeasurableSet s；hcs : Mem
Lp ((const α c).piecewise s hs (const α 0)) p μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.memLp_iff_finMeasSupp`：memLp_iff_finMeasSupp {f
 : α ->ₛ E} (hp_pos : p != 0) (hp_ne_top : p != ∞) : MemLp f p μ ↔ f.FinMeasSupp
 μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.support_indicator`：support_indicator [Zero β] {
s : Set α} (hs : MeasurableSet s) (f : α ->ₛ β) : Function.support (f.piecewise 
s hs (SimpleFunc.const α 0)) = s…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem measure_lt_top_of_memLp_indicator (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {c : E} (hc : c ≠ 0)
    {s : Set α} (hs : MeasurableSet s) (hcs : MemLp ((const α c).piecewise s hs (const α 0)) p μ) :
    μ s < ⊤ := by
  have : Function.support (const α c) = Set.univ := Function.support_const hc
  simpa only [memLp_iff_finMeasSupp hp_pos hp_ne_top, finMeasSupp_iff_support,
    support_indicator, Set.inter_univ, this] using hcs

end SimpleFuncProperties

end SimpleFunc

open SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AEEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : ℝ≥0∞)
  (μ : Measure α)

variable (E)

/-- `Lp.simpleFunc` is a subspace of Lp consisting of equivalence classes of an integrable simple
function. -/
/-
**MeasureTheory.Lp.simpleFunc** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：simpleFunc : AddSubgroup (Lp E p μ) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Lp.simpleFunc` is a subspace of Lp consisting of equivalence classes of an inte
grable simple
function.
-/
def simpleFunc : AddSubgroup (Lp E p μ) where
  carrier := { f : Lp E p μ | ∃ s : α →ₛ E, (AEEqFun.mk s s.aestronglyMeasurable : α →ₘ[μ] E) = f }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    use s + t
    simp only [← hs, ← ht, AEEqFun.mk_add_mk, AddSubgroup.coe_add,
      SimpleFunc.coe_add]
  neg_mem' := by
    rintro f ⟨s, hs⟩
    use -s
    simp only [← hs, AEEqFun.neg_mk, SimpleFunc.coe_neg, AddSubgroup.coe_neg]

variable {E p μ}

namespace simpleFunc

section Instances

/-! Simple functions in Lp space form a `NormedSpace`. -/



/-
**MeasureTheory.Lp.simpleFunc.eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp.si
mpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} {f g : ↥(MeasureT
heory.Lp.simpleFunc E p μ)}, ↑↑f = ↑↑g → f = g
参数：MeasureTheory.Lp.simpleFunc E p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2

--- 原说明 ---
Simple functions in Lp space form a `NormedSpace`.
-/
protected theorem eq' {f g : Lp.simpleFunc E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
  Subtype.ext ∘ Subtype.ext

/-! Implementation note:  If `Lp.simpleFunc E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simpleFunc E p μ`, would be
unnecessary.  But instead, `Lp.simpleFunc E p μ` is defined as an `AddSubgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
/-
**MeasureTheory.Lp.simpleFunc.as** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp.sim
pleFunc`。
形式化陈述：as it is (as of writing) used only in the construction of the Bochner inte
gral. - / protected theorem isBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp.
simpleFunc E p μ)
参数：as of writing；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/-
**MeasureTheory.Lp.simpleFunc.smul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp.s
impleFunc`。
形式化陈述：{α : Type u_1} →   {E : Type u_4} →     {𝕜 : Type u_6} →       [inst : Mea
surableSpace α] →         [inst_1 : NormedAddCommGroup E] →           {p : ENNRe
al} →             {μ : MeasureTheory.Measure α} →               [inst_2 : Normed
Ring 𝕜] →                 [inst_3 : _root_.Module 𝕜 E] → [IsBoundedSMul 𝕜 E] → S
Mul 𝕜 ↥(MeasureTheory.Lp.simpleFunc E p μ)
参数：MeasureTheory.Lp.simpleFunc E p μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a normed space, `Lp.simpleFunc E p μ` is a `SMul`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner i
ntegral.
-/
protected def smul : SMul 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨fun k f =>
    ⟨k • (f : Lp E p μ), by
      rcases f with ⟨f, ⟨s, hs⟩⟩
      use k • s
      apply Eq.trans (AEEqFun.smul_mk k s s.aestronglyMeasurable).symm _
      rw [hs]
      rfl⟩⟩

attribute [local instance] simpleFunc.smul

@[simp, norm_cast]
/-
**MeasureTheory.Lp.simpleFunc.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp.simpleFunc`。
形式化陈述：coe_smul (c : 𝕜) (f : Lp.simpleFunc E p μ) : ((c • f : Lp.simpleFunc E p μ
) : Lp E p μ) = c • (f : Lp E p μ)
参数：c : 𝕜；f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_smul (c : 𝕜) (f : Lp.simpleFunc E p μ) :
    ((c • f : Lp.simpleFunc E p μ) : Lp E p μ) = c • (f : Lp E p μ) :=
  rfl

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a module. Not declared as an
/-
**MeasureTheory.Lp.simpleFunc.as** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp.sim
pleFunc`。
形式化陈述：as it is (as of writing) used only in the construction of the Bochner inte
gral. - / protected theorem isBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp.
simpleFunc E p μ)
参数：as of writing；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/-
**MeasureTheory.Lp.simpleFunc.module** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Lp
.simpleFunc`。
形式化陈述：{α : Type u_1} →   {E : Type u_4} →     {𝕜 : Type u_6} →       [inst : Mea
surableSpace α] →         [inst_1 : NormedAddCommGroup E] →           {p : ENNRe
al} →             {μ : MeasureTheory.Measure α} →               [inst_2 : Normed
Ring 𝕜] →                 [inst_3 : _root_.Module 𝕜 E] →                   [IsBo
undedSMul 𝕜 E] → _root_.Module 𝕜 ↥(MeasureTheory.Lp.simpleFunc E p μ)
参数：MeasureTheory.Lp.simpleFunc E p μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a normed space, `Lp.simpleFunc E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner i
ntegral.
-/
protected def module : Module 𝕜 (Lp.simpleFunc E p μ) where
  one_smul f := by ext1; exact one_smul _ _
  mul_smul x y f := by ext1; exact mul_smul _ _ _
  smul_add x f g := by ext1; exact smul_add _ _ _
  smul_zero x := by ext1; exact smul_zero _
  add_smul x y f := by ext1; exact add_smul _ _ _
  zero_smul f := by ext1; exact zero_smul _ _

attribute [local instance] simpleFunc.module

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
/-
**MeasureTheory.Lp.simpleFunc.as** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp.sim
pleFunc`。
形式化陈述：as it is (as of writing) used only in the construction of the Bochner inte
gral. - / protected theorem isBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp.
simpleFunc E p μ)
参数：as of writing；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
/-
**MeasureTheory.Lp.simpleFunc.isBoundedSMul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} {𝕜 : Type u_6} [inst : MeasurableSpace α] 
[inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [i
nst_2 : NormedRing 𝕜] [inst_3 : _root_.Module 𝕜 E] [inst_4 : IsBoundedSMul 𝕜 E] 
  [inst_5 : Fact (1 ≤ p)], IsBoundedSMul 𝕜 ↥(MeasureTheory.Lp.simpleFunc E p μ)
参数：1 ≤ p；MeasureTheory.Lp.simpleFunc E p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_norm_smul_le`：IsBoundedSMul.of_norm_smul_le (h : forall
 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) : IsBoundedSMul α β
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖

--- 原说明 ---
If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared 
as an
instance as it is (as of writing) used only in the construction of the Bochner i
ntegral.
-/
protected theorem isBoundedSMul [Fact (1 ≤ p)] : IsBoundedSMul 𝕜 (Lp.simpleFunc E p μ) :=
  IsBoundedSMul.of_norm_smul_le fun r f => (norm_smul_le r (f : Lp E p μ) :)

attribute [local instance] simpleFunc.isBoundedSMul

/-- If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared as an
/-
**MeasureTheory.Lp.simpleFunc.as** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp.sim
pleFunc`。
形式化陈述：as it is (as of writing) used only in the construction of the Bochner inte
gral. - / protected theorem isBoundedSMul [Fact (1 <= p)] : IsBoundedSMul 𝕜 (Lp.
simpleFunc E p μ)
参数：as of writing；1 <= p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
@[instance_reducible]
/-
**MeasureTheory.Lp.simpleFunc.normedSpace** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.Lp.simpleFunc`。
形式化陈述：{α : Type u_1} →   {E : Type u_4} →     [inst : MeasurableSpace α] →      
 [inst_1 : NormedAddCommGroup E] →         {p : ENNReal} →           {μ : Measur
eTheory.Measure α} →             {𝕜 : Type u_7} →               [inst_2 : Normed
Field 𝕜] →                 [NormedSpace 𝕜 E] → [inst_4 : Fact (1 ≤ p)] → NormedS
pace 𝕜 ↥(MeasureTheory.Lp.simpleFunc E p μ)
参数：1 ≤ p；MeasureTheory.Lp.simpleFunc E p μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E` is a normed space, `Lp.simpleFunc E p μ` is a normed space. Not declared 
as an
instance as it is (as of writing) used only in the construction of the Bochner i
ntegral.
-/
protected def normedSpace {𝕜} [NormedField 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
    NormedSpace 𝕜 (Lp.simpleFunc E p μ) :=
  ⟨norm_smul_le (α := 𝕜) (β := Lp.simpleFunc E p μ)⟩

end Instances

attribute [local instance] simpleFunc.module simpleFunc.normedSpace simpleFunc.isBoundedSMul

section ToLp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `MemLp`. -/
/-
**MeasureTheory.Lp.simpleFunc._root_.MeasureTheory.SimpleFunc.toLp** 是 Mathlib 中
的一个缩写定义，位于命名空间 `MeasureTheory.Lp.simpleFunc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the equivalence class `[f]` of a simple function `f` satisfying `MemLp
`.
-/
abbrev _root_.MeasureTheory.SimpleFunc.toLp (f : α →ₛ E) (hf : MemLp f p μ) : Lp.simpleFunc E p μ :=
  ⟨hf.toLp f, ⟨f, rfl⟩⟩
/-
**MeasureTheory.Lp.simpleFunc.toLp_eq_toLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp.simpleFunc`。
形式化陈述：toLp_eq_toLp (f : α ->ₛ E) (hf : MemLp f p μ) : (toLp f hf : Lp E p μ) = h
f.toLp f
参数：f : α ->ₛ E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toLp_eq_toLp (f : α →ₛ E) (hf : MemLp f p μ) : (toLp f hf : Lp E p μ) = hf.toLp f :=
  rfl
/-
**MeasureTheory.Lp.simpleFunc.toLp_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp.simpleFunc`。
形式化陈述：toLp_eq_mk (f : α ->ₛ E) (hf : MemLp f p μ) : (toLp f hf : α ->ₘ[μ] E) = A
EEqFun.mk f f.aestronglyMeasurable
参数：f : α ->ₛ E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem toLp_eq_mk (f : α →ₛ E) (hf : MemLp f p μ) :
    (toLp f hf : α →ₘ[μ] E) = AEEqFun.mk f f.aestronglyMeasurable :=
  rfl
/-
**MeasureTheory.Lp.simpleFunc.toLp_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Lp.simpleFunc`。
形式化陈述：toLp_zero : toLp (0 : α ->ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {p :
 ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : TopologicalSpac
e ε] [inst_1 :…
-/
theorem toLp_zero : toLp (0 : α →ₛ E) MemLp.zero = (0 : Lp.simpleFunc E p μ) :=
  rfl
/-
**MeasureTheory.Lp.simpleFunc.toLp_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp.simpleFunc`。
形式化陈述：toLp_add (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) : toLp (f +
 g) (hf.add hg) = toLp f hf + toLp g hg
参数：f g : α ->ₛ E；hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem toLp_add (f g : α →ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f + g) (hf.add hg) = toLp f hf + toLp g hg :=
  rfl
/-
**MeasureTheory.Lp.simpleFunc.toLp_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp.simpleFunc`。
形式化陈述：toLp_neg (f : α ->ₛ E) (hf : MemLp f p μ) : toLp (-f) hf.neg = -toLp f hf
参数：f : α ->ₛ E；hf : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
-/
theorem toLp_neg (f : α →ₛ E) (hf : MemLp f p μ) : toLp (-f) hf.neg = -toLp f hf :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.Lp.simpleFunc.toLp_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp.simpleFunc`。
形式化陈述：toLp_sub (f g : α ->ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) : toLp (f -
 g) (hf.sub hg) = toLp f hf - toLp g hg
参数：f g : α ->ₛ E；hf : MemLp f p μ；hg : MemLp g p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.MemLp.add`：∀ {α : Type u_1} {ε : Type u_3} {m : Measurable
Space α} [inst : TopologicalSpace ε] [inst_1 : ESeminormedAddMonoid ε]   {p : EN
NReal} {μ : M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.MemLp.neg`：∀ {α : Type u_1} {E : Type u_4} {m0 : Measurabl
eSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGro
up E] {f : α …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4
} [inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ 
: MeasureTheory.Measure α} (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLp_sub (f g : α →ₛ E) (hf : MemLp f p μ) (hg : MemLp g p μ) :
    toLp (f - g) (hf.sub hg) = toLp f hf - toLp g hg := by
  simp only [sub_eq_add_neg, ← toLp_neg, ← toLp_add]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
/-
**MeasureTheory.Lp.simpleFunc.toLp_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Lp.simpleFunc`。
形式化陈述：toLp_smul (f : α ->ₛ E) (hf : MemLp f p μ) (c : 𝕜) : toLp (c • f) (hf.cons
t_smul c) = c • toLp f hf
参数：f : α ->ₛ E；hf : MemLp f p μ；c : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.const_smul`：∀ {α : Type u_1} {F : Type u_2} {m : Mea
surableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddC
ommGroup F] {f : α →…
-/
theorem toLp_smul (f : α →ₛ E) (hf : MemLp f p μ) (c : 𝕜) :
    toLp (c • f) (hf.const_smul c) = c • toLp f hf :=
  rfl

nonrec theorem norm_toLp [Fact (1 ≤ p)] (f : α →ₛ E) (hf : MemLp f p μ) :
    ‖toLp f hf‖ = ENNReal.toReal (eLpNorm f p μ) :=
  norm_toLp f hf

end ToLp

section ToSimpleFunc

/-- Find a representative of a `Lp.simpleFunc`. -/
/-
**MeasureTheory.Lp.simpleFunc.toSimpleFunc** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.Lp.simpleFunc`。
形式化陈述：toSimpleFunc (f : Lp.simpleFunc E p μ) : α ->ₛ E
参数：f : Lp.simpleFunc E p μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Find a representative of a `Lp.simpleFunc`.
-/
def toSimpleFunc (f : Lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2

/-- `(toSimpleFunc f)` is measurable. -/
@[fun_prop]
/-
**MeasureTheory.Lp.simpleFunc.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Measura
bleSpace E] (f : ↥(MeasureTheory.Lp.simpleFunc E p μ)),   Measurable ⇑(MeasureTh
eory.Lp.simpleFunc.toSimpleFunc f)
参数：f : ↥(MeasureTheory.Lp.simpleFunc E p μ)；MeasureTheory.Lp.simpleFunc.toSimple
Func f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f

--- 原说明 ---
`(toSimpleFunc f)` is measurable.
-/
protected theorem measurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    Measurable (toSimpleFunc f) :=
  (toSimpleFunc f).measurable
/-
**MeasureTheory.Lp.simpleFunc.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} (f : ↥(MeasureThe
ory.Lp.simpleFunc E p μ)),   MeasureTheory.StronglyMeasurable ⇑(MeasureTheory.Lp
.simpleFunc.toSimpleFunc f)
参数：f : ↥(MeasureTheory.Lp.simpleFunc E p μ)；MeasureTheory.Lp.simpleFunc.toSimple
Func f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
-/
protected theorem stronglyMeasurable (f : Lp.simpleFunc E p μ) :
    StronglyMeasurable (toSimpleFunc f) :=
  (toSimpleFunc f).stronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.Lp.simpleFunc.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Measura
bleSpace E] (f : ↥(MeasureTheory.Lp.simpleFunc E p μ)),   AEMeasurable (⇑(Measur
eTheory.Lp.simpleFunc.toSimpleFunc f)) μ
参数：f : ↥(MeasureTheory.Lp.simpleFunc E p μ)；⇑(MeasureTheory.Lp.simpleFunc.toSimp
leFunc f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Lp.simpleFunc.measurable`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
-/
protected theorem aemeasurable [MeasurableSpace E] (f : Lp.simpleFunc E p μ) :
    AEMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.measurable f).aemeasurable
/-
**MeasureTheory.Lp.simpleFunc.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} (f : ↥(MeasureThe
ory.Lp.simpleFunc E p μ)),   MeasureTheory.AEStronglyMeasurable (⇑(MeasureTheory
.Lp.simpleFunc.toSimpleFunc f)) μ
参数：f : ↥(MeasureTheory.Lp.simpleFunc E p μ)；⇑(MeasureTheory.Lp.simpleFunc.toSimp
leFunc f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.Lp.simpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {E : Ty
pe u_4} [inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}
   {μ : MeasureTheory.Measure α} (f …
-/
protected theorem aestronglyMeasurable (f : Lp.simpleFunc E p μ) :
    AEStronglyMeasurable (toSimpleFunc f) μ :=
  (simpleFunc.stronglyMeasurable f).aestronglyMeasurable
/-
**MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp.simpleFunc`。
形式化陈述：toSimpleFunc_eq_toFun (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
参数：f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.aestronglyMeasurable`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   (f : MeasureTheory.Simp…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem toSimpleFunc_eq_toFun (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f :=
  show ⇑(toSimpleFunc f) =ᵐ[μ] ⇑(f : α →ₘ[μ] E) by
    convert! (AEEqFun.coeFn_mk (toSimpleFunc f) (toSimpleFunc f).aestronglyMeasurable).symm using 2
    exact (Classical.choose_spec f.2).symm

/-- `toSimpleFunc f` satisfies the predicate `MemLp`. -/
/-
**MeasureTheory.Lp.simpleFunc.memLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp.
simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} (f : ↥(MeasureThe
ory.Lp.simpleFunc E p μ)),   MeasureTheory.MemLp (⇑(MeasureTheory.Lp.simpleFunc.
toSimpleFunc f)) p μ
参数：f : ↥(MeasureTheory.Lp.simpleFunc E p μ)；⇑(MeasureTheory.Lp.simpleFunc.toSimp
leFunc f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.ae_eq`：∀ {α : Type u_1} {ε : Type u_2} {m0 : Measura
bleSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α} [inst : ENorm ε]   [inst
_1 : Topologica…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Lp.mem_Lp_iff_memLp`：mem_Lp_iff_memLp {f : α ->ₘ[μ] E} : f
 in Lp E p μ ↔ MemLp f p μ
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
`toSimpleFunc f` satisfies the predicate `MemLp`.
-/
protected theorem memLp (f : Lp.simpleFunc E p μ) : MemLp (toSimpleFunc f) p μ :=
  MemLp.ae_eq (toSimpleFunc_eq_toFun f).symm <| mem_Lp_iff_memLp.mp (f : Lp E p μ).2
/-
**MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：toLp_toSimpleFunc (f : Lp.simpleFunc E p μ) : toLp (toSimpleFunc f) (simpl
eFunc.memLp f) = f
参数：f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.simpleFunc.eq'`：∀ {α : Type u_1} {E : Type u_4} [inst :
 MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measure
Theory.Measure α} {f …
· 使用定理 `MeasureTheory.Lp.simpleFunc.memLp`：∀ {α : Type u_1} {E : Type u_4} [inst
 : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measu
reTheory.Measure α} (f …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem toLp_toSimpleFunc (f : Lp.simpleFunc E p μ) :
    toLp (toSimpleFunc f) (simpleFunc.memLp f) = f :=
  simpleFunc.eq' (Classical.choose_spec f.2)
/-
**MeasureTheory.Lp.simpleFunc.toSimpleFunc_toLp** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：toSimpleFunc_toLp (f : α ->ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f
 hfi) =ᵐ[μ] f
参数：f : α ->ₛ E；hfi : MemLp f p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.mk_eq_mk`：mk_eq_mk {f g : α -> β} {hf hg} : (mk f 
hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem toSimpleFunc_toLp (f : α →ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f := by
  rw [← AEEqFun.mk_eq_mk]; exact Classical.choose_spec (toLp f hfi).2

variable (E μ)
/-
**MeasureTheory.Lp.simpleFunc.zero_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：zero_toSimpleFunc : toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem zero_toSimpleFunc : toSimpleFunc (0 : Lp.simpleFunc E p μ) =ᵐ[μ] 0 := by
  filter_upwards [toSimpleFunc_eq_toFun (0 : Lp.simpleFunc E p μ),
    Lp.coeFn_zero E 1 μ] with _ h₁ _
  rwa [h₁]

variable {E μ}
/-
**MeasureTheory.Lp.simpleFunc.add_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Lp.simpleFunc`。
形式化陈述：add_toSimpleFunc (f g : Lp.simpleFunc E p μ) : toSimpleFunc (f + g) =ᵐ[μ] 
toSimpleFunc f + toSimpleFunc g
参数：f g : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem add_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f + g) =ᵐ[μ] toSimpleFunc f + toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f + g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_add (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_add, Pi.add_apply]
  iterate 4 intro h; rw [h]
/-
**MeasureTheory.Lp.simpleFunc.neg_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Lp.simpleFunc`。
形式化陈述：neg_toSimpleFunc (f : Lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSi
mpleFunc f
参数：f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_neg`：coeFn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem neg_toSimpleFunc (f : Lp.simpleFunc E p μ) : toSimpleFunc (-f) =ᵐ[μ] -toSimpleFunc f := by
  filter_upwards [toSimpleFunc_eq_toFun (-f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_neg (f : Lp E p μ)] with _
  simp only [Pi.neg_apply, AddSubgroup.coe_neg]
  repeat intro h; rw [h]
/-
**MeasureTheory.Lp.simpleFunc.sub_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Lp.simpleFunc`。
形式化陈述：sub_toSimpleFunc (f g : Lp.simpleFunc E p μ) : toSimpleFunc (f - g) =ᵐ[μ] 
toSimpleFunc f - toSimpleFunc g
参数：f g : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem sub_toSimpleFunc (f g : Lp.simpleFunc E p μ) :
    toSimpleFunc (f - g) =ᵐ[μ] toSimpleFunc f - toSimpleFunc g := by
  filter_upwards [toSimpleFunc_eq_toFun (f - g), toSimpleFunc_eq_toFun f,
    toSimpleFunc_eq_toFun g, Lp.coeFn_sub (f : Lp E p μ) g] with _
  simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  repeat' intro h; rw [h]

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
/-
**MeasureTheory.Lp.simpleFunc.smul_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：smul_toSimpleFunc (k : 𝕜) (f : Lp.simpleFunc E p μ) : toSimpleFunc (k • f)
 =ᵐ[μ] k • ⇑(toSimpleFunc f)
参数：k : 𝕜；f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_eq_toFun`：toSimpleFunc_eq_toFun
 (f : Lp.simpleFunc E p μ) : toSimpleFunc f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem smul_toSimpleFunc (k : 𝕜) (f : Lp.simpleFunc E p μ) :
    toSimpleFunc (k • f) =ᵐ[μ] k • ⇑(toSimpleFunc f) := by
  filter_upwards [toSimpleFunc_eq_toFun (k • f), toSimpleFunc_eq_toFun f,
    Lp.coeFn_smul k (f : Lp E p μ)] with _
  simp only [Pi.smul_apply, coe_smul]
  repeat intro h; rw [h]
/-
**MeasureTheory.Lp.simpleFunc.norm_toSimpleFunc** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：norm_toSimpleFunc [Fact (1 <= p)] (f : Lp.simpleFunc E p μ) : ‖f‖ = ENNRea
l.toReal (eLpNorm (toSimpleFunc f) p μ)
参数：1 <= p；f : Lp.simpleFunc E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.simpleFunc.memLp`：∀ {α : Type u_1} {E : Type u_4} [inst
 : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measu
reTheory.Measure α} (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc`：toLp_toSimpleFunc (f : Lp
.simpleFunc E p μ) : toLp (toSimpleFunc f) (simpleFunc.memLp f) = f
· 使用定理 `MeasureTheory.Lp.simpleFunc.norm_toLp`：∀ {α : Type u_1} {E : Type u_4} [
inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : M
easureTheory.Measure α} [in…
-/
theorem norm_toSimpleFunc [Fact (1 ≤ p)] (f : Lp.simpleFunc E p μ) :
    ‖f‖ = ENNReal.toReal (eLpNorm (toSimpleFunc f) p μ) := by
  simpa [toLp_toSimpleFunc] using norm_toLp (toSimpleFunc f) (simpleFunc.memLp f)

end ToSimpleFunc

section Induction

variable (p) in
/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
/-
**MeasureTheory.Lp.simpleFunc.indicatorConst** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.Lp.simpleFunc`。
形式化陈述：indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c : E)
 : Lp.simpleFunc E p μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic function of a finite-measure measurable set `s`, as an `Lp` s
imple function.
-/
def indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Lp.simpleFunc E p μ :=
  toLp ((SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0))
    (memLp_indicator_const p hs c (Or.inr hμs))

@[simp]
/-
**MeasureTheory.Lp.simpleFunc.coe_indicatorConst** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp.simpleFunc`。
形式化陈述：coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) (c 
: E) : (↑(indicatorConst p hs hμs c) : Lp E p μ) = indicatorConstLp p hs hμs c
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem coe_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    (↑(indicatorConst p hs hμs c) : Lp E p μ) = indicatorConstLp p hs hμs c :=
  rfl
/-
**MeasureTheory.Lp.simpleFunc.toSimpleFunc_indicatorConst** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Lp.simpleFunc`。
形式化陈述：toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s 
!= ∞) (c : E) : toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ] (SimpleFunc.const
 _ c).piecewise s hs (SimpleFunc.const _ 0)
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.simpleFunc.toSimpleFunc_toLp`：toSimpleFunc_toLp (f : α 
->ₛ E) (hfi : MemLp f p μ) : toSimpleFunc (toLp f hfi) =ᵐ[μ] f
-/
theorem toSimpleFunc_indicatorConst {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    toSimpleFunc (indicatorConst p hs hμs c) =ᵐ[μ]
      (SimpleFunc.const _ c).piecewise s hs (SimpleFunc.const _ 0) :=
  Lp.simpleFunc.toSimpleFunc_toLp _ _

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_elim]
/-
**MeasureTheory.Lp.simpleFunc.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α},   p ≠ 0 →     p 
≠ ⊤ →       ∀ {P : ↥(MeasureTheory.Lp.simpleFunc E p μ) → Prop},         (∀ (c :
 E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ⊤),             P (MeasureTh
eory.Lp.simpleFunc.indicatorConst p hs ⋯ c)) →           (∀ ⦃f g : MeasureTheory
.SimpleFunc α E⦄ (hf : MeasureTheory.MemLp (⇑f) p μ)               (hg : Measure
Theory.MemLp (⇑g) p μ),               Disjoint (Function.support ⇑f) (Function.s
upport ⇑g) →                 P (f.toLp hf) → P (g.toLp hg) → P (f.toLp hf + g.to
Lp hg)) →             ∀ (f : ↥(MeasureTheory.Lp.simpleFunc E p μ)), P f
参数：MeasureTheory.Lp.simpleFunc E p μ；∀ (c : E) {s : Set α} (hs : MeasurableSet s
) (hμs : μ s < ⊤),             P (MeasureTheory.Lp.simpleFunc.indicatorConst p h
s ⋯ c)；∀ ⦃f g : MeasureTheory.SimpleFunc α E⦄ (hf : MeasureTheory.MemLp (⇑f) p μ
)               (hg : MeasureTheory.MemLp (⇑g) p μ),               Disjoint (Fun
ction.support ⇑f) (Function.support ⇑g) →                 P (f.toLp hf) → P (g.t
oLp hg) → P (f.toLp hf + g.toLp hg)；f : ↥(MeasureTheory.Lp.simpleFunc E p μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.MemLp.toLp.congr_simp`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f f_1 :…
· 使用定理 `MeasureTheory.SimpleFunc.piecewise.congr_simp`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] (s s_1 : Set α) (e_s : s = s_1) (hs : Measurab
leSet s)   (f f_1 : MeasureTheory.S…
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `MeasureTheory.indicatorConstLp_empty`：indicatorConstLp_empty : indicator
ConstLp p MeasurableSet.empty (by simp : μ ∅ != ∞) c = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.SimpleFunc.measure_lt_top_of_memLp_indicator`：measure_lt_t
op_of_memLp_indicator (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 
0) {s : Set α} (hs : MeasurableSet s) (hcs : Mem…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.memLp_add_of_disjoint`：memLp_add_of_disjoint {f g : α -> E
} (h : Disjoint (support f) (support g)) (hf : StronglyMeasurable f) (hg : Stron
glyMeasurable g) : MemLp …
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.Lp.simpleFunc.memLp`：∀ {α : Type u_1} {E : Type u_4} [inst
 : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measu
reTheory.Measure α} (f …
· 使用定理 `MeasureTheory.Lp.simpleFunc.toLp_toSimpleFunc`：toLp_toSimpleFunc (f : Lp
.simpleFunc E p μ) : toLp (toSimpleFunc f) (simpleFunc.memLp f) = f

--- 原说明 ---
To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it s
uffices to show
that the property holds for (multiples of) characteristic functions of finite-me
asure measurable
sets and is closed under addition (of functions with disjoint support).
-/
protected theorem induction (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ∞) {P : Lp.simpleFunc E p μ → Prop}
    (indicatorConst :
      ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
        P (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add :
      ∀ ⦃f g : α →ₛ E⦄,
        ∀ hf : MemLp f p μ,
          ∀ hg : MemLp g p μ,
            Disjoint (support f) (support g) →
              P (toLp f hf) →
                P (toLp g hg) → P (toLp f hf + toLp g hg))
    (f : Lp.simpleFunc E p μ) : P f := by
  suffices ∀ f : α →ₛ E, ∀ hf : MemLp f p μ, P (toLp f hf) by
    rw [← toLp_toSimpleFunc f]
    apply this
  clear f
  apply SimpleFunc.induction
  · intro c s hs hf
    by_cases hc : c = 0
    · convert! indicatorConst 0 MeasurableSet.empty (by simp) using 1
      ext1
      simp [hc]
    exact indicatorConst c hs
      (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs hf)
  · intro f g hfg hf hg hfg'
    obtain ⟨hf', hg'⟩ : MemLp f p μ ∧ MemLp g p μ :=
      (memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable).mp hfg'
    exact add hf' hg' hfg (hf hf') (hg hg')

end Induction

section CoeToLp

variable [Fact (1 ≤ p)]

@[fun_prop]
/-
**MeasureTheory.Lp.simpleFunc.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Fact (1
 ≤ p)], UniformContinuous Subtype.val
参数：1 ≤ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
protected theorem uniformContinuous : UniformContinuous ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  uniformContinuous_comap
/-
**MeasureTheory.Lp.simpleFunc.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Lp.simpleFunc`。
形式化陈述：isUniformEmbedding : IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E
 p μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformEmbedding_comap`：isUniformEmbedding_comap {α : Type*} {β : Type
*} {f : α -> β} [u : UniformSpace β] (hf : Function.Injective f) : @IsUniformEmb
edding α β (Un…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma isUniformEmbedding : IsUniformEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  isUniformEmbedding_comap Subtype.val_injective
/-
**MeasureTheory.Lp.simpleFunc.isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp.simpleFunc`。
形式化陈述：isUniformInducing : IsUniformInducing ((↑) : Lp.simpleFunc E p μ -> Lp E p
 μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformEmbedding.isUniformInducing`：IsUniformEmbedding.isUniformInduci
ng {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformInducing f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.Lp.simpleFunc.isUniformEmbedding`：isUniformEmbedding : IsU
niformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
-/
theorem isUniformInducing : IsUniformInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  simpleFunc.isUniformEmbedding.isUniformInducing
/-
**MeasureTheory.Lp.simpleFunc.isDenseEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Lp.simpleFunc`。
形式化陈述：isDenseEmbedding (hp_ne_top : p != ∞) : IsDenseEmbedding ((↑) : Lp.simpleF
unc E p μ -> Lp E p μ)
参数：hp_ne_top : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isDenseEmbedding`：IsUniformEmbedding.isDenseEmbedding
 {f : α -> β} (h : IsUniformEmbedding f) (hd : DenseRange f) : IsDenseEmbedding 
f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.Lp.simpleFunc.isUniformEmbedding`：isUniformEmbedding : IsU
niformEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_seq_limit`：mem_closure_iff_seq_limit [FrechetUrysohnSpac
e X] {s : Set X} {a : X} : a in closure s ↔ exists x : Nat -> X, (forall n : Nat
, x n in s) ∧ T…
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn_range`：memLp_approxOn_range [Bor
elSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [SeparableSpace (
range f union {0} : Set E)] (hf : M…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toLp_coeFn`：toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ
) : hf.toLp f = f
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp`：tendsto_approxOn_ran
ge_Lp [BorelSpace E] {f : β -> E} [hp : Fact (1 <= p)] (hp_ne_top : p != ∞) {μ :
 Measure β} (fmeas : Measurable f) [Sepa…
-/
lemma isDenseEmbedding (hp_ne_top : p ≠ ∞) :
    IsDenseEmbedding ((↑) : Lp.simpleFunc E p μ → Lp E p μ) := by
  borelize E
  apply simpleFunc.isUniformEmbedding.isDenseEmbedding
  intro f
  rw [mem_closure_iff_seq_limit]
  have hfi' : MemLp f p μ := Lp.memLp f
  have : SeparableSpace (range f ∪ {0} : Set E) :=
    (Lp.stronglyMeasurable f).separableSpace_range_union_singleton
  refine
    ⟨fun n =>
      toLp
        (SimpleFunc.approxOn f (Lp.stronglyMeasurable f).measurable (range f ∪ {0}) 0 _ n)
        (SimpleFunc.memLp_approxOn_range (Lp.stronglyMeasurable f).measurable hfi' n),
      fun n => mem_range_self _, ?_⟩
  convert! SimpleFunc.tendsto_approxOn_range_Lp hp_ne_top (Lp.stronglyMeasurable f).measurable hfi'
  rw [toLp_coeFn f (Lp.memLp f)]
/-
**MeasureTheory.Lp.simpleFunc.isDenseInducing** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Fact (1
 ≤ p)], p ≠ ⊤ → IsDenseInducing Subtype.val
参数：1 ≤ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDenseEmbedding.isDenseInducing`：isDenseInducing (de : IsDenseEmbedding
 e) : IsDenseInducing e
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`：isDenseEmbedding (hp_ne_to
p : p != ∞) : IsDenseEmbedding ((↑) : Lp.simpleFunc E p μ -> Lp E p μ)
-/
protected theorem isDenseInducing (hp_ne_top : p ≠ ∞) :
    IsDenseInducing ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.isDenseEmbedding hp_ne_top).isDenseInducing
/-
**MeasureTheory.Lp.simpleFunc.denseRange** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp.simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Fact (1
 ≤ p)], p ≠ ⊤ → DenseRange Subtype.val
参数：1 ≤ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.dense`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] [inst_1 : TopologicalSpace β] {i : α → β},   IsDenseInducing i → Dens
eRange i
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.simpleFunc.isDenseInducing`：∀ {α : Type u_1} {E : Type 
u_4} [inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   
{μ : MeasureTheory.Measure α} [in…
-/
protected theorem denseRange (hp_ne_top : p ≠ ∞) :
    DenseRange ((↑) : Lp.simpleFunc E p μ → Lp E p μ) :=
  (simpleFunc.isDenseInducing hp_ne_top).dense
/-
**MeasureTheory.Lp.simpleFunc.dense** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp.
simpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [inst_2 : Fact (1
 ≤ p)], p ≠ ⊤ → Dense ↑(MeasureTheory.Lp.simpleFunc E p μ)
参数：1 ≤ p；MeasureTheory.Lp.simpleFunc E p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
-/
protected theorem dense (hp_ne_top : p ≠ ∞) : Dense (Lp.simpleFunc E p μ : Set (Lp E p μ)) := by
  simpa only [denseRange_subtype_val] using! simpleFunc.denseRange (E := E) (μ := μ) hp_ne_top

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable (α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
/-
**MeasureTheory.Lp.simpleFunc.coeToLp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.L
p.simpleFunc`。
形式化陈述：coeToLp : Lp.simpleFunc E p μ ->L[𝕜] Lp E p μ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of Lp simple functions into Lp functions, as a continuous linear m
ap.
-/
def coeToLp : Lp.simpleFunc E p μ →L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simpleFunc E p μ) with
    map_smul' := fun _ _ => rfl }

end CoeToLp

section Order

variable {G : Type*} [NormedAddCommGroup G]

/-
**MeasureTheory.Lp.simpleFunc.coeFn_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Lp.simpleFunc`。
形式化陈述：coeFn_le [PartialOrder G] (f g : Lp.simpleFunc G p μ) : (f : α -> G) <=ᵐ[μ
] g ↔ f <= g
参数：f g : Lp.simpleFunc G p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `MeasureTheory.Lp.coeFn_le`：coeFn_le (f g : Lp E p μ) : f <=ᵐ[μ] g ↔ f <=
 g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coeFn_le [PartialOrder G] (f g : Lp.simpleFunc G p μ) : (f : α → G) ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← Lp.coeFn_le]

variable (p μ G)
/-
**MeasureTheory.Lp.simpleFunc.coeFn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Lp.simpleFunc`。
形式化陈述：coeFn_zero : (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α -> G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.coeFn_zero`：coeFn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0
-/
theorem coeFn_zero : (0 : Lp.simpleFunc G p μ) =ᵐ[μ] (0 : α → G) :=
  Lp.coeFn_zero _ _ _

variable {p μ G}

variable [PartialOrder G]
/-
**MeasureTheory.Lp.simpleFunc.coeFn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp.simpleFunc`。
形式化陈述：coeFn_nonneg (f : Lp.simpleFunc G p μ) : (0 : α -> G) <=ᵐ[μ] f ↔ 0 <= f
参数：f : Lp.simpleFunc G p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `MeasureTheory.Lp.coeFn_nonneg`：coeFn_nonneg (f : Lp E p μ) : 0 <=ᵐ[μ] f 
↔ 0 <= f
· 使用定理 `AddSubmonoid.coe_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : Add
Submonoid M), ↑0 = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coeFn_nonneg (f : Lp.simpleFunc G p μ) : (0 : α → G) ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← Subtype.coe_le_coe, Lp.coeFn_nonneg, AddSubmonoid.coe_zero]
/-
**MeasureTheory.Lp.simpleFunc.exists_simpleFunc_nonneg_ae_eq** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Lp.simpleFunc`。
形式化陈述：exists_simpleFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 <= f) : e
xists f' : α ->ₛ G, 0 <= f' ∧ f =ᵐ[μ] f'
参数：hf : 0 <= f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Set.indicator_apply_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preo
rder M] [inst_1 : Zero M] {s : Set α} {f : α → M} {a : α},   (a ∈ s → 0 ≤ f a) →
 0 ≤ s.indicator…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
-/
theorem exists_simpleFunc_nonneg_ae_eq {f : Lp.simpleFunc G p μ} (hf : 0 ≤ f) :
    ∃ f' : α →ₛ G, 0 ≤ f' ∧ f =ᵐ[μ] f' := by
  rcases f with ⟨⟨f, hp⟩, g, (rfl : _ = f)⟩
  change 0 ≤ᵐ[μ] g at hf
  classical
  refine ⟨g.map ({x : G | 0 ≤ x}.piecewise id 0), fun x ↦ ?_, (AEEqFun.coeFn_mk _ _).trans ?_⟩
  · simpa using! Set.indicator_apply_nonneg id
  · filter_upwards [hf] with x (hx : 0 ≤ g x)
    simpa using! Set.indicator_of_mem hx id |>.symm

variable (p μ G)

/-- Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp. -/
/-
**MeasureTheory.Lp.simpleFunc.coeSimpleFuncNonnegToLpNonneg** 是 Mathlib 中的一个定义，位
于命名空间 `MeasureTheory.Lp.simpleFunc`。
形式化陈述：coeSimpleFuncNonnegToLpNonneg : { g : Lp.simpleFunc G p μ // 0 <= g } -> {
 g : Lp G p μ // 0 <= g }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from nonnegative simple functions of Lp to nonnegative functions of Lp.
-/
def coeSimpleFuncNonnegToLpNonneg :
    { g : Lp.simpleFunc G p μ // 0 ≤ g } → { g : Lp G p μ // 0 ≤ g } := fun g => ⟨g, g.2⟩
/-
**MeasureTheory.Lp.simpleFunc.denseRange_coeSimpleFuncNonnegToLpNonneg** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.Lp.simpleFunc`。
形式化陈述：denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 <= p)] (hp_ne_top :
 p != ∞) : DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G)
参数：1 <= p；hp_ne_top : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_seq_limit`：mem_closure_iff_seq_limit [FrechetUrysohnSpac
e X] {s : Set X} {a : X} : a in closure s ↔ exists x : Nat -> X, (forall n : Nat
, x n in s) ∧ T…
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `TopologicalSpace.IsSeparable.separableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] {s : Set X},   Topo
logicalSpace.IsSeparable s → Topo…
· 使用定理 `TopologicalSpace.IsSeparable.mono`：∀ {α : Type u} [t : TopologicalSpace 
α] {s u : Set α},   TopologicalSpace.IsSeparable s → u ⊆ s → TopologicalSpace.Is
Separable u
· 使用定理 `TopologicalSpace.IsSeparable.union`：∀ {α : Type u} [t : TopologicalSpace
 α] {s u : Set α},   TopologicalSpace.IsSeparable s → TopologicalSpace.IsSeparab
le u → TopologicalSpace.…
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `Set.Finite.isSeparable`：∀ {α : Type u} [t : TopologicalSpace α] {s : Set
 α}, s.Finite → TopologicalSpace.IsSeparable s
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.SimpleFunc.approxOn_mem`：approxOn_mem {f : β -> α} (hf : M
easurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] (n : Nat) (x
 : β) : approxOn f hf s y₀ …
· 使用定理 `MeasureTheory.SimpleFunc.memLp_approxOn`：memLp_approxOn [BorelSpace E] {
f : β -> E} {μ : Measure β} (fmeas : Measurable f) (hf : MemLp f p μ) {s : Set E
} {y₀ : E} (h₀ : y₀ in s) [Se…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.eLpNorm_zero'`：eLpNorm_zero' : eLpNorm (fun _ : α => (0 : 
ε)) p μ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 57 条，此处仅展示前 30 条）
-/
theorem denseRange_coeSimpleFuncNonnegToLpNonneg [hp : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    DenseRange (coeSimpleFuncNonnegToLpNonneg p μ G) := fun g ↦ by
  borelize G
  rw [mem_closure_iff_seq_limit]
  have hg_memLp : MemLp (g : α → G) p μ := Lp.memLp (g : Lp G p μ)
  have zero_mem : (0 : G) ∈ (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } := by
    simp only [union_singleton, mem_inter_iff, mem_insert_iff, true_or,
      mem_ofPred_eq, le_refl, and_self_iff]
  have : SeparableSpace ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y } : Set G) := by
    apply IsSeparable.separableSpace
    apply IsSeparable.mono _ Set.inter_subset_left
    exact
      (Lp.stronglyMeasurable (g : Lp G p μ)).isSeparable_range.union
        (finite_singleton _).isSeparable
  have g_meas : Measurable (g : α → G) := (Lp.stronglyMeasurable (g : Lp G p μ)).measurable
  let x n := SimpleFunc.approxOn (g : α → G) g_meas
    ((range (g : α → G) ∪ {0}) ∩ { y | 0 ≤ y }) 0 zero_mem n
  have hx_nonneg : ∀ n, 0 ≤ x n := by
    intro n a
    change x n a ∈ { y : G | 0 ≤ y }
    have A : (range (g : α → G) ∪ {0} : Set G) ∩ { y | 0 ≤ y } ⊆ { y | 0 ≤ y } :=
      inter_subset_right
    apply A
    exact SimpleFunc.approxOn_mem g_meas _ n a
  have hx_memLp : ∀ n, MemLp (x n) p μ :=
    SimpleFunc.memLp_approxOn _ hg_memLp _ ⟨aestronglyMeasurable_const, by simp⟩
  have h_toLp := fun n => MemLp.coeFn_toLp (hx_memLp n)
  have hx_nonneg_Lp : ∀ n, 0 ≤ toLp (x n) (hx_memLp n) := by
    intro n
    rw [← Lp.simpleFunc.coeFn_le, Lp.simpleFunc.toLp_eq_toLp]
    filter_upwards [Lp.simpleFunc.coeFn_zero p μ G, h_toLp n] with a ha0 ha_toLp
    rw [ha0, ha_toLp]
    exact hx_nonneg n a
  have hx_tendsto :
      Tendsto (fun n : ℕ => eLpNorm ((x n : α → G) - (g : α → G)) p μ) atTop (𝓝 0) := by
    apply SimpleFunc.tendsto_approxOn_Lp_eLpNorm g_meas zero_mem hp_ne_top
    · have hg_nonneg : (0 : α → G) ≤ᵐ[μ] g := (Lp.coeFn_nonneg _).mpr g.2
      refine hg_nonneg.mono fun a ha => subset_closure ?_
      simpa using ha
    · simp_rw [sub_zero]; finiteness
  refine
    ⟨fun n =>
      (coeSimpleFuncNonnegToLpNonneg p μ G) ⟨toLp (x n) (hx_memLp n), hx_nonneg_Lp n⟩,
      fun n => mem_range_self _, ?_⟩
  suffices Tendsto (fun n : ℕ => (toLp (x n) (hx_memLp n) : Lp G p μ)) atTop (𝓝 (g : Lp G p μ)) by
    rw [tendsto_iff_dist_tendsto_zero] at this ⊢
    simp_rw [Subtype.dist_eq]
    exact this
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine Filter.Tendsto.congr (fun n => eLpNorm_congr_ae (EventuallyEq.sub ?_ ?_)) hx_tendsto
  · symm
    rw [Lp.simpleFunc.toLp_eq_toLp]
    exact h_toLp n
  · rfl

end Order

end simpleFunc

end Lp

variable [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {p : ℝ≥0∞} {μ : Measure α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_elim]
/-
**MeasureTheory.Lp.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [_i : Fact (1 ≤ p
)],   p ≠ ⊤ →     ∀ (motive : ↥(MeasureTheory.Lp E p μ) → Prop),       (∀ (c : E
) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ⊤),           motive ↑(Measure
Theory.Lp.simpleFunc.indicatorConst p hs ⋯ c)) →         (∀ ⦃f g : α → E⦄ (hf : 
MeasureTheory.MemLp f p μ) (hg : MeasureTheory.MemLp g p μ),             Disjoin
t (Function.support f) (Function.support g) →               motive (MeasureTheor
y.MemLp.toLp f hf) →                 motive (MeasureTheory.MemLp.toLp g hg) →   
                motive (MeasureTheory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp
 g hg)) →           IsClosed {f | motive f} → ∀ (f : ↥(MeasureTheory.Lp E p μ)),
 motive f
参数：1 ≤ p；motive : ↥(MeasureTheory.Lp E p μ) → Prop；∀ (c : E) {s : Set α} (hs : M
easurableSet s) (hμs : μ s < ⊤),           motive ↑(MeasureTheory.Lp.simpleFunc.
indicatorConst p hs ⋯ c)；∀ ⦃f g : α → E⦄ (hf : MeasureTheory.MemLp f p μ) (hg : 
MeasureTheory.MemLp g p μ),             Disjoint (Function.support f) (Function.
support g) →               motive (MeasureTheory.MemLp.toLp f hf) →             
    motive (MeasureTheory.MemLp.toLp g hg) →                   motive (MeasureTh
eory.MemLp.toLp f hf + MeasureTheory.MemLp.toLp g hg)；f : ↥(MeasureTheory.Lp E p
 μ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `DenseRange.induction_on`：DenseRange.induction_on [TopologicalSpace β] {e
 : α -> β} (he : DenseRange e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b
 }) (ih : for…
· 使用定理 `MeasureTheory.Lp.simpleFunc.denseRange`：∀ {α : Type u_1} {E : Type u_4} 
[inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : 
MeasureTheory.Measure α} [in…
· 使用定理 `MeasureTheory.Lp.simpleFunc.induction`：∀ {α : Type u_1} {E : Type u_4} [
inst : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : M
easureTheory.Measure α},   …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p

--- 原说明 ---
To prove something for an arbitrary `Lp` function in a second countable Borel no
rmed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
theorem Lp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (motive : Lp E p μ → Prop)
    (indicatorConst : ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞),
      motive (Lp.simpleFunc.indicatorConst p hs hμs.ne c))
    (add : ∀ ⦃f g⦄, ∀ hf : MemLp f p μ, ∀ hg : MemLp g p μ, Disjoint (support f) (support g) →
      motive (hf.toLp f) → motive (hg.toLp g) → motive (hf.toLp f + hg.toLp g))
    (isClosed : IsClosed { f : Lp E p μ | motive f }) : ∀ f : Lp E p μ, motive f := by
  refine fun f => (Lp.simpleFunc.denseRange hp_ne_top).induction_on f isClosed ?_
  refine Lp.simpleFunc.induction (α := α) (E := E) (lt_of_lt_of_le zero_lt_one _i.elim).ne'
    hp_ne_top ?_ ?_
  · exact fun c s => indicatorConst c
  · exact fun f g hf hg => add hf hg

/-- To prove something for an arbitrary `MemLp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
/-
**MeasureTheory.MemLp.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α} [_i : Fact (1 ≤ p
)],   p ≠ ⊤ →     ∀ (motive : (α → E) → Prop),       (∀ (c : E) ⦃s : Set α⦄, Mea
surableSet s → μ s < ⊤ → motive (s.indicator fun x => c)) →         (∀ ⦃f g : α 
→ E⦄,             Disjoint (Function.support f) (Function.support g) →          
     MeasureTheory.MemLp f p μ → MeasureTheory.MemLp g p μ → motive f → motive g
 → motive (f + g)) →           IsClosed {f | motive ↑↑f} →             (∀ ⦃f g :
 α → E⦄, f =ᵐ[μ] g → MeasureTheory.MemLp f p μ → motive f → motive g) →         
      ∀ ⦃f : α → E⦄, MeasureTheory.MemLp f p μ → motive f
参数：1 ≤ p；motive : (α → E) → Prop；∀ (c : E) ⦃s : Set α⦄, MeasurableSet s → μ s < 
⊤ → motive (s.indicator fun x => c)；∀ ⦃f g : α → E⦄,             Disjoint (Funct
ion.support f) (Function.support g) →               MeasureTheory.MemLp f p μ → 
MeasureTheory.MemLp g p μ → motive f → motive g → motive (f + g)；∀ ⦃f g : α → E⦄
, f =ᵐ[μ] g → MeasureTheory.MemLp f p μ → motive f → motive g。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `MeasureTheory.SimpleFunc.measure_lt_top_of_memLp_indicator`：measure_lt_t
op_of_memLp_indicator (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 
0) {s : Set α} (hs : MeasurableSet s) (hcs : Mem…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.memLp_add_of_disjoint`：memLp_add_of_disjoint {f g : α -> E
} (h : Disjoint (support f) (support g)) (hf : StronglyMeasurable f) (hg : Stron
glyMeasurable g) : MemLp …
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.SimpleFunc.coe_add`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β),   ⇑(
f + g) = ⇑f + ⇑g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
To prove something for an arbitrary `MemLp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and
 such conditions
can be added once we need them (for example in `h_add` it is only necessary to c
onsider the sum of
a simple function with a multiple of a characteristic function and that the inte
rsection
of their images is a subset of `{0}`).
-/
theorem MemLp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (motive : (α → E) → Prop)
    (indicator : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → motive (s.indicator fun _ => c))
    (add : ∀ ⦃f g : α → E⦄, Disjoint (support f) (support g) → MemLp f p μ → MemLp g p μ →
      motive f → motive g → motive (f + g))
    (closed : IsClosed { f : Lp E p μ | motive f })
    (ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → MemLp f p μ → motive f → motive g) :
    ∀ ⦃f : α → E⦄, MemLp f p μ → motive f := by
  have : ∀ f : SimpleFunc α E, MemLp f p μ → motive f := by
    apply SimpleFunc.induction
    · intro c s hs h
      by_cases hc : c = 0
      · subst hc; convert! indicator 0 MeasurableSet.empty (by simp) using 1; ext; simp
      have hp_pos : p ≠ 0 := (lt_of_lt_of_le zero_lt_one _i.elim).ne'
      exact indicator c hs (SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs h)
    · intro f g hfg hf hg int_fg
      rw [SimpleFunc.coe_add,
        memLp_add_of_disjoint hfg f.stronglyMeasurable g.stronglyMeasurable] at int_fg
      exact add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)
  have : ∀ f : Lp.simpleFunc E p μ, motive f := by
    intro f
    exact
      ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f) (Lp.simpleFunc.memLp f)
        (this (Lp.simpleFunc.toSimpleFunc f) (Lp.simpleFunc.memLp f))
  have : ∀ f : Lp E p μ, motive f := fun f =>
    (Lp.simpleFunc.denseRange hp_ne_top).induction_on f closed this
  exact fun f hf => ae hf.coeFn_toLp (Lp.memLp _) (this (hf.toLp f))

/-- If a set of ae strongly measurable functions is stable under addition and approximates
characteristic functions in `ℒp`, then it is dense in `ℒp`. -/
/-
**MeasureTheory.MemLp.induction_dense** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
emLp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measure α},   p ≠ ⊤ →     ∀ 
(P : (α → E) → Prop),       (∀ (c : E) ⦃s : Set α⦄,           MeasurableSet s → 
            μ s < ⊤ → ∀ {ε : ENNReal}, ε ≠ 0 → ∃ g, MeasureTheory.eLpNorm (g - s
.indicator fun x => c) p μ ≤ ε ∧ P g) →         (∀ (f g : α → E), P f → P g → P 
(f + g)) →           (∀ (f : α → E), P f → MeasureTheory.AEStronglyMeasurable f 
μ) →             ∀ {f : α → E},               MeasureTheory.MemLp f p μ → ∀ {ε :
 ENNReal}, ε ≠ 0 → ∃ g, MeasureTheory.eLpNorm (f - g) p μ ≤ ε ∧ P g
参数：P : (α → E) → Prop；∀ (c : E) ⦃s : Set α⦄,           MeasurableSet s →        
     μ s < ⊤ → ∀ {ε : ENNReal}, ε ≠ 0 → ∃ g, MeasureTheory.eLpNorm (g - s.indica
tor fun x => c) p μ ≤ ε ∧ P g；∀ (f g : α → E), P f → P g → P (f + g)；∀ (f : α → 
E), P f → MeasureTheory.AEStronglyMeasurable f μ；f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.SimpleFunc.piecewise_same`：piecewise_same (f : α ->ₛ β) {s
 : Set α} (hs : MeasurableSet s) : piecewise s hs f f = f
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `MeasureTheory.SimpleFunc.measure_lt_top_of_memLp_indicator`：measure_lt_t
op_of_memLp_indicator (hp_pos : p != 0) (hp_ne_top : p != ∞) {c : E} (hc : c != 
0) {s : Set α} (hs : MeasurableSet s) (hcs : Mem…
· 使用定理 `MeasureTheory.exists_Lp_half`：exists_Lp_half (p : Real>=0∞) {δ : Real>=0
∞} (hδ : δ != 0) : exists η : Real>=0∞, 0 < η ∧ forall (f g : α -> ε), AEStrongl
yMeasurable f μ ->…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.memLp_add_of_disjoint`：memLp_add_of_disjoint {f g : α -> E
} (h : Disjoint (support f) (support g)) (hf : StronglyMeasurable f) (hg : Stron
glyMeasurable g) : MemLp …
· 使用定理 `MeasureTheory.SimpleFunc.stronglyMeasurable`：∀ {α : Type u_1} {β : Type 
u_2} {x : MeasurableSpace α} [inst : TopologicalSpace β] (f : MeasureTheory.Simp
leFunc α β),   MeasureTheory.Stro…
· 使用定理 `MeasureTheory.SimpleFunc.coe_add`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β),   ⇑(
f + g) = ⇑f + ⇑g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If a set of ae strongly measurable functions is stable under addition and approx
imates
characteristic functions in `ℒp`, then it is dense in `ℒp`.
-/
theorem MemLp.induction_dense (hp_ne_top : p ≠ ∞) (P : (α → E) → Prop)
    (h0P :
      ∀ (c : E) ⦃s : Set α⦄,
        MeasurableSet s →
          μ s < ∞ →
            ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : α → E, eLpNorm (g - s.indicator fun _ => c) p μ ≤ ε ∧ P g)
    (h1P : ∀ f g, P f → P g → P (f + g)) (h2P : ∀ f, P f → AEStronglyMeasurable f μ) {f : α → E}
    (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ P g := by
  rcases eq_or_ne p 0 with (rfl | hp_pos)
  · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
        hε with ⟨g, _, Pg⟩
    exact ⟨g, by simp, Pg⟩
  suffices H : ∀ (f' : α →ₛ E) (δ : ℝ≥0∞) (hδ : δ ≠ 0), MemLp f' p μ →
      ∃ g, eLpNorm (⇑f' - g) p μ ≤ δ ∧ P g by
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p hε
    rcases hf.exists_simpleFunc_eLpNorm_sub_lt hp_ne_top ηpos.ne' with ⟨f', hf', f'_mem⟩
    rcases H f' η ηpos.ne' f'_mem with ⟨g, hg, Pg⟩
    refine ⟨g, ?_, Pg⟩
    convert!
      (hη _ _ (hf.aestronglyMeasurable.sub f'.aestronglyMeasurable)
          (f'.aestronglyMeasurable.sub (h2P g Pg)) hf'.le hg).le using 2
    simp only [sub_add_sub_cancel]
  apply SimpleFunc.induction
  · intro c s hs ε εpos Hs
    rcases eq_or_ne c 0 with (rfl | hc)
    · rcases h0P (0 : E) MeasurableSet.empty (by simp only [measure_empty, zero_lt_top])
          εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg, neg_sub] at hg
      refine ⟨g, ?_, Pg⟩
      convert! hg
      ext x
      simp
    · have : μ s < ∞ := SimpleFunc.measure_lt_top_of_memLp_indicator hp_pos hp_ne_top hc hs Hs
      rcases h0P c hs this εpos with ⟨g, hg, Pg⟩
      rw [← eLpNorm_neg, neg_sub] at hg
      exact ⟨g, hg, Pg⟩
  · intro f f' hff' hf hf' δ δpos int_ff'
    obtain ⟨η, ηpos, hη⟩ := exists_Lp_half E μ p δpos
    rw [SimpleFunc.coe_add,
      memLp_add_of_disjoint hff' f.stronglyMeasurable f'.stronglyMeasurable] at int_ff'
    rcases hf η ηpos.ne' int_ff'.1 with ⟨g, hg, Pg⟩
    rcases hf' η ηpos.ne' int_ff'.2 with ⟨g', hg', Pg'⟩
    refine ⟨g + g', ?_, h1P g g' Pg Pg'⟩
    convert!
      (hη _ _ (f.aestronglyMeasurable.sub (h2P g Pg)) (f'.aestronglyMeasurable.sub (h2P g' Pg')) hg
          hg').le using 2
    rw [SimpleFunc.coe_add]
    abel

section Integrable

@[inherit_doc MeasureTheory.Lp.simpleFunc]
notation3:25 α " →₁ₛ[" μ "] " E => @MeasureTheory.Lp.simpleFunc α E _ _ 1 μ

/-
**MeasureTheory.L1.SimpleFunc.toLp_one_eq_toL1** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.L1.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {μ : MeasureTheory.Measure α}   (f : MeasureTheory.SimpleFunc α
 E) (hf : MeasureTheory.Integrable (⇑f) μ),   ↑(f.toLp ⋯) = MeasureTheory.Integr
able.toL1 (⇑f) hf
参数：f : MeasureTheory.SimpleFunc α E；hf : MeasureTheory.Integrable (⇑f) μ；f.toLp 
⋯；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
-/
theorem L1.SimpleFunc.toLp_one_eq_toL1 (f : α →ₛ E) (hf : Integrable f μ) :
    (toLp f (memLp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.toL1 f :=
  rfl

@[fun_prop]
/-
**MeasureTheory.L1.SimpleFunc.integrable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.L1.SimpleFunc`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {μ : MeasureTheory.Measure α}   (f : ↥(α →₁ₛ[μ] E)), MeasureThe
ory.Integrable (⇑(MeasureTheory.Lp.simpleFunc.toSimpleFunc f)) μ
参数：f : ↥(α →₁ₛ[μ] E)；⇑(MeasureTheory.Lp.simpleFunc.toSimpleFunc f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.Lp.simpleFunc.memLp`：∀ {α : Type u_1} {E : Type u_4} [inst
 : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Measu
reTheory.Measure α} (f …
-/
protected theorem L1.SimpleFunc.integrable (f : α →₁ₛ[μ] E) :
    Integrable (Lp.simpleFunc.toSimpleFunc f) μ := by
  rw [← memLp_one_iff_integrable]; exact Lp.simpleFunc.memLp f

/-- To prove something for an arbitrary integrable function in a normed group,
it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_elim]
/-
**MeasureTheory.Integrable.induction** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_4} [inst : MeasurableSpace α] [inst_1 : Norme
dAddCommGroup E] {μ : MeasureTheory.Measure α}   (P : (α → E) → Prop),   (∀ (c :
 E) ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → P (s.indicator fun x => c)) →     (
∀ ⦃f g : α → E⦄,         Disjoint (Function.support f) (Function.support g) →   
        MeasureTheory.Integrable f μ → MeasureTheory.Integrable g μ → P f → P g 
→ P (f + g)) →       IsClosed {f | P ↑↑f} →         (∀ ⦃f g : α → E⦄, f =ᵐ[μ] g 
→ MeasureTheory.Integrable f μ → P f → P g) →           ∀ ⦃f : α → E⦄, MeasureTh
eory.Integrable f μ → P f
参数：P : (α → E) → Prop；∀ (c : E) ⦃s : Set α⦄, MeasurableSet s → μ s < ⊤ → P (s.in
dicator fun x => c)；∀ ⦃f g : α → E⦄,         Disjoint (Function.support f) (Func
tion.support g) →           MeasureTheory.Integrable f μ → MeasureTheory.Integra
ble g μ → P f → P g → P (f + g)；∀ ⦃f g : α → E⦄, f =ᵐ[μ] g → MeasureTheory.Integ
rable f μ → P f → P g。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.MemLp.induction`：∀ {α : Type u_1} {E : Type u_4} [inst : M
easurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTh
eory.Measure α} [_i…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤

--- 原说明 ---
To prove something for an arbitrary integrable function in a normed group,
it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and
 such conditions
can be added once we need them (for example in `h_add` it is only necessary to c
onsider the sum of
a simple function with a multiple of a characteristic function and that the inte
rsection
of their images is a subset of `{0}`).
-/
theorem Integrable.induction (P : (α → E) → Prop)
    (h_ind : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → P (s.indicator fun _ => c))
    (h_add :
      ∀ ⦃f g : α → E⦄,
        Disjoint (support f) (support g) → Integrable f μ → Integrable g μ → P f → P g → P (f + g))
    (h_closed : IsClosed { f : α →₁[μ] E | P f })
    (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → Integrable f μ → P f → P g) :
    ∀ ⦃f : α → E⦄, Integrable f μ → P f := by
  simp only [← memLp_one_iff_integrable] at *
  exact MemLp.induction one_ne_top (motive := P) h_ind h_add h_closed h_ae

end Integrable

end MeasureTheory

