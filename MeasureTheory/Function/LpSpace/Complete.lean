/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `Lp` is a complete space

In this file we show that `Lp` is a complete space for `1 ≤ p`,
in `MeasureTheory.Lp.instCompleteSpace`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

variable {α E : Type*} {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [SeminormedAddGroup E]

namespace MeasureTheory.Lp

/-
**MeasureTheory.Lp.eLpNorm'_lim_eq_lintegral_liminf** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : SeminormedAddGroup E]   {ι : Type u_3} [Nonempty ι] [inst_2 
: LinearOrder ι] {f : ι → α → E} {p : ℝ} {f_lim : α → E},   (∀ᵐ (x : α) ∂μ, Filt
er.Tendsto (fun n => f n x) Filter.atTop (nhds (f_lim x))) →     MeasureTheory.e
LpNorm' f_lim p μ = (∫⁻ (a : α), Filter.liminf (fun x => ‖f x a‖ₑ ^ p) Filter.at
Top ∂μ) ^ (1 / p)
参数：∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (f_lim x))；
∫⁻ (a : α), Filter.liminf (fun x => ‖f x a‖ₑ ^ p) Filter.atTop ∂μ；1 / p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_rpow_const`：continuous_rpow_const {y : Real} : Contin
uous fun a : Real>=0∞ => a ^ y
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm'_eq_lintegral_enorm`：∀ {α : Type u_1} {ε : Type u_
2} {m0 : MeasurableSpace α} [inst : ENorm ε] (f : α → ε) (q : ℝ)   (μ : MeasureT
heory.Measure α), MeasureTheory…
-/
theorem eLpNorm'_lim_eq_lintegral_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → E} {p : ℝ}
    {f_lim : α → E} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ = (∫⁻ a, atTop.liminf (‖f · a‖ₑ ^ p) ∂μ) ^ (1 / p) := by
  suffices h_no_pow : (∫⁻ a, ‖f_lim a‖ₑ ^ p ∂μ) = ∫⁻ a, atTop.liminf fun m => ‖f m a‖ₑ ^ p ∂μ by
    rw [eLpNorm'_eq_lintegral_enorm, h_no_pow]
  refine lintegral_congr_ae (h_lim.mono fun a ha => ?_)
  dsimp only
  rw [Tendsto.liminf_eq]
  refine (ENNReal.continuous_rpow_const.tendsto ‖f_lim a‖₊).comp ?_
  exact (continuous_enorm.tendsto (f_lim a)).comp ha
/-
**MeasureTheory.Lp.eLpNorm'_lim_le_liminf_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [inst : SeminormedAddGroup E]   {f : ℕ → α → E} {p : ℝ},   0 < p →  
   (∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (f n) μ) →       ∀ {f_lim : α 
→ E},         (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds
 (f_lim x))) →           MeasureTheory.eLpNorm' f_lim p μ ≤ Filter.liminf (fun n
 => MeasureTheory.eLpNorm' (f n) p μ) Filter.atTop
参数：∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (f n) μ；∀ᵐ (x : α) ∂μ, Filter.T
endsto (fun n => f n x) Filter.atTop (nhds (f_lim x))；fun n => MeasureTheory.eLp
Norm' (f n) p μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.eLpNorm'_lim_eq_lintegral_liminf`：∀ {α : Type u_1} {E :
 Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Seminor
medAddGroup E]   {ι : Type u_3} [Nonemp…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.le_rpow_inv_iff`：le_rpow_inv_iff {x y : Real>=0∞} {z : Real} (hz
 : 0 < z) : x <= y ^ z⁻¹ ↔ x ^ z <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_liminf_le'`：lintegral_liminf_le' {ι : Type*} {f 
: ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i
, AEMeasurable (f i) μ) …
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
· 使用定理 `AEMeasurable.pow_const`：AEMeasurable.pow_const (hf : AEMeasurable f μ) (
c : γ) : AEMeasurable (fun x => f x ^ c) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `ENNReal.strictMono_rpow_of_pos`：strictMono_rpow_of_pos {z : Real} (h : 0
 < z) : StrictMono fun x : Real>=0∞ => x ^ z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.rpow_left_bijective`：rpow_left_bijective {x : Real} (hx : x != 0
) : Function.Bijective fun y : Real>=0∞ => y ^ x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 38 条，此处仅展示前 30 条）
-/
theorem eLpNorm'_lim_le_liminf_eLpNorm' {f : ℕ → α → E} {p : ℝ}
    (hp_pos : 0 < p) (hf : ∀ n, AEStronglyMeasurable (f n) μ) {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm' f_lim p μ ≤ atTop.liminf fun n => eLpNorm' (f n) p μ := by
  rw [eLpNorm'_lim_eq_lintegral_liminf h_lim]
  rw [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  refine (lintegral_liminf_le' fun m => (hf m).enorm.pow_const _).trans_eq ?_
  have h_pow_liminf :
    atTop.liminf (fun n ↦ eLpNorm' (f n) p μ) ^ p
      = atTop.liminf fun n ↦ eLpNorm' (f n) p μ ^ p := by
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hp_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_pow_liminf]
  simp_rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hp_pos.ne.symm, ENNReal.rpow_one]
/-
**MeasureTheory.Lp.eLpNorm_exponent_top_lim_eq_essSup_liminf** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Lp`。
形式化陈述：eLpNorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι]
 {f : ι -> α -> E} {f_lim : α -> E} (h_lim : forallᵐ x : α ∂μ, Tendsto (fun n =>
 f n x) atTop (𝓝 (f_lim x))) : eLpNorm f_lim ∞ μ = essSup (fun x => atTop.liminf
 fun m => ‖f m x‖ₑ) μ
参数：h_lim : forallᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用引理 `MeasureTheory.eLpNormEssSup_eq_essSup_enorm`：eLpNormEssSup_eq_essSup_eno
rm (f : α -> ε) (μ : Measure α) : eLpNormEssSup f μ = essSup (‖f ·‖ₑ) μ
· 使用定理 `essSup_congr_ae`：essSup_congr_ae {f g : α -> β} (hfg : f =ᵐ[μ] g) : essS
up f μ = essSup g μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
-/
theorem eLpNorm_exponent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι → α → E}
    {f_lim : α → E} (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ = essSup (fun x => atTop.liminf fun m => ‖f m x‖ₑ) μ := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  refine essSup_congr_ae (h_lim.mono fun x hx => ?_)
  dsimp only
  apply (Tendsto.liminf_eq ..).symm
  exact (continuous_enorm.tendsto (f_lim x)).comp hx
/-
**MeasureTheory.Lp.eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top {ι} [Nonempty ι] [
Countable ι] [LinearOrder ι] {f : ι -> α -> E} {f_lim : α -> E} (h_lim : forallᵐ
 x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) : eLpNorm f_lim ∞ μ <= 
atTop.liminf fun n => eLpNorm (f n) ∞ μ
参数：h_lim : forallᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.eLpNorm_exponent_top_lim_eq_essSup_liminf`：eLpNorm_expo
nent_top_lim_eq_essSup_liminf {ι} [Nonempty ι] [LinearOrder ι] {f : ι -> α -> E}
 {f_lim : α -> E} (h_lim : forallᵐ x : α ∂μ, Ten…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_exponent_top`：eLpNorm_exponent_top {f : α -> ε} : 
eLpNorm f ∞ μ = eLpNormEssSup f μ
· 使用定理 `ENNReal.essSup_liminf_le`：essSup_liminf_le {ι} [Countable ι] [Preorder ι
] (f : ι -> α -> Real>=0∞) : essSup (fun x => atTop.liminf fun n => f n x) μ <= 
atTop.liminf f…
-/
theorem eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top {ι} [Nonempty ι] [Countable ι]
    [LinearOrder ι] {f : ι → α → E} {f_lim : α → E}
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim ∞ μ ≤ atTop.liminf fun n => eLpNorm (f n) ∞ μ := by
  rw [eLpNorm_exponent_top_lim_eq_essSup_liminf h_lim]
  simp_rw [eLpNorm_exponent_top, eLpNormEssSup]
  exact ENNReal.essSup_liminf_le _
/-
**MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：eLpNorm_lim_le_liminf_eLpNorm {f : Nat -> α -> E} (hf : forall n, AEStrong
lyMeasurable (f n) μ) (f_lim : α -> E) (h_lim : forallᵐ x : α ∂μ, Tendsto (fun n
 => f n x) atTop (𝓝 (f_lim x))) : eLpNorm f_lim p μ <= atTop.liminf fun n => eLp
Norm (f n) p μ
参数：hf : forall n, AEStronglyMeasurable (f n) μ；f_lim : α -> E；h_lim : forallᵐ x 
: α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.eLpNorm_exponent_zero`：eLpNorm_exponent_zero {f : α -> ε} 
: eLpNorm f 0 μ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top
`：eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top {ι} [Nonempty ι] [Coun
table ι] [LinearOrder ι] {f : ι -> α -> E} {f_lim : α -> E} (h…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `MeasureTheory.Lp.eLpNorm'_lim_le_liminf_eLpNorm'`：∀ {α : Type u_1} {E : 
Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Seminorm
edAddGroup E]   {f : ℕ → α → E} {p : ℝ…
-/
theorem eLpNorm_lim_le_liminf_eLpNorm {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (f_lim : α → E)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim p μ ≤ atTop.liminf fun n => eLpNorm (f n) p μ := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  by_cases hp_top : p = ∞
  · simp_rw [hp_top]
    exact eLpNorm_exponent_top_lim_le_liminf_eLpNorm_exponent_top h_lim
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  exact eLpNorm'_lim_le_liminf_eLpNorm' hp_pos hf h_lim

/-- If the `eLpNorm` of a collection of `AEStronglyMeasurable` functions that converges almost
everywhere is bounded by some constant `C`, then the `eLpNorm` of its limit is also bounded by
`C`. -/
/-
**MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp`。
形式化陈述：eLpNorm_le_of_ae_tendsto {ι : Type*} {u : Filter ι} [NeBot u] [IsCountably
Generated u] {f : ι -> α -> E} {g : α -> E} {C : Real>=0∞} (bound : forallᶠ n in
 u, eLpNorm (f n) p μ <= C) (hf : forall n, AEStronglyMeasurable (f n) μ) (h_ten
dsto : forallᵐ (x : α) ∂μ, Tendsto (f · x) u (𝓝 (g x))) : eLpNorm g p μ <= C
参数：bound : forallᶠ n in u, eLpNorm (f n) p μ <= C；hf : forall n, AEStronglyMeasu
rable (f n) μ；h_tendsto : forallᵐ (x : α) ∂μ, Tendsto (f · x) u (𝓝 (g x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`：eLpNorm_lim_le_liminf_eL
pNorm {f : Nat -> α -> E} (hf : forall n, AEStronglyMeasurable (f n) μ) (f_lim :
 α -> E) (h_lim : forallᵐ x : α ∂μ, …
· 使用定理 `Filter.liminf_le_of_le`：liminf_le_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsBoundedUnder (· >= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If the `eLpNorm` of a collection of `AEStronglyMeasurable` functions that conver
ges almost
everywhere is bounded by some constant `C`, then the `eLpNorm` of its limit is a
lso bounded by
`C`.
-/
theorem eLpNorm_le_of_ae_tendsto {ι : Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} {C : ℝ≥0∞} (bound : ∀ᶠ n in u, eLpNorm (f n) p μ ≤ C)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ (x : α) ∂μ, Tendsto (f · x) u (𝓝 (g x))) :
    eLpNorm g p μ ≤ C := by
  obtain ⟨v, hv⟩ := exists_seq_tendsto u
  have : ∀ᵐ (x : α) ∂μ, Tendsto (fun n => f (v n) x) atTop (𝓝 (g x)) := by
    filter_upwards [h_tendsto] with x hx
    exact hx.comp hv
  calc
  _ ≤ atTop.liminf (fun (n : ℕ) => eLpNorm (f (v n)) p μ) :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf (v n)) g this
  _ ≤ C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := (hb.and (hv.eventually bound)).exists
    exact hn.1.trans hn.2

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/

variable {E : Type*} [NormedAddCommGroup E]

/-
**MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp`。
形式化陈述：tendsto_Lp_iff_tendsto_eLpNorm' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι
 -> Lp E p μ) (f_lim : Lp E p μ) : fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n =>
 eLpNorm (⇑(f n) - ⇑f_lim) p μ) (𝓝 0)
参数：1 <= p；f : ι -> Lp E p μ；f_lim : Lp E p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Lp.dist_def`：dist_def (f g : Lp E p μ) : dist f g = (eLpNo
rm (⇑f - ⇑g) p μ).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `ENNReal.tendsto_toReal_iff`：tendsto_toReal_iff {ι} {fi : Filter ι} {f : 
ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto 
(fun n => (f n).…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Lp_iff_tendsto_eLpNorm' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : Lp E p μ) :
    fi.Tendsto f (𝓝 f_lim) ↔ fi.Tendsto (fun n => eLpNorm (⇑(f n) - ⇑f_lim) p μ) (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _
/-
**MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
形式化陈述：tendsto_Lp_iff_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι 
-> Lp E p μ) (f_lim : α -> E) (f_lim_ℒp : MemLp f_lim p μ) : fi.Tendsto f (𝓝 (f_
lim_ℒp.toLp f_lim)) ↔ fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)
参数：1 <= p；f : ι -> Lp E p μ；f_lim : α -> E；f_lim_ℒp : MemLp f_lim p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'`：tendsto_Lp_iff_tendsto
_eLpNorm' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι -> Lp E p μ) (f_lim : Lp E 
p μ) : fi.Tendsto f (𝓝 f_lim) ↔ fi.Ten…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_Lp_iff_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ)
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0) := by
  rw [tendsto_Lp_iff_tendsto_eLpNorm']
  suffices h_eq :
      (fun n => eLpNorm (⇑(f n) - ⇑(MemLp.toLp f_lim f_lim_ℒp)) p μ) =
        (fun n => eLpNorm (⇑(f n) - f_lim) p μ) by
    rw [h_eq]
  exact funext fun n => eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp f_lim_ℒp))
/-
**MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Lp`。
形式化陈述：tendsto_Lp_iff_tendsto_eLpNorm'' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : 
ι -> α -> E) (f_ℒp : forall n, MemLp (f n) p μ) (f_lim : α -> E) (f_lim_ℒp : Mem
Lp f_lim p μ) : fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_li
m)) ↔ fi.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)
参数：1 <= p；f : ι -> α -> E；f_ℒp : forall n, MemLp (f n) p μ；f_lim : α -> E；f_lim_
ℒp : MemLp f_lim p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'`：tendsto_Lp_iff_tendsto
_eLpNorm' {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι -> Lp E p μ) (f_lim : Lp E 
p μ) : fi.Tendsto f (𝓝 f_lim) ↔ fi.Ten…
· 使用定理 `Filter.tendsto_congr`：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂
 : Filter β} (h : forall x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tendsto_Lp_iff_tendsto_eLpNorm'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E)
    (f_ℒp : ∀ n, MemLp (f n) p μ) (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ) :
    fi.Tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.toLp f_lim)) ↔
      fi.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => (f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)]
  refine Filter.tendsto_congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [((f_ℒp n).sub f_lim_ℒp).coeFn_toLp,
    Lp.coeFn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.toLp f_lim)] with _ hx₁ hx₂
  rw [← hx₂]
  exact hx₁
/-
**MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：tendsto_Lp_of_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 <= p)] {f : ι -
> Lp E p μ} (f_lim : α -> E) (f_lim_ℒp : MemLp f_lim p μ) (h_tendsto : fi.Tendst
o (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)) : fi.Tendsto f (𝓝 (f_lim_ℒp.toL
p f_lim))
参数：1 <= p；f_lim : α -> E；f_lim_ℒp : MemLp f_lim p μ；h_tendsto : fi.Tendsto (fun 
n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm`：tendsto_Lp_iff_tendsto_
eLpNorm {ι} {fi : Filter ι} [Fact (1 <= p)] (f : ι -> Lp E p μ) (f_lim : α -> E)
 (f_lim_ℒp : MemLp f_lim p μ) : fi.Te…
-/
theorem tendsto_Lp_of_tendsto_eLpNorm {ι} {fi : Filter ι} [Fact (1 ≤ p)] {f : ι → Lp E p μ}
    (f_lim : α → E) (f_lim_ℒp : MemLp f_lim p μ)
    (h_tendsto : fi.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)) :
    fi.Tendsto f (𝓝 (f_lim_ℒp.toLp f_lim)) :=
  (tendsto_Lp_iff_tendsto_eLpNorm f f_lim f_lim_ℒp).mpr h_tendsto
/-
**MeasureTheory.Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Lp`。
形式化陈述：cauchySeq_Lp_iff_cauchySeq_eLpNorm {ι} [Nonempty ι] [SemilatticeSup ι] [hp
 : Fact (1 <= p)] (f : ι -> Lp E p μ) : CauchySeq f ↔ Tendsto (fun n : ι × ι => 
eLpNorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) atTop (𝓝 0)
参数：1 <= p；f : ι -> Lp E p μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Lp.dist_def`：dist_def (f g : Lp E p μ) : dist f g = (eLpNo
rm (⇑f - ⇑g) p μ).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `ENNReal.tendsto_toReal_iff`：tendsto_toReal_iff {ι} {fi : Filter ι} {f : 
ι -> Real>=0∞} (hf : forall i, f i != ∞) {x : Real>=0∞} (hx : x != ∞) : Tendsto 
(fun n => (f n).…
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cauchySeq_Lp_iff_cauchySeq_eLpNorm {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)]
    (f : ι → Lp E p μ) :
    CauchySeq f ↔ Tendsto (fun n : ι × ι => eLpNorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) atTop (𝓝 0) := by
  simp_rw [cauchySeq_iff_tendsto_dist_atTop_0, dist_def]
  rw [← ENNReal.toReal_zero, ENNReal.tendsto_toReal_iff (fun n => ?_) ENNReal.zero_ne_top]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact eLpNorm_ne_top _
/-
**MeasureTheory.Lp.completeSpace_lp_of_cauchy_complete_eLpNorm** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：completeSpace_lp_of_cauchy_complete_eLpNorm [hp : Fact (1 <= p)] (H : fora
ll (f : Nat -> α -> E) (_ : forall n, MemLp (f n) p μ) (B : Nat -> Real>=0∞) (_ 
: ∑' i, B i < ∞) (_ : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m
) p μ < B N), exists (f_lim : α -> E), MemLp f_lim p μ ∧ atTop.Tendsto (fun n =>
 eLpNorm (f n - f_lim) p μ) (𝓝 0)) : CompleteSpace (Lp E p μ)
参数：1 <= p；H : forall (f : Nat -> α -> E) (_ : forall n, MemLp (f n) p μ) (B : Na
t -> Real>=0∞) (_ : ∑' i, B i < ∞) (_ : forall N n m : Nat, N <= n -> N <= m -> 
eLpNorm (f n - f m) p μ < B N), exists (f_lim : α -> E), MemLp f_lim p μ ∧ atTop
.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Metric.complete_of_convergent_controlled_sequences`：Metric.complete_of_c
onvergent_controlled_sequences (B : Nat -> Real) (hB : forall n, 0 < B n) (H : f
orall u : Nat -> α, (forall N n m : Nat,…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.ofReal_tsum_of_nonneg`：ENNReal.ofReal_tsum_of_nonneg {f : α -> R
eal} (hf_nonneg : forall n, 0 <= f n) (hf : Summable f) : ENNReal.ofReal (∑' n, 
f n) = ∑' n, ENNRea…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `ENNReal.lt_ofReal_iff_toReal_lt`：lt_ofReal_iff_toReal_lt {a : Real>=0∞} 
{b : Real} (ha : a != ∞) : a < ENNReal.ofReal b ↔ ENNReal.toReal a < b
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
（共 36 条，此处仅展示前 30 条）
-/
theorem completeSpace_lp_of_cauchy_complete_eLpNorm [hp : Fact (1 ≤ p)]
    (H :
      ∀ (f : ℕ → α → E) (_ : ∀ n, MemLp (f n) p μ) (B : ℕ → ℝ≥0∞) (_ : ∑' i, B i < ∞)
        (_ : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N),
        ∃ (f_lim : α → E), MemLp f_lim p μ ∧
          atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) :
    CompleteSpace (Lp E p μ) := by
  let B := fun n : ℕ => ((1 : ℝ) / 2) ^ n
  have hB_pos : ∀ n, 0 < B n := fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n
  refine Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => ?_
  rsuffices ⟨f_lim, hf_lim_meas, h_tendsto⟩ :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (⇑(f n) - f_lim) p μ) (𝓝 0)
  · exact ⟨hf_lim_meas.toLp f_lim, tendsto_Lp_of_tendsto_eLpNorm f_lim hf_lim_meas h_tendsto⟩
  obtain ⟨M, hB⟩ : Summable B := summable_geometric_two
  let B1 n := ENNReal.ofReal (B n)
  have hB1_has : HasSum B1 (ENNReal.ofReal M) := by
    have h_tsum_B1 : ∑' i, B1 i = ENNReal.ofReal M := by
      change (∑' n : ℕ, ENNReal.ofReal (B n)) = ENNReal.ofReal M
      rw [← hB.tsum_eq]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => le_of_lt (hB_pos n)) hB.summable).symm
    have h_sum := (@ENNReal.summable _ B1).hasSum
    rwa [h_tsum_B1] at h_sum
  have hB1 : ∑' i, B1 i < ∞ := by
    rw [hB1_has.tsum_eq]
    exact ENNReal.ofReal_lt_top
  let f1 : ℕ → α → E := fun n => f n
  refine H f1 (fun n => Lp.memLp (f n)) B1 hB1 fun N n m hn hm => ?_
  specialize hf N n m hn hm
  rw [dist_def] at hf
  dsimp only [f1]
  rwa [ENNReal.lt_ofReal_iff_toReal_lt]
  rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm]
  exact Lp.eLpNorm_ne_top _

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/

/-
**MeasureTheory.Lp.eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm'** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp`
-/
private theorem eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) (n : ℕ) :
    eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i := by
  let f_norm_diff i x := ‖f (i + 1) x - f i x‖
  have hgf_norm_diff :
    ∀ n,
      (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) =
        ∑ i ∈ Finset.range (n + 1), f_norm_diff i :=
    fun n => funext fun x => by simp [f_norm_diff]
  rw [hgf_norm_diff]
  refine (eLpNorm'_sum_le (fun i _ => ((hf (i + 1)).sub (hf i)).norm) hp1).trans ?_
  simp_rw [eLpNorm'_norm]
  refine (Finset.sum_le_sum ?_).trans <| ENNReal.sum_le_tsum _
  exact fun m _ => (h_cau m (m + 1) m (Nat.le_succ m) (le_refl m)).le
/-
**MeasureTheory.Lp.lintegral_rpow_sum_enorm_sub_le_rpow_tsum** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lintegral_rpow_sum_enorm_sub_le_rpow_tsum
    {f : ℕ → α → E} {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
    (hn : eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i) :
    (∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  rw [← inv_inv p, @ENNReal.le_rpow_inv_iff _ _ p⁻¹ (by simp [hp_pos]), inv_inv p]
  simp_rw [eLpNorm'_eq_lintegral_enorm, one_div] at hn
  have h_nnnorm_nonneg :
    (fun a => ‖∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖‖ₑ ^ p) = fun a =>
      (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p := by
    ext1 a
    congr
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [Real.norm_of_nonneg _]
      exact Finset.sum_nonneg fun x _ => norm_nonneg _
    · exact fun x _ => norm_nonneg _
  rwa [h_nnnorm_nonneg] at hn
/-
**MeasureTheory.Lp.lintegral_rpow_tsum_coe_enorm_sub_le_tsum** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lintegral_rpow_tsum_coe_enorm_sub_le_tsum {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
    (h : ∀ n, ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p) :
    (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  suffices h_pow : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ≤ (∑' i, B i) ^ p by
      rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv]
  have h_tsum_1 :
    ∀ g : ℕ → ℝ≥0∞, ∑' i, g i = atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), g i := by
    intro g
    rw [ENNReal.tsum_eq_liminf_sum_nat, ← liminf_nat_add _ 1]
  simp_rw [h_tsum_1 _]
  rw [← h_tsum_1]
  have h_liminf_pow :
    ∫⁻ a, (atTop.liminf fun n => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ =
      ∫⁻ a, atTop.liminf fun n => (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos (zero_lt_one.trans_le hp1)
    have h_rpow_surj := (ENNReal.rpow_left_bijective hp_pos.ne.symm).2
    refine (h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj).liminf_apply ?_ ?_ ?_ ?_
    all_goals isBoundedDefault
  rw [h_liminf_pow]
  refine (lintegral_liminf_le' fun n ↦ ?_).trans <| liminf_le_of_frequently_le' <| .of_forall h
  exact ((Finset.range _).aemeasurable_fun_sum fun i _ ↦ ((hf _).sub (hf i)).enorm).pow_const _
/-
**MeasureTheory.Lp.tsum_enorm_sub_ae_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Lp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem tsum_enorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {p : ℝ} (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i) :
    ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ := by
  have hp_pos : 0 < p := zero_lt_one.trans_le hp1
  have h_integral : ∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ < ∞ := by
    have h_tsum_lt_top : (∑' i, B i) ^ p < ∞ := ENNReal.rpow_lt_top_of_nonneg hp_pos.le hB
    refine lt_of_le_of_lt ?_ h_tsum_lt_top
    rwa [one_div, ← ENNReal.le_rpow_inv_iff (by simp [hp_pos] : 0 < p⁻¹), inv_inv] at h
  have rpow_ae_lt_top : ∀ᵐ x ∂μ, (∑' i, ‖f (i + 1) x - f i x‖ₑ) ^ p < ∞ := by
    refine ae_lt_top' (AEMeasurable.pow_const ?_ _) h_integral.ne
    exact AEMeasurable.tsum fun n => ((hf (n + 1)).sub (hf n)).enorm
  refine rpow_ae_lt_top.mono fun x hx => ?_
  rwa [← ENNReal.lt_rpow_inv_iff hp_pos,
    ENNReal.top_rpow_of_pos (by simp [hp_pos] : 0 < p⁻¹)] at hx
/-
**MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Lp`。
形式化陈述：ae_tendsto_of_cauchy_eLpNorm' [CompleteSpace E] {f : Nat -> α -> E} {p : R
eal} (hf : forall n, AEStronglyMeasurable (f n) μ) (hp1 : 1 <= p) {B : Nat -> Re
al>=0∞} (hB : ∑' i, B i != ∞) (h_cau : forall N n m : Nat, N <= n -> N <= m -> e
LpNorm' (f n - f m) p μ < B N) : forallᵐ x ∂μ, exists l : E, atTop.Tendsto (fun 
n => f n x) (𝓝 l)
参数：hf : forall n, AEStronglyMeasurable (f n) μ；hp1 : 1 <= p；hB : ∑' i, B i != ∞；
h_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm' (f n - f m) p μ < B N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Complete.0.MeasureTheory
.Lp.eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm'`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_3} [inst : NormedAddCom
mGroup E]   {f : ℕ → α → E},   (∀ …
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Complete.0.MeasureTheory
.Lp.lintegral_rpow_sum_enorm_sub_le_rpow_tsum`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {E : Type u_3} [inst : NormedAddCommGroup 
E]   {f : ℕ → α → E} {p : ℝ…
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Complete.0.MeasureTheory
.Lp.lintegral_rpow_tsum_coe_enorm_sub_le_tsum`：∀ {α : Type u_1} {m : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {E : Type u_3} [inst : NormedAddCommGroup 
E]   {f : ℕ → α → E},   (∀ …
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Complete.0.MeasureTheory
.Lp.tsum_enorm_sub_ae_lt_top`：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : Meas
ureTheory.Measure α} {E : Type u_3} [inst : NormedAddCommGroup E]   {f : ℕ → α →
 E},   (∀ …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Summable.of_nnnorm`：Summable.of_nnnorm {f : ι -> E} (hf : Summable fun a
 => ‖f a‖₊) : Summable f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tsum_coe_ne_top_iff_summable`：tsum_coe_ne_top_iff_summable {f : 
β -> Real>=0} : (∑' b, (f b : Real>=0∞)) != ∞ ↔ Summable f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Filter.Tendsto.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
-/
theorem ae_tendsto_of_cauchy_eLpNorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  have h_summable : ∀ᵐ x ∂μ, Summable fun i : ℕ => f (i + 1) x - f i x := by
    have h1 :
      ∀ n, eLpNorm' (fun x => ∑ i ∈ Finset.range (n + 1), ‖f (i + 1) x - f i x‖) p μ ≤ ∑' i, B i :=
      eLpNorm'_sum_norm_sub_le_tsum_of_cauchy_eLpNorm' hf hp1 h_cau
    have h2 n :
        ∫⁻ a, (∑ i ∈ Finset.range (n + 1), ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ ≤ (∑' i, B i) ^ p :=
      lintegral_rpow_sum_enorm_sub_le_rpow_tsum hp1 n (h1 n)
    have h3 : (∫⁻ a, (∑' i, ‖f (i + 1) a - f i a‖ₑ) ^ p ∂μ) ^ (1 / p) ≤ ∑' i, B i :=
      lintegral_rpow_tsum_coe_enorm_sub_le_tsum hf hp1 h2
    have h4 : ∀ᵐ x ∂μ, ∑' i, ‖f (i + 1) x - f i x‖ₑ < ∞ :=
      tsum_enorm_sub_ae_lt_top hf hp1 hB h3
    exact h4.mono fun x hx => .of_nnnorm <| ENNReal.tsum_coe_ne_top_iff_summable.mp hx.ne
  refine h_summable.mono fun x hx ↦ ?_
  have hx_sum := hx.hasSum.tendsto_sum_nat
  rw [funext fun n ↦ Finset.sum_range_sub (fun m ↦ f m x) n] at hx_sum
  exact ⟨∑' i, (f (i + 1) x - f i x) + f 0 x, by simpa using hx_sum.add_const (f 0 x)⟩
/-
**MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Lp`。
形式化陈述：ae_tendsto_of_cauchy_eLpNorm [CompleteSpace E] {f : Nat -> α -> E} (hf : f
orall n, AEStronglyMeasurable (f n) μ) (hp : 1 <= p) {B : Nat -> Real>=0∞} (hB :
 ∑' i, B i != ∞) (h_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n -
 f m) p μ < B N) : forallᵐ x ∂μ, exists l : E, atTop.Tendsto (fun n => f n x) (𝓝
 l)
参数：hf : forall n, AEStronglyMeasurable (f n) μ；hp : 1 <= p；hB : ∑' i, B i != ∞；h
_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m) p μ < B N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ae_lt_of_essSup_lt`：ae_lt_of_essSup_lt (hx : essSup f μ < x) (hf : IsBou
ndedUnder (· <= ·) (ae μ) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `cauchySeq_of_le_tendsto_0`：cauchySeq_of_le_tendsto_0 {s : β -> α} (b : β
 -> Real) (h : forall n m N : β, N <= n -> N <= m -> dist (s n) (s m) <= b N) (h
₀ : Tendsto b a…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
· 使用定理 `ENNReal.ne_top_of_tsum_ne_top`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a
 : α), f a ≠ ⊤ → ∀ (a : α), f a ≠ ⊤
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`：tendsto_atTop_zero_of_tsum_ne
_top {f : Nat -> Real>=0∞} (hf : ∑' x, f x != ∞) : Tendsto f atTop (𝓝 0)
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `MeasureTheory.eLpNorm'`：eLpNorm'_exponent_zero {f : α -> ε} : eLpNorm' f
 0 μ = 1
· 使用定理 `MeasureTheory.eLpNorm_eq_eLpNorm'`：eLpNorm_eq_eLpNorm' (hp_ne_zero : p !
= 0) (hp_ne_top : p != ∞) {f : α -> ε} : eLpNorm f p μ = eLpNorm' f (ENNReal.toR
eal p) μ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
（共 36 条，此处仅展示前 30 条）
-/
theorem ae_tendsto_of_cauchy_eLpNorm [CompleteSpace E] {f : ℕ → α → E}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hp : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∀ᵐ x ∂μ, ∃ l : E, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top] at *
    have h_cau_ae : ∀ᵐ x ∂μ, ∀ N n m, N ≤ n → N ≤ m → ‖(f n - f m) x‖ₑ < B N := by
      simp_rw [ae_all_iff]
      exact fun N n m hnN hmN => ae_lt_of_essSup_lt (h_cau N n m hnN hmN)
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup] at h_cau
    refine h_cau_ae.mono fun x hx => cauchySeq_tendsto_of_complete ?_
    refine cauchySeq_of_le_tendsto_0 (fun n => (B n).toReal) ?_ ?_
    · intro n m N hnN hmN
      specialize hx N n m hnN hmN
      rw [_root_.dist_eq_norm,
        ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top hB N),
        ofReal_norm]
      exact hx.le
    · rw [← ENNReal.toReal_zero]
      exact
        Tendsto.comp (g := ENNReal.toReal) (ENNReal.tendsto_toReal ENNReal.zero_ne_top)
          (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)
  have hp1 : 1 ≤ p.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hp_top, ENNReal.ofReal_one]
    exact hp
  have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm' (f n - f m) p.toReal μ < B N := by
    intro N n m hn hm
    specialize h_cau N n m hn hm
    rwa [eLpNorm_eq_eLpNorm' (zero_lt_one.trans_le hp).ne.symm hp_top] at h_cau
  exact ae_tendsto_of_cauchy_eLpNorm' hf hp1 hB h_cau'
/-
**MeasureTheory.Lp.cauchy_tendsto_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Lp`。
形式化陈述：cauchy_tendsto_of_tendsto {f : Nat -> α -> E} (hf : forall n, AEStronglyMe
asurable (f n) μ) (f_lim : α -> E) {B : Nat -> Real>=0∞} (hB : ∑' i, B i != ∞) (
h_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m) p μ < B N) (
h_lim : forallᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) : atTop.
Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)
参数：hf : forall n, AEStronglyMeasurable (f n) μ；f_lim : α -> E；hB : ∑' i, B i != 
∞；h_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m) p μ < B N；
h_lim : forallᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.tendsto_atTop_zero_of_tsum_ne_top`：tendsto_atTop_zero_of_tsum_ne
_top {f : Nat -> Real>=0∞} (hf : ∑' x, f x != ∞) : Tendsto f atTop (𝓝 0)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm`：eLpNorm_lim_le_liminf_eL
pNorm {f : Nat -> α -> E} (hf : forall n, AEStronglyMeasurable (f n) μ) (f_lim :
 α -> E) (h_lim : forallᵐ x : α ∂μ, …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.liminf_le_of_frequently_le'`：liminf_le_of_frequently_le' {α β} [C
ompleteLattice β] {f : Filter α} {u : α -> β} {x : β} (h : existsᶠ a in f, u a <
= x) : liminf u f <= x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
（共 32 条，此处仅展示前 30 条）
-/
theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (f_lim : α → E) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N)
    (h_lim : ∀ᵐ x : α ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have h_B : ∃ N : ℕ, B N ≤ ε := by
    suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε from
      ⟨h_tendsto_zero.choose, h_tendsto_zero.choose_spec _ le_rfl⟩
    exact (ENNReal.tendsto_atTop_zero.mp (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hB)) ε hε
  obtain ⟨N, h_B⟩ := h_B
  refine ⟨N, fun n hn => ?_⟩
  have h_sub : eLpNorm (f n - f_lim) p μ ≤ atTop.liminf fun m => eLpNorm (f n - f m) p μ := by
    refine eLpNorm_lim_le_liminf_eLpNorm (fun m => (hf n).sub (hf m)) (f n - f_lim) ?_
    refine h_lim.mono fun x hx => ?_
    simp_rw [sub_eq_add_neg]
    exact Tendsto.add tendsto_const_nhds (Tendsto.neg hx)
  refine h_sub.trans ?_
  refine liminf_le_of_frequently_le' (frequently_atTop.mpr ?_)
  refine fun N1 => ⟨max N N1, le_max_right _ _, ?_⟩
  exact (h_cau N n (max N N1) hn (le_max_left _ _)).le.trans h_B
/-
**MeasureTheory.Lp.memLp_of_cauchy_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp`。
形式化陈述：memLp_of_cauchy_tendsto (hp : 1 <= p) {f : Nat -> α -> E} (hf : forall n, 
MemLp (f n) p μ) (f_lim : α -> E) (h_lim_meas : AEStronglyMeasurable f_lim μ) (h
_tendsto : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) : MemLp f_l
im p μ
参数：hp : 1 <= p；hf : forall n, MemLp (f n) p μ；f_lim : α -> E；h_lim_meas : AEStro
nglyMeasurable f_lim μ；h_tendsto : atTop.Tendsto (fun n => eLpNorm (f n - f_lim)
 p μ) (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `_private.Mathlib.MeasureTheory.Function.LpSpace.Complete.0.MeasureTheory
.Lp.memLp_of_cauchy_tendsto._abel_1_1`：∀ {α : Type u_1} {E : Type u_2} [inst : N
ormedAddCommGroup E] {f : ℕ → α → E} (f_lim : α → E) (N : ℕ),   f_lim = f_lim - 
f N + f N
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.eLpNorm_add_le`：eLpNorm_add_le (hf : AEStronglyMeasurable 
f μ) (hg : AEStronglyMeasurable g μ) (hp1 : 1 <= p) : eLpNorm (f + g) p μ <= eLp
Norm f p μ + eLpNo…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem memLp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, MemLp (f n) p μ)
    (f_lim : α → E) (h_lim_meas : AEStronglyMeasurable f_lim μ)
    (h_tendsto : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0)) : MemLp f_lim p μ := by
  refine ⟨h_lim_meas, ?_⟩
  rw [ENNReal.tendsto_atTop_zero] at h_tendsto
  obtain ⟨N, h_tendsto_1⟩ := h_tendsto 1 zero_lt_one
  specialize h_tendsto_1 N (le_refl N)
  have h_add : f_lim = f_lim - f N + f N := by abel
  rw [h_add]
  refine lt_of_le_of_lt (eLpNorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) ?_
  rw [ENNReal.add_lt_top]
  constructor
  · refine lt_of_le_of_lt ?_ ENNReal.one_lt_top
    have h_neg : f_lim - f N = -(f N - f_lim) := by simp
    rwa [h_neg, eLpNorm_neg]
  · exact (hf N).2
/-
**MeasureTheory.Lp.cauchy_complete_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Lp`。
形式化陈述：cauchy_complete_eLpNorm [CompleteSpace E] (hp : 1 <= p) {f : Nat -> α -> E
} (hf : forall n, MemLp (f n) p μ) {B : Nat -> Real>=0∞} (hB : ∑' i, B i != ∞) (
h_cau : forall N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m) p μ < B N) :
 exists (f_lim : α -> E), MemLp f_lim p μ ∧ atTop.Tendsto (fun n => eLpNorm (f n
 - f_lim) p μ) (𝓝 0)
参数：hp : 1 <= p；hf : forall n, MemLp (f n) p μ；hB : ∑' i, B i != ∞；h_cau : forall
 N n m : Nat, N <= n -> N <= m -> eLpNorm (f n - f m) p μ < B N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_stronglyMeasurable_limit_of_tendsto_ae`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [TopologicalSpace.Pseud…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm`：ae_tendsto_of_cauchy_eLpN
orm [CompleteSpace E] {f : Nat -> α -> E} (hf : forall n, AEStronglyMeasurable (
f n) μ) (hp : 1 <= p) {B : Nat -> R…
· 使用定理 `MeasureTheory.Lp.cauchy_tendsto_of_tendsto`：cauchy_tendsto_of_tendsto {f
 : Nat -> α -> E} (hf : forall n, AEStronglyMeasurable (f n) μ) (f_lim : α -> E)
 {B : Nat -> Real>=0∞} (hB : ∑' …
· 使用定理 `MeasureTheory.Lp.memLp_of_cauchy_tendsto`：memLp_of_cauchy_tendsto (hp : 
1 <= p) {f : Nat -> α -> E} (hf : forall n, MemLp (f n) p μ) (f_lim : α -> E) (h
_lim_meas : AEStronglyMeasurab…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
-/
theorem cauchy_complete_eLpNorm [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E}
    (hf : ∀ n, MemLp (f n) p μ) {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (f n - f m) p μ < B N) :
    ∃ (f_lim : α → E), MemLp f_lim p μ ∧
      atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) := by
  obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
      ∃ f_lim : α → E, StronglyMeasurable f_lim ∧
        ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) :=
    exists_stronglyMeasurable_limit_of_tendsto_ae (fun n => (hf n).1)
      (ae_tendsto_of_cauchy_eLpNorm (fun n => (hf n).1) hp hB h_cau)
  have h_tendsto' : atTop.Tendsto (fun n => eLpNorm (f n - f_lim) p μ) (𝓝 0) :=
    cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim
  have h_ℒp_lim : MemLp f_lim p μ :=
    memLp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.aestronglyMeasurable h_tendsto'
  exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩

/-- `Lp` is complete for `1 ≤ p`. -/
/-
**MeasureTheory.Lp.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Lp
`。
形式化陈述：instCompleteSpace [CompleteSpace E] [hp : Fact (1 <= p)] : CompleteSpace (
Lp E p μ)
参数：1 <= p。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.completeSpace_lp_of_cauchy_complete_eLpNorm`：completeSp
ace_lp_of_cauchy_complete_eLpNorm [hp : Fact (1 <= p)] (H : forall (f : Nat -> α
 -> E) (_ : forall n, MemLp (f n) p μ) (B : Nat ->…
· 使用定理 `MeasureTheory.Lp.cauchy_complete_eLpNorm`：cauchy_complete_eLpNorm [Compl
eteSpace E] (hp : 1 <= p) {f : Nat -> α -> E} (hf : forall n, MemLp (f n) p μ) {
B : Nat -> Real>=0∞} (hB : ∑' …
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
`Lp` is complete for `1 ≤ p`.
-/
instance instCompleteSpace [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ) :=
  completeSpace_lp_of_cauchy_complete_eLpNorm fun _f hf _B hB h_cau =>
    cauchy_complete_eLpNorm hp.elim hf hB.ne h_cau

end MeasureTheory.Lp

