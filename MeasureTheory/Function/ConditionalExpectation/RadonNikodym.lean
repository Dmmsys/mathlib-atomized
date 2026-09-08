/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-!
# Radon-Nikodym derivatives and conditional expectations

We express the Radon-Nikodym derivative of the pushforward of measures in terms of the conditional
expectation of the Radon-Nikodym derivative of the original measures.

## Main statements

In all statements, `μ` and `ν` are measures with `μ ≪ ν`.

* `rnDeriv_map`: the Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of
  measures by a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation
  of `∂μ/∂ν` with respect to the comap by `g` of the sigma-algebra on `𝓨`.
* `rnDeriv_trim`: the Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed
  measures (for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
  conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`.

We have two versions of the above statements, one with a.e. equality to the conditional expectation
`condLExp` built from the Lebesgue integral, and one with a.e. equality to the
conditional expectation `condExp` built from the Bochner integral.

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equality with respect to
the trimmed measure `ν.trim hg.comap_le`. -/
/-
**MeasureTheory.toReal_rnDeriv_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Me
asurable g) [hσ : SigmaFinite (ν.map g)] : (fun a => ((μ.map g).rnDeriv (ν.map g
) (g a)).toReal) =ᵐ[ν] ν[(fun a => (μ.rnDeriv ν a).toReal) | m𝓨.comap g]
参数：hμν : μ ≪ ν；hg : Measurable g；ν.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.SigmaFinite.of_map`：∀ {α : Type u_1} {β : Type u_2} {m0 : 
MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α)   {f
 : α → β},   AEMeasura…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_iff_comap_le`：measurable_iff_comap_le {m₁ : MeasurableSpace α
} {m₂ : MeasurableSpace β} {f : α -> β} : Measurable f ↔ m₂.comap f <= m₁
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.map_trim_comap`：map_trim_comap {f : α -> β} (hf : Measurab
le f) : @Measure.map _ _ (mβ.comap f) _ f (μ.trim hf.comap_le) = μ.map f
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.comp_measurable`：∀ {α : Type u_1} {ε : Type u_5
} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace
 ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.setIntegral_map`：setIntegral_map {Y} [MeasurableSpace Y] {
g : X -> Y} {f : Y -> E} {s : Set Y} (hs : MeasurableSet s) (hf : AEStronglyMeas
urable f (Measure.m…
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv`：setIntegral_toReal_rnD
eriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫ x in s, (μ.rn
Deriv ν x).toReal ∂ν = μ.real s
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measu
res by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expec
tation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equali
ty with respect to
the trimmed measure `ν.trim hg.comap_le`.
-/
lemma toReal_rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] :
    (fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν]
      ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | m𝓨.comap g] := by
  have : SigmaFinite (ν.trim hg.comap_le) := by
    rw [← map_trim_comap hg] at hσ
    refine SigmaFinite.of_map (ν.trim hg.comap_le) ?_ hσ
    refine Measurable.aemeasurable ?_
    exact measurable_iff_comap_le.mpr le_rfl
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  refine ae_eq_condExp_of_forall_setIntegral_eq _ (by fun_prop) ?_ ?_ ?_
  · rintro _ ⟨t, _, rfl⟩ _
    exact Integrable.integrableOn (Measure.integrable_toReal_rnDeriv.comp_measurable hg)
  · rintro _ ⟨t, ht, rfl⟩ _
    calc ∫ x in g ⁻¹' t, ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν
    _ = ∫ y in t, ((μ.map g).rnDeriv (ν.map g) y).toReal ∂(ν.map g) := by
      rw [setIntegral_map ht _ hg.aemeasurable]
      exact Measurable.aestronglyMeasurable (by fun_prop)
    _ = ∫ x in g ⁻¹' t, (μ.rnDeriv ν x).toReal ∂ν := by
      rw [Measure.setIntegral_toReal_rnDeriv (hμν.map hg),
        Measure.setIntegral_toReal_rnDeriv hμν, measureReal_def, Measure.map_apply hg ht,
        measureReal_def]
  · refine (Measurable.ennreal_toReal fun s hs ↦ ?_).aestronglyMeasurable
    exact ⟨_, Measure.measurable_rnDeriv _ _ hs, rfl⟩

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equality with respect to
the trimmed measure `ν.trim hg.comap_le`. -/
/-
**MeasureTheory.rnDeriv_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurabl
e g) [hσ : SigmaFinite (ν.map g)] : (fun a => (μ.map g).rnDeriv (ν.map g) (g a))
 =ᵐ[ν] ν⁻[μ.rnDeriv ν|m𝓨.comap g]
参数：hμν : μ ≪ ν；hg : Measurable g；ν.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SigmaFinite.of_map`：∀ {α : Type u_1} {β : Type u_2} {m0 : 
MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α)   {f
 : α → β},   AEMeasura…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用引理 `MeasureTheory.Measure.rnDeriv_ne_top`：rnDeriv_ne_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用引理 `MeasureTheory.condLExp_ne_top`：condLExp_ne_top {f : Ω -> Real>=0∞} (hf :
 ∫⁻ x, f x ∂P != ∞) : forallᵐ x ∂P, P⁻[f|mΩ] x != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.lintegral_rnDeriv`：lintegral_rnDeriv [HaveLebesgue
Decomposition μ ν] (hμν : μ ≪ ν) : ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MeasureTheory.toReal_condLExp`：toReal_condLExp (m : MeasurableSpace 𝓧) {
m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {f : 𝓧 -> Real>=0∞} (hf_meas : AEMeasura
ble f μ) (hf : ∫⁻ x…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.toReal_rnDeriv_map`：toReal_rnDeriv_map [IsFiniteMeasure μ]
 (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (
fun a => ((μ.map g).rn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measu
res by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expec
tation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map_ae_eq_trim` for the same statement, but with a.e. equality with
 respect to
the trimmed measure `ν.trim hg.comap_le`.
-/
lemma rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν] ν⁻[μ.rnDeriv ν|m𝓨.comap g] := by
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  have h_ne_top1 : ∀ᵐ x ∂ν, (μ.map g).rnDeriv (ν.map g) (g x) ≠ ∞ :=
    ae_of_ae_map hg.aemeasurable (Measure.rnDeriv_ne_top (μ.map g) (ν.map g))
  have h_ne_top2 : ∀ᵐ x ∂ν, ν⁻[μ.rnDeriv ν|MeasurableSpace.comap g m𝓨] x ≠ ∞ := by
    refine condLExp_ne_top ?_
    simp [Measure.lintegral_rnDeriv hμν]
  have h_condExp := toReal_condLExp (m𝓨.comap g) (f := μ.rnDeriv ν) (μ := ν) (by fun_prop) ?_
  swap; · simp [Measure.lintegral_rnDeriv hμν]
  filter_upwards [toReal_rnDeriv_map hμν hg, h_condExp, h_ne_top1, h_ne_top2]
    with x hx h_condExp h_ne_top1 h_ne_top2
  rwa [← h_condExp, ENNReal.toReal_eq_toReal_iff' h_ne_top1 h_ne_top2] at hx

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map` for the same statement, but with a.e. equality with respect to the measure `ν`. -/
/-
**MeasureTheory.rnDeriv_map_ae_eq_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg 
: Measurable g) [SigmaFinite (ν.map g)] : (fun a => (μ.map g).rnDeriv (ν.map g) 
(g a)) =ᵐ[ν.trim hg.comap_le] ν⁻[μ.rnDeriv ν|m𝓨.comap g]
参数：hμν : μ ≪ ν；hg : Measurable g；ν.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.measurable_condLExp`：measurable_condLExp (mΩ : MeasurableS
pace Ω) (P : Measure[mΩ₀] Ω) (X : Ω -> Real>=0∞) : Measurable[mΩ] P⁻[X|mΩ]
· 使用引理 `MeasureTheory.rnDeriv_map`：rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
 {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (fun a => (μ.ma
p g).rnDeriv (ν…

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measu
res by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expec
tation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `rnDeriv_map` for the same statement, but with a.e. equality with respect to
 the measure `ν`.
-/
lemma rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] :
    (fun a ↦ (μ.map g).rnDeriv (ν.map g) (g a)) =ᵐ[ν.trim hg.comap_le]
      ν⁻[μ.rnDeriv ν|m𝓨.comap g] := by
  rw [StronglyMeasurable.ae_eq_trim_iff]
  · exact rnDeriv_map hμν hg
  · refine Measurable.stronglyMeasurable fun s hs ↦ ?_
    exact ⟨((μ.map g).rnDeriv (ν.map g)) ⁻¹' s, hs.preimage (by fun_prop), by grind⟩
  · fun_prop

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expectation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map` for the same statement, but with a.e. equality with respect to
the measure `ν`. -/
/-
**MeasureTheory.toReal_rnDeriv_map_ae_eq_trim** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：toReal_rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 -> 
𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] : (fun a => ((μ.map g).rnDeriv (ν
.map g) (g a)).toReal) =ᵐ[ν.trim hg.comap_le] ν[(fun a => (μ.rnDeriv ν a).toReal
) | m𝓨.comap g]
参数：hμν : μ ≪ ν；hg : Measurable g；ν.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.StronglyMeasurable.ae_eq_trim_iff`：ae_eq_trim_iff (hm : m 
<= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : f =ᵐ[μ.tr
im hm] g ↔ f =ᵐ[μ] g
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用引理 `MeasureTheory.toReal_rnDeriv_map`：toReal_rnDeriv_map [IsFiniteMeasure μ]
 (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (
fun a => ((μ.map g).rn…

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measu
res by
a function `g : 𝓧 → 𝓨` evaluated at `g x` is a.e.-equal to the conditional expec
tation of `∂μ/∂ν`
with respect to the comap by `g` of the sigma-algebra on `𝓨`.

See `toReal_rnDeriv_map` for the same statement, but with a.e. equality with res
pect to
the measure `ν`.
-/
lemma toReal_rnDeriv_map_ae_eq_trim [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [SigmaFinite (ν.map g)] :
    (fun a ↦ ((μ.map g).rnDeriv (ν.map g) (g a)).toReal) =ᵐ[ν.trim hg.comap_le]
      ν[(fun a ↦ (μ.rnDeriv ν a).toReal) | m𝓨.comap g] := by
  rw [StronglyMeasurable.ae_eq_trim_iff]
  · exact toReal_rnDeriv_map hμν hg
  · refine Measurable.stronglyMeasurable fun s hs ↦ ?_
    refine ⟨(fun a ↦ ((μ.map g).rnDeriv (ν.map g) a).toReal) ⁻¹' s, hs.preimage (by fun_prop), ?_⟩
    rw [← Set.preimage_comp]
    rfl
  · fun_prop

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`. -/
/-
**MeasureTheory.toReal_rnDeriv_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：toReal_rnDeriv_trim (hm : m <= m𝓧) [IsFiniteMeasure μ] [hsf : SigmaFinite 
(ν.trim hm)] (hμν : μ ≪ ν) : (fun x => ((μ.trim hm).rnDeriv (ν.trim hm) x).toRea
l) =ᵐ[ν.trim hm] ν[fun x => (μ.rnDeriv ν x).toReal | m]
参数：hm : m <= m𝓧；ν.trim hm；hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用引理 `MeasureTheory.trim_eq_map`：trim_eq_map (hm : m <= m0) : μ.trim hm = @Mea
sure.map _ _ _ m id μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用引理 `MeasureTheory.toReal_rnDeriv_map_ae_eq_trim`：toReal_rnDeriv_map_ae_eq_tr
im [IsFiniteMeasure μ] (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [SigmaFini
te (ν.map g)] : (fun a => ((μ.map…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasurableSpace.comap_id`：comap_id : m.comap id = m
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equa
l to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`.
-/
lemma toReal_rnDeriv_trim (hm : m ≤ m𝓧) [IsFiniteMeasure μ] [hsf : SigmaFinite (ν.trim hm)]
    (hμν : μ ≪ ν) :
    (fun x ↦ ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) =ᵐ[ν.trim hm]
      ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] := by
  simp_rw [trim_eq_map hm]
  have : SigmaFinite (@Measure.map _ _ m𝓧 m id ν) := by rwa [← trim_eq_map hm]
  have h := toReal_rnDeriv_map_ae_eq_trim hμν (measurable_id'' hm)
  simp_rw [MeasurableSpace.comap_id, id_def, trim_eq_map] at h
  convert! h <;> rw [MeasurableSpace.comap_id]

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equal to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`. -/
/-
**MeasureTheory.rnDeriv_trim** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_trim (hm : m <= m𝓧) [IsFiniteMeasure μ] [SigmaFinite (ν.trim hm)] 
(hμν : μ ≪ ν) : (μ.trim hm).rnDeriv (ν.trim hm) =ᵐ[ν.trim hm] fun x => ENNReal.o
fReal (ν[fun x => (μ.rnDeriv ν x).toReal | m] x)
参数：hm : m <= m𝓧；ν.trim hm；hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_ne_top`：rnDeriv_ne_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.toReal_rnDeriv_trim`：toReal_rnDeriv_trim (hm : m <= m𝓧) [I
sFiniteMeasure μ] [hsf : SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) : (fun x => ((μ.
trim hm).rnDeriv (ν.tri…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures
(for `hm : m ≤ m0` stating that `m` is a sub-sigma-algebra of `m0`) is a.e.-equa
l to the
conditional expectation of `∂μ/∂ν` with respect to the sigma-algebra `m`.
-/
lemma rnDeriv_trim (hm : m ≤ m𝓧) [IsFiniteMeasure μ] [SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) :
    (μ.trim hm).rnDeriv (ν.trim hm)
      =ᵐ[ν.trim hm] fun x ↦ ENNReal.ofReal (ν[fun x ↦ (μ.rnDeriv ν x).toReal | m] x) := by
  filter_upwards [toReal_rnDeriv_trim hm hμν, Measure.rnDeriv_ne_top (μ.trim hm) (ν.trim hm)]
    with x hx hx_ne_top
  rw [← hx, ENNReal.ofReal_toReal hx_ne_top]

end MeasureTheory

