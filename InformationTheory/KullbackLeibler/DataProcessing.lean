/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym

/-!
# Data processing inequality for the Kullback-Leibler divergence

The data processing inequality is a way to express the intuition that applying a (possibly random)
transformation to random variables cannot increase the information they contain.

## Main statements

We prove three versions of the data processing inequality for the Kullback-Leibler divergence, for
measurable maps, restrictions to sub-sigma-algebras, and composition with Markov kernels.
Let `μ, ν` be finite measures on `𝓧`, with sigma-algebra `m𝓧`.

* `klDiv_map_le`: `klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν` for a measurable function `g`.
* `klDiv_trim_le`: `klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν` for a sub-sigma-algebra `m` of `m𝓧`
  (with `hm : m ≤ m𝓧`).
* `klDiv_comp_right_le`: `klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν` for a Markov kernel `κ`.

-/

public section

open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ConvexOn

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → ℝ} {g : 𝓧 → 𝓨}

/-
**ConvexOn.map_condExp_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：map_condExp_rnDeriv_le (hm : m <= m𝓧) (hf : StronglyMeasurable f) (hf_cvx 
: ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0) (h_int 
: Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : (fun x => f ((ν[fun x => (
μ.rnDeriv ν x).toReal | m]) x)) <=ᵐ[ν.trim hm] ν[fun x => f (μ.rnDeriv ν x).toRe
al | m]
参数：hm : m <= m𝓧；hf : StronglyMeasurable f；hf_cvx : ConvexOn Real (Ici 0) f；hf_co
nt_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun x => f (μ.rnDeriv
 ν x).toReal) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_condExp_le_trim`：ConvexOn.map_condExp_le_trim {mE : Measura
bleSpace E} [BorelSpace E] (hm : m <= mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : Co
nvexOn Real s φ) (…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ContinuousOn.lowerSemicontinuousOn`：ContinuousOn.lowerSemicontinuousOn {
f : α -> γ} (h : ContinuousOn f s) : LowerSemicontinuousOn f s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `ConvexOn.continuousOn_Ici`：ConvexOn.continuousOn_Ici {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Ici y) f) (hf_cont : ContinuousWithinAt f (I
ci y) y) : Cont…
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…
-/
lemma map_condExp_rnDeriv_le (hm : m ≤ m𝓧) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x)) ≤ᵐ[ν.trim hm]
      ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m] :=
  hf_cvx.map_condExp_le_trim hm (hf_cvx.continuousOn_Ici hf_cont_at).lowerSemicontinuousOn hf
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int
/-
**ConvexOn.comp_rnDeriv_map_le** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：comp_rnDeriv_map_le (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasur
able f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (I
ci 0) 0) (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : (fun x => 
f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal) <=ᵐ[ν] ν[fun x => f (μ.rnDeriv ν x
).toReal | m𝓨.comap g]
参数：hμν : μ ≪ ν；hg : Measurable g；hf : StronglyMeasurable f；hf_cvx : ConvexOn Rea
l (Ici 0) f；hf_cont_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun 
x => f (μ.rnDeriv ν x).toReal) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_ae_trim`：ae_of_ae_trim (hm : m <= m0) {μ : Measure α
} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用引理 `ConvexOn.map_condExp_rnDeriv_le`：map_condExp_rnDeriv_le (hm : m <= m𝓧) (
hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : Cont
inuousWithinAt f (Ici…
· 使用引理 `MeasureTheory.toReal_rnDeriv_map`：toReal_rnDeriv_map [IsFiniteMeasure μ]
 (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (
fun a => ((μ.map g).rn…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma comp_rnDeriv_map_le (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal) ≤ᵐ[ν]
      ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g] := by
  filter_upwards [toReal_rnDeriv_map hμν hg,
    ae_of_ae_trim _ <| hf_cvx.map_condExp_rnDeriv_le hg.comap_le hf hf_cont_at h_int] with a ha1 ha2
  calc f ((μ.map g).rnDeriv (ν.map g) (g a)).toReal
      = f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) a := ha2
/-
**ConvexOn.integrable_comp_rnDeriv_map** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：integrable_comp_rnDeriv_map (hμν : μ ≪ ν) (hg : Measurable g) (hf : Strong
lyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithi
nAt f (Ici 0) 0) (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : In
tegrable (fun x => f ((μ.map g).rnDeriv (ν.map g) x).toReal) (ν.map g)
参数：hμν : μ ≪ ν；hg : Measurable g；hf : StronglyMeasurable f；hf_cvx : ConvexOn Rea
l (Ici 0) f；hf_cont_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun 
x => f (μ.rnDeriv ν x).toReal) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.continuousOn_Ici`：ConvexOn.continuousOn_Ici {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Ici y) f) (hf_cont : ContinuousWithinAt f (I
ci y) y) : Cont…
· 使用引理 `ConvexOn.exists_affine_le_real`：exists_affine_le_real {s : Set Real} {f 
: Real -> Real} (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : Conve
xOn Real s f) : exis…
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.lowerSemicontinuousOn`：ContinuousOn.lowerSemicontinuousOn {
f : α -> γ} (h : ContinuousOn f s) : LowerSemicontinuousOn f s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_map_measure`：integrable_map_measure {f : α -> α
'} {g : α' -> ε} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasura
ble f μ) : Integrable g (M…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `MeasureTheory.integrable_of_le_of_le`：integrable_of_le_of_le {f g₁ g₂ : 
α -> Real} (hf : AEStronglyMeasurable f μ) (h_le₁ : g₁ <=ᵐ[μ] f) (h_le₂ : f <=ᵐ[
μ] g₂) (h_int₁ : Integrabl…
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用引理 `ConvexOn.comp_rnDeriv_map_le`：comp_rnDeriv_map_le (hμν : μ ≪ ν) (hg : Me
asurable g) (hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_c
ont_at : Continuou…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
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
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用引理 `MeasureTheory.toReal_rnDeriv_map`：toReal_rnDeriv_map [IsFiniteMeasure μ]
 (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (
fun a => ((μ.map g).rn…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
（共 33 条，此处仅展示前 30 条）
-/
lemma integrable_comp_rnDeriv_map (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) x).toReal) (ν.map g) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  rw [integrable_map_measure (StronglyMeasurable.aestronglyMeasurable (by fun_prop))
      hg.aemeasurable]
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x ↦ c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x)
    ?_ ?_ ?_ ?_ integrable_condExp
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact hf_cvx.comp_rnDeriv_map_le hμν hg hf hf_cont_at h_int
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    rw [integrable_congr (toReal_rnDeriv_map hμν hg)]
    fun_prop
/-
**ConvexOn.comp_rnDeriv_trim_le** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：comp_rnDeriv_trim_le (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable
 f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0
) 0) (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : (fun x => f ((
∂μ.trim hm/∂ν.trim hm) x).toReal) <=ᵐ[ν.trim hm] ν[fun x => f (μ.rnDeriv ν x).to
Real | m]
参数：hm : m <= m𝓧；hμν : μ ≪ ν；hf : StronglyMeasurable f；hf_cvx : ConvexOn Real (Ic
i 0) f；hf_cont_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun x => 
f (μ.rnDeriv ν x).toReal) ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ConvexOn.map_condExp_rnDeriv_le`：map_condExp_rnDeriv_le (hm : m <= m𝓧) (
hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : Cont
inuousWithinAt f (Ici…
· 使用引理 `MeasureTheory.toReal_rnDeriv_trim`：toReal_rnDeriv_trim (hm : m <= m𝓧) [I
sFiniteMeasure μ] [hsf : SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) : (fun x => ((μ.
trim hm).rnDeriv (ν.tri…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma comp_rnDeriv_trim_le (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal) ≤ᵐ[ν.trim hm]
      ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m] := by
  filter_upwards [toReal_rnDeriv_trim hm hμν,
    hf_cvx.map_condExp_rnDeriv_le hm hf hf_cont_at h_int] with a ha1 ha2
  calc f ((∂μ.trim hm/∂ν.trim hm) a).toReal
      = f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) a) := by rw [ha1]
    _ ≤ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m]) a := ha2
/-
**ConvexOn.integrable_comp_rnDeriv_trim** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：integrable_comp_rnDeriv_trim (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMe
asurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithinAt 
f (Ici 0) 0) (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : Integr
able (fun x => f ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) (ν.trim hm)
参数：hm : m <= m𝓧；hμν : μ ≪ ν；hf : StronglyMeasurable f；hf_cvx : ConvexOn Real (Ic
i 0) f；hf_cont_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun x => 
f (μ.rnDeriv ν x).toReal) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.continuousOn_Ici`：ConvexOn.continuousOn_Ici {f : Real -> Real} 
{y : Real} (hf_cvx : ConvexOn Real (Ici y) f) (hf_cont : ContinuousWithinAt f (I
ci y) y) : Cont…
· 使用引理 `ConvexOn.exists_affine_le_real`：exists_affine_le_real {s : Set Real} {f 
: Real -> Real} (hsc : IsClosed s) (hfc : LowerSemicontinuousOn f s) (hf : Conve
xOn Real s f) : exis…
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousOn.lowerSemicontinuousOn`：ContinuousOn.lowerSemicontinuousOn {
f : α -> γ} (h : ContinuousOn f s) : LowerSemicontinuousOn f s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `MeasureTheory.integrable_of_le_of_le`：integrable_of_le_of_le {f g₁ g₂ : 
α -> Real} (hf : AEStronglyMeasurable f μ) (h_le₁ : g₁ <=ᵐ[μ] f) (h_le₂ : f <=ᵐ[
μ] g₂) (h_int₁ : Integrabl…
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用引理 `ConvexOn.comp_rnDeriv_trim_le`：comp_rnDeriv_trim_le (hm : m <= m𝓧) (hμν 
: μ ≪ ν) (hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont
_at : ContinuousWit…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
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
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `MeasureTheory.Measure.integrable_toReal_rnDeriv`：∀ {𝓧 : Type u_1} {m𝓧 : 
MeasurableSpace 𝓧} {μ ν : MeasureTheory.Measure 𝓧} [MeasureTheory.IsFiniteMeasur
e μ],   MeasureTheory.Integrable (fun…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
-/
lemma integrable_comp_rnDeriv_trim (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) (ν.trim hm) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ.trim hm/∂ν.trim hm) x).toReal + c')
    (g₂ := fun x ↦ (ν[fun x ↦ f (μ.rnDeriv ν x).toReal | m]) x)
    ?_ ?_ ?_ ?_ ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact hf_cvx.comp_rnDeriv_trim_le hm hμν hf hf_cont_at h_int
  · exact (Integrable.const_mul (by fun_prop) _).add (integrable_const _)
  · exact integrable_condExp.trim hm stronglyMeasurable_condExp
/-
**ConvexOn.integrable_comp_condExp_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `ConvexOn`。
形式化陈述：integrable_comp_condExp_rnDeriv (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : Strongl
yMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : ContinuousWithin
At f (Ici 0) 0) (h_int : Integrable (fun x => f (μ.rnDeriv ν x).toReal) ν) : Int
egrable (fun x => f ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) x)) ν
参数：hm : m <= m𝓧；hμν : μ ≪ ν；hf : StronglyMeasurable f；hf_cvx : ConvexOn Real (Ic
i 0) f；hf_cont_at : ContinuousWithinAt f (Ici 0) 0；h_int : Integrable (fun x => 
f (μ.rnDeriv ν x).toReal) ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.integrable_comp_rnDeriv_trim`：integrable_comp_rnDeriv_trim (hm 
: m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ic
i 0) f) (hf_cont_at : Conti…
· 使用定理 `MeasureTheory.integrable_of_integrable_trim`：integrable_of_integrable_tr
im (hm : m <= m0) (hf_int : Integrable f (μ'.trim hm)) : Integrable f μ'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.toReal_rnDeriv_trim`：toReal_rnDeriv_trim (hm : m <= m𝓧) [I
sFiniteMeasure μ] [hsf : SigmaFinite (ν.trim hm)] (hμν : μ ≪ ν) : (fun x => ((μ.
trim hm).rnDeriv (ν.tri…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma integrable_comp_condExp_rnDeriv (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x)) ν := by
  have h := integrable_comp_rnDeriv_trim hm hμν hf hf_cvx hf_cont_at h_int
  refine integrable_of_integrable_trim hm ((integrable_congr ?_).mp h)
  filter_upwards [toReal_rnDeriv_trim hm hμν] with a ha
  rw [ha]

end ConvexOn

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {μ ν : Measure 𝓧}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : 𝓧 → 𝓨}

/-
**InformationTheory.integrable_llr_map** 是 Mathlib 中的一个引理，位于命名空间 `InformationThe
ory`。
形式化陈述：integrable_llr_map (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (
llr μ ν) μ) : Integrable (llr (μ.map g) (ν.map g)) (μ.map g)
参数：hμν : μ ≪ ν；hg : Measurable g；h_int : Integrable (llr μ ν) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InformationTheory.integrable_klFun_rnDeriv_iff`：integrable_klFun_rnDeriv
_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Inte
grable (llr μ ν) μ
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用引理 `ConvexOn.integrable_comp_rnDeriv_map`：integrable_comp_rnDeriv_map (hμν :
 μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real 
(Ici 0) f) (hf_cont_at : C…
· 使用引理 `InformationTheory.stronglyMeasurable_klFun`：stronglyMeasurable_klFun : S
tronglyMeasurable klFun
· 使用引理 `InformationTheory.convexOn_klFun`：convexOn_klFun : ConvexOn Real (Ici 0)
 klFun
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用引理 `InformationTheory.continuous_klFun`：continuous_klFun : Continuous klFun
-/
lemma integrable_llr_map (hμν : μ ≪ ν) (hg : Measurable g)
    (h_int : Integrable (llr μ ν) μ) :
    Integrable (llr (μ.map g) (ν.map g)) (μ.map g) := by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine convexOn_klFun.integrable_comp_rnDeriv_map hμν hg (by fun_prop) (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]
/-
**InformationTheory.toReal_klDiv_map_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `Informatio
nTheory`。
形式化陈述：toReal_klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) : (klDiv (μ.map g
) (ν.map g)).toReal = ∫ x, klFun ((ν[fun x => (μ.rnDeriv ν x).toReal | m𝓨.comap 
g]) x) ∂ν
参数：hμν : μ ≪ ν；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.toReal_klDiv_eq_integral_klFun`：toReal_klDiv_eq_integr
al_klFun (h : μ ≪ ν) : (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用引理 `InformationTheory.stronglyMeasurable_klFun`：stronglyMeasurable_klFun : S
tronglyMeasurable klFun
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.toReal_rnDeriv_map`：toReal_rnDeriv_map [IsFiniteMeasure μ]
 (hμν : μ ≪ ν) {g : 𝓧 -> 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g)] : (
fun a => ((μ.map g).rn…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma toReal_klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) :
    (klDiv (μ.map g) (ν.map g)).toReal =
      ∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν := by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg), integral_map hg.aemeasurable
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]
  refine integral_congr_ae ?_
  filter_upwards [toReal_rnDeriv_map hμν hg] with a ha using by rw [ha]
/-
**InformationTheory.klDiv_map_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `InformationTheory
`。
形式化陈述：klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (llr
 μ ν) μ) : klDiv (μ.map g) (ν.map g) = ENNReal.ofReal (∫ x, klFun ((ν[fun x => (
μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν)
参数：hμν : μ ≪ ν；hg : Measurable g；h_int : Integrable (llr μ ν) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_eq_integral_klFun`：klDiv_eq_integral_klFun : klD
iv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rn
Deriv ν x).toReal ∂ν) else ∞
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.map`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.M
easure α},   μ.AbsolutelyContinuous …
· 使用引理 `InformationTheory.integrable_llr_map`：integrable_llr_map (hμν : μ ≪ ν) (
hg : Measurable g) (h_int : Integrable (llr μ ν) μ) : Integrable (llr (μ.map g) 
(ν.map g)) (μ.map g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InformationTheory.toReal_klDiv_eq_integral_klFun`：toReal_klDiv_eq_integr
al_klFun (h : μ ≪ ν) : (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
· 使用引理 `InformationTheory.toReal_klDiv_map_of_ac`：toReal_klDiv_map_of_ac (hμν : 
μ ≪ ν) (hg : Measurable g) : (klDiv (μ.map g) (ν.map g)).toReal = ∫ x, klFun ((ν
[fun x => (μ.rnDeriv ν x).toRe…
-/
lemma klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (llr μ ν) μ) :
    klDiv (μ.map g) (ν.map g) =
      ENNReal.ofReal (∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m𝓨.comap g]) x) ∂ν) := by
  rw [klDiv_eq_integral_klFun, if_pos ⟨hμν.map hg, integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg), toReal_klDiv_map_of_ac hμν hg]
/-
**InformationTheory.toReal_klDiv_trim_of_ac** 是 Mathlib 中的一个引理，位于命名空间 `Informati
onTheory`。
形式化陈述：toReal_klDiv_trim_of_ac (hm : m <= m𝓧) (hμν : μ ≪ ν) : (klDiv (μ.trim hm) 
(ν.trim hm)).toReal = ∫ x, klFun ((ν[fun x => (μ.rnDeriv ν x).toReal | m]) x) ∂ν
参数：hm : m <= m𝓧；hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.trim_eq_map`：trim_eq_map (hm : m <= m0) : μ.trim hm = @Mea
sure.map _ _ _ m id μ
· 使用引理 `InformationTheory.toReal_klDiv_map_of_ac`：toReal_klDiv_map_of_ac (hμν : 
μ ≪ ν) (hg : Measurable g) : (klDiv (μ.map g) (ν.map g)).toReal = ∫ x, klFun ((ν
[fun x => (μ.rnDeriv ν x).toRe…
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasurableSpace.comap_id`：comap_id : m.comap id = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toReal_klDiv_trim_of_ac (hm : m ≤ m𝓧) (hμν : μ ≪ ν) :
    (klDiv (μ.trim hm) (ν.trim hm)).toReal =
      ∫ x, klFun ((ν[fun x ↦ (μ.rnDeriv ν x).toReal | m]) x) ∂ν := by
  simp [trim_eq_map, toReal_klDiv_map_of_ac hμν (measurable_id'' hm)]

variable (μ ν) in
/-- **Data processing inequality** for the Kullback-Leibler divergence and measurable functions. -/
/-
**InformationTheory.klDiv_map_le** 是 Mathlib 中的一个定理，位于命名空间 `InformationTheory`。
形式化陈述：klDiv_map_le (hg : Measurable g) : klDiv (μ.map g) (ν.map g) <= klDiv μ ν
参数：hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InformationTheory.klDiv_map_of_ac`：klDiv_map_of_ac (hμν : μ ≪ ν) (hg : M
easurable g) (h_int : Integrable (llr μ ν) μ) : klDiv (μ.map g) (ν.map g) = ENNR
eal.ofReal (∫ x, klFun …
· 使用引理 `InformationTheory.klDiv_eq_integral_klFun`：klDiv_eq_integral_klFun : klD
iv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, klFun (μ.rn
Deriv ν x).toReal ∂ν) else ∞
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_condExp`：integral_condExp (hm : m <= m₀) [hμm : S
igmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `InformationTheory.stronglyMeasurable_klFun`：stronglyMeasurable_klFun : S
tronglyMeasurable klFun
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用引理 `InformationTheory.continuous_klFun`：continuous_klFun : Continuous klFun
· 使用引理 `InformationTheory.integrable_klFun_rnDeriv_iff`：integrable_klFun_rnDeriv
_iff (hμν : μ ≪ ν) : Integrable (fun x => klFun (μ.rnDeriv ν x).toReal) ν ↔ Inte
grable (llr μ ν) μ
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `ConvexOn.integrable_comp_condExp_rnDeriv`：integrable_comp_condExp_rnDeri
v (hm : m <= m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f) (hf_cvx : ConvexOn Re
al (Ici 0) f) (hf_cont_at : Co…
· 使用引理 `InformationTheory.convexOn_klFun`：convexOn_klFun : ConvexOn Real (Ici 0)
 klFun
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.ae_of_ae_trim`：ae_of_ae_trim (hm : m <= m0) {μ : Measure α
} {P : α -> Prop} (h : forallᵐ x ∂μ.trim hm, P x) : forallᵐ x ∂μ, P x
· 使用引理 `ConvexOn.map_condExp_rnDeriv_le`：map_condExp_rnDeriv_le (hm : m <= m𝓧) (
hf : StronglyMeasurable f) (hf_cvx : ConvexOn Real (Ici 0) f) (hf_cont_at : Cont
inuousWithinAt f (Ici…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `InformationTheory.klDiv_of_not_integrable`：klDiv_of_not_integrable (h : 
¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
**Data processing inequality** for the Kullback-Leibler divergence and measurabl
e functions.
-/
theorem klDiv_map_le (hg : Measurable g) : klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int, klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  conv_rhs => rw [← integral_condExp hg.comap_le]
  gcongr 1
  have hf : StronglyMeasurable klFun := by fun_prop
  have hf_cont : ContinuousWithinAt klFun (Ici 0) 0 := by fun_prop
  have h_int' : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν := by
    rwa [integrable_klFun_rnDeriv_iff hμν]
  refine integral_mono_ae ?_ integrable_condExp ?_
  · exact convexOn_klFun.integrable_comp_condExp_rnDeriv hg.comap_le hμν hf hf_cont h_int'
  · refine ae_of_ae_trim hg.comap_le ?_
    exact convexOn_klFun.map_condExp_rnDeriv_le hg.comap_le hf hf_cont h_int'

variable (μ ν) in
/-- **Data processing inequality** for the Kullback-Leibler divergence and sub-sigma-algebras. -/
/-
**InformationTheory.klDiv_trim_le** 是 Mathlib 中的一个定理，位于命名空间 `InformationTheory`。
形式化陈述：klDiv_trim_le (hm : m <= m𝓧) : klDiv (μ.trim hm) (ν.trim hm) <= klDiv μ ν
参数：hm : m <= m𝓧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.trim_eq_map`：trim_eq_map (hm : m <= m0) : μ.trim hm = @Mea
sure.map _ _ _ m id μ
· 使用定理 `InformationTheory.klDiv_map_le`：klDiv_map_le (hg : Measurable g) : klDiv
 (μ.map g) (ν.map g) <= klDiv μ ν
· 使用定理 `measurable_id''`：measurable_id'' {m mα : MeasurableSpace α} (hm : m <= m
α) : @Measurable α α mα m id

--- 原说明 ---
**Data processing inequality** for the Kullback-Leibler divergence and sub-sigma
-algebras.
-/
theorem klDiv_trim_le (hm : m ≤ m𝓧) : klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν := by
  simp_rw [trim_eq_map]
  exact klDiv_map_le μ ν (measurable_id'' hm)

variable (μ ν) in
/-- The **Data Processing Inequality** for the Kullback-Leibler divergence and a Markov kernel. -/
/-
**InformationTheory.klDiv_comp_right_le** 是 Mathlib 中的一个定理，位于命名空间 `InformationTh
eory`。
形式化陈述：klDiv_comp_right_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] : klDiv (κ ∘ₘ μ) (
κ ∘ₘ ν) <= klDiv μ ν
参数：κ : Kernel 𝓧 𝓨。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.snd_compProd`：snd_compProd (μ : Measure α) [SFinit
e μ] (κ : Kernel α β) [IsSFiniteKernel κ] : (μ otimesₘ κ).snd = κ ∘ₘ μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `InformationTheory.klDiv_map_le`：klDiv_map_le (hg : Measurable g) : klDiv
 (μ.map g) (ν.map g) <= klDiv μ ν
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用引理 `InformationTheory.klDiv_compProd_left`：klDiv_compProd_left : klDiv (μ ot
imesₘ κ) (ν otimesₘ κ) = klDiv μ ν

--- 原说明 ---
The **Data Processing Inequality** for the Kullback-Leibler divergence and a Mar
kov kernel.
-/
theorem klDiv_comp_right_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν :=
  calc klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) := by
    rw [← Measure.snd_compProd, ← Measure.snd_compProd]
    exact klDiv_map_le _ _ measurable_snd
  _ = klDiv μ ν := klDiv_compProd_left μ ν κ

end InformationTheory

