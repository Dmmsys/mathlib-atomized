/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

The file also contains properties of `rnDeriv` that use the Radon-Nikodym theorem, notably
* `MeasureTheory.Measure.rnDeriv_withDensity_left`: the Radon-Nikodym derivative of
  `μ.withDensity f` with respect to `ν` is `f * μ.rnDeriv ν`.
* `MeasureTheory.Measure.rnDeriv_withDensity_right`: the Radon-Nikodym derivative of
  `μ` with respect to `ν.withDensity f` is `f⁻¹ * μ.rnDeriv ν`.
* `MeasureTheory.Measure.inv_rnDeriv`: `(μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ`.
* `MeasureTheory.Measure.setLIntegral_rnDeriv`: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` if `μ ≪ ν`.
  There is also a version of this result for the Bochner integral.

## Tags

Radon-Nikodym theorem
-/

public section

assert_not_exists InnerProductSpace
assert_not_exists MeasureTheory.VectorMeasure

noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

/-
**MeasureTheory.Measure.withDensity_rnDeriv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (
h : μ ≪ ν) : ν.withDensity (rnDeriv μ ν) = μ
参数：μ ν : Measure α；h : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MeasureTheory.Measure.singularPart_eq_zero`：singularPart_eq_zero (μ ν : 
Measure α) [μ.HaveLebesgueDecomposition ν] : μ.singularPart ν = 0 ↔ μ ≪ ν
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  suffices μ.singularPart ν = 0 by
    conv_rhs => rw [haveLebesgueDecomposition_add μ ν, this, zero_add]
  exact (singularPart_eq_zero μ ν).mpr h

variable {μ ν : Measure α}

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.withDensity (rnDeriv μ ν) = μ`. -/
/-
**MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：absolutelyContinuous_iff_withDensity_rnDeriv_eq [HaveLebesgueDecomposition
 μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ

--- 原说明 ---
**The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous to `ν` if and
 only if
`ν.withDensity (rnDeriv μ ν) = μ`.
-/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq
    [HaveLebesgueDecomposition μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩
/-
**MeasureTheory.Measure.rnDeriv_pos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 
0 < μ.rnDeriv ν x
参数：hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.ae_withDensity_iff`：ae_withDensity_iff {p : α -> Prop} {f 
: α -> Real>=0∞} (hf : Measurable f) : (forallᵐ x ∂μ.withDensity f, p x) ↔ foral
lᵐ x ∂μ, f x != 0 -> p…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := by
  rw [← Measure.withDensity_rnDeriv_eq _ _ hμν,
    ae_withDensity_iff (Measure.measurable_rnDeriv _ _), Measure.withDensity_rnDeriv_eq _ _ hμν]
  exact ae_of_all _ (fun x hx ↦ hx.pos)
/-
**MeasureTheory.Measure.rnDeriv_pos'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：rnDeriv_pos' [HaveLebesgueDecomposition ν μ] [SigmaFinite μ] (hμν : μ ≪ ν)
 : forallᵐ x ∂μ, 0 < ν.rnDeriv μ x
参数：hμν : μ ≪ ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv`：absolute
lyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
 μ ≪ μ.withDensity (ν.rnDeriv μ)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rnDeriv_pos' [HaveLebesgueDecomposition ν μ] [SigmaFinite μ] (hμν : μ ≪ ν) :
    ∀ᵐ x ∂μ, 0 < ν.rnDeriv μ x := by
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_le ?_
  filter_upwards [Measure.rnDeriv_pos (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)),
    (withDensity_absolutelyContinuous μ (ν.rnDeriv μ)).ae_le
    (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ))] with x hx hx2
  rwa [← hx2]

section rnDeriv_withDensity_leftRight

variable {f : α → ℝ≥0∞}

/-- Auxiliary lemma for `rnDeriv_withDensity_left`. -/
/-
**MeasureTheory.Measure.rnDeriv_withDensity_withDensity_rnDeriv_left** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_withDensity_rnDeriv_left (μ ν : Measure α) [SigmaFinit
e μ] [SigmaFinite ν] (hf_ne_top : forallᵐ x ∂μ, f x != ∞) : ((ν.withDensity (μ.r
nDeriv ν)).withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν
参数：μ ν : Measure α；hf_ne_top : forallᵐ x ∂μ, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.withDensity_add_measure`：withDensity_add_measure {m : Meas
urableSpace α} (μ ν : Measure α) (f : α -> Real>=0∞) : (μ + ν).withDensity f = μ
.withDensity f + ν.withDens…
· 使用定理 `MeasureTheory.SigmaFinite.withDensity_of_ne_top`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] {
f : α → ENNReal},   (∀ᵐ (x : α) ∂μ, f…
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_of_mutuallySingular`：rnDeriv_add_of_mu
tuallySingular (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFin
ite μ] (h : ν₂ ⟂ₘ μ) : (ν₁ + ν₂).rnDeriv μ …
· 使用定理 `MeasureTheory.Measure.MutuallySingular.withDensity`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : α → ENNReal},   μ.Mut
uallySingular ν → (μ.withDensity f).Mutu…
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν

--- 原说明 ---
Auxiliary lemma for `rnDeriv_withDensity_left`.
-/
lemma rnDeriv_withDensity_withDensity_rnDeriv_left (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    ((ν.withDensity (μ.rnDeriv ν)).withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm, withDensity_add_measure]
  have : SigmaFinite ((μ.singularPart ν).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.singularPart_le _ _) hf_ne_top)
  have : SigmaFinite ((ν.withDensity (μ.rnDeriv ν)).withDensity f) :=
    SigmaFinite.withDensity_of_ne_top (ae_mono (Measure.withDensity_rnDeriv_le _ _) hf_ne_top)
  exact (rnDeriv_add_of_mutuallySingular _ _ _ (mutuallySingular_singularPart μ ν).withDensity).symm

/-- Auxiliary lemma for `rnDeriv_withDensity_right`. -/
/-
**MeasureTheory.Measure.rnDeriv_withDensity_withDensity_rnDeriv_right** 是 Mathli
b 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_withDensity_rnDeriv_right (μ ν : Measure α) [SigmaFini
te μ] [SigmaFinite ν] (hf : AEMeasurable f ν) (hf_ne_zero : forallᵐ x ∂ν, f x !=
 0) (hf_ne_top : forallᵐ x ∂ν, f x != ∞) : (ν.withDensity (μ.rnDeriv ν)).rnDeriv
 (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f)
参数：μ ν : Measure α；hf : AEMeasurable f ν；hf_ne_zero : forallᵐ x ∂ν, f x != 0；hf_
ne_top : forallᵐ x ∂ν, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `MeasureTheory.withDensity_absolutelyContinuous'`：withDensity_absolutelyC
ontinuous' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_ze
ro : forallᵐ x ∂μ, f x != 0) : μ ≪ μ.…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用定理 `MeasureTheory.SigmaFinite.withDensity_of_ne_top`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] {
f : α → ENNReal},   (∀ᵐ (x : α) ∂μ, f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_of_mutuallySingular`：rnDeriv_add_of_mu
tuallySingular (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFin
ite μ] (h : ν₂ ⟂ₘ μ) : (ν₁ + ν₂).rnDeriv μ …
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.withDensity`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : α → ENNReal},   μ.Mut
uallySingular ν → (μ.withDensity f).Mutu…
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν

--- 原说明 ---
Auxiliary lemma for `rnDeriv_withDensity_right`.
-/
lemma rnDeriv_withDensity_withDensity_rnDeriv_right (μ ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0)
    (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    (ν.withDensity (μ.rnDeriv ν)).rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) := by
  conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have hν_ac : ν ≪ ν.withDensity f := withDensity_absolutelyContinuous' hf hf_ne_zero
  refine hν_ac.ae_eq ?_
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (rnDeriv_add_of_mutuallySingular _ _ _ ?_).symm
  exact ((mutuallySingular_singularPart μ ν).symm.withDensity).symm
/-
**MeasureTheory.Measure.rnDeriv_withDensity_left_of_absolutelyContinuous** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFin
ite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) : (μ.withDensity f)
.rnDeriv ν =ᵐ[ν] fun x => f x * μ.rnDeriv ν x
参数：hμν : μ ≪ ν；hf : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv₀`：eq_rnDeriv₀ [SigmaFinite ν] {s : Meas
ure α} {f : α -> Real>=0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s +
 ν.withDensity f) : f =…
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurabl
e₀`：setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
 {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f (μ.restric…
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  refine (Measure.eq_rnDeriv₀ ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact hf.mul (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
    · congr with x
      rw [mul_comm]
      simp only [Pi.mul_apply]
    · refine ae_restrict_of_ae ?_
      exact Measure.rnDeriv_lt_top _ _
    · exact (Measure.measurable_rnDeriv _ _).aemeasurable
/-
**MeasureTheory.Measure.rnDeriv_withDensity_left** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
 (hfν : AEMeasurable f ν) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) : (μ.withDensity 
f).rnDeriv ν =ᵐ[ν] fun x => f x * μ.rnDeriv ν x
参数：hfν : AEMeasurable f ν；hf_ne_top : forallᵐ x ∂μ, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_left_of_absolutelyContinuous`：
rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
 [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) : (μ.…
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_withDensity_rnDeriv_left`：rnDe
riv_withDensity_withDensity_rnDeriv_left (μ ν : Measure α) [SigmaFinite μ] [Sigm
aFinite ν] (hf_ne_top : forallᵐ x ∂μ, f x != ∞) : ((ν.wi…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rnDeriv_withDensity_left {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    (hfν : AEMeasurable f ν) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have hμ'ν : μ' ≪ ν := withDensity_absolutelyContinuous _ _
  have h := rnDeriv_withDensity_left_of_absolutelyContinuous hμ'ν hfν
  have h1 : μ'.rnDeriv ν =ᵐ[ν] μ.rnDeriv ν :=
    Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have h2 : (μ'.withDensity f).rnDeriv ν =ᵐ[ν] (μ.withDensity f).rnDeriv ν := by
    exact rnDeriv_withDensity_withDensity_rnDeriv_left μ ν hf_ne_top
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  rw [← hx2, hx, hx1]

/-- Auxiliary lemma for `rnDeriv_withDensity_right`. -/
/-
**MeasureTheory.Measure.rnDeriv_withDensity_right_of_absolutelyContinuous** 是 Ma
thlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α} [HaveLeb
esgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) (h
f_ne_zero : forallᵐ x ∂ν, f x != 0) (hf_ne_top : forallᵐ x ∂ν, f x != ∞) : μ.rnD
eriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * μ.rnDeriv ν x
参数：hμν : μ ≪ ν；hf : AEMeasurable f ν；hf_ne_zero : forallᵐ x ∂ν, f x != 0；hf_ne_t
op : forallᵐ x ∂ν, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SigmaFinite.withDensity_of_ne_top`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] {
f : α → ENNReal},   (∀ᵐ (x : α) ∂μ, f…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用引理 `MeasureTheory.withDensity_absolutelyContinuous'`：withDensity_absolutelyC
ontinuous' {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_ze
ro : forallᵐ x ∂μ, f x != 0) : μ ≪ μ.…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.eq_rnDeriv₀`：eq_rnDeriv₀ [SigmaFinite ν] {s : Meas
ure α} {f : α -> Real>=0∞} (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s +
 ν.withDensity f) : f =…
· 使用定理 `AEMeasurable.mul`：AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (f * g) μ
· 使用引理 `AEMeasurable.mono_ac`：mono_ac (hf : AEMeasurable f ν) (hμν : μ ≪ ν) : AE
Measurable f μ
· 使用定理 `AEMeasurable.inv`：AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurabl
e f⁻¹ μ
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.zero_left`：zero_left : 0 ⟂ₘ μ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul_non_measurabl
e₀`：setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ (μ : Measure α)
 {f : α -> Real>=0∞} {s : Set α} (hf : AEMeasurable f (μ.restric…
· 使用定理 `AEMeasurable.restrict`：AEMeasurable.restrict (hfm : AEMeasurable f μ) {s
} : AEMeasurable f (μ.restrict s)
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
Auxiliary lemma for `rnDeriv_withDensity_right`.
-/
lemma rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α}
    [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν)
    (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  have : SigmaFinite (ν.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_ne_top
  refine (withDensity_absolutelyContinuous' hf hf_ne_zero).ae_eq ?_
  refine (Measure.eq_rnDeriv₀ (ν := ν.withDensity f) ?_ Measure.MutuallySingular.zero_left ?_).symm
  · exact (hf.inv.mono_ac (withDensity_absolutelyContinuous _ _)).mul
      (Measure.measurable_rnDeriv _ _).aemeasurable
  · ext1 s hs
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    rw [zero_add, withDensity_apply _ hs, withDensity_apply _ hs]
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
    · simp only [Pi.mul_apply]
      have : (fun a ↦ f a * ((f a)⁻¹ * μ.rnDeriv ν a)) =ᵐ[ν] μ.rnDeriv ν := by
        filter_upwards [hf_ne_zero, hf_ne_top] with x hx1 hx2
        simp [← mul_assoc, ENNReal.mul_inv_cancel, hx1, hx2]
      rw [lintegral_congr_ae (ae_restrict_of_ae this)]
    · refine ae_restrict_of_ae ?_
      filter_upwards [hf_ne_top] with x hx using hx.lt_top
    · exact hf.restrict
/-
**MeasureTheory.Measure.rnDeriv_withDensity_right** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν
] (hf : AEMeasurable f ν) (hf_ne_zero : forallᵐ x ∂ν, f x != 0) (hf_ne_top : for
allᵐ x ∂ν, f x != ∞) : μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x => (f x)⁻¹ * μ.rn
Deriv ν x
参数：μ ν : Measure α；hf : AEMeasurable f ν；hf_ne_zero : forallᵐ x ∂ν, f x != 0；hf_
ne_top : forallᵐ x ∂ν, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_withDensity_rnDeriv_right`：rnD
eriv_withDensity_withDensity_rnDeriv_right (μ ν : Measure α) [SigmaFinite μ] [Si
gmaFinite ν] (hf : AEMeasurable f ν) (hf_ne_zero : forall…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_right_of_absolutelyContinuous`
：rnDeriv_withDensity_right_of_absolutelyContinuous {ν : Measure α} [HaveLebesgue
Decomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeas…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x := by
  let μ' := ν.withDensity (μ.rnDeriv ν)
  have h₁ : μ'.rnDeriv (ν.withDensity f) =ᵐ[ν] μ.rnDeriv (ν.withDensity f) :=
    rnDeriv_withDensity_withDensity_rnDeriv_right μ ν hf hf_ne_zero hf_ne_top
  have h₂ : μ.rnDeriv ν =ᵐ[ν] μ'.rnDeriv ν :=
    (Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)).symm
  have hμ' := rnDeriv_withDensity_right_of_absolutelyContinuous
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hf hf_ne_zero hf_ne_top
  filter_upwards [h₁, h₂, hμ'] with x hx₁ hx₂ hx_eq
  rw [← hx₁, hx₂, hx_eq]

end rnDeriv_withDensity_leftRight

/-
**MeasureTheory.Measure.rnDeriv_eq_zero_of_mutuallySingular** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_eq_zero_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecompos
ition μ ν'] [SigmaFinite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') : μ.rnDeriv ν' =ᵐ[ν] 0
参数：h : μ ⟂ₘ ν；hνν' : ν ≪ ν'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.rnDeriv_restrict`：rnDeriv_restrict (μ ν : Measure 
α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] {s : Set α} (hs : MeasurableS
et s) : (μ.restrict s).rnDer…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_nullSet`：restrict_nullSe
t (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0
· 使用引理 `MeasureTheory.Measure.rnDeriv_zero`：rnDeriv_zero (ν : Measure α) : (0 : 
Measure α).rnDeriv ν =ᵐ[ν] 0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.trans`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ₁ μ₂ μ₃ : MeasureTheory.Measure α},   μ₁.AbsolutelyContinu
ous μ₂ → μ₂.AbsolutelyContinuous μ₃ → …
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_compl_nullSet`：restrict_
compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
-/
lemma rnDeriv_eq_zero_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν']
    [SigmaFinite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') :
    μ.rnDeriv ν' =ᵐ[ν] 0 := by
  let t := h.nullSet
  have ht : MeasurableSet t := h.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t ?_ (by simp [t])
  change μ.rnDeriv ν' =ᵐ[ν.restrict t] 0
  have : μ.rnDeriv ν' =ᵐ[ν.restrict t] (μ.restrict t).rnDeriv ν' := by
    have h : (μ.restrict t).rnDeriv ν' =ᵐ[ν] t.indicator (μ.rnDeriv ν') :=
      hνν'.ae_le (rnDeriv_restrict μ ν' ht)
    rw [Filter.EventuallyEq, ae_restrict_iff' ht]
    filter_upwards [h] with x hx hxt
    rw [hx, Set.indicator_of_mem hxt]
  refine this.trans ?_
  simp only [t, MutuallySingular.restrict_nullSet]
  suffices (0 : Measure α).rnDeriv ν' =ᵐ[ν'] 0 by
    have h_ac' : ν.restrict t ≪ ν' := restrict_le_self.absolutelyContinuous.trans hνν'
    exact h_ac'.ae_le this
  exact rnDeriv_zero _

variable (μ ν) in
/-
**MeasureTheory.Measure.rnDeriv_eq_zero_ae_singularPart** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_eq_zero_ae_singularPart [SigmaFinite μ] [SigmaFinite ν] : forallᵐ 
x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero_of_mutuallySingular`：rnDeriv_eq_ze
ro_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν'] [SigmaF
inite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') : μ.rnDe…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `LE.le.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ
 ν : MeasureTheory.Measure α}, μ ≤ ν → μ.AbsolutelyContinuous ν
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
-/
lemma rnDeriv_eq_zero_ae_singularPart [SigmaFinite μ] [SigmaFinite ν] :
    ∀ᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := by
  refine rnDeriv_eq_zero_of_mutuallySingular (mutuallySingular_singularPart ν μ).symm ?_
  exact (Measure.singularPart_le _ _).absolutelyContinuous

/-- Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`. -/
/-
**MeasureTheory.Measure.rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySin
gular** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular {ν' : Measur
e α} [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition μ (ν + ν')] [Sig
maFinite ν] (hμν : μ ≪ ν) (hνν' : ν ⟂ₘ ν') : μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv 
ν
参数：ν + ν'；hμν : μ ≪ ν；hνν' : ν ⟂ₘ ν'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.MutuallySingular.measurableSet_nullSet`：measurable
Set_nullSet (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_nullSet`：restrict_nullSe
t (h : μ ⟂ₘ ν) : μ.restrict h.nullSet = 0
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_add`：restrict_add {_m0 : MeasurableSpace 
α} (μ ν : Measure α) (s : Set α) : (μ + ν).restrict s = μ.restrict s + ν.restric
t s
· 使用引理 `MeasureTheory.Measure.MutuallySingular.restrict_compl_nullSet`：restrict_
compl_nullSet (h : μ ⟂ₘ ν) : ν.restrict h.nullSetᶜ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.restrict_withDensity`：restrict_withDensity {s : Set α} (hs
 : MeasurableSet s) (f : α -> Real>=0∞) : (μ.withDensity f).restrict s = (μ.rest
rict s).withDensity f
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'

--- 原说明 ---
Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`.
-/
lemma rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular {ν' : Measure α}
    [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition μ (ν + ν')] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  let t := hνν'.nullSet
  have ht : MeasurableSet t := hνν'.measurableSet_nullSet
  refine ae_of_ae_restrict_of_ae_restrict_compl t (by simp [t]) ?_
  change μ.rnDeriv (ν + ν') =ᵐ[ν.restrict tᶜ] μ.rnDeriv ν
  rw [← withDensity_eq_iff_of_sigmaFinite (μ := ν.restrict tᶜ)
    (Measure.measurable_rnDeriv _ _).aemeasurable (Measure.measurable_rnDeriv _ _).aemeasurable]
  have : (ν.restrict tᶜ).withDensity (μ.rnDeriv (ν + ν'))
      = ((ν + ν').restrict tᶜ).withDensity (μ.rnDeriv (ν + ν')) := by simp [t]
  rw [this, ← restrict_withDensity ht.compl, ← restrict_withDensity ht.compl,
      Measure.withDensity_rnDeriv_eq _ _ (hμν.add_right ν'), Measure.withDensity_rnDeriv_eq _ _ hμν]

/-- Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`. -/
/-
**MeasureTheory.Measure.rnDeriv_add_right_of_mutuallySingular'** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_add_right_of_mutuallySingular' {ν' : Measure α} [SigmaFinite μ] [S
igmaFinite ν] [SigmaFinite ν'] (hμν' : μ ⟂ₘ ν') (hνν' : ν ⟂ₘ ν') : μ.rnDeriv (ν 
+ ν') =ᵐ[ν] μ.rnDeriv ν
参数：hμν' : μ ⟂ₘ ν'；hνν' : ν ⟂ₘ ν'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_right_of_absolutelyContinuous_of_mutua
llySingular`：rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular {ν' :
 Measure α} [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition μ …
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.MutuallySingular.singularPart`：∀ {α : Type u_1} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.MutuallySingular ν → 
∀ (ν' : MeasureTheory.Measure α), (μ.sing…
· 使用引理 `MeasureTheory.Measure.rnDeriv_singularPart`：rnDeriv_singularPart (μ ν : 
Measure α) : (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f

--- 原说明 ---
Auxiliary lemma for `rnDeriv_add_right_of_mutuallySingular`.
-/
lemma rnDeriv_add_right_of_mutuallySingular' {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν']
    (hμν' : μ ⟂ₘ ν') (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν]
  have h₁ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_absolutelyContinuous_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) hνν'
  have h₄ : (μ.singularPart ν).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
    refine h_ac.ae_eq ?_
    simp only [rnDeriv_eq_zero, MutuallySingular.add_right_iff]
    exact ⟨mutuallySingular_singularPart μ ν, hμν'.singularPart ν⟩
  have h₅ : (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := rnDeriv_singularPart μ ν
  filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
  simp only [Pi.add_apply]
  rw [hx₃, hx₄, hx₅]
/-
**MeasureTheory.Measure.rnDeriv_add_right_of_mutuallySingular** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_add_right_of_mutuallySingular {ν' : Measure α} [SigmaFinite μ] [Si
gmaFinite ν] [SigmaFinite ν'] (hνν' : ν ⟂ₘ ν') : μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDe
riv ν
参数：hνν' : ν ⟂ₘ ν'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_right_of_mutuallySingular'`：rnDeriv_ad
d_right_of_mutuallySingular' {ν' : Measure α} [SigmaFinite μ] [SigmaFinite ν] [S
igmaFinite ν'] (hμν' : μ ⟂ₘ ν') (hνν' : ν ⟂ₘ ν') :…
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero_of_mutuallySingular`：rnDeriv_eq_ze
ro_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν'] [SigmaF
inite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') : μ.rnDe…
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.withDensity`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : α → ENNReal},   μ.Mut
uallySingular ν → (μ.withDensity f).Mutu…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero`：rnDeriv_eq_zero (μ ν : Measure α)
 [μ.HaveLebesgueDecomposition ν] : μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
lemma rnDeriv_add_right_of_mutuallySingular {ν' : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ν'] (hνν' : ν ⟂ₘ ν') :
    μ.rnDeriv (ν + ν') =ᵐ[ν] μ.rnDeriv ν := by
  have h_ac : ν ≪ ν + ν' := Measure.AbsolutelyContinuous.rfl.add_right _
  rw [haveLebesgueDecomposition_add μ ν']
  have h₁ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) (ν + ν')
  have h₂ := rnDeriv_add' (μ.singularPart ν') (ν'.withDensity (μ.rnDeriv ν')) ν
  refine (Filter.EventuallyEq.trans (h_ac.ae_le h₁) ?_).trans h₂.symm
  have h₃ := rnDeriv_add_right_of_mutuallySingular' (?_ : μ.singularPart ν' ⟂ₘ ν') hνν'
  · have h₄ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv (ν + ν') =ᵐ[ν] 0 := by
      refine rnDeriv_eq_zero_of_mutuallySingular ?_ h_ac
      exact hνν'.symm.withDensity
    have h₅ : (ν'.withDensity (rnDeriv μ ν')).rnDeriv ν =ᵐ[ν] 0 := by
      rw [rnDeriv_eq_zero]
      exact hνν'.symm.withDensity
    filter_upwards [h₃, h₄, h₅] with x hx₃ hx₄ hx₅
    rw [Pi.add_apply, Pi.add_apply, hx₃, hx₄, hx₅]
  exact mutuallySingular_singularPart μ ν'
/-
**MeasureTheory.Measure.rnDeriv_withDensity_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：rnDeriv_withDensity_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) 
: μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)) =ᵐ[μ] μ.rnDeriv ν
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`：∀ {α : Type u_1} {δ : 
Type u_3} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.Absolute
lyContinuous ν → ∀ {f g : α → δ}, f =ᵐ…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv`：absolute
lyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
 μ ≪ μ.withDensity (ν.rnDeriv μ)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_right_of_mutuallySingular`：rnDeriv_add
_right_of_mutuallySingular {ν' : Measure α} [SigmaFinite μ] [SigmaFinite ν] [Sig
maFinite ν'] (hνν' : ν ⟂ₘ ν') : μ.rnDeriv (ν + ν'…
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.withDensity`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} {f : α → ENNReal},   μ.Mut
uallySingular ν → (μ.withDensity f).Mutu…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.symm`：symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
-/
lemma rnDeriv_withDensity_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)) =ᵐ[μ] μ.rnDeriv ν := by
  conv_rhs => rw [ν.haveLebesgueDecomposition_add μ, add_comm]
  refine (absolutelyContinuous_withDensity_rnDeriv hμν).ae_eq ?_
  exact (rnDeriv_add_right_of_mutuallySingular
    (Measure.mutuallySingular_singularPart ν μ).symm.withDensity).symm

/-- Auxiliary lemma for `inv_rnDeriv`. -/
/-
**MeasureTheory.Measure.inv_rnDeriv_aux** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：inv_rnDeriv_aux [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition
 ν μ] [SigmaFinite μ] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) : (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDe
riv μ
参数：hμν : μ ≪ ν；hνμ : ν ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.withDensity_inv_same`：withDensity_inv_same {μ : Measure α}
 {f : α -> Real>=0∞} (hf : Measurable f) (hf_ne_zero : forallᵐ x ∂μ, f x != 0) (
hf_ne_top : forallᵐ x ∂μ…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `MeasureTheory.Measure.rnDeriv_ne_top`：rnDeriv_ne_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `Measurable.inv`：Measurable.inv (hf : Measurable f) : Measurable f⁻¹

--- 原说明 ---
Auxiliary lemma for `inv_rnDeriv`.
-/
lemma inv_rnDeriv_aux [HaveLebesgueDecomposition μ ν] [HaveLebesgueDecomposition ν μ]
    [SigmaFinite μ] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices μ.withDensity (μ.rnDeriv ν)⁻¹ = μ.withDensity (ν.rnDeriv μ) by
    calc (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.withDensity (μ.rnDeriv ν)⁻¹).rnDeriv μ :=
          (rnDeriv_withDensity _ (measurable_rnDeriv _ _).inv).symm
    _ = (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ := by rw [this]
    _ =ᵐ[μ] ν.rnDeriv μ := rnDeriv_withDensity _ (measurable_rnDeriv _ _)
  rw [withDensity_rnDeriv_eq _ _ hνμ, ← withDensity_rnDeriv_eq _ _ hμν]
  conv in ((ν.withDensity (μ.rnDeriv ν)).rnDeriv ν)⁻¹ => rw [withDensity_rnDeriv_eq _ _ hμν]
  change (ν.withDensity (μ.rnDeriv ν)).withDensity (fun x ↦ (μ.rnDeriv ν x)⁻¹) = ν
  rw [withDensity_inv_same (measurable_rnDeriv _ _)
    (by filter_upwards [hνμ.ae_le (rnDeriv_pos hμν)] with x hx using hx.ne')
    (rnDeriv_ne_top _ _)]
/-
**MeasureTheory.Measure.inv_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : (μ.rnDeriv ν)⁻
¹ =ᵐ[μ] ν.rnDeriv μ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_rnDeriv`：rnDeriv_withDensity_r
nDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : μ.rnDeriv (μ.withDensity 
(ν.rnDeriv μ)) =ᵐ[μ] μ.rnDeriv ν
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MeasureTheory.Measure.inv_rnDeriv_aux`：inv_rnDeriv_aux [HaveLebesgueDeco
mposition μ ν] [HaveLebesgueDecomposition ν μ] [SigmaFinite μ] (hμν : μ ≪ ν) (hν
μ : ν ≪ μ) : (μ.rnDeriv ν)⁻…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用引理 `MeasureTheory.Measure.absolutelyContinuous_withDensity_rnDeriv`：absolute
lyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
 μ ≪ μ.withDensity (ν.rnDeriv μ)
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ := by
  suffices (μ.rnDeriv ν)⁻¹ =ᵐ[μ] (μ.rnDeriv (μ.withDensity (ν.rnDeriv μ)))⁻¹
      ∧ ν.rnDeriv μ =ᵐ[μ] (μ.withDensity (ν.rnDeriv μ)).rnDeriv μ by
    refine (this.1.trans (Filter.EventuallyEq.trans ?_ this.2.symm))
    exact Measure.inv_rnDeriv_aux (absolutelyContinuous_withDensity_rnDeriv hμν)
      (withDensity_absolutelyContinuous _ _)
  constructor
  · filter_upwards [rnDeriv_withDensity_rnDeriv hμν] with x hx
    simp only [Pi.inv_apply, inv_inj]
    exact hx.symm
  · exact (Measure.rnDeriv_withDensity μ (Measure.measurable_rnDeriv ν μ)).symm
/-
**MeasureTheory.Measure.inv_rnDeriv'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：inv_rnDeriv' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : (ν.rnDeriv μ)
⁻¹ =ᵐ[μ] μ.rnDeriv ν
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.inv_rnDeriv`：inv_rnDeriv [SigmaFinite μ] [SigmaFin
ite ν] (hμν : μ ≪ ν) : (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_rnDeriv' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (ν.rnDeriv μ)⁻¹ =ᵐ[μ] μ.rnDeriv ν := by
  filter_upwards [inv_rnDeriv hμν] with x hx; simp only [Pi.inv_apply, ← hx, inv_inv]

variable (ν) in
/-
**MeasureTheory.Measure.ae_rnDeriv_ne_zero_imp_of_ae** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α -> Pro
p} (h : forallᵐ a ∂μ, p a) : forallᵐ a ∂ν, μ.rnDeriv ν a != 0 -> p a
参数：h : forallᵐ a ∂μ, p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.ae_add_measure_iff`：∀ {α : Type u_2} {m0 : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {p : α → Prop} {ν : MeasureTheory.Measure α}, 
  (∀ᵐ (x : α) ∂μ + ν, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero_ae_singularPart`：rnDeriv_eq_zero_a
e_singularPart [SigmaFinite μ] [SigmaFinite ν] : forallᵐ x ∂(ν.singularPart μ), 
μ.rnDeriv ν x = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
-/
lemma ae_rnDeriv_ne_zero_imp_of_ae [SigmaFinite μ] [SigmaFinite ν] {p : α → Prop}
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → p a := by
  rw [ν.haveLebesgueDecomposition_add μ, ae_add_measure_iff]
  constructor
  · rw [← ν.haveLebesgueDecomposition_add μ]
    have : ∀ᵐ x ∂(ν.singularPart μ), μ.rnDeriv ν x = 0 := μ.rnDeriv_eq_zero_ae_singularPart ν
    filter_upwards [this] with x hx h_absurd using absurd hx h_absurd
  · have h_ac : μ.withDensity (ν.rnDeriv μ) ≪ μ := withDensity_absolutelyContinuous _ _
    rw [← ν.haveLebesgueDecomposition_add μ]
    suffices ∀ᵐx ∂μ, μ.rnDeriv ν x ≠ 0 → p x from h_ac this
    filter_upwards [h] with _ h _ using h

section integral

/-
**MeasureTheory.Measure.setLIntegral_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：setLIntegral_rnDeriv_le (s : Set α) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν <= μ s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.withDensity_apply_le`：withDensity_apply_le (f : α -> Real>
=0∞) (s : Set α) : ∫⁻ a in s, f a ∂μ <= μ.withDensity f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.le_iff'`：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂
 s
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
-/
lemma setLIntegral_rnDeriv_le (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s :=
  (withDensity_apply_le _ _).trans (Measure.le_iff'.1 (withDensity_rnDeriv_le μ ν) s)
/-
**MeasureTheory.Measure.lintegral_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：lintegral_rnDeriv_le : ∫⁻ x, μ.rnDeriv ν x ∂ν <= μ Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv_le`：setLIntegral_rnDeriv_le (
s : Set α) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν <= μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
-/
lemma lintegral_rnDeriv_le : ∫⁻ x, μ.rnDeriv ν x ∂ν ≤ μ Set.univ :=
  (setLIntegral_univ _).symm ▸ Measure.setLIntegral_rnDeriv_le Set.univ
/-
**MeasureTheory.Measure.setLIntegral_rnDeriv'** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：setLIntegral_rnDeriv' [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : S
et α} (hs : MeasurableSet s) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s
参数：hμν : μ ≪ ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
-/
lemma setLIntegral_rnDeriv' [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply _ hs, Measure.withDensity_rnDeriv_eq _ _ hμν]
/-
**MeasureTheory.Measure.setLIntegral_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：setLIntegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν] (hμν : μ 
≪ ν) (s : Set α) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s
参数：hμν : μ ≪ ν；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
-/
lemma setLIntegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν]
    (hμν : μ ≪ ν) (s : Set α) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s := by
  rw [← withDensity_apply' _ s, Measure.withDensity_rnDeriv_eq _ _ hμν]
/-
**MeasureTheory.Measure.lintegral_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) : ∫⁻ x, μ.
rnDeriv ν x ∂ν = μ Set.univ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv'`：setLIntegral_rnDeriv' [Have
LebesgueDecomposition μ ν] (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) : ∫⁻
 x in s, μ.rnDeriv ν x ∂ν = μ s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma lintegral_rnDeriv [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ∂ν = μ Set.univ := by
  rw [← setLIntegral_univ, setLIntegral_rnDeriv' hμν MeasurableSet.univ]
/-
**MeasureTheory.Measure.integrableOn_toReal_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s != ∞) : IntegrableOn (f
un x => (μ.rnDeriv ν x).toReal) s ν
参数：hμs : μ s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_toReal_of_lintegral_ne_top`：integrable_toReal_o
f_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hfi : ∫⁻ x, f x
 ∂μ != ∞) : Integrable (fun x => (f x).to…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv_le`：setLIntegral_rnDeriv_le (
s : Set α) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν <= μ s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma integrableOn_toReal_rnDeriv {s : Set α} (hμs : μ s ≠ ∞) :
    IntegrableOn (fun x ↦ (μ.rnDeriv ν x).toReal) s ν := by
  refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable ?_
  exact ((setLIntegral_rnDeriv_le _).trans_lt hμs.lt_top).ne
/-
**MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity'** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：setIntegral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ] {s : Set α} (hs
 : MeasurableSet s) : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rn
Deriv ν)).real s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_toReal_iff`：toReal_eq_toReal_iff (x y : Real>=0∞) : x.
toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma setIntegral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν)).real s := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable, measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply _ hs]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)
/-
**MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：setIntegral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s :
 Set α) : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν)).re
al s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `ENNReal.toReal_eq_toReal_iff`：toReal_eq_toReal_iff (x y : Real>=0∞) : x.
toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma setIntegral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.rnDeriv ν)).real s := by
  rw [integral_toReal (Measure.measurable_rnDeriv _ _).aemeasurable, measureReal_def]
  · rw [ENNReal.toReal_eq_toReal_iff, ← withDensity_apply' _ s]
    simp
  · exact ae_restrict_of_ae (Measure.rnDeriv_lt_top _ _)
/-
**MeasureTheory.Measure.setIntegral_toReal_rnDeriv_le** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory.Measure`。
形式化陈述：setIntegral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s != ∞)
 : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν <= μ.real s
参数：hμs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.setIntegral_mono_set`：setIntegral_mono_set [OrderClosedTop
ology E] (hfi : IntegrableOn f t μ) (hf : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ]
 t) : ∫ x in s, f x ∂μ <…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `MeasureTheory.Measure.integrableOn_toReal_rnDeriv`：integrableOn_toReal_r
nDeriv {s : Set α} (hμs : μ s != ∞) : IntegrableOn (fun x => (μ.rnDeriv ν x).toR
eal) s ν
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity'`：setInt
egral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ] {s : Set α} (hs : Measurabl
eSet s) : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.wit…
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_le`：withDensity_rnDeriv_le (μ 
ν : Measure α) : ν.withDensity (μ.rnDeriv ν) <= μ
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
lemma setIntegral_toReal_rnDeriv_le [SigmaFinite μ] {s : Set α} (hμs : μ s ≠ ∞) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν ≤ μ.real s := by
  set t := toMeasurable μ s with ht
  have ht_m : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t ≠ ∞ := by rwa [ht, measure_toMeasurable s]
  calc ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν
    ≤ ∫ x in t, (μ.rnDeriv ν x).toReal ∂ν := by
        refine setIntegral_mono_set ?_ ?_ (LE.le.eventuallyLE (subset_toMeasurable _ _))
        · exact integrableOn_toReal_rnDeriv hμt
        · exact ae_of_all _ (by simp)
  _ = (withDensity ν (rnDeriv μ ν)).real t := setIntegral_toReal_rnDeriv_eq_withDensity' ht_m
  _ ≤ μ.real t := by
        simp only [measureReal_def]
        gcongr
        apply withDensity_rnDeriv_le
  _ = μ.real s := by rw [measureReal_def, measureReal_def, measure_toMeasurable s]
/-
**MeasureTheory.Measure.setIntegral_toReal_rnDeriv'** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：setIntegral_toReal_rnDeriv' [SigmaFinite μ] [HaveLebesgueDecomposition μ ν
] (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) : ∫ x in s, (μ.rnDeriv ν x).t
oReal ∂ν = μ.real s
参数：hμν : μ ≪ ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity'`：setInt
egral_toReal_rnDeriv_eq_withDensity' [SigmaFinite μ] {s : Set α} (hs : Measurabl
eSet s) : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.wit…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
lemma setIntegral_toReal_rnDeriv' [SigmaFinite μ] [HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity' hs, Measure.withDensity_rnDeriv_eq _ _ hμν,
    measureReal_def]
/-
**MeasureTheory.Measure.setIntegral_toReal_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：setIntegral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (
s : Set α) : ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s
参数：hμν : μ ≪ ν；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity`：setInte
gral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) : ∫ x
 in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
-/
lemma setIntegral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s := by
  rw [setIntegral_toReal_rnDeriv_eq_withDensity s, Measure.withDensity_rnDeriv_eq _ _ hμν]
/-
**MeasureTheory.Measure.integral_toReal_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) : ∫ 
x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv`：setIntegral_toReal_rnD
eriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫ x in s, (μ.rn
Deriv ν x).toReal ∂ν = μ.real s
-/
lemma integral_toReal_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ := by
  rw [← setIntegral_univ, setIntegral_toReal_rnDeriv hμν Set.univ]
/-
**MeasureTheory.Measure.integral_toReal_rnDeriv'** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：integral_toReal_rnDeriv' [IsFiniteMeasure μ] [SigmaFinite ν] : ∫ x, (μ.rnD
eriv ν x).toReal ∂ν = μ.real Set.univ - (μ.singularPart ν).real Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.toReal_sub_of_le`：toReal_sub_of_le (hba : b <= a) (ha : a != ∞) 
: (a - b).toReal = a.toReal - b.toReal
· 使用定理 `MeasureTheory.Measure.singularPart_le`：singularPart_le (μ ν : Measure α)
 : μ.singularPart ν <= μ
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.Measure.sub_apply`：sub_apply [IsFiniteMeasure ν] (h₁ : Mea
surableSet s) (h₂ : ν <= μ) : (μ - ν) s = μ s - ν s
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `MeasureTheory.Measure.measure_sub_singularPart`：measure_sub_singularPart
 (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [IsFiniteMeasure μ] : μ - μ.s
ingularPart ν = ν.withDensity (μ.rnD…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.setIntegral_toReal_rnDeriv_eq_withDensity`：setInte
gral_toReal_rnDeriv_eq_withDensity [SigmaFinite μ] [SFinite ν] (s : Set α) : ∫ x
 in s, (μ.rnDeriv ν x).toReal ∂ν = (ν.withDensity (μ.…
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
-/
lemma integral_toReal_rnDeriv' [IsFiniteMeasure μ] [SigmaFinite ν] :
    ∫ x, (μ.rnDeriv ν x).toReal ∂ν = μ.real Set.univ - (μ.singularPart ν).real Set.univ := by
  rw [measureReal_def, measureReal_def,
    ← ENNReal.toReal_sub_of_le (μ.singularPart_le ν Set.univ) (measure_ne_top _ _),
    ← Measure.sub_apply .univ (Measure.singularPart_le μ ν), Measure.measure_sub_singularPart,
    ← measureReal_def, ← Measure.setIntegral_toReal_rnDeriv_eq_withDensity, setIntegral_univ]

end integral

/-
**MeasureTheory.Measure.rnDeriv_mul_rnDeriv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：rnDeriv_mul_rnDeriv {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [Sigma
Finite κ] (hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_left`：rnDeriv_withDensity_left
 {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) (hf_
ne_top : forallᵐ x ∂μ, f x != ∞) : (…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用引理 `MeasureTheory.Measure.rnDeriv_ne_top`：rnDeriv_ne_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
lemma rnDeriv_mul_rnDeriv {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hμν : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ := by
  refine (rnDeriv_withDensity_left ?_ ?_).symm.trans ?_
  · exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · exact rnDeriv_ne_top _ _
  · rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
/-
**MeasureTheory.Measure.rnDeriv_mul_rnDeriv'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：rnDeriv_mul_rnDeriv' {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [Sigm
aFinite κ] (hνκ : ν ≪ κ) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[ν] μ.rnDeriv κ
参数：hνκ : ν ≪ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_spec`：haveLebesgueDecomp
osition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] : Measurable 
(μ.rnDeriv ν) ∧ μ.singularPart ν ⟂ₘ ν ∧ μ …
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero_of_mutuallySingular`：rnDeriv_eq_ze
ro_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν'] [SigmaF
inite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') : μ.rnDe…
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用引理 `MeasureTheory.Measure.rnDeriv_withDensity_left_of_absolutelyContinuous`：
rnDeriv_withDensity_left_of_absolutelyContinuous {ν : Measure α} [SigmaFinite μ]
 [SigmaFinite ν] (hμν : μ ≪ ν) (hf : AEMeasurable f ν) : (μ.…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `MeasureTheory.Measure.withDensity.instSigmaFinite`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ
],   MeasureTheory.SigmaFinite (ν.withD…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma rnDeriv_mul_rnDeriv' {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hνκ : ν ≪ κ) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[ν] μ.rnDeriv κ := by
  obtain ⟨h_meas, h_sing, hμν⟩ := Measure.haveLebesgueDecomposition_spec μ ν
  filter_upwards [hνκ <| Measure.rnDeriv_add' (μ.singularPart ν) (ν.withDensity (μ.rnDeriv ν)) κ,
    hνκ <| Measure.rnDeriv_withDensity_left_of_absolutelyContinuous hνκ h_meas.aemeasurable,
    Measure.rnDeriv_eq_zero_of_mutuallySingular h_sing hνκ] with x hx1 hx2 hx3
  nth_rw 2 [hμν]
  rw [hx1, Pi.add_apply, hx2, Pi.mul_apply, hx3, Pi.zero_apply, zero_add]
/-
**MeasureTheory.Measure.rnDeriv_le_one_of_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：rnDeriv_le_one_of_le (hμν : μ <= ν) [SigmaFinite ν] : μ.rnDeriv ν <=ᵐ[ν] 1
参数：hμν : μ <= ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.Measure.setLIntegral_rnDeriv_le`：setLIntegral_rnDeriv_le (
s : Set α) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν <= μ s
-/
lemma rnDeriv_le_one_of_le (hμν : μ ≤ ν) [SigmaFinite ν] : μ.rnDeriv ν ≤ᵐ[ν] 1 := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s _ _ ↦ ?_
  simp only [Pi.one_apply, MeasureTheory.setLIntegral_one]
  exact (Measure.setLIntegral_rnDeriv_le s).trans (hμν s)
/-
**MeasureTheory.Measure.rnDeriv_le_one_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：rnDeriv_le_one_iff_le [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν
 : μ ≪ ν) : μ.rnDeriv ν <=ᵐ[ν] 1 ↔ μ <= ν
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.withDensity_apply'`：withDensity_apply' [SFinite μ] (f : α 
-> Real>=0∞) (s : Set α) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
· 使用定理 `MeasureTheory.setLIntegral_mono_ae`：setLIntegral_mono_ae {s : Set α} {f 
g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s)) (hfg : forallᵐ x ∂μ, x i
n s -> f x <= g x) : ∫⁻ …
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `MeasureTheory.Measure.rnDeriv_le_one_of_le`：rnDeriv_le_one_of_le (hμν : 
μ <= ν) [SigmaFinite ν] : μ.rnDeriv ν <=ᵐ[ν] 1
-/
lemma rnDeriv_le_one_iff_le [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν ≤ᵐ[ν] 1 ↔ μ ≤ ν := by
  refine ⟨fun h s ↦ ?_, fun h ↦ rnDeriv_le_one_of_le h⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν, withDensity_apply', ← setLIntegral_one]
  exact setLIntegral_mono_ae aemeasurable_const (h.mono fun _ hh _ ↦ hh)
/-
**MeasureTheory.Measure.rnDeriv_eq_one_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：rnDeriv_eq_one_iff_eq [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν
 : μ ≪ ν) : μ.rnDeriv ν =ᵐ[ν] 1 ↔ μ = ν
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.withDensity_congr_ae`：withDensity_congr_ae {f g : α -> Rea
l>=0∞} (h : f =ᵐ[μ] g) : μ.withDensity f = μ.withDensity g
· 使用定理 `MeasureTheory.withDensity_one`：withDensity_one : μ.withDensity 1 = μ
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
-/
lemma rnDeriv_eq_one_iff_eq [HaveLebesgueDecomposition μ ν] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν] 1 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ν.rnDeriv_self⟩
  rw [← withDensity_rnDeriv_eq _ _ hμν, withDensity_congr_ae h, withDensity_one]

section Ratio

/-
**MeasureTheory.Measure.rnDeriv_add_self** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：rnDeriv_add_self (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnD
eriv (ν + μ) =ᵐ[μ] fun x => (ν.rnDeriv μ x + 1)⁻¹
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right'`：add_right' (h : μ
 ≪ ν') (ν : Measure α) : μ ≪ ν + ν'
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.inv_rnDeriv`：inv_rnDeriv [SigmaFinite μ] [SigmaFin
ite ν] (hμν : μ ≪ ν) : (μ.rnDeriv ν)⁻¹ =ᵐ[μ] ν.rnDeriv μ
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.inv_apply`：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
-/
lemma rnDeriv_add_self (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (ν + μ) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x + 1)⁻¹ := by
  have hν_ac : μ ≪ ν + μ := rfl.absolutelyContinuous.add_right' _
  filter_upwards [ν.rnDeriv_add' μ μ, μ.rnDeriv_self, Measure.inv_rnDeriv hν_ac] with a h1 h2 h3
  rw [Pi.inv_apply, h1, Pi.add_apply, h2, inv_eq_iff_eq_inv] at h3
  rw [h3]
/-
**MeasureTheory.Measure.rnDeriv_self_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：rnDeriv_self_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnD
eriv (μ + ν) =ᵐ[ν] fun x => μ.rnDeriv ν x / (μ.rnDeriv ν x + 1)
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_add_measure_iff`：∀ {α : Type u_2} {m0 : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {p : α → Prop} {ν : MeasureTheory.Measure α}, 
  (∀ᵐ (x : α) ∂μ + ν, …
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用引理 `MeasureTheory.Measure.rnDeriv_self`：rnDeriv_self (μ : Measure α) [SigmaF
inite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ => 1
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_self`：rnDeriv_add_self (μ ν : Measure 
α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnDeriv (ν + μ) =ᵐ[μ] fun x => (ν.rnDeriv
 μ x + 1)⁻¹
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddLECancellable.add_tsub_cancel_right`：∀ {α : Type u_1} [inst : Partial
Order α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b : α}
,   AddLECancellable b → a +…
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.sub_eq_of_eq_add`：∀ {a b c : ENNReal}, b ≠ ⊤ → a = c + b → a - b
 = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 33 条，此处仅展示前 30 条）
-/
lemma rnDeriv_self_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[ν] fun x ↦ μ.rnDeriv ν x / (μ.rnDeriv ν x + 1) := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[ν] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (μ.rnDeriv_add' ν (μ + ν))).2
  have h_one_add := (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).2
  have : (μ.rnDeriv (μ + ν)) =ᵐ[ν] fun x ↦ 1 - (μ.rnDeriv ν x + 1)⁻¹ := by
    filter_upwards [h_add, h_one_add, rnDeriv_add_self ν μ] with a h4 h5 h6
    rw [h5, Pi.add_apply] at h4
    nth_rw 1 [h4, h6]
    simp
  filter_upwards [this, μ.rnDeriv_lt_top ν] with a ha ha_lt_top
  rw [ha, div_eq_mul_inv]
  refine ENNReal.sub_eq_of_eq_add (by simp) ?_
  nth_rewrite 2 [← one_mul (μ.rnDeriv ν a + 1)⁻¹]
  have h := add_mul (μ.rnDeriv ν a) 1 (μ.rnDeriv ν a + 1)⁻¹
  rwa [ENNReal.mul_inv_cancel (by simp) (by simp [ha_lt_top.ne])] at h
/-
**MeasureTheory.Measure.rnDeriv_eq_div_rnDeriv_add** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：rnDeriv_eq_div_rnDeriv_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite 
ν] : μ.rnDeriv ν =ᵐ[ν] fun x => μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用引理 `MeasureTheory.Measure.rnDeriv_self_add`：rnDeriv_self_add (μ ν : Measure 
α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnDeriv (μ + ν) =ᵐ[ν] fun x => μ.rnDeriv 
ν x / (μ.rnDeriv ν x + 1)
· 使用引理 `MeasureTheory.Measure.rnDeriv_add_self`：rnDeriv_add_self (μ ν : Measure 
α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnDeriv (ν + μ) =ᵐ[μ] fun x => (ν.rnDeriv
 μ x + 1)⁻¹
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.div_eq_inv_mul`：∀ {a b : ENNReal}, a / b = b⁻¹ * a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma rnDeriv_eq_div_rnDeriv_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  filter_upwards [rnDeriv_add_self ν μ, rnDeriv_self_add μ ν, μ.rnDeriv_lt_top ν]
      with a ha1 ha2 ha_lt_top
  rw [ha1, ha2, ENNReal.div_eq_inv_mul, inv_inv, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel, one_mul]
  · simp
  · simp [ha_lt_top.ne]
/-
**MeasureTheory.Measure.rnDeriv_div_rnDeriv_eq_div_rnDeriv_add** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：rnDeriv_div_rnDeriv_eq_div_rnDeriv_add {ξ : Measure α} [SigmaFinite μ] [Si
gmaFinite ν] [SigmaFinite ξ] (hμ : μ ≪ ξ) (hν : ν ≪ ξ) : (fun x => μ.rnDeriv ξ x
 / ν.rnDeriv ξ x) =ᵐ[μ + ν] fun x => μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x
参数：hμ : μ ≪ ξ；hν : ν ≪ ξ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_mul_rnDeriv`：rnDeriv_mul_rnDeriv {κ : Meas
ure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ] (hμν : μ ≪ ν) : μ.rnDeriv
 ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeri…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right`：add_right (h1 : μ 
≪ ν) (ν' : Measure α) : μ ≪ ν + ν'
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right'`：add_right' (h : μ
 ≪ ν') (ν : Measure α) : μ ≪ ν + ν'
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_left`：add_left {μ₁ μ₂ ν :
 Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.Measure.rnDeriv_pos`：rnDeriv_pos [HaveLebesgueDecompositio
n μ ν] (hμν : μ ≪ ν) : forallᵐ x ∂μ, 0 < μ.rnDeriv ν x
· 使用定理 `MeasureTheory.Measure.HaveLebesgueDecomposition.add_left`：∀ {α : Type u_
1} {m : MeasurableSpace α} {μ ν μ' : MeasureTheory.Measure α} [μ.HaveLebesgueDec
omposition ν]   [μ'.HaveLebesgueDecomposition …
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.mul_inv`：∀ {a b : ENNReal}, a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊤ ∨ b ≠ 0 → (a *
 b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma rnDeriv_div_rnDeriv_eq_div_rnDeriv_add {ξ : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    (fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x)
      =ᵐ[μ + ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have h1 : μ.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] μ.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right _)
  have h2 : ν.rnDeriv (μ + ν) * (μ + ν).rnDeriv ξ =ᵐ[ξ] ν.rnDeriv ξ :=
    Measure.rnDeriv_mul_rnDeriv (rfl.absolutelyContinuous.add_right' _)
  have h_ac : μ + ν ≪ ξ := hμ.add_left hν
  filter_upwards [h_ac h1, h_ac h2, h_ac <| (μ + ν).rnDeriv_lt_top ξ, ν.rnDeriv_lt_top (μ + ν),
    Measure.rnDeriv_pos h_ac] with a h1 h2 h_lt_top1 h_lt_top2 h_pos
  rw [← h1, ← h2, Pi.mul_apply, Pi.mul_apply, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr h_lt_top1.ne) (Or.inl h_lt_top2.ne), div_eq_mul_inv, mul_assoc,
    mul_comm ((μ + ν).rnDeriv ξ a), mul_assoc, ENNReal.inv_mul_cancel h_pos.ne' h_lt_top1.ne,
    mul_one]

/-- For any measure `ξ` dominating `μ` and `ν`, the Radon-Nikodym derivative of `μ` with respect to
`ν` is `ν`-almost everywhere equal to the ratio of the Radon-Nikodym derivatives of `μ` and `ν` with
respect to `ξ`. -/
/-
**MeasureTheory.Measure.rnDeriv_eq_div** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：rnDeriv_eq_div {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinit
e ξ] (hμ : μ ≪ ξ) (hν : ν ≪ ξ) : μ.rnDeriv ν =ᵐ[ν] fun x => μ.rnDeriv ξ x / ν.rn
Deriv ξ x
参数：hμ : μ ≪ ξ；hν : ν ≪ ξ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.AbsolutelyContinuous.add_right'`：add_right' (h : μ
 ≪ ν') (ν : Measure α) : μ ≪ ν + ν'
· 使用定理 `Eq.absolutelyContinuous`：∀ {α : Type u_1} {mα : MeasurableSpace α} {μ ν 
: MeasureTheory.Measure α}, μ = ν → μ.AbsolutelyContinuous ν
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.rnDeriv_div_rnDeriv_eq_div_rnDeriv_add`：rnDeriv_di
v_rnDeriv_eq_div_rnDeriv_add {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [Si
gmaFinite ξ] (hμ : μ ≪ ξ) (hν : ν ≪ ξ) : (fun x =>…
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_div_rnDeriv_add`：rnDeriv_eq_div_rnDeriv
_add (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] : μ.rnDeriv ν =ᵐ[ν] fun x
 => μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For any measure `ξ` dominating `μ` and `ν`, the Radon-Nikodym derivative of `μ` 
with respect to
`ν` is `ν`-almost everywhere equal to the ratio of the Radon-Nikodym derivatives
 of `μ` and `ν` with
respect to `ξ`.
-/
lemma rnDeriv_eq_div {ξ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x := by
  have hν_ac : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  filter_upwards [μ.rnDeriv_eq_div_rnDeriv_add ν,
    hν_ac (rnDeriv_div_rnDeriv_eq_div_rnDeriv_add hμ hν)] with a h1 h2 using h1.trans h2.symm

end Ratio

section MeasurableEmbedding

variable {mβ : MeasurableSpace β} {f : α → β}

/-
**MeasureTheory.Measure._root_.MeasurableEmbedding.rnDeriv_map_aux** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.rnDeriv_map_aux (hf : MeasurableEmbedding f)
    (hμν : μ ≪ ν) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x ↦ (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite ?_ ?_ (fun s _ _ ↦ ?_)
  · exact (Measure.measurable_rnDeriv _ _).comp hf.measurable
  · exact Measure.measurable_rnDeriv _ _
  rw [← hf.lintegral_map, Measure.setLIntegral_rnDeriv hμν]
  have hs_eq : s = f ⁻¹' f '' s := by rw [hf.injective.preimage_image]
  have : SigmaFinite (ν.map f) := hf.sigmaFinite_map
  rw [hs_eq, ← hf.restrict_map, Measure.setLIntegral_rnDeriv (hf.absolutelyContinuous_map hμν),
    hf.map_apply]
/-
**MeasureTheory.Measure._root_.MeasurableEmbedding.rnDeriv_map** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.rnDeriv_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (fun x ↦ (μ.map f).rnDeriv (ν.map f) (f x)) =ᵐ[ν] μ.rnDeriv ν := by
  rw [μ.haveLebesgueDecomposition_add ν, Measure.map_add _ _ hf.measurable]
  have : SigmaFinite (map f ν) := hf.sigmaFinite_map
  have : SigmaFinite (map f (μ.singularPart ν)) := hf.sigmaFinite_map
  have : SigmaFinite (map f (ν.withDensity (μ.rnDeriv ν))) := hf.sigmaFinite_map
  have h_add := Measure.rnDeriv_add' ((μ.singularPart ν).map f)
    ((ν.withDensity (μ.rnDeriv ν)).map f) (ν.map f)
  rw [Filter.EventuallyEq, hf.ae_map_iff, ← Filter.EventuallyEq] at h_add
  refine h_add.trans ((Measure.rnDeriv_add' _ _ _).trans ?_).symm
  refine Filter.EventuallyEq.add ?_ ?_
  · refine (Measure.rnDeriv_singularPart μ ν).trans ?_
    symm
    suffices (fun x ↦ ((μ.singularPart ν).map f).rnDeriv (ν.map f) x) =ᵐ[ν.map f] 0 by
      rw [Filter.EventuallyEq, hf.ae_map_iff] at this
      exact this
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ Measure.AbsolutelyContinuous.rfl
    exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)
  · exact (hf.rnDeriv_map_aux (withDensity_absolutelyContinuous _ _)).symm
/-
**MeasureTheory.Measure._root_.MeasurableEmbedding.map_withDensity_rnDeriv** 是 M
athlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.map_withDensity_rnDeriv (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (ν.withDensity (μ.rnDeriv ν)).map f = (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    setLIntegral_map hs (Measure.measurable_rnDeriv _ _) hf.measurable]
  refine setLIntegral_congr_fun_ae (hf.measurable hs) ?_
  filter_upwards [hf.rnDeriv_map μ ν] with a ha _ using ha.symm
/-
**MeasureTheory.Measure._root_.MeasurableEmbedding.singularPart_map** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasurableEmbedding.singularPart_map (hf : MeasurableEmbedding f)
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    (μ.map f).singularPart (ν.map f) = (μ.singularPart ν).map f := by
  have h_add : μ.map f = (μ.singularPart ν).map f
      + (ν.map f).withDensity ((μ.map f).rnDeriv (ν.map f)) := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.map_add _ _ hf.measurable, ← hf.map_withDensity_rnDeriv μ ν]
  refine (Measure.eq_singularPart (Measure.measurable_rnDeriv _ _) ?_ h_add).symm
  exact hf.mutuallySingular_map (μ.mutuallySingular_singularPart ν)

end MeasurableEmbedding

end Measure

section IntegralRNDerivMul

open Measure

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/-
**MeasureTheory.lintegral_rnDeriv_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α
 -> Real>=0∞} (hf : AEMeasurable f ν) : ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x
 ∂μ
参数：hμν : μ ≪ ν；hf : AEMeasurable f ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀`：lintegral_withDen
sity_eq_lintegral_mul₀ {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasurable f 
μ) {g : α -> Real>=0∞} (hg : AEMeasurable g…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) : ∫⁻ x, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x, f x ∂μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf]
  simp only [Pi.mul_apply]
/-
**MeasureTheory.setLIntegral_rnDeriv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setLIntegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f 
: α -> Real>=0∞} (hf : AEMeasurable f ν) {s : Set α} (hs : MeasurableSet s) : ∫⁻
 x in s, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x in s, f x ∂μ
参数：hμν : μ ≪ ν；hf : AEMeasurable f ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用引理 `MeasureTheory.setLIntegral_withDensity_eq_lintegral_mul₀`：setLIntegral_w
ithDensity_eq_lintegral_mul₀ {μ : Measure α} {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) {g : α -> Real>=0∞} (hg : AEMeasurabl…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma setLIntegral_rnDeriv_mul [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x * f x ∂ν = ∫⁻ x in s, f x ∂μ := by
  nth_rw 2 [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  rw [setLIntegral_withDensity_eq_lintegral_mul₀ (measurable_rnDeriv μ ν).aemeasurable hf hs]
  simp only [Pi.mul_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HaveLebesgueDecomposition μ ν]
  [SigmaFinite μ] {f : α → E}
/-
**MeasureTheory.integrable_rnDeriv_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integrable_rnDeriv_smul_iff (hμν : μ ≪ ν) : Integrable (fun x => (μ.rnDeri
v ν x).toReal • f x) ν ↔ Integrable f μ
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul'`：integrable_wi
thDensity_iff_integrable_smul' {f : α -> Real>=0∞} (hf : Measurable f) (hflt : f
orallᵐ x ∂μ, f x < ∞) {g : α -> E} : Integrable…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integrable_rnDeriv_smul_iff (hμν : μ ≪ ν) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable f μ := by
  nth_rw 2 [← withDensity_rnDeriv_eq μ ν hμν]
  rw [← integrable_withDensity_iff_integrable_smul' (E := E)
    (measurable_rnDeriv μ ν) (rnDeriv_lt_top μ ν)]
/-
**MeasureTheory.integrable_toReal_rnDeriv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integrable_toReal_rnDeriv_mul_iff (hμν : μ ≪ ν) {f : α -> Real} : Integrab
le (fun x => (μ.rnDeriv ν x).toReal * f x) ν ↔ Integrable f μ
参数：hμν : μ ≪ ν。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_rnDeriv_smul_iff`：integrable_rnDeriv_smul_iff (
hμν : μ ≪ ν) : Integrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν ↔ Integrable
 f μ
-/
lemma integrable_toReal_rnDeriv_mul_iff (hμν : μ ≪ ν) {f : α → ℝ} :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * f x) ν ↔ Integrable f μ :=
  integrable_rnDeriv_smul_iff hμν
/-
**MeasureTheory.integral_rnDeriv_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_rnDeriv_smul (hμν : μ ≪ ν) : ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν
 = ∫ x, f x ∂μ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_withDensity_eq_integral_toReal_smul`：integral_withDensity_eq_in
tegral_toReal_smul {f : X -> Real>=0∞} (f_meas : Measurable f) (hf_lt_top : fora
llᵐ x ∂μ, f x < ∞) (g : X -> E) : …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
-/
theorem integral_rnDeriv_smul (hμν : μ ≪ ν) :
    ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ := by
  rw [← integral_withDensity_eq_integral_toReal_smul (measurable_rnDeriv _ _) (rnDeriv_lt_top _ _),
    withDensity_rnDeriv_eq _ _ hμν]
/-
**MeasureTheory.integral_toReal_rnDeriv_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α -> Real} : ∫ x, (μ.rnDeri
v ν x).toReal * f x ∂ν = ∫ x, f x ∂μ
参数：hμν : μ ≪ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_rnDeriv_smul`：integral_rnDeriv_smul (hμν : μ ≪ ν)
 : ∫ x, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x, f x ∂μ
-/
lemma integral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α → ℝ} :
    ∫ x, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x, f x ∂μ := integral_rnDeriv_smul hμν

/-- See also `setIntegral_rnDeriv_smul'` for a version that requires both measures to be σ-finite,
but doesn't require `s` to be a measurable set. -/
/-
**MeasureTheory.setIntegral_rnDeriv_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setIntegral_rnDeriv_smul (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) 
: ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ
参数：hμν : μ ≪ ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul`：setIntegral_withDens
ity_eq_setIntegral_toReal_smul {f : X -> Real>=0∞} {s : Set X} (hf : Measurable 
f) (hf_top : forallᵐ x ∂μ.restrict s, f …
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ

--- 原说明 ---
See also `setIntegral_rnDeriv_smul'` for a version that requires both measures t
o be σ-finite,
but doesn't require `s` to be a measurable set.
-/
lemma setIntegral_rnDeriv_smul (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul, withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _), hs]

/-- See also `setIntegral_toReal_rnDeriv_mul'` for a version that requires both measures to be
σ-finite, but doesn't require `s` to be a measurable set. -/
/-
**MeasureTheory.setIntegral_toReal_rnDeriv_mul** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：setIntegral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α -> Real} {s : Set α} (
hs : MeasurableSet s) : ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f 
x ∂μ
参数：hμν : μ ≪ ν；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.setIntegral_rnDeriv_smul`：setIntegral_rnDeriv_smul (hμν : 
μ ≪ ν) {s : Set α} (hs : MeasurableSet s) : ∫ x in s, (μ.rnDeriv ν x).toReal • f
 x ∂ν = ∫ x in s, f x ∂μ

--- 原说明 ---
See also `setIntegral_toReal_rnDeriv_mul'` for a version that requires both meas
ures to be
σ-finite, but doesn't require `s` to be a measurable set.
-/
lemma setIntegral_toReal_rnDeriv_mul (hμν : μ ≪ ν) {f : α → ℝ} {s : Set α} (hs : MeasurableSet s) :
    ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f x ∂μ :=
  setIntegral_rnDeriv_smul hμν hs

omit [HaveLebesgueDecomposition μ ν] in
/-- A version of `setIntegral_rnDeriv_smul` that requires both measures to be σ-finite,
but doesn't require `s` to be a measurable set. -/
/-
**MeasureTheory.setIntegral_rnDeriv_smul'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：setIntegral_rnDeriv_smul' [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫ x 
in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ
参数：hμν : μ ≪ ν；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul'`：setIntegral_withDen
sity_eq_setIntegral_toReal_smul' [SFinite μ] {f : X -> Real>=0∞} (s : Set X) (hf
 : Measurable f) (hf_top : forallᵐ x ∂μ.r…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Measure.rnDeriv_lt_top`：rnDeriv_lt_top (μ ν : Measure α) [
SigmaFinite μ] : forallᵐ x ∂ν, μ.rnDeriv ν x < ∞
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…

--- 原说明 ---
A version of `setIntegral_rnDeriv_smul` that requires both measures to be σ-fini
te,
but doesn't require `s` to be a measurable set.
-/
lemma setIntegral_rnDeriv_smul' [SigmaFinite ν] (hμν : μ ≪ ν) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_withDensity_eq_setIntegral_toReal_smul', withDensity_rnDeriv_eq _ _ hμν]
  exacts [measurable_rnDeriv _ _, ae_restrict_of_ae (rnDeriv_lt_top _ _)]

omit [HaveLebesgueDecomposition μ ν] in
/-- A version of `setIntegral_toReal_rnDeriv_mul` that requires both measures to be σ-finite,
but doesn't require `s` to be a measurable set. -/
/-
**MeasureTheory.setIntegral_toReal_rnDeriv_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory`。
形式化陈述：setIntegral_toReal_rnDeriv_mul' [SigmaFinite ν] (hμν : μ ≪ ν) (f : α -> Re
al) (s : Set α) : ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f x ∂μ
参数：hμν : μ ≪ ν；f : α -> Real；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.setIntegral_rnDeriv_smul'`：setIntegral_rnDeriv_smul' [Sigm
aFinite ν] (hμν : μ ≪ ν) (s : Set α) : ∫ x in s, (μ.rnDeriv ν x).toReal • f x ∂ν
 = ∫ x in s, f x ∂μ

--- 原说明 ---
A version of `setIntegral_toReal_rnDeriv_mul` that requires both measures to be 
σ-finite,
but doesn't require `s` to be a measurable set.
-/
lemma setIntegral_toReal_rnDeriv_mul' [SigmaFinite ν] (hμν : μ ≪ ν) (f : α → ℝ) (s : Set α) :
    ∫ x in s, (μ.rnDeriv ν x).toReal * f x ∂ν = ∫ x in s, f x ∂μ :=
  setIntegral_rnDeriv_smul' hμν s

end IntegralRNDerivMul

section Conv

open Measure

variable {G : Type*} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [IsMulLeftInvariant μ]

@[to_additive]
/-
**MeasureTheory.mconv_eq_withDensity_mlconvolution_rnDeriv** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：mconv_eq_withDensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G}
 [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ] (hν₁ : ν₁ ≪ μ
) (hν₂ : ν₂ ≪ μ) : ν₁ ∗ₘ ν₂ = μ.withDensity (ν₁.rnDeriv μ ⋆ₘₗ[μ] ν₂.rnDeriv μ)
参数：hν₁ : ν₁ ≪ μ；hν₂ : ν₂ ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.mconv_withDensity_eq_mlconvolution`：mconv_withDensity_eq_m
lconvolution {f g : G -> Real>=0∞} (hf : Measurable f) (hg : Measurable g) : μ.w
ithDensity f ∗ₘ μ.withDensity g = μ.wi…
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
-/
theorem mconv_eq_withDensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G}
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    ν₁ ∗ₘ ν₂ = μ.withDensity (ν₁.rnDeriv μ ⋆ₘₗ[μ] ν₂.rnDeriv μ) := by
  rw [← mconv_withDensity_eq_mlconvolution (by fun_prop) (by fun_prop),
    withDensity_rnDeriv_eq _ _ hν₁, withDensity_rnDeriv_eq _ _ hν₂]

@[to_additive]
/-
**MeasureTheory.HaveLebesgueDecomposition.mconv** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.HaveLebesgueDecomposition`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] {mG : MeasurableSpace G} [MeasurableMul₂
 G] [MeasurableInv G]   {μ : MeasureTheory.Measure G} [μ.IsMulLeftInvariant] [Me
asureTheory.SFinite μ] {ν₁ ν₂ : MeasureTheory.Measure G}   [ν₁.HaveLebesgueDecom
position μ] [ν₂.HaveLebesgueDecomposition μ],   ν₁.AbsolutelyContinuous μ → ν₂.A
bsolutelyContinuous μ → (ν₁.mconv ν₂).HaveLebesgueDecomposition μ
参数：ν₁.mconv ν₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurable_mlconvolution`：measurable_mlconvolution {f g : 
G -> Real>=0∞} (μ : Measure G) [SFinite μ] (hf : Measurable f) (hg : Measurable 
g) : Measurable (f ⋆ₘₗ[μ] g)
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.mconv_eq_withDensity_mlconvolution_rnDeriv`：mconv_eq_withD
ensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G} [ν₁.HaveLebesgueDec
omposition μ] [ν₂.HaveLebesgueDecomposition μ]…
-/
theorem HaveLebesgueDecomposition.mconv [SFinite μ] {ν₁ ν₂ : Measure G}
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) : (ν₁ ∗ₘ ν₂).HaveLebesgueDecomposition μ :=
  ⟨⟨0, (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)⟩, by fun_prop, by simp,
    by simpa using mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂⟩

@[to_additive]
/-
**MeasureTheory.rnDeriv_mconv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFini
teMeasure ν₂] [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ] 
(hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) : (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ]
 (ν₂.rnDeriv μ)
参数：hν₁ : ν₁ ≪ μ；hν₂ : ν₂ ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HaveLebesgueDecomposition.mconv`：∀ {G : Type u_3} [inst : 
Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G]   {μ : Me
asureTheory.Measure G} [μ.IsMulLeft…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff`：withDensity_eq_iff {f g : α -> Real>=0
∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ != ∞) : μ
.withDensity f = μ.wit…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.aemeasurable_mlconvolution`：aemeasurable_mlconvolution {f 
g : G -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurabl
e (f ⋆ₘₗ[μ] g) μ
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.Measure.lintegral_rnDeriv_lt_top`：lintegral_rnDeriv_lt_top
 (μ ν : Measure α) [IsFiniteMeasure μ] : ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.mconv_absolutelyContinuous`：mconv_absolutelyContin
uous [MeasurableMul₂ M] {μ ν ρ : Measure M} [IsMulLeftInvariant ρ] [SFinite ν] (
hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.mconv_eq_withDensity_mlconvolution_rnDeriv`：mconv_eq_withD
ensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G} [ν₁.HaveLebesgueDec
omposition μ] [ν₂.HaveLebesgueDecomposition μ]…
-/
theorem rnDeriv_mconv [SFinite μ] {ν₁ ν₂ : Measure G} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ) := by
  have := HaveLebesgueDecomposition.mconv hν₁ hν₂
  rw [← withDensity_eq_iff (by fun_prop) (by fun_prop),
    withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂),
    mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂]
  exact (lintegral_rnDeriv_lt_top (ν₁ ∗ₘ ν₂) μ).ne

@[to_additive]
/-
**MeasureTheory.rnDeriv_mconv'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_mconv' [SigmaFinite μ] {ν₁ ν₂ : Measure G} [SigmaFinite ν₁] [Sigma
Finite ν₂] (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) : (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeri
v μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ)
参数：hν₁ : ν₁ ≪ μ；hν₂ : ν₂ ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.withDensity_eq_iff_of_sigmaFinite`：withDensity_eq_iff_of_s
igmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf : AEMeasurable f μ) (hg : A
EMeasurable g μ) : μ.withDensity f = …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.aemeasurable_mlconvolution`：aemeasurable_mlconvolution {f 
g : G -> Real>=0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : AEMeasurabl
e (f ⋆ₘₗ[μ] g) μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.mconv_eq_withDensity_mlconvolution_rnDeriv`：mconv_eq_withD
ensity_mlconvolution_rnDeriv [SFinite μ] {ν₁ ν₂ : Measure G} [ν₁.HaveLebesgueDec
omposition μ] [ν₂.HaveLebesgueDecomposition μ]…
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.Measure.withDensity_rnDeriv_eq`：withDensity_rnDeriv_eq (μ 
ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDe
riv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.mconv_absolutelyContinuous`：mconv_absolutelyContin
uous [MeasurableMul₂ M] {μ ν ρ : Measure M} [IsMulLeftInvariant ρ] [SFinite ν] (
hν : ν ≪ ρ) : μ ∗ₘ ν ≪ ρ
-/
theorem rnDeriv_mconv' [SigmaFinite μ] {ν₁ ν₂ : Measure G} [SigmaFinite ν₁] [SigmaFinite ν₂]
    (hν₁ : ν₁ ≪ μ) (hν₂ : ν₂ ≪ μ) :
    (ν₁ ∗ₘ ν₂).rnDeriv μ =ᵐ[μ] (ν₁.rnDeriv μ) ⋆ₘₗ[μ] (ν₂.rnDeriv μ) := by
  rw [← withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop),
    ← mconv_eq_withDensity_mlconvolution_rnDeriv hν₁ hν₂,
    withDensity_rnDeriv_eq _ _ (mconv_absolutelyContinuous hν₂)]

end Conv

end MeasureTheory

