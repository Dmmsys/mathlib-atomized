/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# Uniqueness of the conditional expectation

Two Lp functions `f, g` which are almost everywhere strongly measurable with respect to a σ-algebra
`m` and verify `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ` for all `m`-measurable sets `s` are equal
almost everywhere. This proves the uniqueness of the conditional expectation, which is not yet
defined in this file but is introduced in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`.

## Main statements

* `Lp.ae_eq_of_forall_setIntegral_eq'`: two `Lp` functions verifying the equality of integrals
  defining the conditional expectation are equal.
* `ae_eq_of_forall_setIntegral_eq_of_sigma_finite'`: two functions verifying the equality of
  integrals defining the conditional expectation are equal almost everywhere.
  Requires `[SigmaFinite (μ.trim hm)]`.

-/

public section


open scoped ENNReal MeasureTheory

namespace MeasureTheory

variable {α E' F' 𝕜 : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [CompleteSpace F']

section UniquenessOfConditionalExpectation

/-! ## Uniqueness of the conditional expectation -/

/-
**MeasureTheory.lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.lpMeas`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_2} {𝕜 : Type u_4} {p : ENNReal} {m m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α}   [inst : RCLike 𝕜] [inst_1 : Norme
dAddCommGroup E'] [inst_2 : InnerProductSpace 𝕜 E'] [CompleteSpace E']   [inst_4
 : NormedSpace ℝ E'],   m ≤ m0 →     ∀ (f : ↥(MeasureTheory.lpMeas E' 𝕜 m p μ)),
       p ≠ 0 →         p ≠ ⊤ →           (∀ (s : Set α), MeasurableSet s → μ s <
 ⊤ → MeasureTheory.IntegrableOn (↑↑↑f) s μ) →             (∀ (s : Set α), Measur
ableSet s → μ s < ⊤ → ∫ (x : α) in s, ↑↑↑f x ∂μ = 0) → ↑↑↑f =ᵐ[μ] 0
参数：f : ↥(MeasureTheory.lpMeas E' 𝕜 m p μ)；∀ (s : Set α), MeasurableSet s → μ s <
 ⊤ → MeasureTheory.IntegrableOn (↑↑↑f) s μ；∀ (s : Set α), MeasurableSet s → μ s 
< ⊤ → ∫ (x : α) in s, ↑↑↑f x ∂μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lpMeas.ae_fin_strongly_measurable'`：∀ {α : Type u_1} {F : 
Type u_2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddComm
Group F]   [inst_2 : NormedSpace 𝕜 F] …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurab
le_trim`：ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm :
 m <= m0) {f : α -> E} (hf_int_finite : forall s, MeasurableSet[m] s …
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ

--- 原说明 ---
## Uniqueness of the conditional expectation
-/
theorem lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn (f : Lp E' p μ) s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, (f : Lp E' p μ) x ∂μ = 0) :
    f =ᵐ[μ] (0 : α → E') := by
  obtain ⟨g, hg_sm, hfg⟩ := lpMeas.ae_fin_strongly_measurable' hm f hp_ne_zero hp_ne_top
  refine hfg.trans ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim hm ?_ ?_ hg_sm
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [IntegrableOn, integrable_congr hfg_restrict.symm]
    exact hf_int_finite s hs hμs
  · intro s hs hμs
    have hfg_restrict : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae hfg
    rw [integral_congr_ae hfg_restrict.symm]
    exact hf_zero s hs hμs

variable (𝕜)

include 𝕜 in
/-
**MeasureTheory.Lp.ae_eq_zero_of_forall_setIntegral_eq_zero'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_2} (𝕜 : Type u_4) {p : ENNReal} {m m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α}   [inst : RCLike 𝕜] [inst_1 : Norme
dAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']   [inst : NormedSp
ace ℝ E'],   m ≤ m0 →     ∀ (f : ↥(MeasureTheory.Lp E' p μ)),       p ≠ 0 →     
    p ≠ ⊤ →           (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.
IntegrableOn (↑↑f) s μ) →             (∀ (s : Set α), MeasurableSet s → μ s < ⊤ 
→ ∫ (x : α) in s, ↑↑f x ∂μ = 0) →               MeasureTheory.AEStronglyMeasurab
le (↑↑f) μ → ↑↑f =ᵐ[μ] 0
参数：𝕜 : Type u_4；f : ↥(MeasureTheory.Lp E' p μ)；∀ (s : Set α), MeasurableSet s → 
μ s < ⊤ → MeasureTheory.IntegrableOn (↑↑f) s μ；∀ (s : Set α), MeasurableSet s → 
μ s < ⊤ → ∫ (x : α) in s, ↑↑f x ∂μ = 0；↑↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero`：∀ {α : Ty
pe u_1} {E' : Type u_2} {𝕜 : Type u_4} {p : ENNReal} {m m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α}   [inst : RCLike 𝕜] […
-/
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' (hm : m ≤ m0) (f : Lp E' p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf_meas : AEStronglyMeasurable[m] f μ) : f =ᵐ[μ] 0 := by
  let f_meas : lpMeas E' 𝕜 m p μ := ⟨f, hf_meas⟩
  have hf_f_meas : f =ᵐ[μ] f_meas := by simp [f_meas]
  refine hf_f_meas.trans ?_
  exact lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    hm f_meas hp_ne_zero hp_ne_top hf_int_finite hf_zero

include 𝕜 in
/-- **Uniqueness of the conditional expectation** -/
/-
**MeasureTheory.Lp.ae_eq_of_forall_setIntegral_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_2} (𝕜 : Type u_4) {p : ENNReal} {m m0 : Meas
urableSpace α} {μ : MeasureTheory.Measure α}   [inst : RCLike 𝕜] [inst_1 : Norme
dAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']   [inst : NormedSp
ace ℝ E'],   m ≤ m0 →     ∀ (f g : ↥(MeasureTheory.Lp E' p μ)),       p ≠ 0 →   
      p ≠ ⊤ →           (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheor
y.IntegrableOn (↑↑f) s μ) →             (∀ (s : Set α), MeasurableSet s → μ s < 
⊤ → MeasureTheory.IntegrableOn (↑↑g) s μ) →               (∀ (s : Set α), Measur
ableSet s → μ s < ⊤ → ∫ (x : α) in s, ↑↑f x ∂μ = ∫ (x : α) in s, ↑↑g x ∂μ) →    
             MeasureTheory.AEStronglyMeasurable (↑↑f) μ → MeasureTheory.AEStrong
lyMeasurable (↑↑g) μ → ↑↑f =ᵐ[μ] ↑↑g
参数：𝕜 : Type u_4；f g : ↥(MeasureTheory.Lp E' p μ)；∀ (s : Set α), MeasurableSet s 
→ μ s < ⊤ → MeasureTheory.IntegrableOn (↑↑f) s μ；∀ (s : Set α), MeasurableSet s 
→ μ s < ⊤ → MeasureTheory.IntegrableOn (↑↑g) s μ；∀ (s : Set α), MeasurableSet s 
→ μ s < ⊤ → ∫ (x : α) in s, ↑↑f x ∂μ = ∫ (x : α) in s, ↑↑g x ∂μ；↑↑f；↑↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.Lp.ae_eq_zero_of_forall_setIntegral_eq_zero'`：∀ {α : Type 
u_1} {E' : Type u_2} (𝕜 : Type u_4) {p : ENNReal} {m m0 : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   [inst : RCLike 𝕜] […
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h

--- 原说明 ---
**Uniqueness of the conditional expectation**
-/
theorem Lp.ae_eq_of_forall_setIntegral_eq' (hm : m ≤ m0) (f g : Lp E' p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf_meas : AEStronglyMeasurable[m] f μ) (hg_meas : AEStronglyMeasurable[m] g μ) :
    f =ᵐ[μ] g := by
  suffices h_sub : ⇑(f - g) =ᵐ[μ] 0 by
    rw [← sub_ae_eq_zero]; exact (Lp.coeFn_sub f g).symm.trans h_sub
  have hfg' : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg s hs hμs)
  have hfg_int : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn (⇑(f - g)) s μ := by
    intro s hs hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub f g))]
    exact (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' 𝕜 hm (f - g) hp_ne_zero hp_ne_top hfg_int hfg'
    <| (hf_meas.sub hg_meas).congr (Lp.coeFn_sub f g).symm

variable {𝕜}
/-
**MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite'** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm : m <= m0) [SigmaFinite
 (μ.trim hm)] {f g : α -> F'} (hf_int_finite : forall s, MeasurableSet[m] s -> μ
 s < ∞ -> IntegrableOn f s μ) (hg_int_finite : forall s, MeasurableSet[m] s -> μ
 s < ∞ -> IntegrableOn g s μ) (hfg_eq : forall s : Set α, MeasurableSet[m] s -> 
μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) (hfm : AEStronglyMeasurable[m] f
 μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g
参数：hm : m <= m0；μ.trim hm；hf_int_finite : forall s, MeasurableSet[m] s -> μ s < 
∞ -> IntegrableOn f s μ；hg_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ 
-> IntegrableOn g s μ；hfg_eq : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -
> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ；hfm : AEStronglyMeasurable[m] f μ；hgm : AE
StronglyMeasurable[m] g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_eq_trim_iff_of_aestronglyMeasurable`：ae_eq_trim_iff_of_
aestronglyMeasurable {α β} [TopologicalSpace β] [MetrizableSpace β] {m m0 : Meas
urableSpace α} {μ : Measure α} {f g : α ->…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.integral_trim`：integral_trim (hm : m <= m0) {f : β -> G} (
hf : StronglyMeasurable[m] f) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`：ae_eq_of_fo
rall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> E} (hf_int_finite
 : forall s, MeasurableSet s -> μ s < ∞ -> Integr…
-/
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  rw [← ae_eq_trim_iff_of_aestronglyMeasurable hm hfm hgm]
  have hf_mk_int_finite (s) :
      MeasurableSet[m] s → μ.trim hm s < ∞ → @IntegrableOn _ _ m _ _ (hfm.mk f) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn, restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hfm.stronglyMeasurable_mk
    exact Integrable.congr (hf_int_finite s hs hμs) (ae_restrict_of_ae hfm.ae_eq_mk)
  have hg_mk_int_finite (s) :
      MeasurableSet[m] s → μ.trim hm s < ∞ → @IntegrableOn _ _ m _ _ (hgm.mk g) s (μ.trim hm) := by
    intro hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [IntegrableOn, restrict_trim hm _ hs]
    refine Integrable.trim hm ?_ hgm.stronglyMeasurable_mk
    exact Integrable.congr (hg_int_finite s hs hμs) (ae_restrict_of_ae hgm.ae_eq_mk)
  have hfg_mk_eq :
    ∀ s : Set α,
      MeasurableSet[m] s →
        μ.trim hm s < ∞ → ∫ x in s, hfm.mk f x ∂μ.trim hm = ∫ x in s, hgm.mk g x ∂μ.trim hm := by
    intro s hs hμs
    rw [trim_measurableSet_eq hm hs] at hμs
    rw [restrict_trim hm _ hs, ← integral_trim hm hfm.stronglyMeasurable_mk, ←
      integral_trim hm hgm.stronglyMeasurable_mk,
      integral_congr_ae (ae_restrict_of_ae hfm.ae_eq_mk.symm),
      integral_congr_ae (ae_restrict_of_ae hgm.ae_eq_mk.symm)]
    exact hfg_eq s hs hμs
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hf_mk_int_finite hg_mk_int_finite hfg_mk_eq

end UniquenessOfConditionalExpectation

section IntegralNormLE

variable {s : Set α}

/-- Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with finite measure. -/
/-
**MeasureTheory.integral_norm_le_of_forall_fin_meas_integral_eq** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_norm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α ->
 Real} (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeas
urable[m] g) (hgi : IntegrableOn g s μ) (hgf : forall t, MeasurableSet[m] t -> μ
 t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ) (hs : MeasurableSet[m] s) (hμs : 
μ s != ∞) : (∫ x in s, ‖g x‖ ∂μ) <= ∫ x in s, ‖f x‖ ∂μ
参数：hm : m <= m0；hf : StronglyMeasurable f；hfi : IntegrableOn f s μ；hg : Strongly
Measurable[m] g；hgi : IntegrableOn g s μ；hgf : forall t, MeasurableSet[m] t -> μ
 t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ；hs : MeasurableSet[m] s；hμs : μ s 
!= ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_norm_eq_pos_sub_neg`：integral_norm_eq_pos_sub_neg
 {f : X -> Real} (hfi : Integrable f μ) : ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x},
 f x ∂μ - ∫ x in {x | f x <= 0},…
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_le_nonneg`：setIntegral_le_nonneg {s : Set X} (
hs : MeasurableSet s) (hf : StronglyMeasurable f) (hfi : Integrable f μ) : ∫ x i
n s, f x ∂μ <= ∫ x in {y …
· 使用定理 `MeasureTheory.setIntegral_nonpos_le`：setIntegral_nonpos_le {s : Set X} (
hs : MeasurableSet s) (hf : StronglyMeasurable f) (hfi : Integrable f μ) : ∫ x i
n {y | f y <= 0}, f x ∂μ …

--- 原说明 ---
Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `
m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite 
measure.
Then `∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ` on all `m`-measurable sets with f
inite measure.
-/
theorem integral_norm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) : (∫ x in s, ‖g x‖ ∂μ) ≤ ∫ x in s, ‖f x‖ ∂μ := by
  rw [integral_norm_eq_pos_sub_neg hgi, integral_norm_eq_pos_sub_neg hfi]
  have h_meas_nonneg_g : MeasurableSet[m] {x | 0 ≤ g x} :=
    (@stronglyMeasurable_const _ _ m _ _).measurableSet_le hg
  have h_meas_nonneg_f : MeasurableSet {x | 0 ≤ f x} :=
    stronglyMeasurable_const.measurableSet_le hf
  have h_meas_nonpos_g : MeasurableSet[m] {x | g x ≤ 0} :=
    hg.measurableSet_le (@stronglyMeasurable_const _ _ m _ _)
  have h_meas_nonpos_f : MeasurableSet {x | f x ≤ 0} :=
    hf.measurableSet_le stronglyMeasurable_const
  refine sub_le_sub ?_ ?_
  · rw [Measure.restrict_restrict (hm _ h_meas_nonneg_g), Measure.restrict_restrict h_meas_nonneg_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonneg_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonneg_g), ←
      Measure.restrict_restrict h_meas_nonneg_f]
    exact setIntegral_le_nonneg (hm _ h_meas_nonneg_g) hf hfi
  · rw [Measure.restrict_restrict (hm _ h_meas_nonpos_g), Measure.restrict_restrict h_meas_nonpos_f,
      hgf _ (@MeasurableSet.inter α m _ _ h_meas_nonpos_g hs)
        ((measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμs)),
      ← Measure.restrict_restrict (hm _ h_meas_nonpos_g), ←
      Measure.restrict_restrict h_meas_nonpos_f]
    exact setIntegral_nonpos_le (hm _ h_meas_nonpos_g) hf hfi

/-- Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite measure.
Then `∫⁻ x in s, ‖g x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ` on all `m`-measurable sets with finite
measure. -/
/-
**MeasureTheory.lintegral_enorm_le_of_forall_fin_meas_integral_eq** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_enorm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α 
-> Real} (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMe
asurable[m] g) (hgi : IntegrableOn g s μ) (hgf : forall t, MeasurableSet[m] t ->
 μ t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ) (hs : MeasurableSet[m] s) (hμs 
: μ s != ∞) : (∫⁻ x in s, ‖g x‖ₑ ∂μ) <= ∫⁻ x in s, ‖f x‖ₑ ∂μ
参数：hm : m <= m0；hf : StronglyMeasurable f；hfi : IntegrableOn f s μ；hg : Strongly
Measurable[m] g；hgi : IntegrableOn g s μ；hgf : forall t, MeasurableSet[m] t -> μ
 t < ∞ -> ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ；hs : MeasurableSet[m] s；hμs : μ s 
!= ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm`：ofReal_integral_n
orm_eq_lintegral_enorm {P : Type*} [NormedAddCommGroup P] {f : α -> P} (hf : Int
egrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂…
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
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
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.integral_norm_le_of_forall_fin_meas_integral_eq`：integral_
norm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α -> Real} (hf : St
ronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg …

--- 原说明 ---
Let `m` be a sub-σ-algebra of `m0`, `f` an `m0`-measurable function and `g` an `
m`-measurable
function, such that their integrals coincide on `m`-measurable sets with finite 
measure.
Then `∫⁻ x in s, ‖g x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ` on all `m`-measurable sets wi
th finite
measure.
-/
theorem lintegral_enorm_le_of_forall_fin_meas_integral_eq (hm : m ≤ m0) {f g : α → ℝ}
    (hf : StronglyMeasurable f) (hfi : IntegrableOn f s μ) (hg : StronglyMeasurable[m] g)
    (hgi : IntegrableOn g s μ)
    (hgf : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫ x in t, g x ∂μ = ∫ x in t, f x ∂μ)
    (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) : (∫⁻ x in s, ‖g x‖ₑ ∂μ) ≤ ∫⁻ x in s, ‖f x‖ₑ ∂μ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm hfi, ←
    ofReal_integral_norm_eq_lintegral_enorm hgi, ENNReal.ofReal_le_ofReal_iff]
  · exact integral_norm_le_of_forall_fin_meas_integral_eq hm hf hfi hg hgi hgf hs hμs
  · positivity

end IntegralNormLE

end MeasureTheory

