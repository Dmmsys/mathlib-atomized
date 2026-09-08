/-
Copyright (c) 2025 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# First mean value theorem for set integrals

We prove versions of the first mean value theorem for set integrals.

## Main results

* `exists_eq_const_mul_setIntegral_of_ae_nonneg` (a.e. nonnegativity of `g` on `s`):
    `∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`.
* `exists_eq_const_mul_setIntegral_of_nonneg` (pointwise nonnegativity of `g` on `s`):
    `∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`.

## Tags

first mean value theorem, set integral
-/

public section

open MeasureTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  {s : Set α} {f g : α → ℝ} {μ : Measure α}

/-- **First mean value theorem for set integrals (a.e. nonnegativity).**
Let `s` be a connected measurable set. If `f` is continuous on `s`, `g` is integrable on `s`,
`f * g` is integrable on `s`, and `g` is nonnegative a.e. on `s` w.r.t. `μ.restrict s`, then
`∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`. -/
/-
**exists_eq_const_mul_setIntegral_of_ae_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_const_mul_setIntegral_of_ae_nonneg (hs_conn : IsConnected s) (hs
_meas : MeasurableSet s) (hf : ContinuousOn f s) (hg : IntegrableOn g s μ) (hfg 
: IntegrableOn (fun x => f x * g x) s μ) (hg0 : forallᵐ x ∂(μ.restrict s), 0 <= 
g x) : exists c in s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)
参数：hs_conn : IsConnected s；hs_meas : MeasurableSet s；hf : ContinuousOn f s；hg : 
IntegrableOn g s μ；hfg : IntegrableOn (fun x => f x * g x) s μ；hg0 : forallᵐ x ∂
(μ.restrict s), 0 <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `AEMeasurable.ennreal_ofReal`：AEMeasurable.ennreal_ofReal {f : α -> Real}
 {μ : Measure α} (hf : AEMeasurable f μ) : AEMeasurable (fun x => ENNReal.ofReal
 (f x)) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `setIntegral_withDensity_eq_setIntegral_toReal_smul₀`：setIntegral_withDen
sity_eq_setIntegral_toReal_smul₀ {f : X -> Real>=0∞} {s : Set X} (hf : AEMeasura
ble f (μ.restrict s)) (hf_top : forallᵐ x…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsConnected.nonempty`：IsConnected.nonempty {s : Set α} (h : IsConnected 
s) : s.Nonempty
· 使用定理 `MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae`：setIntegral_eq_zero_
iff_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : IntegrableO
n f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.integrableOn_congr_fun_ae`：integrableOn_congr_fun_ae (hst 
: f =ᵐ[μ.restrict s] g) : IntegrableOn f s μ ↔ IntegrableOn g s μ
· 使用定理 `MeasureTheory.integrable_withDensity_iff_integrable_smul₀'`：integrable_w
ithDensity_iff_integrable_smul₀' {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf
lt : forallᵐ x ∂μ, f x < ∞) {g : α -> E} : Integ…
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
**First mean value theorem for set integrals (a.e. nonnegativity).**
Let `s` be a connected measurable set. If `f` is continuous on `s`, `g` is integ
rable on `s`,
`f * g` is integrable on `s`, and `g` is nonnegative a.e. on `s` w.r.t. `μ.restr
ict s`, then
`∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`.
-/
theorem exists_eq_const_mul_setIntegral_of_ae_nonneg
    (hs_conn : IsConnected s) (hs_meas : MeasurableSet s) (hf : ContinuousOn f s)
    (hg : IntegrableOn g s μ) (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (hg0 : ∀ᵐ x ∂(μ.restrict s), 0 ≤ g x) :
    ∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ) := by
  let ρ := fun x ↦ ENNReal.ofReal (g x)
  let ν := μ.withDensity ρ
  have hρ_ae : AEMeasurable ρ (μ.restrict s) := by
    apply AEMeasurable.ennreal_ofReal
    exact hg.aestronglyMeasurable.aemeasurable
  have hρ_top : ∀ᵐ x ∂μ.restrict s, ρ x < ⊤ := by simp [ρ]
  have h_toReal_ae : (fun x ↦ (ρ x).toReal) =ᵐ[μ.restrict s] g := by
    apply hg0.mono
    intro x hx
    simpa [ρ]
  have heq : ∫ x in s, f x * g x ∂μ = ∫ x in s, f x ∂ν := by
    calc
      _ = ∫ x in s, (ρ x).toReal * f x ∂μ := by
        apply MeasureTheory.integral_congr_ae
        apply h_toReal_ae.mono
        intro x hx
        simp [hx, mul_comm]
      _ = _ := by
        have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hρ_ae hρ_top f hs_meas
        simp [ν, h]
  have hg1 : ∫ x in s, g x ∂μ = ∫ x in s, (1 : ℝ) ∂ν := by
    have h := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      hρ_ae hρ_top (fun _ ↦ (1 : ℝ)) hs_meas
    calc
      _ = ∫ x in s, (ρ x).toReal ∂μ := by rw [integral_congr_ae h_toReal_ae]
      _ = _ := by simp [ν, h]
  by_cases hν0 : ∫ x in s, (1 : ℝ) ∂ν = 0
  · rcases hs_conn.nonempty with ⟨c, hc⟩
    refine ⟨c, hc, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := heq
      _ = 0 := by
        rw [hν0, setIntegral_eq_zero_iff_of_nonneg_ae hg0 hg] at hg1
        have heq_zero : ∫ x in s, f x * g x ∂μ = 0 := by
          have heq_ae : (fun x ↦ f x * g x) =ᵐ[μ.restrict s] 0 := by
            apply hg1.mono
            intro x hx
            simp [hx]
          simpa using! integral_congr_ae heq_ae
        rw [← heq, heq_zero]
      _ = _ := by simp [hν0, hg1]
  · have hν0' : (ν s).toReal ≠ 0 := by simpa using! hν0
    have hνfin : ν s ≠ ⊤ := by intro this; apply hν0'; simp [this]
    have hν0'' : ν s ≠ 0 := by intro this; apply hν0'; simp [this]
    have hint : IntegrableOn f s ν := by
      have hmul_ae : (fun x ↦ (ρ x).toReal * f x) =ᵐ[μ.restrict s] (fun x ↦ f x * g x) := by
        apply h_toReal_ae.mono
        intro x hx
        simp [hx, mul_comm]
      have h_IntOn : IntegrableOn (fun x ↦ (ρ x).toReal * f x) s μ := by
        rwa [integrableOn_congr_fun_ae hmul_ae]
      have h_Int : Integrable f ((μ.restrict s).withDensity ρ) := by
        rwa [integrable_withDensity_iff_integrable_smul₀' hρ_ae hρ_top, ← IntegrableOn]
      have hνrs : ν.restrict s = (μ.restrict s).withDensity ρ := by
        ext t ht
        simp [ht, ν, hs_meas]
      simpa [IntegrableOn, hνrs] using! h_Int
    obtain ⟨c, hc, h_ave⟩ := exists_eq_setAverage hs_conn hf hint hνfin hν0''
    refine ⟨c, hc, ?_⟩
    calc
      _ = ∫ x in s, f x ∂ν := heq
      _ = f c * ∫ x in s, (1 : ℝ) ∂ν := by
        rw [h_ave]
        simp only [setAverage_eq, smul_eq_mul, integral_const, MeasurableSet.univ,
          measureReal_restrict_apply, Set.univ_inter, mul_one]
        rw [measureReal_def]
        field_simp
      _ = _ := by simp [hg1]

/-- **First mean value theorem for set integrals (pointwise nonnegativity).**
Let `s` be a connected measurable set. If `f` is continuous on `s`, `g` is integrable on `s`,
`f * g` is integrable on `s`, and `g` is nonnegative on `s`, then
`∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)` -/
/-
**exists_eq_const_mul_setIntegral_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_const_mul_setIntegral_of_nonneg (hs_conn : IsConnected s) (hs_me
as : MeasurableSet s) (hf : ContinuousOn f s) (hg : IntegrableOn g s μ) (hfg : I
ntegrableOn (fun x => f x * g x) s μ) (hg0 : forall x in s, 0 <= g x) : exists c
 in s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)
参数：hs_conn : IsConnected s；hs_meas : MeasurableSet s；hf : ContinuousOn f s；hg : 
IntegrableOn g s μ；hfg : IntegrableOn (fun x => f x * g x) s μ；hg0 : forall x in
 s, 0 <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `exists_eq_const_mul_setIntegral_of_ae_nonneg`：exists_eq_const_mul_setInt
egral_of_ae_nonneg (hs_conn : IsConnected s) (hs_meas : MeasurableSet s) (hf : C
ontinuousOn f s) (hg : IntegrableO…

--- 原说明 ---
**First mean value theorem for set integrals (pointwise nonnegativity).**
Let `s` be a connected measurable set. If `f` is continuous on `s`, `g` is integ
rable on `s`,
`f * g` is integrable on `s`, and `g` is nonnegative on `s`, then
`∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ)`
-/
theorem exists_eq_const_mul_setIntegral_of_nonneg
    (hs_conn : IsConnected s) (hs_meas : MeasurableSet s) (hf : ContinuousOn f s)
    (hg : IntegrableOn g s μ) (hfg : IntegrableOn (fun x ↦ f x * g x) s μ)
    (hg0 : ∀ x ∈ s, 0 ≤ g x) :
    ∃ c ∈ s, (∫ x in s, f x * g x ∂μ) = f c * (∫ x in s, g x ∂μ) := by
  have hg0_ae : ∀ᵐ x ∂(μ.restrict s), 0 ≤ g x := by
    rw [ae_restrict_iff' hs_meas]
    exact ae_of_all μ hg0
  exact exists_eq_const_mul_setIntegral_of_ae_nonneg hs_conn hs_meas hf hg hfg hg0_ae
