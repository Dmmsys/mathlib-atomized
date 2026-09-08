/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `MeasureTheory.condExp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is an
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/

public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
/-
**MeasureTheory.condExp_indep_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExp_indep_eq (hle₁ : m₁ <= m) (hle₂ : m₂ <= m) [SigmaFinite (μ.trim hl
e₂)] (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] f
un _ => μ[f]
参数：hle₁ : m₁ <= m；hle₂ : m₂ <= m；μ.trim hle₂；hf : StronglyMeasurable[m₁] f；hindp
 : Indep m₁ m₂ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `MeasureTheory.MemLp.induction_stronglyMeasurable`：∀ {α : Type u_1} {F : 
Type u_2} {p : ENNReal} [inst : NormedAddCommGroup F] {m m0 : MeasurableSpace α}
   {μ : MeasureTheory.Measure α} [inst…
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ProbabilityTheory.Indep_iff`：Indep_iff (m₁ m₂ : MeasurableSpace Ω) {_mΩ 
: MeasurableSpace Ω} (μ : Measure Ω) : Indep m₁ m₂ μ ↔ forall t1 t2, MeasurableS
et[m₁] t1 -> Meas…
· 使用定理 `MeasureTheory.setIntegral_indicator`：setIntegral_indicator (ht : Measura
bleSet t) : ∫ x in s, t.indicator f x ∂μ = ∫ x in s inter t, f x ∂μ
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.integral_add'`：integral_add' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.continuous_integral`：continuous_integral : Continuous fun 
f : α ->₁[μ] G => ∫ a, f a ∂μ
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `MeasureTheory.continuous_setIntegral`：continuous_setIntegral [NormedSpac
e Real E] (s : Set X) : Continuous fun f : X ->₁[μ] E => ∫ x in s, f x ∂μ
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m
₂] = 𝔼[f]`
almost everywhere.
-/
theorem condExp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
    (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] fun _ => μ[f] := by
  by_cases hfint : Integrable f μ
  swap; · rw [condExp_of_not_integrable hfint, integral_undef hfint]; rfl
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle₂ hfint
    (fun s _ hs ↦ integrableOn_const hs.ne) (fun s hms hs => ?_)
      stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_const]
  rw [← memLp_one_iff_integrable] at hfint
  refine MemLp.induction_stronglyMeasurable hle₁ ENNReal.one_ne_top _ ?_ ?_ ?_ ?_ hfint ?_
  · exact ⟨f, hf, EventuallyEq.rfl⟩
  · intro c t hmt _
    rw [Indep_iff] at hindp
    rw [integral_indicator (hle₁ _ hmt), setIntegral_const, smul_smul, measureReal_def,
      measureReal_def, ← ENNReal.toReal_mul,
      mul_comm, ← hindp _ _ hmt hms, setIntegral_indicator (hle₁ _ hmt), setIntegral_const,
      Set.inter_comm, measureReal_def]
  · intro u v _ huint hvint hu hv hu_eq hv_eq
    rw [memLp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq,
      integral_add' huint.integrableOn hvint.integrableOn]
  · have h_integral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x, (f : Ω → E) x ∂μ := by
      simpa using! continuous_integral.comp (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    have h_setIntegral : Continuous fun f : lpMeas E ℝ m₁ 1 μ => ∫ x in s, (f : Ω → E) x ∂μ := by
      simpa using! (continuous_setIntegral s).comp
        (ContinuousLinearMap.continuous (Submodule.subtypeL _))
    exact isClosed_eq (Continuous.const_smul h_integral _) h_setIntegral
  · intro u v huv _ hueq
    rwa [← integral_congr_ae huv, ←
      (setIntegral_congr_ae (hle₂ _ hms) _ : ∫ x in s, u x ∂μ = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx

end MeasureTheory

