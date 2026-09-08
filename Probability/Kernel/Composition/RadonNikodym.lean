/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon-Nikodym derivative of a composition product

We compute the Radon-Nikodym derivative of a composition product `μ ⊗ₘ κ` with respect to another
composition product `ν ⊗ₘ η` in terms of the Radon-Nikodym derivatives `∂μ/∂ν` and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.

## Main statements

* `rnDeriv_compProd`: the Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` equals the product of
  `∂μ/∂ν` and `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
* `rnDeriv_measure_compProd_left`: the Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)`
  (with the same kernel) equals `∂μ/∂ν`.

## TODO

Under suitable assumptions to have Radon-Nikodym derivatives defined for kernels, we should give
equivalent statements with `∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)` replaced by `∂κ/∂η`.

-/


public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- Auxiliary lemma for `rnDeriv_measure_compProd_left`. -/
/-
**ProbabilityTheory.rnDeriv_measure_compProd_left_of_ac** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `rnDeriv_measure_compProd_left`.
-/
private lemma rnDeriv_measure_compProd_left_of_ac (hμν : μ ≪ ν) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ μ.rnDeriv ν p.1 := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) (by fun_prop) fun s hs _ ↦ ?_
  have h_key t₁ t₂ : MeasurableSet t₁ → MeasurableSet t₂ →
      ∫⁻ x in t₁ ×ˢ t₂, (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) x ∂ν ⊗ₘ κ =
        ∫⁻ x in t₁ ×ˢ t₂, μ.rnDeriv ν x.1 ∂ν ⊗ₘ κ := by
    intro ht₁ ht₂
    rw [Measure.setLIntegral_rnDeriv (hμν.compProd_left _),
      Measure.setLIntegral_compProd (by fun_prop) ht₁ ht₂]
    simp only [MeasureTheory.lintegral_const, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter]
    rw [setLIntegral_rnDeriv_mul hμν (κ.measurable_coe ht₂).aemeasurable ht₁,
      Measure.compProd_apply_prod ht₁ ht₂]
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    exact h_key t₁ t₂ ht₁ ht₂
  · intro t ht ht_eq
    rw [setLIntegral_compl ht, ht_eq, setLIntegral_compl ht]
    · congr 1
      specialize h_key .univ .univ .univ .univ
      simpa only [univ_prod_univ, Measure.restrict_univ] using h_key
    · rw [← ht_eq]
      exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
    · exact ((Measure.setLIntegral_rnDeriv_le _).trans_lt (measure_lt_top _ _)).ne
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

/-- Auxiliary lemma for `rnDeriv_measure_compProd_left`. -/
/-
**ProbabilityTheory.rnDeriv_compProd_withDensity_rnDeriv** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：rnDeriv_compProd_withDensity_rnDeriv (μ ν : Measure α) (κ η : Kernel α β) 
[IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] : 
(ν.withDensity (μ.rnDeriv ν) otimesₘ κ).rnDeriv (ν otimesₘ η) =ᵐ[ν otimesₘ η] (μ
 otimesₘ κ).rnDeriv (ν otimesₘ η)
参数：μ ν : Measure α；κ η : Kernel α β。
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
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.compProd_add_left`：compProd_add_left (μ ν : Measur
e α) [SFinite μ] [SFinite ν] (κ : Kernel α β) : (μ + ν) otimesₘ κ = μ otimesₘ κ 
+ ν otimesₘ κ
· 使用定理 `MeasureTheory.Measure.singularPart.instSigmaFinite`：∀ {α : Type u_1} {m 
: MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite 
μ],   MeasureTheory.SigmaFinite (μ.singu…
· 使用定理 `MeasureTheory.Measure.withDensity.instSFinite`：∀ {α : Type u_1} {m0 : Me
asurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {f : α 
→ ENNReal},   MeasureTheory.SFinite…
· 使用引理 `MeasureTheory.Measure.rnDeriv_add'`：rnDeriv_add' (ν₁ ν₂ μ : Measure α) [
SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] : (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.
rnDeriv μ + ν₂.rnDeriv μ
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.singularPart.instIsFiniteMeasure`：∀ {α : Type u_1}
 {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFinite
Measure μ],   MeasureTheory.IsFiniteMeasure …
· 使用定理 `MeasureTheory.Measure.withDensity.instIsFiniteMeasure`：∀ {α : Type u_1} 
{m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteM
easure μ],   MeasureTheory.IsFiniteMeasure …
· 使用引理 `MeasureTheory.Measure.rnDeriv_eq_zero_of_mutuallySingular`：rnDeriv_eq_ze
ro_of_mutuallySingular {ν' : Measure α} [HaveLebesgueDecomposition μ ν'] [SigmaF
inite ν'] (h : μ ⟂ₘ ν) (hνν' : ν ≪ ν') : μ.rnDe…
· 使用定理 `MeasureTheory.Measure.instSFiniteProdCompProd`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Meas
ure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `MeasureTheory.Measure.MutuallySingular.compProd_of_left`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measur
eTheory.Measure α},   μ.MutuallySingular ν → …
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Auxiliary lemma for `rnDeriv_measure_compProd_left`.
-/
lemma rnDeriv_compProd_withDensity_rnDeriv (μ ν : Measure α) (κ η : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := by
  conv_rhs => rw [Measure.haveLebesgueDecomposition_add μ ν]
  rw [Measure.compProd_add_left]
  have h := Measure.rnDeriv_add' (μ.singularPart ν ⊗ₘ κ) (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ)
    (ν ⊗ₘ η)
  have h2 : (μ.singularPart ν ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
    refine Measure.rnDeriv_eq_zero_of_mutuallySingular ?_ ?_
    · exact Measure.MutuallySingular.compProd_of_left (μ.mutuallySingular_singularPart _) _ _
    · exact Measure.AbsolutelyContinuous.rfl
  filter_upwards [h, h2] with x hx hx2
  simp [hx, hx2]

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)` (with the same kernel) equals `∂μ/∂ν`. -/
/-
**ProbabilityTheory.rnDeriv_measure_compProd_left** 是 Mathlib 中的一个引理，位于命名空间 `Pro
babilityTheory`。
形式化陈述：rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β) [IsFinite
Measure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] : (μ otimesₘ κ).rnDeriv (ν oti
mesₘ κ) =ᵐ[ν otimesₘ κ] fun p => (μ.rnDeriv ν) p.1
参数：μ ν : Measure α；κ : Kernel α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `ProbabilityTheory.rnDeriv_compProd_withDensity_rnDeriv`：rnDeriv_compProd
_withDensity_rnDeriv (μ ν : Measure α) (κ η : Kernel α β) [IsFiniteMeasure μ] [I
sFiniteMeasure ν] [IsFiniteKernel κ] [IsFini…
· 使用定理 `_private.Mathlib.Probability.Kernel.Composition.RadonNikodym.0.Probabili
tyTheory.rnDeriv_measure_compProd_left_of_ac`：∀ {α : Type u_1} {β : Type u_2} {m
α : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : MeasureTheory.Measure α},
   μ.AbsolutelyContinuous …
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `MeasureTheory.Measure.withDensity.instIsFiniteMeasure`：∀ {α : Type u_1} 
{m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteM
easure μ],   MeasureTheory.IsFiniteMeasure …
· 使用引理 `MeasureTheory.Measure.ae_eq_compProd_of_ae_eq_fst`：ae_eq_compProd_of_ae_
eq_fst {γ : Type*} {mγ : MeasurableSpace γ} [MeasurableEq γ] (κ : Kernel α β) {f
 g : α -> γ} (hf : Measurable f) (hg : …
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ)` (with the same kernel) equals
 `∂μ/∂ν`.
-/
lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : Kernel α β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (μ.rnDeriv ν) p.1 := by
  calc (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ)
  _ =ᵐ[ν ⊗ₘ κ] (ν.withDensity (μ.rnDeriv ν) ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) :=
    (rnDeriv_compProd_withDensity_rnDeriv μ ν κ κ).symm
  _ =ᵐ[ν ⊗ₘ κ] (fun p ↦ (ν.withDensity (μ.rnDeriv ν)).rnDeriv ν p.1) :=
    rnDeriv_measure_compProd_left_of_ac
      (MeasureTheory.withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) κ
  _ =ᵐ[ν ⊗ₘ κ] fun p ↦ μ.rnDeriv ν p.1 :=
    Measure.ae_eq_compProd_of_ae_eq_fst _ (by fun_prop) (by fun_prop)
      (Measure.rnDeriv_withDensity ν (by fun_prop))

/-- The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` equals the product of `∂μ/∂ν` and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`. -/
/-
**ProbabilityTheory.rnDeriv_compProd** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
 (h_ac : μ otimesₘ κ ≪ μ otimesₘ η) (ν : Measure α) [IsFiniteMeasure ν] : (μ oti
mesₘ κ).rnDeriv (ν otimesₘ η) =ᵐ[ν otimesₘ η] (fun p => μ.rnDeriv ν p.1 * (μ oti
mesₘ κ).rnDeriv (μ otimesₘ η) p)
参数：h_ac : μ otimesₘ κ ≪ μ otimesₘ η；ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `MeasureTheory.Measure.rnDeriv_mul_rnDeriv`：rnDeriv_mul_rnDeriv {κ : Meas
ure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ] (hμν : μ ≪ ν) : μ.rnDeriv
 ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeri…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureProdCompProdOfIsFiniteKernel`：∀
 {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
 {μ : MeasureTheory.Measure α}   {κ : ProbabilityTheory.Ker…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `ProbabilityTheory.rnDeriv_measure_compProd_left`：rnDeriv_measure_compPro
d_left (μ ν : Measure α) (κ : Kernel α β) [IsFiniteMeasure μ] [IsFiniteMeasure ν
] [IsFiniteKernel κ] : (μ otimesₘ κ).…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
The Radon-Nikodym derivative `∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)` equals the product of `∂μ/∂ν`
 and
`∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
-/
lemma rnDeriv_compProd [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) (ν : Measure α) [IsFiniteMeasure ν] :
    (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η]
      (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p) := by
  refine Filter.EventuallyEq.trans (Measure.rnDeriv_mul_rnDeriv h_ac).symm ?_
  filter_upwards [rnDeriv_measure_compProd_left μ ν η] with p hp
  rw [Pi.mul_apply, hp, mul_comm]

end ProbabilityTheory

