/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!

# Conditional expectation of real-valued functions

This file proves some results regarding the conditional expectation of real-valued functions.

## Main results

* `MeasureTheory.rnDeriv_ae_eq_condExp`: the conditional expectation `μ[f | m]` is equal to the
  Radon-Nikodym derivative of `fμ` restricted on `m` with respect to `μ` restricted on `m`.
* `MeasureTheory.Integrable.uniformIntegrable_condExp`: the conditional expectation of a function
  form a uniformly integrable class.

-/

public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

/-
**MeasureTheory.rnDeriv_ae_eq_condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：rnDeriv_ae_eq_condExp {hm : m <= m0} [hμm : SigmaFinite (μ.trim hm)] {f : 
α -> Real} (hf : Integrable f μ) : SignedMeasure.rnDeriv ((μ.withDensityᵥ f).tri
m hm) (μ.trim hm) =ᵐ[μ] μ[f | m]
参数：μ.trim hm；hf : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`：ae_eq_condExp_of_f
orall_setIntegral_eq (hm : m <= m₀) [SigmaFinite (μ.trim hm)] {f g : α -> E} (hf
 : Integrable f μ) (hg_int_finite : forall…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrable_of_integrable_trim`：integrable_of_integrable_tr
im (hm : m <= m0) (hf_int : Integrable f (μ'.trim hm)) : Integrable f μ'
· 使用定理 `MeasureTheory.SignedMeasure.integrable_rnDeriv`：integrable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Integrable.withDensityᵥ_trim_eq_integral`：∀ {α : Type u_1}
 {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} (hm : m ≤ m0) {f : α →
 ℝ},   MeasureTheory.Integrable f μ →     ∀ …
· 使用定理 `MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq`：withDensityᵥ_rnDeri
v_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ] (h : s ≪ᵥ μ.toENNReal
VectorMeasure) : μ.withDensityᵥ (s.rnDeri…
· 使用定理 `MeasureTheory.Integrable.withDensityᵥ_trim_absolutelyContinuous`：∀ {α : 
Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E
] {f : α → E}   {m m0 : MeasurableSpace α} {μ : Measu…
· 使用定理 `MeasureTheory.withDensityᵥ_apply`：withDensityᵥ_apply (hf : Integrable f 
μ) {s : Set α} (hs : MeasurableSet s) : μ.withDensityᵥ f s = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_trim`：setIntegral_trim {X} {m m0 : MeasurableS
pace X} {μ : Measure X} (hm : m <= m0) {f : X -> E} (hf_meas : StronglyMeasurabl
e[m] f) {s : Set X} …
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.SignedMeasure.measurable_rnDeriv`：measurable_rnDeriv (s : 
SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ)
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
-/
theorem rnDeriv_ae_eq_condExp {hm : m ≤ m0} [hμm : SigmaFinite (μ.trim hm)] {f : α → ℝ}
    (hf : Integrable f μ) :
    SignedMeasure.rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm) =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f).trim hm) (μ.trim hm)) hs,
      ← setIntegral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable

section HasSolidNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-
**MeasureTheory.condExp_le_nonneg_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：condExp_le_nonneg_const [PartialOrder E] [ClosedIciTopology E] [IsOrderedA
ddMonoid E] [IsOrderedModule Real E] {f : α -> E} {c : E} (hc : 0 <= c) (hfc : f
orallᵐ x ∂μ, f x <= c) : forallᵐ x ∂μ, μ[f | m] x <= c
参数：hc : 0 <= c；hfc : forallᵐ x ∂μ, f x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `IsCountablySpanning.null_of_forall_restrict_null`：∀ {α : Type u_2} {m0 :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {s : Set α} {C : Set (Set α)},
   IsCountablySpanning C → (∀ t ∈ C, M…
· 使用定理 `MeasureTheory.isCountablySpanning_spanningSets`：isCountablySpanning_span
ningSets (μ : Measure α) [SigmaFinite μ] : IsCountablySpanning (range (spanningS
ets μ))
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.instIsFiniteMeasureRestrictSpanningSetsTrim`：∀ {α : Type u
_1} {m m0 : MeasurableSpace α} (hm : m ≤ m0) (μ : MeasureTheory.Measure α)   [in
st : MeasureTheory.SigmaFinite (μ.trim hm)] (n …
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.condExp_const`：condExp_const (hm : m <= m₀) (c : E) [IsFin
iteMeasure μ] : μ[fun _ : α => c | m] = fun _ => c
-/
lemma condExp_le_nonneg_const [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] {f : α → E} {c : E} (hc : 0 ≤ c) (hfc : ∀ᵐ x ∂μ, f x ≤ c) :
    ∀ᵐ x ∂μ, μ[f | m] x ≤ c := by
  by_cases! hm : ¬ m ≤ m0
  · filter_upwards with a using by simpa [condExp_of_not_le hm]
  by_cases! hfint : ¬ Integrable f μ
  · filter_upwards with a using by simpa [condExp_of_not_integrable hfint]
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · filter_upwards with a using by simpa [condExp_of_not_sigmaFinite hm hsig]
  refine (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null ?_ ?_ <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  · have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hfint
    have h2 := condExp_mono (μ := μ.restrict (spanningSets (μ.trim hm) n)) (m := m)
      hfint.restrict (integrable_const c) (ae_restrict_of_ae hfc)
    filter_upwards [h1, h2] with a ha hb
    grw [← ha, hb, condExp_const hm]

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
/-
**MeasureTheory.abs_condExp_ae_le_condExp_abs** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：abs_condExp_ae_le_condExp_abs (f : α -> E) : |(μ[f | m])| <=ᵐ[μ] μ[|f| | m
]
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `MeasureTheory.condExp_mono`：condExp_mono (hf : Integrable f μ) (hg : Int
egrable g μ) (hfg : f <=ᵐ[μ] g) : μ[f | m] <=ᵐ[μ] μ[g | m]
· 使用定理 `MeasureTheory.Integrable.abs`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_8} [inst : NormedAddCommGroup β]   [ins
t_1 : Lattice β] […
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
· 使用定理 `neg_le_abs`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a
 : α), -a ≤ |a|
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_neg`：condExp_neg (f : α -> E) (m : MeasurableSpace
 α) : μ[-f | m] =ᵐ[μ] -μ[f | m]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le'`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a b 
: α}, |a| ≤ b ↔ a ≤ b ∧ -a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem abs_condExp_ae_le_condExp_abs (f : α → E) : |(μ[f | m])| ≤ᵐ[μ] μ[|f| | m] := by
  by_cases! hfint : ¬Integrable f μ
  · simp only [condExp_of_not_integrable hfint, abs_zero]
    apply condExp_nonneg
    filter_upwards with a using abs_nonneg (f a)
  have h1 := condExp_mono (m := m) hfint hfint.abs (.of_forall (fun x => le_abs_self f x))
  have h2 := condExp_mono (m := m) hfint.neg hfint.abs (.of_forall fun x => neg_le_abs (f x))
  filter_upwards [h1, h2, condExp_neg f m] with a ha hb hc
  exact abs_le'.2 ⟨ha, hc.symm.le.trans hb⟩
/-
**MeasureTheory.integral_abs_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_abs_condExp_le (f : α -> E) : ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| 
∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `MeasureTheory.Integrable.abs`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_8} [inst : NormedAddCommGroup β]   [ins
t_1 : Lattice β] […
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `MeasureTheory.abs_condExp_ae_le_condExp_abs`：abs_condExp_ae_le_condExp_a
bs (f : α -> E) : |(μ[f | m])| <=ᵐ[μ] μ[|f| | m]
· 使用定理 `MeasureTheory.integral_condExp`：integral_condExp (hm : m <= m₀) [hμm : S
igmaFinite (μ.trim hm)] : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ
-/
theorem integral_abs_condExp_le (f : α → E) : ∫ x, |μ[f | m] x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ ≤ ∫ x, μ[|f| | m] x ∂μ :=
    integral_mono_ae integrable_condExp.abs integrable_condExp (abs_condExp_ae_le_condExp_abs f)
  _ = _ := integral_condExp hm

/-- Note that this is not trivial as we don't assume that `f` is integrable. -/
/-
**MeasureTheory.integral_condExp_le_of_ae_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_condExp_le_of_ae_nonneg {f : α -> Real} (hf : 0 <=ᵐ[μ] f) : ∫ x, 
μ[f | m] x ∂μ <= ∫ x, f x ∂μ
参数：hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `MeasureTheory.condExp_nonneg`：condExp_nonneg (hf : 0 <=ᵐ[μ] f) : 0 <=ᵐ[μ
] μ[f | m]
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_abs_condExp_le`：integral_abs_condExp_le (f : α ->
 E) : ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| ∂μ

--- 原说明 ---
Note that this is not trivial as we don't assume that `f` is integrable.
-/
lemma integral_condExp_le_of_ae_nonneg {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ∫ x, μ[f | m] x ∂μ ≤ ∫ x, f x ∂μ := calc
  ∫ x, μ[f | m] x ∂μ = ∫ x, |μ[f | m] x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [condExp_nonneg hf] with ω hω using (abs_of_nonneg hω).symm
  _ ≤ ∫ x, |f x| ∂μ := integral_abs_condExp_le f
  _ = ∫ x, f x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf] with ω hω using abs_of_nonneg hω
/-
**MeasureTheory.setIntegral_abs_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α ->
 E) : ∫ x in s, |μ[f | m] x| ∂μ <= ∫ x in s, |f x| ∂μ
参数：hs : MeasurableSet[m] s；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用定理 `MeasureTheory.integral_abs_condExp_le`：integral_abs_condExp_le (f : α ->
 E) : ∫ x, |μ[f | m] x| ∂μ <= ∫ x, |f x| ∂μ
-/
theorem setIntegral_abs_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → E) :
    ∫ x in s, |μ[f | m] x| ∂μ ≤ ∫ x in s, |f x| ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => abs_nonneg f x)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using integral_nonneg (fun x => abs_nonneg f x)
  calc
  _ = ∫ x in s, |(μ.restrict s)[f | m] x| ∂μ :=
    (integral_congr_ae ((condExp_restrict_ae_eq_restrict hm hs hfint).fun_comp abs)).symm
  _  ≤ _ := integral_abs_condExp_le f

/-- Note that this is not trivial as we don't assume that `f` is integrable. -/
/-
**MeasureTheory.setIntegral_condExp_le_of_ae_restrict_nonneg** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_condExp_le_of_ae_restrict_nonneg {s : Set α} (hs : MeasurableS
et[m] s) {f : α -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) : ∫ x in s, μ[f | m] x ∂μ 
<= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet[m] s；hf : 0 <=ᵐ[μ.restrict s] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `MeasureTheory.setIntegral_nonneg_of_ae_restrict`：setIntegral_nonneg_of_a
e_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExp_restrict_ae_eq_restrict`：condExp_restrict_ae_eq_re
strict (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs_m : MeasurableSet[m] s) (hf_
int : Integrable f μ) : (μ.restrict…
· 使用引理 `MeasureTheory.integral_condExp_le_of_ae_nonneg`：integral_condExp_le_of_a
e_nonneg {f : α -> Real} (hf : 0 <=ᵐ[μ] f) : ∫ x, μ[f | m] x ∂μ <= ∫ x, f x ∂μ

--- 原说明 ---
Note that this is not trivial as we don't assume that `f` is integrable.
-/
lemma setIntegral_condExp_le_of_ae_restrict_nonneg {s : Set α} (hs : MeasurableSet[m] s) {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ.restrict s] f) :
    ∫ x in s, μ[f | m] x ∂μ ≤ ∫ x in s, f x ∂μ := by
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using setIntegral_nonneg_of_ae_restrict hf
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig] using setIntegral_nonneg_of_ae_restrict hf
  calc
  ∫ x in s, μ[f | m] x ∂μ = ∫ x in s, (μ.restrict s)[f | m] x ∂μ :=
    integral_congr_ae (condExp_restrict_ae_eq_restrict hm hs hfint).symm
  _ ≤ ∫ x in s, f x ∂μ := integral_condExp_le_of_ae_nonneg hf
/-
**MeasureTheory.setIntegral_condExp_le_of_ae_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory`。
形式化陈述：setIntegral_condExp_le_of_ae_nonneg {s : Set α} (hs : MeasurableSet[m] s) 
{f : α -> Real} (hf : 0 <=ᵐ[μ] f) : ∫ x in s, μ[f | m] x ∂μ <= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet[m] s；hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.setIntegral_condExp_le_of_ae_restrict_nonneg`：setIntegral_
condExp_le_of_ae_restrict_nonneg {s : Set α} (hs : MeasurableSet[m] s) {f : α ->
 Real} (hf : 0 <=ᵐ[μ.restrict s] f) : ∫ x in s, …
· 使用引理 `MeasureTheory.ae_restrict_le`：ae_restrict_le : ae (μ.restrict s) <= ae μ
-/
lemma setIntegral_condExp_le_of_ae_nonneg {s : Set α} (hs : MeasurableSet[m] s) {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) :
    ∫ x in s, μ[f | m] x ∂μ ≤ ∫ x in s, f x ∂μ :=
  setIntegral_condExp_le_of_ae_restrict_nonneg hs (ae_restrict_le hf)

/-- If `|f|` is bounded almost everywhere by `R`, then so is its conditional expectation. -/
/-
**MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：ae_bdd_abs_condExp_of_ae_bdd_abs {R : E} {f : α -> E} (hbdd : forallᵐ x ∂μ
, |f x| <= R) : forallᵐ x ∂μ, |μ[f | m] x| <= R
参数：hbdd : forallᵐ x ∂μ, |f x| <= R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.abs_condExp_ae_le_condExp_abs`：abs_condExp_ae_le_condExp_a
bs (f : α -> E) : |(μ[f | m])| <=ᵐ[μ] μ[|f| | m]
· 使用引理 `MeasureTheory.condExp_le_nonneg_const`：condExp_le_nonneg_const [PartialO
rder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] {f
 : α -> E} {c : E} (hc : 0 …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E

--- 原说明 ---
If `|f|` is bounded almost everywhere by `R`, then so is its conditional expecta
tion.
-/
theorem ae_bdd_abs_condExp_of_ae_bdd_abs {R : E} {f : α → E} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |μ[f | m] x| ≤ R := by
  by_cases! hn : {x | |f x| ≤ R} = ∅
  · exact measure_mono_null (by simp) <| ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  have hR : 0 ≤ R := (abs_nonneg _).trans hn.some_mem
  exact (abs_condExp_ae_le_condExp_abs f).trans (condExp_le_nonneg_const (m := m) hR hbdd)

/-- If the real-valued function `f` is bounded almost everywhere by `R`, then so is its conditional
expectation. -/
@[deprecated ae_bdd_abs_condExp_of_ae_bdd_abs (since := "2026-05-05")]
/-
**MeasureTheory.ae_bdd_condExp_of_ae_bdd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：ae_bdd_condExp_of_ae_bdd {R : Real>=0} {f : α -> Real} (hbdd : forallᵐ x ∂
μ, |f x| <= R) : forallᵐ x ∂μ, |(μ[f | m]) x| <= R
参数：hbdd : forallᵐ x ∂μ, |f x| <= R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `MeasureTheory.setIntegral_gt_gt`：setIntegral_gt_gt {R : Real} {f : X -> 
Real} (hR : 0 <= R) (hfint : IntegrableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < 
f x} != 0) : μ.real {…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.abs`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {β : Type u_8} [inst : NormedAddCommGroup β]   [ins
t_1 : Lattice β] […
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setIntegral_abs_condExp_le`：setIntegral_abs_condExp_le {s 
: Set α} (hs : MeasurableSet[m] s) (f : α -> E) : ∫ x in s, |μ[f | m] x| ∂μ <= ∫
 x in s, |f x| ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `MeasureTheory.setIntegral_mono_ae`：setIntegral_mono_ae (h : f <=ᵐ[μ] g) 
: ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If the real-valued function `f` is bounded almost everywhere by `R`, then so is 
its conditional
expectation.
-/
theorem ae_bdd_condExp_of_ae_bdd {R : ℝ≥0} {f : α → ℝ} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) :
    ∀ᵐ x ∂μ, |(μ[f | m]) x| ≤ R := by
  by_cases hnm : m ≤ m0
  swap
  · simp_rw [condExp_of_not_le hnm, Pi.zero_apply, abs_zero]
    exact Eventually.of_forall fun _ => R.coe_nonneg
  by_cases hfint : Integrable f μ
  swap
  · simp_rw [condExp_of_not_integrable hfint]
    filter_upwards [hbdd] with x hx
    rw [Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans hx
  by_contra h
  change μ _ ≠ 0 at h
  simp only [← pos_iff_ne_zero, Set.compl_def, Set.mem_ofPred_eq, not_le] at h
  suffices μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R < μ.real {x | ↑R < |(μ[f|m]) x|} * ↑R by
    exact this.ne rfl
  refine lt_of_lt_of_le (setIntegral_gt_gt R.coe_nonneg ?_ h.ne') ?_
  · exact integrable_condExp.abs.integrableOn
  refine (setIntegral_abs_condExp_le ?_ _).trans ?_
  · simp_rw [← Real.norm_eq_abs]
    exact @measurableSet_lt _ _ _ _ _ m _ _ _ _ _ measurable_const
      stronglyMeasurable_condExp.norm.measurable
  simp only [← smul_eq_mul, ← setIntegral_const]
  refine setIntegral_mono_ae hfint.abs.integrableOn ?_ hbdd
  refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_
    (integrable_condExp.integrableOn : IntegrableOn (μ[f|m]) {x | ↑R < |(μ[f|m]) x|} μ).2⟩
  refine setLIntegral_mono
    (stronglyMeasurable_condExp.mono hnm).measurable.nnnorm.coe_nnreal_ennreal fun x hx => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, Real.nnnorm_of_nonneg R.coe_nonneg]
  exact Subtype.mk_le_mk.2 (le_of_lt hx)

end HasSolidNorm

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-
**MeasureTheory.integral_norm_condExp_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_norm_condExp_rpow_le {p : Real} (hp : 1 <= p) {f : α -> E} (hf : 
Integrable (‖f ·‖ ^ p) μ) : ∫ x, ‖μ[f | m] x‖ ^ p ∂μ <= ∫ x, ‖f x‖ ^ p ∂μ
参数：hp : 1 <= p；hf : Integrable (‖f ·‖ ^ p) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
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
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Integrable.norm_condExp_rpow_le`：Integrable.norm_condExp_rpow_le {p : Re
al} (hp : 1 <= p) (hfint : Integrable (fun x => ‖f x‖ ^ p) μ) : (‖μ[f | m] ·‖ ^ 
p) <=ᵐ[μ] μ[(‖f ·‖ ^ …
· 使用引理 `MeasureTheory.integral_condExp_le_of_ae_nonneg`：integral_condExp_le_of_a
e_nonneg {f : α -> Real} (hf : 0 <=ᵐ[μ] f) : ∫ x, μ[f | m] x ∂μ <= ∫ x, f x ∂μ
-/
theorem integral_norm_condExp_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : α → E}
    (hf : Integrable (‖f ·‖ ^ p) μ) :
    ∫ x, ‖μ[f | m] x‖ ^ p ∂μ ≤ ∫ x, ‖f x‖ ^ p ∂μ := calc
  _ ≤ ∫ x, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ integrable_condExp (Integrable.norm_condExp_rpow_le hp hf)
    filter_upwards with a using by positivity
  _ ≤ _ := by
    apply integral_condExp_le_of_ae_nonneg
    filter_upwards with ω using by positivity
/-
**MeasureTheory.integral_norm_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_norm_condExp_le (f : α -> E) : ∫ x, ‖μ[f | m] x‖ ∂μ <= ∫ x, ‖f x‖
 ∂μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.integral_norm_condExp_rpow_le`：integral_norm_condExp_rpow_
le {p : Real} (hp : 1 <= p) {f : α -> E} (hf : Integrable (‖f ·‖ ^ p) μ) : ∫ x, 
‖μ[f | m] x‖ ^ p ∂μ <= ∫ x, ‖f x‖…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
-/
theorem integral_norm_condExp_le (f : α → E) : ∫ x, ‖μ[f | m] x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using integral_norm_condExp_rpow_le le_rfl (by simpa using hfint.norm)
/-
**MeasureTheory.setIntegral_norm_condExp_rpow_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：setIntegral_norm_condExp_rpow_le {p : Real} (hp : 1 <= p) {f : α -> E} {s 
: Set α} (hs : MeasurableSet[m] s) (hf : Integrable (‖f ·‖ ^ p) μ) : ∫ x in s, ‖
μ[f | m] x‖ ^ p ∂μ <= ∫ x in s, ‖f x‖ ^ p ∂μ
参数：hp : 1 <= p；hs : MeasurableSet[m] s；hf : Integrable (‖f ·‖ ^ p) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 65 条，此处仅展示前 30 条）
-/
theorem setIntegral_norm_condExp_rpow_le {p : ℝ} (hp : 1 ≤ p) {f : α → E} {s : Set α}
    (hs : MeasurableSet[m] s) (hf : Integrable (‖f ·‖ ^ p) μ) :
    ∫ x in s, ‖μ[f | m] x‖ ^ p ∂μ ≤ ∫ x in s, ‖f x‖ ^ p ∂μ := by
  have hp' : p ≠ 0 := by linarith
  by_cases! hm : ¬ m ≤ m0
  · simpa [condExp_of_not_le hm, hp'] using integral_nonneg (fun x => by positivity)
  by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
  · simpa [condExp_of_not_sigmaFinite hm hsig, hp'] using integral_nonneg (fun x => by positivity)
  calc
  _ ≤ ∫ x in s, μ[(fun x => ‖f x‖ ^ p) | m] x ∂μ := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with a using by positivity
    · exact integrable_condExp.congr (condExp_restrict_ae_eq_restrict hm hs hf)
    · exact ae_restrict_le (Integrable.norm_condExp_rpow_le hp hf)
  _ ≤ _ := by
    apply setIntegral_condExp_le_of_ae_nonneg hs
    filter_upwards with ω using by positivity
/-
**MeasureTheory.setIntegral_norm_condExp_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：setIntegral_norm_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α -
> E) : ∫ x in s, ‖(μ[f | m]) x‖ ∂μ <= ∫ x in s, ‖f x‖ ∂μ
参数：hs : MeasurableSet[m] s；f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.setIntegral_norm_condExp_rpow_le`：setIntegral_norm_condExp
_rpow_le {p : Real} (hp : 1 <= p) {f : α -> E} {s : Set α} (hs : MeasurableSet[m
] s) (hf : Integrable (‖f ·‖ ^ p) μ)…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
-/
theorem setIntegral_norm_condExp_le {s : Set α} (hs : MeasurableSet[m] s) (f : α → E) :
    ∫ x in s, ‖(μ[f | m]) x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ := by
  by_cases! hfint : ¬ Integrable f μ
  · simpa [condExp_of_not_integrable hfint] using integral_nonneg (fun x => norm_nonneg (f x))
  simpa using setIntegral_norm_condExp_rpow_le le_rfl hs (by simpa using hfint.norm)

/-- If `‖f‖` is bounded almost everywhere by `R`, then so is its conditional expectation. -/
/-
**MeasureTheory.ae_bdd_norm_condExp_of_ae_bdd_norm** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：ae_bdd_norm_condExp_of_ae_bdd_norm {R : Real} {f : α -> E} (hbdd : forallᵐ
 x ∂μ, ‖f x‖ <= R) : forallᵐ x ∂μ, ‖μ[f | m] x‖ <= R
参数：hbdd : forallᵐ x ∂μ, ‖f x‖ <= R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_eq_empty`：ae_eq_empty : s =ᵐ[μ] (∅ : Set α) ↔ μ s = 0
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
· 使用定理 `Filter.EventuallyLE.trans`：∀ {α : Type u} {β : Type v} [inst : Preorder 
β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `norm_condExp_le`：norm_condExp_le (f : α -> E) : (‖μ[f | m] ·‖) <=ᵐ[μ] μ[
(‖f ·‖) | m]
· 使用引理 `MeasureTheory.condExp_le_nonneg_const`：condExp_le_nonneg_const [PartialO
rder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] {f
 : α -> E} {c : E} (hc : 0 …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s

--- 原说明 ---
If `‖f‖` is bounded almost everywhere by `R`, then so is its conditional expecta
tion.
-/
theorem ae_bdd_norm_condExp_of_ae_bdd_norm {R : ℝ} {f : α → E} (hbdd : ∀ᵐ x ∂μ, ‖f x‖ ≤ R) :
    ∀ᵐ x ∂μ, ‖μ[f | m] x‖ ≤ R := by
  by_cases! hn : {x | ‖f x‖ ≤ R} = ∅
  · exact measure_mono_null (by simp) <| ae_eq_empty.1 (hn ▸ (ae_eq_univ.2 hbdd).symm)
  exact (norm_condExp_le f).trans (condExp_le_nonneg_const ((norm_nonneg _).trans hn.some_mem) hbdd)
/-
**MeasureTheory.MemLp.ae_norm_condExp_le_essSup** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
{E : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Compl
eteSpace E] {f : α → E},   MeasureTheory.MemLp f ⊤ μ → ∀ᵐ (x : α) ∂μ, ‖μ[f | m] 
x‖ ≤ essSup (fun x => ‖f x‖) μ
参数：x : α；fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_bdd_norm_condExp_of_ae_bdd_norm`：ae_bdd_norm_condExp_of
_ae_bdd_norm {R : Real} {f : α -> E} (hbdd : forallᵐ x ∂μ, ‖f x‖ <= R) : forallᵐ
 x ∂μ, ‖μ[f | m] x‖ <= R
· 使用定理 `ae_le_essSup`：ae_le_essSup (hf : IsBoundedUnder (· <= ·) (ae μ) f
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_le_lpNorm_exponent_top`：ae_le_lpNorm_exponent_top (hf :
 MemLp f ∞ μ) : forallᵐ x ∂μ, ‖f x‖ <= lpNorm f ∞ μ
-/
theorem MemLp.ae_norm_condExp_le_essSup {f : α → E} (hf : MemLp f ∞ μ) :
    ∀ᵐ (x : α) ∂μ, ‖μ[f | m] x‖ ≤ essSup (‖f ·‖) μ :=
  ae_bdd_norm_condExp_of_ae_bdd_norm (ae_le_essSup ⟨_, ae_le_lpNorm_exponent_top hf⟩)
/-
**MeasureTheory.MemLp.essSup_norm_condExp_le_essSup_norm** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
{E : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Compl
eteSpace E] [NeZero μ] {f : α → E},   MeasureTheory.MemLp f ⊤ μ → essSup (fun x 
=> ‖μ[f | m] x‖) μ ≤ essSup (fun x => ‖f x‖) μ
参数：fun x => ‖μ[f | m] x‖；fun x => ‖f x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `essSup_le_of_ae_le`：essSup_le_of_ae_le {f : α -> β} (c : β) (hf : f <=ᵐ[
μ] fun _ => c) (hfbdd : IsCoboundedUnder (· <= ·) (ae μ) f
· 使用定理 `MeasureTheory.MemLp.ae_norm_condExp_le_essSup`：∀ {α : Type u_1} {m m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAd
dCommGroup E]   [inst_1 : NormedSpa…
· 使用引理 `Filter.isCoboundedUnder_le_of_le`：isCoboundedUnder_le_of_le [Preorder α]
 (l : Filter ι) [NeBot l] {f : ι -> α} {x : α} (hf : forall i, x <= f i) : IsCob
oundedUnder (· <= ·) l…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem MemLp.essSup_norm_condExp_le_essSup_norm [NeZero μ] {f : α → E} (hf : MemLp f ∞ μ) :
    essSup (fun x ↦ ‖μ[f | m] x‖) μ ≤ essSup (fun x ↦ ‖f x‖) μ :=
  essSup_le_of_ae_le _ hf.ae_norm_condExp_le_essSup
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))
/-
**MeasureTheory.MemLp.lpNorm_condExp_le_lpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
{E : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Compl
eteSpace E] {f : α → E} {p : ENNReal},   1 ≤ p → MeasureTheory.MemLp f p μ → Mea
sureTheory.lpNorm μ[f | m] p μ ≤ MeasureTheory.lpNorm f p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExp_of_not_le`：condExp_of_not_le (hm_not : ¬m <= m₀) :
 μ[f | m] = 0
· 使用引理 `MeasureTheory.lpNorm_zero`：lpNorm_zero (p : Real>=0∞) (μ : Measure α) : 
lpNorm (0 : α -> E) p μ = 0
· 使用定理 `MeasureTheory.condExp_of_not_sigmaFinite`：condExp_of_not_sigmaFinite (hm
 : m <= m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) : μ[f | m] = 0
· 使用引理 `MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal`：lpNorm_eq_integral_no
rm_rpow_toReal (hp₀ : p != 0) (hp : p != ∞) (hf : AEStronglyMeasurable f μ) : lp
Norm f p μ = (∫ x, ‖f x‖ ^ p.toReal ∂μ)…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
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
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
（共 45 条，此处仅展示前 30 条）
-/
theorem MemLp.lpNorm_condExp_le_lpNorm {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    lpNorm μ[f | m] p μ ≤ lpNorm f p μ := by
  by_cases NeZero μ
  · have hp' : 0 < p := zero_lt_one.trans_le hp
    by_cases! hm : ¬ m ≤ m0
    · simp [condExp_of_not_le hm]
    by_cases! hsig : ¬ SigmaFinite (μ.trim hm)
    · simp [condExp_of_not_sigmaFinite hm hsig]
    · by_cases! hpt : p ≠ ⊤
      · rw [lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt hf.1,
          lpNorm_eq_integral_norm_rpow_toReal hp'.ne.symm hpt integrable_condExp.1]
        gcongr ?_ ^ ?_
        have : 1 ≤ p.toReal := by
          rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
        exact integral_norm_condExp_rpow_le this <|
          (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
      · by_cases! h : MemLp μ[f | m] ⊤ μ
        · simp_all only [lpNorm_exponent_top_eq_essSup]
          exact hf.essSup_norm_condExp_le_essSup_norm
        · simp_all
  · simp_all [not_neZero]
/-
**MeasureTheory.MemLp.condExp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
{E : Type u_2} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Compl
eteSpace E] {f : α → E} {p : ENNReal},   1 ≤ p → MeasureTheory.MemLp f p μ → Mea
sureTheory.MemLp μ[f | m] p μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.integrable_norm_rpow_iff`：integrable_norm_rpow_iff {f : α 
-> β} {p : Real>=0∞} (hf : AEStronglyMeasurable f μ) (p_zero : p != 0) (p_top : 
p != ∞) : Integrable (fun x …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integrable_condExp`：integrable_condExp : Integrable (μ[f |
 m]) μ
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Integrable.norm_condExp_rpow_le`：Integrable.norm_condExp_rpow_le {p : Re
al} (hp : 1 <= p) (hfint : Integrable (fun x => ‖f x‖ ^ p) μ) : (‖μ[f | m] ·‖ ^ 
p) <=ᵐ[μ] μ[(‖f ·‖ ^ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Integrable.mono_nonneg`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   [inst_1 : Lattice β] […
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Real.continuous_rpow_const`：continuous_rpow_const {q : Real} (h : 0 <= q
) : Continuous (fun x : Real => x ^ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）
-/
theorem MemLp.condExp {f : α → E} {p : ℝ≥0∞} (hp : 1 ≤ p) (hf : MemLp f p μ) :
    MemLp (μ[f | m]) p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p ≠ ⊤
  · rw [← integrable_norm_rpow_iff integrable_condExp.1 hp'.ne.symm hpt]
    have hp : 1 ≤ p.toReal := by
      rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt]
    have := Integrable.norm_condExp_rpow_le (m := m) hp <|
      (integrable_norm_rpow_iff hf.1 hp'.ne.symm hpt).2 hf
    refine Integrable.mono_nonneg integrable_condExp ?_ ?_ this
    · fun_prop (discharger := simp)
    · filter_upwards with a; positivity
  · simp_all only
    exact memLp_top_of_bound integrable_condExp.1 (essSup (‖f ·‖) μ) hf.ae_norm_condExp_le_essSup
/-
**MeasureTheory.eLpNorm_condExp_le_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：eLpNorm_condExp_le_eLpNorm (f : α -> E) {p : Real>=0∞} (hp : 1 <= p) : eLp
Norm (μ[f | m]) p μ <= eLpNorm f p μ
参数：f : α -> E；hp : 1 <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.ofReal_lpNorm`：ofReal_lpNorm (hf : MemLp f p μ) : .ofReal 
(lpNorm f p μ) = eLpNorm f p μ
· 使用定理 `MeasureTheory.MemLp.condExp`：∀ {α : Type u_1} {m m0 : MeasurableSpace α}
 {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAddCommGroup E]   [i
nst_1 : NormedSpa…
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `MeasureTheory.MemLp.lpNorm_condExp_le_lpNorm`：∀ {α : Type u_1} {m m0 : M
easurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} [inst : NormedAdd
CommGroup E]   [inst_1 : NormedSpa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.condExp_of_not_integrable`：condExp_of_not_integrable (hf :
 ¬Integrable f μ) : μ[f | m] = 0
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.eLpNorm_zero`：eLpNorm_zero : eLpNorm (0 : α -> ε) p μ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem eLpNorm_condExp_le_eLpNorm (f : α → E) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (μ[f | m]) p μ ≤ eLpNorm f p μ := by
  by_cases! hf : MemLp f p μ
  · rw [← ofReal_lpNorm hf, ← ofReal_lpNorm (hf.condExp hp)]
    exact ENNReal.ofReal_le_ofReal (hf.lpNorm_condExp_le_lpNorm hp)
  · simp only [MemLp, not_and, not_lt, top_le_iff] at hf
    by_cases! ha : AEStronglyMeasurable f μ
    · simp [hf ha]
    · simp [condExp_of_not_integrable (fun h => ha h.aestronglyMeasurable)]

@[deprecated eLpNorm_condExp_le_eLpNorm (since := "2026-07-01")]
/-
**MeasureTheory.eLpNorm_one_condExp_le_eLpNorm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：eLpNorm_one_condExp_le_eLpNorm (f : α -> E) : eLpNorm (μ[f | m]) 1 μ <= eL
pNorm f 1 μ
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.eLpNorm_condExp_le_eLpNorm`：eLpNorm_condExp_le_eLpNorm (f 
: α -> E) {p : Real>=0∞} (hp : 1 <= p) : eLpNorm (μ[f | m]) p μ <= eLpNorm f p μ
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem eLpNorm_one_condExp_le_eLpNorm (f : α → E) : eLpNorm (μ[f | m]) 1 μ ≤ eLpNorm f 1 μ :=
    eLpNorm_condExp_le_eLpNorm f (refl 1)

end NormedSpace

/-- Given an integrable function `g`, the conditional expectations of `g` with respect to
a sequence of sub-σ-algebras is uniformly integrable. -/
/-
**MeasureTheory.Integrable.uniformIntegrable_condExp** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {ι
 : Type u_2} [MeasureTheory.IsFiniteMeasure μ]   {g : α → ℝ},   MeasureTheory.In
tegrable g μ →     ∀ {ℱ : ι → MeasurableSpace α}, (∀ (i : ι), ℱ i ≤ m0) → Measur
eTheory.UniformIntegrable (fun i => μ[g | ℱ i]) 1 μ
参数：∀ (i : ι), ℱ i ≤ m0；fun i => μ[g | ℱ i]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.nnnorm`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpa
ce α] [inst_1 : NormedAddCommGroup α] [OpensMeasurableSpace α]   [inst_3 : Measu
rableSp…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.mono`：∀ {α : Type u_1} {β : Type u_2} {
f : α → β} {m m' : MeasurableSpace α} [inst : TopologicalSpace β],   MeasureTheo
ry.StronglyMeasurable f → m…
· 使用定理 `MeasureTheory.stronglyMeasurable_condExp`：stronglyMeasurable_condExp : S
tronglyMeasurable[m] (μ[f | m])
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.memLp_one_iff_integrable`：memLp_one_iff_integrable {f : α 
-> ε} : MemLp f 1 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.uniformIntegrable_of`：uniformIntegrable_of [IsFiniteMeasur
e μ] (hp : 1 <= p) (hp' : p != ∞) (hf : forall i, AEStronglyMeasurable (f i) μ) 
(h : forall ε : Real, 0 …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.eLpNorm_eq_zero_iff`：eLpNorm_eq_zero_iff {f : α -> ε} (hf 
: AEStronglyMeasurable f μ) (h0 : p != 0) : eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.AEStronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 : Z…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExp_congr_ae`：condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f |
 m] =ᵐ[μ] μ[g | m]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
Given an integrable function `g`, the conditional expectations of `g` with respe
ct to
a sequence of sub-σ-algebras is uniformly integrable.
-/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → MeasurableSpace α} (hℱ : ∀ i, ℱ i ≤ m0) :
    UniformIntegrable (fun i => μ[g | ℱ i]) 1 μ := by
  let A : MeasurableSpace α := m0
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖(μ[g|ℱ n]) x‖₊} := fun n C =>
    measurableSet_le measurable_const (stronglyMeasurable_condExp.mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun n => (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  by_cases hne : eLpNorm g 1 μ = 0
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff ((stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans zero_le⟩
    filter_upwards [condExp_congr_ae (m := ℱ n) hne] with x hx
    simp [hx]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top hε
  set C : ℝ≥0 := (.mk δ hδ.le)⁻¹ * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := mul_pos (inv_pos.2 hδ) (ENNReal.toNNReal_pos hne hg.eLpNorm_lt_top.ne)
  have : ∀ n, μ {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} ≤ ENNReal.ofReal δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖μ[g|ℱ n] x‖₊} ≤
        eLpNorm μ[g | ℱ n] 1 μ ^ ENNReal.toReal 1 := by
      rw [ENNReal.toReal_one, ENNReal.rpow_one]
      convert!
        mul_meas_ge_le_pow_eLpNorm μ one_ne_zero ENNReal.one_ne_top
          (stronglyMeasurable_condExp.mono (hℱ n)).aestronglyMeasurable C
      · rw [ENNReal.toReal_one, ENNReal.rpow_one, enorm_eq_nnnorm]
    rw [ENNReal.toReal_one, ENNReal.rpow_one, mul_comm, ←
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne)] at this
    simp_rw [ENNReal.coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inl (ENNReal.coe_ne_zero.2 hCpos.ne'))
        (Or.inl ENNReal.coe_lt_top.ne),
      hC, NNReal.inv_mk, ENNReal.coe_mul, ENNReal.coe_toNNReal hg.eLpNorm_lt_top.ne, ← mul_assoc, ←
      ENNReal.ofReal_eq_coe_nnreal, ← ENNReal.ofReal_mul hδ.le, mul_inv_cancel₀ hδ.ne',
      ENNReal.ofReal_one, one_mul, ENNReal.rpow_one]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : MeasurableSet[ℱ n] {x : α | C ≤ ‖(μ[g|ℱ n]) x‖₊} :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ stronglyMeasurable_condExp.measurable)
  rw [← eLpNorm_congr_ae (condExp_indicator hint hmeasℱ)]
  exact eLpNorm_condExp_le_eLpNorm _ le_rfl

end MeasureTheory

