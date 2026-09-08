/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Measurability of the integral against a kernel

The Bochner integral of a strongly measurable function against a kernel is strongly measurable.

## Main statements

* `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right`: the function
  `a ↦ ∫ b, f a b ∂(κ a)` is measurable, for an s-finite kernel `κ : Kernel α β` and a function
  `f : α → β → E` such that `uncurry f` is measurable.

-/

public section


open MeasureTheory ProbabilityTheory Function Set Filter

open scoped MeasureTheory ENNReal Topology

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : Kernel α β} {η : Kernel β γ} {a : α} {E : Type*} [NormedAddCommGroup E]

/-
**ProbabilityTheory.measurableSet_integrable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ProbabilityTheory.measurableSet_integrable ⦃f : β -> E⦄ (hf : StronglyMeas
urable f) : MeasurableSet {a | Integrable f (κ a)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Measurable.lintegral_kernel`：∀ {α : Type u_1} {β : Type u_2} {mα : Measu
rableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel α β}   {f :
 β → ENNReal}, Me…
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem ProbabilityTheory.measurableSet_integrable ⦃f : β → E⦄ (hf : StronglyMeasurable f) :
    MeasurableSet {a | Integrable f (κ a)} := by
  simp_rw [Integrable, hf.aestronglyMeasurable, true_and]
  exact measurableSet_lt hf.enorm.lintegral_kernel measurable_const

variable [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]
/-
**ProbabilityTheory.measurableSet_kernel_integrable** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ProbabilityTheory.measurableSet_kernel_integrable ⦃f : α -> β -> E⦄ (hf : 
StronglyMeasurable (uncurry f)) : MeasurableSet {x | Integrable (f x) (κ x)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.StronglyMeasurable.of_uncurry_left`：of_uncurry_left [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> γ -> β}
 (hf : StronglyMeasurable (uncurry f))…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Measurable.lintegral_kernel_prod_right`：∀ {α : Type u_1} {β : Type u_2} 
{mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : ProbabilityTheory.Kernel 
α β}   [ProbabilityTheory.Is…
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
theorem ProbabilityTheory.measurableSet_kernel_integrable ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) :
    MeasurableSet {x | Integrable (f x) (κ x)} := by
  simp_rw [Integrable, hf.of_uncurry_left.aestronglyMeasurable, true_and]
  exact measurableSet_lt (Measurable.lintegral_kernel_prod_right hf.enorm) measurable_const

open ProbabilityTheory.Kernel

namespace MeasureTheory

variable [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency.types false in
omit [IsSFiniteKernel κ] in
@[fun_prop]
/-
**MeasureTheory.StronglyMeasurable.integral_kernel** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   {E : Type u_4} [inst : NormedAddCom
mGroup E] [inst_1 : NormedSpace ℝ E] ⦃f : β → E⦄,   MeasureTheory.StronglyMeasur
able f → MeasureTheory.StronglyMeasurable fun x => ∫ (y : β), f y ∂κ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
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
· 使用定理 `stronglyMeasurable_of_tendsto`：∀ {α : Type u_1} {β : Type u_2} {ι : Type
 u_5} {m : MeasurableSpace α} [inst : TopologicalSpace β]   [TopologicalSpace.Ps
eudoMetrizableSpace…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq`：integral_eq {m : MeasurableSpace α
} (μ : Measure α) (f : α ->ₛ F) : f.integral μ = ∑ x in f.range, μ.real (f ⁻¹' {
x}) • x
· 使用定理 `Finset.stronglyMeasurable_fun_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measu
rableSpace α} {ι : Type…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.smul_const`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type u_5}   [inst
_1 : TopologicalSpace 𝕜] [inst_2 …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
（共 50 条，此处仅展示前 30 条）
-/
theorem StronglyMeasurable.integral_kernel ⦃f : β → E⦄
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x ↦ ∫ y, f y ∂κ x := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range f ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc β E := SimpleFunc.approxOn _ hf.measurable (range f ∪ {0}) 0 (by simp)
  let f' n : α → E := {x | Integrable f (κ x)}.indicator fun x ↦ (s n).integral (κ x)
  refine stronglyMeasurable_of_tendsto (f := f') atTop (fun n ↦ ?_) ?_
  · refine StronglyMeasurable.indicator ?_ (measurableSet_integrable hf)
    simp_rw [SimpleFunc.integral_eq]
    refine Finset.stronglyMeasurable_fun_sum _ fun _ _ ↦ ?_
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    exact κ.measurable_coe ((s n).measurableSet_fiber _)
  · rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable f (κ x)
    · simp only [mem_ofPred_eq, hfx, indicator_of_mem, f']
      apply tendsto_integral_approxOn_of_measurable_of_range_subset _ hfx
      exact subset_rfl
    · simp [f', hfx, integral_undef]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_right** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   {E : Type u_4} [inst : NormedAddCom
mGroup E] [ProbabilityTheory.IsSFiniteKernel κ] [inst_2 : NormedSpace ℝ E]   ⦃f 
: α → β → E⦄,   MeasureTheory.StronglyMeasurable (Function.uncurry f) →     Meas
ureTheory.StronglyMeasurable fun x => ∫ (y : β), f x y ∂κ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
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
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `MeasureTheory.SimpleFunc.range_comp_subset_range`：range_comp_subset_rang
e [MeasurableSpace β] (f : β ->ₛ γ) {g : α -> β} (hgm : Measurable g) : (f.comp 
g hgm).range subseteq f.range
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.SimpleFunc.integral_eq_sum_of_subset`：integral_eq_sum_of_s
ubset [DecidablePred fun x : F => x != 0] {f : α ->ₛ F} {s : Finset F} (hs : {x 
in f.range | x != 0} subseteq s) : f.int…
· 使用定理 `Finset.stronglyMeasurable_fun_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measu
rableSpace α} {ι : Type…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.smul_const`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} [inst : TopologicalSpace β] {𝕜 : Type u_5}   [inst
_1 : TopologicalSpace 𝕜] [inst_2 …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`：measurable_kerne
l_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)} (ht : MeasurableSet t) : Mea
surable fun a => κ a (Prod.mk a ⁻¹' t)
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_fiber`：measurableSet_fiber (f : α
 ->ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x})
· 使用定理 `ProbabilityTheory.measurableSet_kernel_integrable`：ProbabilityTheory.mea
surableSet_kernel_integrable ⦃f : α -> β -> E⦄ (hf : StronglyMeasurable (uncurry
 f)) : MeasurableSet {x | Integrable (f…
（共 69 条，此处仅展示前 30 条）
-/
theorem StronglyMeasurable.integral_kernel_prod_right ⦃f : α → β → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun x => ∫ y, f x y ∂κ x := by
  classical
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE, stronglyMeasurable_const]
  borelize E
  have : TopologicalSpace.SeparableSpace (range (uncurry f) ∪ {0} : Set E) :=
    hf.separableSpace_range_union_singleton
  let s : ℕ → SimpleFunc (α × β) E :=
    SimpleFunc.approxOn _ hf.measurable (range (uncurry f) ∪ {0}) 0 (by simp)
  let s' : ℕ → α → SimpleFunc β E := fun n x => (s n).comp (Prod.mk x) measurable_prodMk_left
  let f' : ℕ → α → E := fun n =>
    {x | Integrable (f x) (κ x)}.indicator fun x => (s' n x).integral (κ x)
  have hf' : ∀ n, StronglyMeasurable (f' n) := by
    intro n; refine StronglyMeasurable.indicator ?_ (measurableSet_kernel_integrable hf)
    have : ∀ x, ((s' n x).range.filter fun x => x ≠ 0) ⊆ (s n).range := by
      intro
      exact Finset.Subset.trans (Finset.filter_subset _ _) (SimpleFunc.range_comp_subset_range _ _)
    simp only [SimpleFunc.integral_eq_sum_of_subset (this _)]
    refine Finset.stronglyMeasurable_fun_sum _ fun x _ => ?_
    refine (Measurable.ennreal_toReal ?_).stronglyMeasurable.smul_const _
    simp only [s', SimpleFunc.coe_comp, preimage_comp]
    apply Kernel.measurable_kernel_prodMk_left
    exact (s n).measurableSet_fiber x
  have h2f' : Tendsto f' atTop (𝓝 fun x : α => ∫ y : β, f x y ∂κ x) := by
    rw [tendsto_pi_nhds]; intro x
    by_cases hfx : Integrable (f x) (κ x)
    · have (n : _) : Integrable (s' n x) (κ x) := by
        apply (hfx.norm.add hfx.norm).mono' (s' n x).aestronglyMeasurable
        filter_upwards with y
        simp_rw [s', SimpleFunc.coe_comp]; exact SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
      simp only [f', hfx, SimpleFunc.integral_eq_integral _ (this _), indicator_of_mem,
        mem_ofPred_eq]
      refine
        tendsto_integral_of_dominated_convergence (fun y => ‖f x y‖ + ‖f x y‖)
          (fun n => (s' n x).aestronglyMeasurable) (hfx.norm.add hfx.norm) ?_ ?_
      · -- Porting note: was
        -- exact fun n => Eventually.of_forall fun y =>
        --   SimpleFunc.norm_approxOn_zero_le _ _ (x, y) n
        exact fun n => Eventually.of_forall fun y =>
          SimpleFunc.norm_approxOn_zero_le hf.measurable (by simp) (x, y) n
      · refine Eventually.of_forall fun y => SimpleFunc.tendsto_approxOn hf.measurable (by simp) ?_
        apply subset_closure
        simp [-uncurry_apply_pair]
    · simp [f', hfx, integral_undef]
  exact stronglyMeasurable_of_tendsto _ hf' h2f'
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   {E : Type u_4} [inst : NormedAddCom
mGroup E] [ProbabilityTheory.IsSFiniteKernel κ] [inst_2 : NormedSpace ℝ E]   ⦃f 
: α × β → E⦄,   MeasureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasu
rable fun x => ∫ (y : β), f (x, y) ∂κ x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Prob
abilityTheory.Kernel α β}   {E : Type u_4} [inst …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
-/
theorem StronglyMeasurable.integral_kernel_prod_right' ⦃f : α × β → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => ∫ y, f (x, y) ∂κ x := by
  rw [← uncurry_curry f] at hf
  exact hf.integral_kernel_prod_right
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_right''** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} {a : α} {E : Type u_4} [inst :
 NormedAddCommGroup E] {η : ProbabilityTheory.Kernel (α × β) γ}   [ProbabilityTh
eory.IsSFiniteKernel η] [inst_2 : NormedSpace ℝ E] {f : β × γ → E},   MeasureThe
ory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun x => ∫ (y : γ), 
f (x, y) ∂η (a, x)
参数：α × β；y : γ；x, y；a, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'`：∀ {α : Typ
e u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Pro
babilityTheory.Kernel α β}   {E : Type u_4} [inst …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem StronglyMeasurable.integral_kernel_prod_right'' {f : β × γ → E}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ∫ y, f (x, y) ∂η (a, x) := by
  change
    StronglyMeasurable
      ((fun x => ∫ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := η)
      (hf.comp_measurable (measurable_fst.snd.prodMk measurable_snd))
    simpa using this
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_left** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   {E : Type u_4} [inst : NormedAddCom
mGroup E] [ProbabilityTheory.IsSFiniteKernel κ] [inst_2 : NormedSpace ℝ E]   ⦃f 
: β → α → E⦄,   MeasureTheory.StronglyMeasurable (Function.uncurry f) →     Meas
ureTheory.StronglyMeasurable fun y => ∫ (x : β), f x y ∂κ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'`：∀ {α : Typ
e u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Pro
babilityTheory.Kernel α β}   {E : Type u_4} [inst …
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem StronglyMeasurable.integral_kernel_prod_left ⦃f : β → α → E⦄
    (hf : StronglyMeasurable (uncurry f)) : StronglyMeasurable fun y => ∫ x, f x y ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_left'** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} {κ : ProbabilityTheory.Kernel α β}   {E : Type u_4} [inst : NormedAddCom
mGroup E] [ProbabilityTheory.IsSFiniteKernel κ] [inst_2 : NormedSpace ℝ E]   ⦃f 
: β × α → E⦄,   MeasureTheory.StronglyMeasurable f → MeasureTheory.StronglyMeasu
rable fun y => ∫ (x : β), f (x, y) ∂κ y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'`：∀ {α : Typ
e u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Pro
babilityTheory.Kernel α β}   {E : Type u_4} [inst …
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem StronglyMeasurable.integral_kernel_prod_left' ⦃f : β × α → E⦄ (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂κ y :=
  (hf.comp_measurable measurable_swap).integral_kernel_prod_right'
/-
**MeasureTheory.StronglyMeasurable.integral_kernel_prod_left''** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {m
β : MeasurableSpace β}   {mγ : MeasurableSpace γ} {a : α} {E : Type u_4} [inst :
 NormedAddCommGroup E] {η : ProbabilityTheory.Kernel (α × β) γ}   [ProbabilityTh
eory.IsSFiniteKernel η] [inst_2 : NormedSpace ℝ E] {f : γ × β → E},   MeasureThe
ory.StronglyMeasurable f → MeasureTheory.StronglyMeasurable fun y => ∫ (x : γ), 
f (x, y) ∂η (a, y)
参数：α × β；x : γ；x, y；a, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.comp_measurable`：comp_measurable [Topol
ogicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ} {f : α -> β} {g :
 γ -> α} (hf : StronglyMeasurable f) (…
· 使用定理 `MeasureTheory.StronglyMeasurable.integral_kernel_prod_left'`：∀ {α : Type
 u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Prob
abilityTheory.Kernel α β}   {E : Type u_4} [inst …
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
-/
theorem StronglyMeasurable.integral_kernel_prod_left'' {f : γ × β → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun y => ∫ x, f (x, y) ∂η (a, y) := by
  change
    StronglyMeasurable
      ((fun y => ∫ x, (fun u : γ × α × β => f (u.1, u.2.2)) (x, y) ∂η y) ∘ fun x => (a, x))
  apply StronglyMeasurable.comp_measurable _ (measurable_prodMk_left (m := mα))
  · have := MeasureTheory.StronglyMeasurable.integral_kernel_prod_left' (κ := η)
      (hf.comp_measurable (measurable_fst.prodMk measurable_snd.snd))
    simpa using this

end MeasureTheory

