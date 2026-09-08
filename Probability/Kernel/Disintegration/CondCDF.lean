/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

`condCDF` is build from the more general tools about kernel CDFs developed in the file
`Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean`. In that file, we build a function
`α × β → StieltjesFunction ℝ` (which is `α × β → ℝ → ℝ` with additional properties) from a function
`α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some properties like measurability more
easily. Here we apply that construction to the case `β = Unit` and then drop `β` to build
`condCDF : α → StieltjesFunction ℝ`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction ℝ`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction ℝ` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.setLIntegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.IicSnd r s = ρ (s ×ˢ Iic r)`. -/
/-
**MeasureTheory.Measure.IicSnd** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：IicSnd (r : Real) : Measure α
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measure on `α` such that for a measurable set `s`, `ρ.IicSnd r s = ρ (s ×ˢ Iic r
)`.
-/
noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst
/-
**MeasureTheory.Measure.IicSnd_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：IicSnd_apply (r : Real) {s : Set α} (hs : MeasurableSet s) : ρ.IicSnd r s 
= ρ (s ×ˢ Iic r)
参数：r : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.IicSnd.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpac
e α} (ρ : MeasureTheory.Measure (α × ℝ)) (r : ℝ),   ρ.IicSnd r = (ρ.restrict (Se
t.univ ×ˢ Set.Iic r)).f…
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `Set.prod_eq`：prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s i
nter Prod.snd ⁻¹' t
-/
theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs, restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic),
    univ_prod, Set.prod_eq]
/-
**MeasureTheory.Measure.IicSnd_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：IicSnd_univ (r : Real) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IicSnd_apply`：IicSnd_apply (r : Real) {s : Set α} 
(hs : MeasurableSet s) : ρ.IicSnd r s = ρ (s ×ˢ Iic r)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]
/-
**MeasureTheory.Measure.IicSnd_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：IicSnd_mono {r r' : Real} (h_le : r <= r') : ρ.IicSnd r <= ρ.IicSnd r'
参数：h_le : r <= r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.fst_mono`：fst_mono {μ : Measure (α × β)} (h : ρ <=
 μ) : ρ.fst <= μ.fst
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.Iic_subset_Iic._gcongr_3`：∀ {α : Type u_1} [inst : Preorder α] {a b 
: α}, a ≤ b → Set.Iic a ⊆ Set.Iic b
-/
theorem IicSnd_mono {r r' : ℝ} (h_le : r ≤ r') : ρ.IicSnd r ≤ ρ.IicSnd r' := by
  unfold IicSnd; gcongr
/-
**MeasureTheory.Measure.IicSnd_le_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：IicSnd_le_fst (r : Real) : ρ.IicSnd r <= ρ.fst
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.fst_mono`：fst_mono {μ : Measure (α × β)} (h : ρ <=
 μ) : ρ.fst <= μ.fst
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst :=
  fst_mono restrict_le_self
/-
**MeasureTheory.Measure.IicSnd_ac_fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：IicSnd_ac_fst (r : Real) : ρ.IicSnd r ≪ ρ.fst
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le`：absolutelyContinuous_o
f_le (h : μ <= ν) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.IicSnd_le_fst`：IicSnd_le_fst (r : Real) : ρ.IicSnd
 r <= ρ.fst
-/
theorem IicSnd_ac_fst (r : ℝ) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)
/-
**MeasureTheory.Measure.IsFiniteMeasure.IicSnd** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.IsFiniteMeasure`。
形式化陈述：∀ {α : Type u_1} {mα : MeasurableSpace α} {ρ : MeasureTheory.Measure (α × 
ℝ)} [MeasureTheory.IsFiniteMeasure ρ] (r : ℝ),   MeasureTheory.IsFiniteMeasure (
ρ.IicSnd r)
参数：α × ℝ；r : ℝ；ρ.IicSnd r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_of_le`：isFiniteMeasure_of_le (μ : Measure 
α) [IsFiniteMeasure μ] (h : ν <= μ) : IsFiniteMeasure ν
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.Measure.IicSnd_le_fst`：IicSnd_le_fst (r : Real) : ρ.IicSnd
 r <= ρ.fst
-/
theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ] (r : ℝ) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)
/-
**MeasureTheory.Measure.iInf_IicSnd_gt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：iInf_IicSnd_gt (t : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasu
re ρ] : ⨅ r : { r' : Rat // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s
参数：t : Rat；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.IicSnd_apply`：IicSnd_apply (r : Real) {s : Set α} 
(hs : MeasurableSet s) : ρ.IicSnd r s = ρ (s ×ˢ Iic r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.iInf_rat_gt_prod_Iic`：∀ {α : Type u_1} {mα : Measu
rableSpace α} {ρ : MeasureTheory.Measure (α × ℝ)} [MeasureTheory.IsFiniteMeasure
 ρ]   {s : Set α}, MeasurableSet…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_IicSnd_gt (t : ℚ) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : ℚ // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]
/-
**MeasureTheory.Measure.tendsto_IicSnd_atTop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) : Tendsto (fun r :
 Rat => ρ.IicSnd r s) atTop (𝓝 (ρ.fst s))
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.IicSnd_apply`：IicSnd_apply (r : Real) {s : Set α} 
(hs : MeasurableSet s) : ρ.IicSnd r s = ρ (s ×ˢ Iic r)
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.iUnion_Iic_rat`：iUnion_Iic_rat : ⋃ r : Rat, Iic (r : Real) = univ
· 使用定理 `Set.prod_iUnion`：prod_iUnion {s : Set α} {t : ι -> Set β} : (s ×ˢ ⋃ i, t
 i) = ⋃ i, s ×ˢ t i
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `Rat.instOrderTopology`：OrderTopology ℚ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Monotone.set_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: Preorder α] {f : α → Set β} {g : α → Set γ},   Monotone f → Monotone g → Monot
one fun…
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `Monotone.Iic`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f : α → β},   Monotone f → Monotone fun x => Set.Iic (f x)
· 使用定理 `Rat.cast_mono`：cast_mono : Monotone ((↑) : Rat -> K)
-/
theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic
/-
**MeasureTheory.Measure.tendsto_IicSnd_atBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s
) : Tendsto (fun r : Rat => ρ.IicSnd r s) atBot (𝓝 0)
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.IicSnd_apply`：IicSnd_apply (r : Real) {s : Set α} 
(hs : MeasurableSet s) : ρ.IicSnd r s = ρ (s ×ˢ Iic r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.prod_empty`：prod_empty : s ×ˢ (∅ : Set β) = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.iInter_Iic_rat`：iInter_Iic_rat : ⋂ r : Rat, Iic (r : Real) = ∅
· 使用定理 `Set.prod_iInter`：prod_iInter {s : Set α} {t : ι -> Set β} [hι : Nonempty
 ι] : (s ×ˢ ⋂ i, t i) = ⋂ i, s ×ˢ t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `Rat.instOrderTopology`：OrderTopology ℚ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
（共 42 条，此处仅展示前 30 条）
-/
theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  suffices h_neg :
      Tendsto (fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r)))) by
    have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      push _ ∈ _
      refine ⟨fun h i ↦ ⟨(h i).1, ?_⟩, fun h i ↦ ⟨(h i).1, ?_⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    exact tendsto_comp_neg_atTop_iff.mp h_neg
  refine tendsto_measure_iInter_atTop (fun q ↦ (hs.prod measurableSet_Iic).nullMeasurableSet)
    ?_ ⟨0, measure_ne_top ρ _⟩
  refine fun q r hqr ↦ Set.prod_mono subset_rfl fun x hx ↦ ?_
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine hx.trans (neg_le_neg ?_)
  exact mod_cast hqr

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd

/-! ### Auxiliary definitions

We build towards the definition of `ProbabilityTheory.condCDF`. We first define
`ProbabilityTheory.preCDF`, a function defined on `α × ℚ` with the properties of a cdf almost
everywhere. -/

/-- `preCDF` is the Radon-Nikodym derivative of `ρ.IicSnd` with respect to `ρ.fst` at each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the function `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, right-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allows us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (preCDF q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (preCDF q a)`. -/
/-
**ProbabilityTheory.preCDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：preCDF (ρ : Measure (α × Real)) (r : Rat) : α -> Real>=0∞
参数：ρ : Measure (α × Real)；r : Rat。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`preCDF` is the Radon-Nikodym derivative of `ρ.IicSnd` with respect to `ρ.fst` a
t each
`r : ℚ`. This function `ℚ → α → ℝ≥0∞` is such that for almost all `a : α`, the f
unction `ℚ → ℝ≥0∞`
satisfies the properties of a cdf (monotone with limit 0 at -∞ and 1 at +∞, righ
t-continuous).

We define this function on `ℚ` and not `ℝ` because `ℚ` is countable, which allow
s us to prove
properties of the form `∀ᵐ a ∂ρ.fst, ∀ q, P (preCDF q a)`, instead of the weaker
`∀ q, ∀ᵐ a ∂ρ.fst, P (preCDF q a)`.
-/
noncomputable def preCDF (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst
/-
**ProbabilityTheory.measurable_preCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：measurable_preCDF {ρ : Measure (α × Real)} {r : Rat} : Measurable (preCDF 
ρ r)
参数：α × Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
-/
theorem measurable_preCDF {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _
/-
**ProbabilityTheory.measurable_preCDF'** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：measurable_preCDF' {ρ : Measure (α × Real)} : Measurable fun a r => (preCD
F ρ r a).toReal
参数：α × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.ennreal_toReal`：Measurable.ennreal_toReal {f : α -> Real>=0∞}
 (hf : Measurable f) : Measurable fun x => ENNReal.toReal (f x)
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
-/
lemma measurable_preCDF' {ρ : Measure (α × ℝ)} :
    Measurable fun a r ↦ (preCDF ρ r a).toReal := by
  rw [measurable_pi_iff]
  exact fun _ ↦ measurable_preCDF.ennreal_toReal
/-
**ProbabilityTheory.withDensity_preCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：withDensity_preCDF (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ] 
: ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r
参数：ρ : Measure (α × Real)；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`：a
bsolutelyContinuous_iff_withDensity_rnDeriv_eq [HaveLebesgueDecomposition μ ν] :
 μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.IsFiniteMeasure.IicSnd`：∀ {α : Type u_1} {mα : Mea
surableSpace α} {ρ : MeasureTheory.Measure (α × ℝ)} [MeasureTheory.IsFiniteMeasu
re ρ] (r : ℝ),   MeasureTheory.IsF…
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.Measure.IicSnd_ac_fst`：IicSnd_ac_fst (r : Real) : ρ.IicSnd
 r ≪ ρ.fst
-/
theorem withDensity_preCDF (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)
/-
**ProbabilityTheory.setLIntegral_preCDF_fst** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：setLIntegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs
 : MeasurableSet s) [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.Iic
Snd r s
参数：ρ : Measure (α × Real)；r : Rat；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul`：setLIntegral
_withDensity_eq_setLIntegral_mul (μ : Measure α) {f g : α -> Real>=0∞} (hf : Mea
surable f) (hg : Measurable g) {s : Set α} (hs :…
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
· 使用引理 `Pi.one_def`：one_def : (1 : forall i, M i) = fun _ => 1
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.withDensity_preCDF`：withDensity_preCDF (ρ : Measure (α
 × Real)) (r : Rat) [IsFiniteMeasure ρ] : ρ.fst.withDensity (preCDF ρ r) = ρ.Iic
Snd r
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem setLIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] : ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  have : ∀ r, ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ∫⁻ x in s, (preCDF ρ r * 1) x ∂ρ.fst := by
    simp only [mul_one, forall_const]
  rw [this, ← setLIntegral_withDensity_eq_setLIntegral_mul _ measurable_preCDF _ hs]
  · simp only [withDensity_preCDF ρ r, Pi.one_apply, lintegral_one, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter]
  · rw [Pi.one_def]
    exact measurable_const
/-
**ProbabilityTheory.lintegral_preCDF_fst** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：lintegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ
] : ∫⁻ x, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r univ
参数：ρ : Measure (α × Real)；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `ProbabilityTheory.setLIntegral_preCDF_fst`：setLIntegral_preCDF_fst (ρ : 
Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasur
e ρ] : ∫⁻ x in s, preCDF ρ r x …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma lintegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫⁻ x, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r univ := by
  rw [← setLIntegral_univ, setLIntegral_preCDF_fst ρ r MeasurableSet.univ]
/-
**ProbabilityTheory.monotone_preCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory
`。
形式化陈述：monotone_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : forallᵐ a ∂
ρ.fst, Monotone fun r => preCDF ρ r a
参数：ρ : Measure (α × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.setLIntegral_preCDF_fst`：setLIntegral_preCDF_fst (ρ : 
Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasur
e ρ] : ∫⁻ x in s, preCDF ρ r x …
· 使用定理 `MeasureTheory.Measure.IicSnd_mono`：IicSnd_mono {r r' : Real} (h_le : r <
= r') : ρ.IicSnd r <= ρ.IicSnd r'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem monotone_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r ↦ preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs, setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s
/-
**ProbabilityTheory.preCDF_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：preCDF_le_one (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : forallᵐ a ∂ρ.
fst, forall r, preCDF ρ r a <= 1
参数：ρ : Measure (α × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `MeasureTheory.ae_le_of_forall_setLIntegral_le_of_sigmaFinite`：ae_le_of_f
orall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α -> Real>=0∞} (hf :
 Measurable f) (h : forall s, MeasurableSet s -> μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
· 使用定理 `ProbabilityTheory.setLIntegral_preCDF_fst`：setLIntegral_preCDF_fst (ρ : 
Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasur
e ρ] : ∫⁻ x in s, preCDF ρ r x …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.Measure.IicSnd_le_fst`：IicSnd_le_fst (r : Real) : ρ.IicSnd
 r <= ρ.fst
-/
theorem preCDF_le_one (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine fun r ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s
/-
**ProbabilityTheory.setIntegral_preCDF_fst** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：setIntegral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) {s : Set α} (hs 
: MeasurableSet s) [IsFiniteMeasure ρ] : ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst 
= (ρ.IicSnd r).real s
参数：ρ : Measure (α × Real)；r : Rat；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_toReal`：integral_toReal {f : α -> Real>=0∞} (hfm 
: AEMeasurable f μ) (hf : forallᵐ x ∂μ, f x < ∞) : ∫ a, (f a).toReal ∂μ = (∫⁻ a,
 f a ∂μ).toReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.preCDF_le_one`：preCDF_le_one (ρ : Measure (α × Real)) 
[IsFiniteMeasure ρ] : forallᵐ a ∂ρ.fst, forall r, preCDF ρ r a <= 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `ProbabilityTheory.setLIntegral_preCDF_fst`：setLIntegral_preCDF_fst (ρ : 
Measure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasur
e ρ] : ∫⁻ x in s, preCDF ρ r x …
· 使用定理 `MeasureTheory.measureReal_def`：measureReal_def {α : Type*} {m : Measurab
leSpace α} (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal
-/
lemma setIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α} (hs : MeasurableSet s)
    [IsFiniteMeasure ρ] :
    ∫ x in s, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real s := by
  rw [integral_toReal]
  · rw [setLIntegral_preCDF_fst _ _ hs, measureReal_def]
  · exact measurable_preCDF.aemeasurable
  · refine ae_restrict_of_ae ?_
    filter_upwards [preCDF_le_one ρ] with a ha
    exact (ha r).trans_lt ENNReal.one_lt_top
/-
**ProbabilityTheory.integral_preCDF_fst** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：integral_preCDF_fst (ρ : Measure (α × Real)) (r : Rat) [IsFiniteMeasure ρ]
 : ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real univ
参数：ρ : Measure (α × Real)；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用引理 `ProbabilityTheory.setIntegral_preCDF_fst`：setIntegral_preCDF_fst (ρ : Me
asure (α × Real)) (r : Rat) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure 
ρ] : ∫ x in s, (preCDF ρ r x).…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
-/
lemma integral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) [IsFiniteMeasure ρ] :
    ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = (ρ.IicSnd r).real univ := by
  rw [← setIntegral_univ, setIntegral_preCDF_fst ρ _ MeasurableSet.univ]
/-
**ProbabilityTheory.integrable_preCDF** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：integrable_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Rat) :
 Integrable (fun a => (preCDF ρ x a).toReal) ρ.fst
参数：ρ : Measure (α × Real)；x : Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_of_forall_fin_meas_le`：integrable_of_forall_fin
_meas_le [SigmaFinite μ] (C : Real>=0∞) (hC : C < ∞) {f : α -> ε} (hf_meas : AES
tronglyMeasurable[m] f μ) (hf : fora…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
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
· 使用定理 `ProbabilityTheory.measurable_preCDF`：measurable_preCDF {ρ : Measure (α ×
 Real)} {r : Rat} : Measurable (preCDF ρ r)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_le_lintegral`：setLIntegral_le_lintegral (s : 
Set α) (f : α -> Real>=0∞) : ∫⁻ x in s, f x ∂μ <= ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.preCDF_le_one`：preCDF_le_one (ρ : Measure (α × Real)) 
[IsFiniteMeasure ρ] : forallᵐ a ∂ρ.fst, forall r, preCDF ρ r a <= 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.ofReal_toReal_le`：ofReal_toReal_le {a : Real>=0∞} : ENNReal.ofRe
al a.toReal <= a
-/
lemma integrable_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℚ) :
    Integrable (fun a ↦ (preCDF ρ x a).toReal) ρ.fst := by
  refine integrable_of_forall_fin_meas_le _ (measure_lt_top ρ.fst univ) ?_ fun t _ _ ↦ ?_
  · exact measurable_preCDF.ennreal_toReal.aestronglyMeasurable
  · simp_rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    rw [← lintegral_one]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae ?_)
    filter_upwards [preCDF_le_one ρ] with a ha using ENNReal.ofReal_toReal_le.trans (ha _)
/-
**ProbabilityTheory.isRatCondKernelCDFAux_preCDF** 是 Mathlib 中的一个引理，位于命名空间 `Prob
abilityTheory`。
形式化陈述：isRatCondKernelCDFAux_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] 
: IsRatCondKernelCDFAux (fun p r => (preCDF ρ r p.2).toReal) (Kernel.const Unit 
ρ) (Kernel.const Unit ρ.fst) where measurable
参数：ρ : Measure (α × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.preCDF_le_one`：preCDF_le_one (ρ : Measure (α × Real)) 
[IsFiniteMeasure ρ] : forallᵐ a ∂ρ.fst, forall r, preCDF ρ r a <= 1
· 使用定理 `ProbabilityTheory.monotone_preCDF`：monotone_preCDF (ρ : Measure (α × Rea
l)) [IsFiniteMeasure ρ] : forallᵐ a ∂ρ.fst, Monotone fun r => preCDF ρ r a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ProbabilityTheory.integral_preCDF_fst`：integral_preCDF_fst (ρ : Measure 
(α × Real)) (r : Rat) [IsFiniteMeasure ρ] : ∫ x, (preCDF ρ r x).toReal ∂ρ.fst = 
(ρ.IicSnd r).real univ
· 使用定理 `MeasureTheory.Measure.tendsto_IicSnd_atBot`：tendsto_IicSnd_atBot [IsFini
teMeasure ρ] {s : Set α} (hs : MeasurableSet s) : Tendsto (fun r : Rat => ρ.IicS
nd r s) atBot (𝓝 0)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_zero`：ENNReal.toReal 0 = 0
· 使用引理 `ENNReal.continuousAt_toReal`：continuousAt_toReal (hx : x != ∞) : Continu
ousAt ENNReal.toReal x
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `MeasureTheory.Measure.tendsto_IicSnd_atTop`：tendsto_IicSnd_atTop {s : Se
t α} (hs : MeasurableSet s) : Tendsto (fun r : Rat => ρ.IicSnd r s) atTop (𝓝 (ρ.
fst s))
（共 37 条，此处仅展示前 30 条）
-/
lemma isRatCondKernelCDFAux_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDFAux (fun p r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) where
  measurable := measurable_preCDF'.comp measurable_snd
  mono' a r r' hrr' := by
    filter_upwards [monotone_preCDF ρ, preCDF_le_one ρ] with a h₁ h₂
    exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hrr')
  nonneg' _ q := by simp
  le_one' a q := by
    simp only [Kernel.const_apply]
    filter_upwards [preCDF_le_one ρ] with a ha
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp [ha]
  tendsto_integral_of_antitone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atBot MeasurableSet.univ
    rw [← ENNReal.toReal_zero]
    have h0 : Tendsto ENNReal.toReal (𝓝 0) (𝓝 0) :=
      ENNReal.continuousAt_toReal ENNReal.zero_ne_top
    exact h0.comp (h.comp hs_tendsto)
  tendsto_integral_of_monotone a s _ hs_tendsto := by
    simp_rw [Kernel.const_apply, integral_preCDF_fst ρ]
    have h := ρ.tendsto_IicSnd_atTop MeasurableSet.univ
    have h0 : Tendsto ENNReal.toReal (𝓝 (ρ.fst univ)) (𝓝 (ρ.fst.real univ)) :=
      ENNReal.continuousAt_toReal (measure_ne_top _ _)
    exact h0.comp (h.comp hs_tendsto)
  integrable _ q := integrable_preCDF ρ q
  setIntegral a s hs q := by rw [Kernel.const_apply, Kernel.const_apply,
    setIntegral_preCDF_fst _ _ hs, measureReal_def, measureReal_def, Measure.IicSnd_apply _ _ hs]
/-
**ProbabilityTheory.isRatCondKernelCDF_preCDF** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：isRatCondKernelCDF_preCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : I
sRatCondKernelCDF (fun p r => (preCDF ρ r p.2).toReal) (Kernel.const Unit ρ) (Ke
rnel.const Unit ρ.fst)
参数：ρ : Measure (α × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatCondKernelCDFAux.isRatCondKernelCDF`：∀ {α : Type 
u_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : Pro
babilityTheory.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用引理 `ProbabilityTheory.isRatCondKernelCDFAux_preCDF`：isRatCondKernelCDFAux_pr
eCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : IsRatCondKernelCDFAux (fun p
 r => (preCDF ρ r p.2).toReal) (Kern…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用定理 `MeasureTheory.Measure.fst.instIsFiniteMeasure`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : MeasureThe
ory.Measure (α × β)} [MeasureTheory…
-/
lemma isRatCondKernelCDF_preCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsRatCondKernelCDF (fun p r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) :=
  (isRatCondKernelCDFAux_preCDF ρ).isRatCondKernelCDF

/-! ### Conditional cdf -/

/-- Conditional cdf of the measure given the value on `α`, as a Stieltjes function. -/
/-
**ProbabilityTheory.condCDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：condCDF (ρ : Measure (α × Real)) (a : α) : StieltjesFunction Real
参数：ρ : Measure (α × Real)；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
Conditional cdf of the measure given the value on `α`, as a Stieltjes function.
-/
noncomputable def condCDF (ρ : Measure (α × ℝ)) (a : α) : StieltjesFunction ℝ :=
  stieltjesOfMeasurableRat (fun a r ↦ (preCDF ρ r a).toReal) measurable_preCDF' a
/-
**ProbabilityTheory.condCDF_eq_stieltjesOfMeasurableRat_unit_prod** 是 Mathlib 中的
一个引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × Real)) (a 
: α) : condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r => (preCDF ρ
 r p.2).toReal) (measurable_preCDF'.comp measurable_snd) ((), a)
参数：ρ : Measure (α × Real)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.ext`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 :
 TopologicalSpace R] {f g : StieltjesFunction R},   (∀ (x : R), ↑f x = ↑g x) → f
 = g
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.condCDF.eq_1`：∀ {α : Type u_1} {mα : MeasurableSpace α
} (ρ : MeasureTheory.Measure (α × ℝ)) (a : α),   ProbabilityTheory.condCDF ρ a =
     ProbabilityTheo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_unit_prod`：stieltjesOfMeasura
bleRat_unit_prod (hf : Measurable f) (a : α) : stieltjesOfMeasurableRat (fun (p 
: Unit × α) => f p.2) (hf.comp measurable_…
-/
lemma condCDF_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × ℝ)) (a : α) :
    condCDF ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal)
      (measurable_preCDF'.comp measurable_snd) ((), a) := by
  ext x
  rw [condCDF, ← stieltjesOfMeasurableRat_unit_prod]
/-
**ProbabilityTheory.isCondKernelCDF_condCDF** 是 Mathlib 中的一个引理，位于命名空间 `Probabili
tyTheory`。
形式化陈述：isCondKernelCDF_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : IsC
ondKernelCDF (fun p : Unit × α => condCDF ρ p.2) (Kernel.const Unit ρ) (Kernel.c
onst Unit ρ.fst)
参数：ρ : Measure (α × Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.condCDF_eq_stieltjesOfMeasurableRat_unit_prod`：condCDF
_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × Real)) (a : α) : condCD
F ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) …
· 使用引理 `ProbabilityTheory.isCondKernelCDF_stieltjesOfMeasurableRat`：isCondKernel
CDF_stieltjesOfMeasurableRat {f : α × β -> Rat -> Real} (hf : IsRatCondKernelCDF
 f κ ν) [IsFiniteKernel κ] : IsCondKernelCDF (st…
· 使用引理 `ProbabilityTheory.isRatCondKernelCDF_preCDF`：isRatCondKernelCDF_preCDF (
ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : IsRatCondKernelCDF (fun p r => (pr
eCDF ρ r p.2).toReal) (Kernel.con…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
-/
lemma isCondKernelCDF_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (Kernel.const Unit ρ)
      (Kernel.const Unit ρ.fst) := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_preCDF ρ)

/-- The conditional cdf is non-negative for all `a : α`. -/
/-
**ProbabilityTheory.condCDF_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：condCDF_nonneg (ρ : Measure (α × Real)) (a : α) (r : Real) : 0 <= condCDF 
ρ a r
参数：ρ : Measure (α × Real)；a : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_nonneg`：stieltjesOfMeasurable
Rat_nonneg (hf : Measurable f) (a : α) (r : Real) : 0 <= stieltjesOfMeasurableRa
t f hf a r
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf is non-negative for all `a : α`.
-/
theorem condCDF_nonneg (ρ : Measure (α × ℝ)) (a : α) (r : ℝ) : 0 ≤ condCDF ρ a r :=
  stieltjesOfMeasurableRat_nonneg _ a r

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
/-
**ProbabilityTheory.condCDF_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`
。
形式化陈述：condCDF_le_one (ρ : Measure (α × Real)) (a : α) (x : Real) : condCDF ρ a x
 <= 1
参数：ρ : Measure (α × Real)；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_le_one`：stieltjesOfMeasurable
Rat_le_one (hf : Measurable f) (a : α) (x : Real) : stieltjesOfMeasurableRat f h
f a x <= 1
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf is lower or equal to 1 for all `a : α`.
-/
theorem condCDF_le_one (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) : condCDF ρ a x ≤ 1 :=
  stieltjesOfMeasurableRat_le_one _ _ _

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
/-
**ProbabilityTheory.tendsto_condCDF_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：tendsto_condCDF_atBot (ρ : Measure (α × Real)) (a : α) : Tendsto (condCDF 
ρ a) atBot (𝓝 0)
参数：ρ : Measure (α × Real)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot`：tendsto_stielt
jesOfMeasurableRat_atBot (hf : Measurable f) (a : α) : Tendsto (stieltjesOfMeasu
rableRat f hf a) atBot (𝓝 0)
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf tends to 0 at -∞ for all `a : α`.
-/
theorem tendsto_condCDF_atBot (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) := tendsto_stieltjesOfMeasurableRat_atBot _ _

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
/-
**ProbabilityTheory.tendsto_condCDF_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：tendsto_condCDF_atTop (ρ : Measure (α × Real)) (a : α) : Tendsto (condCDF 
ρ a) atTop (𝓝 1)
参数：ρ : Measure (α × Real)；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop`：tendsto_stielt
jesOfMeasurableRat_atTop (hf : Measurable f) (a : α) : Tendsto (stieltjesOfMeasu
rableRat f hf a) atTop (𝓝 1)
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf tends to 1 at +∞ for all `a : α`.
-/
theorem tendsto_condCDF_atTop (ρ : Measure (α × ℝ)) (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) := tendsto_stieltjesOfMeasurableRat_atTop _ _
/-
**ProbabilityTheory.condCDF_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory`。
形式化陈述：condCDF_ae_eq (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat) : (fu
n a => condCDF ρ a r) =ᵐ[ρ.fst] fun a => (preCDF ρ r a).toReal
参数：ρ : Measure (α × Real)；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.condCDF_eq_stieltjesOfMeasurableRat_unit_prod`：condCDF
_eq_stieltjesOfMeasurableRat_unit_prod (ρ : Measure (α × Real)) (a : α) : condCD
F ρ a = stieltjesOfMeasurableRat (fun (p : Unit × α) …
· 使用引理 `ProbabilityTheory.stieltjesOfMeasurableRat_ae_eq`：stieltjesOfMeasurableR
at_ae_eq (hf : IsRatCondKernelCDF f κ ν) (a : α) (q : Rat) : (fun b => stieltjes
OfMeasurableRat f hf.measurable (a, b)…
· 使用引理 `ProbabilityTheory.isRatCondKernelCDF_preCDF`：isRatCondKernelCDF_preCDF (
ρ : Measure (α × Real)) [IsFiniteMeasure ρ] : IsRatCondKernelCDF (fun p r => (pr
eCDF ρ r p.2).toReal) (Kernel.con…
-/
theorem condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ condCDF ρ a r) =ᵐ[ρ.fst] fun a ↦ (preCDF ρ r a).toReal := by
  simp_rw [condCDF_eq_stieltjesOfMeasurableRat_unit_prod ρ]
  exact stieltjesOfMeasurableRat_ae_eq (isRatCondKernelCDF_preCDF ρ) () r
/-
**ProbabilityTheory.ofReal_condCDF_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：ofReal_condCDF_ae_eq (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (r : Rat
) : (fun a => ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r
参数：ρ : Measure (α × Real)；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ProbabilityTheory.preCDF_le_one`：preCDF_le_one (ρ : Measure (α × Real)) 
[IsFiniteMeasure ρ] : forallᵐ a ∂ρ.fst, forall r, preCDF ρ r a <= 1
· 使用定理 `ProbabilityTheory.condCDF_ae_eq`：condCDF_ae_eq (ρ : Measure (α × Real)) 
[IsFiniteMeasure ρ] (r : Rat) : (fun a => condCDF ρ a r) =ᵐ[ρ.fst] fun a => (pre
CDF ρ r a).toReal
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
-/
theorem ofReal_condCDF_ae_eq (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (r : ℚ) :
    (fun a ↦ ENNReal.ofReal (condCDF ρ a r)) =ᵐ[ρ.fst] preCDF ρ r := by
  filter_upwards [condCDF_ae_eq ρ r, preCDF_le_one ρ] with a ha ha_le_one
  rw [ha, ENNReal.ofReal_toReal]
  exact ((ha_le_one r).trans_lt ENNReal.one_lt_top).ne

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
/-
**ProbabilityTheory.measurable_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：measurable_condCDF (ρ : Measure (α × Real)) (x : Real) : Measurable fun a 
=> condCDF ρ a x
参数：ρ : Measure (α × Real)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.measurable_stieltjesOfMeasurableRat`：measurable_stielt
jesOfMeasurableRat (hf : Measurable f) (x : Real) : Measurable fun a => stieltje
sOfMeasurableRat f hf a x
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf is a measurable function of `a : α` for all `x : ℝ`.
-/
theorem measurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) : Measurable fun a ↦ condCDF ρ a x :=
  measurable_stieltjesOfMeasurableRat _ _

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
/-
**ProbabilityTheory.stronglyMeasurable_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：stronglyMeasurable_condCDF (ρ : Measure (α × Real)) (x : Real) : StronglyM
easurable fun a => condCDF ρ a x
参数：ρ : Measure (α × Real)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.stronglyMeasurable_stieltjesOfMeasurableRat`：stronglyM
easurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : Real) : StronglyMeas
urable fun a => stieltjesOfMeasurableRat f hf a x
· 使用引理 `ProbabilityTheory.measurable_preCDF'`：measurable_preCDF' {ρ : Measure (α
 × Real)} : Measurable fun a r => (preCDF ρ r a).toReal

--- 原说明 ---
The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`
.
-/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) (x : ℝ) :
    StronglyMeasurable fun a ↦ condCDF ρ a x := stronglyMeasurable_stieltjesOfMeasurableRat _ _
/-
**ProbabilityTheory.setLIntegral_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：setLIntegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Rea
l) {s : Set α} (hs : MeasurableSet s) : ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x
) ∂ρ.fst = ρ (s ×ˢ Iic x)
参数：ρ : Measure (α × Real)；x : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setLIntegral`：∀ {α : Type u_1} {β : Ty
pe u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheo
ry.Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用引理 `ProbabilityTheory.isCondKernelCDF_condCDF`：isCondKernelCDF_condCDF (ρ : 
Measure (α × Real)) [IsFiniteMeasure ρ] : IsCondKernelCDF (fun p : Unit × α => c
ondCDF ρ p.2) (Kernel.const Uni…
-/
theorem setLIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setLIntegral () hs x
/-
**ProbabilityTheory.lintegral_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheo
ry`。
形式化陈述：lintegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) 
: ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x)
参数：ρ : Measure (α × Real)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.lintegral`：∀ {α : Type u_1} {β : Type 
u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory.
Kernel α (β × ℝ)} {ν : Probabilit…
· 使用定理 `ProbabilityTheory.Kernel.const.instIsFiniteKernel`：∀ {α : Type u_1} {β :
 Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μβ : MeasureTheory
.Measure β}   [MeasureTheory.IsFiniteMe…
· 使用引理 `ProbabilityTheory.isCondKernelCDF_condCDF`：isCondKernelCDF_condCDF (ρ : 
Measure (α × Real)) [IsFiniteMeasure ρ] : IsCondKernelCDF (fun p : Unit × α => c
ondCDF ρ p.2) (Kernel.const Uni…
-/
theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).lintegral () x
/-
**ProbabilityTheory.integrable_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：integrable_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real)
 : Integrable (fun a => condCDF ρ a x) ρ.fst
参数：ρ : Measure (α × Real)；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.integrable`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → StieltjesFu
nction ℝ}   {κ : ProbabilityTheory…
· 使用引理 `ProbabilityTheory.isCondKernelCDF_condCDF`：isCondKernelCDF_condCDF (ρ : 
Measure (α × Real)) [IsFiniteMeasure ρ] : IsCondKernelCDF (fun p : Unit × α => c
ondCDF ρ p.2) (Kernel.const Uni…
-/
theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  (isCondKernelCDF_condCDF ρ).integrable () x
/-
**ProbabilityTheory.setIntegral_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：setIntegral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real
) {s : Set α} (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (
s ×ˢ Iic x)
参数：ρ : Measure (α × Real)；x : Real；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.setIntegral`：∀ {α : Type u_1} {β : Typ
e u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α × β → StieltjesF
unction ℝ}   {κ : ProbabilityTheory…
· 使用引理 `ProbabilityTheory.isCondKernelCDF_condCDF`：isCondKernelCDF_condCDF (ρ : 
Measure (α × Real)) [IsFiniteMeasure ρ] : IsCondKernelCDF (fun p : Unit × α => c
ondCDF ρ p.2) (Kernel.const Uni…
-/
theorem setIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).setIntegral () hs x
/-
**ProbabilityTheory.integral_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheor
y`。
形式化陈述：integral_condCDF (ρ : Measure (α × Real)) [IsFiniteMeasure ρ] (x : Real) :
 ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x)
参数：ρ : Measure (α × Real)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsCondKernelCDF.integral`：∀ {α : Type u_1} {β : Type u
_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {κ : ProbabilityTheory.K
ernel α (β × ℝ)} {ν : Probabilit…
· 使用引理 `ProbabilityTheory.isCondKernelCDF_condCDF`：isCondKernelCDF_condCDF (ρ : 
Measure (α × Real)) [IsFiniteMeasure ρ] : IsCondKernelCDF (fun p : Unit × α => c
ondCDF ρ p.2) (Kernel.const Uni…
-/
theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  (isCondKernelCDF_condCDF ρ).integral () x

section Measure

/-
**ProbabilityTheory.measure_condCDF_Iic** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：measure_condCDF_Iic (ρ : Measure (α × Real)) (a : α) (x : Real) : (condCDF
 ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x)
参数：ρ : Measure (α × Real)；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `ProbabilityTheory.tendsto_condCDF_atBot`：tendsto_condCDF_atBot (ρ : Meas
ure (α × Real)) (a : α) : Tendsto (condCDF ρ a) atBot (𝓝 0)
-/
theorem measure_condCDF_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _
/-
**ProbabilityTheory.measure_condCDF_univ** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：measure_condCDF_univ (ρ : Measure (α × Real)) (a : α) : (condCDF ρ a).meas
ure univ = 1
参数：ρ : Measure (α × Real)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.tendsto_condCDF_atBot`：tendsto_condCDF_atBot (ρ : Meas
ure (α × Real)) (a : α) : Tendsto (condCDF ρ a) atBot (𝓝 0)
· 使用定理 `ProbabilityTheory.tendsto_condCDF_atTop`：tendsto_condCDF_atTop (ρ : Meas
ure (α × Real)) (a : α) : Tendsto (condCDF ρ a) atTop (𝓝 1)
-/
theorem measure_condCDF_univ (ρ : Measure (α × ℝ)) (a : α) : (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)
/-
**ProbabilityTheory.instIsProbabilityMeasureCondCDF** 是 Mathlib 中的一个实例，位于命名空间 `P
robabilityTheory`。
形式化陈述：instIsProbabilityMeasureCondCDF (ρ : Measure (α × Real)) (a : α) : IsProba
bilityMeasure (condCDF ρ a).measure
参数：ρ : Measure (α × Real)；a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ProbabilityTheory.measure_condCDF_univ`：measure_condCDF_univ (ρ : Measur
e (α × Real)) (a : α) : (condCDF ρ a).measure univ = 1
-/
instance instIsProbabilityMeasureCondCDF (ρ : Measure (α × ℝ)) (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
/-
**ProbabilityTheory.measurable_measure_condCDF** 是 Mathlib 中的一个定理，位于命名空间 `Probab
ilityTheory`。
形式化陈述：measurable_measure_condCDF (ρ : Measure (α × Real)) : Measurable fun a => 
(condCDF ρ a).measure
参数：ρ : Measure (α × Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : α → Mea
sureTheory.Measure β}   [∀ (a : α), MeasureThe…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `borel_eq_generateFrom_Iic`：borel_eq_generateFrom_Iic : borel α = Measura
bleSpace.generateFrom (range Iic)
· 使用定理 `isPiSystem_Iic`：isPiSystem_Iic : IsPiSystem (range Iic : Set (Set α))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.measure_condCDF_Iic`：measure_condCDF_Iic (ρ : Measure 
(α × Real)) (a : α) (x : Real) : (condCDF ρ a).measure (Iic x) = ENNReal.ofReal 
(condCDF ρ a x)
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `ProbabilityTheory.measurable_condCDF`：measurable_condCDF (ρ : Measure (α
 × Real)) (x : Real) : Measurable fun a => condCDF ρ a x

--- 原说明 ---
The function `a ↦ (condCDF ρ a).measure` is measurable.
-/
theorem measurable_measure_condCDF (ρ : Measure (α × ℝ)) :
    Measurable fun a => (condCDF ρ a).measure :=
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u ↦ (measurable_condCDF ρ u).ennreal_ofReal

end Measure

end ProbabilityTheory

