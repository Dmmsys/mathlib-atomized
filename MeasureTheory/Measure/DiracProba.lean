/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Dirac deltas as probability measures and embedding of a space into probability measures on it

## Main definitions
* `diracProba`: The Dirac delta mass at a point as a probability measure.

## Main results
* `isEmbedding_diracProba`: If `X` is a completely regular T0 space with its Borel sigma algebra,
  then the mapping that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
  `X ↪ ProbabilityMeasure X`.

## Tags
probability measure, Dirac delta, embedding
-/

@[expose] public section

open Topology Metric Filter Set ENNReal NNReal BoundedContinuousFunction

open scoped Topology ENNReal NNReal BoundedContinuousFunction

/-
**CompletelyRegularSpace.exists_BCNN** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [Compl
etelyRegularSpace X] {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x 
∉ K) : exists (f : X ->ᵇ Real>=0), f x = 1 ∧ (forall y in K, f y = 0)
参数：K_closed : IsClosed K；x_notin_K : x ∉ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyRegularSpace.completely_regular`：∀ {X : Type u} {inst : Topolo
gicalSpace X} [self : CompletelyRegularSpace X] (x : X) (K : Set X),   IsClosed 
K → x ∉ K → ∃ f, Continuous f ∧…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `Real.lipschitzWith_toNNReal`：LipschitzWith 1 Real.toNNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Real.dist_le_of_mem_Icc_01`：dist_le_of_mem_Icc_01 {x y : Real} (hx : x i
n Icc (0 : Real) 1) (hy : y in Icc (0 : Real) 1) : dist x y <= 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
· 使用定理 `Continuous.subtype_val`：Continuous.subtype_val {f : Y -> Subtype p} (hf 
: Continuous f) : Continuous fun x => (f x : X)
· 使用定理 `instBoundedSubNNReal`：BoundedSub NNReal
· 使用定理 `NNReal.instContinuousSub`：ContinuousSub NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.toNNReal_zero`：toNNReal_zero : Real.toNNReal 0 = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
-/
lemma CompletelyRegularSpace.exists_BCNN {X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X]
    {K : Set X} (K_closed : IsClosed K) {x : X} (x_notin_K : x ∉ K) :
    ∃ (f : X →ᵇ ℝ≥0), f x = 1 ∧ (∀ y ∈ K, f y = 0) := by
  obtain ⟨g, g_cont, gx_zero, g_one_on_K⟩ :=
    CompletelyRegularSpace.completely_regular x K K_closed x_notin_K
  have g_bdd : ∀ x y, dist (Real.toNNReal (g x)) (Real.toNNReal (g y)) ≤ 1 := by
    refine fun x y ↦ ((Real.lipschitzWith_toNNReal).dist_le_mul (g x) (g y)).trans ?_
    simpa using Real.dist_le_of_mem_Icc_01 (g x).prop (g y).prop
  set g' := BoundedContinuousFunction.mkOfBound
      ⟨fun x ↦ Real.toNNReal (g x), continuous_real_toNNReal.comp g_cont.subtype_val⟩ 1 g_bdd
  set f := 1 - g'
  refine ⟨f, by simp [f, g', gx_zero], fun y y_in_K ↦ by simp [f, g', g_one_on_K y_in_K, tsub_self]⟩

namespace MeasureTheory

section embed_to_probabilityMeasure

variable {X : Type*} [MeasurableSpace X]

/-- The Dirac delta mass at a point `x : X` as a `ProbabilityMeasure`. -/
/-
**MeasureTheory.diracProba** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：diracProba (x : X) : ProbabilityMeasure X
参数：x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)

--- 原说明 ---
The Dirac delta mass at a point `x : X` as a `ProbabilityMeasure`.
-/
noncomputable def diracProba (x : X) : ProbabilityMeasure X :=
  ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

/-- The assignment `x ↦ diracProba x` is injective if all singletons are measurable. -/
/-
**MeasureTheory.injective_diracProba** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSpace.Sepa
ratesPoints X] : Function.Injective (fun (x : X) => diracProba x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The assignment `x ↦ diracProba x` is injective if all singletons are measurable.
-/
lemma injective_diracProba {X : Type*} [MeasurableSpace X] [MeasurableSpace.SeparatesPoints X] :
    Function.Injective (fun (x : X) ↦ diracProba x) := by
  intro x y x_eq_y
  simpa [diracProba, dirac_eq_dirac_iff] using congr(ProbabilityMeasure.toMeasure $x_eq_y)
/-
**MeasureTheory.diracProba_toMeasure_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：∀ {X : Type u_1} [inst : MeasurableSpace X] (x : X) {A : Set X},   Measura
bleSet A → ↑(MeasureTheory.diracProba x) A = A.indicator 1 x
参数：x : X；MeasureTheory.diracProba x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
-/
@[simp] lemma diracProba_toMeasure_apply' (x : X) {A : Set X} (A_mble : MeasurableSet A) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply' x A_mble
/-
**MeasureTheory.diracProba_toMeasure_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：∀ {X : Type u_1} [inst : MeasurableSpace X] {x : X} {A : Set X}, x ∈ A → ↑
(MeasureTheory.diracProba x) A = 1
参数：MeasureTheory.diracProba x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
-/
@[simp] lemma diracProba_toMeasure_apply_of_mem {x : X} {A : Set X} (x_in_A : x ∈ A) :
    (diracProba x).toMeasure A = 1 := Measure.dirac_apply_of_mem x_in_A
/-
**MeasureTheory.diracProba_toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：∀ {X : Type u_1} [inst : MeasurableSpace X] [MeasurableSingletonClass X] (
x : X) (A : Set X),   ↑(MeasureTheory.diracProba x) A = A.indicator 1 x
参数：x : X；A : Set X；MeasureTheory.diracProba x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.dirac_apply`：dirac_apply [MeasurableSingletonClass
 α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a
-/
@[simp] lemma diracProba_toMeasure_apply [MeasurableSingletonClass X] (x : X) (A : Set X) :
    (diracProba x).toMeasure A = A.indicator 1 x := Measure.dirac_apply _ _

variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The assignment `x ↦ diracProba x` is continuous `X → ProbabilityMeasure X`. -/
/-
**MeasureTheory.continuous_diracProba** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_diracProba : Continuous (fun (x : X) => diracProba x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`：t
endsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Probab
ilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (…
· 使用定理 `measurable_coe_nnreal_ennreal_iff`：measurable_coe_nnreal_ennreal_iff {f 
: α -> Real>=0} : (Measurable fun x => (f x : Real>=0∞)) ↔ Measurable f
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ENNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Re
al>=0∞)

--- 原说明 ---
The assignment `x ↦ diracProba x` is continuous `X → ProbabilityMeasure X`.
-/
lemma continuous_diracProba : Continuous (fun (x : X) ↦ diracProba x) := by
  rw [continuous_iff_continuousAt]
  apply fun x ↦ ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr fun f ↦ ?_
  have f_mble : Measurable (fun X ↦ (f X : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable
  simp only [diracProba, ProbabilityMeasure.coe_mk, lintegral_dirac' _ f_mble]
  exact (ENNReal.continuous_coe.comp f.continuous).continuousAt
/-
**MeasureTheory.not_tendsto_diracProba_of_not_tendsto** 是 Mathlib 中的一个引理，位于命名空间 
`MeasureTheory`。
形式化陈述：not_tendsto_diracProba_of_not_tendsto [CompletelyRegularSpace X] {x : X} (
L : Filter X) (h : ¬ Tendsto id L (𝓝 x)) : ¬ Tendsto diracProba L (𝓝 (diracProba
 x))
参数：L : Filter X；h : ¬ Tendsto id L (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CompletelyRegularSpace.exists_BCNN`：CompletelyRegularSpace.exists_BCNN {
X : Type*} [TopologicalSpace X] [CompletelyRegularSpace X] {K : Set X} (K_closed
 : IsClosed K) {x : X} (…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`：t
endsto_iff_forall_lintegral_tendsto {γ : Type*} {F : Filter γ} {μs : γ -> Probab
ilityMeasure Ω} {μ : ProbabilityMeasure Ω} : Tendsto μs F (…
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_coe_nnreal_ennreal_iff`：measurable_coe_nnreal_ennreal_iff {f 
: α -> Real>=0} : (Measurable fun x => (f x : Real>=0∞)) ↔ Measurable f
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `Filter.not_tendsto_iff_exists_frequently_notMem`：not_tendsto_iff_exists_
frequently_notMem {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : ¬Tendsto f l₁ l
₂ ↔ exists s in l₂, existsᶠ x in l₁, …
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
（共 34 条，此处仅展示前 30 条）
-/
lemma not_tendsto_diracProba_of_not_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X)
    (h : ¬ Tendsto id L (𝓝 x)) :
    ¬ Tendsto diracProba L (𝓝 (diracProba x)) := by
  obtain ⟨U, U_nhds, hU⟩ : ∃ U, U ∈ 𝓝 x ∧ ∃ᶠ x in L, x ∉ U := by
    contrapose! h
    exact h
  have Uint_nhds : interior U ∈ 𝓝 x := by simpa only [interior_mem_nhds] using U_nhds
  obtain ⟨f, fx_eq_one, f_vanishes_outside⟩ :=
    CompletelyRegularSpace.exists_BCNN isOpen_interior.isClosed_compl
      (by simpa only [mem_compl_iff, not_not] using mem_of_mem_nhds Uint_nhds)
  rw [ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto, not_forall]
  use f
  simp only [diracProba, ProbabilityMeasure.coe_mk, fx_eq_one,
             lintegral_dirac' _ (measurable_coe_nnreal_ennreal_iff.mpr f.continuous.measurable)]
  apply not_tendsto_iff_exists_frequently_notMem.mpr
  refine ⟨Ioi 0, Ioi_mem_nhds (by simp only [ENNReal.coe_one, zero_lt_one]),
          hU.mp (Eventually.of_forall ?_)⟩
  intro x x_notin_U
  rw [f_vanishes_outside x (compl_subset_compl.mpr interior_subset x_notin_U)]
  simp only [ENNReal.coe_zero, mem_Ioi, lt_self_iff_false, not_false_eq_true]
/-
**MeasureTheory.tendsto_diracProba_iff_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：tendsto_diracProba_iff_tendsto [CompletelyRegularSpace X] {x : X} (L : Fil
ter X) : Tendsto diracProba L (𝓝 (diracProba x)) ↔ Tendsto id L (𝓝 x)
参数：L : Filter X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `MeasureTheory.not_tendsto_diracProba_of_not_tendsto`：not_tendsto_diracPr
oba_of_not_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X) (h : ¬ Tend
sto id L (𝓝 x)) : ¬ Tendsto diracProba L …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用引理 `MeasureTheory.continuous_diracProba`：continuous_diracProba : Continuous 
(fun (x : X) => diracProba x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
lemma tendsto_diracProba_iff_tendsto [CompletelyRegularSpace X] {x : X} (L : Filter X) :
    Tendsto diracProba L (𝓝 (diracProba x)) ↔ Tendsto id L (𝓝 x) := by
  constructor
  · contrapose
    exact not_tendsto_diracProba_of_not_tendsto L
  · intro h
    have aux := (@continuous_diracProba X _ _ _).continuousAt (x := x)
    simp only [ContinuousAt] at aux
    exact aux.comp h

/-- An inverse function to `diracProba` (only really an inverse under hypotheses that
guarantee injectivity of `diracProba`). -/
/-
**MeasureTheory.diracProbaInverse** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：diracProbaInverse : range (diracProba (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inverse function to `diracProba` (only really an inverse under hypotheses tha
t
guarantee injectivity of `diracProba`).
-/
noncomputable def diracProbaInverse : range (diracProba (X := X)) → X :=
  fun μ' ↦ (mem_range.mp μ'.prop).choose

-- We redeclare `X` here to temporarily avoid the `[TopologicalSpace X]` instance.
/-
**MeasureTheory.diracProba_diracProbaInverse** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：∀ {X : Type u_2} [inst : MeasurableSpace X] (μ : ↑(Set.range MeasureTheory
.diracProba)),   MeasureTheory.diracProba (MeasureTheory.diracProbaInverse μ) = 
↑μ
参数：μ : ↑(Set.range MeasureTheory.diracProba)；MeasureTheory.diracProbaInverse μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
@[simp] lemma diracProba_diracProbaInverse {X : Type*} [MeasurableSpace X]
    (μ : range (diracProba (X := X))) :
    diracProba (diracProbaInverse μ) = μ := (mem_range.mp μ.prop).choose_spec
/-
**MeasureTheory.diracProbaInverse_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：diracProbaInverse_eq [T0Space X] {x : X} {μ : range (diracProba (X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.injective_diracProba`：injective_diracProba {X : Type*} [Me
asurableSpace X] [MeasurableSpace.SeparatesPoints X] : Function.Injective (fun (
x : X) => diracProba x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma diracProbaInverse_eq [T0Space X] {x : X} {μ : range (diracProba (X := X))}
    (h : μ = diracProba x) :
    diracProbaInverse μ = x := by
  apply injective_diracProba (X := X)
  simp only [← h]
  exact (mem_range.mp μ.prop).choose_spec

/-- In a T0 topological space `X`, the assignment `x ↦ diracProba x` is a bijection to its
range in `ProbabilityMeasure X`. -/
/-
**MeasureTheory.diracProbaEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：diracProbaEquiv [T0Space X] : X ≃ range (diracProba (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a T0 topological space `X`, the assignment `x ↦ diracProba x` is a bijection 
to its
range in `ProbabilityMeasure X`.
-/
noncomputable def diracProbaEquiv [T0Space X] : X ≃ range (diracProba (X := X)) where
  toFun := fun x ↦ ⟨diracProba x, by exact mem_range_self x⟩
  invFun := diracProbaInverse
  left_inv x := by apply diracProbaInverse_eq; rfl
  right_inv μ := Subtype.ext (by simp only [diracProba_diracProbaInverse])

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of `diracProbaEquiv.symm` and `diracProba` is the subtype inclusion. -/
/-
**MeasureTheory.diracProba_comp_diracProbaEquiv_symm_eq_val** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：diracProba_comp_diracProbaEquiv_symm_eq_val [T0Space X] : diracProba ∘ (di
racProbaEquiv (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.diracProba_diracProbaInverse`：∀ {X : Type u_2} [inst : Mea
surableSpace X] (μ : ↑(Set.range MeasureTheory.diracProba)),   MeasureTheory.dir
acProba (MeasureTheory.diracProb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of `diracProbaEquiv.symm` and `diracProba` is the subtype inclus
ion.
-/
lemma diracProba_comp_diracProbaEquiv_symm_eq_val [T0Space X] :
    diracProba ∘ (diracProbaEquiv (X := X)).symm = fun μ ↦ μ.val := by
  funext μ; simp [diracProbaEquiv]
/-
**MeasureTheory.tendsto_diracProbaEquivSymm_iff_tendsto** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory`。
形式化陈述：tendsto_diracProbaEquivSymm_iff_tendsto [T0Space X] [CompletelyRegularSpac
e X] {μ : range (diracProba (X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MeasureTheory.tendsto_diracProba_iff_tendsto`：tendsto_diracProba_iff_ten
dsto [CompletelyRegularSpace X] {x : X} (L : Filter X) : Tendsto diracProba L (𝓝
 (diracProba x)) ↔ Tendsto id L (𝓝…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用引理 `MeasureTheory.diracProba_comp_diracProbaEquiv_symm_eq_val`：diracProba_co
mp_diracProbaEquiv_symm_eq_val [T0Space X] : diracProba ∘ (diracProbaEquiv (X
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `tendsto_subtype_rng`：∀ {X : Type u} [inst : TopologicalSpace X] {Y : Typ
e u_5} {p : X → Prop} {l : Filter Y} {f : Y → Subtype p}   {x : Subtype p}, Filt
er.Tendst…
-/
lemma tendsto_diracProbaEquivSymm_iff_tendsto [T0Space X] [CompletelyRegularSpace X]
    {μ : range (diracProba (X := X))} (F : Filter (range (diracProba (X := X)))) :
    Tendsto diracProbaEquiv.symm F (𝓝 (diracProbaEquiv.symm μ)) ↔ Tendsto id F (𝓝 μ) := by
  have key :=
    tendsto_diracProba_iff_tendsto (F.map diracProbaEquiv.symm) (x := diracProbaEquiv.symm μ)
  rw [← (diracProbaEquiv (X := X)).symm_comp_self, ← tendsto_map'_iff] at key
  simp only [tendsto_map'_iff, map_map, Equiv.self_comp_symm, map_id] at key
  simp only [← key, diracProba_comp_diracProbaEquiv_symm_eq_val]
  convert! tendsto_subtype_rng.symm
  exact apply_rangeSplitting (fun x ↦ diracProba x) μ

/-- In a T0 topological space, `diracProbaEquiv` is continuous. -/
/-
**MeasureTheory.continuous_diracProbaEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：continuous_diracProbaEquiv [T0Space X] : Continuous (diracProbaEquiv (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用引理 `MeasureTheory.continuous_diracProba`：continuous_diracProba : Continuous 
(fun (x : X) => diracProba x)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
In a T0 topological space, `diracProbaEquiv` is continuous.
-/
lemma continuous_diracProbaEquiv [T0Space X] :
    Continuous (diracProbaEquiv (X := X)) :=
  Continuous.subtype_mk continuous_diracProba mem_range_self

/-- In a completely regular T0 topological space, the inverse of `diracProbaEquiv` is continuous. -/
/-
**MeasureTheory.continuous_diracProbaEquivSymm** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory`。
形式化陈述：continuous_diracProbaEquivSymm [T0Space X] [CompletelyRegularSpace X] : Co
ntinuous (diracProbaEquiv (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `continuousAt_of_tendsto_nhds`：continuousAt_of_tendsto_nhds [TopologicalS
pace Y] [T1Space Y] {f : X -> Y} {x : X} {y : Y} (h : Tendsto f (𝓝 x) (𝓝 y)) : C
ontinuousAt f x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用引理 `MeasureTheory.tendsto_diracProbaEquivSymm_iff_tendsto`：tendsto_diracProb
aEquivSymm_iff_tendsto [T0Space X] [CompletelyRegularSpace X] {μ : range (diracP
roba (X

--- 原说明 ---
In a completely regular T0 topological space, the inverse of `diracProbaEquiv` i
s continuous.
-/
lemma continuous_diracProbaEquivSymm [T0Space X] [CompletelyRegularSpace X] :
    Continuous (diracProbaEquiv (X := X)).symm := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply continuousAt_of_tendsto_nhds (y := diracProbaInverse μ)
  exact (tendsto_diracProbaEquivSymm_iff_tendsto _).mpr fun _ mem_nhds ↦ mem_nhds

/-- In a completely regular T0 topological space `X`, `diracProbaEquiv` is a homeomorphism to
its image in `ProbabilityMeasure X`. -/
/-
**MeasureTheory.diracProbaHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：diracProbaHomeomorph [T0Space X] [CompletelyRegularSpace X] : X ≃ₜ range (
diracProba (X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.continuous_diracProbaEquiv`：continuous_diracProbaEquiv [T0
Space X] : Continuous (diracProbaEquiv (X
· 使用引理 `MeasureTheory.continuous_diracProbaEquivSymm`：continuous_diracProbaEquiv
Symm [T0Space X] [CompletelyRegularSpace X] : Continuous (diracProbaEquiv (X

--- 原说明 ---
In a completely regular T0 topological space `X`, `diracProbaEquiv` is a homeomo
rphism to
its image in `ProbabilityMeasure X`.
-/
noncomputable def diracProbaHomeomorph [T0Space X] [CompletelyRegularSpace X] :
    X ≃ₜ range (diracProba (X := X)) :=
  @Homeomorph.mk X _ _ _ diracProbaEquiv continuous_diracProbaEquiv continuous_diracProbaEquivSymm

/-- If `X` is a completely regular T0 space with its Borel sigma algebra, then the mapping
that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
`X → ProbabilityMeasure X`. -/
/-
**MeasureTheory.isEmbedding_diracProba** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：isEmbedding_diracProba [T0Space X] [CompletelyRegularSpace X] : IsEmbeddin
g (fun (x : X) => diracProba x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce Y] [inst_2 :…
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `X` is a completely regular T0 space with its Borel sigma algebra, then the m
apping
that takes a point `x : X` to the delta-measure `diracProba x` is an embedding
`X → ProbabilityMeasure X`.
-/
theorem isEmbedding_diracProba [T0Space X] [CompletelyRegularSpace X] :
    IsEmbedding (fun (x : X) ↦ diracProba x) :=
  IsEmbedding.subtypeVal.comp diracProbaHomeomorph.isEmbedding

end embed_to_probabilityMeasure

end MeasureTheory

