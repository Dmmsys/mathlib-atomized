/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Characterization of a finite measure by the integrals of products of bounded functions

Given two finite families of Borel spaces `(i : ι) → X i` and `(j : κ) → Y j` satisfying
`HasOuterApproxClosed`, a finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by
the values `∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for
`f : (i : ι) → X i → ℝ` and `g : (j : κ) → Y j → ℝ`
any families of bounded continuous functions.

In particular, if `μ` and `ν` are two finite measures over `Π i, X i` and `Π j, Y j` respectively,
then their product is the only finite measure `ξ` over `(Π i, X i) × (Π j, Y j)`
such that for any two families bounded continuous functions
`f : (i : ι) → X i → ℝ` and `g : (j : κ) → Y j → ℝ` we have
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
(∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`.

We specialize these results to the cases where one of the families contains only one type.

## Main statements

* `ext_of_integral_prod_mul_prod_boundedContinuousFunction`: A finite measure `μ`
  over `(Π i, X i) × (Π j, Y j)` is determined by the values
  `∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for `f : (i : ι) → X i → ℝ`
  and `g : (j : κ) → Y j → ℝ` any families of bounded continuous functions.

  This is stronger than `ext_of_integral_mul_boundedContinuousFunction` because we do not require
  `Π i, X i` and `Π j, Y j` to be Borel spaces and only consider products of continuous bounded
  functions rather than general continuous bounded functions `(Π i, X i) → ℝ` and `(Π j, Y j) → ℝ`.
* `eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction`: The product of two finite measures
  `μ` and `ν` is the only finite measure `ξ` over `(Π i, X i) × (Π j, Y j)` such that for all
  families of real bounded continuous functions `f` and `g` we have
  `∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
  (∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`.
* `ext_of_integral_mul_boundedContinuousFunction`: A finite measure `μ` over `X × Y` is determined
  by the values `∫ p, f p.1 * g p.2 ∂μ`, for `f : X → ℝ` and `g : Y → ℝ`
  any bounded continuous functions.
* `eq_prod_of_integral_mul_boundedContinuousFunction`: The product of two finite measures `μ` and
  `ν` is the only finite measure `ξ` such that for all real bounded continuous functions
  `f` and `g` we have `∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν`.

## Tags

bounded continuous function, product measure
-/

public section

open BoundedContinuousFunction MeasureTheory Topology Filter Set ENNReal NNReal MeasurableSpace
open scoped Topology ENNReal NNReal

namespace Measure

variable {ι κ Z T : Type*} {X : ι → Type*} {Y : κ → Type*}
  {mX : ∀ i, MeasurableSpace (X i)} [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)]
  [∀ i, HasOuterApproxClosed (X i)]
  {mY : ∀ j, MeasurableSpace (Y j)} [∀ j, TopologicalSpace (Y j)] [∀ j, BorelSpace (Y j)]
  [∀ j, HasOuterApproxClosed (Y j)]
  {mZ : MeasurableSpace Z} [TopologicalSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
  {mT : MeasurableSpace T} [TopologicalSpace T] [BorelSpace T] [HasOuterApproxClosed T]

section fintype

variable [Fintype ι] [Fintype κ]

/-- A finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by the values
`∫⁻ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for `f : (i : ι) → X i → ℝ≥0`
and `g : (j : κ) → Y j → ℝ≥0` any families of bounded continuous functions. -/
/-
**Measure.ext_of_lintegral_prod_mul_prod_boundedContinuousFunction** 是 Mathlib 中
的一个引理，位于命名空间 `Measure`。
形式化陈述：ext_of_lintegral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((
Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] (h : forall (f : (i : ι) -> X i ->ᵇ
 Real>=0) (g : (j : κ) -> Y j ->ᵇ Real>=0), ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j 
(p.2 j) ∂μ = ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) : μ = ν
参数：(Π i, X i) × (Π j, Y j)；h : forall (f : (i : ι) -> X i ->ᵇ Real>=0) (g : (j :
 κ) -> Y j ->ᵇ Real>=0), ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ = ∫⁻ p, 
(∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Set.pi_inter_distrib`：pi_inter_distrib : (s.pi fun i => t i inter t₁ i) 
= s.pi t inter s.pi t₁
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
· 使用定理 `generateFrom_eq_prod`：generateFrom_eq_prod {C : Set (Set α)} {D : Set (S
et β)} (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsCountabl
ySpanning …
· 使用定理 `generateFrom_eq_pi`：generateFrom_eq_pi [h : forall i, MeasurableSpace (α
 i)] {C : forall i, Set (Set (α i))} (hC : forall i, generateFrom (C i) = h i) (
h2C : fo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `borel_eq_generateFrom_isClosed`：borel_eq_generateFrom_isClosed [Topologi
calSpace α] : borel α = .generateFrom { s | IsClosed s }
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `MeasureTheory.ext_of_generate_finite`：ext_of_generate_finite (C : Set (S
et α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C) [IsFiniteMeasure μ] (hμν :
 forall s in C, μ s = ν s)…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
A finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by the values
`∫⁻ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for `f : (i : ι) → X i → ℝ≥0
`
and `g : (j : κ) → Y j → ℝ≥0` any families of bounded continuous functions.
-/
lemma ext_of_lintegral_prod_mul_prod_boundedContinuousFunction
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ≥0) (g : (j : κ) → Y j →ᵇ ℝ≥0),
      ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ =
      ∫⁻ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  have hμν : μ univ = ν univ := by convert! h 1 1 <;> simp
  have : IsFiniteMeasure ν := ⟨by simp [← hμν]⟩
  let π : Set (Set ((Π i, X i) × (Π j, Y j))) :=
    Set.image2 (fun s t ↦ s ×ˢ t) (Set.univ.pi '' (Set.univ.pi fun _ ↦ {s | IsClosed s}))
      (Set.univ.pi '' (Set.univ.pi fun _ ↦ {t | IsClosed t}))
  have hπ1 : IsPiSystem π := by
    rintro - ⟨-, ⟨s₁, hs₁, rfl⟩, -, ⟨t₁, ht₁, rfl⟩, rfl⟩ -
      ⟨-, ⟨s₂, hs₂, rfl⟩, -, ⟨t₂, ht₂, rfl⟩, rfl⟩ -
    refine ⟨_, ⟨fun i ↦ s₁ i ∩ s₂ i, ?_, rfl⟩, _, ⟨fun j ↦ t₁ j ∩ t₂ j, ?_, rfl⟩, ?_⟩
    · simp only [Set.mem_pi, mem_univ, mem_ofPred_eq, forall_const] at hs₁ hs₂ ⊢
      exact fun i ↦ (hs₁ i).inter (hs₂ i)
    · simp only [Set.mem_pi, mem_univ, mem_ofPred_eq, forall_const] at ht₁ ht₂ ⊢
      exact fun j ↦ (ht₁ j).inter (ht₂ j)
    simp [Set.pi_inter_distrib, Set.prod_inter_prod]
  have hπ2 : Prod.instMeasurableSpace = generateFrom π := by
    rw [← generateFrom_eq_prod (C := Set.univ.pi '' (Set.univ.pi fun _ ↦ {s | IsClosed s}))
      (D := Set.univ.pi '' (Set.univ.pi fun _ ↦ {t | IsClosed t}))]
    · rw [← generateFrom_eq_pi (C := fun _ ↦ {s | IsClosed s})]
      · simp [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed]
      · exact fun _ ↦ ⟨fun _ ↦ Set.univ, fun _ ↦ isClosed_univ, iUnion_const _⟩
    · rw [← generateFrom_eq_pi (C := fun _ ↦ {t | IsClosed t})]
      · simp [BorelSpace.measurable_eq, borel_eq_generateFrom_isClosed]
      · exact fun _ ↦ ⟨fun _ ↦ Set.univ, fun _ ↦ isClosed_univ, iUnion_const _⟩
    · exact ⟨fun _ ↦ Set.univ, fun _ ↦ ⟨fun _ ↦ Set.univ, by simp, by simp⟩, iUnion_const _⟩
    · exact ⟨fun _ ↦ Set.univ, fun _ ↦ ⟨fun _ ↦ Set.univ, by simp, by simp⟩, iUnion_const _⟩
  refine ext_of_generate_finite π hπ2 hπ1 ?_ hμν
  rintro - ⟨-, ⟨s, hs, rfl⟩, -, ⟨t, ht, rfl⟩, rfl⟩
  simp only [Set.mem_pi, mem_univ, mem_ofPred_eq, forall_const] at hs ht
  have (p : (Π i, X i) × (Π j, Y j)) := ENNReal.continuous_coe.tendsto _ |>.comp <|
    (tendsto_finsetProd Finset.univ (fun i _ ↦ tendsto_pi_nhds.1
      (HasOuterApproxClosed.tendsto_apprSeq (hs i)) (p.1 i))).mul
    (tendsto_finsetProd Finset.univ (fun j _ ↦ tendsto_pi_nhds.1
      (HasOuterApproxClosed.tendsto_apprSeq (ht j)) (p.2 j)))
  have hp1 (x : Π i, X i) : ∏ i, (s i).indicator (fun _ ↦ (1 : ℝ≥0)) (x i) =
      (Set.univ.pi s).indicator 1 x := by
    simp only [Set.indicator, Set.mem_pi, mem_univ, forall_const, Pi.ofNat_apply]
    split_ifs with hy
    · simp only [Set.mem_pi, mem_univ, forall_const] at hy
      exact Finset.prod_eq_one (by simpa)
    · simpa [Finset.prod_eq_zero_iff] using hy
  have hp2 (y : Π j, Y j) : ∏ j, (t j).indicator (fun _ ↦ (1 : ℝ≥0)) (y j) =
      (Set.univ.pi t).indicator 1 y := by
    simp only [Set.indicator, Set.mem_pi, mem_univ, forall_const, Pi.ofNat_apply]
    split_ifs with hy
    · simp only [Set.mem_pi, mem_univ, forall_const] at hy
      exact Finset.prod_eq_one (by simpa)
    · simpa [Finset.prod_eq_zero_iff] using hy
  simp_rw [hp1, hp2, ← Set.indicator_prod_one, Prod.eta] at this
  have h1 : Tendsto (fun n ↦ ∫⁻ p, ((∏ i, (hs i).apprSeq n (p.1 i)) *
        ∏ j, (ht j).apprSeq n (p.2 j) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ p, (((Set.univ.pi s) ×ˢ (Set.univ.pi t)).indicator 1 p : ℝ≥0) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [Finset.prod_le_one (by simp), Finset.prod_le_one (by simp)]
    · simp
    · exact fun j _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (ht j) _ _
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs i) _ _
  have h2 : Tendsto (fun n ↦ ∫⁻ p, ((∏ i, (hs i).apprSeq n (p.1 i)) *
        ∏ j, (ht j).apprSeq n (p.2 j) : ℝ≥0) ∂μ)
      atTop (𝓝 (∫⁻ p, (((Set.univ.pi s) ×ˢ (Set.univ.pi t)).indicator 1 p : ℝ≥0) ∂ν)) := by
    simp_rw [coe_mul, h]
    refine tendsto_lintegral_filter_of_dominated_convergence 1
      (Eventually.of_forall <| by fun_prop) (Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ ?_)
      (by simp) (ae_of_all _ this)
    grw [Finset.prod_le_one (by simp), Finset.prod_le_one (by simp)]
    · simp
    · exact fun j _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (ht j) _ _
    · exact fun i _ ↦ HasOuterApproxClosed.apprSeq_apply_le_one (hs i) _ _
  convert! tendsto_nhds_unique h1 h2 <;>
    simp [(MeasurableSet.univ_pi (fun i ↦ (hs i).measurableSet)).prod
      (.univ_pi (fun j ↦ (ht j).measurableSet))]

/-- A finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by the values
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for `f : (i : ι) → X i → ℝ`
and `g : (j : κ) → Y j → ℝ` any families of bounded continuous functions. -/
/-
**Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction** 是 Mathlib 中的
一个引理，位于命名空间 `Measure`。
形式化陈述：ext_of_integral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π
 i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f :
 (i : ι) -> X i ->ᵇ Real) (g : (j : κ) -> Y j ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i))
 * ∏ j, g j (p.2 j) ∂μ = ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) : μ = ν
参数：(Π i, X i) × (Π j, Y j)；h : forall (f : (i : ι) -> X i ->ᵇ Real) (g : (j : κ)
 -> Y j ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ = ∫ p, (∏ i, f 
i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_lintegral_prod_mul_prod_boundedContinuousFunction`：ext_of
_lintegral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × 
(Π j, Y j))} [IsFiniteMeasure μ] (h : forall (f : (i :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_eq_toReal_iff'`：toReal_eq_toReal_iff' {x y : Real>=0∞} (h
x : x != ⊤) (hy : y != ⊤) : x.toReal = y.toReal ↔ x = y
· 使用定理 `instBoundedMulNNReal`：BoundedMul NNReal
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ENNReal.ofNNReal_finsetProd`：ofNNReal_finsetProd (s : Finset ι) (f : ι -
> Real>=0) : ↑(∏ i in s, f i) = ∏ i in s, ofNNReal (f i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `BoundedContinuousFunction.coe_prod`：coe_prod {ι : Type*} (s : Finset ι) 
[CommMonoid R] [BoundedMul R] [ContinuousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s,
 f i) = ∏ i in s, ⇑(f i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `BoundedContinuousFunction.lintegral_lt_top_of_nnreal`：lintegral_lt_top_o
f_nnreal (f : X ->ᵇ Real>=0) : ∫⁻ x, f x ∂μ < ∞
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
A finite measure `μ` over `(Π i, X i) × (Π j, Y j)` is determined by the values
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂μ`, for `f : (i : ι) → X i → ℝ`
and `g : (j : κ) → Y j → ℝ` any families of bounded continuous functions.
-/
lemma ext_of_integral_prod_mul_prod_boundedContinuousFunction
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂μ =
      ∫ p, (∏ i, f i (p.1 i)) * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  refine ext_of_lintegral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [← toReal_eq_toReal_iff']
  · simp only [ofNNReal_finsetProd]
    have {μ : Measure ((Π i, X i) × Π j, Y j)} :
        (∫⁻ p, (∏ i, (f i (p.1 i) : ℝ≥0∞)) * ∏ j, (g j (p.2 j) : ℝ≥0∞) ∂μ).toReal =
          ∫ p, (∏ i, (f i (p.1 i)).toReal) * ∏ j, (g j (p.2 j)).toReal ∂μ := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · simp [Finset.prod_nonneg, ofReal_prod_of_nonneg]
      · exact Eventually.of_forall fun _ ↦ by positivity
      exact AEStronglyMeasurable.mul
        (Finset.aestronglyMeasurable_fun_prod _ fun _ _ ↦
          continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
        (Finset.aestronglyMeasurable_fun_prod _ fun _ _ ↦
          continuous_coe.aestronglyMeasurable.comp_measurable (by fun_prop))
    simp_rw [this]
    exact h (fun i ↦ ⟨⟨fun x ↦ (f i x), by fun_prop⟩, (f i).map_bounded'⟩)
      (fun j ↦ ⟨⟨fun y ↦ (g j y), by fun_prop⟩, (g j).map_bounded'⟩)
  · convert!
    (lintegral_lt_top_of_nnreal μ
        ((∏ i, (f i).compContinuous ⟨Function.eval i ∘ Prod.fst, by fun_prop⟩) *
          (∏ j, (g j).compContinuous ⟨Function.eval j ∘ Prod.snd, by fun_prop⟩))).ne
    simp
  · convert!
    (lintegral_lt_top_of_nnreal ν
        ((∏ i, (f i).compContinuous ⟨Function.eval i ∘ Prod.fst, by fun_prop⟩) *
          (∏ j, (g j).compContinuous ⟨Function.eval j ∘ Prod.snd, by fun_prop⟩))).ne
    simp

/-- The product of two finite measures `μ` and `ν` is the only finite measure `ξ` such that
for all families of real bounded continuous functions `f` and `g` we have
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
(∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`. -/
/-
**Measure.eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction** 是 Mathli
b 中的一个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction {μ : Measure (
Π i, X i)} {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))} [IsF
initeMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : (i : ι)
 -> X i ->ᵇ Real) (g : (j : κ) -> Y j ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i)) * (∏ j,
 g j (p.2 j)) ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)) : ξ = μ.
prod ν
参数：Π i, X i；Π j, Y j；(Π i, X i) × (Π j, Y j)；h : forall (f : (i : ι) -> X i ->ᵇ 
Real) (g : (j : κ) -> Y j ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i)) * (∏ j, g j (p.2 j)
) ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction`：ext_of_
integral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × (Π
 j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
The product of two finite measures `μ` and `ν` is the only finite measure `ξ` su
ch that
for all families of real bounded continuous functions `f` and `g` we have
`∫ p, (Π i, f i (p.1 i)) * (Π j, g j (p.2 j)) ∂ξ =
(∫ x, Π i, f i (x i) ∂μ) * (∫ y, Π j, g j (y j) ∂ν)`.
-/
lemma eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction {μ : Measure (Π i, X i)}
    {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * (∏ j, g j (p.2 j)) ∂ξ =
      (∫ x, ∏ i, f i (x i) ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in -- simp followed by fun_prop
/-
**Measure.ext_of_integral_prod_mul_boundedContinuousFunction** 是 Mathlib 中的一个引理，
位于命名空间 `Measure`。
形式化陈述：ext_of_integral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X
 i) × T)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f : (i : ι) -> X 
i ->ᵇ Real) (g : T ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂μ = ∫ p, (∏ i, f 
i (p.1 i)) * g p.2 ∂ν) : μ = ν
参数：(Π i, X i) × T；h : forall (f : (i : ι) -> X i ->ᵇ Real) (g : T ->ᵇ Real), ∫ p
, (∏ i, f i (p.1 i)) * g p.2 ∂μ = ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.fst`：Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).1
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用引理 `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction`：ext_of_
integral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × (Π
 j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
lemma ext_of_integral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂μ = ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ν) :
    μ = ν := by
  let e : ((Π i, X i) × T) ≃ᵐ ((Π i, X i) × (Unit → T)) :=
    { toFun p := ⟨fun i ↦ p.1 i, fun _ ↦ p.2⟩
      invFun p := ⟨fun i ↦ p.1 i, p.2 ()⟩
      left_inv p := by simp
      right_inv p := by simp }
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e] using h f (g ())
/-
**Measure.eq_prod_of_integral_prod_mul_boundedContinuousFunction** 是 Mathlib 中的一
个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_prod_mul_boundedContinuousFunction {μ : Measure (Π i, 
X i)} {ν : Measure T} {ξ : Measure ((Π i, X i) × T)} [IsFiniteMeasure μ] [IsFini
teMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : (i : ι) -> X i ->ᵇ Real) (g : 
T ->ᵇ Real), ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ 
t, g t ∂ν)) : ξ = μ.prod ν
参数：Π i, X i；(Π i, X i) × T；h : forall (f : (i : ι) -> X i ->ᵇ Real) (g : T ->ᵇ R
eal), ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ t, g t 
∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_boundedContinuousFunction`：ext_of_integ
ral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × T)} [IsFinit
eMeasure μ] [IsFiniteMeasure ν] (h : forall (f :…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma eq_prod_of_integral_prod_mul_boundedContinuousFunction {μ : Measure (Π i, X i)}
    {ν : Measure T} {ξ : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (i : ι) → X i →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, (∏ i, f i (p.1 i)) * g p.2 ∂ξ = (∫ x, ∏ i, f i (x i) ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]
/-
**Measure.ext_of_integral_mul_prod_boundedContinuousFunction** 是 Mathlib 中的一个引理，
位于命名空间 `Measure`。
形式化陈述：ext_of_integral_mul_prod_boundedContinuousFunction {μ ν : Measure (Z × (Π 
j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f : Z ->ᵇ Real) (
g : (j : κ) -> Y j ->ᵇ Real), ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂μ = ∫ p, f p.1 * ∏ 
j, g j (p.2 j) ∂ν) : μ = ν
参数：Z × (Π j, Y j)；h : forall (f : Z ->ᵇ Real) (g : (j : κ) -> Y j ->ᵇ Real), ∫ p
, f p.1 * ∏ j, g j (p.2 j) ∂μ = ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用引理 `Measure.ext_of_integral_prod_mul_boundedContinuousFunction`：ext_of_integ
ral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × T)} [IsFinit
eMeasure μ] [IsFiniteMeasure ν] (h : forall (f :…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma ext_of_integral_mul_prod_boundedContinuousFunction {μ ν : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂μ = ∫ p, f p.1 * ∏ j, g j (p.2 j) ∂ν) :
    μ = ν := by
  let e : (Z × (Π i, Y i)) ≃ᵐ ((Π i, Y i) × Z) := .prodComm
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e, mul_comm] using! h g f
/-
**Measure.eq_prod_of_integral_mul_prod_boundedContinuousFunction** 是 Mathlib 中的一
个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_mul_prod_boundedContinuousFunction {μ : Measure Z} {ν 
: Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))} [IsFiniteMeasure μ] [IsFini
teMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : Z ->ᵇ Real) (g : (j : κ) -> Y 
j ->ᵇ Real), ∫ p, f p.1 * (∏ j, g j (p.2 j)) ∂ξ = (∫ z, f z ∂μ) * (∫ y, ∏ j, g j
 (y j) ∂ν)) : ξ = μ.prod ν
参数：Π j, Y j；Z × (Π j, Y j)；h : forall (f : Z ->ᵇ Real) (g : (j : κ) -> Y j ->ᵇ R
eal), ∫ p, f p.1 * (∏ j, g j (p.2 j)) ∂ξ = (∫ z, f z ∂μ) * (∫ y, ∏ j, g j (y j) 
∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_mul_prod_boundedContinuousFunction`：ext_of_integ
ral_mul_prod_boundedContinuousFunction {μ ν : Measure (Z × (Π j, Y j))} [IsFinit
eMeasure μ] [IsFiniteMeasure ν] (h : forall (f :…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma eq_prod_of_integral_mul_prod_boundedContinuousFunction {μ : Measure Z}
    {ν : Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (j : κ) → Y j →ᵇ ℝ),
      ∫ p, f p.1 * (∏ j, g j (p.2 j)) ∂ξ = (∫ z, f z ∂μ) * (∫ y, ∏ j, g j (y j) ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_prod_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

set_option linter.flexible false in -- simp followed by fun_prop
/-- A finite measure `μ` over `X × Y` is determined by the values `∫ p, f p.1 * g p.2 ∂μ`,
for `f : X → ℝ` and `g : Y → ℝ` any bounded continuous functions. -/
/-
**Measure.ext_of_integral_mul_boundedContinuousFunction** 是 Mathlib 中的一个引理，位于命名空
间 `Measure`。
形式化陈述：ext_of_integral_mul_boundedContinuousFunction {μ ν : Measure (Z × T)} [IsF
initeMeasure μ] [IsFiniteMeasure ν] (h : forall (f : Z ->ᵇ Real) (g : T ->ᵇ Real
), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) : μ = ν
参数：Z × T；h : forall (f : Z ->ᵇ Real) (g : T ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂μ = ∫
 p, f p.1 * g p.2 ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MeasurableEquiv.map_measurableEquiv_injective`：map_measurableEquiv_injec
tive (e : α ≃ᵐ β) : Injective (Measure.map e)
· 使用引理 `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction`：ext_of_
integral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × (Π
 j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.integral_map_equiv`：integral_map_equiv {β} [MeasurableSpac
e β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a

--- 原说明 ---
A finite measure `μ` over `X × Y` is determined by the values `∫ p, f p.1 * g p.
2 ∂μ`,
for `f : X → ℝ` and `g : Y → ℝ` any bounded continuous functions.
-/
lemma ext_of_integral_mul_boundedContinuousFunction {μ ν : Measure (Z × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : T →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  let e : (Z × T) ≃ᵐ ((Unit → Z) × (Unit → T)) :=
    .symm <| .prodCongr (.funUnique ..) (.funUnique ..)
  rw [← e.map_measurableEquiv_injective.eq_iff]
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  rw [integral_map_equiv, integral_map_equiv]
  simpa [e] using! h (f ()) (g ())

/-- The product of two finite measures `μ` and `ν` is the only finite measure `ξ` such that
for all real bounded continuous functions `f` and `g` we have
`∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν`. -/
/-
**Measure.eq_prod_of_integral_mul_boundedContinuousFunction** 是 Mathlib 中的一个引理，位
于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_mul_boundedContinuousFunction {μ : Measure Z} {ν : Mea
sure T} {ξ : Measure (Z × T)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteM
easure ξ] (h : forall (f : Z ->ᵇ Real) (g : T ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ =
 (∫ z, f z ∂μ) * (∫ t, g t ∂ν)) : ξ = μ.prod ν
参数：Z × T；h : forall (f : Z ->ᵇ Real) (g : T ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ = (
∫ z, f z ∂μ) * (∫ t, g t ∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_mul_boundedContinuousFunction`：ext_of_integral_m
ul_boundedContinuousFunction {μ ν : Measure (Z × T)} [IsFiniteMeasure μ] [IsFini
teMeasure ν] (h : forall (f : Z ->ᵇ Real) (…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ

--- 原说明 ---
The product of two finite measures `μ` and `ν` is the only finite measure `ξ` su
ch that
for all real bounded continuous functions `f` and `g` we have
`∫ z, f z.1 * g z.2 ∂ξ = ∫ x, f x ∂μ * ∫ y, g y ∂ν`.
-/
lemma eq_prod_of_integral_mul_boundedContinuousFunction {μ : Measure Z}
    {ν : Measure T} {ξ : Measure (Z × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : T →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_boundedContinuousFunction fun f g ↦ by rw [h, ← integral_prod_mul]

end fintype

section finite

variable [Finite ι] [Finite κ]

/-
**Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction'** 是 Mathlib 中
的一个引理，位于命名空间 `Measure`。
形式化陈述：ext_of_integral_prod_mul_prod_boundedContinuousFunction' {μ ν : Measure ((
Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f 
: (Π i, X i) ->ᵇ Real) (g : (Π j, Y j) ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f
 p.1 * g p.2 ∂ν) : μ = ν
参数：(Π i, X i) × (Π j, Y j)；h : forall (f : (Π i, X i) ->ᵇ Real) (g : (Π j, Y j) 
->ᵇ Real), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction`：ext_of_
integral_prod_mul_prod_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × (Π
 j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h…
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `BoundedContinuousFunction.coe_prod`：coe_prod {ι : Type*} (s : Finset ι) 
[CommMonoid R] [BoundedMul R] [ContinuousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s,
 f i) = ∏ i in s, ⇑(f i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext_of_integral_prod_mul_prod_boundedContinuousFunction'
    {μ ν : Measure ((Π i, X i) × (Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  have := Fintype.ofFinite ι; have := Fintype.ofFinite κ
  refine ext_of_integral_prod_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  convert!
    h (∏ i, (f i).compContinuous ⟨Function.eval i, by fun_prop⟩)
      (∏ j, (g j).compContinuous ⟨Function.eval j, by fun_prop⟩) <;> simp
/-
**Measure.eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction'** 是 Mathl
ib 中的一个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction' {μ : Measure 
(Π i, X i)} {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))} [Is
FiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : (Π i, 
X i) ->ᵇ Real) (g : (Π j, Y j) ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) 
* (∫ y, g y ∂ν)) : ξ = μ.prod ν
参数：Π i, X i；Π j, Y j；(Π i, X i) × (Π j, Y j)；h : forall (f : (Π i, X i) ->ᵇ Real
) (g : (Π j, Y j) ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ y, g y ∂
ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_prod_boundedContinuousFunction'`：ext_of
_integral_prod_mul_prod_boundedContinuousFunction' {μ ν : Measure ((Π i, X i) × 
(Π j, Y j))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (…
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma eq_prod_of_integral_prod_mul_prod_boundedContinuousFunction' {μ : Measure (Π i, X i)}
    {ν : Measure (Π j, Y j)} {ξ : Measure ((Π i, X i) × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ y, g y ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_prod_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]
/-
**Measure.ext_of_integral_prod_mul_boundedContinuousFunction'** 是 Mathlib 中的一个引理
，位于命名空间 `Measure`。
形式化陈述：ext_of_integral_prod_mul_boundedContinuousFunction' {μ ν : Measure ((Π i, 
X i) × T)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f : (Π i, X i) -
>ᵇ Real) (g : T ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) : μ = 
ν
参数：(Π i, X i) × T；h : forall (f : (Π i, X i) ->ᵇ Real) (g : T ->ᵇ Real), ∫ p, f 
p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_boundedContinuousFunction`：ext_of_integ
ral_prod_mul_boundedContinuousFunction {μ ν : Measure ((Π i, X i) × T)} [IsFinit
eMeasure μ] [IsFiniteMeasure ν] (h : forall (f :…
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `BoundedContinuousFunction.coe_prod`：coe_prod {ι : Type*} (s : Finset ι) 
[CommMonoid R] [BoundedMul R] [ContinuousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s,
 f i) = ∏ i in s, ⇑(f i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext_of_integral_prod_mul_boundedContinuousFunction' {μ ν : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  have := Fintype.ofFinite ι
  refine ext_of_integral_prod_mul_boundedContinuousFunction fun f g ↦ ?_
  convert! h (∏ i, (f i).compContinuous ⟨Function.eval i, by fun_prop⟩) g <;> simp
/-
**Measure.eq_prod_of_integral_prod_mul_boundedContinuousFunction'** 是 Mathlib 中的
一个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_prod_mul_boundedContinuousFunction' {μ : Measure (Π i,
 X i)} {ν : Measure T} {ξ : Measure ((Π i, X i) × T)} [IsFiniteMeasure μ] [IsFin
iteMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : (Π i, X i) ->ᵇ Real) (g : T -
>ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ t, g t ∂ν)) : ξ = μ.prod ν
参数：Π i, X i；(Π i, X i) × T；h : forall (f : (Π i, X i) ->ᵇ Real) (g : T ->ᵇ Real)
, ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ t, g t ∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_prod_mul_boundedContinuousFunction'`：ext_of_inte
gral_prod_mul_boundedContinuousFunction' {μ ν : Measure ((Π i, X i) × T)} [IsFin
iteMeasure μ] [IsFiniteMeasure ν] (h : forall (f …
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma eq_prod_of_integral_prod_mul_boundedContinuousFunction' {μ : Measure (Π i, X i)}
    {ν : Measure T} {ξ : Measure ((Π i, X i) × T)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : (Π i, X i) →ᵇ ℝ) (g : T →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ x, f x ∂μ) * (∫ t, g t ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_prod_mul_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]
/-
**Measure.ext_of_integral_mul_prod_boundedContinuousFunction'** 是 Mathlib 中的一个引理
，位于命名空间 `Measure`。
形式化陈述：ext_of_integral_mul_prod_boundedContinuousFunction' {μ ν : Measure (Z × (Π
 i, Y i))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : forall (f : Z ->ᵇ Real) 
(g : (Π j, Y j) ->ᵇ Real), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) : μ = 
ν
参数：Z × (Π i, Y i)；h : forall (f : Z ->ᵇ Real) (g : (Π j, Y j) ->ᵇ Real), ∫ p, f 
p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_mul_prod_boundedContinuousFunction`：ext_of_integ
ral_mul_prod_boundedContinuousFunction {μ ν : Measure (Z × (Π j, Y j))} [IsFinit
eMeasure μ] [IsFiniteMeasure ν] (h : forall (f :…
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `BoundedContinuousFunction.coe_prod`：coe_prod {ι : Type*} (s : Finset ι) 
[CommMonoid R] [BoundedMul R] [ContinuousMul R] (f : ι -> α ->ᵇ R) : ⇑(∏ i in s,
 f i) = ∏ i in s, ⇑(f i)
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext_of_integral_mul_prod_boundedContinuousFunction' {μ ν : Measure (Z × (Π i, Y i))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ), ∫ p, f p.1 * g p.2 ∂μ = ∫ p, f p.1 * g p.2 ∂ν) :
    μ = ν := by
  have := Fintype.ofFinite κ
  refine ext_of_integral_mul_prod_boundedContinuousFunction fun f g ↦ ?_
  convert! h f (∏ j, (g j).compContinuous ⟨Function.eval j, by fun_prop⟩) <;> simp
/-
**Measure.eq_prod_of_integral_mul_prod_boundedContinuousFunction'** 是 Mathlib 中的
一个引理，位于命名空间 `Measure`。
形式化陈述：eq_prod_of_integral_mul_prod_boundedContinuousFunction' {μ : Measure Z} {ν
 : Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))} [IsFiniteMeasure μ] [IsFin
iteMeasure ν] [IsFiniteMeasure ξ] (h : forall (f : Z ->ᵇ Real) (g : (Π j, Y j) -
>ᵇ Real), ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ y, g y ∂ν)) : ξ = μ.prod ν
参数：Π j, Y j；Z × (Π j, Y j)；h : forall (f : Z ->ᵇ Real) (g : (Π j, Y j) ->ᵇ Real)
, ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ y, g y ∂ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Measure.ext_of_integral_mul_prod_boundedContinuousFunction'`：ext_of_inte
gral_mul_prod_boundedContinuousFunction' {μ ν : Measure (Z × (Π i, Y i))} [IsFin
iteMeasure μ] [IsFiniteMeasure ν] (h : forall (f …
· 使用定理 `MeasureTheory.Measure.prod.instIsFiniteMeasure`：∀ {α : Type u_4} {β : Ty
pe u_5} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : MeasureTheory.Mea
sure α)   (ν : MeasureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
-/
lemma eq_prod_of_integral_mul_prod_boundedContinuousFunction' {μ : Measure Z}
    {ν : Measure (Π j, Y j)} {ξ : Measure (Z × (Π j, Y j))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ξ]
    (h : ∀ (f : Z →ᵇ ℝ) (g : (Π j, Y j) →ᵇ ℝ),
      ∫ p, f p.1 * g p.2 ∂ξ = (∫ z, f z ∂μ) * (∫ y, g y ∂ν)) :
    ξ = μ.prod ν :=
  ext_of_integral_mul_prod_boundedContinuousFunction' fun f g ↦ by rw [h, ← integral_prod_mul]

end finite

end Measure

