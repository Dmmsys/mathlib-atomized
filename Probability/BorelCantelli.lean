/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Martingale.BorelCantelli
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Independence.Basic

/-!

# The second Borel-Cantelli lemma

This file contains the *second Borel-Cantelli lemma* which states that, given a sequence of
independent sets `(sₙ)` in a probability space, if `∑ n, μ sₙ = ∞`, then the limsup of `sₙ` has
measure 1. We employ a proof using Lévy's generalized Borel-Cantelli by choosing an appropriate
filtration.

## Main result

- `ProbabilityTheory.measure_limsup_eq_one`: the second Borel-Cantelli lemma.

**Note**: for the *first Borel-Cantelli lemma*, which holds in general measure spaces (not only
in probability spaces), see `MeasureTheory.measure_limsup_atTop_eq_zero`.
-/

public section

open scoped ENNReal Topology
open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section BorelCantelli

variable {ι β : Type*} [LinearOrder ι] [mβ : MeasurableSpace β] [NormedAddCommGroup β]
  [BorelSpace β] {f : ι → Ω → β} {i j : ι} {s : ι → Set Ω}

/-
**ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt** 是 Mathlib 中的一个定理，位于命名空
间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι
 : Type u_2} {β : Type u_3}   [inst : LinearOrder ι] [mβ : MeasurableSpace β] [i
nst_1 : NormedAddCommGroup β] [inst_2 : BorelSpace β]   {f : ι → Ω → β} {i j : ι
} (hf : ∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)),   ProbabilityTheory.
iIndepFun f μ →     i < j → ProbabilityTheory.Indep (MeasurableSpace.comap (f j)
 mβ) (↑(MeasureTheory.Filtration.natural f hf) i) μ
参数：hf : ∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；MeasurableSpace.comap 
(f j) mβ；↑(MeasureTheory.Filtration.natural f hf) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.indep_iSup_of_disjoint`：indep_iSup_of_disjoint (h_le :
 forall i, m i <= _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T)
 : Indep (⨆ i in S, m i) (⨆ i …
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
-/
theorem iIndepFun.indep_comap_natural_of_lt (hf : ∀ i, StronglyMeasurable (f i))
    (hfi : iIndepFun f μ) (hij : i < j) :
    Indep (MeasurableSpace.comap (f j) mβ) (Filtration.natural f hf i) μ := by
  suffices Indep (⨆ k ∈ ({j} : Set ι), MeasurableSpace.comap (f k) mβ)
      (⨆ k ∈ {k | k ≤ i}, MeasurableSpace.comap (f k) mβ) μ by rwa [iSup_singleton] at this
  exact indep_iSup_of_disjoint (fun k => (hf k).measurable.comap_le) hfi (by simpa)
/-
**ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.iIndepFun`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι
 : Type u_2} {β : Type u_3}   [inst : LinearOrder ι] [mβ : MeasurableSpace β] [i
nst_1 : NormedAddCommGroup β] [inst_2 : BorelSpace β]   {f : ι → Ω → β} {i j : ι
} [SecondCountableTopology β] [CompleteSpace β] [inst_5 : NormedSpace ℝ β]   (hf
 : ∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)),   ProbabilityTheory.iInde
pFun f μ →     i < j → μ[f j | ↑(MeasureTheory.Filtration.natural f hf) i] =ᵐ[μ]
 fun x => ∫ (x : Ω), f j x ∂μ
参数：hf : ∀ (i : ι), MeasureTheory.StronglyMeasurable (f i)；MeasureTheory.Filtrati
on.natural f hf；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepFun.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {β : ι → Type 
u_10}   {m : (i : ι) → MeasurableSpace…
· 使用定理 `MeasureTheory.condExp_indep_eq`：condExp_indep_eq (hle₁ : m₁ <= m) (hle₂ 
: m₂ <= m) [SigmaFinite (μ.trim hle₂)] (hf : StronglyMeasurable[m₁] f) (hindp : 
Indep m₁ m₂ μ) : μ[f…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Measurable.comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSpa
ce α} {m₂ : MeasurableSpace β} {f : α → β},   Measurable f → MeasurableSpace.com
ap f m₂ ≤…
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
· 使用定理 `ProbabilityTheory.iIndepFun.indep_comap_natural_of_lt`：∀ {Ω : Type u_1} 
{m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι : Type u_2} {β : Type 
u_3}   [inst : LinearOrder ι] [mβ : Measura…
-/
theorem iIndepFun.condExp_natural_ae_eq_of_lt [SecondCountableTopology β] [CompleteSpace β]
    [NormedSpace ℝ β] (hf : ∀ i, StronglyMeasurable (f i)) (hfi : iIndepFun f μ)
    (hij : i < j) : μ[f j | Filtration.natural f hf i] =ᵐ[μ] fun _ => μ[f j] := by
  have : IsProbabilityMeasure μ := hfi.isProbabilityMeasure
  exact condExp_indep_eq (hf j).measurable.comap_le (Filtration.le _ _)
    (comap_measurable <| f j).stronglyMeasurable (hfi.indep_comap_natural_of_lt hf hij)
/-
**ProbabilityTheory.iIndepSet.condExp_indicator_filtrationOfSet_ae_eq** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.iIndepSet`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι
 : Type u_2} [inst : LinearOrder ι] {i j : ι}   {s : ι → Set Ω} (hsm : ∀ (n : ι)
, MeasurableSet (s n)),   ProbabilityTheory.iIndepSet s μ →     i < j → μ[(s j).
indicator fun x => 1 | ↑(MeasureTheory.filtrationOfSet hsm) i] =ᵐ[μ] fun x => μ.
real (s j)
参数：hsm : ∀ (n : ι), MeasurableSet (s n)；s j；MeasureTheory.filtrationOfSet hsm；s 
j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_one`：stronglyMeasurable_one [One β] : S
tronglyMeasurable (1 : α -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Filtration.filtrationOfSet_eq_natural`：filtrationOfSet_eq_
natural [forall i, MulZeroOneClass (β i)] [forall i, Nontrivial (β i)] {s : ι ->
 Set Ω} (hsm : forall i, MeasurableSet[m]…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt`：∀ {Ω : Type u_1
} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι : Type u_2} {β : Typ
e u_3}   [inst : LinearOrder ι] [mβ : Measura…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ProbabilityTheory.iIndepSet.iIndepFun_indicator`：∀ {Ω : Type u_1} {ι : T
ype u_2} {β : Type u_6} {_mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
[inst : Zero β]   [inst_1 : One β] {m…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_indicator_const`：integral_indicator_const [Comple
teSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) : ∫ x : X, s.indicator
 (fun _ : X => e) x ∂μ = μ.r…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem iIndepSet.condExp_indicator_filtrationOfSet_ae_eq (hsm : ∀ n, MeasurableSet (s n))
    (hs : iIndepSet s μ) (hij : i < j) :
    μ[(s j).indicator (fun _ => 1 : Ω → ℝ) | filtrationOfSet hsm i] =ᵐ[μ]
    fun _ => μ.real (s j) := by
  rw [Filtration.filtrationOfSet_eq_natural (β := fun _ ↦ ℝ) hsm]
  refine (iIndepFun.condExp_natural_ae_eq_of_lt _ hs.iIndepFun_indicator hij).trans ?_
  simp only [integral_indicator_const _ (hsm _), smul_eq_mul, mul_one]; rfl

open Filter

/-- **The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)` such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1. -/
/-
**ProbabilityTheory.measure_limsup_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Probability
Theory`。
形式化陈述：measure_limsup_eq_one {s : Nat -> Set Ω} (hsm : forall n, MeasurableSet (s
 n)) (hs : iIndepSet s μ) (hs' : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1
参数：hsm : forall n, MeasurableSet (s n)；hs : iIndepSet s μ；hs' : (∑' n, μ (s n)) 
= ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.iIndepSet.isProbabilityMeasure`：∀ {Ω : Type u_1} {ι : 
Type u_2} {x : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {s : ι → Set Ω},
   ProbabilityTheory.iIndepSet s μ → M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `MeasureTheory.ae_mem_limsup_atTop_iff`：ae_mem_limsup_atTop_iff (μ : Meas
ure Ω) [IsFiniteMeasure μ] {s : Nat -> Set Ω} (hs : forall n, MeasurableSet[ℱ n]
 (s n)) : forallᵐ ω ∂μ, ω i…
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.measurableSet_filtrationOfSet'`：measurableSet_filtrationOf
Set' {s : ι -> Set Ω} (hsm : forall n, MeasurableSet[m] (s n)) (i : ι) : Measura
bleSet[filtrationOfSet hsm i] (s i…
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ProbabilityTheory.iIndepSet.condExp_indicator_filtrationOfSet_ae_eq`：∀ {
Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {ι : Type u
_2} [inst : LinearOrder ι] {i j : ι}   {s : ι → Set Ω} (h…
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_add_one_eq_top`：tsum_add_one_eq_top {f : Nat -> Real>=0∞} (
hf : ∑' n, f n = ∞) (hf0 : f 0 != ∞) : ∑' n, f (n + 1) = ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `ENNReal.tendsto_nat_tsum`：tendsto_nat_tsum (f : Nat -> Real>=0∞) : Tends
to (fun n : Nat => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n))
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone'`：tendsto_atTop_atTop_of_monotone
' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u) (H : ¬BddAbove (ran
ge u)) : Tendsto u atTop atTo…
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_range_succ_sub_sum`：∀ {M : Type u_4} (f : ℕ → M) {n : ℕ} [ins
t : AddCommGroup M],   ∑ i ∈ Finset.range (n + 1), f i - ∑ i ∈ Finset.range n, f
 i = f n
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
**The second Borel-Cantelli lemma**: Given a sequence of independent sets `(sₙ)`
 such that
`∑ n, μ sₙ = ∞`, `limsup sₙ` has measure 1.
-/
theorem measure_limsup_eq_one {s : ℕ → Set Ω} (hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ)
    (hs' : (∑' n, μ (s n)) = ∞) : μ (limsup s atTop) = 1 := by
  have : IsProbabilityMeasure μ := hs.isProbabilityMeasure
  rw [measure_congr (eventuallyEq_set.2 (ae_mem_limsup_atTop_iff μ <|
    measurableSet_filtrationOfSet' hsm) : (limsup s atTop : Set Ω) =ᵐ[μ]
      {ω | Tendsto (fun n => ∑ k ∈ Finset.range n,
        (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop})]
  suffices {ω | Tendsto (fun n => ∑ k ∈ Finset.range n,
      (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|filtrationOfSet hsm k]) ω) atTop atTop} =ᵐ[μ] Set.univ by
    rw [measure_congr this, measure_univ]
  have : ∀ᵐ ω ∂μ, ∀ n, (μ[(s (n + 1)).indicator (1 : Ω → ℝ) | filtrationOfSet hsm n]) ω = _ :=
    ae_all_iff.2 fun n => hs.condExp_indicator_filtrationOfSet_ae_eq hsm n.lt_succ_self
  filter_upwards [this] with ω hω
  refine eq_true (?_ : Tendsto _ _ _)
  simp_rw [hω]
  have htends : Tendsto (fun n => ∑ k ∈ Finset.range n, μ (s (k + 1))) atTop (𝓝 ∞) := by
    rw [← ENNReal.tsum_add_one_eq_top hs' (measure_ne_top _ _)]
    exact ENNReal.tendsto_nat_tsum _
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htends
  refine tendsto_atTop_atTop_of_monotone' ?_ ?_
  · refine monotone_nat_of_le_succ fun n => ?_
    rw [← sub_nonneg, Finset.sum_range_succ_sub_sum]
    exact ENNReal.toReal_nonneg
  · rintro ⟨B, hB⟩
    refine not_eventually.2 (Frequently.of_forall fun n => ?_) (htends B.toNNReal)
    rw [mem_upperBounds] at hB
    specialize hB (∑ k ∈ Finset.range n, μ (s (k + 1))).toReal _
    · refine ⟨n, ?_⟩
      rw [ENNReal.toReal_sum (by finiteness)]
      rfl
    · rwa [not_lt, ENNReal.ofNNReal_toNNReal, ENNReal.le_ofReal_iff_toReal_le]
      · simp
      · exact le_trans (by positivity) hB

end BorelCantelli

end ProbabilityTheory

