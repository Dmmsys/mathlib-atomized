/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Properties of the integral of `mulExpNegMulSq`

The mapping `mulExpNegMulSq` can be used to transform a function `g : E → ℝ` into a bounded
function `mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)`. This file
contains results on the integral of `mulExpNegMulSq g ε` with respect to a finite measure `P`.

## Lemmas

- `tendsto_integral_mulExpNegMulSq_comp`: By the dominated convergence theorem and
  `mulExpNegMulSq_abs_le_norm`, the integral of `mulExpNegMulSq ε ∘ g` with respect to a
  finite measure `P` converges to the integral of `g`, as `ε → 0`;
- `tendsto_integral_mul_one_add_inv_smul_sq_pow`: The integral of `mulExpNegMulSq ε ∘ g` with
  respect to a finite measure `P` can be approximated by the integral of the sequence approximating
  the exponential function, `fun x => (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x`. This allows to
  transfer properties of a subalgebra of functions containing `g` to the function
  `mulExpNegMulSq ε ∘ g`, see e.g. `integral_mulExpNegMulSq_comp_eq`.

## Main Result

`dist_integral_mulExpNegMulSq_comp_le`: For a subalgebra of functions `A`, if for any `g ∈ A` the
integral with respect to two finite measures `P, P'` coincide, then the difference of the integrals
of `mulExpNegMulSq ε ∘ g` with respect to `P, P'` is bounded by `6 * √ε`.
This is a key ingredient in the proof of theorem `ext_of_forall_mem_subalgebra_integral_eq`, where
it is shown that a subalgebra of functions that separates points separates finite measures.
-/

public section

open MeasureTheory Real NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure E} [IsFiniteMeasure P] {ε : ℝ}

/-
**integrable_mulExpNegMulSq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_mulExpNegMulSq_comp (f : C(E, Real)) (hε : 0 < ε) : Integrable 
(fun x => mulExpNegMulSq ε (f x)) P
参数：f : C(E, Real)；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedContinuousFunction.integrable`：integrable [IsFiniteMeasure μ] (f 
: X ->ᵇ E) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.mulExpNegMulSq`：∀ {ε : ℝ} {α : Type u_1} [inst : TopologicalS
pace α] {f : α → ℝ},   Continuous f → Continuous fun x => ε.mulExpNegMulSq (f x)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.dist_mulExpNegMulSq_le_two_mul_sqrt`：dist_mulExpNegMulSq_le_two_mul
_sqrt (hε : 0 < ε) (x y : Real) : dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y)
 <= 2 * (√ε)⁻¹
-/
theorem integrable_mulExpNegMulSq_comp (f : C(E, ℝ)) (hε : 0 < ε) :
    Integrable (fun x => mulExpNegMulSq ε (f x)) P := by
  apply integrable P ⟨⟨fun x => mulExpNegMulSq ε (f x), by fun_prop⟩, ⟨2 * (√ε)⁻¹, _⟩⟩
  exact fun x y => dist_mulExpNegMulSq_le_two_mul_sqrt hε (f x) (f y)
/-
**integrable_mulExpNegMulSq_comp_restrict_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：integrable_mulExpNegMulSq_comp_restrict_of_isCompact {K : Set E} (hK : IsC
ompact K) (hKmeas : MeasurableSet K) (g : C(E, Real)) : Integrable (fun x => mul
ExpNegMulSq ε (g x)) (P.restrict K)
参数：hK : IsCompact K；hKmeas : MeasurableSet K；g : C(E, Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_compact'`：ContinuousOn.integrableOn_compact' (
hK : IsCompact K) (h'K : MeasurableSet K) (hf : ContinuousOn f K) : IntegrableOn
 f K μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.mulExpNegMulSq`：∀ {ε : ℝ} {α : Type u_1} [inst : TopologicalS
pace α] {f : α → ℝ},   Continuous f → Continuous fun x => ε.mulExpNegMulSq (f x)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
theorem integrable_mulExpNegMulSq_comp_restrict_of_isCompact {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (g : C(E, ℝ)) :
    Integrable (fun x => mulExpNegMulSq ε (g x)) (P.restrict K) :=
  g.continuous.mulExpNegMulSq.continuousOn.integrableOn_compact' hK hKmeas

/-- The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` converges to the
integral of `g`, as `ε → 0` from above. -/
/-
**tendsto_integral_mulExpNegMulSq_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_mulExpNegMulSq_comp (g : E ->ᵇ Real) : Tendsto (fun ε => 
∫ x, mulExpNegMulSq ε (g x) ∂P) (𝓝[>] 0) (𝓝 (∫ x, g x ∂P))
参数：g : E ->ᵇ Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_of_seq_tendsto`：tendsto_of_seq_tendsto {f : α -> β} {k : 
Filter α} {l : Filter β} [k.IsCountablyGenerated] : (forall x : Nat -> α, Tendst
o x atTop k -> Tend…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tendsto_nhdsWithin_iff`：tendsto_nhdsWithin_iff {a : α} {l : Filter β} {s
 : Set α} {f : β -> α} : Tendsto f l (𝓝[s] a) ↔ Tendsto f l (𝓝 a) ∧ forallᶠ n in
 l, f n in s
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_norm_le_const`：tendsto_integral
_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated] {F : ι -> α
 -> G} [IsFiniteMeasure μ] {f : α -> G} (h_m…
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
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.mulExpNegMulSq`：∀ {ε : ℝ} {α : Type u_1} [inst : TopologicalS
pace α] {f : α → ℝ},   Continuous f → Continuous fun x => ε.mulExpNegMulSq (f x)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.abs_mulExpNegMulSq_comp_le_norm`：abs_mulExpNegMulSq_comp_le_norm {E
 : Type*} [TopologicalSpace E] {x : E} (g : BoundedContinuousFunction E Real) (h
ε : 0 <= ε) : |(mulExpNegM…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` conv
erges to the
integral of `g`, as `ε → 0` from above.
-/
theorem tendsto_integral_mulExpNegMulSq_comp (g : E →ᵇ ℝ) :
    Tendsto (fun ε => ∫ x, mulExpNegMulSq ε (g x) ∂P) (𝓝[>] 0) (𝓝 (∫ x, g x ∂P)) := by
  apply tendsto_of_seq_tendsto
  intro u hu
  obtain ⟨N, hupos⟩ := eventually_atTop.mp (tendsto_nhdsWithin_iff.mp hu).2
  apply tendsto_integral_filter_of_norm_le_const ?h_meas ?h_bound ?h_lim
  · exact Eventually.of_forall (fun n => g.continuous.mulExpNegMulSq.aestronglyMeasurable)
  · use norm g
    rw [eventually_atTop]
    use N
    intro n hn
    exact Eventually.of_forall
      (fun _ => abs_mulExpNegMulSq_comp_le_norm g (le_of_lt (Set.mem_Ioi.mp (hupos n hn))))
  · exact Eventually.of_forall (fun _ => (tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_mulExpNegMulSq).comp hu)

/-- The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` can be
approximated by the integral of the sequence approximating the exponential function. -/
/-
**tendsto_integral_mul_one_add_inv_smul_sq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_integral_mul_one_add_inv_smul_sq_pow (g : E ->ᵇ Real) (hε : 0 < ε)
 : Tendsto (fun (n : Nat) => ∫ x, (g * (1 + (n : Real)⁻¹ • -(ε • g * g)) ^ n) x 
∂P) atTop (𝓝 (∫ x, mulExpNegMulSq ε (g x) ∂P))
参数：g : E ->ᵇ Real；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_filter_of_norm_le_const`：tendsto_integral
_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountablyGenerated] {F : ι -> α
 -> G} [IsFiniteMeasure μ] {f : α -> G} (h_m…
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
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `Continuous.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst : M
easurableSpace α] [inst_1 : TopologicalSpace α] [OpensMeasurableSpace α]   [inst
_3 : TopologicalSpa…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `mulExpNegMulSq ε ∘ g` with respect to a finite measure `P` can 
be
approximated by the integral of the sequence approximating the exponential funct
ion.
-/
theorem tendsto_integral_mul_one_add_inv_smul_sq_pow (g : E →ᵇ ℝ) (hε : 0 < ε) :
    Tendsto (fun (n : ℕ) => ∫ x, (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P)
    atTop (𝓝 (∫ x, mulExpNegMulSq ε (g x) ∂P)) := by
  apply tendsto_integral_filter_of_norm_le_const ?h_meas ?h_bound ?h_lim
  · apply Eventually.of_forall
    exact fun n => StronglyMeasurable.aestronglyMeasurable (Continuous.stronglyMeasurable
        (Continuous.mul g.continuous ((1 + ((n : ℝ)⁻¹ • -(ε • g * g))) ^ n).continuous))
  · obtain ⟨N, hgN⟩ := exists_nat_gt (ε * (norm g * norm g))
    use norm g
    rw [eventually_atTop]
    use N
    intro n hn
    have hnpos : 0 < (n : ℝ) := by
      apply lt_of_lt_of_le (lt_of_le_of_lt _ hgN) (Nat.cast_le.mpr hn)
      exact (mul_nonneg (le_of_lt hε) (mul_self_nonneg (norm g)))
    apply Eventually.of_forall
    intro x
    simp only [smul_neg, BoundedContinuousFunction.coe_mul, Pi.mul_apply, pow_apply,
      BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_one, coe_neg,
      BoundedContinuousFunction.coe_smul, smul_eq_mul, Pi.add_apply, Pi.one_apply, Pi.neg_apply,
      norm_mul, norm_eq_abs, norm_pow]
    refine (mul_le_mul_of_nonneg_right (norm_coe_le_norm g x) (pow_nonneg (abs_nonneg _) n)).trans
      <| mul_le_of_le_one_right (norm_nonneg _) ?_
    apply pow_le_one₀ (abs_nonneg _)
    rw [mul_assoc, inv_mul_eq_div, abs_le]
    refine ⟨?_, (add_le_iff_nonpos_right 1).mpr (Left.neg_nonpos_iff.mpr
      (div_nonneg (mul_nonneg (le_of_lt hε) (mul_self_nonneg (g x))) (le_of_lt hnpos)))⟩
    apply le_trans (by linarith) (sub_nonneg_of_le ((div_le_one hnpos).mpr _))
    apply le_trans (le_trans _ (le_of_lt hgN)) (Nat.cast_le.mpr hn)
    apply mul_le_mul (le_refl ε) _ (mul_self_nonneg (g x)) (le_of_lt hε)
    rw [← abs_le_iff_mul_self_le, abs_norm]
    exact norm_coe_le_norm g x
  · apply Eventually.of_forall
    intro x
    apply Tendsto.const_mul (g x)
    simpa [mul_assoc, inv_mul_eq_div, ← neg_div] using
      tendsto_one_add_div_pow_exp (-(ε * (g x * g x)))
/-
**integral_mulExpNegMulSq_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_mulExpNegMulSq_comp_eq {P' : Measure E} [IsFiniteMeasure P'] {A :
 Subalgebra Real (E ->ᵇ Real)} (hε : 0 < ε) (heq : forall g in A, ∫ x, (g : E ->
 Real) x ∂P = ∫ x, (g : E -> Real) x ∂P') {g : E ->ᵇ Real} (hgA : g in A) : ∫ x,
 mulExpNegMulSq ε (g x) ∂P = ∫ x, mulExpNegMulSq ε (g x) ∂P'
参数：E ->ᵇ Real；hε : 0 < ε；heq : forall g in A, ∫ x, (g : E -> Real) x ∂P = ∫ x, (
g : E -> Real) x ∂P'；hgA : g in A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_integral_mul_one_add_inv_smul_sq_pow`：tendsto_integral_mul_one_a
dd_inv_smul_sq_pow (g : E ->ᵇ Real) (hε : 0 < ε) : Tendsto (fun (n : Nat) => ∫ x
, (g * (1 + (n : Real)⁻¹ • -(ε • g…
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem integral_mulExpNegMulSq_comp_eq {P' : Measure E} [IsFiniteMeasure P']
    {A : Subalgebra ℝ (E →ᵇ ℝ)} (hε : 0 < ε)
    (heq : ∀ g ∈ A, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P') {g : E →ᵇ ℝ} (hgA : g ∈ A) :
    ∫ x, mulExpNegMulSq ε (g x) ∂P = ∫ x, mulExpNegMulSq ε (g x) ∂P' := by
  have one_add_inv_mul_mem (n : ℕ) : g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n ∈ A := by
    apply Subalgebra.mul_mem A hgA (Subalgebra.pow_mem A _ n)
    apply Subalgebra.add_mem A (Subalgebra.one_mem A) (Subalgebra.smul_mem A _ n⁻¹)
    exact Subalgebra.neg_mem A (Subalgebra.mul_mem A (Subalgebra.smul_mem A hgA ε) hgA)
  have limP : Tendsto (fun n : ℕ => ∫ x, (g * (1 + (n : ℝ)⁻¹ • -(ε • g * g)) ^ n) x ∂P) atTop
      (𝓝 (∫ x, mulExpNegMulSq ε (g x) ∂P')) := by
    rw [funext fun n => heq _ (one_add_inv_mul_mem n)]
    exact tendsto_integral_mul_one_add_inv_smul_sq_pow g hε
  exact tendsto_nhds_unique
    (tendsto_integral_mul_one_add_inv_smul_sq_pow g hε) limP
/-
**abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt (f : C(E, Real)) {K : 
Set E} (hK : MeasurableSet K) (hε : 0 < ε) (hKP : P Kᶜ < ε.toNNReal) : |∫ x, mul
ExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P| < √ε
参数：f : C(E, Real)；hK : MeasurableSet K；hε : 0 < ε；hKP : P Kᶜ < ε.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.norm_integral_sub_setIntegral_le`：norm_integral_sub_setInt
egral_le [IsFiniteMeasure μ] {C : Real} (hf : forallᵐ (x : X) ∂μ, ‖f x‖ <= C) {s
 : Set X} (hs : MeasurableSet s) (hf…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Real.abs_mulExpNegMulSq_le`：abs_mulExpNegMulSq_le (hε : 0 < ε) {x : Real
} : |mulExpNegMulSq ε x| <= (√ε)⁻¹
· 使用定理 `integrable_mulExpNegMulSq_comp`：integrable_mulExpNegMulSq_comp (f : C(E,
 Real)) (hε : 0 < ε) : Integrable (fun x => mulExpNegMulSq ε (f x)) P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_inv_lt_iff₀`：mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `Real.mul_self_sqrt`：mul_self_sqrt (h : 0 <= x) : √x * √x = x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.toReal_lt_of_lt_ofReal`：toReal_lt_of_lt_ofReal {b : Real} (h : a
 < ENNReal.ofReal b) : ENNReal.toReal a < b
-/
theorem abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt (f : C(E, ℝ))
    {K : Set E} (hK : MeasurableSet K) (hε : 0 < ε) (hKP : P Kᶜ < ε.toNNReal) :
    |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P| < √ε := by
  apply lt_of_le_of_lt (norm_integral_sub_setIntegral_le
    (Eventually.of_forall (fun _ => abs_mulExpNegMulSq_le hε)) hK
    (integrable_mulExpNegMulSq_comp f hε))
  rw [mul_inv_lt_iff₀ (sqrt_pos_of_pos hε), mul_self_sqrt (le_of_lt hε)]
  exact toReal_lt_of_lt_ofReal hKP
/-
**abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure {K : Set E} (hK : I
sCompact K) (hKmeas : MeasurableSet K) (f g : C(E, Real)) {δ : Real} (hε : 0 < ε
) (hfg : forall x in K, |g x - f x| < δ) : |∫ x in K, mulExpNegMulSq ε (g x) ∂P 
- ∫ x in K, mulExpNegMulSq ε (f x) ∂P| <= δ * (P K).toReal
参数：hK : IsCompact K；hKmeas : MeasurableSet K；f g : C(E, Real)；hε : 0 < ε；hfg : f
orall x in K, |g x - f x| < δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `integrable_mulExpNegMulSq_comp_restrict_of_isCompact`：integrable_mulExpN
egMulSq_comp_restrict_of_isCompact {K : Set E} (hK : IsCompact K) (hKmeas : Meas
urableSet K) (g : C(E, Real)) : Integrable…
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const`：norm_setIntegral_le_
of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C) : ‖∫
 x in s, f x ∂μ‖ <= C * μ.real s
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Real.dist_mulExpNegMulSq_le_dist`：dist_mulExpNegMulSq_le_dist (hε : 0 < 
ε) {x y : Real} : dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) <= dist x y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure {K : Set E} (hK : IsCompact K)
    (hKmeas : MeasurableSet K) (f g : C(E, ℝ)) {δ : ℝ} (hε : 0 < ε)
    (hfg : ∀ x ∈ K, |g x - f x| < δ) :
    |∫ x in K, mulExpNegMulSq ε (g x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P|
      ≤ δ * (P K).toReal := by
  rw [← (integral_sub (integrable_mulExpNegMulSq_comp_restrict_of_isCompact hK hKmeas g)
      (integrable_mulExpNegMulSq_comp_restrict_of_isCompact hK hKmeas f)), ← norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top
    (fun x hxK => le_trans (dist_mulExpNegMulSq_le_dist hε) (hfg x hxK).le)

variable {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']

/-- If for any `g ∈ A` the integrals with respect to two finite measures `P, P'` coincide, then the
difference of the integrals of `mulExpNegMulSq ε ∘ g` with respect to `P, P'` is bounded by
`6 * √ε`. -/
/-
**dist_integral_mulExpNegMulSq_comp_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_integral_mulExpNegMulSq_comp_le (f : E ->ᵇ Real) {A : Subalgebra Real
 (E ->ᵇ Real)} (hA : (A.map (toContinuousMapₐ Real)).SeparatesPoints) (heq : for
all g in A, ∫ x, (g : E -> Real) x ∂P = ∫ x, (g : E -> Real) x ∂P') (hε : 0 < ε)
 : |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'| <= 6 * √ε
参数：f : E ->ᵇ Real；E ->ᵇ Real；hA : (A.map (toContinuousMapₐ Real)).SeparatesPoint
s；heq : forall g in A, ∫ x, (g : E -> Real) x ∂P = ∫ x, (g : E -> Real) x ∂P'；hε
 : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用定理 `ENNReal.toReal_pos`：toReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top : a
 != ∞) : 0 < a.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
（共 123 条，此处仅展示前 30 条）

--- 原说明 ---
If for any `g ∈ A` the integrals with respect to two finite measures `P, P'` coi
ncide, then the
difference of the integrals of `mulExpNegMulSq ε ∘ g` with respect to `P, P'` is
 bounded by
`6 * √ε`.
-/
theorem dist_integral_mulExpNegMulSq_comp_le (f : E →ᵇ ℝ)
    {A : Subalgebra ℝ (E →ᵇ ℝ)} (hA : (A.map (toContinuousMapₐ ℝ)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P') (hε : 0 < ε) :
    |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'| ≤ 6 * √ε := by
  -- if both measures are zero, the result is trivial
  by_cases hPP' : P = 0 ∧ P' = 0
  · simp only [hPP', integral_zero_measure, sub_self, abs_zero, Nat.ofNat_pos,
    mul_nonneg_iff_of_pos_left, (le_of_lt (sqrt_pos_of_pos hε))]
  let const : ℝ := (max (P.real Set.univ) (P'.real Set.univ))
  have pos_of_measure : 0 < const := by
    rw [not_and_or] at hPP'
    rcases hPP' with hP0 | hP'0
    · exact lt_max_of_lt_left
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP0) (by finiteness))
    · exact lt_max_of_lt_right
        (toReal_pos ((Measure.measure_univ_ne_zero).mpr hP'0) (by finiteness))
  -- obtain K, a compact and closed set, which covers E up to a small area of measure at most ε
  -- w.r.t. both P and P'
  obtain ⟨KP, _, hKPco, hKPcl, hKP⟩ := MeasurableSet.exists_isCompact_isClosed_sdiff_lt
    (MeasurableSet.univ) (measure_ne_top P Set.univ) (ofReal_pos.mpr hε).ne'
  obtain ⟨KP', _, hKP'co, hKP'cl, hKP'⟩ := MeasurableSet.exists_isCompact_isClosed_sdiff_lt
    (MeasurableSet.univ) (measure_ne_top P' Set.univ) (ofReal_pos.mpr hε).ne'
  let K := KP ∪ KP'
  have hKco := IsCompact.union hKPco hKP'co
  have hKcl := IsClosed.union hKPcl hKP'cl
  simp only [← Set.compl_eq_univ_sdiff] at hKP hKP'
  have hKPbound : P (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_left))) hKP
  have hKP'bound : P' (KP ∪ KP')ᶜ < ε.toNNReal := lt_of_le_of_lt
        (measure_mono (Set.compl_subset_compl_of_subset (Set.subset_union_right))) hKP'
  -- Stone-Weierstrass approximation of f on K
  obtain ⟨g', hg'A, hg'approx⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      hA f hKco (Left.mul_pos (sqrt_pos_of_pos hε) (inv_pos_of_pos pos_of_measure))
  simp only [Subalgebra.mem_map] at hg'A
  let g := hg'A.choose
  have hgA : g ∈ A := hg'A.choose_spec.1
  have hgapprox : ∀ x ∈ K, ‖g x - f x‖ < √ε * const⁻¹ := by
    rw [← coe_toContinuousMapₐ ℝ g, hg'A.choose_spec.2]
    exact hg'approx
  -- collect the results needed in the decomposition at the end of the proof
  have line1 : |∫ x, mulExpNegMulSq ε (f x) ∂P
      - ∫ x in K, mulExpNegMulSq ε (f x) ∂P| < √ε :=
    abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      f (IsClosed.measurableSet hKcl) hε hKPbound
  have line3 : |∫ x in K, mulExpNegMulSq ε (g x) ∂P
      - ∫ x, mulExpNegMulSq ε (g x) ∂P| < √ε := by
    rw [abs_sub_comm]
    exact (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      g (IsClosed.measurableSet hKcl) hε hKPbound)
  have line5 : |∫ x, mulExpNegMulSq ε (g x) ∂P'
      - ∫ x in K, mulExpNegMulSq ε (g x) ∂P'| < √ε :=
    (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      g (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line7 : |∫ x in K, mulExpNegMulSq ε (f x) ∂P'
      - ∫ x, mulExpNegMulSq ε (f x) ∂P'| < √ε := by
    rw [abs_sub_comm]
    exact (abs_integral_sub_setIntegral_mulExpNegMulSq_comp_lt
      f (IsClosed.measurableSet hKcl) hε hKP'bound)
  have line2 : |∫ x in K, mulExpNegMulSq ε (f x) ∂P
      - ∫ x in K, mulExpNegMulSq ε (g x) ∂P| ≤ √ε := by
    rw [abs_sub_comm]
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_left _) (le_of_lt pos_of_measure)
    exact (toReal_le_toReal (by finiteness) (by finiteness)).mpr
        (measure_mono (Set.subset_univ _))
  have line6 : |∫ x in K, mulExpNegMulSq ε (g x) ∂P'
      - ∫ x in K, mulExpNegMulSq ε (f x) ∂P'| ≤ √ε := by
    apply le_trans (abs_setIntegral_mulExpNegMulSq_comp_sub_le_mul_measure hKco
      (IsClosed.measurableSet hKcl) f g hε hgapprox)
    rw [mul_assoc]
    apply mul_le_of_le_one_right (le_of_lt (sqrt_pos_of_pos hε))
    apply inv_mul_le_one_of_le₀ (le_max_of_le_right _) (le_of_lt pos_of_measure)
    exact (toReal_le_toReal (by finiteness) (by finiteness)).mpr
        (measure_mono (Set.subset_univ _))
  have line4 : |∫ x, mulExpNegMulSq ε (g x) ∂P
      - ∫ x, mulExpNegMulSq ε (g x) ∂P'| = 0 := by
    rw [abs_eq_zero, sub_eq_zero]
    exact integral_mulExpNegMulSq_comp_eq hε heq hgA
  calc
      |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'|
    ≤ |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (f x) ∂P|
      + |∫ x in K, mulExpNegMulSq ε (f x) ∂P - ∫ x in K, mulExpNegMulSq ε (g x) ∂P|
      + |∫ x in K, mulExpNegMulSq ε (g x) ∂P - ∫ x, mulExpNegMulSq ε (g x) ∂P|
      + |∫ x, mulExpNegMulSq ε (g x) ∂P - ∫ x, mulExpNegMulSq ε (g x) ∂P'|
      + |∫ x, mulExpNegMulSq ε (g x) ∂P' - ∫ x in K, mulExpNegMulSq ε (g x) ∂P'|
      + |∫ x in K, mulExpNegMulSq ε (g x) ∂P' - ∫ x in K, mulExpNegMulSq ε (f x) ∂P'|
      + |∫ x in K, mulExpNegMulSq ε (f x) ∂P' - ∫ x, mulExpNegMulSq ε (f x) ∂P'| :=
        @dist_triangle8 ℝ _ _ _ _ _ _ _ _ _
  _ ≤ 6 * √ε := by linarith
