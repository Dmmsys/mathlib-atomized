/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Basic properties of Haar measures on real vector spaces

-/

public section

noncomputable section

open Function Filter Inv MeasureTheory.Measure Module Set TopologicalSpace
open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

/-- The instance `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` applies in particular
to show that an additive Haar measure on a nontrivial finite-dimensional real vector space has no
atom. -/
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个示例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The instance `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` applies
 in particular
to show that an additive Haar measure on a nontrivial finite-dimensional real ve
ctor space has no
atom.
-/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] :
    NullSingletonClass μ := by
  infer_instance

section LinearEquiv

variable {𝕜 G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H]
  [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H] [T2Space H]

/-
**MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.MapLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} {G : Type u_2} {H : Type u_3} [inst : MeasurableSpace G] 
[inst_1 : MeasurableSpace H]   [inst_2 : NontriviallyNormedField 𝕜] [inst_3 : To
pologicalSpace G] [inst_4 : TopologicalSpace H]   [inst_5 : AddCommGroup G] [ins
t_6 : AddCommGroup H] [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]   [ins
t_9 : _root_.Module 𝕜 G] [inst_10 : _root_.Module 𝕜 H] (μ : MeasureTheory.Measur
e G) [μ.IsAddHaarMeasure]   [BorelSpace G] [BorelSpace H] [CompleteSpace 𝕜] [T2S
pace G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]   [ContinuousSMul 𝕜 H] [T2S
pace H] (e : G ≃ₗ[𝕜] H), (MeasureTheory.Measure.map (⇑e) μ).IsAddHaarMeasure
参数：μ : MeasureTheory.Measure G；e : G ≃ₗ[𝕜] H；MeasureTheory.Measure.map (⇑e) μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.isAddHaarMeasure_map`：∀ {E : Type u_3} {F : Type u
_4} {R : Type u_5} {S : Type u_6} [inst : Semiring R] [inst_1 : Semiring S]   [i
nst_2 : AddCommGroup E] [inst_3 …
-/
instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  e.toContinuousLinearEquiv.isAddHaarMeasure_map _

end LinearEquiv

section SeminormedGroup
variable {G H : Type*} [MeasurableSpace G] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G]
  [MeasurableSpace H] [SeminormedGroup H] [OpensMeasurableSpace H]

-- TODO: This could be streamlined by proving that inner regular measures always exist
open Metric Bornology in
@[to_additive]
/-
**MeasureTheory.Measure._root_.MonoidHom.exists_nhds_isBounded** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MonoidHom.exists_nhds_isBounded (f : G →* H) (hf : Measurable f) (x : G) :
    ∃ s ∈ 𝓝 x, IsBounded (f '' s) := by
  let K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < haar (interior K ∩ f ⁻¹' ball 1 n) := by
    by_contra!
    simp_rw [nonpos_iff_eq_zero, ← measure_iUnion_null_iff, ← inter_iUnion, ← preimage_iUnion,
      iUnion_ball_nat, preimage_univ, inter_univ] at this
    exact this.not_gt <| isOpen_interior.measure_pos _ K.interior_nonempty
  rw [← mul_one x, ← smul_eq_mul]
  refine ⟨_, smul_mem_nhds_smul _ <| div_mem_nhds_one_of_haar_pos_ne_top haar _
    (isOpen_interior.measurableSet.inter <| hf measurableSet_ball) hn <|
      mt (measure_mono_top <| inter_subset_left.trans interior_subset) K.isCompact.measure_ne_top,
    ?_⟩
  have : Bornology.IsBounded (f '' (interior K ∩ f ⁻¹' ball 1 n)) :=
    isBounded_ball.subset <| (image_mono inter_subset_right).trans <| image_preimage_subset _ _
  rw [image_smul_distrib, image_div]
  exact (this.div this).smul _

end SeminormedGroup

/-- A Borel-measurable group hom from a locally compact normed group to a real normed space is
continuous. -/
/-
**MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure.AddMonoidHom`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : SeminormedAddCommGroup G] [inst_1 
: MeasurableSpace G] [BorelSpace G]   [LocallyCompactSpace G] [inst_4 : Seminorm
edAddCommGroup H] [inst_5 : MeasurableSpace H] [OpensMeasurableSpace H]   [Norme
dSpace ℝ H] (f : G →+ H), Measurable ⇑f → Continuous ⇑f
参数：f : G →+ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.exists_nhds_isBounded`：∀ {G : Type u_1} {H : Type u_2} [ins
t : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   [Is
TopologicalAddGroup G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `AddMonoidHom.continuous_of_isBounded_nhds_zero`：AddMonoidHom.continuous_
of_isBounded_nhds_zero (f : G ->+ H) (hs : s in 𝓝 (0 : G)) (hbounded : IsBounded
 (f '' s)) : Continuous f

--- 原说明 ---
A Borel-measurable group hom from a locally compact normed group to a real norme
d space is
continuous.
-/
lemma AddMonoidHom.continuous_of_measurable {G H : Type*}
    [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SeminormedAddCommGroup H] [MeasurableSpace H] [OpensMeasurableSpace H] [NormedSpace ℝ H]
    (f : G →+ H) (hf : Measurable f) : Continuous f :=
  let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded hf 0; f.continuous_of_isBounded_nhds_zero hs hbdd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
/-
**MeasureTheory.Measure.integral_comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：integral_comp_smul (f : E -> F) (R : Real) : ∫ x, f (R • x) ∂μ = |(R ^ fin
rank Real E)⁻¹| • ∫ x, f x ∂μ
参数：f : E -> F；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finrank_zero_iff`：Module.finrank_zero_iff [IsDomain R] [IsTorsion
Free R M] : finrank R M = 0 ↔ Subsingleton M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `MeasureTheory.measure_univ_of_isAddLeftInvariant`：∀ {G : Type u_1} [inst
 : MeasurableSpace G] [inst_1 : TopologicalSpace G] [BorelSpace G] [inst_3 : Add
Group G]   [IsTopologicalAddGroup G] […
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `RealNormedSpace.noncompactSpace`：∀ (E : Type u_3) [inst : NormedAddCommG
roup E] [Nontrivial E] [NormedSpace ℝ E], NoncompactSpace E
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
The integral of `f (R • x)` with respect to an additive Haar measure is a multip
le of the
integral of `f`. The formula we give works even when `f` is not integrable or `R
 = 0`
thanks to the convention that a non-integrable function has integral zero.
-/
theorem integral_comp_smul (f : E → F) (R : ℝ) :
    ∫ x, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext x; rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp [zero_pow hE.ne', measure_univ_of_isAddLeftInvariant, measureReal_def]
  · calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂Measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
/-
**MeasureTheory.Measure.integral_comp_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：integral_comp_smul_of_nonneg (f : E -> F) (R : Real) {hR : 0 <= R} : ∫ x, 
f (R • x) ∂μ = (R ^ finrank Real E)⁻¹ • ∫ x, f x ∂μ
参数：f : E -> F；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.integral_comp_smul`：integral_comp_smul (f : E -> F
) (R : Real) : ∫ x, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x, f x ∂μ
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The integral of `f (R • x)` with respect to an additive Haar measure is a multip
le of the
integral of `f`. The formula we give works even when `f` is not integrable or `R
 = 0`
thanks to the convention that a non-integrable function has integral zero.
-/
theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
    ∫ x, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
/-
**MeasureTheory.Measure.integral_comp_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：integral_comp_inv_smul (f : E -> F) (R : Real) : ∫ x, f (R⁻¹ • x) ∂μ = |R 
^ finrank Real E| • ∫ x, f x ∂μ
参数：f : E -> F；R : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.integral_comp_smul`：integral_comp_smul (f : E -> F
) (R : Real) : ∫ x, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x, f x ∂μ
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a mult
iple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R
 = 0`
thanks to the convention that a non-integrable function has integral zero.
-/
theorem integral_comp_inv_smul (f : E → F) (R : ℝ) :
    ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹, inv_pow, inv_inv]

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R = 0`
thanks to the convention that a non-integrable function has integral zero. -/
/-
**MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：integral_comp_inv_smul_of_nonneg (f : E -> F) {R : Real} (hR : 0 <= R) : ∫
 x, f (R⁻¹ • x) ∂μ = R ^ finrank Real E • ∫ x, f x ∂μ
参数：f : E -> F；hR : 0 <= R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.integral_comp_inv_smul`：integral_comp_inv_smul (f 
: E -> F) (R : Real) : ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank Real E| • ∫ x, f x ∂μ
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a mult
iple of the
integral of `f`. The formula we give works even when `f` is not integrable or `R
 = 0`
thanks to the convention that a non-integrable function has integral zero.
-/
theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x, f (R⁻¹ • x) ∂μ = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R, abs_of_nonneg (pow_nonneg hR _)]
/-
**MeasureTheory.Measure.setIntegral_comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：setIntegral_comp_smul (f : E -> F) {R : Real} (s : Set E) (hR : R != 0) : 
∫ x in s, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x in R • s, f x ∂μ
参数：f : E -> F；s : Set E；hR : R != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableEquiv.symm_comp_self`：symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e
 = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_map_equiv`：setIntegral_map_equiv {Y} [Measurab
leSpace Y] (e : X ≃ᵐ Y) (f : Y -> E) (s : Set Y) : ∫ y in s, f y ∂Measure.map e 
μ = ∫ x in e ⁻¹' s, f (e …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.map_addHaar_smul`：map_addHaar_smul {r : Real} (hr 
: r != 0) : Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) 
• μ
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `MeasureTheory.Measure.restrict_smul`：restrict_smul {_m0 : MeasurableSpac
e α} {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (
μ : Measure α) (s : Set α…
· 使用定理 `MeasureTheory.integral_smul_measure`：integral_smul_measure (f : α -> G) 
(c : Real>=0∞) : ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem setIntegral_comp_smul (f : E → F) {R : ℝ} (s : Set E) (hR : R ≠ 0) :
    ∫ x in s, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x in R • s, f x ∂μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv
  calc
  ∫ x in s, f (R • x) ∂μ
    = ∫ x in e ⁻¹' e.symm ⁻¹' s, f (e x) ∂μ := by simp [← preimage_comp]; rfl
  _ = ∫ y in e.symm ⁻¹' s, f y ∂map (fun x ↦ R • x) μ := (setIntegral_map_equiv _ _ _).symm
  _ = |(R ^ finrank ℝ E)⁻¹| • ∫ y in e.symm ⁻¹' s, f y ∂μ := by
    simp [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
  _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x in R • s, f x ∂μ := by
    congr 3
    ext y
    rw [mem_smul_set_iff_inv_smul_mem₀ hR]
    rfl
/-
**MeasureTheory.Measure.setIntegral_comp_smul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：setIntegral_comp_smul_of_pos (f : E -> F) {R : Real} (s : Set E) (hR : 0 <
 R) : ∫ x in s, f (R • x) ∂μ = (R ^ finrank Real E)⁻¹ • ∫ x in R • s, f x ∂μ
参数：f : E -> F；s : Set E；hR : 0 < R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.setIntegral_comp_smul`：setIntegral_comp_smul (f : 
E -> F) {R : Real} (s : Set E) (hR : R != 0) : ∫ x in s, f (R • x) ∂μ = |(R ^ fi
nrank Real E)⁻¹| • ∫ x in R • s, …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem setIntegral_comp_smul_of_pos (f : E → F) {R : ℝ} (s : Set E) (hR : 0 < R) :
    ∫ x in s, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x in R • s, f x ∂μ := by
  rw [setIntegral_comp_smul μ f s hR.ne', abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]
/-
**MeasureTheory.Measure.integral_comp_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：integral_comp_mul_left (g : Real -> F) (a : Real) : (∫ x : Real, g (a * x)
) = |a⁻¹| • ∫ y : Real, g y
参数：g : Real -> F；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.integral_comp_smul`：integral_comp_smul (f : E -> F
) (R : Real) : ∫ x, f (R • x) ∂μ = |(R ^ finrank Real E)⁻¹| • ∫ x, f x ∂μ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_mul_left (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (a * x)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_smul, Module.finrank_self, pow_one]
/-
**MeasureTheory.Measure.integral_comp_inv_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：integral_comp_inv_mul_left (g : Real -> F) (a : Real) : (∫ x : Real, g (a⁻
¹ * x)) = |a| • ∫ y : Real, g y
参数：g : Real -> F；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.integral_comp_inv_smul`：integral_comp_inv_smul (f 
: E -> F) (R : Real) : ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank Real E| • ∫ x, f x ∂μ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_inv_mul_left (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (a⁻¹ * x)) = |a| • ∫ y : ℝ, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, Module.finrank_self, pow_one]
/-
**MeasureTheory.Measure.integral_comp_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：integral_comp_mul_right (g : Real -> F) (a : Real) : (∫ x : Real, g (x * a
)) = |a⁻¹| • ∫ y : Real, g y
参数：g : Real -> F；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.integral_comp_mul_left`：integral_comp_mul_left (g 
: Real -> F) (a : Real) : (∫ x : Real, g (a * x)) = |a⁻¹| • ∫ y : Real, g y
-/
theorem integral_comp_mul_right (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (x * a)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_mul_left g a
/-
**MeasureTheory.Measure.integral_comp_inv_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：integral_comp_inv_mul_right (g : Real -> F) (a : Real) : (∫ x : Real, g (x
 * a⁻¹)) = |a| • ∫ y : Real, g y
参数：g : Real -> F；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.Measure.integral_comp_inv_mul_left`：integral_comp_inv_mul_
left (g : Real -> F) (a : Real) : (∫ x : Real, g (a⁻¹ * x)) = |a| • ∫ y : Real, 
g y
-/
theorem integral_comp_inv_mul_right (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (x * a⁻¹)) = |a| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a
/-
**MeasureTheory.Measure.integral_comp_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：integral_comp_div (g : Real -> F) (a : Real) : (∫ x : Real, g (x / a)) = |
a| • ∫ y : Real, g y
参数：g : Real -> F；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.integral_comp_inv_mul_right`：integral_comp_inv_mul
_right (g : Real -> F) (a : Real) : (∫ x : Real, g (x * a⁻¹)) = |a| • ∫ y : Real
, g y
-/
theorem integral_comp_div (g : ℝ → F) (a : ℝ) : (∫ x : ℝ, g (x / a)) = |a| • ∫ y : ℝ, g y :=
  integral_comp_inv_mul_right g a

end Measure

variable {F : Type*} [NormedAddCommGroup F]

/-
**MeasureTheory.integrable_comp_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace R
eal E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E] (μ : Measur
e E) [IsAddHaarMeasure μ] (f : E -> F) {R : Real} (hR : R != 0) : Integrable (fu
n x => f (R • x)) μ ↔ Integrable f μ
参数：μ : Measure E；f : E -> F；hR : R != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_map_equiv`：integrable_map_equiv (f : α ≃ᵐ δ) (g
 : δ -> ε) : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_addHaar_smul`：map_addHaar_smul {r : Real} (hr 
: r != 0) : Measure.map (r • ·) μ = ENNReal.ofReal (abs (r ^ finrank Real E)⁻¹) 
• μ
· 使用定理 `MeasureTheory.integrable_smul_measure`：integrable_smul_measure {f : α ->
 ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c • μ) ↔ Integrab
le f μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → F) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ ↔ Integrable f μ := by
  -- reduce to one-way implication
  suffices
    ∀ {g : E → F} (_ : Integrable g μ) {S : ℝ} (_ : S ≠ 0), Integrable (fun x => g (S • x)) μ by
    refine ⟨fun hf => ?_, fun hf => this hf hR⟩
    convert! this hf (inv_ne_zero hR)
    rw [← mul_smul, mul_inv_cancel₀ hR, one_smul]
  -- now prove
  intro g hg S hS
  let t := ((Homeomorph.smul (isUnit_iff_ne_zero.2 hS).unit).toMeasurableEquiv : E ≃ᵐ E)
  refine (integrable_map_equiv t g).mp (?_ : Integrable g (map (S • ·) μ))
  rwa [map_addHaar_smul μ hS, integrable_smul_measure _ ENNReal.ofReal_ne_top]
  simpa only [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos] using inv_ne_zero (pow_ne_zero _ hS)
/-
**MeasureTheory.Integrable.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.In
tegrable`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] {E : Type u_2} [inst_1 : No
rmedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [inst_3 : MeasurableSpace E] [B
orelSpace E] [FiniteDimensional ℝ E] {μ : MeasureTheory.Measure E} [μ.IsAddHaarM
easure]   {f : E → F}, MeasureTheory.Integrable f μ → ∀ {R : ℝ}, R ≠ 0 → Measure
Theory.Integrable (fun x => f (R • x)) μ
参数：fun x => f (R • x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_comp_smul_iff`：integrable_comp_smul_iff {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace
 E] [FiniteDimensional Real …
-/
theorem Integrable.comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f : E → F} (hf : Integrable f μ) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ :=
  (integrable_comp_smul_iff μ f hR).2 hf
/-
**MeasureTheory.integrable_comp_mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integrable_comp_mul_left_iff (g : Real -> F) {R : Real} (hR : R != 0) : (I
ntegrable fun x => g (R * x)) ↔ Integrable g
参数：g : Real -> F；hR : R != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_comp_smul_iff`：integrable_comp_smul_iff {E : Ty
pe*} [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace
 E] [FiniteDimensional Real …
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
-/
theorem integrable_comp_mul_left_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (R * x)) ↔ Integrable g := by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR
/-
**MeasureTheory.Integrable.comp_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Integrable`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] {g : ℝ → F},   MeasureTheor
y.Integrable g MeasureTheory.volume →     ∀ {R : ℝ}, R ≠ 0 → MeasureTheory.Integ
rable (fun x => g (R * x)) MeasureTheory.volume
参数：fun x => g (R * x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_comp_mul_left_iff`：integrable_comp_mul_left_iff
 (g : Real -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (R * x)) ↔ In
tegrable g
-/
theorem Integrable.comp_mul_left' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (R * x) :=
  (integrable_comp_mul_left_iff g hR).2 hg
/-
**MeasureTheory.integrable_comp_mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integrable_comp_mul_right_iff (g : Real -> F) {R : Real} (hR : R != 0) : (
Integrable fun x => g (x * R)) ↔ Integrable g
参数：g : Real -> F；hR : R != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.integrable_comp_mul_left_iff`：integrable_comp_mul_left_iff
 (g : Real -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (R * x)) ↔ In
tegrable g
-/
theorem integrable_comp_mul_right_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (x * R)) ↔ Integrable g := by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR
/-
**MeasureTheory.Integrable.comp_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] {g : ℝ → F},   MeasureTheor
y.Integrable g MeasureTheory.volume →     ∀ {R : ℝ}, R ≠ 0 → MeasureTheory.Integ
rable (fun x => g (x * R)) MeasureTheory.volume
参数：fun x => g (x * R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_comp_mul_right_iff`：integrable_comp_mul_right_i
ff (g : Real -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (x * R)) ↔ 
Integrable g
-/
theorem Integrable.comp_mul_right' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x * R) :=
  (integrable_comp_mul_right_iff g hR).2 hg
/-
**MeasureTheory.integrable_comp_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integrable_comp_div_iff (g : Real -> F) {R : Real} (hR : R != 0) : (Integr
able fun x => g (x / R)) ↔ Integrable g
参数：g : Real -> F；hR : R != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_comp_mul_right_iff`：integrable_comp_mul_right_i
ff (g : Real -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (x * R)) ↔ 
Integrable g
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem integrable_comp_div_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (x / R)) ↔ Integrable g :=
  integrable_comp_mul_right_iff g (inv_ne_zero hR)
/-
**MeasureTheory.Integrable.comp_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Int
egrable`。
形式化陈述：∀ {F : Type u_1} [inst : NormedAddCommGroup F] {g : ℝ → F},   MeasureTheor
y.Integrable g MeasureTheory.volume →     ∀ {R : ℝ}, R ≠ 0 → MeasureTheory.Integ
rable (fun x => g (x / R)) MeasureTheory.volume
参数：fun x => g (x / R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_comp_div_iff`：integrable_comp_div_iff (g : Real
 -> F) {R : Real} (hR : R != 0) : (Integrable fun x => g (x / R)) ↔ Integrable g
-/
theorem Integrable.comp_div {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x / R) :=
  (integrable_comp_div_iff g hR).2 hg

section InnerProductSpace

variable {E' F' A : Type*}
variable [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  [MeasurableSpace F'] [BorelSpace F']

variable (f : E' ≃ₗᵢ[ℝ] F')
variable [NormedAddCommGroup A]

/-
**MeasureTheory.integrable_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integrable_comp (g : F' -> A) : Integrable (g ∘ f) ↔ Integrable g
参数：g : F' -> A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integrable_comp_emb`：∀ {α : Type u_1} {δ
 : Type u_4} {ε : Type u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   [inst : MeasurableSpace δ] [inst_1 : …
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem integrable_comp (g : F' → A) : Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasurableEquiv.measurableEmbedding
/-
**MeasureTheory.integral_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_comp [NormedSpace Real A] (g : F' -> A) : ∫ (x : E'), g (f x) = ∫
 (y : F'), g y
参数：g : F' -> A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp'`：∀ {α : Type u_1} {G : Ty
pe u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : Measurable
Space α}   {μ : MeasureTheory.Measur…
· 使用定理 `LinearIsometryEquiv.measurePreserving`：measurePreserving (f : E ≃ₗᵢ[Real
] F) : MeasurePreserving f
-/
theorem integral_comp [NormedSpace ℝ A] (g : F' → A) : ∫ (x : E'), g (f x) = ∫ (y : F'), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasurableEquiv) g

end InnerProductSpace

end MeasureTheory

