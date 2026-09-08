/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Conditional expectation in L2

This file contains one step of the construction of the conditional expectation, which is completed
in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

We build the conditional expectation of an `L²` function, as an element of `L²`. This is the
orthogonal projection on the subspace of almost everywhere `m`-measurable functions.

## Main definitions

* `condExpL2`: Conditional expectation of a function in L2 with respect to a sigma-algebra: it is
  the orthogonal projection on the subspace `lpMeas`.

## Implementation notes

Most of the results in this file are valid for a complete real normed space `F`.
However, some lemmas also use `𝕜 : RCLike`:
* `condExpL2` is defined only for an `InnerProductSpace` for now, and we use `𝕜` for its field.
* results about scalar multiplication are stated not only for `ℝ` but also for `𝕜` if we happen to
  have `NormedSpace 𝕜 F`.

-/

@[expose] public section


open TopologicalSpace Filter ContinuousLinearMap

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α E E' F G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- E for an inner product space
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
  -- E' for an inner product space on which we compute integrals
  [NormedAddCommGroup E']
  [InnerProductSpace 𝕜 E'] [CompleteSpace E'] [NormedSpace ℝ E']
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (E 𝕜)

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
/-
**MeasureTheory.condExpL2** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL2 (hm : m <= m0) : (α ->₂[μ] E) ->L[𝕜] lpMeas E 𝕜 m 2 μ
参数：hm : m <= m0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Conditional expectation of a function in L2 with respect to a sigma-algebra
-/
noncomputable def condExpL2 (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] lpMeas E 𝕜 m 2 μ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  (lpMeas E 𝕜 m 2 μ).orthogonalProjectionOnto

variable {E 𝕜}
/-
**MeasureTheory.aestronglyMeasurable_condExpL2** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：aestronglyMeasurable_condExpL2 (hm : m <= m0) (f : α ->₂[μ] E) : AEStrongl
yMeasurable[m] (condExpL2 E 𝕜 hm f : α -> E) μ
参数：hm : m <= m0；f : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.lpMeas.aestronglyMeasurable`：∀ {α : Type u_1} {F : Type u_
2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 F] …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem aestronglyMeasurable_condExpL2 (hm : m ≤ m0) (f : α →₂[μ] E) :
    AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm f : α → E) μ :=
  lpMeas.aestronglyMeasurable _
/-
**MeasureTheory.integrableOn_condExpL2_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：integrableOn_condExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (
f : α ->₂[μ] E) : IntegrableOn (ε
参数：hm : m <= m0；hμs : μ s != ∞；f : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.integrableOn_Lp_of_measure_ne_top`：integrableOn_Lp_of_meas
ure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α} (f : Lp E p μ) 
(hp : 1 <= p) (hμs : μ s != ∞) : Inte…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
-/
theorem integrableOn_condExpL2_of_measure_ne_top (hm : m ≤ m0) (hμs : μ s ≠ ∞) (f : α →₂[μ] E) :
    IntegrableOn (ε := E) (condExpL2 E 𝕜 hm f) s μ :=
  integrableOn_Lp_of_measure_ne_top (condExpL2 E 𝕜 hm f : α →₂[μ] E) fact_one_le_two_ennreal.elim
    hμs
/-
**MeasureTheory.integrable_condExpL2_of_isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：integrable_condExpL2_of_isFiniteMeasure (hm : m <= m0) [IsFiniteMeasure μ]
 {f : α ->₂[μ] E} : Integrable (ε
参数：hm : m <= m0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `MeasureTheory.integrableOn_condExpL2_of_measure_ne_top`：integrableOn_con
dExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) : Inte
grableOn (ε
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem integrable_condExpL2_of_isFiniteMeasure (hm : m ≤ m0) [IsFiniteMeasure μ] {f : α →₂[μ] E} :
    Integrable (ε := E) (condExpL2 E 𝕜 hm f) μ :=
  integrableOn_univ.mp <| integrableOn_condExpL2_of_measure_ne_top hm (measure_ne_top _ _) f
/-
**MeasureTheory.norm_condExpL2_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_condExpL2_le_one (hm : m <= m0) : ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖
 <= 1
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.orthogonalProjectionOnto_norm_le`：orthogonalProjectionOnto_nor
m_le : ‖K.orthogonalProjectionOnto‖ <= 1
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem norm_condExpL2_le_one (hm : m ≤ m0) : ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ ≤ 1 :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  Submodule.orthogonalProjectionOnto_norm_le _
/-
**MeasureTheory.norm_condExpL2_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_condExpL2_le (hm : m <= m0) (f : α ->₂[μ] E) : ‖condExpL2 E 𝕜 hm f‖ <
= ‖f‖
参数：hm : m <= m0；f : α ->₂[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.norm_condExpL2_le_one`：norm_condExpL2_le_one (hm : m <= m0
) : ‖@condExpL2 α E 𝕜 _ _ _ _ _ _ μ hm‖ <= 1
-/
theorem norm_condExpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) : ‖condExpL2 E 𝕜 hm f‖ ≤ ‖f‖ :=
  ((@condExpL2 _ E 𝕜 _ _ _ _ _ _ μ hm).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_condExpL2_le_one hm))
/-
**MeasureTheory.eLpNorm_condExpL2_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：eLpNorm_condExpL2_le (hm : m <= m0) (f : α ->₂[μ] E) : eLpNorm (ε
参数：hm : m <= m0；f : α ->₂[μ] E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `Submodule.norm_coe`：norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module
 𝕜 E] {s : Submodule 𝕜 E} (x : s) : ‖(x : E)‖ = ‖x‖
· 使用定理 `MeasureTheory.norm_condExpL2_le`：norm_condExpL2_le (hm : m <= m0) (f : α
 ->₂[μ] E) : ‖condExpL2 E 𝕜 hm f‖ <= ‖f‖
-/
theorem eLpNorm_condExpL2_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    eLpNorm (ε := E) (condExpL2 E 𝕜 hm f) 2 μ ≤ eLpNorm f 2 μ := by
  rw [← ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _), ←
    Lp.norm_def, ← Lp.norm_def, Submodule.norm_coe]
  exact norm_condExpL2_le hm f
/-
**MeasureTheory.norm_condExpL2_coe_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：norm_condExpL2_coe_le (hm : m <= m0) (f : α ->₂[μ] E) : ‖(condExpL2 E 𝕜 hm
 f : α ->₂[μ] E)‖ <= ‖f‖
参数：hm : m <= m0；f : α ->₂[μ] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.eLpNorm_condExpL2_le`：eLpNorm_condExpL2_le (hm : m <= m0) 
(f : α ->₂[μ] E) : eLpNorm (ε
-/
theorem norm_condExpL2_coe_le (hm : m ≤ m0) (f : α →₂[μ] E) :
    ‖(condExpL2 E 𝕜 hm f : α →₂[μ] E)‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_condExpL2_le hm f)
/-
**MeasureTheory.inner_condExpL2_left_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：inner_condExpL2_left_eq_right (hm : m <= m0) {f g : α ->₂[μ] E} : ⟪(condEx
pL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = ⟪f, (condExpL2 E 𝕜 hm g : α ->₂[μ] E)⟫
参数：hm : m <= m0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.inner_starProjection_left_eq_right`：inner_starProjection_left_
eq_right [K.HasOrthogonalProjection] (u v : E) : ⟪K.starProjection u, v⟫ = ⟪u, K
.starProjection v⟫
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `MeasureTheory.instCompleteSpaceSubtypeAEEqFunMemAddSubgroupLpSubmoduleLp
MeasOfFactLeMeasurableSpace`：∀ {α : Type u_1} {F : Type u_2} {𝕜 : Type u_3} {p :
 ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSp
ace 𝕜 F] …
-/
theorem inner_condExpL2_left_eq_right (hm : m ≤ m0) {f g : α →₂[μ] E} :
    ⟪(condExpL2 E 𝕜 hm f : α →₂[μ] E), g⟫ = ⟪f, (condExpL2 E 𝕜 hm g : α →₂[μ] E)⟫ :=
  haveI : Fact (m ≤ m0) := ⟨hm⟩
  Submodule.inner_starProjection_left_eq_right _ f g
/-
**MeasureTheory.condExpL2_indicator_of_measurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：condExpL2_indicator_of_measurable (hm : m <= m0) (hs : MeasurableSet[m] s)
 (hμs : μ s != ∞) (c : E) : (condExpL2 E 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs 
c) : α ->₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c
参数：hm : m <= m0；hs : MeasurableSet[m] s；hμs : μ s != ∞；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpL2.eq_1`：∀ {α : Type u_1} (E : Type u_2) (𝕜 : Type 
u_7) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `MeasureTheory.mem_lpMeas_indicatorConstLp`：mem_lpMeas_indicatorConstLp {
m m0 : MeasurableSpace α} (hm : m <= m0) {μ : Measure α} {s : Set α} (hs : Measu
rableSet[m] s) (hμs : μ s != ∞)…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `MeasureTheory.instCompleteSpaceSubtypeAEEqFunMemAddSubgroupLpSubmoduleLp
MeasOfFactLeMeasurableSpace`：∀ {α : Type u_1} {F : Type u_2} {𝕜 : Type u_3} {p :
 ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSp
ace 𝕜 F] …
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem condExpL2_indicator_of_measurable (hm : m ≤ m0) (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞)
    (c : E) :
    (condExpL2 E 𝕜 hm (indicatorConstLp 2 (hm s hs) hμs c) : α →₂[μ] E) =
      indicatorConstLp 2 (hm s hs) hμs c := by
  rw [condExpL2]
  have : Fact (m ≤ m0) := ⟨hm⟩
  have h_mem : indicatorConstLp 2 (hm s hs) hμs c ∈ lpMeas E 𝕜 m 2 μ :=
    mem_lpMeas_indicatorConstLp hm hs hμs
  let ind := (⟨indicatorConstLp 2 (hm s hs) hμs c, h_mem⟩ : lpMeas E 𝕜 m 2 μ)
  have h_coe_ind : (ind : α →₂[μ] E) = indicatorConstLp 2 (hm s hs) hμs c := rfl
  have h_orth_mem := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ind
  rw [← h_coe_ind, h_orth_mem]
/-
**MeasureTheory.inner_condExpL2_eq_inner_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：inner_condExpL2_eq_inner_fun (hm : m <= m0) (f g : α ->₂[μ] E) (hg : AEStr
onglyMeasurable[m] g μ) : ⟪(condExpL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = ⟪f, g⟫
参数：hm : m <= m0；f g : α ->₂[μ] E；hg : AEStronglyMeasurable[m] g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
· 使用定理 `MeasureTheory.condExpL2.eq_1`：∀ {α : Type u_1} (E : Type u_2) (𝕜 : Type 
u_7) [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.starProjection_inner_eq_zero`：starProjection_inner_eq_zero (v 
w : E) (hw : w in K) : ⟪v - K.starProjection v, w⟫ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable`：mem_lpMeas_iff_aestro
nglyMeasurable {m m0 : MeasurableSpace α} {μ : Measure α} {f : Lp F p μ} : f in 
lpMeas F 𝕜 m p μ ↔ AEStronglyMeasurable…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_condExpL2_eq_inner_fun (hm : m ≤ m0) (f g : α →₂[μ] E)
    (hg : AEStronglyMeasurable[m] g μ) :
    ⟪(condExpL2 E 𝕜 hm f : α →₂[μ] E), g⟫ = ⟪f, g⟫ := by
  symm
  rw [← sub_eq_zero, ← inner_sub_left, condExpL2]
  simp only [← Submodule.starProjection_apply,
    mem_lpMeas_iff_aestronglyMeasurable.mpr hg,
    Submodule.starProjection_inner_eq_zero f g]

section Real

variable {hm : m ≤ m0}

/-
**MeasureTheory.integral_condExpL2_eq_of_fin_meas_real** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：integral_condExpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[
m] s) (hμs : μ s != ∞) : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x ∂μ = ∫ x in s
, f x ∂μ
参数：f : Lp 𝕜 2 μ；hs : MeasurableSet[m] s；hμs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L2.inner_indicatorConstLp_one`：inner_indicatorConstLp_one 
(hs : MeasurableSet s) (hμs : μ s != ∞) (f : Lp 𝕜 2 μ) : ⟪indicatorConstLp 2 hs 
hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂…
· 使用定理 `MeasureTheory.inner_condExpL2_left_eq_right`：inner_condExpL2_left_eq_rig
ht (hm : m <= m0) {f g : α ->₂[μ] E} : ⟪(condExpL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = 
⟪f, (condExpL2 E 𝕜 hm g : α ->₂[μ…
· 使用定理 `MeasureTheory.condExpL2_indicator_of_measurable`：condExpL2_indicator_of_
measurable (hm : m <= m0) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : E) : (
condExpL2 E 𝕜 hm (indicatorConstLp 2 …
-/
theorem integral_condExpL2_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← L2.inner_indicatorConstLp_one (𝕜 := 𝕜) (hm s hs) hμs f]
  have h_eq_inner : ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α → 𝕜) x ∂μ =
      ⟪indicatorConstLp 2 (hm s hs) hμs (1 : 𝕜), condExpL2 𝕜 𝕜 hm f⟫ := by
    rw [L2.inner_indicatorConstLp_one (hm s hs) hμs]
  rw [h_eq_inner, ← inner_condExpL2_left_eq_right, condExpL2_indicator_of_measurable hm hs hμs]
/-
**MeasureTheory.lintegral_nnnorm_condExpL2_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：lintegral_nnnorm_condExpL2_le (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (
f : Lp Real 2 μ) : ∫⁻ x in s, ‖(condExpL2 Real Real hm f : α -> Real) x‖₊ ∂μ <= 
∫⁻ x in s, ‖f x‖₊ ∂μ
参数：hs : MeasurableSet[m] s；hμs : μ s != ∞；f : Lp Real 2 μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.lpMeas.aestronglyMeasurable`：∀ {α : Type u_1} {F : Type u_
2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 F] …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_enorm_le_of_forall_fin_meas_integral_eq`：lintegr
al_enorm_le_of_forall_fin_meas_integral_eq (hm : m <= m0) {f g : α -> Real} (hf 
: StronglyMeasurable f) (hfi : IntegrableOn f s μ) (h…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `MeasureTheory.integrableOn_Lp_of_measure_ne_top`：integrableOn_Lp_of_meas
ure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α} (f : Lp E p μ) 
(hp : 1 <= p) (hμs : μ s != ∞) : Inte…
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.integrableOn_condExpL2_of_measure_ne_top`：integrableOn_con
dExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) : Inte
grableOn (ε
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_condExpL2_eq_of_fin_meas_real`：integral_condExpL2
_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) :
 ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
-/
theorem lintegral_nnnorm_condExpL2_le (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
    ∫⁻ x in s, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ ≤ ∫⁻ x in s, ‖f x‖₊ ∂μ := by
  let h_meas := lpMeas.aestronglyMeasurable (condExpL2 ℝ ℝ hm f)
  let g := h_meas.choose
  have hg_meas : StronglyMeasurable[m] g := h_meas.choose_spec.1
  have hg_eq : g =ᵐ[μ] condExpL2 ℝ ℝ hm f := h_meas.choose_spec.2.symm
  have hg_eq_restrict : g =ᵐ[μ.restrict s] condExpL2 ℝ ℝ hm f := ae_restrict_of_ae hg_eq
  have hg_nnnorm_eq : (fun x => (‖g x‖₊ : ℝ≥0∞)) =ᵐ[μ.restrict s] fun x =>
      (‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ : ℝ≥0∞) := by
    refine hg_eq_restrict.mono fun x hx => ?_
    dsimp only
    simp_rw [hx]
  rw [lintegral_congr_ae hg_nnnorm_eq.symm]
  refine lintegral_enorm_le_of_forall_fin_meas_integral_eq
    hm (Lp.stronglyMeasurable f) ?_ ?_ ?_ ?_ hs hμs
  · exact integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs
  · exact hg_meas
  · rw [IntegrableOn, integrable_congr hg_eq_restrict]
    exact integrableOn_condExpL2_of_measure_ne_top hm hμs f
  · intro t ht hμt
    rw [← integral_condExpL2_eq_of_fin_meas_real (hm := hm) f ht hμt.ne]
    exact setIntegral_congr_ae (hm t ht) (hg_eq.mono fun x hx _ => hx)
/-
**MeasureTheory.condExpL2_ae_eq_zero_of_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：condExpL2_ae_eq_zero_of_ae_eq_zero (hs : MeasurableSet[m] s) (hμs : μ s !=
 ∞) {f : Lp Real 2 μ} (hf : f =ᵐ[μ.restrict s] 0) : condExpL2 Real Real hm f =ᵐ[
μ.restrict s] (0 : α -> Real)
参数：hs : MeasurableSet[m] s；hμs : μ s != ∞；hf : f =ᵐ[μ.restrict s] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.lintegral_nnnorm_condExpL2_le`：lintegral_nnnorm_condExpL2_
le (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (f : Lp Real 2 μ) : ∫⁻ x in s, ‖(c
ondExpL2 Real Real hm f : α -> Re…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Measurable.coe_nnreal_ennreal`：Measurable.coe_nnreal_ennreal {f : α -> R
eal>=0} (hf : Measurable f) : Measurable fun x => (f x : Real>=0∞)
· 使用定理 `Measurable.nnnorm`：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpa
ce α] [inst_1 : NormedAddCommGroup α] [OpensMeasurableSpace α]   [inst_3 : Measu
rableSp…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `nnnorm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖₊
 = 0 ↔ a = 0
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
-/
theorem condExpL2_ae_eq_zero_of_ae_eq_zero (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞) {f : Lp ℝ 2 μ}
    (hf : f =ᵐ[μ.restrict s] 0) : condExpL2 ℝ ℝ hm f =ᵐ[μ.restrict s] (0 : α → ℝ) := by
  suffices h_nnnorm_eq_zero : ∫⁻ x in s, ‖(condExpL2 ℝ ℝ hm f : α → ℝ) x‖₊ ∂μ = 0 by
    rw [lintegral_eq_zero_iff] at h_nnnorm_eq_zero
    · refine h_nnnorm_eq_zero.mono fun x hx => ?_
      dsimp only at hx
      rw [Pi.zero_apply] at hx ⊢
      · rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    · refine Measurable.coe_nnreal_ennreal (Measurable.nnnorm ?_)
      exact (Lp.stronglyMeasurable _).measurable
  rw [← nonpos_iff_eq_zero]
  refine (lintegral_nnnorm_condExpL2_le hs hμs f).trans (le_of_eq ?_)
  rw [lintegral_eq_zero_iff]
  · refine hf.mono fun x hx => ?_
    dsimp only
    rw [hx]
    simp
  · exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)
/-
**MeasureTheory.lintegral_nnnorm_condExpL2_indicator_le_real** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_nnnorm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs :
 μ s != ∞) (ht : MeasurableSet[m] t) (hμt : μ t != ∞) : ∫⁻ a in t, ‖(condExpL2 R
eal Real hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a‖₊ ∂μ <= μ (s inter t)
参数：hs : MeasurableSet s；hμs : μ s != ∞；ht : MeasurableSet[m] t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.lintegral_nnnorm_condExpL2_le`：lintegral_nnnorm_condExpL2_
le (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (f : Lp Real 2 μ) : ∫⁻ x in s, ‖(c
ondExpL2 Real Real hm f : α -> Re…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem lintegral_nnnorm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ ≤ μ (s ∩ t) := by
  refine (lintegral_nnnorm_condExpL2_le ht hμt _).trans (le_of_eq ?_)
  have h_eq :
    ∫⁻ x in t, ‖(indicatorConstLp 2 hs hμs (1 : ℝ)) x‖₊ ∂μ =
      ∫⁻ x in t, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    refine (@indicatorConstLp_coeFn _ _ _ 2 _ _ _ hs hμs (1 : ℝ)).mono fun x hx => ?_
    dsimp only
    rw [hx]
    classical
    simp_rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [h_eq, lintegral_indicator hs, lintegral_const, Measure.restrict_restrict hs]
  simp only [one_mul, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]

end Real

/-- `condExpL2` commutes with taking inner products with constants. See the lemma
`condExpL2_comp_continuousLinearMap` for a more general result about commuting with continuous
linear maps. -/
/-
**MeasureTheory.condExpL2_const_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpL2_const_inner (hm : m <= m0) (f : Lp E 2 μ) (c : E) : condExpL2 𝕜 
𝕜 hm (((Lp.memLp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ] fun a => ⟪c, (c
ondExpL2 E 𝕜 hm f : α -> E) a⟫
参数：hm : m <= m0；f : Lp E 2 μ；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.MemLp.const_inner`：∀ {α : Type u_1} {m : MeasurableSpace α
} {p : ENNReal} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3}   [i
nst : RCLike 𝕜] [inst…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `MeasureTheory.Lp.ae_eq_of_forall_setIntegral_eq'`：∀ {α : Type u_1} {E' :
 Type u_2} (𝕜 : Type u_4) {p : ENNReal} {m m0 : MeasurableSpace α} {μ : MeasureT
heory.Measure α}   [inst : RCLike 𝕜] […
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.integrableOn_condExpL2_of_measure_ne_top`：integrableOn_con
dExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) : Inte
grableOn (ε
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Integrable.const_inner`：∀ {α : Type u_1} {m : MeasurableSp
ace α} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3} [inst : RCLik
e 𝕜]   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.integral_condExpL2_eq_of_fin_meas_real`：integral_condExpL2
_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) :
 ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x…
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.L2.inner_indicatorConstLp_eq_setIntegral_inner`：inner_indi
catorConstLp_eq_setIntegral_inner (f : Lp E 2 μ) (hs : MeasurableSet s) (c : E) 
(hμs : μ s != ∞) : (⟪indicatorConstLp 2 hs hμs c, …
· 使用定理 `MeasureTheory.inner_condExpL2_left_eq_right`：inner_condExpL2_left_eq_rig
ht (hm : m <= m0) {f g : α ->₂[μ] E} : ⟪(condExpL2 E 𝕜 hm f : α ->₂[μ] E), g⟫ = 
⟪f, (condExpL2 E 𝕜 hm g : α ->₂[μ…
· 使用定理 `MeasureTheory.condExpL2_indicator_of_measurable`：condExpL2_indicator_of_
measurable (hm : m <= m0) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) (c : E) : (
condExpL2 E 𝕜 hm (indicatorConstLp 2 …
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.lpMeas.aestronglyMeasurable`：∀ {α : Type u_1} {F : Type u_
2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 F] …
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
`condExpL2` commutes with taking inner products with constants. See the lemma
`condExpL2_comp_continuousLinearMap` for a more general result about commuting w
ith continuous
linear maps.
-/
theorem condExpL2_const_inner (hm : m ≤ m0) (f : Lp E 2 μ) (c : E) :
    condExpL2 𝕜 𝕜 hm (((Lp.memLp f).const_inner c).toLp fun a => ⟪c, f a⟫) =ᵐ[μ]
    fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫ := by
  have h_mem_Lp : MemLp (fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫) 2 μ := by
    refine MemLp.const_inner _ ?_; exact Lp.memLp _
  have h_eq : h_mem_Lp.toLp _ =ᵐ[μ] fun a => ⟪c, (condExpL2 E 𝕜 hm f : α → E) a⟫ :=
    h_mem_Lp.coeFn_toLp
  refine EventuallyEq.trans ?_ h_eq
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜 hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) ?_ ?_ ?_ ?_
  · intro s _ hμs
    rw [IntegrableOn, integrable_congr (ae_restrict_of_ae h_eq)]
    exact (integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _).const_inner _
  · intro s hs hμs
    rw [integral_condExpL2_eq_of_fin_meas_real _ hs hμs.ne,
      integral_congr_ae (ae_restrict_of_ae h_eq), ←
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 (↑(condExpL2 E 𝕜 hm f)) (hm s hs) c hμs.ne,
      ← inner_condExpL2_left_eq_right, condExpL2_indicator_of_measurable _ hs,
      L2.inner_indicatorConstLp_eq_setIntegral_inner 𝕜 f (hm s hs) c hμs.ne,
      setIntegral_congr_ae (hm s hs)
        ((MemLp.coeFn_toLp ((Lp.memLp f).const_inner c)).mono fun x hx _ => hx)]
  · exact lpMeas.aestronglyMeasurable _
  · refine AEStronglyMeasurable.congr ?_ h_eq.symm
    exact (lpMeas.aestronglyMeasurable _).const_inner

/-- `condExpL2` verifies the equality of integrals defining the conditional expectation. -/
/-
**MeasureTheory.integral_condExpL2_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_condExpL2_eq (hm : m <= m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m
] s) (hμs : μ s != ∞) : ∫ x in s, (condExpL2 E' 𝕜 hm f : α -> E') x ∂μ = ∫ x in 
s, f x ∂μ
参数：hm : m <= m0；f : Lp E' 2 μ；hs : MeasurableSet[m] s；hμs : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integrableOn_Lp_of_measure_ne_top`：integrableOn_Lp_of_meas
ure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α} (f : Lp E p μ) 
(hp : 1 <= p) (hμs : μ s != ∞) : Inte…
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `integral_eq_zero_of_forall_integral_inner_eq_zero`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {E : Type u_2} (𝕜 : Type u_3) 
[inst : RCLike 𝕜]   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Lp.coeFn_sub`：coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] 
f - g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.const_inner`：∀ {α : Type u_1} {m : MeasurableSp
ace α} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3} [inst : RCLik
e 𝕜]   [inst_1 : NormedAdd…
· 使用定理 `MeasureTheory.MemLp.const_inner`：∀ {α : Type u_1} {m : MeasurableSpace α
} {p : ENNReal} {μ : MeasureTheory.Measure α} {E : Type u_2} {𝕜 : Type u_3}   [i
nst : RCLike 𝕜] [inst…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.condExpL2_const_inner`：condExpL2_const_inner (hm : m <= m0
) (f : Lp E 2 μ) (c : E) : condExpL2 𝕜 𝕜 hm (((Lp.memLp f).const_inner c).toLp f
un a => ⟪c, f a⟫) =ᵐ[μ] f…
· 使用定理 `MeasureTheory.integral_condExpL2_eq_of_fin_meas_real`：integral_condExpL2
_eq_of_fin_meas_real (f : Lp 𝕜 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) :
 ∫ x in s, (condExpL2 𝕜 𝕜 hm f : α -> 𝕜) x…

--- 原说明 ---
`condExpL2` verifies the equality of integrals defining the conditional expectat
ion.
-/
theorem integral_condExpL2_eq (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) : ∫ x in s, (condExpL2 E' 𝕜 hm f : α → E') x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← sub_eq_zero, ←
    integral_sub' (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)
      (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs)]
  refine integral_eq_zero_of_forall_integral_inner_eq_zero 𝕜 _ ?_ ?_
  · rw [integrable_congr (ae_restrict_of_ae (Lp.coeFn_sub (↑(condExpL2 E' 𝕜 hm f)) f).symm)]
    exact integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs
  intro c
  simp_rw [Pi.sub_apply, inner_sub_right]
  rw [integral_sub
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)
      ((integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs).const_inner c)]
  have h_ae_eq_f := MemLp.coeFn_toLp (E := 𝕜) ((Lp.memLp f).const_inner c)
  rw [sub_eq_zero, ←
    setIntegral_congr_ae (hm s hs) ((condExpL2_const_inner hm f c).mono fun x hx _ => hx), ←
    setIntegral_congr_ae (hm s hs) (h_ae_eq_f.mono fun x hx _ => hx)]
  exact integral_condExpL2_eq_of_fin_meas_real _ hs hμs

variable {E'' 𝕜' : Type*} [RCLike 𝕜'] [NormedAddCommGroup E''] [InnerProductSpace 𝕜' E'']
  [CompleteSpace E''] [NormedSpace ℝ E'']

variable (𝕜 𝕜')
/-
**MeasureTheory.condExpL2_comp_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：condExpL2_comp_continuousLinearMap (hm : m <= m0) (T : E' ->L[Real] E'') (
f : α ->₂[μ] E') : (condExpL2 E'' 𝕜' hm (T.compLp f) : α ->₂[μ] E'') =ᵐ[μ] T.com
pLp (condExpL2 E' 𝕜 hm f : α ->₂[μ] E')
参数：hm : m <= m0；T : E' ->L[Real] E''；f : α ->₂[μ] E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Lp.ae_eq_of_forall_setIntegral_eq'`：∀ {α : Type u_1} {E' :
 Type u_2} (𝕜 : Type u_4) {p : ENNReal} {m m0 : MeasurableSpace α} {μ : MeasureT
heory.Measure α}   [inst : RCLike 𝕜] […
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `MeasureTheory.integrableOn_condExpL2_of_measure_ne_top`：integrableOn_con
dExpL2_of_measure_ne_top (hm : m <= m0) (hμs : μ s != ∞) (f : α ->₂[μ] E) : Inte
grableOn (ε
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.integrableOn_Lp_of_measure_ne_top`：integrableOn_Lp_of_meas
ure_ne_top {E} [NormedAddCommGroup E] {p : Real>=0∞} {s : Set α} (f : Lp E p μ) 
(hp : 1 <= p) (hμs : μ s != ∞) : Inte…
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.setIntegral_compLp`：setIntegral_compLp (L : E ->SL[σ
] F) (φ : Lp E p μ) {s : Set X} (hs : MeasurableSet s) : ∫ x in s, (L.compLp φ) 
x ∂μ = ∫ x in s, L (φ x) ∂μ
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `MeasureTheory.integral_condExpL2_eq`：integral_condExpL2_eq (hm : m <= m0
) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) : ∫ x in s, (condEx
pL2 E' 𝕜 hm f : α -> E') …
· 使用定理 `MeasureTheory.lpMeas.aestronglyMeasurable`：∀ {α : Type u_1} {F : Type u_
2} {𝕜 : Type u_3} {p : ENNReal} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup F
]   [inst_2 : NormedSpace 𝕜 F] …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
-/
theorem condExpL2_comp_continuousLinearMap (hm : m ≤ m0) (T : E' →L[ℝ] E'') (f : α →₂[μ] E') :
    (condExpL2 E'' 𝕜' hm (T.compLp f) : α →₂[μ] E'') =ᵐ[μ]
    T.compLp (condExpL2 E' 𝕜 hm f : α →₂[μ] E') := by
  refine Lp.ae_eq_of_forall_setIntegral_eq' 𝕜' hm _ _ two_ne_zero ENNReal.coe_ne_top
    (fun s _ hμs => integrableOn_condExpL2_of_measure_ne_top hm hμs.ne _) (fun s _ hμs =>
      integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne) ?_ ?_ ?_
  · intro s hs hμs
    rw [T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hμs.ne),
      integral_condExpL2_eq hm f hs hμs.ne,
      integral_condExpL2_eq hm (T.compLp f) hs hμs.ne, T.setIntegral_compLp _ (hm s hs),
      T.integral_comp_comm
        (integrableOn_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs.ne)]
  · exact lpMeas.aestronglyMeasurable _
  · have h_coe := T.coeFn_compLp (condExpL2 E' 𝕜 hm f : α →₂[μ] E')
    rw [← EventuallyEq] at h_coe
    refine AEStronglyMeasurable.congr ?_ h_coe.symm
    exact T.continuous.comp_aestronglyMeasurable (lpMeas.aestronglyMeasurable (condExpL2 E' 𝕜 hm f))

variable {𝕜 𝕜'}

section CondexpL2Indicator

variable (𝕜)

/-
**MeasureTheory.condExpL2_indicator_ae_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：condExpL2_indicator_ae_eq_smul (hm : m <= m0) (hs : MeasurableSet s) (hμs 
: μ s != ∞) (x : E') : condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun
 a => (condExpL2 Real Real hm (indicatorConstLp 2 hs hμs (1 : Real)) : α -> Real
) a • x
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.indicatorConstLp_eq_toSpanSingleton_compLp`：indicatorConst
Lp_eq_toSpanSingleton_compLp {s : Set α} [NormedSpace Real E] (hs : MeasurableSe
t s) (hμs : μ s != ∞) (x : E) : indicatorConst…
· 使用定理 `MeasureTheory.condExpL2_comp_continuousLinearMap`：condExpL2_comp_continu
ousLinearMap (hm : m <= m0) (T : E' ->L[Real] E'') (f : α ->₂[μ] E') : (condExpL
2 E'' 𝕜' hm (T.compLp f) : α ->₂[μ] E'…
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
-/
theorem condExpL2_indicator_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') :
    condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) =ᵐ[μ] fun a =>
      (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)) : α → ℝ) a • x := by
  rw [indicatorConstLp_eq_toSpanSingleton_compLp hs hμs x]
  have h_comp :=
    condExpL2_comp_continuousLinearMap ℝ 𝕜 hm (toSpanSingleton ℝ x)
      (indicatorConstLp 2 hs hμs (1 : ℝ))
  refine h_comp.trans ?_
  exact (toSpanSingleton ℝ x).coeFn_compLp _
/-
**MeasureTheory.condExpL2_indicator_eq_toSpanSingleton_comp** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：condExpL2_indicator_eq_toSpanSingleton_comp (hm : m <= m0) (hs : Measurabl
eSet s) (hμs : μ s != ∞) (x : E') : (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμ
s x) : α ->₂[μ] E') = (toSpanSingleton Real x).compLp (condExpL2 Real Real hm (i
ndicatorConstLp 2 hs hμs 1))
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpL2_indicator_ae_eq_smul`：condExpL2_indicator_ae_eq_
smul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E') : condExpL2
 E' 𝕜 hm (indicatorConstLp 2 hs hμ…
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
-/
theorem condExpL2_indicator_eq_toSpanSingleton_comp (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') : (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α →₂[μ] E') =
    (toSpanSingleton ℝ x).compLp (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1)) := by
  ext1
  refine (condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).trans ?_
  have h_comp := (toSpanSingleton ℝ x).coeFn_compLp
    (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α →₂[μ] ℝ)
  rw [← EventuallyEq] at h_comp
  refine EventuallyEq.trans ?_ h_comp.symm
  filter_upwards with y using rfl

variable {𝕜}
/-
**MeasureTheory.setLIntegral_nnnorm_condExpL2_indicator_le** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_nnnorm_condExpL2_indicator_le (hm : m <= m0) (hs : Measurable
Set s) (hμs : μ s != ∞) (x : E') {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ 
t != ∞) : ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α -> E'
) a‖₊ ∂μ <= μ (s inter t) * ‖x‖₊
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : E'；ht : MeasurableSet[m]
 t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpL2_indicator_ae_eq_smul`：condExpL2_indicator_ae_eq_
smul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : E') : condExpL2
 E' 𝕜 hm (indicatorConstLp 2 hs hμ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.lintegral_mul_const`：lintegral_mul_const (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.lintegral_nnnorm_condExpL2_indicator_le_real`：lintegral_nn
norm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s != ∞) (ht : M
easurableSet[m] t) (hμt : μ t != ∞) : ∫⁻ a in t,…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem setLIntegral_nnnorm_condExpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : E') {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤
    μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpL2_indicator_ae_eq_smul 𝕜 hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)
    _ ≤ μ (s ∩ t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]
/-
**MeasureTheory.lintegral_nnnorm_condExpL2_indicator_le** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：lintegral_nnnorm_condExpL2_indicator_le (hm : m <= m0) (hs : MeasurableSet
 s) (hμs : μ s != ∞) (x : E') [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖(condExpL2 E' 𝕜
 hm (indicatorConstLp 2 hs hμs x) : α -> E') a‖₊ ∂μ <= μ s * ‖x‖₊
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : E'；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_le_of_forall_fin_meas_trim_le`：lintegral_le_of_f
orall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] 
(C : Real>=0∞) {f : α -> Real>=0∞} (hf : fo…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_nnnorm_condExpL2_indicator_le`：setLIntegral_n
nnorm_condExpL2_indicator_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s !=
 ∞) (x : E') {t : Set α} (ht : MeasurableSet[m…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_nnnorm_condExpL2_indicator_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : E') [SigmaFinite (μ.trim hm)] :
    ∫⁻ a, ‖(condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x) : α → E') a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
/-
**MeasureTheory.integrable_condExpL2_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：integrable_condExpL2_indicator (hm : m <= m0) [SigmaFinite (μ.trim hm)] (h
s : MeasurableSet s) (hμs : μ s != ∞) (x : E') : Integrable (ε
参数：hm : m <= m0；μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_of_forall_fin_meas_le'`：integrable_of_forall_fi
n_meas_le' {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] (C : Real>=0
∞) (hC : C < ∞) {f : α -> ε} (hf_meas…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_nnnorm_condExpL2_indicator_le`：setLIntegral_n
nnorm_condExpL2_indicator_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s !=
 ∞) (x : E') {t : Set α} (ht : MeasurableSet[m…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of 
a measurable set
with finite measure is integrable.
-/
theorem integrable_condExpL2_indicator (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E') :
    Integrable (ε := E') (condExpL2 E' 𝕜 hm (indicatorConstLp 2 hs hμs x)) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt =>
      (setLIntegral_nnnorm_condExpL2_indicator_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left

end CondexpL2Indicator

section CondexpIndSMul

variable [NormedSpace ℝ G] {hm : m ≤ m0}

/-- Conditional expectation of the indicator of a measurable set with finite measure, in L2. -/
/-
**MeasureTheory.condExpIndSMul** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndSMul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x :
 G) : Lp G 2 μ
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Conditional expectation of the indicator of a measurable set with finite measure
, in L2.
-/
noncomputable def condExpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    Lp G 2 μ :=
  (toSpanSingleton ℝ x).compLpL 2 μ (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs (1 : ℝ)))
/-
**MeasureTheory.aestronglyMeasurable_condExpIndSMul** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：aestronglyMeasurable_condExpIndSMul (hm : m <= m0) (hs : MeasurableSet s) 
(hμs : μ s != ∞) (x : G) : AEStronglyMeasurable[m] (condExpIndSMul hm hs hμs x) 
μ
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL2`：aestronglyMeasurable_condE
xpL2 (hm : m <= m0) (f : α ->₂[μ] E) : AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm
 f : α -> E) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul.eq_1`：∀ {α : Type u_1} {G : Type u_5} [inst
 : NormedAddCommGroup G] {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   {s : Set α} [inst_1…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.congr`：congr (hf : AEStronglyMeasurab
le[m] f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable[m] g μ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ContinuousLinearMap.coeFn_compLpL`：coeFn_compLpL [Fact (1 <= p)] (L : E 
->SL[σ] F) (f : Lp E p μ) : L.compLpL p μ f =ᵐ[μ] fun a => L (f a)
-/
theorem aestronglyMeasurable_condExpIndSMul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : AEStronglyMeasurable[m] (condExpIndSMul hm hs hμs x) μ := by
  have h : AEStronglyMeasurable[m] (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aestronglyMeasurable_condExpL2 _ _
  rw [condExpIndSMul]
  exact ((toSpanSingleton ℝ x).continuous.comp_aestronglyMeasurable h).congr
    (coeFn_compLpL _ _).symm
/-
**MeasureTheory.condExpIndSMul_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndSMul_add (hs : MeasurableSet s) (hμs : μ s != ∞) (x y : G) : con
dExpIndSMul hm hs hμs (x + y) = condExpIndSMul hm hs hμs x + condExpIndSMul hm h
s hμs y
参数：hs : MeasurableSet s；hμs : μ s != ∞；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.toSpanSingleton_add`：toSpanSingleton_add [Continuous
Add M₁] (x y : M₁) : toSpanSingleton R₁ (x + y) = toSpanSingleton R₁ x + toSpanS
ingleton R₁ y
· 使用定理 `ContinuousLinearMap.add_compLpL`：add_compLpL [Fact (1 <= p)] (L L' : E -
>SL[σ] F) : (L + L').compLpL p μ = L.compLpL p μ + L'.compLpL p μ
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
-/
theorem condExpIndSMul_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndSMul hm hs hμs (x + y) = condExpIndSMul hm hs hμs x + condExpIndSMul hm hs hμs y := by
  simp_rw [condExpIndSMul]; rw [toSpanSingleton_add, add_compLpL, add_apply]
/-
**MeasureTheory.condExpIndSMul_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndSMul_smul [NormedSpace Real F] [SMulCommClass Real 𝕜 F] (hs : Me
asurableSet s) (hμs : μ s != ∞) (c : 𝕜) (x : F) : condExpIndSMul hm hs hμs (c • 
x) = c • condExpIndSMul hm hs hμs x
参数：hs : MeasurableSet s；hμs : μ s != ∞；c : 𝕜；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.compLpL.congr_simp`：∀ {α : Type u_1} {E : Type u_4} 
{F : Type u_5} {m : MeasurableSpace α} (p : ENNReal) (μ : MeasureTheory.Measure 
α)   [inst : NormedAddCommGr…
· 使用定理 `ContinuousLinearMap.toSpanSingleton_smul`：toSpanSingleton_smul {α} [Mono
id α] [DistribMulAction α M₁] [ContinuousConstSMul α M₁] [SMulCommClass R₁ α M₁]
 (c : α) (x : M₁) : toSpanSing…
· 使用定理 `ContinuousLinearMap.smul_compLpL`：smul_compLpL [Fact (1 <= p)] {𝕜''} [No
rmedRing 𝕜''] [Module 𝕜'' F] [IsBoundedSMul 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F] (c :
 𝕜'') (L : E ->SL[σ] F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condExpIndSMul_smul [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndSMul hm hs hμs (c • x) = c • condExpIndSMul hm hs hμs x := by
  simp_rw [condExpIndSMul, toSpanSingleton_smul, smul_compLpL, smul_apply]
/-
**MeasureTheory.condExpIndSMul_ae_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：condExpIndSMul_ae_eq_smul (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s
 != ∞) (x : G) : condExpIndSMul hm hs hμs x =ᵐ[μ] fun a => (condExpL2 Real Real 
hm (indicatorConstLp 2 hs hμs 1) : α -> Real) a • x
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.coeFn_compLpL`：coeFn_compLpL [Fact (1 <= p)] (L : E 
->SL[σ] F) (f : Lp E p μ) : L.compLpL p μ f =ᵐ[μ] fun a => L (f a)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
theorem condExpIndSMul_ae_eq_smul (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndSMul hm hs hμs x =ᵐ[μ] fun a =>
      (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x :=
  (toSpanSingleton ℝ x).coeFn_compLpL _
/-
**MeasureTheory.setLIntegral_nnnorm_condExpIndSMul_le** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：setLIntegral_nnnorm_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s
) (hμs : μ s != ∞) (x : G) {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t != ∞
) : (∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ) <= μ (s inter t) * ‖x‖₊
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : G；ht : MeasurableSet[m] 
t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.setLIntegral_congr_fun_ae`：setLIntegral_congr_fun_ae {f g 
: α -> Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : forallᵐ x ∂μ, x in s 
-> f x = g x) : ∫⁻ x in s, f …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpIndSMul_ae_eq_smul`：condExpIndSMul_ae_eq_smul (hm :
 m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpIndSMul hm hs
 hμs x =ᵐ[μ] fun a => (condEx…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.lintegral_mul_const`：lintegral_mul_const (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a * r ∂μ = (∫⁻ a, f a ∂μ) * r
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.Lp.stronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {m 
: MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Norme
dAddCommGroup E] (f : ↥(M…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.lintegral_nnnorm_condExpL2_indicator_le_real`：lintegral_nn
norm_condExpL2_indicator_le_real (hs : MeasurableSet s) (hμs : μ s != ∞) (ht : M
easurableSet[m] t) (hμt : μ t != ∞) : ∫⁻ a in t,…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem setLIntegral_nnnorm_condExpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) {t : Set α} (ht : MeasurableSet[m] t) (hμt : μ t ≠ ∞) :
    (∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ) ≤ μ (s ∩ t) * ‖x‖₊ :=
  calc
    ∫⁻ a in t, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ =
        ∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a • x‖₊ ∂μ :=
      setLIntegral_congr_fun_ae (hm t ht)
        ((condExpIndSMul_ae_eq_smul hm hs hμs x).mono fun a ha _ => by rw [ha])
    _ = (∫⁻ a in t, ‖(condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) a‖₊ ∂μ) * ‖x‖₊ := by
      simp_rw [nnnorm_smul, ENNReal.coe_mul]
      rw [lintegral_mul_const]
      exact (Lp.stronglyMeasurable _).enorm (ε := ℝ)
    _ ≤ μ (s ∩ t) * ‖x‖₊ := by grw [lintegral_nnnorm_condExpL2_indicator_le_real hs hμs ht hμt]
/-
**MeasureTheory.lintegral_nnnorm_condExpIndSMul_le** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：lintegral_nnnorm_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (
hμs : μ s != ∞) (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condExpIndSMul hm hs 
hμs x a‖₊ ∂μ <= μ s * ‖x‖₊
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；x : G；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_le_of_forall_fin_meas_trim_le`：lintegral_le_of_f
orall_fin_meas_trim_le {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] 
(C : Real>=0∞) {f : α -> Real>=0∞} (hf : fo…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_nnnorm_condExpIndSMul_le`：setLIntegral_nnnorm
_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G
) {t : Set α} (ht : MeasurableSet[m] t) (…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_nnnorm_condExpIndSMul_le (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) [SigmaFinite (μ.trim hm)] : ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖₊ ∂μ ≤ μ s * ‖x‖₊ := by
  refine lintegral_le_of_forall_fin_meas_trim_le hm (μ s * ‖x‖₊) fun t ht hμt => ?_
  refine (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
  gcongr
  apply Set.inter_subset_left

/-- If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of a measurable set
with finite measure is integrable. -/
/-
**MeasureTheory.integrable_condExpIndSMul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integrable_condExpIndSMul (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : M
easurableSet s) (hμs : μ s != ∞) (x : G) : Integrable (condExpIndSMul hm hs hμs 
x) μ
参数：hm : m <= m0；μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_of_forall_fin_meas_le'`：integrable_of_forall_fi
n_meas_le' {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)] (C : Real>=0
∞) (hC : C < ∞) {f : α -> ε} (hf_meas…
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.Lp.aestronglyMeasurable`：∀ {α : Type u_1} {E : Type u_4} {
m : MeasurableSpace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : Nor
medAddCommGroup E] (f : ↥(M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.setLIntegral_nnnorm_condExpIndSMul_le`：setLIntegral_nnnorm
_condExpIndSMul_le (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G
) {t : Set α} (ht : MeasurableSet[m] t) (…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If the measure `μ.trim hm` is sigma-finite, then the conditional expectation of 
a measurable set
with finite measure is integrable.
-/
theorem integrable_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (x : G) : Integrable (condExpIndSMul hm hs hμs x) μ := by
  refine integrable_of_forall_fin_meas_le' hm (μ s * ‖x‖₊)
    (ENNReal.mul_lt_top hμs.lt_top ENNReal.coe_lt_top) ?_ ?_
  · exact Lp.aestronglyMeasurable _
  · refine fun t ht hμt => (setLIntegral_nnnorm_condExpIndSMul_le hm hs hμs x ht hμt).trans ?_
    gcongr
    apply Set.inter_subset_left
/-
**MeasureTheory.condExpIndSMul_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndSMul_empty {x : G} : condExpIndSMul hm MeasurableSet.empty ((mea
sure_empty (μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.condExpIndSMul.eq_1`：∀ {α : Type u_1} {G : Type u_5} [inst
 : NormedAddCommGroup G] {m m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α
}   {s : Set α} [inst_1…
· 使用定理 `MeasureTheory.indicatorConstLp_empty`：indicatorConstLp_empty : indicator
ConstLp p MeasurableSet.empty (by simp : μ ∅ != ∞) c = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem condExpIndSMul_empty {x : G} : condExpIndSMul hm MeasurableSet.empty
    ((measure_empty (μ := μ)).le.trans_lt ENNReal.coe_lt_top).ne x = 0 := by
  rw [condExpIndSMul, indicatorConstLp_empty]
  simp only [Submodule.coe_zero, map_zero]
/-
**MeasureTheory.setIntegral_condExpL2_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：setIntegral_condExpL2_indicator (hs : MeasurableSet[m] s) (ht : Measurable
Set t) (hμs : μ s != ∞) (hμt : μ t != ∞) : ∫ x in s, (condExpL2 Real Real hm (in
dicatorConstLp 2 ht hμt 1) : α -> Real) x ∂μ = μ.real (t inter s)
参数：hs : MeasurableSet[m] s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.integral_condExpL2_eq`：integral_condExpL2_eq (hm : m <= m0
) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s) (hμs : μ s != ∞) : ∫ x in s, (condEx
pL2 E' 𝕜 hm f : α -> E') …
· 使用定理 `MeasureTheory.setIntegral_indicatorConstLp`：setIntegral_indicatorConstLp
 [CompleteSpace E] {p : Real>=0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hμt : μ t != ∞) (e : E) : ∫ x i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem setIntegral_condExpL2_indicator (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    ∫ x in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ = μ.real (t ∩ s) :=
  calc
    ∫ x in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) x ∂μ =
        ∫ x in s, indicatorConstLp 2 ht hμt (1 : ℝ) x ∂μ :=
      @integral_condExpL2_eq α _ ℝ _ _ _ _ _ _ _ _ _ hm (indicatorConstLp 2 ht hμt (1 : ℝ)) hs hμs
    _ = μ.real (t ∩ s) • (1 : ℝ) := setIntegral_indicatorConstLp (hm s hs) ht hμt 1
    _ = μ.real (t ∩ s) := by rw [smul_eq_mul, mul_one]
/-
**MeasureTheory.setIntegral_condExpIndSMul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setIntegral_condExpIndSMul (hs : MeasurableSet[m] s) (ht : MeasurableSet t
) (hμs : μ s != ∞) (hμt : μ t != ∞) (x : G') : ∫ a in s, (condExpIndSMul hm ht h
μt x) a ∂μ = μ.real (t inter s) • x
参数：hs : MeasurableSet[m] s；ht : MeasurableSet t；hμs : μ s != ∞；hμt : μ t != ∞；x 
: G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.condExpIndSMul_ae_eq_smul`：condExpIndSMul_ae_eq_smul (hm :
 m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpIndSMul hm hs
 hμs x =ᵐ[μ] fun a => (condEx…
· 使用定理 `integral_smul_const`：integral_smul_const {𝕜 : Type*} [RCLike 𝕜] [NormedS
pace 𝕜 E] [CompleteSpace E] (f : X -> 𝕜) (c : E) : ∫ x, f x • c ∂μ = (∫ x, f x ∂
μ) • c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_condExpL2_indicator`：setIntegral_condExpL2_ind
icator (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : 
μ t != ∞) : ∫ x in s, (condExpL2 Re…
-/
theorem setIntegral_condExpIndSMul (hs : MeasurableSet[m] s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (x : G') :
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ = μ.real (t ∩ s) • x :=
  calc
    ∫ a in s, (condExpIndSMul hm ht hμt x) a ∂μ =
        ∫ a in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a • x ∂μ :=
      setIntegral_congr_ae (hm s hs)
        ((condExpIndSMul_ae_eq_smul hm ht hμt x).mono fun _ hx _ => hx)
    _ = (∫ a in s, (condExpL2 ℝ ℝ hm (indicatorConstLp 2 ht hμt 1) : α → ℝ) a ∂μ) • x :=
      (integral_smul_const _ x)
    _ = μ.real (t ∩ s) • x := by rw [setIntegral_condExpL2_indicator hs ht hμs hμt]
/-
**MeasureTheory.condExpL2_indicator_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：condExpL2_indicator_nonneg (hm : m <= m0) (hs : MeasurableSet s) (hμs : μ 
s != ∞) [SigmaFinite (μ.trim hm)] : (0 : α -> Real) <=ᵐ[μ] condExpL2 Real Real h
m (indicatorConstLp 2 hs hμs 1)
参数：hm : m <= m0；hs : MeasurableSet s；hμs : μ s != ∞；μ.trim hm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `MeasureTheory.aestronglyMeasurable_condExpL2`：aestronglyMeasurable_condE
xpL2 (hm : m <= m0) (f : α ->₂[μ] E) : AEStronglyMeasurable[m] (condExpL2 E 𝕜 hm
 f : α -> E) μ
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_le_of_ae_le_trim`：ae_le_of_ae_le_trim {E} [LE E] {hm : 
m <= m0} {f₁ f₂ : α -> E} (h12 : f₁ <=ᵐ[μ.trim hm] f₂) : f₁ <=ᵐ[μ] f₂
· 使用定理 `MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite`：ae_
nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α -> Rea
l} (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ …
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.integrable_condExpL2_indicator`：integrable_condExpL2_indic
ator (hm : m <= m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s 
!= ∞) (x : E') : Integrable (ε
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_trim`：setIntegral_trim {X} {m m0 : MeasurableS
pace X} {μ : Measure X} (hm : m <= m0) {f : X -> E} (hf_meas : StronglyMeasurabl
e[m] f) {s : Set X} …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `MeasureTheory.setIntegral_condExpL2_indicator`：setIntegral_condExpL2_ind
icator (hs : MeasurableSet[m] s) (ht : MeasurableSet t) (hμs : μ s != ∞) (hμt : 
μ t != ∞) : ∫ x in s, (condExpL2 Re…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.le_trim`：le_trim (hm : m <= m0) : μ s <= μ.trim hm s
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
-/
theorem condExpL2_indicator_nonneg (hm : m ≤ m0) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    [SigmaFinite (μ.trim hm)] : (0 : α → ℝ) ≤ᵐ[μ]
    condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) := by
  have h : AEStronglyMeasurable[m] (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) μ :=
    aestronglyMeasurable_condExpL2 _ _
  refine EventuallyLE.trans_eq ?_ h.ae_eq_mk.symm
  refine @ae_le_of_ae_le_trim _ _ _ _ _ _ hm (0 : α → ℝ) _ ?_
  refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
  · rintro t - -
    refine @Integrable.integrableOn _ _ m _ _ _ _ _ ?_
    refine Integrable.trim hm ?_ h.stronglyMeasurable_mk
    rw [integrable_congr h.ae_eq_mk.symm]
    exact integrable_condExpL2_indicator hm hs hμs _
  · intro t ht hμt
    rw [← setIntegral_trim hm h.stronglyMeasurable_mk ht]
    have h_ae :
        ∀ᵐ x ∂μ, x ∈ t → h.mk _ x = (condExpL2 ℝ ℝ hm (indicatorConstLp 2 hs hμs 1) : α → ℝ) x := by
      filter_upwards [h.ae_eq_mk] with x hx using fun _ => hx.symm
    rw [setIntegral_congr_ae (hm t ht) h_ae,
      setIntegral_condExpL2_indicator ht hs ((le_trim hm).trans_lt hμt).ne hμs]
    exact ENNReal.toReal_nonneg
/-
**MeasureTheory.condExpIndSMul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：condExpIndSMul_nonneg {E} [NormedAddCommGroup E] [PartialOrder E] [NormedS
pace Real E] [IsOrderedModule Real E] [SigmaFinite (μ.trim hm)] (hs : Measurable
Set s) (hμs : μ s != ∞) (x : E) (hx : 0 <= x) : (0 : α -> E) <=ᵐ[μ] condExpIndSM
ul hm hs hμs x
参数：μ.trim hm；hs : MeasurableSet s；hμs : μ s != ∞；x : E；hx : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.condExpL2_indicator_nonneg`：condExpL2_indicator_nonneg (hm
 : m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) [SigmaFinite (μ.trim hm)] : 
(0 : α -> Real) <=ᵐ[μ] condExp…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.condExpIndSMul_ae_eq_smul`：condExpIndSMul_ae_eq_smul (hm :
 m <= m0) (hs : MeasurableSet s) (hμs : μ s != ∞) (x : G) : condExpIndSMul hm hs
 hμs x =ᵐ[μ] fun a => (condEx…
-/
theorem condExpIndSMul_nonneg {E}
    [NormedAddCommGroup E] [PartialOrder E] [NormedSpace ℝ E] [IsOrderedModule ℝ E]
    [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    (0 : α → E) ≤ᵐ[μ] condExpIndSMul hm hs hμs x := by
  refine EventuallyLE.trans_eq ?_ (condExpIndSMul_ae_eq_smul hm hs hμs x).symm
  filter_upwards [condExpL2_indicator_nonneg hm hs hμs] with a ha
  exact smul_nonneg ha hx

end CondexpIndSMul

end MeasureTheory

