/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.Measure.PreVariation

/-!
# Total variation for vector-valued measures

This file contains the definition of variation for any `VectorMeasure` in an `ENormedAddCommMonoid`,
in particular, any `NormedAddCommGroup`.

Given a vector-valued measure `μ` we consider the problem of finding a countably additive function
`f` such that, for any set `E`, `‖μ(E)‖ ≤ f(E)`. This suggests defining `f(E)` as the supremum over
partitions `{Eᵢ}` of `E`, of the quantity `∑ᵢ, ‖μ(Eᵢ)‖`. Indeed any solution of the problem must be
not less than this function. It turns out that this function is a measure.

## Main definitions

* `VectorMeasure.variation`: the variation as a `Measure X`
* `VectorMeasure.ennrealVariation`: the variation as a `VectorMeasure X ℝ≥0∞`

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} {mX : MeasurableSpace X}

open scoped ENNReal

namespace MeasureTheory.VectorMeasure

variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

/-- The norm of a vector measure is σ-subadditive on measurable sets. -/
/-
**MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiv
eSetFun (‖μ ·‖ₑ)
参数：μ : VectorMeasure X V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `enorm_tsum_le_tsum_enorm`：enorm_tsum_le_tsum_enorm {f : ι -> ε} : ‖∑' i,
 f i‖ₑ <= ∑' i, ‖f i‖ₑ

--- 原说明 ---
The norm of a vector measure is σ-subadditive on measurable sets.
-/
lemma isSigmaSubadditiveSetFun_enorm (μ : VectorMeasure X V) :
    IsSigmaSubadditiveSetFun (‖μ ·‖ₑ) := by
  intro s hs
  have hmeas : ∀ i, MeasurableSet (s i).val := fun i => (s i).prop
  simpa [VectorMeasure.of_disjoint_iUnion hmeas hs] using enorm_tsum_le_tsum_enorm

/-- The variation of a `VectorMeasure` as a `Measure`. -/
/-
**MeasureTheory.VectorMeasure.variation** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.VectorMeasure`。
形式化陈述：variation (μ : VectorMeasure X V) : Measure X
参数：μ : VectorMeasure X V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.isSigmaSubadditiveSetFun_enorm`：isSigmaSubad
ditiveSetFun_enorm (μ : VectorMeasure X V) : IsSigmaSubadditiveSetFun (‖μ ·‖ₑ)

--- 原说明 ---
The variation of a `VectorMeasure` as a `Measure`.
-/
noncomputable def variation (μ : VectorMeasure X V) : Measure X :=
  preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp)

/-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
/-
**MeasureTheory.VectorMeasure.ennrealVariation** 是 Mathlib 中的一个定义，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X Real>=0∞
参数：μ : VectorMeasure X V。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`.
-/
noncomputable def ennrealVariation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ :=
  μ.variation.toENNRealVectorMeasure

end MeasureTheory.VectorMeasure

