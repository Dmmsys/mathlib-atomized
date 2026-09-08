/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Notation

/-!
# `C^n` structures

In this file we define `C^n` structures that build on Lie groups. We prefer using the
term `ContMDiffRing` instead of Lie mainly because Lie ring has currently another use
in mathematics.
-/

public section

open scoped Manifold ContDiff

section ContMDiffRing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ∞ω}

-- See note [Design choices about smooth algebraic structures]
/-- A `C^n` (semi)ring is a (semi)ring `R` where addition and multiplication are `C^n`.
If `R` is a ring, then negation is automatically `C^n`, as it is multiplication with `-1`. -/
/-
**ContMDiffRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {H : Type u_2}
 →       [inst_1 : TopologicalSpace H] →         {E : Type u_3} →           [ins
t_2 : NormedAddCommGroup E] →             [inst_3 : NormedSpace 𝕜 E] →          
     ModelWithCorners 𝕜 E H →                 WithTop ℕ∞ → (R : Type u_4) → [Sem
iring R] → [inst : TopologicalSpace R] → [ChartedSpace H R] → Prop
参数：R : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `C^n` (semi)ring is a (semi)ring `R` where addition and multiplication are `C^
n`.
If `R` is a ring, then negation is automatically `C^n`, as it is multiplication 
with `-1`.
-/
class ContMDiffRing (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
    (R : Type*) [Semiring R] [TopologicalSpace R] [ChartedSpace H R] : Prop
    extends ContMDiffAdd I n R where
  contMDiff_mul : CMDiff n fun p : R × R => p.1 * p.2

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ContMDiffRing.toContMDiffMul (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Semiring R] [TopologicalSpace R] [ChartedSpace H R] [h : ContMDiffRing I n R] :
    ContMDiffMul I n R :=
  { h with }

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ContMDiffRing.toLieAddGroup (I : ModelWithCorners 𝕜 E H) (R : Type*)
    [Ring R] [TopologicalSpace R] [ChartedSpace H R] [ContMDiffRing I n R] : LieAddGroup I n R where
  compatible := StructureGroupoid.compatible (contDiffGroupoid n I)
  contMDiff_add := contMDiff_add I n
  contMDiff_neg := by simpa only [neg_one_mul] using contMDiff_mul_left (G := R) (a := -1)

end ContMDiffRing

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instFieldContMDiffRing
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} :
    ContMDiffRing 𝓘(𝕜) n 𝕜 :=
  { instNormedSpaceLieAddGroup with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps, chartAt_self_eq]
      rw [contDiffOn_univ]
      exact contDiff_mul }

variable {𝕜 R E H : Type*} [TopologicalSpace R] [TopologicalSpace H] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ChartedSpace H R] (I : ModelWithCorners 𝕜 E H)
  (n : ℕ∞ω)

/-- A `C^n` (semi)ring is a topological (semi)ring. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
/-
**topologicalSemiring_of_contMDiffRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：topologicalSemiring_of_contMDiffRing [Semiring R] [ContMDiffRing I n R] : 
IsTopologicalSemiring R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousMul_of_contMDiffMul`：continuousMul_of_contMDiffMul [ContMDiffM
ul I n G] : ContinuousMul G
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `continuousAdd_of_contMDiffAdd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2
 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffAdd`：∀ {𝕜 : Type u_1} {inst : NontriviallyNorme
dField 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 
: NormedAddCommGro…

--- 原说明 ---
A `C^n` (semi)ring is a topological (semi)ring. This is not an instance for tech
nical reasons,
see note [Design choices about smooth algebraic structures].
-/
theorem topologicalSemiring_of_contMDiffRing [Semiring R] [ContMDiffRing I n R] :
    IsTopologicalSemiring R :=
  { continuousMul_of_contMDiffMul I n, continuousAdd_of_contMDiffAdd I n with }
