/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth, Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Units of a normed algebra

We construct the Lie group structure on the group of units of a complete normed `𝕜`-algebra `R`. The
group of units `Rˣ` has a natural `C^n` manifold structure modelled on `R` given by its embedding
into `R`. Together with the smoothness of the multiplication and inverse of its elements, `Rˣ` forms
a Lie group.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`ContinuousLinearMap.toNormedAlgebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`), as demonstrated by:
```
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance
```

We also prove that if `R` acts smoothly on a manifold, its group of units does as well;
in particular, the general linear group `(V →L[𝕜] V)ˣ` is a Lie group acting smoothly on `V`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace Units

variable {R : Type*} [NormedRing R] [CompleteSpace R] {n : ℕ∞ω}

/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ChartedSpace R Rˣ :=
  isOpenEmbedding_val.singletonChartedSpace
/-
**Units.chartAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl
/-
**Units.chartAt_source** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ :=
  rfl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsManifold 𝓘(𝕜, R) n Rˣ :=
  isOpenEmbedding_val.isManifold_singleton

/-- For a complete normed ring `R`, the embedding of the units `Rˣ` into `R` is a `C^n` map between
manifolds. -/
/-
**Units.contMDiff_val** 是 Mathlib 中的一个引理，位于命名空间 `Units`。
形式化陈述：contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `contMDiff_isOpenEmbedding`：contMDiff_isOpenEmbedding [Nonempty M] : have
I
· 使用定理 `Units.isOpenEmbedding_val`：isOpenEmbedding_val : IsOpenEmbedding (val : 
Rˣ -> R) where toIsEmbedding
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
For a complete normed ring `R`, the embedding of the units `Rˣ` into `R` is a `C
^n` map between
manifolds.
-/
lemma contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ → R) :=
  contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

/-- The units of a complete normed ring form a Lie group. -/
/-
**Units.** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The units of a complete normed ring form a Lie group.
-/
instance : LieGroup 𝓘(𝕜, R) n Rˣ where
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
      (fun x : R × R => x.1 * x.2) ∘ (fun x : Rˣ × Rˣ => (x.1, x.2)) := by ext; simp
    rw [this]
    have : ContMDiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R × R) n
      (fun x : Rˣ × Rˣ => ((x.1 : R), (x.2 : R))) :=
      (contMDiff_val.comp contMDiff_fst).prodMk_space (contMDiff_val.comp contMDiff_snd)
    refine ContMDiff.comp ?_ this
    rw [contMDiff_iff_contDiff]
    exact contDiff_mul
  contMDiff_inv := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ → R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this, ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ringInverse _ _

/-- If a complete normed ring `R` acts continuously differentiably on a manifold `M`, its
submanifold of units does as well. -/
/-
**Units.contMDiffSMul** 是 Mathlib 中的一个实例，位于命名空间 `Units`。
形式化陈述：contMDiffSMul [MulAction R M] [ContMDiffSMul 𝓘(𝕜, R) I n R M] : ContMDiffS
Mul 𝓘(𝕜, R) I n Rˣ M
参数：𝕜, R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.contMDiffSMul_compHom`：MulAction.contMDiffSMul_compHom [Monoid
 G] [MulAction G M] {n : Nat∞ω} [ContMDiffSMul I I' n G M] {G' : Type*} [Topolog
icalSpace G'] [Charte…
· 使用引理 `Units.contMDiff_val`：contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : 
Rˣ -> R)

--- 原说明 ---
If a complete normed ring `R` acts continuously differentiably on a manifold `M`
, its
submanifold of units does as well.
-/
instance contMDiffSMul [MulAction R M] [ContMDiffSMul 𝓘(𝕜, R) I n R M] :
    ContMDiffSMul 𝓘(𝕜, R) I n Rˣ M :=
  MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` is a Lie group. -/
/-
**Units.** 是 Mathlib 中的一个示例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` is a Lie group.
-/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` acts smoothly on `V`. -/
/-
**Units.** 是 Mathlib 中的一个示例，位于命名空间 `Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` acts smoothly on `
V`.
-/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : ℕ∞ω) :
    ContMDiffSMul 𝓘(𝕜, V →L[𝕜] V) 𝓘(𝕜, V) n (V →L[𝕜] V)ˣ V :=
  inferInstance

end Units

