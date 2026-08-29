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

An important special case of this construction is the general linear group. For a normed space `V`
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

variable {R : Type*} [NormedRing R] [CompleteSpace R] {n : Nat∞ω}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChartedSpace R Rˣ
  body: isOpenEmbedding_val.singletonChartedSpace

中文:
实例 :
  签名: Charted空间 R Rˣ
  定义体: isOpenEmbedding_val.singletonChartedSpace

Depends on / 依赖: isOpenEmbedding_val, isOpenEmbedding_val.singletonChartedSpace, singletonChartedSpace
-/
instance : ChartedSpace R Rˣ :=
  isOpenEmbedding_val.singletonChartedSpace

/--
theorem `chartAt_apply` / 定理 `chartAt_apply`

English:
theorem chartAt_apply
  given: {a : Rˣ} {b : Rˣ}
  statement: chartAt R a b = b
  proof: rfl

中文:
定理 chartAt_apply
  条件: {a : Rˣ} {b : Rˣ}
  结论: chartAt R a b = b
  证明: rfl
-/
theorem chartAt_apply {a : Rˣ} {b : Rˣ} : chartAt R a b = b :=
  rfl

/--
theorem `chartAt_source` / 定理 `chartAt_source`

English:
theorem chartAt_source
  given: {a : Rˣ}
  statement: (chartAt R a).source = Set.univ
  proof: rfl

中文:
定理 chartAt_source
  条件: {a : Rˣ}
  结论: (chartAt R a).source = 集合.univ
  证明: rfl
-/
theorem chartAt_source {a : Rˣ} : (chartAt R a).source = Set.univ :=
  rfl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsManifold 𝓘(𝕜, R) n Rˣ
  body: isOpenEmbedding_val.isManifold_singleton

中文:
实例 :
  签名: 是流形 𝓘(𝕜, R) n Rˣ
  定义体: isOpenEmbedding_val.isManifold_singleton

Depends on / 依赖: isManifold_singleton, isOpenEmbedding_val, isOpenEmbedding_val.isManifold_singleton
-/
instance : IsManifold 𝓘(𝕜, R) n Rˣ :=
  isOpenEmbedding_val.isManifold_singleton

/--
lemma `contMDiff_val` / 引理 `contMDiff_val`

English:
lemma contMDiff_val
  statement: ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ -> R)
  proof: contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

中文:
引理 contMDiff_val
  结论: ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ -> R)
  证明: contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

Depends on / 依赖: Units.isOpenEmbedding_val, contMDiff_isOpenEmbedding, isOpenEmbedding_val
-/
lemma contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ -> R) :=
  contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieGroup 𝓘(𝕜, R) n Rˣ
  body: by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
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
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this]; rw [ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ringInverse _ _

中文:
实例 :
  签名: Lie群 𝓘(𝕜, R) n Rˣ
  定义体: by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
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
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this]; rw [ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ringInverse _ _

Depends on / 依赖: ContMDiff, ContMDiff.comp, ContMDiff.of_comp_isOpenEmbedding, Units.isOpenEmbedding_val, contDiff_mul, contMDiff_fst, contMDiff_iff_contDiff, contMDiff_inv, contMDiff_snd, contMDiff_val, contMDiff_val.comp, finsuppTensorFinsuppLid_apply_apply, isOpenEmbedding_val, of_comp_isOpenEmbedding, prodMk_space
-/
instance : LieGroup 𝓘(𝕜, R) n Rˣ where
  contMDiff_mul := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ × Rˣ => x.1 * x.2) =
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
    have : (val : Rˣ -> R) ∘ (fun x : Rˣ => x⁻¹) = Ring.inverse ∘ val := by ext; simp
    rw [this]; rw [ContMDiff]
    refine fun x => ContMDiffAt.comp x ?_ (contMDiff_val x)
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_ringInverse _ _

/--
Instance `contMDiffSMul` / 实例 `contMDiffSMul`

English:
instance contMDiffSMul
  signature: [MulAction R M] [ContMDiffSMul 𝓘(𝕜, R) I n R M]
  body: MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

中文:
实例 contMDiffSMul
  签名: [乘法作用 R M] [余ntMDiffSMul 𝓘(𝕜, R) I n R M]
  定义体: MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

Depends on / 依赖: MulAction, MulAction.contMDiffSMul_compHom, coeHom, contMDiffSMul_compHom, contMDiff_val, finsuppTensorFinsuppLid_single_tmul_single
-/
instance contMDiffSMul [MulAction R M] [ContMDiffSMul 𝓘(𝕜, R) I n R M] :
    ContMDiffSMul 𝓘(𝕜, R) I n Rˣ M :=
  MulAction.contMDiffSMul_compHom (f := coeHom R) contMDiff_val

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` is a Lie group. -/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : Nat∞ω) :
    LieGroup 𝓘(𝕜, V ->L[𝕜] V) n (V ->L[𝕜] V)ˣ := inferInstance

/-- The general linear group `(V →L[𝕜] V)ˣ` of a Banach space `V` acts smoothly on `V`. -/
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : Nat∞ω) :
    ContMDiffSMul 𝓘(𝕜, V ->L[𝕜] V) 𝓘(𝕜, V) n (V ->L[𝕜] V)ˣ V :=
  inferInstance

end Units
