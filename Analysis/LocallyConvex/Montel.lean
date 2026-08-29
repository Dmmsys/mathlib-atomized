/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM
public import Mathlib.Analysis.Normed.Module.FiniteDimension
/-!
# Montel spaces

A Montel space is a topological vector space `E` that has the Heine-Borel property: every closed and
(von Neumann) bounded set is compact.

Note that we are not requiring that `E` is a barrelled space, so the usual definition of a Montel
space would be `[MontelSpace 𝕜 E] [BarrelledSpace 𝕜 E]`.

* `MontelSpace.finiteDimensional_of_normedSpace`: every normed Montel space is finite dimensional.
* `ContinuousLinearEquiv.toCompactConvergenceCLM`: if `E` is a Montel space then topology of compact
  convergence and the strong topology on `E →SL[σ] F` coincide. We record this as a continuous
  linear equivalence between `E →SL[σ] F` and `E →SL_c[σ] F`. This is Proposition 34.5 in
  [F. Trèves][treves1967].

## References
* [F. Trèves, *Topological vector spaces, distributions and kernels*][treves1967]

-/

@[expose] public section

open Filter Topology Set ContinuousLinearMap Bornology

section Definition

variable {𝕜 E F : Type*}
variable [SeminormedRing 𝕜] [Zero E] [SMul 𝕜 E]
  [TopologicalSpace E]

/--
Definition of `MontelSpace` / `MontelSpace` 的定义

English:
class MontelSpace
  parameters: (𝕜 E : Type*) [SeminormedRing 𝕜] [Zero E] [SMul 𝕜 E]
  axioms and operations (1):
    - heine_borel : forall s : Set E, IsClosed s -> IsVonNBounded 𝕜 s -> IsCompact s

中文:
类 Montel空间
  参数: (𝕜 E : 类型) [Seminormed环 𝕜] [零 E] [标量乘法 𝕜 E]
  公理与运算 (1 个):
    - heine_borel : 对任意 s : 集合 E, 是闭集 s -> IsVonNBounded 𝕜 s -> 是紧集 s
-/
class MontelSpace (𝕜 E : Type*) [SeminormedRing 𝕜] [Zero E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  heine_borel : forall s : Set E, IsClosed s -> IsVonNBounded 𝕜 s -> IsCompact s

namespace MontelSpace

variable (𝕜) in
/--
theorem `isCompact_of_isClosed_of_isVonNBounded` / 定理 `isCompact_of_isClosed_of_isVonNBounded`

English:
theorem isCompact_of_isClosed_of_isVonNBounded
  statement: [hm : MontelSpace 𝕜 E] {s : Set E}
  proof: hm.heine_borel s h_closed h_bounded

中文:
定理 isCompact_of_isClosed_of_isVonNBounded
  结论: [hm : Montel空间 𝕜 E] {s : 集合 E}
  证明: hm.heine_borel s h_closed h_bounded

Depends on / 依赖: h_bounded, h_closed, heine_borel, hm.heine_borel
-/
theorem isCompact_of_isClosed_of_isVonNBounded [hm : MontelSpace 𝕜 E] {s : Set E}
    (h_closed : IsClosed s) (h_bounded : IsVonNBounded 𝕜 s) : IsCompact s :=
  hm.heine_borel s h_closed h_bounded

end MontelSpace

end Definition

section Normed

namespace MontelSpace

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [hM : MontelSpace 𝕜 E]

/--
theorem `finiteDimensional_of_normedSpace` / 定理 `finiteDimensional_of_normedSpace`

English:
theorem finiteDimensional_of_normedSpace
  statement: FiniteDimensional 𝕜 E
  proof: FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
    (isCompact_of_isClosed_of_isVonNBounded 𝕜 Metric.isClosed_closedBall
      (NormedSpace.isVonNBounded_closedBall _ _ _))

中文:
定理 finiteDimensional_of_normedSpace
  结论: 有限维 𝕜 E
  证明: FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
    (isCompact_of_isClosed_of_isVonNBounded 𝕜 Metric.isClosed_closedBall
      (NormedSpace.isVonNBounded_closedBall _ _ _))

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_isCompact_closedBall, Metric, Metric.isClosed_closedBall, NormedSpace, NormedSpace.isVonNBounded_closedBall, isClosed_closedBall, isCompact_of_isClosed_of_isVonNBounded, isVonNBounded_closedBall, zero_lt_one
-/
theorem finiteDimensional_of_normedSpace : FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one
    (isCompact_of_isClosed_of_isVonNBounded 𝕜 Metric.isClosed_closedBall
      (NormedSpace.isVonNBounded_closedBall _ _ _))

end MontelSpace

end Normed

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ ->+* 𝕜₂}
variable {E F : Type*}
  [AddCommGroup E] [Module 𝕜₁ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F]

open CompactConvergenceCLM

set_option backward.privateInPublic true in
variable (σ E F) in
/--
Definition of `_root_.LinearEquiv.toCompactConvergenceCLM` / `_root_.LinearEquiv.toCompactConvergenceCLM` 的定义

English:
definition _root_.LinearEquiv.toCompactConvergenceCLM
  signature: :
  body: LinearEquiv.refl 𝕜₂ _

中文:
定义 _root_.线性等价.toCompactConvergenceCLM
  签名: :
  定义体: LinearEquiv.refl 𝕜₂ _
-/
private def _root_.LinearEquiv.toCompactConvergenceCLM :
    (E ->SL[σ] F) ≃ₗ[𝕜₂] E ->SL_c[σ] F :=
  LinearEquiv.refl 𝕜₂ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (σ E F) in
/--
Definition of `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM` / `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM` 的定义

English:
definition _root_.ContinuousLinearEquiv.toCompactConvergenceCLM
  signature: [T1Space E] [MontelSpace 𝕜₁ E]
  body: LinearEquiv.toCompactConvergenceCLM σ E F
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, continuous_def]
    intro s hs
    apply hs.mono
    apply UniformConvergenceCLM.topologicalSpace_mono
    intro x hx
    exact hx.isVonNBounded 𝕜₁
  continuous_invFun := by
    apply continuous_of_continuousAt_zero (LinearEquiv.toCompactConvergenceCLM σ E F).symm
    rw [ContinuousAt]; rw [_root_.map_zero]; rw [CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_iff
      ContinuousLinearMap.hasBasis_nhds_zero]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    use ⟨closure a, b⟩
    exact ⟨⟨MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜₁ isClosed_closure
      ha.closure, hb⟩, fun _ hf _ hx => hf _ (subset_closure hx)⟩

@[simp]

中文:
定义 _root_.连续线性等价.toCompactConvergenceCLM
  签名: [T1空间 E] [Montel空间 𝕜₁ E]
  定义体: LinearEquiv.toCompactConvergenceCLM σ E F
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, continuous_def]
    intro s hs
    apply hs.mono
    apply UniformConvergenceCLM.topologicalSpace_mono
    intro x hx
    exact hx.isVonNBounded 𝕜₁
  continuous_invFun := by
    apply continuous_of_continuousAt_zero (LinearEquiv.toCompactConvergenceCLM σ E F).symm
    rw [ContinuousAt]; rw [_root_.map_zero]; rw [CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_iff
      ContinuousLinearMap.hasBasis_nhds_zero]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    use ⟨closure a, b⟩
    exact ⟨⟨MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜₁ isClosed_closure
      ha.closure, hb⟩, fun _ hf _ hx => hf _ (subset_closure hx)⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.toCompactConvergenceCLM, toCompactConvergenceCLM
-/
def _root_.ContinuousLinearEquiv.toCompactConvergenceCLM [T1Space E] [MontelSpace 𝕜₁ E] :
    (E ->SL[σ] F) ≃L[𝕜₂] E ->SL_c[σ] F where
  __ := LinearEquiv.toCompactConvergenceCLM σ E F
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, continuous_def]
    intro s hs
    apply hs.mono
    apply UniformConvergenceCLM.topologicalSpace_mono
    intro x hx
    exact hx.isVonNBounded 𝕜₁
  continuous_invFun := by
    apply continuous_of_continuousAt_zero (LinearEquiv.toCompactConvergenceCLM σ E F).symm
    rw [ContinuousAt]; rw [_root_.map_zero]; rw [CompactConvergenceCLM.hasBasis_nhds_zero.tendsto_iff
      ContinuousLinearMap.hasBasis_nhds_zero]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    use ⟨closure a, b⟩
    exact ⟨⟨MontelSpace.isCompact_of_isClosed_of_isVonNBounded 𝕜₁ isClosed_closure
      ha.closure, hb⟩, fun _ hf _ hx => hf _ (subset_closure hx)⟩

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM_apply` / 定理 `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM_apply`

English:
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_apply
  statement: [T1Space E] [MontelSpace 𝕜₁ E]
  proof: rfl

@[simp]

中文:
定理 _root_.连续线性等价.toCompactConvergenceCLM_apply
  结论: [T1空间 E] [Montel空间 𝕜₁ E]
  证明: rfl

@[simp]
-/
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_apply [T1Space E] [MontelSpace 𝕜₁ E]
    (f : E ->SL[σ] F) (x : E) : ContinuousLinearEquiv.toCompactConvergenceCLM σ E F f x = f x := rfl

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM_symm_apply` / 定理 `_root_.ContinuousLinearEquiv.toCompactConvergenceCLM_symm_apply`

English:
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_symm_apply
  statement: [T1Space E]
  proof: rfl

中文:
定理 _root_.连续线性等价.toCompactConvergenceCLM_symm_apply
  结论: [T1空间 E]
  证明: rfl
-/
theorem _root_.ContinuousLinearEquiv.toCompactConvergenceCLM_symm_apply [T1Space E]
    [MontelSpace 𝕜₁ E] (f : E ->SL_c[σ] F) (x : E) :
    (ContinuousLinearEquiv.toCompactConvergenceCLM σ E F).symm f x = f x := rfl
