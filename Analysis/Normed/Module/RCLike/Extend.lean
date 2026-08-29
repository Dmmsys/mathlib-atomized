/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.RCLike.Extend

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `StrongDual.extendRCLike` preserves the norm of the functional.
-/

public section

open RCLike ContinuousLinearMap Module
open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]

/--
theorem `Module.Dual.norm_extendRCLike_le_seminorm` / 定理 `Module.Dual.norm_extendRCLike_le_seminorm`

English:
theorem Module.Dual.norm_extendRCLike_le_seminorm
  statement: [AddCommGroup E] [Module 𝕜 E] [Module Real E]
  proof: by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 <= ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ <= |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _

中文:
定理 模.对偶.norm_extendRCLike_le_seminorm
  结论: [加法交换群 E] [模 𝕜 E] [模 实数 E]
  证明: by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 <= ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ <= |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _

Depends on / 依赖: extendRCLike, fr.extendRCLike, fr.norm_extendRCLike_apply_sq, le_abs_self, map_smul_eq_mul, norm_conj, norm_extendRCLike_apply_sq, norm_pos_iff
-/
theorem Module.Dual.norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module Real E]
    [IsScalarTower Real 𝕜 E] (fr : Dual Real E) {p : Seminorm 𝕜 E} (hp : forall x, |fr x| <= p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ <= p x := by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 <= ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ <= |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _ <= p (conj (fr.extendRCLike x) • x) := hp _
    _ = ‖conj (fr.extendRCLike x)‖ * p x := map_smul_eq_mul _ _ _
    _ = ‖(fr.extendRCLike x)‖ * p x := by rw [norm_conj]
exact (mul_le_mul_iff_left₀ (norm_pos_iff.2 hx)).1 by simpa [pow_two, mul_comm] using hsq

namespace StrongDual

/-- The extension `StrongDual.extendRCLike` as a continuous linear equivalence between
the strong duals when scalar multiplication (by `𝕜`) is jointly continuous. -/
@[expose, simps! -isSimp apply symm_apply]
/--
Definition of `extendRCLikeL` / `extendRCLikeL` 的定义

English:
definition extendRCLikeL
  signature: {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
  body: extendRCLikeₗ
  continuous_toFun := by
    rw [(ContinuousLinearMap.isEmbedding_restrictScalars Real).continuous_iff]
.restrictScalars Real let smulI : F ->L[Real] F := (I : 𝕜) • ContinuousLinearMap.id 𝕜 F
    let mulI : 𝕜 ->L[Real] 𝕜 := ContinuousLinearMap.mul Real 𝕜 (I : 𝕜)
    exact ofRealCLM.pos

中文:
定义 extendRCLikeL
  签名: {𝕜 F : 类型} [RCLike 𝕜] [拓扑空间 F]
  定义体: extendRCLikeₗ
  continuous_toFun := by
    rw [(ContinuousLinearMap.isEmbedding_restrictScalars Real).continuous_iff]
.restrictScalars Real let smulI : F ->L[Real] F := (I : 𝕜) • ContinuousLinearMap.id 𝕜 F
    let mulI : 𝕜 ->L[Real] 𝕜 := ContinuousLinearMap.mul Real 𝕜 (I : 𝕜)
    exact ofRealCLM.pos
-/
noncomputable def extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
    [AddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module Real F] [IsScalarTower Real 𝕜 F] :
    StrongDual Real F ≃L[Real] StrongDual 𝕜 F where
  toLinearEquiv := extendRCLikeₗ
  continuous_toFun := by
    rw [(ContinuousLinearMap.isEmbedding_restrictScalars Real).continuous_iff]
.restrictScalars Real let smulI : F ->L[Real] F := (I : 𝕜) • ContinuousLinearMap.id 𝕜 F
    let mulI : 𝕜 ->L[Real] 𝕜 := ContinuousLinearMap.mul Real 𝕜 (I : 𝕜)
    exact ofRealCLM.postcomp F - mulI.postcomp F ∘L smulI.precomp 𝕜 ∘L ofRealCLM.postcomp F
.continuous
.continuous.comp continuous_invFun := reCLM.postcomp F
    (ContinuousLinearMap.isEmbedding_restrictScalars Real).continuous

@[simp]
/--
lemma `toLinearEquiv_extendRCLikeL` / 引理 `toLinearEquiv_extendRCLikeL`

English:
lemma toLinearEquiv_extendRCLikeL
  statement: {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
  proof: rfl

中文:
引理 toLinearEquiv_extendRCLikeL
  结论: {𝕜 F : 类型} [RCLike 𝕜] [拓扑空间 F]
  证明: rfl

Depends on / 依赖: toLinearEquiv
-/
lemma toLinearEquiv_extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
    [AddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module Real F] [IsScalarTower Real 𝕜 F] :
    (extendRCLikeL (𝕜 := 𝕜) (F := F)).toLinearEquiv = extendRCLikeₗ :=
  rfl

/--
theorem `norm_extendRCLike_le_seminorm` / 定理 `norm_extendRCLike_le_seminorm`

English:
theorem norm_extendRCLike_le_seminorm
  statement: [AddCommGroup E] [Module 𝕜 E] [Module Real E]
  proof: Dual.norm_extendRCLike_le_seminorm fr hp x

中文:
定理 norm_extendRCLike_le_seminorm
  结论: [加法交换群 E] [模 𝕜 E] [模 实数 E]
  证明: Dual.norm_extendRCLike_le_seminorm fr hp x

Depends on / 依赖: Dual.norm_extendRCLike_le_seminorm, norm_extendRCLike_le_seminorm
-/
theorem norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module Real E]
    [IsScalarTower Real 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] (fr : StrongDual Real E)
    {p : Seminorm 𝕜 E} (hp : forall x, |fr x| <= p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ <= p x :=
  Dual.norm_extendRCLike_le_seminorm fr hp x

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace Real F] [IsScalarTower Real 𝕜 F]

/--
theorem `norm_extendRCLike_bound` / 定理 `norm_extendRCLike_bound`

English:
theorem norm_extendRCLike_bound
  given: (fr : StrongDual Real F) (x : F)
  proof: by
  refine Module.Dual.norm_extendRCLike_le_seminorm (p := ‖fr‖₊ • normSeminorm 𝕜 F)
    fr.toLinearMap ?_ x
  simp [← Real.norm_eq_abs, NNReal.smul_def, le_opNorm]

@[simp]

中文:
定理 norm_extendRCLike_bound
  条件: (fr : StrongDual 实数 F) (x : F)
  证明: by
  refine Module.Dual.norm_extendRCLike_le_seminorm (p := ‖fr‖₊ • normSeminorm 𝕜 F)
    fr.toLinearMap ?_ x
  simp [← Real.norm_eq_abs, NNReal.smul_def, le_opNorm]

@[simp]

Depends on / 依赖: Module, Module.Dual.norm_extendRCLike_le_seminorm, NNReal, NNReal.smul_def, Real.norm_eq_abs, fr.toLinearMap, le_opNorm, normSeminorm, norm_eq_abs, norm_extendRCLike_le_seminorm, smul_def, toLinearMap
-/
theorem norm_extendRCLike_bound (fr : StrongDual Real F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ <= ‖fr‖ * ‖x‖ := by
  refine Module.Dual.norm_extendRCLike_le_seminorm (p := ‖fr‖₊ • normSeminorm 𝕜 F)
    fr.toLinearMap ?_ x
  simp [← Real.norm_eq_abs, NNReal.smul_def, le_opNorm]

@[simp]
/--
theorem `norm_extendRCLike` / 定理 `norm_extendRCLike`

English:
theorem norm_extendRCLike
  given: (fr : StrongDual Real F)
  statement: ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖
  proof: le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound)
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ <= ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ <= ‖(fr.extendRCLike 

中文:
定理 norm_extendRCLike
  条件: (fr : StrongDual 实数 F)
  结论: ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖
  证明: le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound)
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ <= ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ <= ‖(fr.extendRCLike 

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, StrongDual, abs_re_le_norm, extendRCLike, fr.extendRCLike, fr.norm_extendRCLike_bound, le_antisymm, le_opNorm, norm_extendRCLike_bound, norm_nonneg, opNorm_le_bound
-/
theorem norm_extendRCLike (fr : StrongDual Real F) : ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖ :=
le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound)
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ <= ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ <= ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ * ‖x‖ := le_opNorm _ _

/-- `StrongDual.extendRCLike` bundled into a linear isometry equivalence. -/
@[expose, simps! -isSimp apply symm_apply]
/--
Definition of `extendRCLikeₗᵢ` / `extendRCLikeₗᵢ` 的定义

English:
definition extendRCLikeₗᵢ
  signature: : StrongDual Real F ≃ₗᵢ[Real] StrongDual 𝕜 F where
  body: StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

@[simp]

中文:
定义 extendRCLikeₗᵢ
  签名: : StrongDual 实数 F ≃ₗᵢ[实数] StrongDual 𝕜 F where
  定义体: StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

@[simp]

Depends on / 依赖: StrongDual, StrongDual.extendRCLike
-/
noncomputable def extendRCLikeₗᵢ : StrongDual Real F ≃ₗᵢ[Real] StrongDual 𝕜 F where
  toLinearEquiv := StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

@[simp]
/--
lemma `toLinearEquiv_extendRCLikeₗᵢ` / 引理 `toLinearEquiv_extendRCLikeₗᵢ`

English:
lemma toLinearEquiv_extendRCLikeₗᵢ
  proof: rfl

@[simp]

中文:
引理 toLinearEquiv_extendRCLikeₗᵢ
  证明: rfl

@[simp]

Depends on / 依赖: toLinearEquiv
-/
lemma toLinearEquiv_extendRCLikeₗᵢ :
    (extendRCLikeₗᵢ (𝕜 := 𝕜) (F := F)).toLinearEquiv = extendRCLikeₗ :=
  rfl

@[simp]
/--
lemma `toContinuousLinearEquiv_extendRCLikeₗᵢ` / 引理 `toContinuousLinearEquiv_extendRCLikeₗᵢ`

English:
lemma toContinuousLinearEquiv_extendRCLikeₗᵢ
  proof: rfl

中文:
引理 toContinuousLinearEquiv_extendRCLikeₗᵢ
  证明: rfl

Depends on / 依赖: extendRCLikeL, toContinuousLinearEquiv
-/
lemma toContinuousLinearEquiv_extendRCLikeₗᵢ :
    (extendRCLikeₗᵢ (F := F) (𝕜 := 𝕜)).toContinuousLinearEquiv = extendRCLikeL :=
  rfl

end StrongDual

namespace ContinuousLinearMap
open StrongDual

@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_bound := norm_extendRCLike_bound
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜' := norm_extendRCLike
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜 := norm_extendRCLike

end ContinuousLinearMap
