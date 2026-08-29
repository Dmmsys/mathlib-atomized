/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of a continuous linear map.
-/

public section


namespace ContinuousLinearMap

/--
Definition of `det` / `det` 的定义

English:
abbreviation det
  signature: {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
  body: LinearMap.det (A : M ->ₗ[R] M)

中文:
缩写 det
  签名: {R : 类型} [交换环 R] {M : 类型} [拓扑空间 M] [加法交换群 M]
  定义体: LinearMap.det (A : M ->ₗ[R] M)

Depends on / 依赖: LinearMap, LinearMap.det
-/
noncomputable abbrev det {R : Type*} [CommRing R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ->L[R] M) : R :=
  LinearMap.det (A : M ->ₗ[R] M)

/--
theorem `det_pi` / 定理 `det_pi`

English:
theorem det_pi
  statement: {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M]
  proof: LinearMap.det_pi _

中文:
定理 det_pi
  结论: {ι R M : 类型} [有限类型 ι] [交换环 R] [加法交换群 M]
  证明: LinearMap.det_pi _

Depends on / 依赖: LinearMap, LinearMap.det_pi, det_pi
-/
theorem det_pi {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M]
    [TopologicalSpace M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : ι -> M ->L[R] M) :
    (pi (fun i => (f i).comp (proj i))).det = ∏ i, (f i).det :=
  LinearMap.det_pi _

/--
theorem `det_smulRight` / 定理 `det_smulRight`

English:
theorem det_smulRight
  statement: {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
  proof: by simp

中文:
定理 det_smulRight
  结论: {𝕜 : 类型} [交换环 𝕜] [拓扑空间 𝕜] [连续乘法 𝕜]
  证明: by simp
-/
theorem det_smulRight {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (f : 𝕜 ->L[𝕜] 𝕜) (v : 𝕜) : (smulRight f v).det = f 1 * v := by simp

/--
theorem `det_toSpanSingleton` / 定理 `det_toSpanSingleton`

English:
theorem det_toSpanSingleton
  statement: {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
  proof: by rw [← smulRight_id, det_smulRight]; simp

中文:
定理 det_toSpanSingleton
  结论: {𝕜 : 类型} [交换环 𝕜] [拓扑空间 𝕜] [连续乘法 𝕜]
  证明: by rw [← smulRight_id, det_smulRight]; simp

Depends on / 依赖: det_smulRight, smulRight_id
-/
theorem det_toSpanSingleton {𝕜 : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
    (v : 𝕜) : (toSpanSingleton 𝕜 v).det = v := by rw [← smulRight_id, det_smulRight]; simp

end ContinuousLinearMap

namespace ContinuousLinearEquiv

@[simp]
/--
theorem `det_coe_symm` / 定理 `det_coe_symm`

English:
theorem det_coe_symm
  statement: {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
  proof: LinearEquiv.det_coe_symm A.toLinearEquiv

中文:
定理 det_coe_symm
  结论: {R : 类型} [域 R] {M : 类型} [拓扑空间 M] [加法交换群 M]
  证明: LinearEquiv.det_coe_symm A.toLinearEquiv

Depends on / 依赖: A.toLinearEquiv, LinearEquiv, LinearEquiv.det_coe_symm, det_coe_symm, toLinearEquiv
-/
theorem det_coe_symm {R : Type*} [Field R] {M : Type*} [TopologicalSpace M] [AddCommGroup M]
    [Module R M] (A : M ≃L[R] M) : (A.symm : M ->L[R] M).det = (A : M ->L[R] M).det⁻¹ :=
  LinearEquiv.det_coe_symm A.toLinearEquiv

end ContinuousLinearEquiv
