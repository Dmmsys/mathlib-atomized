/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Heather Macbeth
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# Uniform space structure on matrices
-/

public section


open Uniformity Topology

variable (m n 𝕜 : Type*) [UniformSpace 𝕜]

namespace Matrix

/--
Instance `instUniformSpace` / 实例 `instUniformSpace`

English:
instance instUniformSpace
  signature: : UniformSpace (Matrix m n 𝕜)
  body: inferInstanceAs UniformSpace (m -> n -> 𝕜)

中文:
实例 instUniformSpace
  签名: : 一致空间 (矩阵 m n 𝕜)
  定义体: inferInstanceAs UniformSpace (m -> n -> 𝕜)

Depends on / 依赖: UniformSpace
-/
instance instUniformSpace : UniformSpace (Matrix m n 𝕜) :=
inferInstanceAs UniformSpace (m -> n -> 𝕜)

/--
Instance `instIsUniformAddGroup` / 实例 `instIsUniformAddGroup`

English:
instance instIsUniformAddGroup
  signature: [AddGroup 𝕜] [IsUniformAddGroup 𝕜]
  body: inferInstanceAs IsUniformAddGroup (m -> n -> 𝕜)

中文:
实例 instIsUniformAddGroup
  签名: [加法群 𝕜] [是UniformAdd群 𝕜]
  定义体: inferInstanceAs IsUniformAddGroup (m -> n -> 𝕜)

Depends on / 依赖: IsUniformAddGroup
-/
instance instIsUniformAddGroup [AddGroup 𝕜] [IsUniformAddGroup 𝕜] :
    IsUniformAddGroup (Matrix m n 𝕜) :=
inferInstanceAs IsUniformAddGroup (m -> n -> 𝕜)

/--
theorem `uniformity` / 定理 `uniformity`

English:
theorem uniformity
  proof: by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl

中文:
定理 uniformity
  证明: by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl

Depends on / 依赖: Filter, Filter.comap_comap, Filter.comap_iInf, Pi.uniformity, comap_comap, comap_iInf, simp_rw, uniformity
-/
theorem uniformity :
    𝓤 (Matrix m n 𝕜) = ⨅ (i : m) (j : n), (𝓤 𝕜).comap fun a => (a.1 i j, a.2 i j) := by
  erw [Pi.uniformity]
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap]
  rfl

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: {β : Type*} [UniformSpace β] {f : β -> Matrix m n 𝕜}
  proof: by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a

中文:
定理 uniformContinuous
  条件: {β : 类型} [一致空间 β] {f : β -> 矩阵 m n 𝕜}
  证明: by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a

Depends on / 依赖: Filter, Filter.tendsto_comap_iff, Filter.tendsto_iInf, Iff.intro, Matrix, Matrix.uniformity, UniformContinuous, tendsto_comap_iff, tendsto_iInf, uniformity
-/
theorem uniformContinuous {β : Type*} [UniformSpace β] {f : β -> Matrix m n 𝕜} :
    UniformContinuous f ↔ forall i j, UniformContinuous fun x => f x i j := by
  simp only [UniformContinuous, Matrix.uniformity, Filter.tendsto_iInf, Filter.tendsto_comap_iff]
  apply Iff.intro <;> intro a <;> apply a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: 𝕜] : CompleteSpace (Matrix m n 𝕜)
  body: inferInstanceAs CompleteSpace (m -> n -> 𝕜)

中文:
实例 [完备空间
  签名: 𝕜] : 完备空间 (矩阵 m n 𝕜)
  定义体: inferInstanceAs CompleteSpace (m -> n -> 𝕜)

Depends on / 依赖: CompleteSpace
-/
instance [CompleteSpace 𝕜] : CompleteSpace (Matrix m n 𝕜) :=
inferInstanceAs CompleteSpace (m -> n -> 𝕜)

end Matrix
