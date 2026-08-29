/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.UniformField

/-!
# Normed space structure on the completion of a normed space

If `E` is a normed space over `𝕜`, then so is `UniformSpace.Completion E`. In this file we provide
necessary instances and define `UniformSpace.Completion.toComplₗᵢ` - coercion
`E → UniformSpace.Completion E` as a bundled linear isometry.

We also show that if `A` is a normed algebra over `𝕜`, then so is `UniformSpace.Completion A`.

TODO: Generalise the results here from the concrete `completion` to any `AbstractCompletion`.
-/

@[expose] public section


noncomputable section

namespace UniformSpace

namespace Completion

variable (𝕜 E : Type*)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
  body: norm_smul_le

中文:
实例 [NormedField
  签名: 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    NormedSpace 𝕜 (Completion E) where
  norm_smul_le := norm_smul_le

section Module

variable {𝕜 E}
variable [Semiring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [UniformContinuousConstSMul 𝕜 E]

/--
Definition of `toComplₗᵢ` / `toComplₗᵢ` 的定义

English:
definition toComplₗᵢ
  signature: : E ->ₗᵢ[𝕜] Completion E
  body: { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]

中文:
定义 toComplₗᵢ
  签名: : E ->ₗᵢ[𝕜] Completion E
  定义体: { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]

Depends on / 依赖: coe_smul, map_smul, norm_coe, norm_map, toCompl
-/
def toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E :=
  { toCompl with
    toFun := (↑)
    map_smul' := coe_smul
    norm_map' := norm_coe }

@[simp]
/--
theorem `coe_toComplₗᵢ` / 定理 `coe_toComplₗᵢ`

English:
theorem coe_toComplₗᵢ
  statement: ⇑(toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E) = ((↑) : E -> Completion E)
  proof: rfl

中文:
定理 coe_toComplₗᵢ
  结论: ⇑(toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E) = ((↑) : E -> Completion E)
  证明: rfl
-/
theorem coe_toComplₗᵢ : ⇑(toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E) = ((↑) : E -> Completion E) :=
  rfl

/--
Definition of `toComplL` / `toComplL` 的定义

English:
definition toComplL
  signature: : E ->L[𝕜] Completion E
  body: toComplₗᵢ.toContinuousLinearMap

@[simp]

中文:
定义 toComplL
  签名: : E ->L[𝕜] Completion E
  定义体: toComplₗᵢ.toContinuousLinearMap

@[simp]

Depends on / 依赖: toContinuousLinearMap
-/
def toComplL : E ->L[𝕜] Completion E :=
  toComplₗᵢ.toContinuousLinearMap

@[simp]
/--
theorem `coe_toComplL` / 定理 `coe_toComplL`

English:
theorem coe_toComplL
  statement: ⇑(toComplL : E ->L[𝕜] Completion E) = ((↑) : E -> Completion E)
  proof: rfl

@[simp]

中文:
定理 coe_toComplL
  结论: ⇑(toComplL : E ->L[𝕜] Completion E) = ((↑) : E -> Completion E)
  证明: rfl

@[simp]
-/
theorem coe_toComplL : ⇑(toComplL : E ->L[𝕜] Completion E) = ((↑) : E -> Completion E) :=
  rfl

@[simp]
/--
theorem `norm_toComplL` / 定理 `norm_toComplL`

English:
theorem norm_toComplL
  statement: {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  proof: (toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

中文:
定理 norm_toComplL
  结论: {𝕜 E : 类型} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  证明: (toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

Depends on / 依赖: Completion, norm_toContinuousLinearMap
-/
theorem norm_toComplL {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Nontrivial E] : ‖(toComplL : E ->L[𝕜] Completion E)‖ = 1 :=
  (toComplₗᵢ : E ->ₗᵢ[𝕜] Completion E).norm_toContinuousLinearMap

end Module

section Algebra

variable (A : Type*)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedRing
  signature: A] : NormedRing (Completion A) where
  body: inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul, norm_coe] using norm_mul_le x y

中文:
实例 [SeminormedRing
  签名: A] : NormedRing (Completion A) where
  定义体: inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul, norm_coe] using norm_mul_le x y
-/
instance [SeminormedRing A] : NormedRing (Completion A) where
  __ : NormedAddCommGroup (Completion A) := inferInstance
  __ : Ring (Completion A) := inferInstance
  norm_mul_le x y := by
    induction x, y using induction_on₂ with
    | hp => apply isClosed_le <;> fun_prop
    | ih x y => simpa only [← coe_mul, norm_coe] using norm_mul_le x y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SeminormedCommRing
  signature: A] : NormedCommRing (Completion A) where
  body: inferInstance
  __ : NormedRing (Completion A) := inferInstance

中文:
实例 [SeminormedCommRing
  签名: A] : NormedCommRing (Completion A) where
  定义体: inferInstance
  __ : NormedRing (Completion A) := inferInstance
-/
instance [SeminormedCommRing A] : NormedCommRing (Completion A) where
  __ : CommRing (Completion A) := inferInstance
  __ : NormedRing (Completion A) := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] :
  body: norm_smul_le

中文:
实例 [NormedField
  签名: 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] :
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance [NormedField 𝕜] [SeminormedCommRing A] [NormedAlgebra 𝕜 A] :
    NormedAlgebra 𝕜 (Completion A) where
  norm_smul_le := norm_smul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedField
  signature: A] [CompletableTopField A] :
  body: inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

中文:
实例 [NormedField
  签名: A] [CompletableTopField A] :
  定义体: inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])
-/
instance [NormedField A] [CompletableTopField A] :
    NormedField (UniformSpace.Completion A) where
  __ : NormedCommRing (Completion A) := inferInstance
  __ : Field (Completion A) := inferInstance
  norm_mul x y := induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) (by simp [← coe_mul])

end Algebra

end Completion

end UniformSpace
