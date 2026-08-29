/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Results about operator norms in normed algebras

This file (split off from `OperatorNorm.lean`) contains results about the operator norm
of multiplication and scalar-multiplication operations in normed algebras and normed modules.
-/

@[expose] public section

suppress_compilation

open Metric
open scoped NNReal Topology Uniformity

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]

section SemiNormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

section MultiplicationLinear

section NonUnital

variable (𝕜) (R : Type*) [NonUnitalSeminormedRing R]
variable [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : R ->L[𝕜] R ->L[𝕜] R
  body: (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y

@[simp]

中文:
定义 mul
  签名: : R ->L[𝕜] R ->L[𝕜] R
  定义体: (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mul, norm_mul_le
-/
def mul : R ->L[𝕜] R ->L[𝕜] R :=
  (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y

@[simp]
/--
theorem `mul_apply'` / 定理 `mul_apply'`

English:
theorem mul_apply'
  given: (x y : R)
  statement: mul 𝕜 R x y = x * y
  proof: rfl

@[simp]

中文:
定理 mul_apply'
  条件: (x y : R)
  结论: mul 𝕜 R x y = x * y
  证明: rfl

@[simp]
-/
theorem mul_apply' (x y : R) : mul 𝕜 R x y = x * y :=
  rfl

@[simp]
/--
theorem `opNorm_mul_apply_le` / 定理 `opNorm_mul_apply_le`

English:
theorem opNorm_mul_apply_le
  given: (x : R)
  statement: ‖mul 𝕜 R x‖ <= ‖x‖
  proof: opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)

中文:
定理 opNorm_mul_apply_le
  条件: (x : R)
  结论: ‖mul 𝕜 R x‖ <= ‖x‖
  证明: opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)

Depends on / 依赖: norm_mul_le, norm_nonneg, opNorm_le_bound
-/
theorem opNorm_mul_apply_le (x : R) : ‖mul 𝕜 R x‖ <= ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)

/--
theorem `opNorm_mul_le` / 定理 `opNorm_mul_le`

English:
theorem opNorm_mul_le
  statement: ‖mul 𝕜 R‖ <= 1
  proof: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

中文:
定理 opNorm_mul_le
  结论: ‖mul 𝕜 R‖ <= 1
  证明: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, zero_le_one
-/
theorem opNorm_mul_le : ‖mul 𝕜 R‖ <= 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/--
Definition of `_root_.NonUnitalAlgHom.Lmul` / `_root_.NonUnitalAlgHom.Lmul` 的定义

English:
definition _root_.NonUnitalAlgHom.Lmul
  signature: : R ->ₙₐ[𝕜] R ->L[𝕜] R
  body: { mul 𝕜 R with
    map_mul' := fun _ _ => ext fun _ => mul_assoc _ _ _
    map_zero' := ext fun _ => zero_mul _ }

中文:
定义 _root_.非幺Alg态射.Lmul
  签名: : R ->ₙₐ[𝕜] R ->L[𝕜] R
  定义体: { mul 𝕜 R with
    map_mul' := fun _ _ => ext fun _ => mul_assoc _ _ _
    map_zero' := ext fun _ => zero_mul _ }

Depends on / 依赖: map_mul, map_zero, mul_assoc, zero_mul
-/
def _root_.NonUnitalAlgHom.Lmul : R ->ₙₐ[𝕜] R ->L[𝕜] R :=
  { mul 𝕜 R with
    map_mul' := fun _ _ => ext fun _ => mul_assoc _ _ _
    map_zero' := ext fun _ => zero_mul _ }

variable {𝕜 R} in
@[simp]
/--
theorem `_root_.NonUnitalAlgHom.coe_Lmul` / 定理 `_root_.NonUnitalAlgHom.coe_Lmul`

English:
theorem _root_.NonUnitalAlgHom.coe_Lmul
  statement: ⇑(NonUnitalAlgHom.Lmul 𝕜 R) = mul 𝕜 R
  proof: rfl

中文:
定理 _root_.非幺Alg态射.coe_Lmul
  结论: ⇑(非幺Alg态射.Lmul 𝕜 R) = mul 𝕜 R
  证明: rfl
-/
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 R) = mul 𝕜 R :=
  rfl

/--
Definition of `mulLeftRight` / `mulLeftRight` 的定义

English:
definition mulLeftRight
  signature: : R ->L[𝕜] R ->L[𝕜] R ->L[𝕜] R
  body: ((compL 𝕜 R R R).comp (mul 𝕜 R).flip).flip.comp (mul 𝕜 R)

@[simp]

中文:
定义 mulLeftRight
  签名: : R ->L[𝕜] R ->L[𝕜] R ->L[𝕜] R
  定义体: ((compL 𝕜 R R R).comp (mul 𝕜 R).flip).flip.comp (mul 𝕜 R)

@[simp]

Depends on / 依赖: flip.comp
-/
def mulLeftRight : R ->L[𝕜] R ->L[𝕜] R ->L[𝕜] R :=
  ((compL 𝕜 R R R).comp (mul 𝕜 R).flip).flip.comp (mul 𝕜 R)

@[simp]
/--
theorem `mulLeftRight_apply` / 定理 `mulLeftRight_apply`

English:
theorem mulLeftRight_apply
  given: (x y z : R)
  statement: mulLeftRight 𝕜 R x y z = x * z * y
  proof: rfl

中文:
定理 mulLeftRight_apply
  条件: (x y z : R)
  结论: mulLeftRight 𝕜 R x y z = x * z * y
  证明: rfl
-/
theorem mulLeftRight_apply (x y z : R) : mulLeftRight 𝕜 R x y z = x * z * y :=
  rfl

/--
theorem `opNorm_mulLeftRight_apply_apply_le` / 定理 `opNorm_mulLeftRight_apply_apply_le`

English:
theorem opNorm_mulLeftRight_apply_apply_le
  given: (x y : R)
  statement: ‖mulLeftRight 𝕜 R x y‖ <= ‖x‖ * ‖y‖
  proof: (opNorm_comp_le _ _).trans
(mul_comm _ _).trans_le
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)

中文:
定理 opNorm_mulLeftRight_apply_apply_le
  条件: (x y : R)
  结论: ‖mulLeftRight 𝕜 R x y‖ <= ‖x‖ * ‖y‖
  证明: (opNorm_comp_le _ _).trans
(mul_comm _ _).trans_le
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)

Depends on / 依赖: mul_comm, mul_le_mul, norm_mul_le, norm_nonneg, opNorm_comp_le, opNorm_le_bound, opNorm_mul_apply_le, trans_eq, trans_le
-/
theorem opNorm_mulLeftRight_apply_apply_le (x y : R) : ‖mulLeftRight 𝕜 R x y‖ <= ‖x‖ * ‖y‖ :=
(opNorm_comp_le _ _).trans
(mul_comm _ _).trans_le
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)

/--
theorem `opNorm_mulLeftRight_apply_le` / 定理 `opNorm_mulLeftRight_apply_le`

English:
theorem opNorm_mulLeftRight_apply_le
  given: (x : R)
  statement: ‖mulLeftRight 𝕜 R x‖ <= ‖x‖
  proof: opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 R x)

中文:
定理 opNorm_mulLeftRight_apply_le
  条件: (x : R)
  结论: ‖mulLeftRight 𝕜 R x‖ <= ‖x‖
  证明: opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 R x)

Depends on / 依赖: norm_nonneg, opNorm_le_bound, opNorm_mulLeftRight_apply_apply_le
-/
theorem opNorm_mulLeftRight_apply_le (x : R) : ‖mulLeftRight 𝕜 R x‖ <= ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 R x)

/--
theorem `opNorm_mulLeftRight_le` / 定理 `opNorm_mulLeftRight_le`

English:
theorem opNorm_mulLeftRight_le
  proof: opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 R x

中文:
定理 opNorm_mulLeftRight_le
  证明: opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 R x

Depends on / 依赖: one_mul, opNorm_le_bound, opNorm_mulLeftRight_apply_le, zero_le_one
-/
theorem opNorm_mulLeftRight_le :
    ‖mulLeftRight 𝕜 R‖ <= 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 R x


/--
Definition of `_root_.RegularNormedAlgebra` / `_root_.RegularNormedAlgebra` 的定义

English:
class _root_.RegularNormedAlgebra
  parameters: : Prop where
  axioms and operations (1):
    - isometry_mul' : Isometry (mul 𝕜 R)

中文:
类 _root_.RegularNormed代数
  参数: : 命题 where
  公理与运算 (1 个):
    - isometry_mul' : 等距 (mul 𝕜 R)
-/
class _root_.RegularNormedAlgebra : Prop where
  /-- The left regular representation of the algebra on itself is an isometry. -/
  isometry_mul' : Isometry (mul 𝕜 R)

/--
Instance `_root_.NormedAlgebra.instRegularNormedAlgebra` / 实例 `_root_.NormedAlgebra.instRegularNormedAlgebra`

English:
instance _root_.NormedAlgebra.instRegularNormedAlgebra
  signature: {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
  body: AddMonoidHomClass.isometry_of_norm (mul 𝕜 R)
fun x => le_antisymm (opNorm_mul_apply_le _ _ _) by
      convert! ratio_le_opNorm ((mul 𝕜 R) x) (1 : R)
      simp [norm_one]

中文:
实例 _root_.赋范代数.instRegularNormedAlgebra
  签名: {𝕜 R : 类型} [NontriviallyNormedField 𝕜]
  定义体: AddMonoidHomClass.isometry_of_norm (mul 𝕜 R)
fun x => le_antisymm (opNorm_mul_apply_le _ _ _) by
      convert! ratio_le_opNorm ((mul 𝕜 R) x) (1 : R)
      simp [norm_one]

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, isometry_of_norm
-/
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing R] [NormedAlgebra 𝕜 R] [NormOneClass R] : RegularNormedAlgebra 𝕜 R where
isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 R)
fun x => le_antisymm (opNorm_mul_apply_le _ _ _) by
      convert! ratio_le_opNorm ((mul 𝕜 R) x) (1 : R)
      simp [norm_one]

variable [RegularNormedAlgebra 𝕜 R]

/--
lemma `isometry_mul` / 引理 `isometry_mul`

English:
lemma isometry_mul
  statement: Isometry (mul 𝕜 R)
  proof: RegularNormedAlgebra.isometry_mul'

@[simp]

中文:
引理 isometry_mul
  结论: 等距 (mul 𝕜 R)
  证明: RegularNormedAlgebra.isometry_mul'

@[simp]

Depends on / 依赖: RegularNormedAlgebra, RegularNormedAlgebra.isometry_mul, isometry_mul
-/
lemma isometry_mul : Isometry (mul 𝕜 R) :=
  RegularNormedAlgebra.isometry_mul'

@[simp]
/--
lemma `opNorm_mul_apply` / 引理 `opNorm_mul_apply`

English:
lemma opNorm_mul_apply
  given: (x : R)
  statement: ‖mul 𝕜 R x‖ = ‖x‖
  proof: (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 R)).mp (isometry_mul 𝕜 R) x

@[simp]

中文:
引理 opNorm_mul_apply
  条件: (x : R)
  结论: ‖mul 𝕜 R x‖ = ‖x‖
  证明: (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 R)).mp (isometry_mul 𝕜 R) x

@[simp]

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_iff_norm, isometry_iff_norm, isometry_mul
-/
lemma opNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 R)).mp (isometry_mul 𝕜 R) x

@[simp]
/--
lemma `opNNNorm_mul_apply` / 引理 `opNNNorm_mul_apply`

English:
lemma opNNNorm_mul_apply
  given: (x : R)
  statement: ‖mul 𝕜 R x‖₊ = ‖x‖₊
  proof: Subtype.ext opNorm_mul_apply 𝕜 R x

中文:
引理 opNNNorm_mul_apply
  条件: (x : R)
  结论: ‖mul 𝕜 R x‖₊ = ‖x‖₊
  证明: Subtype.ext opNorm_mul_apply 𝕜 R x

Depends on / 依赖: Subtype, Subtype.ext, opNorm_mul_apply
-/
lemma opNNNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖₊ = ‖x‖₊ :=
Subtype.ext opNorm_mul_apply 𝕜 R x

/--
Definition of `mulₗᵢ` / `mulₗᵢ` 的定义

English:
definition mulₗᵢ
  signature: : R ->ₗᵢ[𝕜] R ->L[𝕜] R where
  body: mul 𝕜 R
  norm_map' x := opNorm_mul_apply 𝕜 R x

@[simp]

中文:
定义 mulₗᵢ
  签名: : R ->ₗᵢ[𝕜] R ->L[𝕜] R where
  定义体: mul 𝕜 R
  norm_map' x := opNorm_mul_apply 𝕜 R x

@[simp]
-/
def mulₗᵢ : R ->ₗᵢ[𝕜] R ->L[𝕜] R where
  toLinearMap := mul 𝕜 R
  norm_map' x := opNorm_mul_apply 𝕜 R x

@[simp]
/--
theorem `coe_mulₗᵢ` / 定理 `coe_mulₗᵢ`

English:
theorem coe_mulₗᵢ
  statement: ⇑(mulₗᵢ 𝕜 R) = mul 𝕜 R
  proof: rfl

中文:
定理 coe_mulₗᵢ
  结论: ⇑(mulₗᵢ 𝕜 R) = mul 𝕜 R
  证明: rfl
-/
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 R) = mul 𝕜 R :=
  rfl

end NonUnital

section NonUnitalSeminormedCommRing
variable {R : Type*} [NonUnitalSeminormedCommRing R] [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R]
  [SMulCommClass 𝕜 R R]

/--
lemma `flip_mul` / 引理 `flip_mul`

English:
lemma flip_mul
  statement: (ContinuousLinearMap.mul 𝕜 R).flip = .mul 𝕜 R
  proof: by ext; simp [mul_comm]

中文:
引理 flip_mul
  结论: (连续线性映射.mul 𝕜 R).flip = .mul 𝕜 R
  证明: by ext; simp [mul_comm]
-/
@[simp] lemma flip_mul : (ContinuousLinearMap.mul 𝕜 R).flip = .mul 𝕜 R := by ext; simp [mul_comm]

end NonUnitalSeminormedCommRing

section RingEquiv

variable (𝕜 E)

/--
Definition of `toSpanSingletonLIE` / `toSpanSingletonLIE` 的定义

English:
definition toSpanSingletonLIE
  signature: : E ≃ₗᵢ[𝕜] (𝕜 ->L[𝕜] E) where
  body: toSpanSingletonLE 𝕜 𝕜 E
  norm_map' _ := by simp

@[simp]

中文:
定义 toSpanSingletonLIE
  签名: : E ≃ₗᵢ[𝕜] (𝕜 ->L[𝕜] E) where
  定义体: toSpanSingletonLE 𝕜 𝕜 E
  norm_map' _ := by simp

@[simp]

Depends on / 依赖: toSpanSingletonLE
-/
def toSpanSingletonLIE : E ≃ₗᵢ[𝕜] (𝕜 ->L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE 𝕜 𝕜 E
  norm_map' _ := by simp

@[simp]
/--
lemma `toSpanSingletonLIE_apply` / 引理 `toSpanSingletonLIE_apply`

English:
lemma toSpanSingletonLIE_apply
  given: (x : E)
  statement: toSpanSingletonLIE 𝕜 E x = toSpanSingleton 𝕜 x
  proof: rfl

中文:
引理 toSpanSingletonLIE_apply
  条件: (x : E)
  结论: toSpanSingletonLIE 𝕜 E x = toSpanSingleton 𝕜 x
  证明: rfl
-/
lemma toSpanSingletonLIE_apply (x : E) : toSpanSingletonLIE 𝕜 E x = toSpanSingleton 𝕜 x := rfl

/--
lemma `toSpanSingletonLIE_symm_apply` / 引理 `toSpanSingletonLIE_symm_apply`

English:
lemma toSpanSingletonLIE_symm_apply
  given: (f : 𝕜 ->L[𝕜] E)
  proof: rfl

中文:
引理 toSpanSingletonLIE_symm_apply
  条件: (f : 𝕜 ->L[𝕜] E)
  证明: rfl
-/
@[simp] lemma toSpanSingletonLIE_symm_apply (f : 𝕜 ->L[𝕜] E) :
    (toSpanSingletonLIE 𝕜 E).symm f = f 1 := rfl

/--
lemma `toLinearEquiv_toSpanSingletonLIE` / 引理 `toLinearEquiv_toSpanSingletonLIE`

English:
lemma toLinearEquiv_toSpanSingletonLIE
  proof: rfl

中文:
引理 toLinearEquiv_toSpanSingletonLIE
  证明: rfl
-/
@[simp] lemma toLinearEquiv_toSpanSingletonLIE :
    (toSpanSingletonLIE 𝕜 E).toLinearEquiv = toSpanSingletonLE 𝕜 𝕜 E := rfl

/--
lemma `toContinuousLinearEquiv_toSpanSingletonLIE` / 引理 `toContinuousLinearEquiv_toSpanSingletonLIE`

English:
lemma toContinuousLinearEquiv_toSpanSingletonLIE
  proof: rfl

@[deprecated "Use the reverse of `toSpanSingletonLE`." (since := "2026-05-21")]
alias ring_lmap_equiv_selfₗ := toSpanSingletonLE

@[deprecated "Use the reverse of `toSpanSingletonLIE`." (since := "2026-05-21")]
alias ring_lmap_equiv_self := toSpanSingletonLIE

中文:
引理 toContinuousLinearEquiv_toSpanSingletonLIE
  证明: rfl

@[deprecated "Use the reverse of `toSpanSingletonLE`." (since := "2026-05-21")]
alias ring_lmap_equiv_selfₗ := toSpanSingletonLE

@[deprecated "Use the reverse of `toSpanSingletonLIE`." (since := "2026-05-21")]
alias ring_lmap_equiv_self := toSpanSingletonLIE
-/
@[simp] lemma toContinuousLinearEquiv_toSpanSingletonLIE :
    (toSpanSingletonLIE 𝕜 E).toContinuousLinearEquiv = toSpanSingletonCLE := rfl

@[deprecated "Use the reverse of `toSpanSingletonLE`." (since := "2026-05-21")]
alias ring_lmap_equiv_selfₗ := toSpanSingletonLE

@[deprecated "Use the reverse of `toSpanSingletonLIE`." (since := "2026-05-21")]
alias ring_lmap_equiv_self := toSpanSingletonLIE

end RingEquiv

end MultiplicationLinear

section SMulLinear

variable (𝕜) (R : Type*) [SeminormedRing R]
variable [NormedAlgebra 𝕜 R] [Module R E] [IsBoundedSMul R E] [IsScalarTower 𝕜 R E]

/--
Definition of `lsmul` / `lsmul` 的定义

English:
definition lsmul
  signature: : R ->L[𝕜] E ->L[𝕜] E
  body: ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : R ->ₗ[𝕜] E ->ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using! norm_smul_le c x

@[simp]

中文:
定义 lsmul
  签名: : R ->L[𝕜] E ->L[𝕜] E
  定义体: ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : R ->ₗ[𝕜] E ->ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using! norm_smul_le c x

@[simp]

Depends on / 依赖: Algebra, Algebra.lsmul, norm_smul_le, one_mul, toLinearMap
-/
def lsmul : R ->L[𝕜] E ->L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : R ->ₗ[𝕜] E ->ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using! norm_smul_le c x

@[simp]
/--
theorem `lsmul_apply` / 定理 `lsmul_apply`

English:
theorem lsmul_apply
  given: (c : R) (x : E)
  statement: lsmul 𝕜 R c x = c • x
  proof: rfl

中文:
定理 lsmul_apply
  条件: (c : R) (x : E)
  结论: lsmul 𝕜 R c x = c • x
  证明: rfl
-/
theorem lsmul_apply (c : R) (x : E) : lsmul 𝕜 R c x = c • x :=
  rfl

variable {𝕜} in
@[simp]
/--
theorem `lsmul_flip_apply` / 定理 `lsmul_flip_apply`

English:
theorem lsmul_flip_apply
  given: (x : E)
  proof: rfl

中文:
定理 lsmul_flip_apply
  条件: (x : E)
  证明: rfl
-/
theorem lsmul_flip_apply (x : E) :
    (lsmul 𝕜 𝕜).flip x = toSpanSingleton 𝕜 x :=
  rfl

variable {𝕜} in
/--
theorem `lsmul_flip_inj` / 定理 `lsmul_flip_inj`

English:
theorem lsmul_flip_inj
  given: {x y : E}
  proof: ⟨fun h => by simpa using congr($h 1), fun h => h ▸ rfl⟩

中文:
定理 lsmul_flip_inj
  条件: {x y : E}
  证明: ⟨fun h => by simpa using congr($h 1), fun h => h ▸ rfl⟩
-/
theorem lsmul_flip_inj {x y : E} :
    (lsmul 𝕜 R).flip x = (lsmul 𝕜 R).flip y ↔ x = y :=
  ⟨fun h => by simpa using congr($h 1), fun h => h ▸ rfl⟩

variable {R 𝕜}

/--
theorem `opNorm_lsmul_apply_le` / 定理 `opNorm_lsmul_apply_le`

English:
theorem opNorm_lsmul_apply_le
  given: (x : R)
  statement: ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖ <= ‖x‖
  proof: ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y

中文:
定理 opNorm_lsmul_apply_le
  条件: (x : R)
  结论: ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖ <= ‖x‖
  证明: ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, norm_nonneg, norm_smul_le, opNorm_le_bound
-/
theorem opNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖ <= ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y

/--
theorem `opNNNorm_lsmul_apply_le` / 定理 `opNNNorm_lsmul_apply_le`

English:
theorem opNNNorm_lsmul_apply_le
  given: (x : R)
  statement: ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖₊ <= ‖x‖₊
  proof: ContinuousLinearMap.opNNNorm_le_bound _ _ fun y => nnnorm_smul_le x y

中文:
定理 opNNNorm_lsmul_apply_le
  条件: (x : R)
  结论: ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖₊ <= ‖x‖₊
  证明: ContinuousLinearMap.opNNNorm_le_bound _ _ fun y => nnnorm_smul_le x y

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNNNorm_le_bound, nnnorm_smul_le, opNNNorm_le_bound
-/
theorem opNNNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖₊ <= ‖x‖₊ :=
  ContinuousLinearMap.opNNNorm_le_bound _ _ fun y => nnnorm_smul_le x y

/--
theorem `opNorm_lsmul_le` / 定理 `opNorm_lsmul_le`

English:
theorem opNorm_lsmul_le
  statement: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ <= 1
  proof: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

中文:
定理 opNorm_lsmul_le
  结论: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ <= 1
  证明: LinearMap.mkContinuous₂_norm_le _ zero_le_one _

Depends on / 依赖: LinearMap, LinearMap.mkContinuous, zero_le_one
-/
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ <= 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/--
theorem `opNNNorm_lsmul_le` / 定理 `opNNNorm_lsmul_le`

English:
theorem opNNNorm_lsmul_le
  statement: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖₊ <= 1
  proof: by
  rw [← NNReal.coe_le_coe]
  simpa using opNorm_lsmul_le

中文:
定理 opNNNorm_lsmul_le
  结论: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖₊ <= 1
  证明: by
  rw [← NNReal.coe_le_coe]
  simpa using opNorm_lsmul_le

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, opNorm_lsmul_le
-/
theorem opNNNorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖₊ <= 1 := by
  rw [← NNReal.coe_le_coe]
  simpa using opNorm_lsmul_le

/--
theorem `opENorm_lsmul_le` / 定理 `opENorm_lsmul_le`

English:
theorem opENorm_lsmul_le
  statement: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ₑ <= 1
  proof: by
  rw [enorm_eq_nnnorm]
  simpa using opNNNorm_lsmul_le

中文:
定理 opENorm_lsmul_le
  结论: ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ₑ <= 1
  证明: by
  rw [enorm_eq_nnnorm]
  simpa using opNNNorm_lsmul_le

Depends on / 依赖: enorm_eq_nnnorm, opNNNorm_lsmul_le
-/
theorem opENorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ₑ <= 1 := by
  rw [enorm_eq_nnnorm]
  simpa using opNNNorm_lsmul_le

end SMulLinear

end ContinuousLinearMap

end SemiNormed

section Normed

namespace ContinuousLinearMap

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable (𝕜) (R : Type*)

section

variable [NonUnitalNormedRing R] [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R]
variable [SMulCommClass 𝕜 R R] [RegularNormedAlgebra 𝕜 R] [Nontrivial R]

@[simp]
/--
theorem `opNorm_mul` / 定理 `opNorm_mul`

English:
theorem opNorm_mul
  statement: ‖mul 𝕜 R‖ = 1
  proof: (mulₗᵢ 𝕜 R).norm_toContinuousLinearMap

@[simp]

中文:
定理 opNorm_mul
  结论: ‖mul 𝕜 R‖ = 1
  证明: (mulₗᵢ 𝕜 R).norm_toContinuousLinearMap

@[simp]

Depends on / 依赖: norm_toContinuousLinearMap
-/
theorem opNorm_mul : ‖mul 𝕜 R‖ = 1 :=
  (mulₗᵢ 𝕜 R).norm_toContinuousLinearMap

@[simp]
/--
theorem `opNNNorm_mul` / 定理 `opNNNorm_mul`

English:
theorem opNNNorm_mul
  statement: ‖mul 𝕜 R‖₊ = 1
  proof: Subtype.ext opNorm_mul 𝕜 R

@[simp]

中文:
定理 opNNNorm_mul
  结论: ‖mul 𝕜 R‖₊ = 1
  证明: Subtype.ext opNorm_mul 𝕜 R

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, opNorm_mul
-/
theorem opNNNorm_mul : ‖mul 𝕜 R‖₊ = 1 :=
Subtype.ext opNorm_mul 𝕜 R

@[simp]
/--
theorem `opENorm_mul` / 定理 `opENorm_mul`

English:
theorem opENorm_mul
  statement: ‖mul 𝕜 R‖ₑ = 1
  proof: by
  simp [enorm_eq_nnnorm]

中文:
定理 opENorm_mul
  结论: ‖mul 𝕜 R‖ₑ = 1
  证明: by
  simp [enorm_eq_nnnorm]

Depends on / 依赖: enorm_eq_nnnorm
-/
theorem opENorm_mul : ‖mul 𝕜 R‖ₑ = 1 := by
  simp [enorm_eq_nnnorm]

end

/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_le` as an equality. -/
@[simp]
/--
theorem `opNorm_lsmul` / 定理 `opNorm_lsmul`

English:
theorem opNorm_lsmul
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
  proof: by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa using le_of_opNorm_le _ (h 1) y

@[simp]

中文:
定理 opNorm_lsmul
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E] [NormSMul类 R E]
  证明: by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa using le_of_opNorm_le _ (h 1) y

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_eq_of_bounds, exists_ne, le_of_mul_le_mul_right, le_of_opNorm_le, norm_pos_iff, norm_pos_iff.mpr, one_mul, opNorm_eq_of_bounds, opNorm_lsmul_apply_le, zero_le_one
-/
theorem opNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa using le_of_opNorm_le _ (h 1) y

@[simp]
/--
theorem `opNNNorm_lsmul` / 定理 `opNNNorm_lsmul`

English:
theorem opNNNorm_lsmul
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
  proof: by
  rw [← NNReal.coe_inj]
  simp

@[simp]

中文:
定理 opNNNorm_lsmul
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E] [NormSMul类 R E]
  证明: by
  rw [← NNReal.coe_inj]
  simp

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_inj, coe_inj
-/
theorem opNNNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖₊ = 1 := by
  rw [← NNReal.coe_inj]
  simp

@[simp]
/--
theorem `opENorm_lsmul` / 定理 `opENorm_lsmul`

English:
theorem opENorm_lsmul
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
  proof: by
  simp [enorm_eq_nnnorm]

中文:
定理 opENorm_lsmul
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E] [NormSMul类 R E]
  证明: by
  simp [enorm_eq_nnnorm]

Depends on / 依赖: enorm_eq_nnnorm
-/
theorem opENorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ₑ = 1 := by
  simp [enorm_eq_nnnorm]

/-- The norm of `lsmul x` equals `‖x‖` in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_apply_le` as an equality. -/
@[simp]
/--
theorem `opNorm_lsmul_apply` / 定理 `opNorm_lsmul_apply`

English:
theorem opNorm_lsmul_apply
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
  proof: by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · simp [norm_smul]
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa [norm_smul] using h y

@[simp]

中文:
定理 opNorm_lsmul_apply
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E]
  证明: by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · simp [norm_smul]
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa [norm_smul] using h y

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_eq_of_bounds, exists_ne, le_of_mul_le_mul_right, norm_nonneg, norm_pos_iff, norm_pos_iff.mpr, norm_smul, opNorm_eq_of_bounds
-/
theorem opNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E ->L[𝕜] E)‖ = ‖a‖ := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · simp [norm_smul]
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa [norm_smul] using h y

@[simp]
/--
theorem `opNNNorm_lsmul_apply` / 定理 `opNNNorm_lsmul_apply`

English:
theorem opNNNorm_lsmul_apply
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
  proof: by
  rw [← NNReal.coe_inj]
  simp

@[simp]

中文:
定理 opNNNorm_lsmul_apply
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E]
  证明: by
  rw [← NNReal.coe_inj]
  simp

@[simp]

Depends on / 依赖: NNReal, NNReal.coe_inj, coe_inj
-/
theorem opNNNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E ->L[𝕜] E)‖₊ = ‖a‖₊ := by
  rw [← NNReal.coe_inj]
  simp

@[simp]
/--
theorem `opENorm_lsmul_apply` / 定理 `opENorm_lsmul_apply`

English:
theorem opENorm_lsmul_apply
  statement: [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
  proof: by
  simp [enorm_eq_nnnorm]

中文:
定理 opENorm_lsmul_apply
  结论: [NormedDivision环 R] [赋范代数 𝕜 R] [模 R E]
  证明: by
  simp [enorm_eq_nnnorm]

Depends on / 依赖: enorm_eq_nnnorm
-/
theorem opENorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E ->L[𝕜] E)‖ₑ = ‖a‖ₑ := by
  simp [enorm_eq_nnnorm]

end ContinuousLinearMap

end Normed
