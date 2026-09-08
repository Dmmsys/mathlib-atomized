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

/-- Multiplication in a non-unital normed algebra as a continuous bilinear map. -/
/-
**ContinuousLinearMap.mul** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：mul : R ->L[𝕜] R ->L[𝕜] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication in a non-unital normed algebra as a continuous bilinear map.
-/
def mul : R →L[𝕜] R →L[𝕜] R :=
  (LinearMap.mul 𝕜 R).mkContinuous₂ 1 fun x y => by simpa using norm_mul_le x y

@[simp]
/-
**ContinuousLinearMap.mul_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：mul_apply' (x y : R) : mul 𝕜 R x y = x * y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem mul_apply' (x y : R) : mul 𝕜 R x y = x * y :=
  rfl

@[simp]
/-
**ContinuousLinearMap.opNorm_mul_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：opNorm_mul_apply_le (x : R) : ‖mul 𝕜 R x‖ <= ‖x‖
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem opNorm_mul_apply_le (x : R) : ‖mul 𝕜 R x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (norm_mul_le x)
/-
**ContinuousLinearMap.opNorm_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opNorm_mul_le : ‖mul 𝕜 R‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem opNorm_mul_le : ‖mul 𝕜 R‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

/-- Multiplication on the left in a non-unital normed algebra `R` as a non-unital algebra
homomorphism into the algebra of *continuous* linear maps. This is the left regular representation
of `A` acting on itself.

This has more algebraic structure than `ContinuousLinearMap.mul`, but there is no longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism into *continuous*
linear maps. -/
/-
**ContinuousLinearMap._root_.NonUnitalAlgHom.Lmul** 是 Mathlib 中的一个定义，位于命名空间 `Con
tinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication on the left in a non-unital normed algebra `R` as a non-unital al
gebra
homomorphism into the algebra of *continuous* linear maps. This is the left regu
lar representation
of `A` acting on itself.

This has more algebraic structure than `ContinuousLinearMap.mul`, but there is n
o longer continuity
bundled in the first coordinate.  An alternative viewpoint is that this upgrades
`NonUnitalAlgHom.lmul` from a homomorphism into linear maps to a homomorphism in
to *continuous*
linear maps.
-/
def _root_.NonUnitalAlgHom.Lmul : R →ₙₐ[𝕜] R →L[𝕜] R :=
  { mul 𝕜 R with
    map_mul' := fun _ _ ↦ ext fun _ ↦ mul_assoc _ _ _
    map_zero' := ext fun _ ↦ zero_mul _ }

variable {𝕜 R} in
@[simp]
/-
**ContinuousLinearMap._root_.NonUnitalAlgHom.coe_Lmul** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NonUnitalAlgHom.coe_Lmul : ⇑(NonUnitalAlgHom.Lmul 𝕜 R) = mul 𝕜 R :=
  rfl

/-- Simultaneous left- and right-multiplication in a non-unital normed algebra, considered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried. -/
/-
**ContinuousLinearMap.mulLeftRight** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：mulLeftRight : R ->L[𝕜] R ->L[𝕜] R ->L[𝕜] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Simultaneous left- and right-multiplication in a non-unital normed algebra, cons
idered as a
continuous trilinear map. This is akin to its non-continuous version `LinearMap.
mulLeftRight`,
but there is a minor difference: `LinearMap.mulLeftRight` is uncurried.
-/
def mulLeftRight : R →L[𝕜] R →L[𝕜] R →L[𝕜] R :=
  ((compL 𝕜 R R R).comp (mul 𝕜 R).flip).flip.comp (mul 𝕜 R)

@[simp]
/-
**ContinuousLinearMap.mulLeftRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：mulLeftRight_apply (x y z : R) : mulLeftRight 𝕜 R x y z = x * z * y
参数：x y z : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem mulLeftRight_apply (x y z : R) : mulLeftRight 𝕜 R x y z = x * z * y :=
  rfl
/-
**ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousLinearMap`。
形式化陈述：opNorm_mulLeftRight_apply_apply_le (x y : R) : ‖mulLeftRight 𝕜 R x y‖ <= ‖
x‖ * ‖y‖
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousLinearMap.opNorm_mul_apply_le`：opNorm_mul_apply_le (x : R) : ‖
mul 𝕜 R x‖ <= ‖x‖
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
-/
theorem opNorm_mulLeftRight_apply_apply_le (x y : R) : ‖mulLeftRight 𝕜 R x y‖ ≤ ‖x‖ * ‖y‖ :=
  (opNorm_comp_le _ _).trans <|
    (mul_comm _ _).trans_le <|
      mul_le_mul (opNorm_mul_apply_le _ _ _)
        (opNorm_le_bound _ (norm_nonneg _) fun _ => (norm_mul_le _ _).trans_eq (mul_comm _ _))
        (norm_nonneg _) (norm_nonneg _)
/-
**ContinuousLinearMap.opNorm_mulLeftRight_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：opNorm_mulLeftRight_apply_le (x : R) : ‖mulLeftRight 𝕜 R x‖ <= ‖x‖
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le`：opNorm_mulLeftRi
ght_apply_apply_le (x y : R) : ‖mulLeftRight 𝕜 R x y‖ <= ‖x‖ * ‖y‖
-/
theorem opNorm_mulLeftRight_apply_le (x : R) : ‖mulLeftRight 𝕜 R x‖ ≤ ‖x‖ :=
  opNorm_le_bound _ (norm_nonneg x) (opNorm_mulLeftRight_apply_apply_le 𝕜 R x)
/-
**ContinuousLinearMap.opNorm_mulLeftRight_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：opNorm_mulLeftRight_le : ‖mulLeftRight 𝕜 R‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `ContinuousLinearMap.opNorm_mulLeftRight_apply_le`：opNorm_mulLeftRight_ap
ply_le (x : R) : ‖mulLeftRight 𝕜 R x‖ <= ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem opNorm_mulLeftRight_le :
    ‖mulLeftRight 𝕜 R‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => (one_mul ‖x‖).symm ▸ opNorm_mulLeftRight_apply_le 𝕜 R x


/-- This is a mixin class for non-unital normed algebras which states that the left-regular
representation of the algebra on itself is isometric. Every unital normed algebra with `‖1‖ = 1` is
a regular normed algebra (see `NormedAlgebra.instRegularNormedAlgebra`). In addition, so is every
C⋆-algebra, non-unital included (see `CStarRing.instRegularNormedAlgebra`), but there are yet other
examples. Any algebra with an approximate identity (e.g., `L¹`) is also regular.

This is a useful class because it gives rise to a nice norm on the unitization; in particular it is
a C⋆-norm when the norm on `A` is a C⋆-norm. -/
/-
**ContinuousLinearMap._root_.RegularNormedAlgebra** 是 Mathlib 中的一个类，位于命名空间 `Cont
inuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a mixin class for non-unital normed algebras which states that the left-
regular
representation of the algebra on itself is isometric. Every unital normed algebr
a with `‖1‖ = 1` is
a regular normed algebra (see `NormedAlgebra.instRegularNormedAlgebra`). In addi
tion, so is every
C⋆-algebra, non-unital included (see `CStarRing.instRegularNormedAlgebra`), but 
there are yet other
examples. Any algebra with an approximate identity (e.g., `L¹`) is also regular.

This is a useful class because it gives rise to a nice norm on the unitization; 
in particular it is
a C⋆-norm when the norm on `A` is a C⋆-norm.
-/
class _root_.RegularNormedAlgebra : Prop where
  /-- The left regular representation of the algebra on itself is an isometry. -/
  isometry_mul' : Isometry (mul 𝕜 R)

/-- Every (unital) normed algebra such that `‖1‖ = 1` is a `RegularNormedAlgebra`. -/
/-
**ContinuousLinearMap._root_.NormedAlgebra.instRegularNormedAlgebra** 是 Mathlib 
中的一个实例，位于命名空间 `ContinuousLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every (unital) normed algebra such that `‖1‖ = 1` is a `RegularNormedAlgebra`.
-/
instance _root_.NormedAlgebra.instRegularNormedAlgebra {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing R] [NormedAlgebra 𝕜 R] [NormOneClass R] : RegularNormedAlgebra 𝕜 R where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 R) <|
    fun x => le_antisymm (opNorm_mul_apply_le _ _ _) <| by
      convert! ratio_le_opNorm ((mul 𝕜 R) x) (1 : R)
      simp [norm_one]

variable [RegularNormedAlgebra 𝕜 R]
/-
**ContinuousLinearMap.isometry_mul** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：isometry_mul : Isometry (mul 𝕜 R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RegularNormedAlgebra.isometry_mul'`：∀ {𝕜 : Type u_1} {inst : Nontriviall
yNormedField 𝕜} {R : Type u_3} {inst_1 : NonUnitalSeminormedRing R}   {inst_2 : 
NormedSpace 𝕜 R} {inst_3…
-/
lemma isometry_mul : Isometry (mul 𝕜 R) :=
  RegularNormedAlgebra.isometry_mul'

@[simp]
/-
**ContinuousLinearMap.opNorm_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖ = ‖x‖
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `AddMonoidHomClass.isometry_iff_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F 
: Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [ins
t_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `ContinuousLinearMap.isometry_mul`：isometry_mul : Isometry (mul 𝕜 R)
-/
lemma opNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖ = ‖x‖ :=
  (AddMonoidHomClass.isometry_iff_norm (mul 𝕜 R)).mp (isometry_mul 𝕜 R) x

@[simp]
/-
**ContinuousLinearMap.opNNNorm_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：opNNNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖₊ = ‖x‖₊
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `ContinuousLinearMap.opNorm_mul_apply`：opNorm_mul_apply (x : R) : ‖mul 𝕜 
R x‖ = ‖x‖
-/
lemma opNNNorm_mul_apply (x : R) : ‖mul 𝕜 R x‖₊ = ‖x‖₊ :=
  Subtype.ext <| opNorm_mul_apply 𝕜 R x

/-- Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps. -/
/-
**ContinuousLinearMap.mul** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：mul : R ->L[𝕜] R ->L[𝕜] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication in a normed algebra as a linear isometry to the space of
continuous linear maps.
-/
def mulₗᵢ : R →ₗᵢ[𝕜] R →L[𝕜] R where
  toLinearMap := mul 𝕜 R
  norm_map' x := opNorm_mul_apply 𝕜 R x

@[simp]
/-
**ContinuousLinearMap.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁ : Type u_4} [inst_1 : Topologic
alSpace M₁] [inst_2 : AddCommMonoid M₁]   [inst_3 : _root_.Module R₁ M₁] (f g : 
M₁ →L[R₁] M₁), ↑(f * g) = ↑f * ↑g
参数：f g : M₁ →L[R₁] M₁；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.toLinearMap_mul`：toLinearMap_mul (f g : M₁ ->L[R₁] M
₁) : (↑(f * g) : M₁ ->ₗ[R₁] M₁) = f * g
-/
theorem coe_mulₗᵢ : ⇑(mulₗᵢ 𝕜 R) = mul 𝕜 R :=
  rfl

end NonUnital

section NonUnitalSeminormedCommRing
variable {R : Type*} [NonUnitalSeminormedCommRing R] [NormedSpace 𝕜 R] [IsScalarTower 𝕜 R R]
  [SMulCommClass 𝕜 R R]

/-
**ContinuousLinearMap.flip_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {R : Type u_3} [inst_1
 : NonUnitalSeminormedCommRing R]   [inst_2 : NormedSpace 𝕜 R] [inst_3 : IsScala
rTower 𝕜 R R] [inst_4 : SMulCommClass 𝕜 R R],   (ContinuousLinearMap.mul 𝕜 R).fl
ip = ContinuousLinearMap.mul 𝕜 R
参数：ContinuousLinearMap.mul 𝕜 R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma flip_mul : (ContinuousLinearMap.mul 𝕜 R).flip = .mul 𝕜 R := by ext; simp [mul_comm]

end NonUnitalSeminormedCommRing

section RingEquiv

variable (𝕜 E)

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
/-
**ContinuousLinearMap.toSpanSingletonLIE** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：toSpanSingletonLIE : E ≃ₗᵢ[𝕜] (𝕜 ->L[𝕜] E) where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearl
y isometrically
equivalent to `M`.
-/
def toSpanSingletonLIE : E ≃ₗᵢ[𝕜] (𝕜 →L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE 𝕜 𝕜 E
  norm_map' _ := by simp

@[simp]
/-
**ContinuousLinearMap.toSpanSingletonLIE_apply** 是 Mathlib 中的一个引理，位于命名空间 `Contin
uousLinearMap`。
形式化陈述：toSpanSingletonLIE_apply (x : E) : toSpanSingletonLIE 𝕜 E x = toSpanSingle
ton 𝕜 x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma toSpanSingletonLIE_apply (x : E) : toSpanSingletonLIE 𝕜 E x = toSpanSingleton 𝕜 x := rfl
/-
**ContinuousLinearMap.toSpanSingletonLIE_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) [inst : NontriviallyNormedField 𝕜] [inst_1
 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] (f : 𝕜 →L[𝕜] E), (Cont
inuousLinearMap.toSpanSingletonLIE 𝕜 E).symm f = f 1
参数：𝕜 : Type u_1；E : Type u_2；f : 𝕜 →L[𝕜] E；ContinuousLinearMap.toSpanSingletonLI
E 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
@[simp] lemma toSpanSingletonLIE_symm_apply (f : 𝕜 →L[𝕜] E) :
    (toSpanSingletonLIE 𝕜 E).symm f = f 1 := rfl
/-
**ContinuousLinearMap.toLinearEquiv_toSpanSingletonLIE** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) [inst : NontriviallyNormedField 𝕜] [inst_1
 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E],   (ContinuousLinearMa
p.toSpanSingletonLIE 𝕜 E).toLinearEquiv = ContinuousLinearMap.toSpanSingletonLE 
𝕜 𝕜 E
参数：𝕜 : Type u_1；E : Type u_2；ContinuousLinearMap.toSpanSingletonLIE 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
@[simp] lemma toLinearEquiv_toSpanSingletonLIE :
    (toSpanSingletonLIE 𝕜 E).toLinearEquiv = toSpanSingletonLE 𝕜 𝕜 E := rfl
/-
**ContinuousLinearMap.toContinuousLinearEquiv_toSpanSingletonLIE** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ (𝕜 : Type u_1) (E : Type u_2) [inst : NontriviallyNormedField 𝕜] [inst_1
 : SeminormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E], ↑(ContinuousLinearMap
.toSpanSingletonLIE 𝕜 E) = ContinuousLinearMap.toSpanSingletonCLE
参数：𝕜 : Type u_1；E : Type u_2；ContinuousLinearMap.toSpanSingletonLIE 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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

/-- Scalar multiplication as a continuous bilinear map. -/
/-
**ContinuousLinearMap.lsmul** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：lsmul : R ->L[𝕜] E ->L[𝕜] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication as a continuous bilinear map.
-/
def lsmul : R →L[𝕜] E →L[𝕜] E :=
  ((Algebra.lsmul 𝕜 𝕜 E).toLinearMap : R →ₗ[𝕜] E →ₗ[𝕜] E).mkContinuous₂ 1 fun c x => by
    simpa only [one_mul] using! norm_smul_le c x

@[simp]
/-
**ContinuousLinearMap.lsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：lsmul_apply (c : R) (x : E) : lsmul 𝕜 R c x = c • x
参数：c : R；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem lsmul_apply (c : R) (x : E) : lsmul 𝕜 R c x = c • x :=
  rfl

variable {𝕜} in
@[simp]
/-
**ContinuousLinearMap.lsmul_flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：lsmul_flip_apply (x : E) : (lsmul 𝕜 𝕜).flip x = toSpanSingleton 𝕜 x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem lsmul_flip_apply (x : E) :
    (lsmul 𝕜 𝕜).flip x = toSpanSingleton 𝕜 x :=
  rfl

variable {𝕜} in
/-
**ContinuousLinearMap.lsmul_flip_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：lsmul_flip_inj {x y : E} : (lsmul 𝕜 R).flip x = (lsmul 𝕜 R).flip y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem lsmul_flip_inj {x y : E} :
    (lsmul 𝕜 R).flip x = (lsmul 𝕜 R).flip y ↔ x = y :=
  ⟨fun h => by simpa using congr($h 1), fun h => h ▸ rfl⟩

variable {R 𝕜}
/-
**ContinuousLinearMap.opNorm_lsmul_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：opNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖ <= ‖x‖
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
-/
theorem opNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E →L[𝕜] E)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun y => norm_smul_le x y
/-
**ContinuousLinearMap.opNNNorm_lsmul_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：opNNNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖₊ <= ‖x‖₊
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNNNorm_le_bound`：opNNNorm_le_bound (f : E ->SL[σ₁₂
] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
-/
theorem opNNNorm_lsmul_apply_le (x : R) : ‖(lsmul 𝕜 R x : E →L[𝕜] E)‖₊ ≤ ‖x‖₊ :=
  ContinuousLinearMap.opNNNorm_le_bound _ _ fun y => nnnorm_smul_le x y

/-- The norm of `lsmul` is at most 1 in any semi-normed group. -/
/-
**ContinuousLinearMap.opNorm_lsmul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：opNorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mkContinuous₂_norm_le`：mkContinuous₂_norm_le (f : E ->ₛₗ[σ₁₃] 
F ->ₛₗ[σ₂₃] G) {C : Real} (h0 : 0 <= C) (hC : forall x y, ‖f x y‖ <= C * ‖x‖ * ‖
y‖) : ‖f.mkContinuous…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
The norm of `lsmul` is at most 1 in any semi-normed group.
-/
theorem opNorm_lsmul_le : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _
/-
**ContinuousLinearMap.opNNNorm_lsmul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：opNNNorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖₊ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_le`：opNorm_lsmul_le : ‖(lsmul 𝕜 R : R -
>L[𝕜] E ->L[𝕜] E)‖ <= 1
-/
theorem opNNNorm_lsmul_le : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe]
  simpa using opNorm_lsmul_le
/-
**ContinuousLinearMap.opENorm_lsmul_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：opENorm_lsmul_le : ‖(lsmul 𝕜 R : R ->L[𝕜] E ->L[𝕜] E)‖ₑ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_eq_nnnorm`：enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊
· 使用定理 `ContinuousLinearMap.opNNNorm_lsmul_le`：opNNNorm_lsmul_le : ‖(lsmul 𝕜 R :
 R ->L[𝕜] E ->L[𝕜] E)‖₊ <= 1
-/
theorem opENorm_lsmul_le : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ₑ ≤ 1 := by
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
/-
**ContinuousLinearMap.opNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：opNorm_mul : ‖mul 𝕜 R‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometry.norm_toContinuousLinearMap`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u
_3} {E : Type u_5} {F : Type u_6} [inst : SeminormedAddCommGroup E]   [inst_1 : 
SeminormedAddCommGroup F] [inst…
· 使用定理 `EMetric.instNontrivialTopologyOfNontrivial`：∀ {α : Type u_2} [inst : EMe
tricSpace α] [Nontrivial α], NontrivialTopology α
-/
theorem opNorm_mul : ‖mul 𝕜 R‖ = 1 :=
  (mulₗᵢ 𝕜 R).norm_toContinuousLinearMap

@[simp]
/-
**ContinuousLinearMap.opNNNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：opNNNorm_mul : ‖mul 𝕜 R‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.opNorm_mul`：opNorm_mul : ‖mul 𝕜 R‖ = 1
-/
theorem opNNNorm_mul : ‖mul 𝕜 R‖₊ = 1 :=
  Subtype.ext <| opNorm_mul 𝕜 R

@[simp]
/-
**ContinuousLinearMap.opENorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：opENorm_mul : ‖mul 𝕜 R‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNNNorm_mul`：opNNNorm_mul : ‖mul 𝕜 R‖₊ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opENorm_mul : ‖mul 𝕜 R‖ₑ = 1 := by
  simp [enorm_eq_nnnorm]

end

/-- The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_le` as an equality. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMa
p`。
形式化陈述：opNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [Norm
SMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E -
>L[𝕜] E)‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {φ : E ->SL
[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (
h_below : forall N >= 0, (for…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_apply_le`：opNorm_lsmul_apply_le (x : R)
 : ‖(lsmul 𝕜 R x : E ->L[𝕜] E)‖ <= ‖x‖
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
The norm of `lsmul` equals 1 in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_le` as an equality.
-/
theorem opNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ = 1 := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one (fun x => ?_) fun N _ h => ?_
  · rw [one_mul]
    apply opNorm_lsmul_apply_le
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa using le_of_opNorm_le _ (h 1) y

@[simp]
/-
**ContinuousLinearMap.opNNNorm_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：opNNNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [No
rmSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E
 ->L[𝕜] E)‖₊ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.opNorm_lsmul`：opNorm_lsmul [NormedDivisionRing R] [N
ormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontri
vial E] : ‖(lsmul 𝕜 R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNNNorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖₊ = 1 := by
  rw [← NNReal.coe_inj]
  simp

@[simp]
/-
**ContinuousLinearMap.opENorm_lsmul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：opENorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [Nor
mSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R ->L[𝕜] E 
->L[𝕜] E)‖ₑ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNNNorm_lsmul`：opNNNorm_lsmul [NormedDivisionRing R
] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E] [IsScalarTower 𝕜 R E] [No
ntrivial E] : ‖(lsmul 𝕜 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opENorm_lsmul [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E]
    [IsScalarTower 𝕜 R E] [Nontrivial E] : ‖(lsmul 𝕜 R : R →L[𝕜] E →L[𝕜] E)‖ₑ = 1 := by
  simp [enorm_eq_nnnorm]

/-- The norm of `lsmul x` equals `‖x‖` in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_apply_le` as an equality. -/
@[simp]
/-
**ContinuousLinearMap.opNorm_lsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：opNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
 [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} : ‖(lsmul 𝕜 R 
a : E ->L[𝕜] E)‖ = ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {φ : E ->SL
[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (
h_below : forall N >= 0, (for…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
The norm of `lsmul x` equals `‖x‖` in any nontrivial normed group.

This is `ContinuousLinearMap.opNorm_lsmul_apply_le` as an equality.
-/
theorem opNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E →L[𝕜] E)‖ = ‖a‖ := by
  refine ContinuousLinearMap.opNorm_eq_of_bounds (norm_nonneg _) (fun x => ?_) fun N _ h => ?_
  · simp [norm_smul]
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hy)
  simpa [norm_smul] using h y

@[simp]
/-
**ContinuousLinearMap.opNNNorm_lsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：opNNNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R 
E] [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} : ‖(lsmul 𝕜 
R a : E ->L[𝕜] E)‖₊ = ‖a‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.opNorm_lsmul_apply`：opNorm_lsmul_apply [NormedDivisi
onRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E] [IsScalarTower 𝕜 
R E] [Nontrivial E] {a : R} …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opNNNorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E →L[𝕜] E)‖₊ = ‖a‖₊ := by
  rw [← NNReal.coe_inj]
  simp

@[simp]
/-
**ContinuousLinearMap.opENorm_lsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：opENorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E
] [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} : ‖(lsmul 𝕜 R
 a : E ->L[𝕜] E)‖ₑ = ‖a‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNNNorm_lsmul_apply`：opNNNorm_lsmul_apply [NormedDi
visionRing R] [NormedAlgebra 𝕜 R] [Module R E] [NormSMulClass R E] [IsScalarTowe
r 𝕜 R E] [Nontrivial E] {a : R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem opENorm_lsmul_apply [NormedDivisionRing R] [NormedAlgebra 𝕜 R] [Module R E]
    [NormSMulClass R E] [IsScalarTower 𝕜 R E] [Nontrivial E] {a : R} :
    ‖(lsmul 𝕜 R a : E →L[𝕜] E)‖ₑ = ‖a‖ₑ := by
  simp [enorm_eq_nnnorm]

end ContinuousLinearMap

end Normed

