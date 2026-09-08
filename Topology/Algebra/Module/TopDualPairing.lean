/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.PerfectPairing
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuous Perfect Pairing for `topDualPairing`

This file proves that `topDualPairing 𝕜 E` is a continuous perfect pairing when `E` is a
finite-dimensional Hausdorff space over a complete nontrivially normed field.

## Main results

* `topDualPairing_isContPerfPair`: The `topDualPairing` is a continuous perfect pairing for
  finite-dimensional Hausdorff spaces over complete nontrivially normed fields.
-/

public section

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [T2Space E]

/-- The `topDualPairing` is a continuous perfect pairing for finite-dimensional
Hausdorff spaces over complete nontrivially normed fields. -/
/-
**topDualPairing_isContPerfPair** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：topDualPairing_isContPerfPair : (topDualPairing 𝕜 E).IsContPerfPair where 
continuous_uncurry
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用引理 `isModuleTopologyOfFiniteDimensional`：isModuleTopologyOfFiniteDimensional
 [T2Space E] [FiniteDimensional 𝕜 E] : IsModuleTopology 𝕜 E
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `IsModuleTopology.continuous_bilinear_of_finite_left`：continuous_bilinear
_of_finite_left [Module.Finite R A] (bil : A ->ₗ[R] B ->ₗ[R] C) : Continuous (fu
n ab => bil ab.1 ab.2 : (A × B -> C))
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.flip_bijective_iff₁`：flip_bijective_iff₁ [FiniteDimensional K 
V₁] : Bijective B.flip ↔ Bijective B

--- 原说明 ---
The `topDualPairing` is a continuous perfect pairing for finite-dimensional
Hausdorff spaces over complete nontrivially normed fields.
-/
instance topDualPairing_isContPerfPair : (topDualPairing 𝕜 E).IsContPerfPair where
  continuous_uncurry := by
    have : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
    have : IsModuleTopology 𝕜 (E →L[𝕜] 𝕜) := isModuleTopologyOfFiniteDimensional
    exact IsModuleTopology.continuous_bilinear_of_finite_left (topDualPairing 𝕜 E)
  bijective_left := Function.bijective_id
  bijective_right := by
    refine LinearMap.toContinuousLinearMap.bijective.comp ?_
    rw [LinearMap.flip_bijective_iff₁]
    exact LinearMap.toContinuousLinearMap.symm.bijective
