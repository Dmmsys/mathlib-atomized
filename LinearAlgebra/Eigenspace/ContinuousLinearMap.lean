/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Eigenspaces of continuous linear maps

This file provides some basic properties of eigenspaces of continuous linear maps.

These results are in a separate file to avoid heavy topology imports.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T0Space M]
  [ContinuousConstSMul R M] [IsTopologicalAddGroup M] (f : M →L[R] M) (μ : R) (n : ℕ)

open Module End

/-
**ContinuousLinearMap.isClosed_genEigenspace** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：isClosed_genEigenspace : IsClosed (genEigenspace (f : End R M) μ n : Set M
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousLinearMap.toLinearMap_pow`：toLinearMap_pow (f : M₁ ->L[R₁] M₁)
 (n : Nat) : (↑(f ^ n) : M₁ ->ₗ[R₁] M₁) = f ^ n
· 使用定理 `ContinuousLinearMap.isClosed_ker`：isClosed_ker [T1Space M₂] (f : M₁ ->SL
[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
-/
instance isClosed_genEigenspace : IsClosed (genEigenspace (f : End R M) μ n : Set M) := by
  simpa [genEigenspace_nat] using isClosed_ker ↑((f - μ • 1) ^ n)
/-
**ContinuousLinearMap.isClosed_eigenspace** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：isClosed_eigenspace : IsClosed (eigenspace (f : End R M) μ : Set M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isClosed_eigenspace : IsClosed (eigenspace (f : End R M) μ : Set M) :=
  isClosed_genEigenspace f μ 1

end ContinuousLinearMap

