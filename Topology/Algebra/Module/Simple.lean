/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The kernel of a linear function is closed or dense

In this file we prove (`LinearMap.isClosed_or_dense_ker`) that the kernel of a linear function
`f : M →ₗ[R] N` is either closed or dense in `M` provided that `N` is a simple module over `R`. This
applies, e.g., to the case when `R = N` is a division ring.
-/

public section


universe u v w

variable {R : Type u} {M : Type v} {N : Type w} [Ring R] [TopologicalSpace R] [TopologicalSpace M]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [ContinuousSMul R M] [Module R N] [ContinuousAdd M]
  [IsSimpleModule R N]

/-- The kernel of a linear map taking values in a simple module over the base ring is closed or
dense. Applies, e.g., to the case when `R = N` is a division ring. -/
/-
**LinearMap.isClosed_or_dense_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isClosed_or_dense_ker (l : M ->ₗ[R] N) : IsClosed (LinearMap.ker
 l : Set M) ∨ Dense (LinearMap.ker l : Set M)
参数：l : M ->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.surjective_or_eq_zero`：surjective_or_eq_zero [IsSimpleModule R
 N] (f : M ->ₗ[R] N) : Function.Surjective f ∨ f = 0
· 使用定理 `Submodule.isClosed_or_dense_of_isCoatom`：Submodule.isClosed_or_dense_of_
isCoatom (s : Submodule R M) (hs : IsCoatom s) : IsClosed (s : Set M) ∨ Dense (s
 : Set M)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `LinearMap.isCoatom_ker_of_surjective`：isCoatom_ker_of_surjective [IsSimp
leModule R N] {f : M ->ₗ[R] N} (hf : Function.Surjective f) : IsCoatom (LinearMa
p.ker f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The kernel of a linear map taking values in a simple module over the base ring i
s closed or
dense. Applies, e.g., to the case when `R = N` is a division ring.
-/
theorem LinearMap.isClosed_or_dense_ker (l : M →ₗ[R] N) :
    IsClosed (LinearMap.ker l : Set M) ∨ Dense (LinearMap.ker l : Set M) := by
  rcases l.surjective_or_eq_zero with (hl | rfl)
  · exact (LinearMap.ker l).isClosed_or_dense_of_isCoatom (LinearMap.isCoatom_ker_of_surjective hl)
  · rw [LinearMap.ker_zero]
    left
    exact isClosed_univ
