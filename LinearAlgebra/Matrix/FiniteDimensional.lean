/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The finite-dimensional space of matrices

This file shows that `m` by `n` matrices form a finite-dimensional space.
Note that this is proven more generally elsewhere over modules as `Module.Finite.matrix`; this file
exists only to provide an entry in the instance list for `FiniteDimensional`.

## Main definitions

* `Matrix.finiteDimensional`: matrices form a finite-dimensional vector space over a field `K`
* `LinearMap.finiteDimensional`

## Tags

matrix, finite dimensional, findim, finrank

-/

public section


universe u v

namespace Matrix

section FiniteDimensional

variable {m n : Type*} {R : Type v} [Field R]

/-
**Matrix.finiteDimensional** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：finiteDimensional [Finite m] [Finite n] : FiniteDimensional R (Matrix m n 
R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance finiteDimensional [Finite m] [Finite n] : FiniteDimensional R (Matrix m n R) :=
  Module.Finite.matrix

end FiniteDimensional

end Matrix

namespace LinearMap

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-
**LinearMap.finiteDimensional** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：finiteDimensional : FiniteDimensional K (V ->ₗ[K] W)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
instance finiteDimensional : FiniteDimensional K (V →ₗ[K] W) :=
  Module.Finite.linearMap _ _ _ _

variable {A : Type*} [Ring A] [Algebra K A] [Module A V] [IsScalarTower K A V] [Module A W]
  [IsScalarTower K A W]

/-- Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the source and
target are, as they form a subspace of all `k`-linear maps. -/
/-
**LinearMap.finiteDimensional'** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：finiteDimensional' : FiniteDimensional K (V ->ₗ[A] W)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.of_injective`：of_injective (f : V ->ₗ[K] V₂) (w : Func
tion.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)

--- 原说明 ---
Linear maps over a `k`-algebra are finite dimensional (over `k`) if both the sou
rce and
target are, as they form a subspace of all `k`-linear maps.
-/
instance finiteDimensional' : FiniteDimensional K (V →ₗ[A] W) :=
  FiniteDimensional.of_injective (restrictScalarsₗ K A V W K) (restrictScalars_injective _)

end LinearMap

