/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dual space, linear maps and matrices.

This file contains some results about matrices and dual spaces.

## Tags

matrix, linear map, transpose, dual
-/

@[expose] public section

open Matrix Module

section Transpose

variable {K V₁ V₂ ι₁ ι₂ : Type*} [CommSemiring K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {B₁ : Basis ι₁ K V₁}
  {B₂ : Basis ι₂ K V₂}

@[simp]
/-
**LinearMap.toMatrix_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.toMatrix_transpose (u : V₁ ->ₗ[K] V₂) : LinearMap.toMatrix B₂.du
alBasis B₁.dualBasis (Module.Dual.transpose (R
参数：u : V₁ ->ₗ[K] V₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `Module.Basis.dualBasis_repr`：∀ {R : Type uR} {M : Type uM} {ι : Type uι}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R 
M] [inst_3 : Deci…
· 使用定理 `Module.Basis.dualBasis_apply`：dualBasis_apply (i : ι) (m : M) : b.dualBa
sis i m = b.repr m i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.toMatrix_transpose (u : V₁ →ₗ[K] V₂) :
    LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R := K) u) =
      (LinearMap.toMatrix B₁ B₂ u)ᵀ := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Dual.transpose_apply, B₁.dualBasis_repr,
    B₂.dualBasis_apply, Matrix.transpose_apply, LinearMap.comp_apply]

@[simp]
/-
**Matrix.toLin_transpose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Matrix.toLin B₁.dualBasis B₂
.dualBasis Mᵀ = Module.Dual.transpose (R
参数：M : Matrix ι₁ ι₂ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_toLin`：LinearMap.toMatrix_toLin (M : Matrix m n R) : 
LinearMap.toMatrix v₁ v₂ (Matrix.toLin v₁ v₂ M) = M
· 使用定理 `LinearMap.toMatrix_transpose`：LinearMap.toMatrix_transpose (u : V₁ ->ₗ[K
] V₂) : LinearMap.toMatrix B₂.dualBasis B₁.dualBasis (Module.Dual.transpose (R
-/
theorem Matrix.toLin_transpose (M : Matrix ι₁ ι₂ K) : Matrix.toLin B₁.dualBasis B₂.dualBasis Mᵀ =
    Module.Dual.transpose (R := K) (Matrix.toLin B₂ B₁ M) := by
  apply (LinearMap.toMatrix B₁.dualBasis B₂.dualBasis).injective
  rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_transpose, LinearMap.toMatrix_toLin]

end Transpose

set_option backward.isDefEq.respectTransparency false in
/-- The dot product as a linear equivalence to the dual. -/
/-
**dotProductEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (n : Type u_2) → [inst : CommSemiring R] → [Fintype n] 
→ [DecidableEq n] → (n → R) ≃ₗ[R] Module.Dual R (n → R)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dot product as a linear equivalence to the dual.
-/
@[simps] def dotProductEquiv (R n : Type*) [CommSemiring R] [Fintype n] [DecidableEq n] :
    (n → R) ≃ₗ[R] Module.Dual R (n → R) where
  toFun v := ⟨⟨dotProduct v, dotProduct_add v⟩, fun t ↦ dotProduct_smul t v⟩
  map_add' v w := by ext; simp
  map_smul' t v := by ext; simp
  invFun f i := f (LinearMap.single R _ i 1)
  left_inv v := by simp
  right_inv f := by ext; simp
