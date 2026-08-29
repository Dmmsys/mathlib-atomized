/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Determinant

/-!
# Matrices are isomorphic with linear maps between Lp spaces

This file provides a `WithLp` version of `Matrix.toLin'`.
-/

@[expose] public section

open Matrix ENNReal

variable {m n o R : Type*}

namespace Matrix
variable [Fintype n] [DecidableEq n] [CommRing R] (p q r : Real>=0∞)

open WithLp (toLp ofLp)

/--
Definition of `toLpLin` / `toLpLin` 的定义

English:
definition toLpLin
  signature: : Matrix m n R ≃ₗ[R] WithLp p (n -> R) ->ₗ[R] WithLp q (m -> R)
  body: toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n -> R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m -> R)).symm

@[simp]

中文:
定义 toLpLin
  签名: : 矩阵 m n R ≃ₗ[R] WithLp p (n -> R) ->ₗ[R] WithLp q (m -> R)
  定义体: toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n -> R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m -> R)).symm

@[simp]

Depends on / 依赖: WithLp, WithLp.linearEquiv, arrowCongr, linearEquiv, symm.arrowCongr
-/
def toLpLin : Matrix m n R ≃ₗ[R] WithLp p (n -> R) ->ₗ[R] WithLp q (m -> R) :=
  toLin' ≪≫ₗ
    (WithLp.linearEquiv _ R (n -> R)).symm.arrowCongr
      (WithLp.linearEquiv _ R (m -> R)).symm

@[simp]
/--
lemma `toLpLin_toLp` / 引理 `toLpLin_toLp`

English:
lemma toLpLin_toLp
  given: (A : Matrix m n R) (x : n -> R)
  proof: rfl

@[simp]

中文:
引理 toLpLin_toLp
  条件: (A : 矩阵 m n R) (x : n -> R)
  证明: rfl

@[simp]
-/
lemma toLpLin_toLp (A : Matrix m n R) (x : n -> R) :
    toLpLin p q A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[simp]
/--
theorem `ofLp_toLpLin` / 定理 `ofLp_toLpLin`

English:
theorem ofLp_toLpLin
  given: (A : Matrix m n R) (x : WithLp p (n -> R))
  proof: rfl

中文:
定理 ofLp_toLpLin
  条件: (A : 矩阵 m n R) (x : WithLp p (n -> R))
  证明: rfl
-/
theorem ofLp_toLpLin (A : Matrix m n R) (x : WithLp p (n -> R)) :
    ofLp (toLpLin p q A x) = Matrix.toLin' A (ofLp x) :=
  rfl

/--
theorem `toLpLin_apply` / 定理 `toLpLin_apply`

English:
theorem toLpLin_apply
  given: (M : Matrix m n R) (v : WithLp p (n -> R))
  proof: rfl

中文:
定理 toLpLin_apply
  条件: (M : 矩阵 m n R) (v : WithLp p (n -> R))
  证明: rfl
-/
theorem toLpLin_apply (M : Matrix m n R) (v : WithLp p (n -> R)) :
    toLpLin p q M v = toLp _ (M *ᵥ ofLp v) := rfl

/--
theorem `toLpLin_eq_toLin` / 定理 `toLpLin_eq_toLin`

English:
theorem toLpLin_eq_toLin
  given: [Finite m]
  proof: rfl

@[simp]

中文:
定理 toLpLin_eq_toLin
  条件: [有限 m]
  证明: rfl

@[simp]
-/
theorem toLpLin_eq_toLin [Finite m] :
    toLpLin p q = Matrix.toLin (PiLp.basisFun p R n) (PiLp.basisFun q R m) :=
  rfl

@[simp]
/--
theorem `toLpLin_one` / 定理 `toLpLin_one`

English:
theorem toLpLin_one
  statement: toLpLin p p (1 : Matrix n n R) = LinearMap.id
  proof: by ext; simp

中文:
定理 toLpLin_one
  结论: toLpLin p p (1 : 矩阵 n n R) = 线性映射.id
  证明: by ext; simp
-/
theorem toLpLin_one : toLpLin p p (1 : Matrix n n R) = LinearMap.id := by ext; simp

/--
theorem `toLpLin_mul` / 定理 `toLpLin_mul`

English:
theorem toLpLin_mul
  given: [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R)
  proof: by
  ext; simp

中文:
定理 toLpLin_mul
  条件: [有限类型 o] [DecidableEq o] (A : 矩阵 m n R) (B : 矩阵 n o R)
  证明: by
  ext; simp
-/
theorem toLpLin_mul [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p r (A * B) = toLpLin q r A ∘ₗ toLpLin p q B := by
  ext; simp

/-- A copy of `toLpLin_mul` that works for `simp`, for the common case where the domain and codomain
have the same norm. -/
@[simp]
/--
theorem `toLpLin_mul_same` / 定理 `toLpLin_mul_same`

English:
theorem toLpLin_mul_same
  given: [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R)
  proof: toLpLin_mul _ _ _ _ _

@[simp]

中文:
定理 toLpLin_mul_same
  条件: [有限类型 o] [DecidableEq o] (A : 矩阵 m n R) (B : 矩阵 n o R)
  证明: toLpLin_mul _ _ _ _ _

@[simp]

Depends on / 依赖: toLpLin_mul
-/
theorem toLpLin_mul_same [Fintype o] [DecidableEq o] (A : Matrix m n R) (B : Matrix n o R) :
    toLpLin p p (A * B) = toLpLin p p A ∘ₗ toLpLin p p B :=
  toLpLin_mul _ _ _ _ _

@[simp]
/--
theorem `toLpLin_symm_id` / 定理 `toLpLin_symm_id`

English:
theorem toLpLin_symm_id
  statement: (toLpLin p p).symm .id = (1 : Matrix n n R)
  proof: .injective by simp toLpLin p p

中文:
定理 toLpLin_symm_id
  结论: (toLpLin p p).symm .id = (1 : 矩阵 n n R)
  证明: .injective by simp toLpLin p p

Depends on / 依赖: injective, toLpLin
-/
theorem toLpLin_symm_id : (toLpLin p p).symm .id = (1 : Matrix n n R) :=
.injective by simp toLpLin p p

/--
theorem `toLpLin_symm_comp` / 定理 `toLpLin_symm_comp`

English:
theorem toLpLin_symm_comp
  statement: [Fintype o] [DecidableEq o]
  proof: .injective by simp [toLpLin_mul (q := q)] toLpLin p r

中文:
定理 toLpLin_symm_comp
  结论: [有限类型 o] [DecidableEq o]
  证明: .injective by simp [toLpLin_mul (q := q)] toLpLin p r

Depends on / 依赖: injective, toLpLin, toLpLin_mul
-/
theorem toLpLin_symm_comp [Fintype o] [DecidableEq o]
    (A : WithLp q (n -> R) ->ₗ[R] WithLp r (m -> R)) (B : WithLp p (o -> R) ->ₗ[R] WithLp q (n -> R)) :
    (toLpLin p r).symm (A ∘ₗ B) = (toLpLin q r).symm A * (toLpLin p q).symm B :=
.injective by simp [toLpLin_mul (q := q)] toLpLin p r

/-- `Matrix.toLinAlgEquiv'` adapted for `PiLp R _`. -/
@[simps!]
/--
Definition of `toLpLinAlgEquiv` / `toLpLinAlgEquiv` 的定义

English:
definition toLpLinAlgEquiv
  signature: : Matrix n n R ≃ₐ[R] Module.End R (WithLp p (n -> R))
  body: .ofLinearEquiv (toLpLin p p) (toLpLin_one p) (toLpLin_mul p p p)

@[simp]

中文:
定义 toLpLinAlgEquiv
  签名: : 矩阵 n n R ≃ₐ[R] 模.End R (WithLp p (n -> R))
  定义体: .ofLinearEquiv (toLpLin p p) (toLpLin_one p) (toLpLin_mul p p p)

@[simp]

Depends on / 依赖: ofLinearEquiv, toLpLin, toLpLin_mul, toLpLin_one
-/
def toLpLinAlgEquiv : Matrix n n R ≃ₐ[R] Module.End R (WithLp p (n -> R)) :=
  .ofLinearEquiv (toLpLin p p) (toLpLin_one p) (toLpLin_mul p p p)

@[simp]
/--
theorem `toLpLin_pow` / 定理 `toLpLin_pow`

English:
theorem toLpLin_pow
  given: (A : Matrix n n R) (k : Nat)
  statement: toLpLin p p (A ^ k) = toLpLin p p A ^ k
  proof: map_pow (toLpLinAlgEquiv p) A k

@[simp]

中文:
定理 toLpLin_pow
  条件: (A : 矩阵 n n R) (k : 自然数)
  结论: toLpLin p p (A ^ k) = toLpLin p p A ^ k
  证明: map_pow (toLpLinAlgEquiv p) A k

@[simp]

Depends on / 依赖: map_pow, toLpLinAlgEquiv
-/
theorem toLpLin_pow (A : Matrix n n R) (k : Nat) : toLpLin p p (A ^ k) = toLpLin p p A ^ k :=
  map_pow (toLpLinAlgEquiv p) A k

@[simp]
/--
theorem `toLpLin_symm_pow` / 定理 `toLpLin_symm_pow`

English:
theorem toLpLin_symm_pow
  given: (A : Module.End R (WithLp p (n -> R))) (k : Nat)
  proof: map_pow (toLpLinAlgEquiv p).symm A k

中文:
定理 toLpLin_symm_pow
  条件: (A : 模.End R (WithLp p (n -> R))) (k : 自然数)
  证明: map_pow (toLpLinAlgEquiv p).symm A k

Depends on / 依赖: map_pow, toLpLinAlgEquiv
-/
theorem toLpLin_symm_pow (A : Module.End R (WithLp p (n -> R))) (k : Nat) :
    (toLpLin p p).symm (A ^ k) = (toLpLin p p).symm A ^ k :=
  map_pow (toLpLinAlgEquiv p).symm A k

end Matrix

@[simp]
/--
theorem `LinearMap.det_toLpLin` / 定理 `LinearMap.det_toLpLin`

English:
theorem LinearMap.det_toLpLin
  statement: {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (p : Real>=0∞)
  proof: by
  simp [Matrix.toLpLin_eq_toLin]

中文:
定理 线性映射.det_toLpLin
  结论: {ι R : 类型} [有限类型 ι] [DecidableEq ι] [交换环 R] (p : 实数>=0∞)
  证明: by
  simp [Matrix.toLpLin_eq_toLin]

Depends on / 依赖: Matrix, Matrix.toLpLin_eq_toLin, toLpLin_eq_toLin
-/
theorem LinearMap.det_toLpLin {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (p : Real>=0∞)
    (m : Matrix ι ι R) : (m.toLpLin p p).det = m.det := by
  simp [Matrix.toLpLin_eq_toLin]
