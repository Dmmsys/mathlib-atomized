/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.WithConv
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # The convolutive star ring on matrices

In this file, we provide the star algebra instance on `WithConv (Matrix m n R)` given by
the Hadamard product and intrinsic star (i.e., the star of each element in the matrix). -/

@[expose] public section

variable {m n α β : Type*}

open Matrix WithConv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] : Mul (WithConv (Matrix m n α)) where mul a b
  body: toConv (a.ofConv ⊙ b.ofConv)

中文:
实例 [乘法
  签名: α] : 乘法 (WithConv (矩阵 m n α)) where mul a b
  定义体: toConv (a.ofConv ⊙ b.ofConv)

Depends on / 依赖: a.ofConv, b.ofConv, ofConv, toConv
-/
instance [Mul α] : Mul (WithConv (Matrix m n α)) where mul a b := toConv (a.ofConv ⊙ b.ofConv)

/--
lemma `convMul_def` / 引理 `convMul_def`

English:
lemma convMul_def
  given: [Mul α] (x y : WithConv (Matrix m n α))
  proof: rfl

中文:
引理 convMul_def
  条件: [乘法 α] (x y : WithConv (矩阵 m n α))
  证明: rfl
-/
lemma convMul_def [Mul α] (x y : WithConv (Matrix m n α)) :
    x * y = toConv (x.ofConv ⊙ y.ofConv) := rfl

attribute [local simp] convMul_def

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup (WithConv (Matrix m n α)) where
  body: by simp [convMul_def, hadamard_assoc]

中文:
实例 [半群
  签名: α] : 半群 (WithConv (矩阵 m n α)) where
  定义体: by simp [convMul_def, hadamard_assoc]

Depends on / 依赖: convMul_def, hadamard_assoc
-/
instance [Semigroup α] : Semigroup (WithConv (Matrix m n α)) where
  mul_assoc _ _ _ := by simp [convMul_def, hadamard_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: α] : NonUnitalNonAssocSemiring (WithConv (Matrix m n α)) where
  body: by simp [hadamard_add]
  right_distrib _ _ _ := by simp [add_hadamard]
  zero_mul := by simp
  mul_zero := by simp

中文:
实例 [非幺非结合半环
  签名: α] : 非幺非结合半环 (WithConv (矩阵 m n α)) where
  定义体: by simp [hadamard_add]
  right_distrib _ _ _ := by simp [add_hadamard]
  zero_mul := by simp
  mul_zero := by simp

Depends on / 依赖: add_hadamard, hadamard_add, mul_zero, right_distrib, zero_mul
-/
instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (WithConv (Matrix m n α)) where
  left_distrib _ _ _ := by simp [hadamard_add]
  right_distrib _ _ _ := by simp [add_hadamard]
  zero_mul := by simp
  mul_zero := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMagma
  signature: α] : CommMagma (WithConv (Matrix m n α)) where
  body: by simp [hadamard_comm]

中文:
实例 [交换原群
  签名: α] : 交换原群 (WithConv (矩阵 m n α)) where
  定义体: by simp [hadamard_comm]

Depends on / 依赖: hadamard_comm
-/
instance [CommMagma α] : CommMagma (WithConv (Matrix m n α)) where
  mul_comm := by simp [hadamard_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [One
  signature: α] : One (WithConv (Matrix m n α)) where one
  body: toConv (of 1)

中文:
实例 [幺
  签名: α] : 幺 (WithConv (矩阵 m n α)) where one
  定义体: toConv (of 1)

Depends on / 依赖: toConv
-/
instance [One α] : One (WithConv (Matrix m n α)) where one := toConv (of 1)

/--
lemma `convOne_def` / 引理 `convOne_def`

English:
lemma convOne_def
  given: [One α]
  statement: (1 : WithConv (Matrix m n α)) = toConv (of 1)
  proof: rfl

中文:
引理 convOne_def
  条件: [幺 α]
  结论: (1 : WithConv (矩阵 m n α)) = toConv (of 1)
  证明: rfl
-/
lemma convOne_def [One α] : (1 : WithConv (Matrix m n α)) = toConv (of 1) := rfl

attribute [local simp] convOne_def

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass (WithConv (Matrix m n α)) where
  body: by simp
  mul_one := by simp

中文:
实例 [MulOne类
  签名: α] : MulOne类 (WithConv (矩阵 m n α)) where
  定义体: by simp
  mul_one := by simp

Depends on / 依赖: mul_one
-/
instance [MulOneClass α] : MulOneClass (WithConv (Matrix m n α)) where
  one_mul := by simp
  mul_one := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : Monoid (WithConv (Matrix m n α)) where

中文:
实例 [幺半群
  签名: α] : 幺半群 (WithConv (矩阵 m n α)) where
-/
instance [Monoid α] : Monoid (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid (WithConv (Matrix m n α)) where

中文:
实例 [交换幺半群
  签名: α] : 交换幺半群 (WithConv (矩阵 m n α)) where
-/
instance [CommMonoid α] : CommMonoid (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: α] : NonAssocSemiring (WithConv (Matrix m n α)) where

中文:
实例 [非结合半环
  签名: α] : 非结合半环 (WithConv (矩阵 m n α)) where
-/
instance [NonAssocSemiring α] : NonAssocSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: α] : NonUnitalSemiring (WithConv (Matrix m n α)) where

中文:
实例 [非幺半环
  签名: α] : 非幺半环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalSemiring α] : NonUnitalSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocCommSemiring
  signature: α] :

中文:
实例 [非幺非结合交换半环
  签名: α] :
-/
instance [NonUnitalNonAssocCommSemiring α] :
    NonUnitalNonAssocCommSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: α] : NonUnitalCommSemiring (WithConv (Matrix m n α)) where

中文:
实例 [非幺交换半环
  签名: α] : 非幺交换半环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocCommSemiring
  signature: α] : NonAssocCommSemiring (WithConv (Matrix m n α)) where

中文:
实例 [非结合交换半环
  签名: α] : 非结合交换半环 (WithConv (矩阵 m n α)) where
-/
instance [NonAssocCommSemiring α] : NonAssocCommSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: α] : Semiring (WithConv (Matrix m n α)) where

中文:
实例 [半环
  签名: α] : 半环 (WithConv (矩阵 m n α)) where
-/
instance [Semiring α] : Semiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: α] : CommSemiring (WithConv (Matrix m n α)) where

中文:
实例 [交换半环
  签名: α] : 交换半环 (WithConv (矩阵 m n α)) where
-/
instance [CommSemiring α] : CommSemiring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: α] : NonUnitalNonAssocRing (WithConv (Matrix m n α)) where

中文:
实例 [非幺非结合环
  签名: α] : 非幺非结合环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocCommRing
  signature: α] : NonUnitalNonAssocCommRing (WithConv (Matrix m n α)) where

中文:
实例 [非幺非结合交换环
  签名: α] : 非幺非结合交换环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalNonAssocCommRing α] : NonUnitalNonAssocCommRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: α] : NonUnitalRing (WithConv (Matrix m n α)) where

中文:
实例 [非幺环
  签名: α] : 非幺环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalRing α] : NonUnitalRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: α] : NonUnitalCommRing (WithConv (Matrix m n α)) where

中文:
实例 [非幺交换环
  签名: α] : 非幺交换环 (WithConv (矩阵 m n α)) where
-/
instance [NonUnitalCommRing α] : NonUnitalCommRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: α] : NonAssocRing (WithConv (Matrix m n α)) where

中文:
实例 [非结合环
  签名: α] : 非结合环 (WithConv (矩阵 m n α)) where
-/
instance [NonAssocRing α] : NonAssocRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocCommRing
  signature: α] : NonAssocCommRing (WithConv (Matrix m n α)) where

中文:
实例 [非结合交换环
  签名: α] : 非结合交换环 (WithConv (矩阵 m n α)) where
-/
instance [NonAssocCommRing α] : NonAssocCommRing (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: α] : Ring (WithConv (Matrix m n α)) where

中文:
实例 [环
  签名: α] : 环 (WithConv (矩阵 m n α)) where
-/
instance [Ring α] : Ring (WithConv (Matrix m n α)) where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: α] : CommRing (WithConv (Matrix m n α)) where

中文:
实例 [交换环
  签名: α] : 交换环 (WithConv (矩阵 m n α)) where
-/
instance [CommRing α] : CommRing (WithConv (Matrix m n α)) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: α] : Star (WithConv (Matrix m n α)) where star x
  body: toConv (x.ofConv.map star)

中文:
实例 [对合
  签名: α] : 对合 (WithConv (矩阵 m n α)) where star x
  定义体: toConv (x.ofConv.map star)

Depends on / 依赖: ofConv, toConv, x.ofConv.map
-/
instance [Star α] : Star (WithConv (Matrix m n α)) where star x := toConv (x.ofConv.map star)

/--
lemma `intrinsicStar_def` / 引理 `intrinsicStar_def`

English:
lemma intrinsicStar_def
  given: [Star α] (x : WithConv (Matrix m n α))
  proof: rfl

中文:
引理 intrinsicStar_def
  条件: [对合 α] (x : WithConv (矩阵 m n α))
  证明: rfl
-/
lemma intrinsicStar_def [Star α] (x : WithConv (Matrix m n α)) :
    star x = toConv (x.ofConv.map star) := rfl

attribute [local simp] intrinsicStar_def

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvolutiveStar
  signature: α] : InvolutiveStar (WithConv (Matrix m n α)) where
  body: by ext; simp

中文:
实例 [InvolutiveStar
  签名: α] : InvolutiveStar (WithConv (矩阵 m n α)) where
  定义体: by ext; simp
-/
instance [InvolutiveStar α] : InvolutiveStar (WithConv (Matrix m n α)) where
  star_involutive _ := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: α] [StarAddMonoid α] : StarAddMonoid (WithConv (Matrix m n α)) where
  body: by simp [Matrix.map_add]

中文:
实例 [加法幺半群
  签名: α] [StarAdd幺半群 α] : StarAdd幺半群 (WithConv (矩阵 m n α)) where
  定义体: by simp [Matrix.map_add]

Depends on / 依赖: Matrix, Matrix.map_add, map_add
-/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (WithConv (Matrix m n α)) where
  star_add _ _ := by simp [Matrix.map_add]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mul
  signature: α] [StarMul α] : StarMul (WithConv (Matrix m n α)) where
  body: by ext; simp

中文:
实例 [乘法
  签名: α] [StarMul α] : StarMul (WithConv (矩阵 m n α)) where
  定义体: by ext; simp
-/
instance [Mul α] [StarMul α] : StarMul (WithConv (Matrix m n α)) where
  star_mul _ _ := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: α] [StarRing α] : StarRing (WithConv (Matrix m n α)) where
  body: by simp

中文:
实例 [非幺非结合半环
  签名: α] [对合环 α] : 对合环 (WithConv (矩阵 m n α)) where
  定义体: by simp
-/
instance [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (WithConv (Matrix m n α)) where
  star_add := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] [MulAction β α] [Mul α] [SMulCommClass β α α] :
  body: by simp

中文:
实例 [幺半群
  签名: β] [乘法作用 β α] [乘法 α] [标量交换类 β α α] :
  定义体: by simp
-/
instance [Monoid β] [MulAction β α] [Mul α] [SMulCommClass β α α] :
    SMulCommClass β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_comm := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: β] [MulAction β α] [Mul α] [IsScalarTower β α α] :
  body: by simp

中文:
实例 [幺半群
  签名: β] [乘法作用 β α] [乘法 α] [标量塔 β α α] :
  定义体: by simp
-/
instance [Monoid β] [MulAction β α] [Mul α] [IsScalarTower β α α] :
    IsScalarTower β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_assoc := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: β] [Semiring α] [Algebra β α] : Algebra β (WithConv (Matrix m n α))
  body: .ofModule smul_mul_assoc mul_smul_comm

中文:
实例 [交换半环
  签名: β] [半环 α] [代数 β α] : 代数 β (WithConv (矩阵 m n α))
  定义体: .ofModule smul_mul_assoc mul_smul_comm

Depends on / 依赖: mul_smul_comm, ofModule, smul_mul_assoc
-/
instance [CommSemiring β] [Semiring α] [Algebra β α] : Algebra β (WithConv (Matrix m n α)) :=
  .ofModule smul_mul_assoc mul_smul_comm

/--
theorem `Matrix.WithConv.IsIdempotentElem.isSelfAdjoint` / 定理 `Matrix.WithConv.IsIdempotentElem.isSelfAdjoint`

English:
theorem Matrix.WithConv.IsIdempotentElem.isSelfAdjoint
  statement: [Semiring α] [IsLeftCancelMulZero α]
  proof: by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint]; rw [WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

中文:
定理 矩阵.WithConv.IsIdempotentElem.isSelfAdjoint
  结论: [半环 α] [是左消去MulZero α]
  证明: by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint]; rw [WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.iff_eq_zero_or_one, IsSelfAdjoint, Matrix, Matrix.ext_iff, WithConv, WithConv.ext_iff, convMul_def, ext_iff, hadamard_apply, iff_eq_zero_or_one, isIdempotentElem_iff, simp_rw
-/
theorem Matrix.WithConv.IsIdempotentElem.isSelfAdjoint [Semiring α] [IsLeftCancelMulZero α]
    [StarRing α] {f : WithConv (Matrix m n α)} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint]; rw [WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

section toLin'
variable [CommSemiring α] [StarRing α] [Fintype n] [DecidableEq n]

namespace WithConv

variable (m n α) in
/--
Definition of `matrixToLin'StarAlgEquiv` / `matrixToLin'StarAlgEquiv` 的定义

English:
definition matrixToLin'StarAlgEquiv
  signature: :
  body: congrLinearEquiv toLin'
  map_mul' _ _ := by ext; simp
.symm map_star' _ := by exact Matrix.intrinsicStar_toLin' _

中文:
定义 matrixToLin'StarAlg等价
  签名: :
  定义体: congrLinearEquiv toLin'
  map_mul' _ _ := by ext; simp
.symm map_star' _ := by exact Matrix.intrinsicStar_toLin' _

Depends on / 依赖: congrLinearEquiv
-/
def matrixToLin'StarAlgEquiv :
    WithConv (Matrix m n α) ≃⋆ₐ[α] WithConv ((n -> α) ->ₗ[α] m -> α) where
  __ := congrLinearEquiv toLin'
  map_mul' _ _ := by ext; simp
.symm map_star' _ := by exact Matrix.intrinsicStar_toLin' _

/--
lemma `matrixToLin'StarAlgEquiv_apply` / 引理 `matrixToLin'StarAlgEquiv_apply`

English:
lemma matrixToLin'StarAlgEquiv_apply
  given: (x : WithConv (Matrix m n α))
  proof: rfl

中文:
引理 matrixToLin'StarAlgEquiv_apply
  条件: (x : WithConv (矩阵 m n α))
  证明: rfl
-/
@[simp] lemma matrixToLin'StarAlgEquiv_apply (x : WithConv (Matrix m n α)) :
    matrixToLin'StarAlgEquiv m n α x = toConv x.ofConv.toLin' := rfl
/--
lemma `symm_matrixToLin'StarAlgEquiv_apply` / 引理 `symm_matrixToLin'StarAlgEquiv_apply`

English:
lemma symm_matrixToLin'StarAlgEquiv_apply
  given: (x : WithConv ((n -> α) ->ₗ[α] m -> α))
  proof: rfl

中文:
引理 symm_matrixToLin'StarAlgEquiv_apply
  条件: (x : WithConv ((n -> α) ->ₗ[α] m -> α))
  证明: rfl
-/
@[simp] lemma symm_matrixToLin'StarAlgEquiv_apply (x : WithConv ((n -> α) ->ₗ[α] m -> α)) :
    (matrixToLin'StarAlgEquiv m n α).symm x = toConv x.ofConv.toMatrix' := rfl

end WithConv

omit [StarRing α] in
/--
lemma `Matrix.toLin'_hadamard` / 引理 `Matrix.toLin'_hadamard`

English:
lemma Matrix.toLin'_hadamard
  given: (x y : Matrix m n α)
  proof: by ext; simp

中文:
引理 矩阵.toLin'_hadamard
  条件: (x y : 矩阵 m n α)
  证明: by ext; simp
-/
lemma Matrix.toLin'_hadamard (x y : Matrix m n α) :
    (x ⊙ y).toLin' = (toConv x.toLin' * toConv y.toLin').ofConv := by ext; simp

/--
theorem `Matrix.isSymm_iff_intrinsicStar_toLin'` / 定理 `Matrix.isSymm_iff_intrinsicStar_toLin'`

English:
theorem Matrix.isSymm_iff_intrinsicStar_toLin'
  given: {A : Matrix n n α}
  proof: by
  rw [intrinsicStar_toLin']; rw [toConv_injective.eq_iff]; rw [toLin'.injective.eq_iff]; rw [← transpose_conjTranspose]; rw [star_eq_conjTranspose]; rw [conjTranspose_inj]; rw [IsSymm]

中文:
定理 矩阵.isSymm_iff_intrinsicStar_toLin'
  条件: {A : 矩阵 n n α}
  证明: by
  rw [intrinsicStar_toLin']; rw [toConv_injective.eq_iff]; rw [toLin'.injective.eq_iff]; rw [← transpose_conjTranspose]; rw [star_eq_conjTranspose]; rw [conjTranspose_inj]; rw [IsSymm]

Depends on / 依赖: IsSymm, conjTranspose_inj, eq_iff, injective, injective.eq_iff, intrinsicStar_toLin, star_eq_conjTranspose, toConv_injective, toConv_injective.eq_iff, transpose_conjTranspose
-/
theorem Matrix.isSymm_iff_intrinsicStar_toLin' {A : Matrix n n α} :
    A.IsSymm ↔ star (toConv A.toLin') = toConv (star A).toLin' := by
  rw [intrinsicStar_toLin']; rw [toConv_injective.eq_iff]; rw [toLin'.injective.eq_iff]; rw [← transpose_conjTranspose]; rw [star_eq_conjTranspose]; rw [conjTranspose_inj]; rw [IsSymm]

end toLin'
