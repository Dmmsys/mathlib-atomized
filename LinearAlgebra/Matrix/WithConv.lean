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

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] : Mul (WithConv (Matrix m n α)) where mul a b := toConv (a.ofConv ⊙ b.ofConv)
/-
**convMul_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convMul_def [Mul α] (x y : WithConv (Matrix m n α)) : x * y = toConv (x.of
Conv ⊙ y.ofConv)
参数：x y : WithConv (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convMul_def [Mul α] (x y : WithConv (Matrix m n α)) :
    x * y = toConv (x.ofConv ⊙ y.ofConv) := rfl

attribute [local simp] convMul_def
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semigroup α] : Semigroup (WithConv (Matrix m n α)) where
  mul_assoc _ _ _ := by simp [convMul_def, hadamard_assoc]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (WithConv (Matrix m n α)) where
  left_distrib _ _ _ := by simp [hadamard_add]
  right_distrib _ _ _ := by simp [add_hadamard]
  zero_mul := by simp
  mul_zero := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMagma α] : CommMagma (WithConv (Matrix m n α)) where
  mul_comm := by simp [hadamard_comm]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One α] : One (WithConv (Matrix m n α)) where one := toConv (of 1)
/-
**convOne_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convOne_def [One α] : (1 : WithConv (Matrix m n α)) = toConv (of 1)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma convOne_def [One α] : (1 : WithConv (Matrix m n α)) = toConv (of 1) := rfl

attribute [local simp] convOne_def
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulOneClass α] : MulOneClass (WithConv (Matrix m n α)) where
  one_mul := by simp
  mul_one := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] : Monoid (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] : CommMonoid (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring α] : NonAssocSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring α] : NonUnitalSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocCommSemiring α] :
    NonUnitalNonAssocCommSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocCommSemiring α] : NonAssocCommSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring α] : Semiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring α] : CommSemiring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocCommRing α] : NonUnitalNonAssocCommRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing α] : NonUnitalRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing α] : NonUnitalCommRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing α] : NonAssocRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocCommRing α] : NonAssocCommRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring α] : Ring (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing α] : CommRing (WithConv (Matrix m n α)) where
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star α] : Star (WithConv (Matrix m n α)) where star x := toConv (x.ofConv.map star)
/-
**intrinsicStar_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：intrinsicStar_def [Star α] (x : WithConv (Matrix m n α)) : star x = toConv
 (x.ofConv.map star)
参数：x : WithConv (Matrix m n α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma intrinsicStar_def [Star α] (x : WithConv (Matrix m n α)) :
    star x = toConv (x.ofConv.map star) := rfl

attribute [local simp] intrinsicStar_def
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar α] : InvolutiveStar (WithConv (Matrix m n α)) where
  star_involutive _ := by ext; simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid α] [StarAddMonoid α] : StarAddMonoid (WithConv (Matrix m n α)) where
  star_add _ _ := by simp [Matrix.map_add]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [StarMul α] : StarMul (WithConv (Matrix m n α)) where
  star_mul _ _ := by ext; simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring α] [StarRing α] : StarRing (WithConv (Matrix m n α)) where
  star_add := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] [MulAction β α] [Mul α] [SMulCommClass β α α] :
    SMulCommClass β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_comm := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid β] [MulAction β α] [Mul α] [IsScalarTower β α α] :
    IsScalarTower β (WithConv (Matrix m n α)) (WithConv (Matrix m n α)) where smul_assoc := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring β] [Semiring α] [Algebra β α] : Algebra β (WithConv (Matrix m n α)) :=
  .ofModule smul_mul_assoc mul_smul_comm

/-- All matrices are intrinsically self-adjoint if they are convolutively idempotent. -/
/-
**Matrix.WithConv.IsIdempotentElem.isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.WithConv.IsIdempotentElem.isSelfAdjoint [Semiring α] [IsLeftCancelM
ulZero α] [StarRing α] {f : WithConv (Matrix m n α)} (hf : IsIdempotentElem f) :
 IsSelfAdjoint f
参数：Matrix m n α；hf : IsIdempotentElem f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSelfAdjoint.eq_1`：∀ {R : Type u_1} [inst : Star R] (x : R), IsSelfAdjo
int x = (star x = x)
· 使用定理 `WithConv.ext_iff`：∀ {A : Type u_2} {x y : WithConv A}, x = y ↔ x.ofConv 
= y.ofConv
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1

--- 原说明 ---
All matrices are intrinsically self-adjoint if they are convolutively idempotent
.
-/
theorem Matrix.WithConv.IsIdempotentElem.isSelfAdjoint [Semiring α] [IsLeftCancelMulZero α]
    [StarRing α] {f : WithConv (Matrix m n α)} (hf : IsIdempotentElem f) : IsSelfAdjoint f := by
  simp_rw [IsIdempotentElem, WithConv.ext_iff, ← Matrix.ext_iff, convMul_def, hadamard_apply,
    ← isIdempotentElem_iff, IsIdempotentElem.iff_eq_zero_or_one] at hf
  rw [IsSelfAdjoint, WithConv.ext_iff]
  ext i j
  obtain (h | h) := hf i j <;> simp_all

section toLin'
variable [CommSemiring α] [StarRing α] [Fintype n] [DecidableEq n]

namespace WithConv

variable (m n α) in
/-- `WithConv (Matrix m n α)` is ⋆-algebraically equivalent to `WithConv ((n → α) →ₗ m → α)`.

In particular, the convolutive product on linear maps corresponds to the Hadamard product
on matrices and the intrinsic star on linear maps corresponds to taking the star of each element in
the matrix. -/
/-
**WithConv.matrixToLin'StarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：(m : Type u_1) →   (n : Type u_2) →     (α : Type u_3) →       [inst : Com
mSemiring α] →         [inst_1 : StarRing α] →           [inst_2 : Fintype n] → 
            [inst_3 : DecidableEq n] → WithConv (Matrix m n α) ≃⋆ₐ[α] WithConv (
(n → α) →ₗ[α] m → α)
参数：n → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithConv (Matrix m n α)` is ⋆-algebraically equivalent to `WithConv ((n → α) →ₗ
 m → α)`.

In particular, the convolutive product on linear maps corresponds to the Hadamar
d product
on matrices and the intrinsic star on linear maps corresponds to taking the star
 of each element in
the matrix.
-/
def matrixToLin'StarAlgEquiv :
    WithConv (Matrix m n α) ≃⋆ₐ[α] WithConv ((n → α) →ₗ[α] m → α) where
  __ := congrLinearEquiv toLin'
  map_mul' _ _ := by ext; simp
  map_star' _ := by exact Matrix.intrinsicStar_toLin' _ |>.symm
/-
**WithConv.matrixToLin'StarAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : CommSemiring α] [in
st_1 : StarRing α] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (x : WithConv
 (Matrix m n α)),   (WithConv.matrixToLin'StarAlgEquiv m n α) x = WithConv.toCon
v (Matrix.toLin' x.ofConv)
参数：x : WithConv (Matrix m n α)；WithConv.matrixToLin'StarAlgEquiv m n α；Matrix.to
Lin' x.ofConv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
-/
@[simp] lemma matrixToLin'StarAlgEquiv_apply (x : WithConv (Matrix m n α)) :
    matrixToLin'StarAlgEquiv m n α x = toConv x.ofConv.toLin' := rfl
/-
**WithConv.symm_matrixToLin'StarAlgEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithCo
nv`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : CommSemiring α] [in
st_1 : StarRing α] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (x : WithConv
 ((n → α) →ₗ[α] m → α)),   (WithConv.matrixToLin'StarAlgEquiv m n α).symm x = Wi
thConv.toConv (LinearMap.toMatrix' x.ofConv)
参数：x : WithConv ((n → α) →ₗ[α] m → α)；WithConv.matrixToLin'StarAlgEquiv m n α；Li
nearMap.toMatrix' x.ofConv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
-/
@[simp] lemma symm_matrixToLin'StarAlgEquiv_apply (x : WithConv ((n → α) →ₗ[α] m → α)) :
    (matrixToLin'StarAlgEquiv m n α).symm x = toConv x.ofConv.toMatrix' := rfl

end WithConv

omit [StarRing α] in
/-
**Matrix.toLin'_hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {α : Type u_3} [inst : CommSemiring α] [in
st_1 : Fintype n] [inst_2 : DecidableEq n]   (x y : Matrix m n α),   Matrix.toLi
n' (x.hadamard y) = (WithConv.toConv (Matrix.toLin' x) * WithConv.toConv (Matrix
.toLin' y)).ofConv
参数：x y : Matrix m n α；x.hadamard y；WithConv.toConv (Matrix.toLin' x) * WithConv.
toConv (Matrix.toLin' y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.comul_single`：∀ {R : Type u_1} {n : Type u_2} [inst : CommSemiring R]
 [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : n → Type u_3}   [inst_3 : (i
 : n)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Matrix.toLin'_hadamard (x y : Matrix m n α) :
    (x ⊙ y).toLin' = (toConv x.toLin' * toConv y.toLin').ofConv := by ext; simp
/-
**Matrix.isSymm_iff_intrinsicStar_toLin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Matrix.isSymm_iff_intrinsicStar_toLin' {A : Matrix n n α} : A.IsSymm ↔ sta
r (toConv A.toLin') = toConv (star A).toLin'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.intrinsicStar_toLin'`：intrinsicStar_toLin' (A : Matrix n m R) : s
tar (toConv A.toLin') = toConv (A.map star).toLin'
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_conjTranspose`：transpose_conjTranspose [Star α] (M : Ma
trix m n α) : Mᵀᴴ = M.map star
· 使用定理 `Matrix.star_eq_conjTranspose`：star_eq_conjTranspose [Star α] (M : Matrix
 m m α) : star M = Mᴴ
· 使用定理 `Matrix.conjTranspose_inj`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} [
inst : InvolutiveStar α] {A B : Matrix m n α},   A.conjTranspose = B.conjTranspo
se ↔ A = B
· 使用定理 `Matrix.IsSymm.eq_1`：∀ {α : Type u_1} {n : Type u_3} (A : Matrix n n α), 
A.IsSymm = (A.transpose = A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Matrix.isSymm_iff_intrinsicStar_toLin' {A : Matrix n n α} :
    A.IsSymm ↔ star (toConv A.toLin') = toConv (star A).toLin' := by
  rw [intrinsicStar_toLin', toConv_injective.eq_iff, toLin'.injective.eq_iff,
    ← transpose_conjTranspose, star_eq_conjTranspose, conjTranspose_inj, IsSymm]

end toLin'

