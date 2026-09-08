/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hermitian matrices over ℝ and ℂ

This file proves that Hermitian matrices over ℝ and ℂ are exactly the ones whose corresponding
linear map is self-adjoint.

## Tags

self-adjoint matrix, hermitian matrix
-/

public section

-- TODO:
-- assert_not_exists MonoidAlgebra

open RCLike

namespace Matrix

variable {𝕜 m n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜]

/-- The diagonal elements of a complex Hermitian matrix are real. -/
/-
**Matrix.IsHermitian.coe_re_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermi
tian`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} {A : Matrix n n 𝕜} [inst : RCLike 𝕜],   A.
IsHermitian → ∀ (i : n), ↑(RCLike.re (A i i)) = A i i
参数：i : n；RCLike.re (A i i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.conj_eq_iff_re`：conj_eq_iff_re {z : K} : conj z = z ↔ (re z : K) 
= z
· 使用定理 `RCLike.star_def`：star_def : (Star.star : K -> K) = conj
· 使用定理 `Matrix.conjTranspose_apply`：conjTranspose_apply [Star α] (M : Matrix m n
 α) (i j) : M.conjTranspose j i = star (M i j)
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A

--- 原说明 ---
The diagonal elements of a complex Hermitian matrix are real.
-/
lemma IsHermitian.coe_re_apply_self (h : A.IsHermitian) (i : n) : (re (A i i) : 𝕜) = A i i := by
  rw [← conj_eq_iff_re, ← star_def, ← conjTranspose_apply, h.eq]

/-- The diagonal elements of a complex Hermitian matrix are real. -/
/-
**Matrix.IsHermitian.coe_re_diag** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} {A : Matrix n n 𝕜} [inst : RCLike 𝕜],   A.
IsHermitian → (fun i => ↑(RCLike.re (A.diag i))) = A.diag
参数：fun i => ↑(RCLike.re (A.diag i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.IsHermitian.coe_re_apply_self`：∀ {𝕜 : Type u_1} {n : Type u_3} {A
 : Matrix n n 𝕜} [inst : RCLike 𝕜],   A.IsHermitian → ∀ (i : n), ↑(RCLike.re (A 
i i)) = A i i

--- 原说明 ---
The diagonal elements of a complex Hermitian matrix are real.
-/
lemma IsHermitian.coe_re_diag (h : A.IsHermitian) : (fun i => (re (A.diag i) : 𝕜)) = A.diag :=
  funext h.coe_re_apply_self

/-- A matrix is Hermitian iff the corresponding linear map with an orthonormal basis is
symmetric. -/
@[simp]
/-
**Matrix.isSymmetric_toLin_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isSymmetric_toLin_iff [Fintype n] [DecidableEq n] {E : Type*} [NormedAddCo
mmGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis n 𝕜 E) : (A.toLin b.toB
asis b.toBasis).IsSymmetric ↔ A.IsHermitian
参数：b : OrthonormalBasis n 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ext_inner_right`：ext_inner_right {x y : E} (h : forall v, ⟪x, v⟫ = ⟪y, v
⟫) : x = y
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A

--- 原说明 ---
A matrix is Hermitian iff the corresponding linear map with an orthonormal basis
 is
symmetric.
-/
lemma isSymmetric_toLin_iff [Fintype n] [DecidableEq n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : OrthonormalBasis n 𝕜 E) :
    (A.toLin b.toBasis b.toBasis).IsSymmetric ↔ A.IsHermitian := by
  have : FiniteDimensional 𝕜 E := b.toBasis.finiteDimensional_of_finite
  simp_rw [LinearMap.IsSymmetric, ← LinearMap.adjoint_inner_left, ← toLin_conjTranspose]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ by rw [h.eq]⟩
  simpa using! (LinearMap.ext fun x ↦ ext_inner_right _ (h x)).symm

/-- A matrix is Hermitian iff the corresponding linear map on the Euclidean space is
symmetric. -/
@[simp]
/-
**Matrix.isSymmetric_toEuclideanLin_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isSymmetric_toEuclideanLin_iff [Fintype n] [DecidableEq n] : A.toEuclidean
Lin.IsSymmetric ↔ A.IsHermitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.isSymmetric_toLin_iff`：isSymmetric_toLin_iff [Fintype n] [Decidab
leEq n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : Orthonor
malBasis n 𝕜 E) : …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
A matrix is Hermitian iff the corresponding linear map on the Euclidean space is
symmetric.
-/
lemma isSymmetric_toEuclideanLin_iff [Fintype n] [DecidableEq n] :
    A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian :=
  isSymmetric_toLin_iff (EuclideanSpace.basisFun n 𝕜)

@[deprecated isSymmetric_toEuclideanLin_iff "use isSymmetric_toEuclideanLin_iff.symm"
  (since := "2026-03-30")]
/-
**Matrix.isHermitian_iff_isSymmetric** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] : IsHermitian A ↔ 
A.toEuclideanLin.IsSymmetric
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Matrix.isSymmetric_toEuclideanLin_iff`：isSymmetric_toEuclideanLin_iff [F
intype n] [DecidableEq n] : A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian
-/
lemma isHermitian_iff_isSymmetric [Fintype n] [DecidableEq n] :
    IsHermitian A ↔ A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.symm
/-
**Matrix.IsHermitian.im_star_dotProduct_mulVec_self** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.IsHermitian`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} {A : Matrix n n 𝕜} [inst : RCLike 𝕜] [inst
_1 : Fintype n],   A.IsHermitian → ∀ (x : n → 𝕜), RCLike.im (star x ⬝ᵥ A.mulVec 
x) = 0
参数：x : n → 𝕜；star x ⬝ᵥ A.mulVec x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `LinearMap.IsSymmetric.im_inner_self_apply`：∀ {𝕜 : Type u_1} {E : Type u_
2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductS
pace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matrix.isSymmetric_toEuclideanLin_iff`：isSymmetric_toEuclideanLin_iff [F
intype n] [DecidableEq n] : A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian
-/
lemma IsHermitian.im_star_dotProduct_mulVec_self [Fintype n] (hA : A.IsHermitian) (x : n → 𝕜) :
     RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0 := by
  classical
  simpa [dotProduct_comm] using! (isSymmetric_toEuclideanLin_iff.mpr hA).im_inner_self_apply _

end Matrix

/-- A linear map is symmetric iff the corresponding matrix with an orthonormal basis is
Hermitian. -/
@[simp]
/-
**LinearMap.isHermitian_toMatrix_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.isHermitian_toMatrix_iff {n 𝕜 E : Type*} [Fintype n] [DecidableE
q n] [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E ->ₗ[𝕜] E} 
(b : OrthonormalBasis n 𝕜 E) : (f.toMatrix b.toBasis b.toBasis).IsHermitian ↔ f.
IsSymmetric
参数：b : OrthonormalBasis n 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.isSymmetric_toLin_iff`：isSymmetric_toLin_iff [Fintype n] [Decidab
leEq n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (b : Orthonor
malBasis n 𝕜 E) : …
· 使用定理 `Matrix.toLin_toMatrix`：Matrix.toLin_toMatrix (f : M₁ ->ₗ[R] M₂) : Matrix
.toLin v₁ v₂ (LinearMap.toMatrix v₁ v₂ f) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A linear map is symmetric iff the corresponding matrix with an orthonormal basis
 is
Hermitian.
-/
lemma LinearMap.isHermitian_toMatrix_iff {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {f : E →ₗ[𝕜] E} (b : OrthonormalBasis n 𝕜 E) :
    (f.toMatrix b.toBasis b.toBasis).IsHermitian ↔ f.IsSymmetric := by
  rw [← Matrix.isSymmetric_toLin_iff b, Matrix.toLin_toMatrix]
