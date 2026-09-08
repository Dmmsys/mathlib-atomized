/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.PosDef

/-! # LDL decomposition

This file proves the LDL-decomposition of matrices: Any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix.

## Main definitions

* `LDL.lower` is the lower triangular matrix `L`.
* `LDL.lowerInv` is the inverse of the lower triangular matrix `L`.
* `LDL.diag` is the diagonal matrix `D`.

## Main result

* `LDL.lower_conj_diag` states that any positive definite matrix can be decomposed as `LDLᴴ`.

## TODO

* Prove that `LDL.lower` is lower triangular from `LDL.lowerInv_triangular`.

-/

@[expose] public section

open Module

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]

section set_options

set_option quotPrecheck false
local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y)

open Matrix InnerProductSpace

open scoped ComplexOrder

variable {S : Matrix n n 𝕜} [Fintype n] (hS : S.PosDef)

/-- The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is obtained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ` on the standard
basis vectors `Pi.basisFun`. -/
/-
**LDL.lowerInv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LDL.lowerInv : Matrix n n 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The inverse of the lower triangular matrix `L` of the LDL-decomposition. It is o
btained by
applying Gram-Schmidt-Orthogonalization w.r.t. the inner product induced by `Sᵀ`
 on the standard
basis vectors `Pi.basisFun`.
-/
noncomputable def LDL.lowerInv : Matrix n n 𝕜 :=
  @gramSchmidt 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)
/-
**LDL.lowerInv_eq_gramSchmidtBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LDL.lowerInv_eq_gramSchmidtBasis : LDL.lowerInv hS = ((Pi.basisFun 𝕜 n).to
Matrix (@gramSchmidtBasis 𝕜 (n -> 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose) (S
ᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)))ᵀ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.transpose`：transpose {M : Matrix n n R'} (hM : M.PosDef) :
 Mᵀ.PosDef
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LDL.lowerInv.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [in
st_1 : LinearOrder n] [inst_2 : WellFoundedLT n]   [inst_3 : LocallyFiniteOrderB
ot n] {…
· 使用定理 `Module.Basis.coePiBasisFun.toMatrix_eq_transpose`：∀ {ι : Type u_1} {R : 
Type u_5} [inst : CommSemiring R] [inst_1 : Finite ι],   (Pi.basisFun R ι).toMat
rix = Matrix.transpose
· 使用定理 `InnerProductSpace.coe_gramSchmidtBasis`：coe_gramSchmidtBasis (b : Basis 
ι 𝕜 E) : (gramSchmidtBasis b : ι -> E) = gramSchmidt 𝕜 b
-/
theorem LDL.lowerInv_eq_gramSchmidtBasis :
    LDL.lowerInv hS =
      ((Pi.basisFun 𝕜 n).toMatrix
          (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
            (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n)))ᵀ := by
  let := (Sᵀ.toNormedAddCommGroup hS.transpose)
  let := (Sᵀ.toInnerProductSpace hS.transpose.posSemidef)
  ext i j
  rw [LDL.lowerInv, Basis.coePiBasisFun.toMatrix_eq_transpose, coe_gramSchmidtBasis]
  rfl
/-
**LDL.invertibleLowerInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
noncomputable instance LDL.invertibleLowerInv : Invertible (LDL.lowerInv hS) := by
  rw [LDL.lowerInv_eq_gramSchmidtBasis]
  haveI :=
    Basis.invertibleToMatrix (Pi.basisFun 𝕜 n)
      (@gramSchmidtBasis 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
        (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n))
  infer_instance
/-
**LDL.lowerInv_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LDL.lowerInv_orthogonal {i j : n} (h₀ : i != j) : ⟪LDL.lowerInv hS i, Sᵀ *
ᵥ LDL.lowerInv hS j⟫ₑ = 0
参数：h₀ : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.gramSchmidt_orthogonal`：gramSchmidt_orthogonal (f : ι 
-> E) {a b : ι} (h₀ : a != b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0
· 使用定理 `Matrix.PosDef.transpose`：transpose {M : Matrix n n R'} (hM : M.PosDef) :
 Mᵀ.PosDef
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem LDL.lowerInv_orthogonal {i j : n} (h₀ : i ≠ j) :
    ⟪LDL.lowerInv hS i, Sᵀ *ᵥ LDL.lowerInv hS j⟫ₑ = 0 :=
  @gramSchmidt_orthogonal 𝕜 _ _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) _ _ _ _ _ _ _ h₀

/-- The entries of the diagonal matrix `D` of the LDL decomposition. -/
/-
**LDL.diagEntries** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LDL.diagEntries : n -> 𝕜
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The entries of the diagonal matrix `D` of the LDL decomposition.
-/
noncomputable def LDL.diagEntries : n → 𝕜 := fun i =>
  ⟪star (LDL.lowerInv hS i), S *ᵥ star (LDL.lowerInv hS i)⟫ₑ

/-- The diagonal matrix `D` of the LDL decomposition. -/
/-
**LDL.diag** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LDL.diag : Matrix n n 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal matrix `D` of the LDL decomposition.
-/
noncomputable def LDL.diag : Matrix n n 𝕜 :=
  Matrix.diagonal (LDL.diagEntries hS)
/-
**LDL.lowerInv_triangular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LDL.lowerInv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0
参数：hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.transpose`：transpose {M : Matrix n n R'} (hM : M.PosDef) :
 Mᵀ.PosDef
· 使用定理 `Matrix.PosDef.posSemidef`：posSemidef {M : Matrix n n R} (hM : M.PosDef) 
: M.PosSemidef
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InnerProductSpace.gramSchmidt_triangular`：gramSchmidt_triangular {i j : 
ι} (hij : i < j) (b : Basis ι 𝕜 E) : b.repr (gramSchmidt 𝕜 b i) j = 0
· 使用定理 `Pi.basisFun_repr`：basisFun_repr (x : η -> R) (i : η) : (Pi.basisFun R η)
.repr x i = x i
· 使用定理 `LDL.lowerInv.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [in
st_1 : LinearOrder n] [inst_2 : WellFoundedLT n]   [inst_3 : LocallyFiniteOrderB
ot n] {…
-/
theorem LDL.lowerInv_triangular {i j : n} (hij : i < j) : LDL.lowerInv hS i j = 0 := by
  rw [← @gramSchmidt_triangular 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
      (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ i j hij (Pi.basisFun 𝕜 n),
    Pi.basisFun_repr, LDL.lowerInv]

/-- Inverse statement of **LDL decomposition**: we can conjugate a positive definite matrix
by some lower triangular matrix and get a diagonal matrix. -/
/-
**LDL.diag_eq_lowerInv_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL.lowerInv hS * S * (LDL.lower
Inv hS)ᴴ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal.congr_simp`：∀ {n : Type u_3} {α : Type v} {inst : Decida
bleEq n} [inst_1 : DecidableEq n] [inst_2 : Zero α] (d d_1 : n → α),   d = d_1 →
 ∀ (a a_1 : n), …
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matrix.mul_mul_apply`：mul_mul_apply [Fintype n] (A B C : Matrix n n α) (
i j : n) : (A * B * C) i j = A i ⬝ᵥ B *ᵥ (Cᵀ j)
· 使用定理 `Matrix.conjTranspose.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} 
[inst : Star α] (M : Matrix m n α), M.conjTranspose = M.transpose.map star
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LDL.lowerInv_orthogonal`：LDL.lowerInv_orthogonal {i j : n} (h₀ : i != j)
 : ⟪LDL.lowerInv hS i, Sᵀ *ᵥ LDL.lowerInv hS j⟫ₑ = 0
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Matrix.mulVec_transpose`：mulVec_transpose [Fintype m] (A : Matrix m n α)
 (x : m -> α) : Aᵀ *ᵥ x = x ᵥ* A
· 使用引理 `EuclideanSpace.inner_toLp_toLp`：inner_toLp_toLp (x y : ι -> 𝕜) : ⟪toLp 2
 x, toLp 2 y⟫ = dotProduct y (star x)
· 使用定理 `RCLike.star_def`：star_def : (Star.star : K -> K) = conj
· 使用定理 `Matrix.star_dotProduct_star`：star_dotProduct_star : star v ⬝ᵥ star w = s
tar (w ⬝ᵥ v)

--- 原说明 ---
Inverse statement of **LDL decomposition**: we can conjugate a positive definite
 matrix
by some lower triangular matrix and get a diagonal matrix.
-/
theorem LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL.lowerInv hS * S * (LDL.lowerInv hS)ᴴ := by
  ext i j
  by_cases hij : i = j
  · simp only [diag, diagEntries, EuclideanSpace.inner_toLp_toLp, star_star, hij,
      diagonal_apply_eq, Matrix.mul_assoc, dotProduct_comm]
    rfl
  · simp only [LDL.diag, hij, diagonal_apply_ne, Ne, not_false_iff, mul_mul_apply]
    rw [conjTranspose, transpose_map, transpose_transpose, dotProduct_mulVec,
      (LDL.lowerInv_orthogonal hS fun h : j = i => hij h.symm).symm, ← inner_conj_symm,
      mulVec_transpose, EuclideanSpace.inner_toLp_toLp, ← RCLike.star_def, ←
      star_dotProduct_star, star_star]
    rfl

/-- The lower triangular matrix `L` of the LDL decomposition. -/
/-
**LDL.lower** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LDL.lower
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower triangular matrix `L` of the LDL decomposition.
-/
noncomputable def LDL.lower :=
  (LDL.lowerInv hS)⁻¹

/-- **LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a diagonal matrix. -/
/-
**LDL.lower_conj_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LDL.lower_conj_diag : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LDL.lower.eq_1`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n : Type u_2} [inst_
1 : LinearOrder n] [inst_2 : WellFoundedLT n]   [inst_3 : LocallyFiniteOrderBot 
n] {…
· 使用定理 `Matrix.conjTranspose_nonsing_inv`：conjTranspose_nonsing_inv [StarRing α]
 : A⁻¹ᴴ = Aᴴ⁻¹
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.inv_mul_eq_iff_eq_mul_of_invertible`：inv_mul_eq_iff_eq_mul_of_inv
ertible (A : Matrix n n α) [Invertible A] (B C : Matrix n m α) : A⁻¹ * B = C ↔ B
 = A * C
· 使用定理 `Matrix.mul_inv_eq_iff_eq_mul_of_invertible`：mul_inv_eq_iff_eq_mul_of_inv
ertible (A : Matrix n n α) [Invertible A] (B C : Matrix m n α) : B * A⁻¹ = C ↔ B
 = C * A
· 使用定理 `LDL.diag_eq_lowerInv_conj`：LDL.diag_eq_lowerInv_conj : LDL.diag hS = LDL
.lowerInv hS * S * (LDL.lowerInv hS)ᴴ

--- 原说明 ---
**LDL decomposition**: any positive definite matrix `S` can be
decomposed as `S = LDLᴴ` where `L` is a lower-triangular matrix and `D` is a dia
gonal matrix.
-/
theorem LDL.lower_conj_diag : LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ = S := by
  rw [LDL.lower, conjTranspose_nonsing_inv, Matrix.mul_assoc,
    Matrix.inv_mul_eq_iff_eq_mul_of_invertible (LDL.lowerInv hS),
    Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  exact LDL.diag_eq_lowerInv_conj hS

end set_options

