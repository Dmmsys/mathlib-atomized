/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Spectrum of positive (semi)definite matrices

This file proves that eigenvalues of positive (semi)definite matrices are (nonnegative) positive.

## Main definitions

* `Matrix.toInnerProductSpace`: the pre-inner product space on `n → 𝕜` induced by a
  positive semi-definite matrix `M`, and is given by `⟪x, y⟫ = xᴴMy`.

-/

@[expose] public section

open WithLp Matrix Unitary
open scoped ComplexOrder

namespace Matrix
variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜] {A : Matrix n n 𝕜}

/-! ### Positive semidefinite matrices -/

/-- A Hermitian matrix is positive semi-definite if and only if its eigenvalues are non-negative. -/
/-
**Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 `Matrix.IsHermitian`。
形式化陈述：∀ {n : Type u_2} {𝕜 : Type u_3} [inst : Fintype n] [inst_1 : RCLike 𝕜] {A 
: Matrix n n 𝕜} [inst_2 : DecidableEq n]   (hA : A.IsHermitian), A.PosSemidef ↔ 
0 ≤ hA.eigenvalues
参数：hA : A.IsHermitian。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.IsUnit.posSemidef_star_right_conjugate_iff`：∀ {n : Type u_2} {R :
 Type u_3} [inst : Ring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [inst
_3 : Fintype n]   [inst_4 : DecidableEq…
· 使用定理 `Unitary.isUnit_coe`：isUnit_coe {U : unitary R} : IsUnit (U : R)
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A Hermitian matrix is positive semi-definite if and only if its eigenvalues are 
non-negative.
-/
lemma IsHermitian.posSemidef_iff_eigenvalues_nonneg [DecidableEq n] (hA : IsHermitian A) :
    PosSemidef A ↔ 0 ≤ hA.eigenvalues := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posSemidef_star_right_conjugate_iff, posSemidef_diagonal_iff, Pi.le_def]

namespace PosSemidef

/-- The eigenvalues of a positive semi-definite matrix are non-negative -/
/-
**Matrix.PosSemidef.eigenvalues_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemi
def`。
形式化陈述：eigenvalues_nonneg [DecidableEq n] (hA : A.PosSemidef) (i : n) : 0 <= hA.1
.eigenvalues i
参数：hA : A.PosSemidef；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg`：∀ {n : Type u_2} {
𝕜 : Type u_3} [inst : Fintype n] [inst_1 : RCLike 𝕜] {A : Matrix n n 𝕜} [inst_2 
: DecidableEq n]   (hA : A.IsHermitian), A…

--- 原说明 ---
The eigenvalues of a positive semi-definite matrix are non-negative
-/
lemma eigenvalues_nonneg [DecidableEq n] (hA : A.PosSemidef) (i : n) : 0 ≤ hA.1.eigenvalues i :=
  hA.isHermitian.posSemidef_iff_eigenvalues_nonneg.mp hA _
/-
**Matrix.PosSemidef.re_dotProduct_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSe
midef`。
形式化陈述：re_dotProduct_nonneg (hA : A.PosSemidef) (x : n -> 𝕜) : 0 <= RCLike.re (st
ar x ⬝ᵥ (A *ᵥ x))
参数：hA : A.PosSemidef；x : n -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.nonneg_iff`：nonneg_iff : 0 <= z ↔ 0 <= re z ∧ im z = 0
· 使用定理 `Matrix.PosSemidef.dotProduct_mulVec_nonneg`：dotProduct_mulVec_nonneg {M 
: Matrix n n R} (hM : M.PosSemidef) : forall x : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x)
-/
lemma re_dotProduct_nonneg (hA : A.PosSemidef) (x : n → 𝕜) : 0 ≤ RCLike.re (star x ⬝ᵥ (A *ᵥ x)) :=
  RCLike.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg _) |>.1
/-
**Matrix.PosSemidef.det_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemidef`。
形式化陈述：det_nonneg [DecidableEq n] (hA : A.PosSemidef) : 0 <= A.det
参数：hA : A.PosSemidef。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.det_eq_prod_eigenvalues`：det_eq_prod_eigenvalues : de
t A = ∏ i, (hA.eigenvalues i : 𝕜)
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
-/
lemma det_nonneg [DecidableEq n] (hA : A.PosSemidef) : 0 ≤ A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg fun i _ ↦ by simpa using hA.eigenvalues_nonneg i
/-
**Matrix.PosSemidef.trace_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosSemid
ef`。
形式化陈述：trace_eq_zero_iff (hA : A.PosSemidef) : A.trace = 0 ↔ A = 0
参数：hA : A.PosSemidef。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `Unitary.conjStarAlgAut_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Se
miring R] [inst_1 : StarMul R] [inst_2 : SMul S R]   [inst_3 : IsScalarTower S R
 R] [inst_4 : SMul…
· 使用定理 `Matrix.trace_mul_cycle`：trace_mul_cycle [NonUnitalCommSemiring R] (A : M
atrix m n R) (B : Matrix n p R) (C : Matrix p m R) : trace (A * B * C) = trace (
C * A * B)
· 使用定理 `Unitary.coe_star_mul_self`：coe_star_mul_self (U : unitary R) : (star U :
 R) * U = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.trace_diagonal`：∀ {R : Type u_6} [inst : AddCommMonoid R] {o : Ty
pe u_8} [inst_1 : Fintype o] [inst_2 : DecidableEq o] (d : o → R),   (Matrix.dia
gonal d).tr…
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Matrix.PosSemidef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.Po
sSemidef) : M.IsHermitian
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsHermitian.eigenvalues_eq_zero_iff`：eigenvalues_eq_zero_iff : hA
.eigenvalues = 0 ↔ A = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma trace_eq_zero_iff (hA : A.PosSemidef) : A.trace = 0 ↔ A = 0 := by
  classical
  conv_lhs => rw [hA.1.spectral_theorem, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self,
    one_mul, trace_diagonal, Finset.sum_eq_zero_iff_of_nonneg (by simp [hA.eigenvalues_nonneg])]
  simp [← hA.isHermitian.eigenvalues_eq_zero_iff, funext_iff]

end PosSemidef

/-
**Matrix.eigenvalues_conjTranspose_mul_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix`。
形式化陈述：eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq 
n] (i : n) : 0 <= (isHermitian_conjTranspose_mul_self A).eigenvalues i
参数：A : Matrix m n 𝕜；i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
· 使用定理 `Matrix.posSemidef_conjTranspose_mul_self`：posSemidef_conjTranspose_mul_s
elf [StarOrderedRing R] (A : Matrix m n R) : PosSemidef (Aᴴ * A)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
-/
lemma eigenvalues_conjTranspose_mul_self_nonneg (A : Matrix m n 𝕜) [DecidableEq n] (i : n) :
    0 ≤ (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  (posSemidef_conjTranspose_mul_self _).eigenvalues_nonneg _
/-
**Matrix.eigenvalues_self_mul_conjTranspose_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix`。
形式化陈述：eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq 
m] (i : m) : 0 <= (isHermitian_mul_conjTranspose_self A).eigenvalues i
参数：A : Matrix m n 𝕜；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.PosSemidef.eigenvalues_nonneg`：eigenvalues_nonneg [DecidableEq n]
 (hA : A.PosSemidef) (i : n) : 0 <= hA.1.eigenvalues i
· 使用定理 `Matrix.posSemidef_self_mul_conjTranspose`：posSemidef_self_mul_conjTransp
ose [StarOrderedRing R] (A : Matrix m n R) : PosSemidef (A * Aᴴ)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
-/
lemma eigenvalues_self_mul_conjTranspose_nonneg (A : Matrix m n 𝕜) [DecidableEq m] (i : m) :
    0 ≤ (isHermitian_mul_conjTranspose_self A).eigenvalues i :=
  (posSemidef_self_mul_conjTranspose _).eigenvalues_nonneg _

/-! ### Positive definite matrices -/

/-- A Hermitian matrix is positive-definite if and only if its eigenvalues are positive. -/
/-
**Matrix.IsHermitian.posDef_iff_eigenvalues_pos** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.IsHermitian`。
形式化陈述：∀ {n : Type u_2} {𝕜 : Type u_3} [inst : Fintype n] [inst_1 : RCLike 𝕜] {A 
: Matrix n n 𝕜} [inst_2 : DecidableEq n]   (hA : A.IsHermitian), A.PosDef ↔ ∀ (i
 : n), 0 < hA.eigenvalues i
参数：hA : A.IsHermitian；i : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.IsUnit.posDef_star_right_conjugate_iff`：∀ {n : Type u_2} {R : Typ
e u_3} [inst : Ring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [inst_3 :
 Fintype n]   [inst_4 : DecidableEq…
· 使用定理 `Unitary.isUnit_coe`：isUnit_coe {U : unitary R} : IsUnit (U : R)
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A Hermitian matrix is positive-definite if and only if its eigenvalues are posit
ive.
-/
lemma IsHermitian.posDef_iff_eigenvalues_pos [DecidableEq n] (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [isUnit_coe.posDef_star_right_conjugate_iff]

namespace PosDef

/-
**Matrix.PosDef.re_dotProduct_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：re_dotProduct_pos (hA : A.PosDef) {x : n -> 𝕜} (hx : x != 0) : .1 0 < RCLi
ke.re (star x ⬝ᵥ (A *ᵥ x))
参数：hA : A.PosDef；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RCLike.pos_iff`：pos_iff : 0 < z ↔ 0 < re z ∧ im z = 0
· 使用引理 `Matrix.PosDef.dotProduct_mulVec_pos`：dotProduct_mulVec_pos {M : Matrix n
 n R} (hM : M.PosDef) {x} (hx : x != 0) : 0 < star x ⬝ᵥ (M *ᵥ x)
-/
lemma re_dotProduct_pos (hA : A.PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx) |>.1

/-- The eigenvalues of a positive definite matrix are positive. -/
/-
**Matrix.PosDef.eigenvalues_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：eigenvalues_pos [DecidableEq n] (hA : A.PosDef) (i : n) : 0 < hA.1.eigenva
lues i
参数：hA : A.PosDef；i : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.PosDef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.PosDef
) : M.IsHermitian
· 使用定理 `Matrix.IsHermitian.posDef_iff_eigenvalues_pos`：∀ {n : Type u_2} {𝕜 : Typ
e u_3} [inst : Fintype n] [inst_1 : RCLike 𝕜] {A : Matrix n n 𝕜} [inst_2 : Decid
ableEq n]   (hA : A.IsHermitian), A…

--- 原说明 ---
The eigenvalues of a positive definite matrix are positive.
-/
lemma eigenvalues_pos [DecidableEq n] (hA : A.PosDef) (i : n) : 0 < hA.1.eigenvalues i :=
  hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i
/-
**Matrix.PosDef.det_pos** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.PosDef`。
形式化陈述：det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A
参数：hA : A.PosDef。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.PosDef.isHermitian`：isHermitian {M : Matrix n n R} (hM : M.PosDef
) : M.IsHermitian
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.det_eq_prod_eigenvalues`：det_eq_prod_eigenvalues : de
t A = ∏ i, (hA.eigenvalues i : 𝕜)
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `RCLike.toIsStrictOrderedRing`：toIsStrictOrderedRing : IsStrictOrderedRin
g K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `Matrix.PosDef.eigenvalues_pos`：eigenvalues_pos [DecidableEq n] (hA : A.P
osDef) (i : n) : 0 < hA.1.eigenvalues i
-/
lemma det_pos [DecidableEq n] (hA : A.PosDef) : 0 < det A := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_pos
  intro i _
  simpa using hA.eigenvalues_pos i

end PosDef

set_option backward.privateInPublic true in
/-- The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toSeminormedAddCommGroup`, `Matrix.toNormedAddCommGroup`,
and `Matrix.toInnerProductSpace`. -/
@[instance_reducible]
/-
**Matrix.PosSemidef.preInnerProductSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-inner product space structure implementation. Only an auxiliary for
`Matrix.toSeminormedAddCommGroup`, `Matrix.toNormedAddCommGroup`,
and `Matrix.toInnerProductSpace`.
-/
private def PosSemidef.preInnerProductSpace {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    PreInnerProductSpace.Core 𝕜 (n → 𝕜) where
  inner x y := (M *ᵥ y) ⬝ᵥ star x
  conj_inner_symm x y := by
    rw [dotProduct_comm, star_dotProduct, starRingEnd_apply, star_star,
      star_mulVec, dotProduct_comm (M *ᵥ y), dotProduct_mulVec, hM.isHermitian.eq]
  re_inner_nonneg x := dotProduct_comm _ (star x) ▸ hM.re_dotProduct_nonneg x
  add_left := by simp only [star_add, dotProduct_add, forall_const]
  smul_left _ _ _ := by rw [← smul_eq_mul, ← dotProduct_smul, starRingEnd_apply, ← star_smul]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive semi-definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
/-
**Matrix.toSeminormedAddCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：toSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) : Seminorm
edAddCommGroup (n -> 𝕜)
参数：M : Matrix n n 𝕜；hM : M.PosSemidef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive semi-definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`.
-/
noncomputable abbrev toSeminormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    SeminormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup _ _ _ _ _ hM.preInnerProductSpace

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`. -/
/-
**Matrix.toNormedAddCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：toNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) : NormedAddCommGro
up (n -> 𝕜)
参数：M : Matrix n n 𝕜；hM : M.PosDef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive definite matrix `M` induces a norm `‖x‖ = sqrt (re xᴴMx)`.
-/
noncomputable abbrev toNormedAddCommGroup (M : Matrix n n 𝕜) (hM : M.PosDef) :
    NormedAddCommGroup (n → 𝕜) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _
  { __ := hM.posSemidef.preInnerProductSpace
    definite x (hx : _ ⬝ᵥ _ = 0) := by
      by_contra! h
      simpa [hx, lt_irrefl, dotProduct_comm] using hM.re_dotProduct_pos h }

/-- A positive semi-definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`. -/
@[instance_reducible]
/-
**Matrix.toInnerProductSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) : @InnerProduct
Space 𝕜 (n -> 𝕜) _ (M.toSeminormedAddCommGroup hM)
参数：M : Matrix n n 𝕜；hM : M.PosSemidef。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive semi-definite matrix `M` induces an inner product `⟪x, y⟫ = xᴴMy`.
-/
def toInnerProductSpace (M : Matrix n n 𝕜) (hM : M.PosSemidef) :
    @InnerProductSpace 𝕜 (n → 𝕜) _ (M.toSeminormedAddCommGroup hM) :=
  InnerProductSpace.ofCore _

end Matrix

