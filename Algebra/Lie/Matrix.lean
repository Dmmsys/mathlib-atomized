/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Lie algebras of matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring. This file provides some very basic definitions whose
primary value stems from their utility when constructing the classical Lie algebras using matrices.

## Main definitions

  * `lieEquivMatrix'`
  * `Matrix.lieConj`
  * `Matrix.reindexLieEquiv`

## Tags

lie algebra, matrix
-/

@[expose] public section


universe u v w w₁ w₂

section Matrices

open scoped Matrix

variable {R : Type u} [CommRing R]
variable {n : Type w} [DecidableEq n] [Fintype n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
/-
**lieEquivMatrix'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lieEquivMatrix' : Module.End R (n -> R) ≃ₗ⁅R⁆ Matrix n n R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star

--- 原说明 ---
The natural equivalence between linear endomorphisms of finite free modules and 
square matrices
is compatible with the Lie algebra structures.
-/
def lieEquivMatrix' : Module.End R (n → R) ≃ₗ⁅R⁆ Matrix n n R :=
  { LinearMap.toMatrix' with
    map_lie' := fun {T S} => by
      let f := @LinearMap.toMatrix' R _ n n _ _
      change f (T.comp S - S.comp T) = f T * f S - f S * f T
      have h : ∀ T S : Module.End R _, f (T.comp S) = f T * f S := LinearMap.toMatrix'_comp
      rw [map_sub, h, h] }

@[simp]
/-
**lieEquivMatrix'_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type w} [inst_1 : DecidableEq n] [
inst_2 : Fintype n]   (f : Module.End R (n → R)), lieEquivMatrix' f = LinearMap.
toMatrix' f
参数：f : Module.End R (n → R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lieEquivMatrix'_apply (f : Module.End R (n → R)) :
    lieEquivMatrix' f = LinearMap.toMatrix' f :=
  rfl

@[simp]
/-
**lieEquivMatrix'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type w} [inst_1 : DecidableEq n] [
inst_2 : Fintype n] (A : Matrix n n R),   lieEquivMatrix'.symm A = Matrix.toLin'
 A
参数：A : Matrix n n R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem lieEquivMatrix'_symm_apply (A : Matrix n n R) :
    (@lieEquivMatrix' R _ n _ _).symm A = Matrix.toLin' A :=
  rfl

namespace Matrix

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
/-
**Matrix.lieConj** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix 
n n R
参数：P : Matrix n n R；h : Invertible P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invertible matrix induces a Lie algebra equivalence from the space of matrice
s to itself.
-/
def lieConj (P : Matrix n n R) (h : Invertible P) : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R :=
  ((@lieEquivMatrix' R _ n _ _).symm.trans (P.toLinearEquiv' h).lieConj).trans lieEquivMatrix'

@[simp]
/-
**Matrix.lieConj_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：lieConj_apply (P A : Matrix n n R) (h : Invertible P) : P.lieConj h A = P 
* A * P⁻¹
参数：P A : Matrix n n R；h : Invertible P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearMap.toMatrix'_comp`：∀ {R : Type u_1} [inst : CommSemiring R] {l : 
Type u_3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fin
type n] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieConj_apply (P A : Matrix n n R) (h : Invertible P) :
    P.lieConj h A = P * A * P⁻¹ := by
  simp [LinearEquiv.conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

@[simp]
/-
**Matrix.lieConj_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) : (P.lieConj h)
.symm A = P⁻¹ * A * P
参数：P A : Matrix n n R；h : Invertible P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Matrix.invOf_eq_nonsing_inv`：invOf_eq_nonsing_inv [Invertible A] : ⅟A = 
A⁻¹
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `LinearMap.toMatrix'_comp`：∀ {R : Type u_1} [inst : CommSemiring R] {l : 
Type u_3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fin
type n] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) :
    (P.lieConj h).symm A = P⁻¹ * A * P := by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

set_option backward.isDefEq.respectTransparency false in
/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `Matrix.reindex`, is an equivalence of Lie algebras. -/
/-
**Matrix.reindexLieEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For square matrices, the natural map that reindexes a matrix's rows and columns 
with equivalent
types, `Matrix.reindex`, is an equivalence of Lie algebras.
-/
def reindexLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix m m R :=
  { Matrix.reindexLinearEquiv R R e e with
    toFun := Matrix.reindex e e
    map_lie' := fun {_ _} => by
      simp only [LieRing.of_associative_ring_bracket, Matrix.reindex_apply,
        Matrix.submatrix_mul_equiv, Matrix.submatrix_sub, Pi.sub_apply] }

@[simp]
/-
**Matrix.reindexLieEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLieEquiv_apply (M : Matrix n n R) : Matrix.reindexLieEquiv e M = Ma
trix.reindex e e M
参数：M : Matrix n n R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexLieEquiv_apply (M : Matrix n n R) :
    Matrix.reindexLieEquiv e M = Matrix.reindex e e M :=
  rfl

@[simp]
/-
**Matrix.reindexLieEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：reindexLieEquiv_symm : (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matri
x.reindexLieEquiv e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reindexLieEquiv_symm :
    (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm :=
  rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule (Matrix n n R) (n → R) where
  bracket := mulVec
  add_lie := add_mulVec
  lie_add := mulVec_add
  leibniz_lie x y v := by simp only [Ring.lie_def, mulVec_mulVec, sub_mulVec, sub_add_cancel]
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule R (Matrix n n R) (n → R) where
  smul_lie := smul_mulVec
  lie_smul t A := mulVec_smul A t
/-
**Matrix.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {n : Type w} [inst_1 : DecidableEq n] [
inst_2 : Fintype n] (A : Matrix n n R)   (v : n → R), ⁅A, v⁆ = A.mulVec v
参数：A : Matrix n n R；v : n → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lie_apply (A : Matrix n n R) (v : n → R) : ⁅A, v⁆ = A *ᵥ v := rfl

end Matrix

namespace LieModule

@[simp]
/-
**LieModule.toEnd_matrix** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：toEnd_matrix : toEnd R (Matrix n n R) (n -> R) = (lieEquivMatrix' (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.ext`：ext {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
· 使用定理 `Matrix.instLieModuleForall`：∀ {R : Type u} [inst : CommRing R] {n : Type
 w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule R (Matrix n n R) 
(n → R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
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
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toEnd_matrix :
    toEnd R (Matrix n n R) (n → R) = (lieEquivMatrix' (R := R) (n := n)).symm := by
  ext; simp
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFaithful R (Matrix n n R) (n → R) where
  injective_toEnd := by
    simpa using EmbeddingLike.injective _

end LieModule

end Matrices

