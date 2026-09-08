/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Polynomial identities from evaluation at invertible matrices

We prove `MvPolynomial.eq_of_eval_eq_on_gl`: two polynomials in `MvPolynomial (m × m) k` over an
infinite field `k` are equal if their evaluations agree at every invertible matrix. The proof
uses that the set of invertible matrices is Zariski-dense in `Matrix m m k`.
-/

@[expose] public section

namespace MvPolynomial

/-- Two polynomials in `MvPolynomial (m × m) k` over an infinite field `k` are equal if their
evaluations agree at every invertible matrix.

The proof considers `(p - q) * det(X)`, where `det(X) := Matrix.det (Matrix.mvPolynomialX m m k)`
is the generic determinant polynomial. Evaluated at any `s : m × m → k`, this product vanishes:
if `det (Matrix.of fun i j => s (i, j)) = 0` the determinant factor kills it; otherwise the
matrix is invertible and the hypothesis applies. By `MvPolynomial.funext` the product is zero,
and since `det(X) ≠ 0` and `MvPolynomial _ k` is an integral domain, `p = q`. -/
/-
**MvPolynomial.eq_of_eval_eq_on_gl** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_of_eval_eq_on_gl {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [I
nfinite k] {p q : MvPolynomial (m × m) k} (h : forall g : Matrix.GeneralLinearGr
oup m k, MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) p = 
MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) q) : p = q
参数：m × m；h : forall g : Matrix.GeneralLinearGroup m k, MvPolynomial.eval (fun ij
 : m × m => (g : Matrix m m k) ij.1 ij.2) p = MvPolynomial.eval (fun ij : m × m 
=> (g : Matrix m m k) ij.1 ij.2) q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.funext`：funext {σ : Type*} {p q : MvPolynomial σ R} (h : fo
rall x : σ -> R, eval x p = eval x q) : p = q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Matrix.eval_det_mvPolynomialX`：eval_det_mvPolynomialX [DecidableEq m] [F
intype m] [CommRing R] (s : m × m -> R) : MvPolynomial.eval s (det (mvPolynomial
X m m R)) = det (Ma…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Matrix.det_mvPolynomialX_ne_zero`：det_mvPolynomialX_ne_zero [DecidableEq
 m] [Fintype m] [CommRing R] [Nontrivial R] : det (mvPolynomialX m m R) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R

--- 原说明 ---
Two polynomials in `MvPolynomial (m × m) k` over an infinite field `k` are equal
 if their
evaluations agree at every invertible matrix.

The proof considers `(p - q) * det(X)`, where `det(X) := Matrix.det (Matrix.mvPo
lynomialX m m k)`
is the generic determinant polynomial. Evaluated at any `s : m × m → k`, this pr
oduct vanishes:
if `det (Matrix.of fun i j => s (i, j)) = 0` the determinant factor kills it; ot
herwise the
matrix is invertible and the hypothesis applies. By `MvPolynomial.funext` the pr
oduct is zero,
and since `det(X) ≠ 0` and `MvPolynomial _ k` is an integral domain, `p = q`.
-/
theorem eq_of_eval_eq_on_gl {m k : Type*} [Fintype m] [DecidableEq m] [Field k] [Infinite k]
    {p q : MvPolynomial (m × m) k}
    (h : ∀ g : Matrix.GeneralLinearGroup m k,
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) p =
           MvPolynomial.eval (fun ij : m × m => (g : Matrix m m k) ij.1 ij.2) q) :
    p = q := by
  have hprod : (p - q) * Matrix.det (Matrix.mvPolynomialX m m k) = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_mul, map_sub, map_zero, Matrix.eval_det_mvPolynomialX]
    by_cases hs_det : Matrix.det (Matrix.of fun i j : m => s (i, j)) = 0
    · rw [hs_det, mul_zero]
    · have hh : (eval s) p = (eval s) q :=
        h (Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.of fun i j : m => s (i, j)) hs_det)
      rw [hh, sub_self, zero_mul]
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_right (Matrix.det_mvPolynomialX_ne_zero m k))

end MvPolynomial

