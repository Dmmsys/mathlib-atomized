/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrices of multivariate polynomials

In this file, we prove results about matrices over an `MvPolynomial` ring.
In particular, we provide `Matrix.mvPolynomialX` which associates every entry of a matrix with a
unique variable.

## Tags

matrix determinant, multivariate polynomial
-/

@[expose] public section


variable {m n R S : Type*}

namespace Matrix

variable (m n R)

/-- The matrix with variable `X (i,j)` at location `(i,j)`. -/
/-
**Matrix.mvPolynomialX** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix with variable `X (i,j)` at location `(i,j)`.
-/
noncomputable def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)

-- TODO: set as an equation lemma for `mvPolynomialX`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/-
**Matrix.mvPolynomialX_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mvPolynomialX_apply [CommSemiring R] (i j) : mvPolynomialX m n R i j = MvP
olynomial.X (i, j)
参数：i j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl

variable {m n R}

/-- Any matrix `A` can be expressed as the evaluation of `Matrix.mvPolynomialX`.

This is of particular use when `MvPolynomial (m × n) R` is an integral domain but `S` is
not, as if the `MvPolynomial.eval₂` can be pulled to the outside of a goal, it can be solved in
under cancellative assumptions. -/
/-
**Matrix.mvPolynomialX_map_eval** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any matrix `A` can be expressed as the evaluation of `Matrix.mvPolynomialX`.

This is of particular use when `MvPolynomial (m × n) R` is an integral domain bu
t `S` is
not, as if the `MvPolynomial.eval₂` can be pulled to the outside of a goal, it c
an be solved in
under cancellative assumptions.
-/
theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

/-- A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `RingHom` on the LHS. -/
/-
**Matrix.mvPolynomialX_mapMatrix_eval** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R] 
(A : Matrix m m R) : (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (m
vPolynomialX m m R) = A
参数：A : Matrix m m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mvPolynomialX_map_eval₂`：mvPolynomialX_map_eval₂ [CommSemiring R]
 [CommSemiring S] (f : R ->+* S) (A : Matrix m n S) : (mvPolynomialX m n R).map 
(MvPolynomial.eval₂ …

--- 原说明 ---
A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `RingHom` on the LH
S.
-/
theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (R)

/-- A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `AlgHom` on the LHS. -/
/-
**Matrix.mvPolynomialX_mapMatrix_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R]
 [CommSemiring S] [Algebra R S] (A : Matrix m m S) : (MvPolynomial.aeval fun p :
 m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A
参数：A : Matrix m m S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.mvPolynomialX_map_eval₂`：mvPolynomialX_map_eval₂ [CommSemiring R]
 [CommSemiring S] (f : R ->+* S) (A : Matrix m n S) : (mvPolynomialX m n R).map 
(MvPolynomial.eval₂ …

--- 原说明 ---
A variant of `Matrix.mvPolynomialX_map_eval₂` with a bundled `AlgHom` on the LHS
.
-/
theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (m)

/-- In a nontrivial ring, `Matrix.mvPolynomialX m m R` has non-zero determinant. -/
/-
**Matrix.det_mvPolynomialX_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontri
vial R] : det (mvPolynomialX m m R) != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.mvPolynomialX_mapMatrix_eval`：mvPolynomialX_mapMatrix_eval [Finty
pe m] [DecidableEq m] [CommSemiring R] (A : Matrix m m R) : (MvPolynomial.eval f
un p : m × m => A p.1 p.2…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1

--- 原说明 ---
In a nontrivial ring, `Matrix.mvPolynomialX m m R` has non-zero determinant.
-/
theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, map_zero] at this
  exact zero_ne_one this

/-- Evaluating the generic determinant polynomial `det (mvPolynomialX m m R)` at a point `s`
gives the determinant of the matrix obtained by substituting `s`. -/
/-
**Matrix.eval_det_mvPolynomialX** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：eval_det_mvPolynomialX [DecidableEq m] [Fintype m] [CommRing R] (s : m × m
 -> R) : MvPolynomial.eval s (det (mvPolynomialX m m R)) = det (Matrix.of fun i 
j : m => s (i, j))
参数：s : m × m -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Finty
pe n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] (f
 : R …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `MvPolynomial.eval_X`：eval_X : forall n, eval f (X n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Evaluating the generic determinant polynomial `det (mvPolynomialX m m R)` at a p
oint `s`
gives the determinant of the matrix obtained by substituting `s`.
-/
theorem eval_det_mvPolynomialX [DecidableEq m] [Fintype m] [CommRing R] (s : m × m → R) :
    MvPolynomial.eval s (det (mvPolynomialX m m R)) = det (Matrix.of fun i j : m => s (i, j)) := by
  rw [(MvPolynomial.eval s).map_det]
  congr 1
  ext i j
  simp [mvPolynomialX]

end Matrix

