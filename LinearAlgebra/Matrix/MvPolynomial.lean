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

/--
Definition of `mvPolynomialX` / `mvPolynomialX` 的定义

English:
definition mvPolynomialX
  signature: [CommSemiring R]
  body: of fun i j => MvPolynomial.X (i, j)

中文:
定义 mvPolynomialX
  签名: [交换半环 R]
  定义体: of fun i j => MvPolynomial.X (i, j)

Depends on / 依赖: MvPolynomial, MvPolynomial.X
-/
noncomputable def mvPolynomialX [CommSemiring R] : Matrix m n (MvPolynomial (m × n) R) :=
  of fun i j => MvPolynomial.X (i, j)

-- TODO: set as an equation lemma for `mvPolynomialX`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `mvPolynomialX_apply` / 定理 `mvPolynomialX_apply`

English:
theorem mvPolynomialX_apply
  given: [CommSemiring R] (i j)
  proof: rfl

中文:
定理 mvPolynomialX_apply
  条件: [交换半环 R] (i j)
  证明: rfl
-/
theorem mvPolynomialX_apply [CommSemiring R] (i j) :
    mvPolynomialX m n R i j = MvPolynomial.X (i, j) :=
  rfl

variable {m n R}

/--
theorem `mvPolynomialX_map_eval₂` / 定理 `mvPolynomialX_map_eval₂`

English:
theorem mvPolynomialX_map_eval₂
  given: [CommSemiring R] [CommSemiring S] (f : R ->+* S) (A : Matrix m n S)
  proof: ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

中文:
定理 mvPolynomialX_map_eval₂
  条件: [交换半环 R] [交换半环 S] (f : R ->+* S) (A : 矩阵 m n S)
  证明: ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

Depends on / 依赖: MvPolynomial, MvPolynomial.eval
-/
theorem mvPolynomialX_map_eval₂ [CommSemiring R] [CommSemiring S] (f : R ->+* S) (A : Matrix m n S) :
    (mvPolynomialX m n R).map (MvPolynomial.eval₂ f fun p : m × n => A p.1 p.2) = A :=
  ext fun i j => MvPolynomial.eval₂_X _ (fun p : m × n => A p.1 p.2) (i, j)

/--
theorem `mvPolynomialX_mapMatrix_eval` / 定理 `mvPolynomialX_mapMatrix_eval`

English:
theorem mvPolynomialX_mapMatrix_eval
  statement: [Fintype m] [DecidableEq m] [CommSemiring R]
  proof: mvPolynomialX_map_eval₂ _ A

中文:
定理 mvPolynomialX_mapMatrix_eval
  结论: [有限类型 m] [DecidableEq m] [交换半环 R]
  证明: mvPolynomialX_map_eval₂ _ A
-/
theorem mvPolynomialX_mapMatrix_eval [Fintype m] [DecidableEq m] [CommSemiring R]
    (A : Matrix m m R) :
    (MvPolynomial.eval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (R)

/--
theorem `mvPolynomialX_mapMatrix_aeval` / 定理 `mvPolynomialX_mapMatrix_aeval`

English:
theorem mvPolynomialX_mapMatrix_aeval
  statement: [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
  proof: mvPolynomialX_map_eval₂ _ A

中文:
定理 mvPolynomialX_mapMatrix_aeval
  结论: [有限类型 m] [DecidableEq m] [交换半环 R] [交换半环 S]
  证明: mvPolynomialX_map_eval₂ _ A
-/
theorem mvPolynomialX_mapMatrix_aeval [Fintype m] [DecidableEq m] [CommSemiring R] [CommSemiring S]
    [Algebra R S] (A : Matrix m m S) :
    (MvPolynomial.aeval fun p : m × m => A p.1 p.2).mapMatrix (mvPolynomialX m m R) = A :=
  mvPolynomialX_map_eval₂ _ A

variable (m)

/--
theorem `det_mvPolynomialX_ne_zero` / 定理 `det_mvPolynomialX_ne_zero`

English:
theorem det_mvPolynomialX_ne_zero
  given: [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R]
  proof: by
  intro h_det
  have := congr_arg Matrix.det (mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one]; rw [← RingHom.map_det]; rw [h_det]; rw [map_zero] at this
  exact zero_ne_one this

中文:
定理 det_mvPolynomialX_ne_zero
  条件: [DecidableEq m] [有限类型 m] [交换环 R] [非平凡 R]
  证明: by
  intro h_det
  have := congr_arg Matrix.det (mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one]; rw [← RingHom.map_det]; rw [h_det]; rw [map_zero] at this
  exact zero_ne_one this

Depends on / 依赖: Matrix, Matrix.det, RingHom, RingHom.map_det, congr_arg, det_one, h_det, map_det, map_zero, mvPolynomialX_mapMatrix_eval, zero_ne_one
-/
theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (mvPolynomialX m m R) != 0 := by
  intro h_det
  have := congr_arg Matrix.det (mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one]; rw [← RingHom.map_det]; rw [h_det]; rw [map_zero] at this
  exact zero_ne_one this

/--
theorem `eval_det_mvPolynomialX` / 定理 `eval_det_mvPolynomialX`

English:
theorem eval_det_mvPolynomialX
  given: [DecidableEq m] [Fintype m] [CommRing R] (s : m × m -> R)
  proof: by
  rw [(MvPolynomial.eval s).map_det]
  congr 1
  ext i j
  simp [mvPolynomialX]

中文:
定理 eval_det_mvPolynomialX
  条件: [DecidableEq m] [有限类型 m] [交换环 R] (s : m × m -> R)
  证明: by
  rw [(MvPolynomial.eval s).map_det]
  congr 1
  ext i j
  simp [mvPolynomialX]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, map_det, mvPolynomialX
-/
theorem eval_det_mvPolynomialX [DecidableEq m] [Fintype m] [CommRing R] (s : m × m -> R) :
    MvPolynomial.eval s (det (mvPolynomialX m m R)) = det (Matrix.of fun i j : m => s (i, j)) := by
  rw [(MvPolynomial.eval s).map_det]
  congr 1
  ext i j
  simp [mvPolynomialX]

end Matrix
