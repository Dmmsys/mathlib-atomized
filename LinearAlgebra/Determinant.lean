/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Tactic.FieldSimp

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`LinearAlgebra.Matrix.Determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `Basis.det`: the determinant of a family of vectors with respect to a basis,
  as a multilinear map
* `LinearMap.det`: the determinant of an endomorphism `f : End R M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)
* `LinearEquiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
  multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
  result is `1` instead)

## Tags

basis, det, determinant
-/

@[expose] public section


noncomputable section

open Matrix Module LinearMap Submodule Set Function

universe u v w

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (e : Basis ι R M)

section Conjugate

variable {A : Type*} [CommRing A]
variable {m n : Type*}

/--
Definition of `equivOfPiLEquivPi` / `equivOfPiLEquivPi` 的定义

English:
definition equivOfPiLEquivPi
  signature: {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
  body: Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

中文:
定义 equivOfPiLEquivPi
  签名: {R : 类型} [有限 m] [有限 n] [交换环 R] [非平凡 R]
  定义体: Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

Depends on / 依赖: Basis.indexEquiv, Basis.ofEquivFun, Pi.basisFun, basisFun, e.symm, indexEquiv, ofEquivFun
-/
def equivOfPiLEquivPi {R : Type*} [Finite m] [Finite n] [CommRing R] [Nontrivial R]
    (e : (m -> R) ≃ₗ[R] n -> R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

namespace Matrix

variable [Fintype m] [Fintype n]

/--
Definition of `indexEquivOfInv` / `indexEquivOfInv` 的定义

English:
definition indexEquivOfInv
  signature: [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
  body: equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)

中文:
定义 indexEquivOfInv
  签名: [非平凡 A] [DecidableEq m] [DecidableEq n] {M : 矩阵 m n A}
  定义体: equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)

Depends on / 依赖: equivOfPiLEquivPi
-/
def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : m ≃ n :=
  equivOfPiLEquivPi (toLin'OfInv hMM' hM'M)

/--
theorem `det_comm` / 定理 `det_comm`

English:
theorem det_comm
  given: [DecidableEq n] (M N : Matrix n n A)
  statement: det (M * N) = det (N * M)
  proof: by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

中文:
定理 det_comm
  条件: [DecidableEq n] (M N : 矩阵 n n A)
  结论: det (M * N) = det (N * M)
  证明: by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

Depends on / 依赖: det_mul, mul_comm
-/
theorem det_comm [DecidableEq n] (M N : Matrix n n A) : det (M * N) = det (N * M) := by
  rw [det_mul]; rw [det_mul]; rw [mul_comm]

/--
theorem `det_comm'` / 定理 `det_comm'`

English:
theorem det_comm'
  statement: [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A}
  proof: by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e]; rw [← submatrix_mul_equiv _ _ _ (Equiv.refl n) _]; rw [det_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

中文:
定理 det_comm'
  结论: [DecidableEq m] [DecidableEq n] {M : 矩阵 n m A} {N : 矩阵 m n A}
  证明: by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e]; rw [← submatrix_mul_equiv _ _ _ (Equiv.refl n) _]; rw [det_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

Depends on / 依赖: nontriviality
-/
theorem det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A}
    {M' : Matrix m n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) : det (M * N) = det (N * M) := by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := indexEquivOfInv hMM' hM'M
  rw [← det_submatrix_equiv_self e]; rw [← submatrix_mul_equiv _ _ _ (Equiv.refl n) _]; rw [det_comm]; rw [submatrix_mul_equiv]; rw [Equiv.coe_refl]; rw [submatrix_id_id]

/--
theorem `det_conj_of_mul_eq_one` / 定理 `det_conj_of_mul_eq_one`

English:
theorem det_conj_of_mul_eq_one
  statement: [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
  proof: by
  rw [← det_comm' hM'M hMM']; rw [← Matrix.mul_assoc]; rw [hM'M]; rw [Matrix.one_mul]

中文:
定理 det_conj_of_mul_eq_one
  结论: [DecidableEq m] [DecidableEq n] {M : 矩阵 m n A}
  证明: by
  rw [← det_comm' hM'M hMM']; rw [← Matrix.mul_assoc]; rw [hM'M]; rw [Matrix.one_mul]

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.one_mul, det_comm, mul_assoc, one_mul
-/
theorem det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A}
    {M' : Matrix n m A} {N : Matrix n n A} (hMM' : M * M' = 1) (hM'M : M' * M = 1) :
    det (M * N * M') = det N := by
  rw [← det_comm' hM'M hMM']; rw [← Matrix.mul_assoc]; rw [hM'M]; rw [Matrix.one_mul]

end Matrix

end Conjugate

namespace LinearMap

/-! ### Determinant of a linear map -/


variable {A : Type*} [CommRing A] [Module A M]
variable {κ : Type*} [Fintype κ]

/--
theorem `det_toMatrix_eq_det_toMatrix` / 定理 `det_toMatrix_eq_det_toMatrix`

English:
theorem det_toMatrix_eq_det_toMatrix
  statement: [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M)
  proof: by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c]; rw [← basis_toMatrix_mul_linearMap_toMatrix b c b]; rw [Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix]; rw [Basis.toMatrix_self]

中文:
定理 det_toMatrix_eq_det_toMatrix
  结论: [DecidableEq κ] (b : 基 ι A M) (c : 基 κ A M)
  证明: by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c]; rw [← basis_toMatrix_mul_linearMap_toMatrix b c b]; rw [Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix]; rw [Basis.toMatrix_self]

Depends on / 依赖: Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self, Matrix, Matrix.det_conj_of_mul_eq_one, basis_toMatrix_mul_linearMap_toMatrix, det_conj_of_mul_eq_one, linearMap_toMatrix_mul_basis_toMatrix, toMatrix_mul_toMatrix, toMatrix_self
-/
theorem det_toMatrix_eq_det_toMatrix [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M)
    (f : M ->ₗ[A] M) : det (LinearMap.toMatrix b b f) = det (LinearMap.toMatrix c c f) := by
  rw [← linearMap_toMatrix_mul_basis_toMatrix c b c]; rw [← basis_toMatrix_mul_linearMap_toMatrix b c b]; rw [Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.toMatrix_mul_toMatrix]; rw [Basis.toMatrix_self]


/-- The determinant of an endomorphism given a basis.

See `LinearMap.det` for a version that populates the basis non-computably.

Although the `Trunc (Basis ι A M)` parameter makes it slightly more convenient to switch bases,
there is no good way to generalize over universe parameters, so we can't fully state in `detAux`'s
type that it does not depend on the choice of basis. Instead you can use the `detAux_def''` lemma,
or avoid mentioning a basis at all using `LinearMap.det`.
-/
irreducible_def detAux : Trunc (Basis ι A M) -> (M ->ₗ[A] M) ->* A :=
  Trunc.lift
    (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M ->ₗ[A] M) ->* Matrix ι ι A))
fun b c => MonoidHom.ext det_toMatrix_eq_det_toMatrix b c

/--
theorem `detAux_def'` / 定理 `detAux_def'`

English:
theorem detAux_def'
  given: (b : Basis ι A M) (f : M ->ₗ[A] M)
  proof: by
  #adaptation_note /-- Proof repaired after leanprover/lean4#13492.
  The first line below was previously just `rw [detAux]`.
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  simp only [detAux_def, Trunc.lift_mk]
  rfl

中文:
定理 detAux_def'
  条件: (b : 基 ι A M) (f : M ->ₗ[A] M)
  证明: by
  #adaptation_note /-- Proof repaired after leanprover/lean4#13492.
  The first line below was previously just `rw [detAux]`.
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  simp only [detAux_def, Trunc.lift_mk]
  rfl

Depends on / 依赖: Trunc.lift_mk, adaptation_note, addressing, appropriately, approve, authors, detAux, detAux_def, either, leanprover, lift_mk, maintainers, minimize, prerequisites, previously, problem, removing, repaired, replacement, request
-/
theorem detAux_def' (b : Basis ι A M) (f : M ->ₗ[A] M) :
    LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f) := by
  #adaptation_note /-- Proof repaired after leanprover/lean4#13492.
  The first line below was previously just `rw [detAux]`.
  The replacement proof is a short-term fix, and we request that the authors/maintainers of
  this file review the proof, and either approve it by removing this note, revise
  the proof or the prerequisites appropriately, or minimize a problem in lean4 that still
  needs addressing. -/
  simp only [detAux_def, Trunc.lift_mk]
  rfl

/--
theorem `detAux_def''` / 定理 `detAux_def''`

English:
theorem detAux_def''
  statement: {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
  proof: by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']

@[simp]

中文:
定理 detAux_def''
  结论: {ι' : 类型} [有限类型 ι'] [DecidableEq ι'] (tb : Trunc <| 基 ι A M)
  证明: by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']

@[simp]

Depends on / 依赖: Trunc.induction_on, detAux_def, det_toMatrix_eq_det_toMatrix, induction_on
-/
theorem detAux_def'' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M)
    (b' : Basis ι' A M) (f : M ->ₗ[A] M) :
    LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  induction tb using Trunc.induction_on with
  | h b => rw [detAux_def', det_toMatrix_eq_det_toMatrix b b']

@[simp]
/--
theorem `detAux_id` / 定理 `detAux_id`

English:
theorem detAux_id
  given: (b : Trunc <| Basis ι A M)
  statement: LinearMap.detAux b LinearMap.id = 1
  proof: (LinearMap.detAux b).map_one

@[simp]

中文:
定理 detAux_id
  条件: (b : Trunc <| 基 ι A M)
  结论: 线性映射.detAux b 线性映射.id = 1
  证明: (LinearMap.detAux b).map_one

@[simp]

Depends on / 依赖: LinearMap, LinearMap.detAux, detAux, map_one
-/
theorem detAux_id (b : Trunc <| Basis ι A M) : LinearMap.detAux b LinearMap.id = 1 :=
  (LinearMap.detAux b).map_one

@[simp]
/--
theorem `detAux_comp` / 定理 `detAux_comp`

English:
theorem detAux_comp
  given: (b : Trunc <| Basis ι A M) (f g : M ->ₗ[A] M)
  proof: (LinearMap.detAux b).map_mul f g

中文:
定理 detAux_comp
  条件: (b : Trunc <| 基 ι A M) (f g : M ->ₗ[A] M)
  证明: (LinearMap.detAux b).map_mul f g

Depends on / 依赖: LinearMap, LinearMap.detAux, detAux, map_mul
-/
theorem detAux_comp (b : Trunc <| Basis ι A M) (f g : M ->ₗ[A] M) :
    LinearMap.detAux b (f.comp g) = LinearMap.detAux b f * LinearMap.detAux b g :=
  (LinearMap.detAux b).map_mul f g

section

open scoped Classical in
-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
protected irreducible_def det : (M ->ₗ[A] M) ->* A :=
  if H : exists s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.choose_spec.some)
  else 1

open scoped Classical in
/--
theorem `coe_det` / 定理 `coe_det`

English:
theorem coe_det
  given: [DecidableEq M]
  proof: by
  ext
  rw [LinearMap.det_def]
  split_ifs
  · congr -- use the correct `DecidableEq` instance
  rfl

中文:
定理 coe_det
  条件: [DecidableEq M]
  证明: by
  ext
  rw [LinearMap.det_def]
  split_ifs
  · congr -- use the correct `DecidableEq` instance
  rfl

Depends on / 依赖: DecidableEq, LinearMap, LinearMap.det_def, correct, det_def, instance, split_ifs
-/
theorem coe_det [DecidableEq M] :
    ⇑(LinearMap.det : (M ->ₗ[A] M) ->* A) =
      if H : exists s : Finset M, Nonempty (Basis s A M) then
        LinearMap.detAux (Trunc.mk H.choose_spec.some)
      else 1 := by
  ext
  rw [LinearMap.det_def]
  split_ifs
  · congr -- use the correct `DecidableEq` instance
  rfl

/--
theorem `_root_.Module.Free.of_det_ne_one` / 定理 `_root_.Module.Free.of_det_ne_one`

English:
theorem _root_.Module.Free.of_det_ne_one
  given: {f : M ->ₗ[R] M} (hf : f.det != 1)
  proof: by
  by_cases H : exists s : Finset M, Nonempty (Module.Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

中文:
定理 _root_.模.自由.of_det_ne_one
  条件: {f : M ->ₗ[R] M} (hf : f.det != 1)
  证明: by
  by_cases H : exists s : Finset M, Nonempty (Module.Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

Depends on / 依赖: Finset, LinearMap, LinearMap.coe_det, Module, Module.Basis, Module.Free.of_basis, Nonempty, classical, coe_det, of_basis
-/
theorem _root_.Module.Free.of_det_ne_one {f : M ->ₗ[R] M} (hf : f.det != 1) :
    Module.Free R M := by
  by_cases H : exists s : Finset M, Nonempty (Module.Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

end

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `LinearMap.det_toMatrix`)
/--
theorem `det_eq_det_toMatrix_of_finset` / 定理 `det_eq_det_toMatrix_of_finset`

English:
theorem det_eq_det_toMatrix_of_finset
  statement: [DecidableEq M] {s : Finset M} (b : Basis s A M)
  proof: by
  have : exists s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det]; rw [dif_pos this]; rw [detAux_def'' _ b]

@[simp]

中文:
定理 det_eq_det_toMatrix_of_finset
  结论: [DecidableEq M] {s : 有限集 M} (b : 基 s A M)
  证明: by
  have : exists s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det]; rw [dif_pos this]; rw [detAux_def'' _ b]

@[simp]

Depends on / 依赖: Finset, LinearMap, LinearMap.coe_det, Nonempty, coe_det, detAux_def, dif_pos
-/
theorem det_eq_det_toMatrix_of_finset [DecidableEq M] {s : Finset M} (b : Basis s A M)
    (f : M ->ₗ[A] M) : LinearMap.det f = Matrix.det (LinearMap.toMatrix b b f) := by
  have : exists s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det]; rw [dif_pos this]; rw [detAux_def'' _ b]

@[simp]
/--
theorem `det_toMatrix` / 定理 `det_toMatrix`

English:
theorem det_toMatrix
  given: (b : Basis ι A M) (f : M ->ₗ[A] M)
  proof: by
  have := Classical.decEq M
  rw [det_eq_det_toMatrix_of_finset b.reindexFinsetRange]; rw [det_toMatrix_eq_det_toMatrix b b.reindexFinsetRange]

@[simp]

中文:
定理 det_toMatrix
  条件: (b : 基 ι A M) (f : M ->ₗ[A] M)
  证明: by
  have := Classical.decEq M
  rw [det_eq_det_toMatrix_of_finset b.reindexFinsetRange]; rw [det_toMatrix_eq_det_toMatrix b b.reindexFinsetRange]

@[simp]

Depends on / 依赖: Classical, Classical.decEq, b.reindexFinsetRange, det_eq_det_toMatrix_of_finset, det_toMatrix_eq_det_toMatrix, reindexFinsetRange
-/
theorem det_toMatrix (b : Basis ι A M) (f : M ->ₗ[A] M) :
    Matrix.det (toMatrix b b f) = LinearMap.det f := by
  have := Classical.decEq M
  rw [det_eq_det_toMatrix_of_finset b.reindexFinsetRange]; rw [det_toMatrix_eq_det_toMatrix b b.reindexFinsetRange]

@[simp]
/--
theorem `det_toMatrix'` / 定理 `det_toMatrix'`

English:
theorem det_toMatrix'
  given: {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι -> A) ->ₗ[A] ι -> A)
  proof: by simp [← toMatrix_eq_toMatrix']

@[simp]

中文:
定理 det_toMatrix'
  条件: {ι : 类型} [有限类型 ι] [DecidableEq ι] (f : (ι -> A) ->ₗ[A] ι -> A)
  证明: by simp [← toMatrix_eq_toMatrix']

@[simp]

Depends on / 依赖: toMatrix_eq_toMatrix
-/
theorem det_toMatrix' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι -> A) ->ₗ[A] ι -> A) :
    Matrix.det (LinearMap.toMatrix' f) = LinearMap.det f := by simp [← toMatrix_eq_toMatrix']

@[simp]
/--
theorem `det_toLin` / 定理 `det_toLin`

English:
theorem det_toLin
  given: (b : Basis ι R M) (f : Matrix ι ι R)
  proof: by
  rw [← LinearMap.det_toMatrix b]; rw [LinearMap.toMatrix_toLin]

@[simp]

中文:
定理 det_toLin
  条件: (b : 基 ι R M) (f : 矩阵 ι ι R)
  证明: by
  rw [← LinearMap.det_toMatrix b]; rw [LinearMap.toMatrix_toLin]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, LinearMap.toMatrix_toLin, det_toMatrix, toMatrix_toLin
-/
theorem det_toLin (b : Basis ι R M) (f : Matrix ι ι R) :
    LinearMap.det (Matrix.toLin b b f) = f.det := by
  rw [← LinearMap.det_toMatrix b]; rw [LinearMap.toMatrix_toLin]

@[simp]
/--
theorem `det_toLin'` / 定理 `det_toLin'`

English:
theorem det_toLin'
  given: (f : Matrix ι ι R)
  statement: LinearMap.det (Matrix.toLin' f) = Matrix.det f
  proof: by
  simp only [← toLin_eq_toLin', det_toLin]

中文:
定理 det_toLin'
  条件: (f : 矩阵 ι ι R)
  结论: 线性映射.det (矩阵.toLin' f) = 矩阵.det f
  证明: by
  simp only [← toLin_eq_toLin', det_toLin]

Depends on / 依赖: det_toLin, toLin_eq_toLin
-/
theorem det_toLin' (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin' f) = Matrix.det f := by
  simp only [← toLin_eq_toLin', det_toLin]

/-- To show `P (LinearMap.det f)` it suffices to consider `P (Matrix.det (toMatrix _ _ f))` and
`P 1`. -/
@[elab_as_elim]
/--
theorem `det_cases` / 定理 `det_cases`

English:
theorem det_cases
  statement: [DecidableEq M] {P : A -> Prop} (f : M ->ₗ[A] M)
  proof: by
  if H : exists s : Finset M, Nonempty (Basis s A M) then
    obtain ⟨s, ⟨b⟩⟩ := H
    rw [← det_toMatrix b]
    exact hb s b
  else
    rwa [LinearMap.det_def, dif_neg H]

@[simp]

中文:
定理 det_cases
  结论: [DecidableEq M] {P : A -> 命题} (f : M ->ₗ[A] M)
  证明: by
  if H : exists s : Finset M, Nonempty (Basis s A M) then
    obtain ⟨s, ⟨b⟩⟩ := H
    rw [← det_toMatrix b]
    exact hb s b
  else
    rwa [LinearMap.det_def, dif_neg H]

@[simp]

Depends on / 依赖: Finset, LinearMap, LinearMap.det_def, Nonempty, det_def, det_toMatrix, dif_neg
-/
theorem det_cases [DecidableEq M] {P : A -> Prop} (f : M ->ₗ[A] M)
    (hb : forall (s : Finset M) (b : Basis s A M), P (Matrix.det (toMatrix b b f))) (h1 : P 1) :
    P (LinearMap.det f) := by
  if H : exists s : Finset M, Nonempty (Basis s A M) then
    obtain ⟨s, ⟨b⟩⟩ := H
    rw [← det_toMatrix b]
    exact hb s b
  else
    rwa [LinearMap.det_def, dif_neg H]

@[simp]
/--
theorem `det_comp` / 定理 `det_comp`

English:
theorem det_comp
  given: (f g : M ->ₗ[A] M)
  proof: LinearMap.det.map_mul f g

@[simp]

中文:
定理 det_comp
  条件: (f g : M ->ₗ[A] M)
  证明: LinearMap.det.map_mul f g

@[simp]

Depends on / 依赖: LinearMap, LinearMap.det.map_mul, map_mul
-/
theorem det_comp (f g : M ->ₗ[A] M) :
    LinearMap.det (f.comp g) = LinearMap.det f * LinearMap.det g :=
  LinearMap.det.map_mul f g

@[simp]
/--
theorem `det_id` / 定理 `det_id`

English:
theorem det_id
  statement: LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
  proof: LinearMap.det.map_one

中文:
定理 det_id
  结论: 线性映射.det (线性映射.id : M ->ₗ[A] M) = 1
  证明: LinearMap.det.map_one

Depends on / 依赖: LinearMap, LinearMap.det.map_one, map_one
-/
theorem det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1 :=
  LinearMap.det.map_one

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`. -/
@[simp]
/--
theorem `det_smul` / 定理 `det_smul`

English:
theorem det_smul
  given: [Module.Free A M] (c : A) (f : M ->ₗ[A] M)
  proof: by
  nontriviality A
  by_cases H : exists s : Finset M, Nonempty (Basis s A M)
  · have : Module.Finite A M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact Module.Finite.of_basis hs
    simp only [← det_toMatrix (Module.finBasis A M), map_smul, Fintype.card_fin, Matrix.det_smul]
  · classical
      have : Module.finrank A M = 0 := finrank_eq_zero_of_not_exists_basis H
      simp [coe_det, H, this]

中文:
定理 det_smul
  条件: [模.自由 A M] (c : A) (f : M ->ₗ[A] M)
  证明: by
  nontriviality A
  by_cases H : exists s : Finset M, Nonempty (Basis s A M)
  · have : Module.Finite A M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact Module.Finite.of_basis hs
    simp only [← det_toMatrix (Module.finBasis A M), map_smul, Fintype.card_fin, Matrix.det_smul]
  · classical
      have : Module.finrank A M = 0 := finrank_eq_zero_of_not_exists_basis H
      simp [coe_det, H, this]

Depends on / 依赖: Finite, Finset, Fintype, Fintype.card_fin, Matrix, Matrix.det_smul, Module, Module.Finite, Module.Finite.of_basis, Module.finBasis, Module.finrank, Nonempty, card_fin, classical, coe_det, det_smul, det_toMatrix, finBasis, finrank, finrank_eq_zero_of_not_exists_basis
-/
theorem det_smul [Module.Free A M] (c : A) (f : M ->ₗ[A] M) :
    LinearMap.det (c • f) = c ^ Module.finrank A M * LinearMap.det f := by
  nontriviality A
  by_cases H : exists s : Finset M, Nonempty (Basis s A M)
  · have : Module.Finite A M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact Module.Finite.of_basis hs
    simp only [← det_toMatrix (Module.finBasis A M), map_smul, Fintype.card_fin, Matrix.det_smul]
  · classical
      have : Module.finrank A M = 0 := finrank_eq_zero_of_not_exists_basis H
      simp [coe_det, H, this]

/--
theorem `det_zero'` / 定理 `det_zero'`

English:
theorem det_zero'
  given: {ι : Type*} [Finite ι] [Nonempty ι] (b : Basis ι A M)
  proof: by
  have := Classical.decEq ι
  cases nonempty_fintype ι
  rw [← det_toMatrix b]; rw [map_zero]; rw [det_zero]

中文:
定理 det_zero'
  条件: {ι : 类型} [有限 ι] [非空 ι] (b : 基 ι A M)
  证明: by
  have := Classical.decEq ι
  cases nonempty_fintype ι
  rw [← det_toMatrix b]; rw [map_zero]; rw [det_zero]

Depends on / 依赖: Classical, Classical.decEq, det_toMatrix, det_zero, map_zero, nonempty_fintype
-/
theorem det_zero' {ι : Type*} [Finite ι] [Nonempty ι] (b : Basis ι A M) :
    LinearMap.det (0 : M ->ₗ[A] M) = 0 := by
  have := Classical.decEq ι
  cases nonempty_fintype ι
  rw [← det_toMatrix b]; rw [map_zero]; rw [det_zero]

/-- In a finite-dimensional vector space, the zero map has determinant `1` in dimension `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, where we define
the determinant to be `1`. -/
@[simp]
/--
theorem `det_zero` / 定理 `det_zero`

English:
theorem det_zero
  given: [Module.Free A M]
  proof: by
  simp only [← zero_smul A (1 : M ->ₗ[A] M), det_smul, mul_one, map_one]

中文:
定理 det_zero
  条件: [模.自由 A M]
  证明: by
  simp only [← zero_smul A (1 : M ->ₗ[A] M), det_smul, mul_one, map_one]

Depends on / 依赖: det_smul, map_one, mul_one, zero_smul
-/
theorem det_zero [Module.Free A M] :
    LinearMap.det (0 : M ->ₗ[A] M) = (0 : A) ^ Module.finrank A M := by
  simp only [← zero_smul A (1 : M ->ₗ[A] M), det_smul, mul_one, map_one]

/--
theorem `det_eq_one_of_not_module_finite` / 定理 `det_eq_one_of_not_module_finite`

English:
theorem det_eq_one_of_not_module_finite
  given: (h : ¬Module.Finite R M) (f : M ->ₗ[R] M)
  statement: f.det = 1
  proof: by
  rw [LinearMap.det]; rw [dif_neg]; rw [MonoidHom.one_apply]
  exact fun ⟨_, ⟨b⟩⟩ => h (Module.Finite.of_basis b)

@[nontriviality]

中文:
定理 det_eq_one_of_not_module_finite
  条件: (h : ¬模.有限 R M) (f : M ->ₗ[R] M)
  结论: f.det = 1
  证明: by
  rw [LinearMap.det]; rw [dif_neg]; rw [MonoidHom.one_apply]
  exact fun ⟨_, ⟨b⟩⟩ => h (Module.Finite.of_basis b)

@[nontriviality]

Depends on / 依赖: Finite, LinearMap, LinearMap.det, Module, Module.Finite.of_basis, MonoidHom, MonoidHom.one_apply, dif_neg, of_basis, one_apply
-/
theorem det_eq_one_of_not_module_finite (h : ¬Module.Finite R M) (f : M ->ₗ[R] M) : f.det = 1 := by
  rw [LinearMap.det]; rw [dif_neg]; rw [MonoidHom.one_apply]
  exact fun ⟨_, ⟨b⟩⟩ => h (Module.Finite.of_basis b)

@[nontriviality]
/--
theorem `det_eq_one_of_subsingleton` / 定理 `det_eq_one_of_subsingleton`

English:
theorem det_eq_one_of_subsingleton
  given: [Subsingleton M] (f : M ->ₗ[R] M)
  proof: by
  have b : Basis (Fin 0) R M := Basis.empty M
  rw [← f.det_toMatrix b]
  exact Matrix.det_isEmpty

中文:
定理 det_eq_one_of_subsingleton
  条件: [子单例 M] (f : M ->ₗ[R] M)
  证明: by
  have b : Basis (Fin 0) R M := Basis.empty M
  rw [← f.det_toMatrix b]
  exact Matrix.det_isEmpty

Depends on / 依赖: Basis.empty, Matrix, Matrix.det_isEmpty, det_isEmpty, det_toMatrix, f.det_toMatrix
-/
theorem det_eq_one_of_subsingleton [Subsingleton M] (f : M ->ₗ[R] M) :
    LinearMap.det (f : M ->ₗ[R] M) = 1 := by
  have b : Basis (Fin 0) R M := Basis.empty M
  rw [← f.det_toMatrix b]
  exact Matrix.det_isEmpty

/--
theorem `det_eq_one_of_finrank_eq_zero` / 定理 `det_eq_one_of_finrank_eq_zero`

English:
theorem det_eq_one_of_finrank_eq_zero
  statement: {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
  proof: by
  classical
    refine @LinearMap.det_cases M _ 𝕜 _ _ _ (fun t => t = 1) f ?_ rfl
    intro s b
    have : IsEmpty s := by
      rw [← Fintype.card_eq_zero_iff]
      exact (Module.finrank_eq_card_basis b).symm.trans h
    exact Matrix.det_isEmpty

中文:
定理 det_eq_one_of_finrank_eq_zero
  结论: {𝕜 : 类型} [域 𝕜] {M : 类型} [加法交换群 M]
  证明: by
  classical
    refine @LinearMap.det_cases M _ 𝕜 _ _ _ (fun t => t = 1) f ?_ rfl
    intro s b
    have : IsEmpty s := by
      rw [← Fintype.card_eq_zero_iff]
      exact (Module.finrank_eq_card_basis b).symm.trans h
    exact Matrix.det_isEmpty

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff, IsEmpty, LinearMap, LinearMap.det_cases, Matrix, Matrix.det_isEmpty, Module, Module.finrank_eq_card_basis, card_eq_zero_iff, classical, det_cases, det_isEmpty, finrank_eq_card_basis, symm.trans
-/
theorem det_eq_one_of_finrank_eq_zero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] (h : Module.finrank 𝕜 M = 0) (f : M ->ₗ[𝕜] M) :
    LinearMap.det (f : M ->ₗ[𝕜] M) = 1 := by
  classical
    refine @LinearMap.det_cases M _ 𝕜 _ _ _ (fun t => t = 1) f ?_ rfl
    intro s b
    have : IsEmpty s := by
      rw [← Fintype.card_eq_zero_iff]
      exact (Module.finrank_eq_card_basis b).symm.trans h
    exact Matrix.det_isEmpty

/-- Conjugating a linear map by a linear equiv does not change its determinant. -/
@[simp]
/--
theorem `det_conj` / 定理 `det_conj`

English:
theorem det_conj
  given: {N : Type*} [AddCommGroup N] [Module A N] (f : M ->ₗ[A] M) (e : M ≃ₗ[A] N)
  proof: by
  classical
    by_cases H : exists s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f]; rw [← det_toMatrix (b.map e)]; rw [toMatrix_comp (b.map e) b (b.map e)]; rw [toMatrix_comp (b.map e) b b]; rw [← Matrix.mul_assoc]; rw [Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬exists t : Finset N, Nonempty (Basis t A N) := by
        contrapose H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dif_neg, not_false_eq_true]

中文:
定理 det_conj
  条件: {N : 类型} [加法交换群 N] [模 A N] (f : M ->ₗ[A] M) (e : M ≃ₗ[A] N)
  证明: by
  classical
    by_cases H : exists s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f]; rw [← det_toMatrix (b.map e)]; rw [toMatrix_comp (b.map e) b (b.map e)]; rw [toMatrix_comp (b.map e) b b]; rw [← Matrix.mul_assoc]; rw [Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬exists t : Finset N, Nonempty (Basis t A N) := by
        contrapose H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dif_neg, not_false_eq_true]

Depends on / 依赖: Finset, LinearEquiv, LinearEquiv.comp_coe, LinearEquiv.refl_toLinearMap, Matrix, Matrix.det_conj_of_mul_eq_one, Matrix.mul_assoc, Nonempty, b.map, classical, comp_coe, det_conj_of_mul_eq_one, det_toMatrix, e.self_trans_symm, e.symm_trans_self, mul_assoc, refl_toLinearMap, self_trans_symm, symm_trans_self, toMatrix_comp
-/
theorem det_conj {N : Type*} [AddCommGroup N] [Module A N] (f : M ->ₗ[A] M) (e : M ≃ₗ[A] N) :
    LinearMap.det ((e : M ->ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N ->ₗ[A] M)) = LinearMap.det f := by
  classical
    by_cases H : exists s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f]; rw [← det_toMatrix (b.map e)]; rw [toMatrix_comp (b.map e) b (b.map e)]; rw [toMatrix_comp (b.map e) b b]; rw [← Matrix.mul_assoc]; rw [Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬exists t : Finset N, Nonempty (Basis t A N) := by
        contrapose H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dif_neg, not_false_eq_true]

/--
theorem `isUnit_det` / 定理 `isUnit_det`

English:
theorem isUnit_det
  given: {A : Type*} [CommRing A] [Module A M] (f : M ->ₗ[A] M) (hf : IsUnit f)
  proof: IsUnit.map LinearMap.det hf

中文:
定理 isUnit_det
  条件: {A : 类型} [交换环 A] [模 A M] (f : M ->ₗ[A] M) (hf : 是单位 f)
  证明: IsUnit.map LinearMap.det hf

Depends on / 依赖: IsUnit, IsUnit.map, LinearMap, LinearMap.det
-/
theorem isUnit_det {A : Type*} [CommRing A] [Module A M] (f : M ->ₗ[A] M) (hf : IsUnit f) :
    IsUnit (LinearMap.det f) := IsUnit.map LinearMap.det hf

/--
lemma `isUnit_iff_isUnit_det` / 引理 `isUnit_iff_isUnit_det`

English:
lemma isUnit_iff_isUnit_det
  given: [Module.Finite R M] [Module.Free R M] (f : M ->ₗ[R] M)
  proof: by
  let b := Module.Free.chooseBasis R M
  rw [← isUnit_toMatrix_iff b]; rw [← det_toMatrix b]; rw [Matrix.isUnit_iff_isUnit_det (toMatrix b b f)]

中文:
引理 isUnit_iff_isUnit_det
  条件: [模.有限 R M] [模.自由 R M] (f : M ->ₗ[R] M)
  证明: by
  let b := Module.Free.chooseBasis R M
  rw [← isUnit_toMatrix_iff b]; rw [← det_toMatrix b]; rw [Matrix.isUnit_iff_isUnit_det (toMatrix b b f)]

Depends on / 依赖: Matrix, Matrix.isUnit_iff_isUnit_det, Module, Module.Free.chooseBasis, chooseBasis, det_toMatrix, isUnit_iff_isUnit_det, isUnit_toMatrix_iff, toMatrix
-/
lemma isUnit_iff_isUnit_det [Module.Finite R M] [Module.Free R M] (f : M ->ₗ[R] M) :
    IsUnit f ↔ IsUnit f.det := by
  let b := Module.Free.chooseBasis R M
  rw [← isUnit_toMatrix_iff b]; rw [← det_toMatrix b]; rw [Matrix.isUnit_iff_isUnit_det (toMatrix b b f)]

/--
theorem `free_of_det_ne_one` / 定理 `free_of_det_ne_one`

English:
theorem free_of_det_ne_one
  given: {f : M ->ₗ[R] M} (hf : f.det != 1)
  statement: Module.Free R M
  proof: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

中文:
定理 free_of_det_ne_one
  条件: {f : M ->ₗ[R] M} (hf : f.det != 1)
  结论: 模.自由 R M
  证明: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

Depends on / 依赖: Finset, LinearMap, LinearMap.coe_det, Module, Module.Free.of_basis, Nonempty, classical, coe_det, of_basis
-/
theorem free_of_det_ne_one {f : M ->ₗ[R] M} (hf : f.det != 1) : Module.Free R M := by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Free.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

/--
theorem `finite_of_det_ne_one` / 定理 `finite_of_det_ne_one`

English:
theorem finite_of_det_ne_one
  given: {f : M ->ₗ[R] M} (hf : f.det != 1)
  statement: Module.Finite R M
  proof: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Finite.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

中文:
定理 finite_of_det_ne_one
  条件: {f : M ->ₗ[R] M} (hf : f.det != 1)
  结论: 模.有限 R M
  证明: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Finite.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

Depends on / 依赖: Finite, Finset, LinearMap, LinearMap.coe_det, Module, Module.Finite.of_basis, Nonempty, classical, coe_det, of_basis
-/
theorem finite_of_det_ne_one {f : M ->ₗ[R] M} (hf : f.det != 1) : Module.Finite R M := by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact Module.Finite.of_basis hs
  · classical simp [LinearMap.coe_det, H] at hf

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bot_lt_ker_of_det_eq_zero` / 定理 `bot_lt_ker_of_det_eq_zero`

English:
theorem bot_lt_ker_of_det_eq_zero
  given: [IsDomain R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0)
  proof: by
  have : Module.Finite R M := by simp [finite_of_det_ne_one (f := f), hf]
  let b := Module.finBasis R M
  suffices exists x, f x = 0 ∧ x != 0 by simpa [bot_lt_iff_ne_bot, ker_eq_bot']
  obtain ⟨v, hv_ne_zero, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (det_toMatrix b f ▸ hf)
  refine ⟨b.equivFun.symm v, ?_, b.equivFun.symm.map_ne_zero_iff.mpr hv_ne_zero⟩
  rw [← b.equivFun.injective.eq_iff]
  simp_all [funext_iff, Matrix.mulVec, dotProduct, toMatrix_apply, mul_comm]

中文:
定理 bot_lt_ker_of_det_eq_zero
  条件: [是整环 R] [自由 R M] {f : M ->ₗ[R] M} (hf : f.det = 0)
  证明: by
  have : Module.Finite R M := by simp [finite_of_det_ne_one (f := f), hf]
  let b := Module.finBasis R M
  suffices exists x, f x = 0 ∧ x != 0 by simpa [bot_lt_iff_ne_bot, ker_eq_bot']
  obtain ⟨v, hv_ne_zero, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (det_toMatrix b f ▸ hf)
  refine ⟨b.equivFun.symm v, ?_, b.equivFun.symm.map_ne_zero_iff.mpr hv_ne_zero⟩
  rw [← b.equivFun.injective.eq_iff]
  simp_all [funext_iff, Matrix.mulVec, dotProduct, toMatrix_apply, mul_comm]

Depends on / 依赖: Finite, Matrix, Matrix.exists_mulVec_eq_zero_iff.mpr, Matrix.mulVec, Module, Module.Finite, Module.finBasis, b.equivFun.injective.eq_iff, b.equivFun.symm, b.equivFun.symm.map_ne_zero_iff.mpr, bot_lt_iff_ne_bot, det_toMatrix, dotProduct, eq_iff, equivFun, exists_mulVec_eq_zero_iff, finBasis, finite_of_det_ne_one, funext_iff, hv_ne_zero
-/
theorem bot_lt_ker_of_det_eq_zero [IsDomain R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0) :
    ⊥ < ker f := by
  have : Module.Finite R M := by simp [finite_of_det_ne_one (f := f), hf]
  let b := Module.finBasis R M
  suffices exists x, f x = 0 ∧ x != 0 by simpa [bot_lt_iff_ne_bot, ker_eq_bot']
  obtain ⟨v, hv_ne_zero, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (det_toMatrix b f ▸ hf)
  refine ⟨b.equivFun.symm v, ?_, b.equivFun.symm.map_ne_zero_iff.mpr hv_ne_zero⟩
  rw [← b.equivFun.injective.eq_iff]
  simp_all [funext_iff, Matrix.mulVec, dotProduct, toMatrix_apply, mul_comm]

/--
theorem `det_eq_zero_iff_ker_ne_bot` / 定理 `det_eq_zero_iff_ker_ne_bot`

English:
theorem det_eq_zero_iff_ker_ne_bot
  given: [IsDomain R] [Free R M] [Module.Finite R M] {f : M ->ₗ[R] M}
  proof: by
  constructor <;> intro h
  · exact bot_lt_iff_ne_bot.mp (bot_lt_ker_of_det_eq_zero h)
  · let b := Module.finBasis R M
    obtain ⟨v, ⟨_, hv_ne_zero⟩⟩ := (ker f).ne_bot_iff.mp h
    rw [← det_toMatrix b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun i => b.repr v i, by simpa, by simpa [toMatrix_mulVec_repr]⟩

中文:
定理 det_eq_zero_iff_ker_ne_bot
  条件: [是整环 R] [自由 R M] [模.有限 R M] {f : M ->ₗ[R] M}
  证明: by
  constructor <;> intro h
  · exact bot_lt_iff_ne_bot.mp (bot_lt_ker_of_det_eq_zero h)
  · let b := Module.finBasis R M
    obtain ⟨v, ⟨_, hv_ne_zero⟩⟩ := (ker f).ne_bot_iff.mp h
    rw [← det_toMatrix b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun i => b.repr v i, by simpa, by simpa [toMatrix_mulVec_repr]⟩

Depends on / 依赖: Matrix, Matrix.exists_mulVec_eq_zero_iff, Module, Module.finBasis, b.repr, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mp, bot_lt_ker_of_det_eq_zero, det_toMatrix, exists_mulVec_eq_zero_iff, finBasis, hv_ne_zero, ne_bot_iff, ne_bot_iff.mp, toMatrix_mulVec_repr
-/
theorem det_eq_zero_iff_ker_ne_bot [IsDomain R] [Free R M] [Module.Finite R M] {f : M ->ₗ[R] M} :
    f.det = 0 ↔ ker f != ⊥ := by
  constructor <;> intro h
  · exact bot_lt_iff_ne_bot.mp (bot_lt_ker_of_det_eq_zero h)
  · let b := Module.finBasis R M
    obtain ⟨v, ⟨_, hv_ne_zero⟩⟩ := (ker f).ne_bot_iff.mp h
    rw [← det_toMatrix b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun i => b.repr v i, by simpa, by simpa [toMatrix_mulVec_repr]⟩

/--
theorem `range_lt_top_of_det_eq_zero` / 定理 `range_lt_top_of_det_eq_zero`

English:
theorem range_lt_top_of_det_eq_zero
  statement: [IsDomain R] [Free R M] {f : M ->ₗ[R] M}
  proof: by
  rw [lt_top_iff_ne_top]
  intro h
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective h
  simpa [hf] using congr_arg LinearMap.det hg

中文:
定理 range_lt_top_of_det_eq_zero
  结论: [是整环 R] [自由 R M] {f : M ->ₗ[R] M}
  证明: by
  rw [lt_top_iff_ne_top]
  intro h
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective h
  simpa [hf] using congr_arg LinearMap.det hg

Depends on / 依赖: LinearMap, LinearMap.det, congr_arg, exists_rightInverse_of_surjective, f.exists_rightInverse_of_surjective, lt_top_iff_ne_top
-/
theorem range_lt_top_of_det_eq_zero [IsDomain R] [Free R M] {f : M ->ₗ[R] M}
    (hf : f.det = 0) : range f < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective h
  simpa [hf] using congr_arg LinearMap.det hg

/--
lemma `det_ring` / 引理 `det_ring`

English:
lemma det_ring
  given: (f : R ->ₗ[R] R)
  statement: f.det = f 1
  proof: by
  simp [← det_toMatrix (Basis.singleton Unit R)]

中文:
引理 det_ring
  条件: (f : R ->ₗ[R] R)
  结论: f.det = f 1
  证明: by
  simp [← det_toMatrix (Basis.singleton Unit R)]
-/
@[simp] lemma det_ring (f : R ->ₗ[R] R) : f.det = f 1 := by
  simp [← det_toMatrix (Basis.singleton Unit R)]

/--
lemma `det_mulLeft` / 引理 `det_mulLeft`

English:
lemma det_mulLeft
  given: (a : R)
  statement: (mulLeft R a).det = a
  proof: by simp

中文:
引理 det_mulLeft
  条件: (a : R)
  结论: (mulLeft R a).det = a
  证明: by simp
-/
lemma det_mulLeft (a : R) : (mulLeft R a).det = a := by simp
/--
lemma `det_mulRight` / 引理 `det_mulRight`

English:
lemma det_mulRight
  given: (a : R)
  statement: (mulRight R a).det = a
  proof: by simp

中文:
引理 det_mulRight
  条件: (a : R)
  结论: (mulRight R a).det = a
  证明: by simp
-/
lemma det_mulRight (a : R) : (mulRight R a).det = a := by simp

/--
theorem `det_prodMap` / 定理 `det_prodMap`

English:
theorem det_prodMap
  statement: [Module.Free R M] [Module.Free R M'] [Module.Finite R M] [Module.Finite R M']
  proof: by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R M'
  rw [← det_toMatrix (b.prod b')]; rw [← det_toMatrix b]; rw [← det_toMatrix b']; rw [toMatrix_prodMap]; rw [det_fromBlocks_zero₂₁]; rw [det_toMatrix]

omit [DecidableEq ι] in

中文:
定理 det_prodMap
  结论: [模.自由 R M] [模.自由 R M'] [模.有限 R M] [模.有限 R M']
  证明: by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R M'
  rw [← det_toMatrix (b.prod b')]; rw [← det_toMatrix b]; rw [← det_toMatrix b']; rw [toMatrix_prodMap]; rw [det_fromBlocks_zero₂₁]; rw [det_toMatrix]

omit [DecidableEq ι] in

Depends on / 依赖: Module, Module.Free.chooseBasis, b.prod, chooseBasis, det_toMatrix, toMatrix_prodMap
-/
theorem det_prodMap [Module.Free R M] [Module.Free R M'] [Module.Finite R M] [Module.Finite R M']
    (f : Module.End R M) (f' : Module.End R M') :
    (prodMap f f').det = f.det * f'.det := by
  let b := Module.Free.chooseBasis R M
  let b' := Module.Free.chooseBasis R M'
  rw [← det_toMatrix (b.prod b')]; rw [← det_toMatrix b]; rw [← det_toMatrix b']; rw [toMatrix_prodMap]; rw [det_fromBlocks_zero₂₁]; rw [det_toMatrix]

omit [DecidableEq ι] in
/--
theorem `det_pi` / 定理 `det_pi`

English:
theorem det_pi
  given: [Module.Free R M] [Module.Finite R M] (f : ι -> M ->ₗ[R] M)
  proof: by
  classical
  let b := Module.Free.chooseBasis R M
let B := (Pi.basis (fun _ : ι => b)).reindex
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix b]
  have : ((LinearMap.toMatrix B B) (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)) =
      Matrix.blockDiagonal (fun i => LinearMap.toMatrix b b (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    unfold B
    simp_rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.sigmaEquivProd_symm_apply, Prod.swap_prod_mk, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toMatrix_apply', LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this]; rw [Matrix.det_blockDiagonal]

中文:
定理 det_pi
  条件: [模.自由 R M] [模.有限 R M] (f : ι -> M ->ₗ[R] M)
  证明: by
  classical
  let b := Module.Free.chooseBasis R M
let B := (Pi.basis (fun _ : ι => b)).reindex
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix b]
  have : ((LinearMap.toMatrix B B) (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)) =
      Matrix.blockDiagonal (fun i => LinearMap.toMatrix b b (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    unfold B
    simp_rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.sigmaEquivProd_symm_apply, Prod.swap_prod_mk, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toMatrix_apply', LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this]; rw [Matrix.det_blockDiagonal]

Depends on / 依赖: Basis.coe_reindex, Equiv.prodComm, Equiv.sigmaEquivProd, Function, Function.comp_apply, LinearMap, LinearMap.det_toMatrix, LinearMap.pi, LinearMap.proj, LinearMap.toMatrix, LinearMap.toMatrix_apply, Matrix, Matrix.blockDiagonal, Matrix.blockDiagonal_apply, Module, Module.Free.chooseBasis, Pi.basis, blockDiagonal, blockDiagonal_apply, chooseBasis
-/
theorem det_pi [Module.Free R M] [Module.Finite R M] (f : ι -> M ->ₗ[R] M) :
    (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  classical
  let b := Module.Free.chooseBasis R M
let B := (Pi.basis (fun _ : ι => b)).reindex
    (Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _)
  simp_rw [← LinearMap.det_toMatrix B, ← LinearMap.det_toMatrix b]
  have : ((LinearMap.toMatrix B B) (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)) =
      Matrix.blockDiagonal (fun i => LinearMap.toMatrix b b (f i)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    unfold B
    simp_rw [LinearMap.toMatrix_apply', Matrix.blockDiagonal_apply, Basis.coe_reindex,
      Function.comp_apply, Basis.repr_reindex_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Equiv.sigmaEquivProd_symm_apply, Prod.swap_prod_mk, Pi.basis_apply,
      Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toMatrix_apply', LinearMap.coe_proj, Function.eval, Pi.single_apply]
    split_ifs with h
    · rw [h]
    · simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [this]; rw [Matrix.det_blockDiagonal]

end LinearMap

namespace Algebra

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S] [Free R S]

/--
lemma `det_lsmul` / 引理 `det_lsmul`

English:
lemma det_lsmul
  given: (x : R)
  statement: LinearMap.det (lsmul R R S x) = x ^ finrank R S
  proof: by
  rw [lsmul_eq_smul_one]; rw [LinearMap.det_smul]; rw [map_one]; rw [mul_one]

中文:
引理 det_lsmul
  条件: (x : R)
  结论: 线性映射.det (lsmul R R S x) = x ^ finrank R S
  证明: by
  rw [lsmul_eq_smul_one]; rw [LinearMap.det_smul]; rw [map_one]; rw [mul_one]

Depends on / 依赖: LinearMap, LinearMap.det_smul, det_smul, lsmul_eq_smul_one, map_one, mul_one
-/
lemma det_lsmul (x : R) : LinearMap.det (lsmul R R S x) = x ^ finrank R S := by
  rw [lsmul_eq_smul_one]; rw [LinearMap.det_smul]; rw [map_one]; rw [mul_one]

end Algebra

namespace LinearEquiv

/--
Definition of `det` / `det` 的定义

English:
definition det
  signature: : (M ≃ₗ[R] M) ->* Rˣ
  body: (Units.map (LinearMap.det : (M ->ₗ[R] M) ->* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]

中文:
定义 det
  签名: : (M ≃ₗ[R] M) ->* Rˣ
  定义体: (Units.map (LinearMap.det : (M ->ₗ[R] M) ->* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]
-/
protected def det : (M ≃ₗ[R] M) ->* Rˣ :=
  (Units.map (LinearMap.det : (M ->ₗ[R] M) ->* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]
/--
theorem `coe_det` / 定理 `coe_det`

English:
theorem coe_det
  given: (f : M ≃ₗ[R] M)
  statement: ↑(LinearEquiv.det f) = LinearMap.det (f : M ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 coe_det
  条件: (f : M ≃ₗ[R] M)
  结论: ↑(线性等价.det f) = 线性映射.det (f : M ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = LinearMap.det (f : M ->ₗ[R] M) :=
  rfl

@[simp]
/--
theorem `coe_inv_det` / 定理 `coe_inv_det`

English:
theorem coe_inv_det
  given: (f : M ≃ₗ[R] M)
  statement: ↑(LinearEquiv.det f)⁻¹ = LinearMap.det (f.symm : M ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 coe_inv_det
  条件: (f : M ≃ₗ[R] M)
  结论: ↑(线性等价.det f)⁻¹ = 线性映射.det (f.symm : M ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem coe_inv_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f)⁻¹ = LinearMap.det (f.symm : M ->ₗ[R] M) :=
  rfl

@[simp]
/--
theorem `det_refl` / 定理 `det_refl`

English:
theorem det_refl
  statement: LinearEquiv.det (LinearEquiv.refl R M) = 1
  proof: Units.ext LinearMap.det_id

@[simp]

中文:
定理 det_refl
  结论: 线性等价.det (线性等价.refl R M) = 1
  证明: Units.ext LinearMap.det_id

@[simp]

Depends on / 依赖: LinearMap, LinearMap.det_id, Units.ext, det_id
-/
theorem det_refl : LinearEquiv.det (LinearEquiv.refl R M) = 1 :=
Units.ext LinearMap.det_id

@[simp]
/--
theorem `det_trans` / 定理 `det_trans`

English:
theorem det_trans
  given: (f g : M ≃ₗ[R] M)
  proof: map_mul _ g f

@[simp]

中文:
定理 det_trans
  条件: (f g : M ≃ₗ[R] M)
  证明: map_mul _ g f

@[simp]

Depends on / 依赖: map_mul
-/
theorem det_trans (f g : M ≃ₗ[R] M) :
    LinearEquiv.det (f.trans g) = LinearEquiv.det g * LinearEquiv.det f :=
  map_mul _ g f

@[simp]
/--
theorem `det_symm` / 定理 `det_symm`

English:
theorem det_symm
  given: (f : M ≃ₗ[R] M)
  statement: LinearEquiv.det f.symm = LinearEquiv.det f⁻¹
  proof: map_inv _ f

中文:
定理 det_symm
  条件: (f : M ≃ₗ[R] M)
  结论: 线性等价.det f.symm = 线性等价.det f⁻¹
  证明: map_inv _ f

Depends on / 依赖: map_inv
-/
theorem det_symm (f : M ≃ₗ[R] M) : LinearEquiv.det f.symm = LinearEquiv.det f⁻¹ :=
  map_inv _ f

/-- Conjugating a linear equiv by a linear equiv does not change its determinant. -/
@[simp]
/--
theorem `det_conj` / 定理 `det_conj`

English:
theorem det_conj
  given: (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M')
  proof: by
  rw [← Units.val_inj]; rw [coe_det]; rw [coe_det]; rw [← comp_coe]; rw [← comp_coe]; rw [LinearMap.det_conj]

中文:
定理 det_conj
  条件: (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M')
  证明: by
  rw [← Units.val_inj]; rw [coe_det]; rw [coe_det]; rw [← comp_coe]; rw [← comp_coe]; rw [LinearMap.det_conj]

Depends on / 依赖: LinearMap, LinearMap.det_conj, Units.val_inj, coe_det, comp_coe, det_conj, val_inj
-/
theorem det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') :
    LinearEquiv.det ((e.symm.trans f).trans e) = LinearEquiv.det f := by
  rw [← Units.val_inj]; rw [coe_det]; rw [coe_det]; rw [← comp_coe]; rw [← comp_coe]; rw [LinearMap.det_conj]

attribute [irreducible] LinearEquiv.det

end LinearEquiv

/--
theorem `LinearMap.det_map` / 定理 `LinearMap.det_map`

English:
theorem LinearMap.det_map
  statement: {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  proof: have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ det_conj _ _

中文:
定理 线性映射.det_map
  结论: {K V W : 类型} [域 K] [加法交换群 V] [模 K V]
  证明: have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ det_conj _ _
-/
@[simp] theorem LinearMap.det_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {F : Type*} [EquivLike F (End K V) (End K W)]
    [AlgEquivClass F K _ _] (f : F) (x : End K V) : (f x).det = x.det :=
  have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ det_conj _ _

/--
theorem `Matrix.det_map` / 定理 `Matrix.det_map`

English:
theorem Matrix.det_map
  statement: {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  proof: by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.det_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'

中文:
定理 矩阵.det_map
  结论: {K m n : 类型} [域 K] [有限类型 m] [有限类型 n]
  证明: by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.det_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'
-/
@[simp] theorem Matrix.det_map {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : Type*} [EquivLike F (Matrix m m K) (Matrix n n K)]
    [AlgEquivClass F K _ _] (f : F) (x : Matrix m m K) : (f x).det = x.det := by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.det_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'

/--
theorem `Matrix.det_map'` / 定理 `Matrix.det_map'`

English:
theorem Matrix.det_map'
  statement: {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
  proof: by
  by_cases! Nonempty m
  · exact det_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp

中文:
定理 矩阵.det_map'
  结论: {K m F : 类型} [域 K] [有限类型 m] [DecidableEq m]
  证明: by
  by_cases! Nonempty m
  · exact det_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp
-/
@[simp] theorem Matrix.det_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).det = x.det := by
  by_cases! Nonempty m
  · exact det_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
/--
theorem `LinearEquiv.det_mul_det_symm` / 定理 `LinearEquiv.det_mul_det_symm`

English:
theorem LinearEquiv.det_mul_det_symm
  given: {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M)
  proof: by
  simp [← LinearMap.det_comp]

中文:
定理 线性等价.det_mul_det_symm
  条件: {A : 类型} [交换环 A] [模 A M] (f : M ≃ₗ[A] M)
  证明: by
  simp [← LinearMap.det_comp]

Depends on / 依赖: LinearMap, LinearMap.det_comp, det_comp
-/
theorem LinearEquiv.det_mul_det_symm {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f : M ->ₗ[A] M) * LinearMap.det (f.symm : M ->ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

/-- The determinants of a `LinearEquiv` and its inverse multiply to 1. -/
@[simp]
/--
theorem `LinearEquiv.det_symm_mul_det` / 定理 `LinearEquiv.det_symm_mul_det`

English:
theorem LinearEquiv.det_symm_mul_det
  given: {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M)
  proof: by
  simp [← LinearMap.det_comp]

中文:
定理 线性等价.det_symm_mul_det
  条件: {A : 类型} [交换环 A] [模 A M] (f : M ≃ₗ[A] M)
  证明: by
  simp [← LinearMap.det_comp]

Depends on / 依赖: LinearMap, LinearMap.det_comp, det_comp
-/
theorem LinearEquiv.det_symm_mul_det {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    LinearMap.det (f.symm : M ->ₗ[A] M) * LinearMap.det (f : M ->ₗ[A] M) = 1 := by
  simp [← LinearMap.det_comp]

-- Cannot be stated using `LinearMap.det` because `f` is not an endomorphism.
/--
theorem `LinearEquiv.isUnit_det` / 定理 `LinearEquiv.isUnit_det`

English:
theorem LinearEquiv.isUnit_det
  given: (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R M')
  proof: by
  apply isUnit_det_of_left_inverse
  simpa using (LinearMap.toMatrix_comp v v' v f.symm f).symm

中文:
定理 线性等价.isUnit_det
  条件: (f : M ≃ₗ[R] M') (v : 基 ι R M) (v' : 基 ι R M')
  证明: by
  apply isUnit_det_of_left_inverse
  simpa using (LinearMap.toMatrix_comp v v' v f.symm f).symm

Depends on / 依赖: LinearMap, LinearMap.toMatrix_comp, f.symm, isUnit_det_of_left_inverse, toMatrix_comp
-/
theorem LinearEquiv.isUnit_det (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R M') :
    IsUnit (LinearMap.toMatrix v v' f).det := by
  apply isUnit_det_of_left_inverse
  simpa using (LinearMap.toMatrix_comp v v' v f.symm f).symm

/--
theorem `LinearEquiv.isUnit_det'` / 定理 `LinearEquiv.isUnit_det'`

English:
theorem LinearEquiv.isUnit_det'
  given: {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M)
  proof: .of_mul_eq_one _ f.det_mul_det_symm

中文:
定理 线性等价.isUnit_det'
  条件: {A : 类型} [交换环 A] [模 A M] (f : M ≃ₗ[A] M)
  证明: .of_mul_eq_one _ f.det_mul_det_symm

Depends on / 依赖: det_mul_det_symm, f.det_mul_det_symm, of_mul_eq_one
-/
theorem LinearEquiv.isUnit_det' {A : Type*} [CommRing A] [Module A M] (f : M ≃ₗ[A] M) :
    IsUnit (LinearMap.det (f : M ->ₗ[A] M)) :=
  .of_mul_eq_one _ f.det_mul_det_symm

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `LinearEquiv.det_coe_symm` / 定理 `LinearEquiv.det_coe_symm`

English:
theorem LinearEquiv.det_coe_symm
  given: {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M)
  proof: by
  simp [field, IsUnit.ne_zero f.isUnit_det']

中文:
定理 线性等价.det_coe_symm
  条件: {𝕜 : 类型} [域 𝕜] [模 𝕜 M] (f : M ≃ₗ[𝕜] M)
  证明: by
  simp [field, IsUnit.ne_zero f.isUnit_det']

Depends on / 依赖: IsUnit, IsUnit.ne_zero, f.isUnit_det, isUnit_det, ne_zero
-/
theorem LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) :
    LinearMap.det (f.symm : M ->ₗ[𝕜] M) = (LinearMap.det (f : M ->ₗ[𝕜] M))⁻¹ := by
  simp [field, IsUnit.ne_zero f.isUnit_det']

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
/--
Definition of `LinearEquiv.ofIsUnitDet` / `LinearEquiv.ofIsUnitDet` 的定义

English:
definition LinearEquiv.ofIsUnitDet
  signature: {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
  body: f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc toLin v' v (toMatrix v v' f)⁻¹ (f x)
      _ = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x := by
        rw [toLin_mul v v' v]; rw [toLin_toMatrix]; rw [LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc f (toLin v' v (toMatrix v v' f)⁻¹ x)
      _ = toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x := by
        rw [toLin_mul v' v v']; rw [LinearMap.comp_apply]; rw [toLin_toMatrix v v']
      _ = x := by simp [h]

@[simp]

中文:
定义 线性等价.ofIsUnitDet
  签名: {f : M ->ₗ[R] M'} {v : 基 ι R M} {v' : 基 ι R M'}
  定义体: f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc toLin v' v (toMatrix v v' f)⁻¹ (f x)
      _ = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x := by
        rw [toLin_mul v v' v]; rw [toLin_toMatrix]; rw [LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc f (toLin v' v (toMatrix v v' f)⁻¹ x)
      _ = toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x := by
        rw [toLin_mul v' v v']; rw [LinearMap.comp_apply]; rw [toLin_toMatrix v v']
      _ = x := by simp [h]

@[simp]
-/
def LinearEquiv.ofIsUnitDet {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv x :=
    calc toLin v' v (toMatrix v v' f)⁻¹ (f x)
      _ = toLin v v ((toMatrix v v' f)⁻¹ * toMatrix v v' f) x := by
        rw [toLin_mul v v' v]; rw [toLin_toMatrix]; rw [LinearMap.comp_apply]
      _ = x := by simp [h]
  right_inv x :=
    calc f (toLin v' v (toMatrix v v' f)⁻¹ x)
      _ = toLin v' v' (toMatrix v v' f * (toMatrix v v' f)⁻¹) x := by
        rw [toLin_mul v' v v']; rw [LinearMap.comp_apply]; rw [toLin_toMatrix v v']
      _ = x := by simp [h]

@[simp]
/--
theorem `LinearEquiv.coe_ofIsUnitDet` / 定理 `LinearEquiv.coe_ofIsUnitDet`

English:
theorem LinearEquiv.coe_ofIsUnitDet
  statement: {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
  proof: by
  ext x
  rfl

中文:
定理 线性等价.coe_ofIsUnitDet
  结论: {f : M ->ₗ[R] M'} {v : 基 ι R M} {v' : 基 ι R M'}
  证明: by
  ext x
  rfl
-/
theorem LinearEquiv.coe_ofIsUnitDet {f : M ->ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) :
    (LinearEquiv.ofIsUnitDet h : M ->ₗ[R] M') = f := by
  ext x
  rfl

/--
Definition of `LinearMap.equivOfIsUnitDet` / `LinearMap.equivOfIsUnitDet` 的定义

English:
definition LinearMap.equivOfIsUnitDet
  body: by
  by_cases hR : Nontrivial R
  · let ⟨ι, b⟩ := (Module.Free.exists_basis R M).some
    have : Finite ι := Module.Finite.finite_basis b
    have : Fintype ι := Fintype.ofFinite ι
    have : DecidableEq ι := Classical.typeDecidableEq ι
    exact LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := f) (by rwa [det_toMatrix b])
  · exact 1

@[simp]

中文:
定义 线性映射.equivOfIsUnitDet
  定义体: by
  by_cases hR : Nontrivial R
  · let ⟨ι, b⟩ := (Module.Free.exists_basis R M).some
    have : Finite ι := Module.Finite.finite_basis b
    have : Fintype ι := Fintype.ofFinite ι
    have : DecidableEq ι := Classical.typeDecidableEq ι
    exact LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := f) (by rwa [det_toMatrix b])
  · exact 1

@[simp]

Depends on / 依赖: Classical, Classical.typeDecidableEq, DecidableEq, Finite, Fintype, Fintype.ofFinite, LinearEquiv, LinearEquiv.ofIsUnitDet, Module, Module.Finite.finite_basis, Module.Free.exists_basis, Nontrivial, det_toMatrix, exists_basis, finite_basis, ofFinite, ofIsUnitDet, typeDecidableEq
-/
noncomputable def LinearMap.equivOfIsUnitDet
    [Module.Free R M] [Module.Finite R M]
    {f : M ->ₗ[R] M} (h : IsUnit f.det) :
    M ≃ₗ[R] M := by
  by_cases hR : Nontrivial R
  · let ⟨ι, b⟩ := (Module.Free.exists_basis R M).some
    have : Finite ι := Module.Finite.finite_basis b
    have : Fintype ι := Fintype.ofFinite ι
    have : DecidableEq ι := Classical.typeDecidableEq ι
    exact LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := f) (by rwa [det_toMatrix b])
  · exact 1

@[simp]
/--
theorem `LinearMap.equivOfIsUnitDet_apply` / 定理 `LinearMap.equivOfIsUnitDet_apply`

English:
theorem LinearMap.equivOfIsUnitDet_apply
  proof: by
  nontriviality M
  simp [equivOfIsUnitDet, dif_pos (Module.nontrivial R M)]

@[simp]

中文:
定理 线性映射.equivOfIsUnitDet_apply
  证明: by
  nontriviality M
  simp [equivOfIsUnitDet, dif_pos (Module.nontrivial R M)]

@[simp]

Depends on / 依赖: Module, Module.nontrivial, dif_pos, equivOfIsUnitDet, nontrivial, nontriviality
-/
theorem LinearMap.equivOfIsUnitDet_apply
    [Module.Free R M] [Module.Finite R M]
    {f : M ->ₗ[R] M} (h : IsUnit f.det) (x : M) :
    (LinearMap.equivOfIsUnitDet h) x = f x := by
  nontriviality M
  simp [equivOfIsUnitDet, dif_pos (Module.nontrivial R M)]

@[simp]
/--
theorem `LinearMap.coe_equivOfIsUnitDet` / 定理 `LinearMap.coe_equivOfIsUnitDet`

English:
theorem LinearMap.coe_equivOfIsUnitDet
  proof: by
  ext
  apply LinearMap.equivOfIsUnitDet_apply

中文:
定理 线性映射.coe_equivOfIsUnitDet
  证明: by
  ext
  apply LinearMap.equivOfIsUnitDet_apply

Depends on / 依赖: LinearMap, LinearMap.equivOfIsUnitDet_apply, equivOfIsUnitDet_apply
-/
theorem LinearMap.coe_equivOfIsUnitDet
    [Module.Free R M] [Module.Finite R M]
    {f : M ->ₗ[R] M} (h : IsUnit f.det) :
    (LinearMap.equivOfIsUnitDet h : M ->ₗ[R] M) = f := by
  ext
  apply LinearMap.equivOfIsUnitDet_apply

/--
Definition of `LinearMap.equivOfDetNeZero` / `LinearMap.equivOfDetNeZero` 的定义

English:
abbreviation LinearMap.equivOfDetNeZero
  signature: {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]
  body: have : IsUnit (LinearMap.toMatrix (Module.finBasis 𝕜 M)
      (Module.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this

中文:
缩写 线性映射.equivOfDetNeZero
  签名: {𝕜 : 类型} [域 𝕜] {M : 类型} [加法交换群 M] [模 𝕜 M]
  定义体: have : IsUnit (LinearMap.toMatrix (Module.finBasis 𝕜 M)
      (Module.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this

Depends on / 依赖: IsUnit, LinearEquiv, LinearEquiv.ofIsUnitDet, LinearMap, LinearMap.det_toMatrix, LinearMap.toMatrix, Module, Module.finBasis, det_toMatrix, finBasis, isUnit_iff_ne_zero, ofIsUnitDet, toMatrix
-/
abbrev LinearMap.equivOfDetNeZero {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (f : M ->ₗ[𝕜] M) (hf : LinearMap.det f != 0) : M ≃ₗ[𝕜] M :=
  have : IsUnit (LinearMap.toMatrix (Module.finBasis 𝕜 M)
      (Module.finBasis 𝕜 M) f).det := by
    rw [LinearMap.det_toMatrix]
    exact isUnit_iff_ne_zero.2 hf
  LinearEquiv.ofIsUnitDet this

/--
theorem `LinearMap.associated_det_of_eq_comp` / 定理 `LinearMap.associated_det_of_eq_comp`

English:
theorem LinearMap.associated_det_of_eq_comp
  statement: (e : M ≃ₗ[R] M) (f f' : M ->ₗ[R] M)
  proof: by
  suffices Associated (LinearMap.det (f' ∘ₗ ↑e)) (LinearMap.det f') by
    convert! this using 2
    ext x
    exact h x
  rw [← mul_one (LinearMap.det f')]; rw [LinearMap.det_comp]
  exact Associated.mul_left _ (associated_one_iff_isUnit.mpr e.isUnit_det')

中文:
定理 线性映射.associated_det_of_eq_comp
  结论: (e : M ≃ₗ[R] M) (f f' : M ->ₗ[R] M)
  证明: by
  suffices Associated (LinearMap.det (f' ∘ₗ ↑e)) (LinearMap.det f') by
    convert! this using 2
    ext x
    exact h x
  rw [← mul_one (LinearMap.det f')]; rw [LinearMap.det_comp]
  exact Associated.mul_left _ (associated_one_iff_isUnit.mpr e.isUnit_det')

Depends on / 依赖: Associated, Associated.mul_left, LinearMap, LinearMap.det, LinearMap.det_comp, associated_one_iff_isUnit, associated_one_iff_isUnit.mpr, convert, det_comp, e.isUnit_det, isUnit_det, mul_left, mul_one
-/
theorem LinearMap.associated_det_of_eq_comp (e : M ≃ₗ[R] M) (f f' : M ->ₗ[R] M)
    (h : forall x, f x = f' (e x)) : Associated (LinearMap.det f) (LinearMap.det f') := by
  suffices Associated (LinearMap.det (f' ∘ₗ ↑e)) (LinearMap.det f') by
    convert! this using 2
    ext x
    exact h x
  rw [← mul_one (LinearMap.det f')]; rw [LinearMap.det_comp]
  exact Associated.mul_left _ (associated_one_iff_isUnit.mpr e.isUnit_det')

/--
theorem `LinearMap.associated_det_comp_equiv` / 定理 `LinearMap.associated_det_comp_equiv`

English:
theorem LinearMap.associated_det_comp_equiv
  statement: {N : Type*} [AddCommGroup N] [Module R N]
  proof: by
  refine LinearMap.associated_det_of_eq_comp (e.trans e'.symm) _ _ ?_
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

中文:
定理 线性映射.associated_det_comp_equiv
  结论: {N : 类型} [加法交换群 N] [模 R N]
  证明: by
  refine LinearMap.associated_det_of_eq_comp (e.trans e'.symm) _ _ ?_
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap, LinearMap.associated_det_of_eq_comp, LinearMap.comp_apply, apply_symm_apply, associated_det_of_eq_comp, coe_coe, comp_apply, e.trans, trans_apply
-/
theorem LinearMap.associated_det_comp_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (f : N ->ₗ[R] M) (e e' : M ≃ₗ[R] N) :
    Associated (LinearMap.det (f ∘ₗ ↑e)) (LinearMap.det (f ∘ₗ ↑e')) := by
  refine LinearMap.associated_det_of_eq_comp (e.trans e'.symm) _ _ ?_
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

namespace Module.Basis

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
nonrec def det : M [⋀^ι]->ₗ[R] R where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v => det (e.toMatrix v))
      (fun v i x y => by
        simp only [e.toMatrix_update, map_add, Finsupp.coe_add, det_updateCol_add])
      (fun u i c x => by
        simp only [e.toMatrix_update, smul_eq_mul, map_smul]
        apply det_updateCol_smul)
  map_eq_zero_of_eq' := by
    intro v i j h hij
    dsimp
    rw [← Function.update_eq_self i v]; rw [h]; rw [← det_transpose]; rw [e.toMatrix_update]; rw [← updateRow_transpose]; rw [← e.toMatrix_transpose_apply]
    apply det_zero_of_row_eq hij
    rw [updateRow_ne hij.symm]; rw [updateRow_self]

/--
theorem `det_apply` / 定理 `det_apply`

English:
theorem det_apply
  given: (v : ι -> M)
  statement: e.det v = Matrix.det (e.toMatrix v)
  proof: rfl

中文:
定理 det_apply
  条件: (v : ι -> M)
  结论: e.det v = 矩阵.det (e.toMatrix v)
  证明: rfl
-/
theorem det_apply (v : ι -> M) : e.det v = Matrix.det (e.toMatrix v) :=
  rfl

/--
theorem `det_self` / 定理 `det_self`

English:
theorem det_self
  statement: e.det e = 1
  proof: by simp [e.det_apply]

@[simp]

中文:
定理 det_self
  结论: e.det e = 1
  证明: by simp [e.det_apply]

@[simp]

Depends on / 依赖: det_apply, e.det_apply
-/
theorem det_self : e.det e = 1 := by simp [e.det_apply]

@[simp]
/--
theorem `det_isEmpty` / 定理 `det_isEmpty`

English:
theorem det_isEmpty
  given: [IsEmpty ι]
  statement: e.det = AlternatingMap.constOfIsEmpty R M ι 1
  proof: by
  ext v
  exact Matrix.det_isEmpty

中文:
定理 det_isEmpty
  条件: [是空 ι]
  结论: e.det = 交错映射.constOfIsEmpty R M ι 1
  证明: by
  ext v
  exact Matrix.det_isEmpty

Depends on / 依赖: Matrix, Matrix.det_isEmpty, det_isEmpty
-/
theorem det_isEmpty [IsEmpty ι] : e.det = AlternatingMap.constOfIsEmpty R M ι 1 := by
  ext v
  exact Matrix.det_isEmpty

/--
theorem `det_ne_zero` / 定理 `det_ne_zero`

English:
theorem det_ne_zero
  given: [Nontrivial R]
  statement: e.det != 0
  proof: fun h => by simpa [h] using e.det_self

中文:
定理 det_ne_zero
  条件: [非平凡 R]
  结论: e.det != 0
  证明: fun h => by simpa [h] using e.det_self

Depends on / 依赖: det_self, e.det_self
-/
theorem det_ne_zero [Nontrivial R] : e.det != 0 := fun h => by simpa [h] using e.det_self

/--
theorem `smul_det` / 定理 `smul_det`

English:
theorem smul_det
  statement: {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M]
  proof: by
  simp_rw [det_apply, toMatrix_smul_left]

中文:
定理 smul_det
  结论: {G} [群 G] [分配乘法作用 G M] [标量交换类 G R M]
  证明: by
  simp_rw [det_apply, toMatrix_smul_left]

Depends on / 依赖: det_apply, simp_rw, toMatrix_smul_left
-/
theorem smul_det {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    (g : G) (v : ι -> M) :
    (g • e).det v = e.det (g⁻¹ • v) := by
  simp_rw [det_apply, toMatrix_smul_left]

/--
theorem `is_basis_iff_det` / 定理 `is_basis_iff_det`

English:
theorem is_basis_iff_det
  given: {v : ι -> M}
  proof: by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan.ge
    rw [e.det_apply]
    convert! LinearEquiv.isUnit_det (LinearEquiv.refl R M) v' e using 2
    ext i j
    simp [v']
  · intro h
    rw [Basis.det_apply]; rw [Basis.toMatrix_eq_toMatrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def]; rw [Basis.map_apply]; rw [LinearEquiv.ofIsUnitDet_apply]; rw [e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩

中文:
定理 is_basis_iff_det
  条件: {v : ι -> M}
  证明: by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan.ge
    rw [e.det_apply]
    convert! LinearEquiv.isUnit_det (LinearEquiv.refl R M) v' e using 2
    ext i j
    simp [v']
  · intro h
    rw [Basis.det_apply]; rw [Basis.toMatrix_eq_toMatrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def]; rw [Basis.map_apply]; rw [LinearEquiv.ofIsUnitDet_apply]; rw [e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩

Depends on / 依赖: Basis.det_apply, Basis.map, Basis.map_apply, Basis.mk, Basis.toMatrix_eq_toMatrix_constr, LinearEquiv, LinearEquiv.isUnit_det, LinearEquiv.ofIsUnitDet, LinearEquiv.ofIsUnitDet_apply, LinearEquiv.refl, _def, constr_basis, convert, det_apply, e.constr_basis, e.det_apply, hspan.ge, isUnit_det, linearIndependent, map_apply
-/
theorem is_basis_iff_det {v : ι -> M} :
    LinearIndependent R v ∧ span R (Set.range v) = ⊤ ↔ IsUnit (e.det v) := by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan.ge
    rw [e.det_apply]
    convert! LinearEquiv.isUnit_det (LinearEquiv.refl R M) v' e using 2
    ext i j
    simp [v']
  · intro h
    rw [Basis.det_apply]; rw [Basis.toMatrix_eq_toMatrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def]; rw [Basis.map_apply]; rw [LinearEquiv.ofIsUnitDet_apply]; rw [e.constr_basis]
    rw [← this]
    exact ⟨v'.linearIndependent, v'.span_eq⟩

/--
theorem `isUnit_det` / 定理 `isUnit_det`

English:
theorem isUnit_det
  given: (e' : Basis ι R M)
  statement: IsUnit (e.det e')
  proof: (is_basis_iff_det e).mp ⟨e'.linearIndependent, e'.span_eq⟩

中文:
定理 isUnit_det
  条件: (e' : 基 ι R M)
  结论: 是单位 (e.det e')
  证明: (is_basis_iff_det e).mp ⟨e'.linearIndependent, e'.span_eq⟩

Depends on / 依赖: is_basis_iff_det, linearIndependent, span_eq
-/
theorem isUnit_det (e' : Basis ι R M) : IsUnit (e.det e') :=
  (is_basis_iff_det e).mp ⟨e'.linearIndependent, e'.span_eq⟩

end Module.Basis

/--
theorem `AlternatingMap.eq_smul_basis_det` / 定理 `AlternatingMap.eq_smul_basis_det`

English:
theorem AlternatingMap.eq_smul_basis_det
  given: (f : M [⋀^ι]->ₗ[R] R)
  statement: f = f e • e.det
  proof: by
  refine Basis.ext_alternating e fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self]

@[simp]

中文:
定理 交错映射.eq_smul_basis_det
  条件: (f : M [⋀^ι]->ₗ[R] R)
  结论: f = f e • e.det
  证明: by
  refine Basis.ext_alternating e fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self]

@[simp]

Depends on / 依赖: AlternatingMap, AlternatingMap.map_perm, Basis.det_self, Basis.ext_alternating, Equiv.Perm, Equiv.ofBijective, Finite, Finite.injective_iff_bijective, det_self, e.det, ext_alternating, injective_iff_bijective, map_perm, ofBijective
-/
theorem AlternatingMap.eq_smul_basis_det (f : M [⋀^ι]->ₗ[R] R) : f = f e • e.det := by
  refine Basis.ext_alternating e fun i h => ?_
  let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [AlternatingMap.map_perm, Basis.det_self]

@[simp]
/--
theorem `AlternatingMap.map_basis_eq_zero_iff` / 定理 `AlternatingMap.map_basis_eq_zero_iff`

English:
theorem AlternatingMap.map_basis_eq_zero_iff
  statement: {ι : Type*} [Finite ι] (e : Basis ι R M)
  proof: ⟨fun h => by
    cases nonempty_fintype ι
    let := Classical.decEq ι
    simpa [h] using f.eq_smul_basis_det e,
   fun h => h.symm ▸ AlternatingMap.zero_apply _⟩

中文:
定理 交错映射.map_basis_eq_zero_iff
  结论: {ι : 类型} [有限 ι] (e : 基 ι R M)
  证明: ⟨fun h => by
    cases nonempty_fintype ι
    let := Classical.decEq ι
    simpa [h] using f.eq_smul_basis_det e,
   fun h => h.symm ▸ AlternatingMap.zero_apply _⟩

Depends on / 依赖: AlternatingMap, AlternatingMap.zero_apply, Classical, Classical.decEq, eq_smul_basis_det, f.eq_smul_basis_det, h.symm, nonempty_fintype, zero_apply
-/
theorem AlternatingMap.map_basis_eq_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]->ₗ[R] R) : f e = 0 ↔ f = 0 :=
  ⟨fun h => by
    cases nonempty_fintype ι
    let := Classical.decEq ι
    simpa [h] using f.eq_smul_basis_det e,
   fun h => h.symm ▸ AlternatingMap.zero_apply _⟩

/--
theorem `AlternatingMap.map_basis_ne_zero_iff` / 定理 `AlternatingMap.map_basis_ne_zero_iff`

English:
theorem AlternatingMap.map_basis_ne_zero_iff
  statement: {ι : Type*} [Finite ι] (e : Basis ι R M)
  proof: not_congr f.map_basis_eq_zero_iff e

中文:
定理 交错映射.map_basis_ne_zero_iff
  结论: {ι : 类型} [有限 ι] (e : 基 ι R M)
  证明: not_congr f.map_basis_eq_zero_iff e

Depends on / 依赖: f.map_basis_eq_zero_iff, map_basis_eq_zero_iff, not_congr
-/
theorem AlternatingMap.map_basis_ne_zero_iff {ι : Type*} [Finite ι] (e : Basis ι R M)
    (f : M [⋀^ι]->ₗ[R] R) : f e != 0 ↔ f != 0 :=
not_congr f.map_basis_eq_zero_iff e

variable {A : Type*} [CommRing A] [Module A M]

namespace Module.Basis

@[simp]
/--
theorem `det_comp` / 定理 `det_comp`

English:
theorem det_comp
  given: (e : Basis ι A M) (f : M ->ₗ[A] M) (v : ι -> M)
  proof: by
  rw [det_apply]; rw [det_apply]; rw [← f.det_toMatrix e]; rw [← Matrix.det_mul]; rw [e.toMatrix_eq_toMatrix_constr (f ∘ v)]; rw [e.toMatrix_eq_toMatrix_constr v]; rw [← toMatrix_comp]; rw [e.constr_comp]

@[simp]

中文:
定理 det_comp
  条件: (e : 基 ι A M) (f : M ->ₗ[A] M) (v : ι -> M)
  证明: by
  rw [det_apply]; rw [det_apply]; rw [← f.det_toMatrix e]; rw [← Matrix.det_mul]; rw [e.toMatrix_eq_toMatrix_constr (f ∘ v)]; rw [e.toMatrix_eq_toMatrix_constr v]; rw [← toMatrix_comp]; rw [e.constr_comp]

@[simp]

Depends on / 依赖: Matrix, Matrix.det_mul, constr_comp, det_apply, det_mul, det_toMatrix, e.constr_comp, e.toMatrix_eq_toMatrix_constr, f.det_toMatrix, toMatrix_comp, toMatrix_eq_toMatrix_constr
-/
theorem det_comp (e : Basis ι A M) (f : M ->ₗ[A] M) (v : ι -> M) :
    e.det (f ∘ v) = (LinearMap.det f) * e.det v := by
  rw [det_apply]; rw [det_apply]; rw [← f.det_toMatrix e]; rw [← Matrix.det_mul]; rw [e.toMatrix_eq_toMatrix_constr (f ∘ v)]; rw [e.toMatrix_eq_toMatrix_constr v]; rw [← toMatrix_comp]; rw [e.constr_comp]

@[simp]
/--
theorem `det_comp_basis` / 定理 `det_comp_basis`

English:
theorem det_comp_basis
  given: [Module A M'] (b : Basis ι A M) (b' : Basis ι A M') (f : M ->ₗ[A] M')
  proof: by
  rw [det_apply]; rw [← LinearMap.det_toMatrix b']; rw [LinearMap.toMatrix_comp _ b]; rw [Matrix.det_mul]; rw [LinearMap.toMatrix_basis_equiv]; rw [Matrix.det_one]; rw [mul_one]
  congr 1; ext i j
  rw [toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Function.comp_apply]

@[simp]

中文:
定理 det_comp_basis
  条件: [模 A M'] (b : 基 ι A M) (b' : 基 ι A M') (f : M ->ₗ[A] M')
  证明: by
  rw [det_apply]; rw [← LinearMap.det_toMatrix b']; rw [LinearMap.toMatrix_comp _ b]; rw [Matrix.det_mul]; rw [LinearMap.toMatrix_basis_equiv]; rw [Matrix.det_one]; rw [mul_one]
  congr 1; ext i j
  rw [toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Function.comp_apply]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.det_toMatrix, LinearMap.toMatrix_apply, LinearMap.toMatrix_basis_equiv, LinearMap.toMatrix_comp, Matrix, Matrix.det_mul, Matrix.det_one, comp_apply, det_apply, det_mul, det_one, det_toMatrix, mul_one, toMatrix_apply, toMatrix_basis_equiv, toMatrix_comp
-/
theorem det_comp_basis [Module A M'] (b : Basis ι A M) (b' : Basis ι A M') (f : M ->ₗ[A] M') :
    b'.det (f ∘ b) = LinearMap.det (f ∘ₗ (b'.equiv b (Equiv.refl ι) : M' ->ₗ[A] M)) := by
  rw [det_apply]; rw [← LinearMap.det_toMatrix b']; rw [LinearMap.toMatrix_comp _ b]; rw [Matrix.det_mul]; rw [LinearMap.toMatrix_basis_equiv]; rw [Matrix.det_one]; rw [mul_one]
  congr 1; ext i j
  rw [toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Function.comp_apply]

@[simp]
/--
theorem `det_basis` / 定理 `det_basis`

English:
theorem det_basis
  given: (b : Basis ι A M) (b' : Basis ι A M)
  proof: (b.det_comp_basis b' (LinearMap.id)).symm

中文:
定理 det_basis
  条件: (b : 基 ι A M) (b' : 基 ι A M)
  证明: (b.det_comp_basis b' (LinearMap.id)).symm

Depends on / 依赖: LinearMap, LinearMap.id, b.det_comp_basis, det_comp_basis
-/
theorem det_basis (b : Basis ι A M) (b' : Basis ι A M) :
    LinearMap.det (b'.equiv b (Equiv.refl ι)).toLinearMap = b'.det b :=
  (b.det_comp_basis b' (LinearMap.id)).symm

/--
theorem `det_mul_det` / 定理 `det_mul_det`

English:
theorem det_mul_det
  given: (b b' b'' : Basis ι A M)
  proof: by
  have : b'' = (b'.equiv b'' (Equiv.refl ι)).toLinearMap ∘ b' := by
    ext; simp
  conv_rhs =>
    rw [this]; rw [Basis.det_comp]; rw [det_basis]; rw [mul_comm]

中文:
定理 det_mul_det
  条件: (b b' b'' : 基 ι A M)
  证明: by
  have : b'' = (b'.equiv b'' (Equiv.refl ι)).toLinearMap ∘ b' := by
    ext; simp
  conv_rhs =>
    rw [this]; rw [Basis.det_comp]; rw [det_basis]; rw [mul_comm]

Depends on / 依赖: Basis.det_comp, Equiv.refl, conv_rhs, det_basis, det_comp, mul_comm, toLinearMap
-/
theorem det_mul_det (b b' b'' : Basis ι A M) :
    b.det b' * b'.det b'' = b.det b'' := by
  have : b'' = (b'.equiv b'' (Equiv.refl ι)).toLinearMap ∘ b' := by
    ext; simp
  conv_rhs =>
    rw [this]; rw [Basis.det_comp]; rw [det_basis]; rw [mul_comm]

/--
theorem `det_inv` / 定理 `det_inv`

English:
theorem det_inv
  given: (b : Basis ι A M) (b' : Basis ι A M)
  proof: by
  rw [← Units.mul_eq_one_iff_inv_eq]; rw [IsUnit.unit_spec]; rw [← det_basis]; rw [← det_basis]
  exact LinearEquiv.det_mul_det_symm _

中文:
定理 det_inv
  条件: (b : 基 ι A M) (b' : 基 ι A M)
  证明: by
  rw [← Units.mul_eq_one_iff_inv_eq]; rw [IsUnit.unit_spec]; rw [← det_basis]; rw [← det_basis]
  exact LinearEquiv.det_mul_det_symm _

Depends on / 依赖: IsUnit, IsUnit.unit_spec, LinearEquiv, LinearEquiv.det_mul_det_symm, Units.mul_eq_one_iff_inv_eq, det_basis, det_mul_det_symm, mul_eq_one_iff_inv_eq, unit_spec
-/
theorem det_inv (b : Basis ι A M) (b' : Basis ι A M) :
    (b.isUnit_det b').unit⁻¹ = b'.det b := by
  rw [← Units.mul_eq_one_iff_inv_eq]; rw [IsUnit.unit_spec]; rw [← det_basis]; rw [← det_basis]
  exact LinearEquiv.det_mul_det_symm _

/--
theorem `det_reindex` / 定理 `det_reindex`

English:
theorem det_reindex
  statement: {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι' -> M)
  proof: by
  rw [det_apply]; rw [toMatrix_reindex']; rw [det_reindexAlgEquiv]; rw [det_apply]

中文:
定理 det_reindex
  结论: {ι' : 类型} [有限类型 ι'] [DecidableEq ι'] (b : 基 ι R M) (v : ι' -> M)
  证明: by
  rw [det_apply]; rw [toMatrix_reindex']; rw [det_reindexAlgEquiv]; rw [det_apply]

Depends on / 依赖: det_apply, det_reindexAlgEquiv, toMatrix_reindex
-/
theorem det_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι' -> M)
    (e : ι ≃ ι') : (b.reindex e).det v = b.det (v ∘ e) := by
  rw [det_apply]; rw [toMatrix_reindex']; rw [det_reindexAlgEquiv]; rw [det_apply]

/--
theorem `det_reindex'` / 定理 `det_reindex'`

English:
theorem det_reindex'
  statement: {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
  proof: AlternatingMap.ext fun _ => det_reindex _ _ _

中文:
定理 det_reindex'
  结论: {ι' : 类型} [有限类型 ι'] [DecidableEq ι'] (b : 基 ι R M)
  证明: AlternatingMap.ext fun _ => det_reindex _ _ _

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, det_reindex
-/
theorem det_reindex' {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (e : ι ≃ ι') : (b.reindex e).det = b.det.domDomCongr e :=
  AlternatingMap.ext fun _ => det_reindex _ _ _

/--
theorem `det_reindex_symm` / 定理 `det_reindex_symm`

English:
theorem det_reindex_symm
  statement: {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
  proof: by
  rw [det_reindex]; rw [Function.comp_assoc]; rw [e.self_comp_symm]; rw [Function.comp_id]

@[simp]

中文:
定理 det_reindex_symm
  结论: {ι' : 类型} [有限类型 ι'] [DecidableEq ι'] (b : 基 ι R M)
  证明: by
  rw [det_reindex]; rw [Function.comp_assoc]; rw [e.self_comp_symm]; rw [Function.comp_id]

@[simp]

Depends on / 依赖: Function, Function.comp_assoc, Function.comp_id, comp_assoc, comp_id, det_reindex, e.self_comp_symm, self_comp_symm
-/
theorem det_reindex_symm {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M)
    (v : ι -> M) (e : ι' ≃ ι) : (b.reindex e.symm).det (v ∘ e) = b.det v := by
  rw [det_reindex]; rw [Function.comp_assoc]; rw [e.self_comp_symm]; rw [Function.comp_id]

@[simp]
/--
theorem `det_map` / 定理 `det_map`

English:
theorem det_map
  given: (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι -> M')
  proof: by
  rw [det_apply]; rw [toMatrix_map]; rw [det_apply]

中文:
定理 det_map
  条件: (b : 基 ι R M) (f : M ≃ₗ[R] M') (v : ι -> M')
  证明: by
  rw [det_apply]; rw [toMatrix_map]; rw [det_apply]

Depends on / 依赖: det_apply, toMatrix_map
-/
theorem det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι -> M') :
    (b.map f).det v = b.det (f.symm ∘ v) := by
  rw [det_apply]; rw [toMatrix_map]; rw [det_apply]

/--
theorem `det_map'` / 定理 `det_map'`

English:
theorem det_map'
  given: (b : Basis ι R M) (f : M ≃ₗ[R] M')
  proof: AlternatingMap.ext b.det_map f

中文:
定理 det_map'
  条件: (b : 基 ι R M) (f : M ≃ₗ[R] M')
  证明: AlternatingMap.ext b.det_map f

Depends on / 依赖: AlternatingMap, AlternatingMap.ext, b.det_map, det_map
-/
theorem det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).det = b.det.compLinearMap f.symm :=
AlternatingMap.ext b.det_map f

end Module.Basis

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `Pi.basisFun_det` / 定理 `Pi.basisFun_det`

English:
theorem Pi.basisFun_det
  statement: (Pi.basisFun R ι).det = Matrix.detRowAlternating
  proof: by
  ext M
  rw [Basis.det_apply]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [det_transpose]; rw [det]

中文:
定理 依赖函数类型.basisFun_det
  结论: (依赖函数类型.basisFun R ι).det = 矩阵.detRowAlternating
  证明: by
  ext M
  rw [Basis.det_apply]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [det_transpose]; rw [det]

Depends on / 依赖: Basis.coePiBasisFun.toMatrix_eq_transpose, Basis.det_apply, coePiBasisFun, det_apply, det_transpose, toMatrix_eq_transpose
-/
theorem Pi.basisFun_det : (Pi.basisFun R ι).det = Matrix.detRowAlternating := by
  ext M
  rw [Basis.det_apply]; rw [Basis.coePiBasisFun.toMatrix_eq_transpose]; rw [det_transpose]; rw [det]

/--
theorem `Pi.basisFun_det_apply` / 定理 `Pi.basisFun_det_apply`

English:
theorem Pi.basisFun_det_apply
  given: (v : ι -> ι -> R)
  proof: by
  rw [Pi.basisFun_det]
  rfl

中文:
定理 依赖函数类型.basisFun_det_apply
  条件: (v : ι -> ι -> R)
  证明: by
  rw [Pi.basisFun_det]
  rfl

Depends on / 依赖: Pi.basisFun_det, basisFun_det
-/
theorem Pi.basisFun_det_apply (v : ι -> ι -> R) :
    (Pi.basisFun R ι).det v = (Matrix.of v).det := by
  rw [Pi.basisFun_det]
  rfl

namespace Module.Basis

/--
theorem `det_smul_mk_coord_eq_det_update` / 定理 `det_smul_mk_coord_eq_det_update`

English:
theorem det_smul_mk_coord_eq_det_update
  statement: {v : ι -> M} (hli : LinearIndependent R v)
  proof: by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [smul_eq_mul, coe_mk, LinearMap.smul_apply,
      MultilinearMap.toLinearMap_apply]
  · rw [mk_coord_apply_eq, mul_one, update_eq_self]
    congr
  · rw [mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact e.det.map_eq_zero_of_eq _ (by simp [hik]) hik

中文:
定理 det_smul_mk_coord_eq_det_update
  结论: {v : ι -> M} (hli : LinearIndependent R v)
  证明: by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [smul_eq_mul, coe_mk, LinearMap.smul_apply,
      MultilinearMap.toLinearMap_apply]
  · rw [mk_coord_apply_eq, mul_one, update_eq_self]
    congr
  · rw [mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact e.det.map_eq_zero_of_eq _ (by simp [hik]) hik

Depends on / 依赖: Basis.mk, LinearMap, LinearMap.smul_apply, MultilinearMap, MultilinearMap.toLinearMap_apply, coe_mk, e.det.map_eq_zero_of_eq, eq_comm, eq_or_ne, map_eq_zero_of_eq, mk_coord_apply_eq, mk_coord_apply_ne, mul_one, mul_zero, smul_apply, smul_eq_mul, toLinearMap_apply, update_eq_self
-/
theorem det_smul_mk_coord_eq_det_update {v : ι -> M} (hli : LinearIndependent R v)
    (hsp : ⊤ <= span R (range v)) (i : ι) :
    e.det v • (Basis.mk hli hsp).coord i = e.det.toMultilinearMap.toLinearMap v i := by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [smul_eq_mul, coe_mk, LinearMap.smul_apply,
      MultilinearMap.toLinearMap_apply]
  · rw [mk_coord_apply_eq, mul_one, update_eq_self]
    congr
  · rw [mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact e.det.map_eq_zero_of_eq _ (by simp [hik]) hik

/--
theorem `det_unitsSMul` / 定理 `det_unitsSMul`

English:
theorem det_unitsSMul
  given: (e : Basis ι R M) (w : ι -> Rˣ)
  proof: by
  ext f
  change
    (Matrix.det fun i j => (e.unitsSMul w).repr (f j) i) =
      (↑(∏ i, w i)⁻¹ : R) • Matrix.det fun i j => e.repr (f j) i
  simp only [e.repr_unitsSMul]
  convert! Matrix.det_mul_column (fun i => (↑(w i)⁻¹ : R)) fun i j => e.repr (f j) i
  simp [← Finset.prod_inv_distrib]

中文:
定理 det_unitsSMul
  条件: (e : 基 ι R M) (w : ι -> Rˣ)
  证明: by
  ext f
  change
    (Matrix.det fun i j => (e.unitsSMul w).repr (f j) i) =
      (↑(∏ i, w i)⁻¹ : R) • Matrix.det fun i j => e.repr (f j) i
  simp only [e.repr_unitsSMul]
  convert! Matrix.det_mul_column (fun i => (↑(w i)⁻¹ : R)) fun i j => e.repr (f j) i
  simp [← Finset.prod_inv_distrib]

Depends on / 依赖: Finset, Finset.prod_inv_distrib, Matrix, Matrix.det, Matrix.det_mul_column, convert, det_mul_column, e.repr, e.repr_unitsSMul, e.unitsSMul, prod_inv_distrib, repr_unitsSMul, unitsSMul
-/
theorem det_unitsSMul (e : Basis ι R M) (w : ι -> Rˣ) :
    (e.unitsSMul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det := by
  ext f
  change
    (Matrix.det fun i j => (e.unitsSMul w).repr (f j) i) =
      (↑(∏ i, w i)⁻¹ : R) • Matrix.det fun i j => e.repr (f j) i
  simp only [e.repr_unitsSMul]
  convert! Matrix.det_mul_column (fun i => (↑(w i)⁻¹ : R)) fun i j => e.repr (f j) i
  simp [← Finset.prod_inv_distrib]

/-- The determinant of a basis constructed by `unitsSMul` is the product of the given units. -/
@[simp]
/--
theorem `det_unitsSMul_self` / 定理 `det_unitsSMul_self`

English:
theorem det_unitsSMul_self
  given: (w : ι -> Rˣ)
  statement: e.det (e.unitsSMul w) = ∏ i, (w i : R)
  proof: by
  simp [det_apply]

中文:
定理 det_unitsSMul_self
  条件: (w : ι -> Rˣ)
  结论: e.det (e.unitsSMul w) = ∏ i, (w i : R)
  证明: by
  simp [det_apply]

Depends on / 依赖: det_apply
-/
theorem det_unitsSMul_self (w : ι -> Rˣ) : e.det (e.unitsSMul w) = ∏ i, (w i : R) := by
  simp [det_apply]

/-- The determinant of a basis constructed by `isUnitSMul` is the product of the given units. -/
@[simp]
/--
theorem `det_isUnitSMul` / 定理 `det_isUnitSMul`

English:
theorem det_isUnitSMul
  given: {w : ι -> R} (hw : forall i, IsUnit (w i))
  proof: e.det_unitsSMul_self _

中文:
定理 det_isUnitSMul
  条件: {w : ι -> R} (hw : 对任意 i, 是单位 (w i))
  证明: e.det_unitsSMul_self _

Depends on / 依赖: det_unitsSMul_self, e.det_unitsSMul_self
-/
theorem det_isUnitSMul {w : ι -> R} (hw : forall i, IsUnit (w i)) :
    e.det (e.isUnitSMul hw) = ∏ i, w i :=
  e.det_unitsSMul_self _

end Module.Basis

section Dual

/--
theorem `_root_.LinearMap.det_dualMap` / 定理 `_root_.LinearMap.det_dualMap`

English:
theorem _root_.LinearMap.det_dualMap
  proof: by
  set b := Module.Free.chooseBasis R M
  have : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  rw [← LinearMap.det_toMatrix b]; rw [← LinearMap.det_toMatrix b.dualBasis]
  simp [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]

中文:
定理 _root_.线性映射.det_dualMap
  证明: by
  set b := Module.Free.chooseBasis R M
  have : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  rw [← LinearMap.det_toMatrix b]; rw [← LinearMap.det_toMatrix b.dualBasis]
  simp [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]

Depends on / 依赖: ChooseBasisIndex, Fintype, LinearMap, LinearMap.det_toMatrix, LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Module, Module.Free.ChooseBasisIndex, Module.Free.ChooseBasisIndex.fintype, Module.Free.chooseBasis, b.dualBasis, chooseBasis, det_toMatrix, dualBasis, dualMap_def, fintype, toMatrix_transpose
-/
theorem _root_.LinearMap.det_dualMap
    [Module.Free R M] [Module.Finite R M] (f : M ->ₗ[R] M) :
    f.dualMap.det = f.det := by
  set b := Module.Free.chooseBasis R M
  have : Fintype (Module.Free.ChooseBasisIndex R M) :=
    Module.Free.ChooseBasisIndex.fintype R M
  rw [← LinearMap.det_toMatrix b]; rw [← LinearMap.det_toMatrix b.dualBasis]
  simp [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]

end Dual

section

variable {R V : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [Module.Finite R V]
    (W : Submodule R V) [Module.Free R W] [Module.Finite R W] [Module.Free R (V ⧸ W)]

open Module.Basis in
/--
theorem `LinearMap.det_eq_det_mul_det` / 定理 `LinearMap.det_eq_det_mul_det`

English:
theorem LinearMap.det_eq_det_mul_det
  given: (e : V ->ₗ[R] V) (he : W <= W.comap e)
  proof: by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l =>
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.det_toMatrix b]; rw [this]; rw [← LinearMap.det_toMatrix bW]; rw [← LinearMap.det_toMatrix bQ]; rw [Matrix.det_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker]; rw [Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l]; rw [W.mapQ_apply]
      simp

中文:
定理 线性映射.det_eq_det_mul_det
  条件: (e : V ->ₗ[R] V) (he : W <= W.comap e)
  证明: by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l =>
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.det_toMatrix b]; rw [this]; rw [← LinearMap.det_toMatrix bW]; rw [← LinearMap.det_toMatrix bQ]; rw [Matrix.det_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker]; rw [Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l]; rw [W.mapQ_apply]
      simp

Depends on / 依赖: ChooseBasisIndex, LinearMap, LinearMap.toMat, LinearMap.toMatrix, Matrix, Matrix.of, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Sum.inl, Sum.inr, W.mapQ, chooseBasis, e.restrict, restrict, sumQuot, toMatrix
-/
theorem LinearMap.det_eq_det_mul_det (e : V ->ₗ[R] V) (he : W <= W.comap e) :
    e.det = (e.restrict he).det * (W.mapQ W e he).det := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l =>
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.det_toMatrix b]; rw [this]; rw [← LinearMap.det_toMatrix bW]; rw [← LinearMap.det_toMatrix bQ]; rw [Matrix.det_fromBlocks_zero₂₁]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker]; rw [Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l]; rw [W.mapQ_apply]
      simp

end
