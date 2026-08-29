/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree strictly less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
(semi)ring `R`, denoted `R[X]_n`.

## Main definitions/lemmas

* `degreeLT.basis R n`: a basis for `R[X]_n` the submodule of polynomials with degree `< n`,
  given by the monomials `X^i` for `i < n`.

* `degreeLT.basisProd R m n`: a basis for `R[X]_m × R[X]_n`, which is the sum of two instances of
  the basis given above.

* `degreeLT.addLinearEquiv R m n`: an isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n`,
  given by the fact that the bases are both indexed by `Fin (m + n)`. This is used for the Sylvester
  matrix, which is the matrix representing the Sylvester map between these two spaces, in a future
  file.

* `taylorLinear r n`: The linear automorphism induced by `taylor r` on `R[X]_n` which sends `X` to
  `X + r` and preserves degrees.

-/

@[expose] public section

open Module

namespace Polynomial

@[inherit_doc] scoped notation:9000 R "[X]_" n:arg => Polynomial.degreeLT R n

namespace degreeLT

variable {R : Type*} [Semiring R] {m n : Nat} (i : Fin n) (P : R[X]_n)

variable (R) in
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: (n : Nat)
  body: .ofEquivFun (degreeLTEquiv R n)

中文:
定义 basis
  签名: (n : 自然数)
  定义体: .ofEquivFun (degreeLTEquiv R n)

Depends on / 依赖: degreeLTEquiv, ofEquivFun
-/
noncomputable def basis (n : Nat) : Basis (Fin n) R R[X]_n :=
  .ofEquivFun (degreeLTEquiv R n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite R R[X]_n
  body: .of_basis basis ..

中文:
实例 :
  签名: 模.有限 R R[X]_n
  定义体: .of_basis basis ..

Depends on / 依赖: of_basis
-/
instance : Module.Finite R R[X]_n := .of_basis basis ..
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R R[X]_n
  body: .of_basis basis ..

中文:
实例 :
  签名: 模.自由 R R[X]_n
  定义体: .of_basis basis ..

Depends on / 依赖: of_basis
-/
instance : Module.Free R R[X]_n := .of_basis basis ..

/--
lemma `basis_repr` / 引理 `basis_repr`

English:
lemma basis_repr
  statement: (basis R n).repr P i = (P : R[X]).coeff i
  proof: rfl

中文:
引理 basis_repr
  结论: (basis R n).repr P i = (P : R[X]).coeff i
  证明: rfl
-/
@[simp] lemma basis_repr : (basis R n).repr P i = (P : R[X]).coeff i :=
  rfl

/--
lemma `basis_val` / 引理 `basis_val`

English:
lemma basis_val
  statement: (basis R n i : R[X]) = X ^ (i : Nat)
  proof: by
  change _ = ((⟨X ^ (i : Nat), mem_degreeLT.2 <| (degree_X_pow_le i).trans_lt <|
      Nat.cast_lt.2 i.is_lt⟩ : R[X]_n) : R[X])
  refine congr_arg _ (Basis.apply_eq_iff.2 <| Finsupp.ext fun j => ?_)
  simp only [basis_repr, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]

中文:
引理 basis_val
  结论: (basis R n i : R[X]) = X ^ (i : 自然数)
  证明: by
  change _ = ((⟨X ^ (i : Nat), mem_degreeLT.2 <| (degree_X_pow_le i).trans_lt <|
      Nat.cast_lt.2 i.is_lt⟩ : R[X]_n) : R[X])
  refine congr_arg _ (Basis.apply_eq_iff.2 <| Finsupp.ext fun j => ?_)
  simp only [basis_repr, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]
-/
@[simp] lemma basis_val : (basis R n i : R[X]) = X ^ (i : Nat) := by
  change _ = ((⟨X ^ (i : Nat), mem_degreeLT.2 <| (degree_X_pow_le i).trans_lt <|
      Nat.cast_lt.2 i.is_lt⟩ : R[X]_n) : R[X])
  refine congr_arg _ (Basis.apply_eq_iff.2 <| Finsupp.ext fun j => ?_)
  simp only [basis_repr, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]

variable (R m n) in
/--
Definition of `basisProd` / `basisProd` 的定义

English:
definition basisProd
  signature: : Basis (Fin (m + n)) R (R[X]_m × R[X]_n)
  body: ((basis R m).prod (basis R n)).reindex finSumFinEquiv

中文:
定义 basisProd
  签名: : 基 (有限集 (m + n)) R (R[X]_m × R[X]_n)
  定义体: ((basis R m).prod (basis R n)).reindex finSumFinEquiv

Depends on / 依赖: finSumFinEquiv, reindex
-/
noncomputable def basisProd : Basis (Fin (m + n)) R (R[X]_m × R[X]_n) :=
  ((basis R m).prod (basis R n)).reindex finSumFinEquiv

/--
lemma `basisProd_castAdd` / 引理 `basisProd_castAdd`

English:
lemma basisProd_castAdd
  given: (m n : Nat) (i : Fin m)
  proof: by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_castAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inl]; rw [LinearMap.coe_inl]; rw [Function.comp_apply]

中文:
引理 basisProd_castAdd
  条件: (m n : 自然数) (i : 有限集 m)
  证明: by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_castAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inl]; rw [LinearMap.coe_inl]; rw [Function.comp_apply]
-/
@[simp] lemma basisProd_castAdd (m n : Nat) (i : Fin m) :
    basisProd R m n (i.castAdd n) = (basis R m i, 0) := by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_castAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inl]; rw [LinearMap.coe_inl]; rw [Function.comp_apply]

/--
lemma `basisProd_natAdd` / 引理 `basisProd_natAdd`

English:
lemma basisProd_natAdd
  given: (m n : Nat) (i : Fin n)
  proof: by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_natAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inr]; rw [LinearMap.coe_inr]; rw [Function.comp_apply]

中文:
引理 basisProd_natAdd
  条件: (m n : 自然数) (i : 有限集 n)
  证明: by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_natAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inr]; rw [LinearMap.coe_inr]; rw [Function.comp_apply]
-/
@[simp] lemma basisProd_natAdd (m n : Nat) (i : Fin n) :
    basisProd R m n (i.natAdd m) = (0, basis R n i) := by
  rw [basisProd]; rw [Basis.reindex_apply]; rw [finSumFinEquiv_symm_apply_natAdd]; rw [Basis.prod_apply]; rw [Sum.elim_inr]; rw [LinearMap.coe_inr]; rw [Function.comp_apply]

variable (R m n) in
/--
Definition of `addLinearEquiv` / `addLinearEquiv` 的定义

English:
definition addLinearEquiv
  signature: :
  body: Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)

中文:
定义 addLinearEquiv
  签名: :
  定义体: Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)

Depends on / 依赖: Basis.equiv, Equiv.refl, basisProd
-/
noncomputable def addLinearEquiv :
    R[X]_(m + n) ≃ₗ[R] R[X]_m × R[X]_n :=
  Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)

/--
lemma `addLinearEquiv_castAdd` / 引理 `addLinearEquiv_castAdd`

English:
lemma addLinearEquiv_castAdd
  given: (i : Fin m)
  proof: by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_castAdd]

中文:
引理 addLinearEquiv_castAdd
  条件: (i : 有限集 m)
  证明: by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_castAdd]

Depends on / 依赖: Basis.equiv_apply, Equiv.refl_apply, addLinearEquiv, basisProd_castAdd, equiv_apply, refl_apply
-/
lemma addLinearEquiv_castAdd (i : Fin m) :
    addLinearEquiv R m n (basis R (m + n) (i.castAdd n)) = (basis R m i, 0) := by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_castAdd]

/--
lemma `addLinearEquiv_natAdd` / 引理 `addLinearEquiv_natAdd`

English:
lemma addLinearEquiv_natAdd
  given: (i : Fin n)
  proof: by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_natAdd]

中文:
引理 addLinearEquiv_natAdd
  条件: (i : 有限集 n)
  证明: by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_natAdd]

Depends on / 依赖: Basis.equiv_apply, Equiv.refl_apply, addLinearEquiv, basisProd_natAdd, equiv_apply, refl_apply
-/
lemma addLinearEquiv_natAdd (i : Fin n) :
    addLinearEquiv R m n (basis R (m + n) (i.natAdd m)) = (0, basis R n i) := by
  rw [addLinearEquiv]; rw [Basis.equiv_apply]; rw [Equiv.refl_apply]; rw [basisProd_natAdd]

/--
lemma `addLinearEquiv_symm_apply_inl_basis` / 引理 `addLinearEquiv_symm_apply_inl_basis`

English:
lemma addLinearEquiv_symm_apply_inl_basis
  given: (i : Fin m)
  proof: (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm

中文:
引理 addLinearEquiv_symm_apply_inl_basis
  条件: (i : 有限集 m)
  证明: (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, addLinearEquiv_castAdd, symm_apply_eq
-/
lemma addLinearEquiv_symm_apply_inl_basis (i : Fin m) :
    (addLinearEquiv R m n).symm (LinearMap.inl R _ _ (basis R m i)) =
      basis R (m + n) (i.castAdd n) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm

/--
lemma `addLinearEquiv_symm_apply_inr_basis` / 引理 `addLinearEquiv_symm_apply_inr_basis`

English:
lemma addLinearEquiv_symm_apply_inr_basis
  given: (j : Fin n)
  proof: (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm

中文:
引理 addLinearEquiv_symm_apply_inr_basis
  条件: (j : 有限集 n)
  证明: (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, addLinearEquiv_natAdd, symm_apply_eq
-/
lemma addLinearEquiv_symm_apply_inr_basis (j : Fin n) :
    (addLinearEquiv R m n).symm (LinearMap.inr R _ _ (basis R n j)) =
      basis R (m + n) (j.natAdd m) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm

/--
lemma `addLinearEquiv_symm_apply_inl` / 引理 `addLinearEquiv_symm_apply_inl`

English:
lemma addLinearEquiv_symm_apply_inl
  given: (P : R[X]_m)
  proof: by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis]

中文:
引理 addLinearEquiv_symm_apply_inl
  条件: (P : R[X]_m)
  证明: by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis]

Depends on / 依赖: LinearMap, LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis, coe_inl, sum_repr
-/
lemma addLinearEquiv_symm_apply_inl (P : R[X]_m) :
    ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ P) : R[X]) = (P : R[X]) := by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis]

/--
lemma `addLinearEquiv_symm_apply_inr` / 引理 `addLinearEquiv_symm_apply_inr`

English:
lemma addLinearEquiv_symm_apply_inr
  given: (Q : R[X]_n)
  proof: by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_inr_basis,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]

中文:
引理 addLinearEquiv_symm_apply_inr
  条件: (Q : R[X]_n)
  证明: by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_inr_basis,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]

Depends on / 依赖: Finset, Finset.sum_mul, LinearMap, LinearMap.coe_inr, addLinearEquiv_symm_apply_inr_basis, add_comm, coe_inr, mul_assoc, pow_add, smul_eq_C_mul, sum_mul, sum_repr
-/
lemma addLinearEquiv_symm_apply_inr (Q : R[X]_n) :
    ((addLinearEquiv R m n).symm (LinearMap.inr R _ _ Q) : R[X]) = (Q : R[X]) * X ^ (m : Nat) := by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_inr_basis,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]

/--
lemma `addLinearEquiv_symm_apply` / 引理 `addLinearEquiv_symm_apply`

English:
lemma addLinearEquiv_symm_apply
  given: (PQ)
  proof: calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) :
      R[X]) := by
    rw [LinearMap.inl_apply]; rw [LinearMap.inr_apply]; rw [Prod.add_def]; rw [add_zero]; rw [zero_add]
  _ = _ := by
    rw [map_add]; rw [Submodule.coe_add]; rw [addLinearEquiv_symm_ap

中文:
引理 addLinearEquiv_symm_apply
  条件: (PQ)
  证明: calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) :
      R[X]) := by
    rw [LinearMap.inl_apply]; rw [LinearMap.inr_apply]; rw [Prod.add_def]; rw [add_zero]; rw [zero_add]
  _ = _ := by
    rw [map_add]; rw [Submodule.coe_add]; rw [addLinearEquiv_symm_ap
-/
lemma addLinearEquiv_symm_apply (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + (PQ.2 : R[X]) * X ^ (m : Nat) := calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) :
      R[X]) := by
    rw [LinearMap.inl_apply]; rw [LinearMap.inr_apply]; rw [Prod.add_def]; rw [add_zero]; rw [zero_add]
  _ = _ := by
    rw [map_add]; rw [Submodule.coe_add]; rw [addLinearEquiv_symm_apply_inl]; rw [addLinearEquiv_symm_apply_inr]

/--
lemma `addLinearEquiv_symm_apply'` / 引理 `addLinearEquiv_symm_apply'`

English:
lemma addLinearEquiv_symm_apply'
  given: (PQ)
  proof: by
  rw [X_pow_mul]; rw [addLinearEquiv_symm_apply]

中文:
引理 addLinearEquiv_symm_apply'
  条件: (PQ)
  证明: by
  rw [X_pow_mul]; rw [addLinearEquiv_symm_apply]

Depends on / 依赖: X_pow_mul, addLinearEquiv_symm_apply
-/
lemma addLinearEquiv_symm_apply' (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + X ^ (m : Nat) * (PQ.2 : R[X]) := by
  rw [X_pow_mul]; rw [addLinearEquiv_symm_apply]

/--
lemma `addLinearEquiv_apply'` / 引理 `addLinearEquiv_apply'`

English:
lemma addLinearEquiv_apply'
  given: {R : Type*} [Ring R] (f)
  proof: by
  rw [and_comm]; rw [eq_comm]; rw [eq_comm (b := _ %ₘ _)]
  nontriviality R; refine div_modByMonic_unique _ _ (monic_X_pow _) ⟨?_, ?_⟩
  · rw [← addLinearEquiv_symm_apply', LinearEquiv.symm_apply_apply]
  · rw [degree_X_pow, ← mem_degreeLT]; exact Subtype.prop _

中文:
引理 addLinearEquiv_apply'
  条件: {R : 类型} [环 R] (f)
  证明: by
  rw [and_comm]; rw [eq_comm]; rw [eq_comm (b := _ %ₘ _)]
  nontriviality R; refine div_modByMonic_unique _ _ (monic_X_pow _) ⟨?_, ?_⟩
  · rw [← addLinearEquiv_symm_apply', LinearEquiv.symm_apply_apply]
  · rw [degree_X_pow, ← mem_degreeLT]; exact Subtype.prop _

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_apply, Subtype, Subtype.prop, addLinearEquiv_symm_apply, and_comm, degree_X_pow, div_modByMonic_unique, eq_comm, mem_degreeLT, monic_X_pow, nontriviality, symm_apply_apply
-/
lemma addLinearEquiv_apply' {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) ∧
      ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) := by
  rw [and_comm]; rw [eq_comm]; rw [eq_comm (b := _ %ₘ _)]
  nontriviality R; refine div_modByMonic_unique _ _ (monic_X_pow _) ⟨?_, ?_⟩
  · rw [← addLinearEquiv_symm_apply', LinearEquiv.symm_apply_apply]
  · rw [degree_X_pow, ← mem_degreeLT]; exact Subtype.prop _

/--
lemma `addLinearEquiv_apply_fst` / 引理 `addLinearEquiv_apply_fst`

English:
lemma addLinearEquiv_apply_fst
  given: {R : Type*} [Ring R] (f)
  proof: (addLinearEquiv_apply' f).1

中文:
引理 addLinearEquiv_apply_fst
  条件: {R : 类型} [环 R] (f)
  证明: (addLinearEquiv_apply' f).1

Depends on / 依赖: addLinearEquiv_apply
-/
lemma addLinearEquiv_apply_fst {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).1

/--
lemma `addLinearEquiv_apply_snd` / 引理 `addLinearEquiv_apply_snd`

English:
lemma addLinearEquiv_apply_snd
  given: {R : Type*} [Ring R] (f)
  proof: (addLinearEquiv_apply' f).2

中文:
引理 addLinearEquiv_apply_snd
  条件: {R : 类型} [环 R] (f)
  证明: (addLinearEquiv_apply' f).2

Depends on / 依赖: addLinearEquiv_apply
-/
lemma addLinearEquiv_apply_snd {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).2

/--
lemma `addLinearEquiv_apply` / 引理 `addLinearEquiv_apply`

English:
lemma addLinearEquiv_apply
  given: {R : Type*} [Ring R] (f)
  proof: Prod.ext (Subtype.ext <| addLinearEquiv_apply_fst f) (Subtype.ext <| addLinearEquiv_apply_snd f)

中文:
引理 addLinearEquiv_apply
  条件: {R : 类型} [环 R] (f)
  证明: Prod.ext (Subtype.ext <| addLinearEquiv_apply_fst f) (Subtype.ext <| addLinearEquiv_apply_snd f)

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, addLinearEquiv_apply_fst, addLinearEquiv_apply_snd
-/
lemma addLinearEquiv_apply {R : Type*} [Ring R] (f) :
    addLinearEquiv R m n f =
      (⟨f %ₘ (X ^ m), addLinearEquiv_apply_fst f ▸ Subtype.prop _⟩,
      ⟨f /ₘ (X ^ m), addLinearEquiv_apply_snd f ▸ Subtype.prop _⟩) :=
  Prod.ext (Subtype.ext <| addLinearEquiv_apply_fst f) (Subtype.ext <| addLinearEquiv_apply_snd f)

end degreeLT

section taylor

variable {R : Type*} [CommRing R] {r : R} {m n : Nat} {s : R} {f g : R[X]}

@[simp]
/--
lemma `taylor_mem_degreeLT` / 引理 `taylor_mem_degreeLT`

English:
lemma taylor_mem_degreeLT
  statement: taylor r f in R[X]_n ↔ f in R[X]_n
  proof: by simp [mem_degreeLT]

中文:
引理 taylor_mem_degreeLT
  结论: taylor r f in R[X]_n ↔ f in R[X]_n
  证明: by simp [mem_degreeLT]

Depends on / 依赖: comp_fract, continuous_id, continuous_id.prodMk, h.comp_fract, mem_degreeLT, prodMk
-/
lemma taylor_mem_degreeLT : taylor r f in R[X]_n ↔ f in R[X]_n := by simp [mem_degreeLT]

/--
lemma `comap_taylorEquiv_degreeLT` / 引理 `comap_taylorEquiv_degreeLT`

English:
lemma comap_taylorEquiv_degreeLT
  statement: (R[X]_n).comap (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n
  proof: by
  ext; simp [taylorEquiv]

中文:
引理 comap_taylorEquiv_degreeLT
  结论: (R[X]_n).comap (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n
  证明: by
  ext; simp [taylorEquiv]

Depends on / 依赖: taylorEquiv
-/
lemma comap_taylorEquiv_degreeLT : (R[X]_n).comap (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n := by
  ext; simp [taylorEquiv]

/--
lemma `map_taylorEquiv_degreeLT` / 引理 `map_taylorEquiv_degreeLT`

English:
lemma map_taylorEquiv_degreeLT
  statement: (R[X]_n).map (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n
  proof: by
  nth_rw 1 [← comap_taylorEquiv_degreeLT (r := r), Submodule.map_comap_eq_of_surjective]
  exact (taylorEquiv r).surjective

中文:
引理 map_taylorEquiv_degreeLT
  结论: (R[X]_n).map (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n
  证明: by
  nth_rw 1 [← comap_taylorEquiv_degreeLT (r := r), Submodule.map_comap_eq_of_surjective]
  exact (taylorEquiv r).surjective

Depends on / 依赖: LinearOrderedCommGroup, LinearOrderedCommGroup.toIsTopologicalGroup, Submodule, Submodule.map_comap_eq_of_surjective, comap_taylorEquiv_degreeLT, map_comap_eq_of_surjective, nth_rw, surjective, taylorEquiv, toIsTopologicalGroup
-/
lemma map_taylorEquiv_degreeLT : (R[X]_n).map (taylorEquiv r : R[X] ->ₗ[R] R[X]) = R[X]_n := by
  nth_rw 1 [← comap_taylorEquiv_degreeLT (r := r), Submodule.map_comap_eq_of_surjective]
  exact (taylorEquiv r).surjective

/-- The map `taylor r` induces an automorphism of the module `R[X]_n` of polynomials of
degree `< n`. -/
@[simps! apply_coe]
/--
Definition of `taylorLinearEquiv` / `taylorLinearEquiv` 的定义

English:
definition taylorLinearEquiv
  signature: (r : R) (n : Nat)
  body: (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT

中文:
定义 taylorLinearEquiv
  签名: (r : R) (n : 自然数)
  定义体: (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT

Depends on / 依赖: map_taylorEquiv_degreeLT, ofSubmodules, taylorEquiv
-/
noncomputable def taylorLinearEquiv (r : R) (n : Nat) : R[X]_n ≃ₗ[R] R[X]_n :=
  (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT

/--
lemma `taylorLinearEquiv_symm` / 引理 `taylorLinearEquiv_symm`

English:
lemma taylorLinearEquiv_symm
  given: (r : R)
  proof: LinearEquiv.ext fun _ => rfl

中文:
引理 taylorLinearEquiv_symm
  条件: (r : R)
  证明: LinearEquiv.ext fun _ => rfl
-/
@[simp] lemma taylorLinearEquiv_symm (r : R) :
    (taylorLinearEquiv r n).symm = taylorLinearEquiv (-r) n :=
LinearEquiv.ext fun _ => rfl

/--
theorem `det_taylorLinearEquiv_toLinearMap` / 定理 `det_taylorLinearEquiv_toLinearMap`

English:
theorem det_taylorLinearEquiv_toLinearMap
  proof: by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n)]; rw [Matrix.det_of_isUpperTriangular]; rw [Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply]; rw [degreeLT.basis_repr]; rw [← natDegree_X_pow (R := R) (i : Nat)]
    change (taylor r (degreeLT.basis R n i)).co

中文:
定理 det_taylorLinearEquiv_toLinearMap
  证明: by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n)]; rw [Matrix.det_of_isUpperTriangular]; rw [Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply]; rw [degreeLT.basis_repr]; rw [← natDegree_X_pow (R := R) (i : Nat)]
    change (taylor r (degreeLT.basis R n i)).co
-/
@[simp] theorem det_taylorLinearEquiv_toLinearMap :
    (taylorLinearEquiv r n).toLinearMap.det = 1 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n)]; rw [Matrix.det_of_isUpperTriangular]; rw [Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply]; rw [degreeLT.basis_repr]; rw [← natDegree_X_pow (R := R) (i : Nat)]
    change (taylor r (degreeLT.basis R n i)).coeff _ = 1
    rw [degreeLT.basis_val]; rw [coeff_taylor_natDegree]; rw [leadingCoeff_X_pow]
  · intro i j hji
    rw [LinearMap.toMatrix_apply]; rw [LinearEquiv.coe_coe]; rw [degreeLT.basis_repr]
    change (taylor r (degreeLT.basis R n j)).coeff i = 0
    rw [degreeLT.basis_val]; rw [coeff_eq_zero_of_degree_lt (by simpa [-taylor_X_pow]; rw [-taylor_pow])]

/--
theorem `det_taylorLinearEquiv` / 定理 `det_taylorLinearEquiv`

English:
theorem det_taylorLinearEquiv
  proof: Units.ext by rw [LinearEquiv.coe_det, det_taylorLinearEquiv_toLinearMap, Units.val_one]

中文:
定理 det_taylorLinearEquiv
  证明: Units.ext by rw [LinearEquiv.coe_det, det_taylorLinearEquiv_toLinearMap, Units.val_one]
-/
@[simp] theorem det_taylorLinearEquiv :
    (taylorLinearEquiv r n).det = 1 :=
Units.ext by rw [LinearEquiv.coe_det, det_taylorLinearEquiv_toLinearMap, Units.val_one]

end taylor

end Polynomial
