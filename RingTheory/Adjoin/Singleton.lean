/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Tower
/-!
# Adjoin one single element

This file contains basic results on `Algebra.adjoin`, specifically on adjoining singletons.

## Tags

adjoin, algebra, ringhom

-/

@[expose] public section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

namespace Algebra

open Polynomial

/--
Definition of `RingHom.adjoinAlgebraMap` / `RingHom.adjoinAlgebraMap` 的定义

English:
definition RingHom.adjoinAlgebraMap
  signature: :
  body: RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val A[b])) _
    (fun x => by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]

中文:
定义 环态射.adjoinAlgebraMap
  签名: :
  定义体: RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val A[b])) _
    (fun x => by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]
-/
def RingHom.adjoinAlgebraMap :
    A[b] ->+* A[(algebraMap B C) b] :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp
    (Subalgebra.val A[b])) _
    (fun x => by induction x using adjoin_singleton_induction with
      | f p => aesop (add norm [adjoin_singleton_eq_range_aeval, aeval_algebraMap_apply]))

@[simp]
/--
theorem `RingHom.adjoinAlgebraMap_apply` / 定理 `RingHom.adjoinAlgebraMap_apply`

English:
theorem RingHom.adjoinAlgebraMap_apply
  given: (x : A[b])
  proof: rfl

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_apply := RingHom.adjoinAlgebraMap_apply

中文:
定理 环态射.adjoinAlgebraMap_apply
  条件: (x : A[b])
  证明: rfl

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_apply := RingHom.adjoinAlgebraMap_apply

Depends on / 依赖: algebraMap
-/
theorem RingHom.adjoinAlgebraMap_apply (x : A[b]) :
    (RingHom.adjoinAlgebraMap b x (C := C) : C) = algebraMap B C x := rfl

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_apply := RingHom.adjoinAlgebraMap_apply

/--
theorem `RingHom.adjoinAlgebraMap_surjective` / 定理 `RingHom.adjoinAlgebraMap_surjective`

English:
theorem RingHom.adjoinAlgebraMap_surjective
  proof: by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_surjective := RingHom.adjoinAlgebraMap_surjective

中文:
定理 环态射.adjoinAlgebraMap_surjective
  证明: by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_surjective := RingHom.adjoinAlgebraMap_surjective

Depends on / 依赖: adjoin_eq_exists_aeval, aeval_algebraMap_apply, algebraMap
-/
theorem RingHom.adjoinAlgebraMap_surjective :
    Function.Surjective (RingHom.adjoinAlgebraMap (A := A) b (C := C)) := by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

@[deprecated (since := "2026-02-27")]
alias RingHom.adjoin_algebraMap_surjective := RingHom.adjoinAlgebraMap_surjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A[b] A[(algebraMap B C) b]
  body: RingHom.toAlgebra (RingHom.adjoinAlgebraMap b)

中文:
实例 :
  签名: 代数 A[b] A[(algebraMap B C) b]
  定义体: RingHom.toAlgebra (RingHom.adjoinAlgebraMap b)

Depends on / 依赖: RingHom, RingHom.adjoinAlgebraMap, RingHom.toAlgebra, adjoinAlgebraMap, toAlgebra
-/
instance : Algebra A[b] A[(algebraMap B C) b] :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap b)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower A[b] A[(algebraMap B C) b] C
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: 标量塔 A[b] A[(algebraMap B C) b] C
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower A[b] A[(algebraMap B C) b] C :=
  IsScalarTower.of_algebraMap_eq' rfl

/--
Definition of `RingHom.adjoinAlgebraMapEquiv` / `RingHom.adjoinAlgebraMapEquiv` 的定义

English:
definition RingHom.adjoinAlgebraMapEquiv
  signature: [FaithfulSMul B C]
  body: by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap b)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap b)).mpr (fun y => ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval b, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subt

中文:
定义 环态射.adjoinAlgebraMapEquiv
  签名: [忠实标量乘法 B C]
  定义体: by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap b)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap b)).mpr (fun y => ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval b, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subt

Depends on / 依赖: Algebra, Algebra.adjoin_singleton_induction, Function, Function.bijective_iff_existsUnique, Polynomial, Polynomial.aeval_algebraMap_apply, RingEquiv, RingEquiv.ofBijective, RingHom, RingHom.adjoinAlgebraMap, Subtype, Subtype.ext_iff, adjoinAlgebraMap, adjoin_singleton_induction, aeval_algebraMap_apply, bijective_iff_existsUnique, ext_iff, ofBijective, p.aeval
-/
noncomputable def RingHom.adjoinAlgebraMapEquiv [FaithfulSMul B C] :
    A[b] ≃+* A[(algebraMap B C) b] := by
  apply RingEquiv.ofBijective (RingHom.adjoinAlgebraMap b)
     ((Function.bijective_iff_existsUnique (adjoinAlgebraMap b)).mpr (fun y => ?_))
  induction y using Algebra.adjoin_singleton_induction with | f p =>
  use ⟨p.aeval b, by simp⟩
  aesop (add norm [Polynomial.aeval_algebraMap_apply, Subtype.ext_iff])

end Algebra
