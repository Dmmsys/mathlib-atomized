/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor product and products of algebras

In this file we examine the behaviour of the tensor product with (finite) products. This
is a direct application of `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` to the algebra case.

-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {ι : Type*} (B : ι -> Type*) [forall i, Semiring (B i)] [forall i, Algebra R (B i)]

@[simp]
/--
lemma `piRightHom_one` / 引理 `piRightHom_one`

English:
lemma piRightHom_one
  statement: piRightHom R S A B 1 = 1
  proof: rfl

中文:
引理 piRightHom_one
  结论: piRightHom R S A B 1 = 1
  证明: rfl
-/
lemma piRightHom_one : piRightHom R S A B 1 = 1 := rfl

variable {R S A B} in
@[simp]
/--
lemma `piRightHom_mul` / 引理 `piRightHom_mul`

English:
lemma piRightHom_mul
  given: (x y : A otimes[R] forall i, B i)
  proof: by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

中文:
引理 piRightHom_mul
  条件: (x y : A otimes[R] 对任意 i, B i)
  证明: by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

Depends on / 依赖: add_mul, mul_add
-/
lemma piRightHom_mul (x y : A otimes[R] forall i, B i) :
    piRightHom R S A B (x * y) = piRightHom R S A B x * piRightHom R S A B y := by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

/--
Definition of `piRightHom` / `piRightHom` 的定义

English:
definition piRightHom
  signature: : A otimes[R] (forall i, B i) ->ₐ[S] forall i, A otimes[R] B i
  body: AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

中文:
定义 piRightHom
  签名: : A otimes[R] (对任意 i, B i) ->ₐ[S] 对任意 i, A otimes[R] B i
  定义体: AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, TensorProduct, _root_, _root_.TensorProduct.piRightHom, ofLinearMap, piRightHom
-/
def piRightHom : A otimes[R] (forall i, B i) ->ₐ[S] forall i, A otimes[R] B i :=
  AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

variable [Fintype ι] [DecidableEq ι]

/--
Definition of `piRight` / `piRight` 的定义

English:
definition piRight
  signature: : A otimes[R] (forall i, B i) ≃ₐ[S] forall i, A otimes[R] B i
  body: AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]

中文:
定义 piRight
  签名: : A otimes[R] (对任意 i, B i) ≃ₐ[S] 对任意 i, A otimes[R] B i
  定义体: AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofLinearEquiv, TensorProduct, _root_, _root_.TensorProduct.piRight, ofLinearEquiv, piRight
-/
def piRight : A otimes[R] (forall i, B i) ≃ₐ[S] forall i, A otimes[R] B i :=
  AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]
/--
lemma `piRight_tmul` / 引理 `piRight_tmul`

English:
lemma piRight_tmul
  given: (x : A) (f : forall i, B i)
  proof: rfl

中文:
引理 piRight_tmul
  条件: (x : A) (f : 对任意 i, B i)
  证明: rfl
-/
lemma piRight_tmul (x : A) (f : forall i, B i) :
    piRight R S A B (x otimesₜ f) = (fun j => x otimesₜ f j) := rfl

variable (ι) in
/--
Definition of `piScalarRight` / `piScalarRight` 的定义

English:
definition piScalarRight
  signature: : A otimes[R] (ι -> R) ≃ₐ[S] ι -> A
  body: (piRight R S A (fun _ : ι => R)).trans
    AlgEquiv.piCongrRight (fun _ => Algebra.TensorProduct.rid R S A)

中文:
定义 piScalarRight
  签名: : A otimes[R] (ι -> R) ≃ₐ[S] ι -> A
  定义体: (piRight R S A (fun _ : ι => R)).trans
    AlgEquiv.piCongrRight (fun _ => Algebra.TensorProduct.rid R S A)

Depends on / 依赖: AlgEquiv, AlgEquiv.piCongrRight, Algebra, Algebra.TensorProduct.rid, TensorProduct, piCongrRight, piRight
-/
def piScalarRight : A otimes[R] (ι -> R) ≃ₐ[S] ι -> A :=
(piRight R S A (fun _ : ι => R)).trans
    AlgEquiv.piCongrRight (fun _ => Algebra.TensorProduct.rid R S A)

/--
lemma `piScalarRight_tmul` / 引理 `piScalarRight_tmul`

English:
lemma piScalarRight_tmul
  given: (x : A) (y : ι -> R)
  proof: rfl

@[simp]

中文:
引理 piScalarRight_tmul
  条件: (x : A) (y : ι -> R)
  证明: rfl

@[simp]
-/
lemma piScalarRight_tmul (x : A) (y : ι -> R) :
    piScalarRight R S A ι (x otimesₜ y) = fun i => y i • x :=
  rfl

@[simp]
/--
lemma `piScalarRight_tmul_apply` / 引理 `piScalarRight_tmul_apply`

English:
lemma piScalarRight_tmul_apply
  given: (x : A) (y : ι -> R) (i : ι)
  proof: rfl

中文:
引理 piScalarRight_tmul_apply
  条件: (x : A) (y : ι -> R) (i : ι)
  证明: rfl
-/
lemma piScalarRight_tmul_apply (x : A) (y : ι -> R) (i : ι) :
    piScalarRight R S A ι (x otimesₜ y) i = y i • x :=
  rfl

section

variable (B C : Type*) [Semiring B] [Semiring C] [Algebra R B] [Algebra R C]

/-- Tensor product of rings commutes with binary products on the right. -/
nonrec def prodRight : A otimes[R] (B × C) ≃ₐ[S] A otimes[R] B × A otimes[R] C :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodRight R S A B C)
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ => by simp))

/--
lemma `prodRight_tmul` / 引理 `prodRight_tmul`

English:
lemma prodRight_tmul
  given: (a : A) (x : B × C)
  statement: prodRight R S A B C (a otimesₜ x) = (a otimesₜ x.1, a otimesₜ x.2)
  proof: rfl

@[simp]

中文:
引理 prodRight_tmul
  条件: (a : A) (x : B × C)
  结论: prodRight R S A B C (a otimesₜ x) = (a otimesₜ x.1, a otimesₜ x.2)
  证明: rfl

@[simp]
-/
lemma prodRight_tmul (a : A) (x : B × C) : prodRight R S A B C (a otimesₜ x) = (a otimesₜ x.1, a otimesₜ x.2) :=
  rfl

@[simp]
/--
lemma `prodRight_tmul_fst` / 引理 `prodRight_tmul_fst`

English:
lemma prodRight_tmul_fst
  given: (a : A) (x : B × C)
  statement: (prodRight R S A B C (a otimesₜ x)).fst = a otimesₜ x.1
  proof: rfl

@[simp]

中文:
引理 prodRight_tmul_fst
  条件: (a : A) (x : B × C)
  结论: (prodRight R S A B C (a otimesₜ x)).fst = a otimesₜ x.1
  证明: rfl

@[simp]
-/
lemma prodRight_tmul_fst (a : A) (x : B × C) : (prodRight R S A B C (a otimesₜ x)).fst = a otimesₜ x.1 :=
  rfl

@[simp]
/--
lemma `prodRight_tmul_snd` / 引理 `prodRight_tmul_snd`

English:
lemma prodRight_tmul_snd
  given: (a : A) (x : B × C)
  statement: (prodRight R S A B C (a otimesₜ x)).snd = a otimesₜ x.2
  proof: rfl

@[simp]

中文:
引理 prodRight_tmul_snd
  条件: (a : A) (x : B × C)
  结论: (prodRight R S A B C (a otimesₜ x)).snd = a otimesₜ x.2
  证明: rfl

@[simp]
-/
lemma prodRight_tmul_snd (a : A) (x : B × C) : (prodRight R S A B C (a otimesₜ x)).snd = a otimesₜ x.2 :=
  rfl

@[simp]
/--
lemma `prodRight_symm_tmul` / 引理 `prodRight_symm_tmul`

English:
lemma prodRight_symm_tmul
  given: (a : A) (b : B) (c : C)
  proof: by
  apply (prodRight R S A B C).injective
  simp [prodRight_tmul]

中文:
引理 prodRight_symm_tmul
  条件: (a : A) (b : B) (c : C)
  证明: by
  apply (prodRight R S A B C).injective
  simp [prodRight_tmul]

Depends on / 依赖: injective, prodRight, prodRight_tmul
-/
lemma prodRight_symm_tmul (a : A) (b : B) (c : C) :
    (prodRight R S A B C).symm (a otimesₜ b, a otimesₜ c) = a otimesₜ (b, c) := by
  apply (prodRight R S A B C).injective
  simp [prodRight_tmul]

end

end Algebra.TensorProduct

/--
theorem `TensorProduct.piScalarRight_symm_algebraMap` / 定理 `TensorProduct.piScalarRight_symm_algebraMap`

English:
theorem TensorProduct.piScalarRight_symm_algebraMap
  proof: by
  simp [Algebra.algebraMap_eq_smul_one, Pi.smul_def', LinearEquiv.symm_apply_eq,
    piScalarRight_apply, piScalarRightHom_tmul]

中文:
定理 张量积.piScalarRight_symm_algebraMap
  证明: by
  simp [Algebra.algebraMap_eq_smul_one, Pi.smul_def', LinearEquiv.symm_apply_eq,
    piScalarRight_apply, piScalarRightHom_tmul]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, LinearEquiv, LinearEquiv.symm_apply_eq, Pi.smul_def, algebraMap_eq_smul_one, piScalarRightHom_tmul, piScalarRight_apply, smul_def, symm_apply_eq
-/
theorem TensorProduct.piScalarRight_symm_algebraMap
    (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    {N : Type*} [Semiring N] [Algebra R N] [Module S N] [IsScalarTower R S N]
    (x : ι -> R) :
    (TensorProduct.piScalarRight R S N ι).symm (algebraMap _ _ x) = 1 otimesₜ[R] x := by
  simp [Algebra.algebraMap_eq_smul_one, Pi.smul_def', LinearEquiv.symm_apply_eq,
    piScalarRight_apply, piScalarRightHom_tmul]
