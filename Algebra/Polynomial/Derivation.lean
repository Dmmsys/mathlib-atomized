/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard M. Hill
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Derivation.Basic
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

@[expose] public section

noncomputable section

namespace Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R]

set_option backward.isDefEq.respectTransparency false in
/-- `Polynomial.derivative` as a derivation. -/
@[simps]
/--
Definition of `derivative'` / `derivative'` 的定义

English:
definition derivative'
  signature: : Derivation R R[X] R[X] where
  body: derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

中文:
定义 derivative'
  签名: : Derivation R R[X] R[X] where
  定义体: derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

Depends on / 依赖: derivative
-/
def derivative' : Derivation R R[X] R[X] where
  toFun := derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

@[simp]
/--
theorem `derivation_C` / 定理 `derivation_C`

English:
theorem derivation_C
  given: (D : Derivation R R[X] A) (a : R)
  statement: D (C a) = 0
  proof: D.map_algebraMap a

@[simp]

中文:
定理 derivation_C
  条件: (D : Derivation R R[X] A) (a : R)
  结论: D (C a) = 0
  证明: D.map_algebraMap a

@[simp]

Depends on / 依赖: D.map_algebraMap, map_algebraMap
-/
theorem derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
/--
theorem `C_smul_derivation_apply` / 定理 `C_smul_derivation_apply`

English:
theorem C_smul_derivation_apply
  given: (D : Derivation R R[X] A) (a : R) (f : R[X])
  proof: by
  have : C a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

@[ext]

中文:
定理 C_smul_derivation_apply
  条件: (D : Derivation R R[X] A) (a : R) (f : R[X])
  证明: by
  have : C a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

@[ext]

Depends on / 依赖: C_mul, D.map_smul, map_smul
-/
theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

@[ext]
/--
theorem `derivation_ext` / 定理 `derivation_ext`

English:
theorem derivation_ext
  given: {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X)
  statement: D₁ = D₂
  proof: Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

中文:
定理 derivation_ext
  条件: {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X)
  结论: D₁ = D₂
  证明: Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

Depends on / 依赖: Algebra, Algebra.coe_top, Derivation, Derivation.eqOn_adjoin, Derivation.ext, Set.eqOn_singleton, Set.mem_univ, adjoin_X, coe_top, eqOn_adjoin, eqOn_singleton, mem_univ
-/
theorem derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂ :=
Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

variable [IsScalarTower R (Polynomial R) A]
variable (R)

/--
Definition of `mkDerivation` / `mkDerivation` 的定义

English:
definition mkDerivation
  signature: : A ->ₗ[R] Derivation R R[X] A where
  body: fun a => (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b => by ext; simp
  map_smul' := fun t a => by ext; simp

中文:
定义 mkDerivation
  签名: : A ->ₗ[R] Derivation R R[X] A where
  定义体: fun a => (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b => by ext; simp
  map_smul' := fun t a => by ext; simp

Depends on / 依赖: LinearMap, LinearMap.toSpanSingleton, compDer, derivative, toSpanSingleton
-/
def mkDerivation : A ->ₗ[R] Derivation R R[X] A where
  toFun := fun a => (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b => by ext; simp
  map_smul' := fun t a => by ext; simp

/--
lemma `mkDerivation_apply` / 引理 `mkDerivation_apply`

English:
lemma mkDerivation_apply
  given: (a : A) (f : R[X])
  proof: by
  rfl

@[simp]

中文:
引理 mkDerivation_apply
  条件: (a : A) (f : R[X])
  证明: by
  rfl

@[simp]
-/
lemma mkDerivation_apply (a : A) (f : R[X]) :
    mkDerivation R a f = derivative f • a := by
  rfl

@[simp]
/--
theorem `mkDerivation_X` / 定理 `mkDerivation_X`

English:
theorem mkDerivation_X
  given: (a : A)
  statement: mkDerivation R a X = a
  proof: by simp [mkDerivation_apply]

中文:
定理 mkDerivation_X
  条件: (a : A)
  结论: mkDerivation R a X = a
  证明: by simp [mkDerivation_apply]

Depends on / 依赖: mkDerivation_apply
-/
theorem mkDerivation_X (a : A) : mkDerivation R a X = a := by simp [mkDerivation_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mkDerivation_one_eq_derivative'` / 引理 `mkDerivation_one_eq_derivative'`

English:
lemma mkDerivation_one_eq_derivative'
  statement: mkDerivation R (1 : R[X]) = derivative'
  proof: by
  ext : 1
  simp [derivative']

中文:
引理 mkDerivation_one_eq_derivative'
  结论: mkDerivation R (1 : R[X]) = derivative'
  证明: by
  ext : 1
  simp [derivative']

Depends on / 依赖: derivative
-/
lemma mkDerivation_one_eq_derivative' : mkDerivation R (1 : R[X]) = derivative' := by
  ext : 1
  simp [derivative']

/--
lemma `mkDerivation_one_eq_derivative` / 引理 `mkDerivation_one_eq_derivative`

English:
lemma mkDerivation_one_eq_derivative
  given: (f : R[X])
  statement: mkDerivation R (1 : R[X]) f = derivative f
  proof: by
  rw [mkDerivation_one_eq_derivative']
  rfl

中文:
引理 mkDerivation_one_eq_derivative
  条件: (f : R[X])
  结论: mkDerivation R (1 : R[X]) f = derivative f
  证明: by
  rw [mkDerivation_one_eq_derivative']
  rfl

Depends on / 依赖: mkDerivation_one_eq_derivative
-/
lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  rw [mkDerivation_one_eq_derivative']
  rfl

/--
Definition of `mkDerivationEquiv` / `mkDerivationEquiv` 的定义

English:
definition mkDerivationEquiv
  signature: : A ≃ₗ[R] Derivation R R[X] A
  body: LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }

中文:
定义 mkDerivationEquiv
  签名: : A ≃ₗ[R] Derivation R R[X] A
  定义体: LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }

Depends on / 依赖: LinearEquiv, LinearEquiv.symm, derivation_ext, invFun, left_inv, map_add, map_smul, mkDerivation, mkDerivation_X, right_inv
-/
def mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A :=
LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }

/--
lemma `mkDerivationEquiv_apply` / 引理 `mkDerivationEquiv_apply`

English:
lemma mkDerivationEquiv_apply
  given: (a : A)
  proof: by
  rfl

中文:
引理 mkDerivationEquiv_apply
  条件: (a : A)
  证明: by
  rfl
-/
@[simp] lemma mkDerivationEquiv_apply (a : A) :
    mkDerivationEquiv R a = mkDerivation R a := by
  rfl

/--
lemma `mkDerivationEquiv_symm_apply` / 引理 `mkDerivationEquiv_symm_apply`

English:
lemma mkDerivationEquiv_symm_apply
  given: (D : Derivation R R[X] A)
  proof: rfl

中文:
引理 mkDerivationEquiv_symm_apply
  条件: (D : Derivation R R[X] A)
  证明: rfl
-/
@[simp] lemma mkDerivationEquiv_symm_apply (D : Derivation R R[X] A) :
    (mkDerivationEquiv R).symm D = D X := rfl

end CommSemiring
end Polynomial

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

open Polynomial Module

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
For a derivation `d : A → M` and an element `a : A`, `d.compAEval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `Module.AEval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
/-
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an algebra instance
within the definition.
-/
@[simps]
/--
Definition of `compAEval` / `compAEval` 的定义

English:
definition compAEval
  signature: : Derivation R R[X] AEval R M a where
  body: AEval.of R M a (d (aeval a f))
  map_add' := by simp
  map_smul' := by simp
  leibniz' := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

中文:
定义 compAEval
  签名: : Derivation R R[X] AEval R M a where
  定义体: AEval.of R M a (d (aeval a f))
  map_add' := by simp
  map_smul' := by simp
  leibniz' := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

Depends on / 依赖: AEval.of
-/
def compAEval : Derivation R R[X] AEval R M a where
  toFun f := AEval.of R M a (d (aeval a f))
  map_add' := by simp
  map_smul' := by simp
  leibniz' := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

/--
theorem `compAEval_eq` / 定理 `compAEval_eq`

English:
theorem compAEval_eq
  given: (d : Derivation R A M) (f : R[X])
  proof: by
  simpa using AEval.of_aeval_smul _ _ _

中文:
定理 compAEval_eq
  条件: (d : Derivation R A M) (f : R[X])
  证明: by
  simpa using AEval.of_aeval_smul _ _ _

Depends on / 依赖: AEval.of_aeval_smul, of_aeval_smul
-/
theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  simpa using AEval.of_aeval_smul _ _ _

/--
theorem `comp_aeval_eq` / 定理 `comp_aeval_eq`

English:
theorem comp_aeval_eq
  given: (d : Derivation R A M) (f : R[X])
  proof: calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

中文:
定理 comp_aeval_eq
  条件: (d : Derivation R A M) (f : R[X])
  证明: calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

Depends on / 依赖: AEval.of, compAEval, compAEval_apply, compAEval_eq, d.compAEval
-/
theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

end Derivation
