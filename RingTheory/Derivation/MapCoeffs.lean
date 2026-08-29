/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.RingTheory.Derivation.DifferentialRing
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.FieldTheory.Separable

/-!
# Coefficient-wise derivation on polynomials

In this file we define applying a derivation on the coefficients of a polynomial,
show this forms a derivation, and prove `apply_eval_eq`, which shows that for a derivation `D`,
`D(p(x)) = (D.mapCoeffs p)(x) + D(x) * p'(x)`. `apply_aeval_eq` and `apply_aeval_eq'`
are generalizations of that for algebras. We also have a special case for `DifferentialAlgebra`s.
-/

@[expose] public section

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapCoeffs` / `mapCoeffs` 的定义

English:
definition mapCoeffs
  signature: : Derivation R A[X] (PolynomialModule A M) where
  body: (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b => ext; simp [Polynomial.monomial_mul_monomial, add_comm]

@[simp]

中文:
定义 mapCoeffs
  签名: : 导子 R A[X] (多项式模 A M) where
  定义体: (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b => ext; simp [Polynomial.monomial_mul_monomial, add_comm]

@[simp]

Depends on / 依赖: PolynomialModule, PolynomialModule.map, d.toLinearMap, toLinearMap
-/
def mapCoeffs : Derivation R A[X] (PolynomialModule A M) where
  __ := (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b => ext; simp [Polynomial.monomial_mul_monomial, add_comm]

@[simp]
/--
lemma `mapCoeffs_apply` / 引理 `mapCoeffs_apply`

English:
lemma mapCoeffs_apply
  given: (p : A[X]) (i)
  statement: (d.mapCoeffs p).coeff i = d (coeff p i)
  proof: rfl

中文:
引理 mapCoeffs_apply
  条件: (p : A[X]) (i)
  结论: (d.mapCoeffs p).coeff i = d (coeff p i)
  证明: rfl
-/
lemma mapCoeffs_apply (p : A[X]) (i) : (d.mapCoeffs p).coeff i = d (coeff p i) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `mapCoeffs_monomial` / 引理 `mapCoeffs_monomial`

English:
lemma mapCoeffs_monomial
  given: (n : Nat) (x : A)
  proof: by
  ext; simp [coeff_monomial, apply_ite d, Finsupp.single_apply]

@[simp]

中文:
引理 mapCoeffs_monomial
  条件: (n : 自然数) (x : A)
  证明: by
  ext; simp [coeff_monomial, apply_ite d, Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, apply_ite, coeff_monomial, single_apply
-/
lemma mapCoeffs_monomial (n : Nat) (x : A) :
    d.mapCoeffs (monomial n x) = .single A n (d x) := by
  ext; simp [coeff_monomial, apply_ite d, Finsupp.single_apply]

@[simp]
/--
lemma `mapCoeffs_X` / 引理 `mapCoeffs_X`

English:
lemma mapCoeffs_X
  statement: d.mapCoeffs (X : A[X]) = 0
  proof: by
  simp [← monomial_one_one_eq_X, PolynomialModule.single]

@[simp]

中文:
引理 mapCoeffs_X
  结论: d.mapCoeffs (X : A[X]) = 0
  证明: by
  simp [← monomial_one_one_eq_X, PolynomialModule.single]

@[simp]

Depends on / 依赖: PolynomialModule, PolynomialModule.single, monomial_one_one_eq_X, single
-/
lemma mapCoeffs_X : d.mapCoeffs (X : A[X]) = 0 := by
  simp [← monomial_one_one_eq_X, PolynomialModule.single]

@[simp]
/--
lemma `mapCoeffs_C` / 引理 `mapCoeffs_C`

English:
lemma mapCoeffs_C
  given: (x : A)
  proof: by simp [← monomial_zero_left]

中文:
引理 mapCoeffs_C
  条件: (x : A)
  证明: by simp [← monomial_zero_left]

Depends on / 依赖: monomial_zero_left
-/
lemma mapCoeffs_C (x : A) :
    d.mapCoeffs (C x) = .single A 0 (d x) := by simp [← monomial_zero_left]

variable {B M' : Type*} [CommRing B] [Algebra R B] [Algebra A B]
    [AddCommGroup M'] [Module B M'] [Module R M'] [Module A M']

/--
theorem `apply_aeval_eq'` / 定理 `apply_aeval_eq'`

English:
theorem apply_aeval_eq'
  statement: (d' : Derivation R B M') (f : M ->ₗ[A] M')
  proof: by
  induction p using Polynomial.induction_on' with
  | add => simp_all only [map_add, add_smul]; abel
  | monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, mapCoeffs_monomial,
      PolynomialModule.map_single, PolynomialModule.eval_single, derivative_monomial, map_mul,
      _root_.map_natCast, h]
    rw [add_comm]; rw [← smul_smul]; rw [← smul_smul]; rw [Nat.cast_smul_eq_nsmul]

中文:
定理 apply_aeval_eq'
  结论: (d' : 导子 R B M') (f : M ->ₗ[A] M')
  证明: by
  induction p using Polynomial.induction_on' with
  | add => simp_all only [map_add, add_smul]; abel
  | monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, mapCoeffs_monomial,
      PolynomialModule.map_single, PolynomialModule.eval_single, derivative_monomial, map_mul,
      _root_.map_natCast, h]
    rw [add_comm]; rw [← smul_smul]; rw [← smul_smul]; rw [Nat.cast_smul_eq_nsmul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Polynomial, Polynomial.induction_on, PolynomialModule, PolynomialModule.eval_single, PolynomialModule.map_single, _root_, _root_.map_natCast, add_comm, add_smul, aeval_monomial, cast_smul_eq_nsmul, derivative_monomial, eval_single, induction_on, leibniz, leibniz_pow, mapCoeffs_monomial, map_add, map_mul
-/
theorem apply_aeval_eq' (d' : Derivation R B M') (f : M ->ₗ[A] M')
    (h : forall a, f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]) :
    d' (aeval x p) = PolynomialModule.eval x (PolynomialModule.map B f (d.mapCoeffs p)) +
      aeval x (derivative p) • d' x := by
  induction p using Polynomial.induction_on' with
  | add => simp_all only [map_add, add_smul]; abel
  | monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, mapCoeffs_monomial,
      PolynomialModule.map_single, PolynomialModule.eval_single, derivative_monomial, map_mul,
      _root_.map_natCast, h]
    rw [add_comm]; rw [← smul_smul]; rw [← smul_smul]; rw [Nat.cast_smul_eq_nsmul]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `apply_aeval_eq` / 定理 `apply_aeval_eq`

English:
theorem apply_aeval_eq
  statement: [IsScalarTower R A B] [IsScalarTower A B M'] (d : Derivation R B M')
  proof: apply_aeval_eq' (d.compAlgebraMap A) d LinearMap.id (fun _a => rfl) x p

中文:
定理 apply_aeval_eq
  结论: [标量塔 R A B] [标量塔 A B M'] (d : 导子 R B M')
  证明: apply_aeval_eq' (d.compAlgebraMap A) d LinearMap.id (fun _a => rfl) x p

Depends on / 依赖: LinearMap, LinearMap.id, apply_aeval_eq, compAlgebraMap, d.compAlgebraMap
-/
theorem apply_aeval_eq [IsScalarTower R A B] [IsScalarTower A B M'] (d : Derivation R B M')
    (x : B) (p : A[X]) :
    d (aeval x p) =
      (((d.compAlgebraMap A).mapCoeffs p).map B .id).eval x + aeval x (derivative p) • d x :=
  apply_aeval_eq' (d.compAlgebraMap A) d LinearMap.id (fun _a => rfl) x p

/--
theorem `apply_eval_eq` / 定理 `apply_eval_eq`

English:
theorem apply_eval_eq
  given: (x : A) (p : A[X])
  proof: by
  convert! apply_aeval_eq d x p
  ext
  rfl

中文:
定理 apply_eval_eq
  条件: (x : A) (p : A[X])
  证明: by
  convert! apply_aeval_eq d x p
  ext
  rfl

Depends on / 依赖: apply_aeval_eq, convert
-/
theorem apply_eval_eq (x : A) (p : A[X]) :
    d (eval x p) = PolynomialModule.eval x (d.mapCoeffs p) + eval x (derivative p) • d x := by
  convert! apply_aeval_eq d x p
  ext
  rfl

end Derivation

namespace Differential

variable {A : Type*} [CommRing A] [Differential A]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapCoeffs` / `mapCoeffs` 的定义

English:
definition mapCoeffs
  signature: : Derivation Int A[X] A[X]
  body: PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]

中文:
定义 mapCoeffs
  签名: : 导子 整数 A[X] A[X]
  定义体: PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]

Depends on / 依赖: Differential, Differential.deriv.mapCoeffs, PolynomialModule, PolynomialModule.equivPolynomialSelf.compDer, compDer, equivPolynomialSelf, mapCoeffs
-/
def mapCoeffs : Derivation Int A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]
/--
lemma `coeff_mapCoeffs` / 引理 `coeff_mapCoeffs`

English:
lemma coeff_mapCoeffs
  given: (p : A[X]) (i)
  proof: rfl

中文:
引理 coeff_mapCoeffs
  条件: (p : A[X]) (i)
  证明: rfl
-/
lemma coeff_mapCoeffs (p : A[X]) (i) :
    coeff (mapCoeffs p) i = (coeff p i)′ := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mapCoeffs_monomial` / 引理 `mapCoeffs_monomial`

English:
lemma mapCoeffs_monomial
  given: (n : Nat) (x : A)
  proof: by
  simp [mapCoeffs]

@[simp]

中文:
引理 mapCoeffs_monomial
  条件: (n : 自然数) (x : A)
  证明: by
  simp [mapCoeffs]

@[simp]

Depends on / 依赖: mapCoeffs
-/
lemma mapCoeffs_monomial (n : Nat) (x : A) :
    mapCoeffs (monomial n x) = monomial n x′ := by
  simp [mapCoeffs]

@[simp]
/--
lemma `mapCoeffs_X` / 引理 `mapCoeffs_X`

English:
lemma mapCoeffs_X
  proof: by simp [← monomial_one_one_eq_X]

@[simp]

中文:
引理 mapCoeffs_X
  证明: by simp [← monomial_one_one_eq_X]

@[simp]

Depends on / 依赖: monomial_one_one_eq_X
-/
lemma mapCoeffs_X :
    mapCoeffs (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

@[simp]
/--
lemma `mapCoeffs_C` / 引理 `mapCoeffs_C`

English:
lemma mapCoeffs_C
  given: (x : A)
  proof: by simp [← monomial_zero_left]

中文:
引理 mapCoeffs_C
  条件: (x : A)
  证明: by simp [← monomial_zero_left]

Depends on / 依赖: monomial_zero_left
-/
lemma mapCoeffs_C (x : A) :
    mapCoeffs (C x) = C x′ := by simp [← monomial_zero_left]

variable {R : Type*} [CommRing R] [Differential R] [Algebra A R] [DifferentialAlgebra A R]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `deriv_aeval_eq` / 定理 `deriv_aeval_eq`

English:
theorem deriv_aeval_eq
  given: (x : R) (p : A[X])
  proof: by
  convert! Derivation.apply_aeval_eq' Differential.deriv _ (Algebra.linearMap A R) ..
  · simp [mapCoeffs]
  · simp [deriv_algebraMap]

中文:
定理 deriv_aeval_eq
  条件: (x : R) (p : A[X])
  证明: by
  convert! Derivation.apply_aeval_eq' Differential.deriv _ (Algebra.linearMap A R) ..
  · simp [mapCoeffs]
  · simp [deriv_algebraMap]

Depends on / 依赖: Algebra, Algebra.linearMap, Derivation, Derivation.apply_aeval_eq, Differential, Differential.deriv, apply_aeval_eq, convert, deriv_algebraMap, linearMap, mapCoeffs
-/
theorem deriv_aeval_eq (x : R) (p : A[X]) :
    (aeval x p)′ = aeval x (mapCoeffs p) + aeval x (derivative p) * x′ := by
  convert! Derivation.apply_aeval_eq' Differential.deriv _ (Algebra.linearMap A R) ..
  · simp [mapCoeffs]
  · simp [deriv_algebraMap]

/--
Definition of `implicitDeriv` / `implicitDeriv` 的定义

English:
definition implicitDeriv
  signature: (v : A[X])
  body: mapCoeffs + v • derivative'.restrictScalars Int

@[simp]

中文:
定义 implicitDeriv
  签名: (v : A[X])
  定义体: mapCoeffs + v • derivative'.restrictScalars Int

@[simp]

Depends on / 依赖: derivative, mapCoeffs, restrictScalars
-/
def implicitDeriv (v : A[X]) :
    Derivation Int A[X] A[X] :=
  mapCoeffs + v • derivative'.restrictScalars Int

@[simp]
/--
lemma `implicitDeriv_C` / 引理 `implicitDeriv_C`

English:
lemma implicitDeriv_C
  given: (v : A[X]) (b : A)
  proof: by
  simp [implicitDeriv]

@[simp]

中文:
引理 implicitDeriv_C
  条件: (v : A[X]) (b : A)
  证明: by
  simp [implicitDeriv]

@[simp]

Depends on / 依赖: implicitDeriv
-/
lemma implicitDeriv_C (v : A[X]) (b : A) :
    implicitDeriv v (C b) = C b′ := by
  simp [implicitDeriv]

@[simp]
/--
lemma `implicitDeriv_X` / 引理 `implicitDeriv_X`

English:
lemma implicitDeriv_X
  given: (v : A[X])
  proof: by
  simp [implicitDeriv]

中文:
引理 implicitDeriv_X
  条件: (v : A[X])
  证明: by
  simp [implicitDeriv]

Depends on / 依赖: implicitDeriv
-/
lemma implicitDeriv_X (v : A[X]) :
    implicitDeriv v X = v := by
  simp [implicitDeriv]

/--
lemma `deriv_aeval_eq_implicitDeriv` / 引理 `deriv_aeval_eq_implicitDeriv`

English:
lemma deriv_aeval_eq_implicitDeriv
  given: (x : R) (v : A[X]) (h : x′ = aeval x v) (p : A[X])
  proof: by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

中文:
引理 deriv_aeval_eq_implicitDeriv
  条件: (x : R) (v : A[X]) (h : x′ = aeval x v) (p : A[X])
  证明: by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

Depends on / 依赖: deriv_aeval_eq, implicitDeriv, mul_comm
-/
lemma deriv_aeval_eq_implicitDeriv (x : R) (v : A[X]) (h : x′ = aeval x v) (p : A[X]) :
    (aeval x p)′ = aeval x (implicitDeriv v p) := by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

variable {R' : Type*} [CommRing R'] [Differential R'] [Algebra A R'] [DifferentialAlgebra A R']
variable [IsDomain R'] [Nontrivial R]

/--
lemma `algHom_deriv` / 引理 `algHom_deriv`

English:
lemma algHom_deriv
  given: (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R) (h : IsSeparable A x)
  proof: by
  let p := minpoly A x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · rw [Polynomial.aeval_algHom]
    simp only [AlgHom.coe_comp, Function.comp_apply, ne_eq, map_eq_zero_iff f hf]
    apply Separable.aeval_derivative_ne_zero h (minpoly.aeval A x)
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

omit [Nontrivial R] in

中文:
引理 algHom_deriv
  条件: (f : R ->ₐ[A] R') (hf : 函数.单射 f) (x : R) (h : 是可分 A x)
  证明: by
  let p := minpoly A x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · rw [Polynomial.aeval_algHom]
    simp only [AlgHom.coe_comp, Function.comp_apply, ne_eq, map_eq_zero_iff f hf]
    apply Separable.aeval_derivative_ne_zero h (minpoly.aeval A x)
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

omit [Nontrivial R] in

Depends on / 依赖: AlgHom, AlgHom.coe_comp, Function, Function.comp_apply, Polynomial, Polynomial.aeval_algHom, Separable, Separable.aeval_derivative_ne_zero, add_left_cancel, aeval_algHom, aeval_derivative_ne_zero, coe_comp, comp_apply, deriv_aeval_eq, derivative, mapCoeffs, map_eq_zero_iff, map_mul, minpoly, minpoly.aeval
-/
lemma algHom_deriv (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ := by
  let p := minpoly A x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · rw [Polynomial.aeval_algHom]
    simp only [AlgHom.coe_comp, Function.comp_apply, ne_eq, map_eq_zero_iff f hf]
    apply Separable.aeval_derivative_ne_zero h (minpoly.aeval A x)
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

omit [Nontrivial R] in
/--
lemma `algEquiv_deriv` / 引理 `algEquiv_deriv`

English:
lemma algEquiv_deriv
  given: (f : R ≃ₐ[A] R') (x : R) (h : IsSeparable A x)
  proof: haveI := f.nontrivial
  algHom_deriv f.toAlgHom f.injective x h

中文:
引理 algEquiv_deriv
  条件: (f : R ≃ₐ[A] R') (x : R) (h : 是可分 A x)
  证明: haveI := f.nontrivial
  algHom_deriv f.toAlgHom f.injective x h

Depends on / 依赖: algHom_deriv, f.injective, f.nontrivial, f.toAlgHom, injective, nontrivial, toAlgHom
-/
lemma algEquiv_deriv (f : R ≃ₐ[A] R') (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv f.toAlgHom f.injective x h

variable [Algebra.IsSeparable A R]

/--
lemma `algHom_deriv'` / 引理 `algHom_deriv'`

English:
lemma algHom_deriv'
  given: (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R)
  proof: algHom_deriv f hf x (Algebra.IsSeparable.isSeparable' x)

omit [Nontrivial R] in

中文:
引理 algHom_deriv'
  条件: (f : R ->ₐ[A] R') (hf : 函数.单射 f) (x : R)
  证明: algHom_deriv f hf x (Algebra.IsSeparable.isSeparable' x)

omit [Nontrivial R] in

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, algHom_deriv, isSeparable
-/
lemma algHom_deriv' (f : R ->ₐ[A] R') (hf : Function.Injective f) (x : R) :
    f (x′) = (f x)′ := algHom_deriv f hf x (Algebra.IsSeparable.isSeparable' x)

omit [Nontrivial R] in
/--
lemma `algEquiv_deriv'` / 引理 `algEquiv_deriv'`

English:
lemma algEquiv_deriv'
  given: (f : R ≃ₐ[A] R') (x : R)
  proof: haveI := f.nontrivial
  algHom_deriv' f.toAlgHom f.injective x

中文:
引理 algEquiv_deriv'
  条件: (f : R ≃ₐ[A] R') (x : R)
  证明: haveI := f.nontrivial
  algHom_deriv' f.toAlgHom f.injective x

Depends on / 依赖: algHom_deriv, f.injective, f.nontrivial, f.toAlgHom, injective, nontrivial, toAlgHom
-/
lemma algEquiv_deriv' (f : R ≃ₐ[A] R') (x : R) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv' f.toAlgHom f.injective x

end Differential
