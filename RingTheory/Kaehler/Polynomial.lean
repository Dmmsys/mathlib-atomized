/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# The Kähler differential module of polynomial algebras
-/

@[expose] public section

open Algebra Module
open scoped TensorProduct

universe u v

variable (R : Type u) [CommRing R]

suppress_compilation

section MvPolynomial

/--
Definition of `KaehlerDifferential.mvPolynomialEquiv` / `KaehlerDifferential.mvPolynomialEquiv` 的定义

English:
definition KaehlerDifferential.mvPolynomialEquiv
  signature: (σ : Type*)
  body: (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x => D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.co

中文:
定义 KaehlerDifferential.mvPolynomialEquiv
  签名: (σ : 类型)
  定义体: (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x => D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.co

Depends on / 依赖: Finsupp, Finsupp.single, MvPolynomial, MvPolynomial.mkDerivation, liftKaehlerDifferential, mkDerivation, single
-/
def KaehlerDifferential.mvPolynomialEquiv (σ : Type*) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ ->₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x => D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | add => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | single a b => simp [-map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero]; rw [map_zero]; rw [map_zero]
    | add => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | single a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]

/--
Definition of `KaehlerDifferential.mvPolynomialBasis` / `KaehlerDifferential.mvPolynomialBasis` 的定义

English:
definition KaehlerDifferential.mvPolynomialBasis
  signature: (σ)
  body: ⟨mvPolynomialEquiv R σ⟩

中文:
定义 KaehlerDifferential.mvPolynomialBasis
  签名: (σ)
  定义体: ⟨mvPolynomialEquiv R σ⟩

Depends on / 依赖: mvPolynomialEquiv
-/
def KaehlerDifferential.mvPolynomialBasis (σ) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv R σ⟩

/--
lemma `KaehlerDifferential.mvPolynomialBasis_repr_comp_D` / 引理 `KaehlerDifferential.mvPolynomialBasis_repr_comp_D`

English:
lemma KaehlerDifferential.mvPolynomialBasis_repr_comp_D
  given: (σ)
  proof: Derivation.liftKaehlerDifferential_comp _

中文:
引理 KaehlerDifferential.mvPolynomialBasis_repr_comp_D
  条件: (σ)
  证明: Derivation.liftKaehlerDifferential_comp _

Depends on / 依赖: Derivation, Derivation.liftKaehlerDifferential_comp, liftKaehlerDifferential_comp
-/
lemma KaehlerDifferential.mvPolynomialBasis_repr_comp_D (σ) :
    (mvPolynomialBasis R σ).repr.toLinearMap.compDer (D _ _) =
      MvPolynomial.mkDerivation _ (Finsupp.single · 1) :=
  Derivation.liftKaehlerDifferential_comp _

/--
lemma `KaehlerDifferential.mvPolynomialBasis_repr_D` / 引理 `KaehlerDifferential.mvPolynomialBasis_repr_D`

English:
lemma KaehlerDifferential.mvPolynomialBasis_repr_D
  given: (σ) (x)
  proof: Derivation.congr_fun (mvPolynomialBasis_repr_comp_D R σ) x

@[simp]

中文:
引理 KaehlerDifferential.mvPolynomialBasis_repr_D
  条件: (σ) (x)
  证明: Derivation.congr_fun (mvPolynomialBasis_repr_comp_D R σ) x

@[simp]

Depends on / 依赖: Derivation, Derivation.congr_fun, congr_fun, mvPolynomialBasis_repr_comp_D
-/
lemma KaehlerDifferential.mvPolynomialBasis_repr_D (σ) (x) :
    (mvPolynomialBasis R σ).repr (D _ _ x) =
      MvPolynomial.mkDerivation R (Finsupp.single · (1 : MvPolynomial σ R)) x :=
  Derivation.congr_fun (mvPolynomialBasis_repr_comp_D R σ) x

@[simp]
/--
lemma `KaehlerDifferential.mvPolynomialBasis_repr_D_X` / 引理 `KaehlerDifferential.mvPolynomialBasis_repr_D_X`

English:
lemma KaehlerDifferential.mvPolynomialBasis_repr_D_X
  given: (σ) (i)
  proof: by
  simp [mvPolynomialBasis_repr_D]

@[simp]

中文:
引理 KaehlerDifferential.mvPolynomialBasis_repr_D_X
  条件: (σ) (i)
  证明: by
  simp [mvPolynomialBasis_repr_D]

@[simp]

Depends on / 依赖: mvPolynomialBasis_repr_D
-/
lemma KaehlerDifferential.mvPolynomialBasis_repr_D_X (σ) (i) :
    (mvPolynomialBasis R σ).repr (D _ _ (.X i)) = Finsupp.single i 1 := by
  simp [mvPolynomialBasis_repr_D]

@[simp]
/--
lemma `KaehlerDifferential.mvPolynomialBasis_repr_apply` / 引理 `KaehlerDifferential.mvPolynomialBasis_repr_apply`

English:
lemma KaehlerDifferential.mvPolynomialBasis_repr_apply
  given: (σ) (x) (i)
  proof: by
  classical
  suffices ((Finsupp.lapply i).comp
    (mvPolynomialBasis R σ).repr.toLinearMap).compDer (D _ _) = MvPolynomial.pderiv i by
    rw [← this]; rfl
  apply MvPolynomial.derivation_ext
  simp [Finsupp.single_apply, Pi.single_apply]

中文:
引理 KaehlerDifferential.mvPolynomialBasis_repr_apply
  条件: (σ) (x) (i)
  证明: by
  classical
  suffices ((Finsupp.lapply i).comp
    (mvPolynomialBasis R σ).repr.toLinearMap).compDer (D _ _) = MvPolynomial.pderiv i by
    rw [← this]; rfl
  apply MvPolynomial.derivation_ext
  simp [Finsupp.single_apply, Pi.single_apply]

Depends on / 依赖: Finsupp, Finsupp.lapply, Finsupp.single_apply, MvPolynomial, MvPolynomial.derivation_ext, MvPolynomial.pderiv, Pi.single_apply, classical, compDer, derivation_ext, lapply, mvPolynomialBasis, pderiv, repr.toLinearMap, single_apply, toLinearMap
-/
lemma KaehlerDifferential.mvPolynomialBasis_repr_apply (σ) (x) (i) :
    (mvPolynomialBasis R σ).repr (D _ _ x) i = MvPolynomial.pderiv i x := by
  classical
  suffices ((Finsupp.lapply i).comp
    (mvPolynomialBasis R σ).repr.toLinearMap).compDer (D _ _) = MvPolynomial.pderiv i by
    rw [← this]; rfl
  apply MvPolynomial.derivation_ext
  simp [Finsupp.single_apply, Pi.single_apply]

/--
lemma `KaehlerDifferential.mvPolynomialBasis_repr_symm_single` / 引理 `KaehlerDifferential.mvPolynomialBasis_repr_symm_single`

English:
lemma KaehlerDifferential.mvPolynomialBasis_repr_symm_single
  given: (σ) (i) (x)
  proof: by
  apply (mvPolynomialBasis R σ).repr.injective; simp [LinearEquiv.map_smul, -map_smul]

@[simp]

中文:
引理 KaehlerDifferential.mvPolynomialBasis_repr_symm_single
  条件: (σ) (i) (x)
  证明: by
  apply (mvPolynomialBasis R σ).repr.injective; simp [LinearEquiv.map_smul, -map_smul]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.map_smul, injective, map_smul, mvPolynomialBasis, repr.injective
-/
lemma KaehlerDifferential.mvPolynomialBasis_repr_symm_single (σ) (i) (x) :
    (mvPolynomialBasis R σ).repr.symm (Finsupp.single i x) = x • D R (MvPolynomial σ R) (.X i) := by
  apply (mvPolynomialBasis R σ).repr.injective; simp [LinearEquiv.map_smul, -map_smul]

@[simp]
/--
lemma `KaehlerDifferential.mvPolynomialBasis_apply` / 引理 `KaehlerDifferential.mvPolynomialBasis_apply`

English:
lemma KaehlerDifferential.mvPolynomialBasis_apply
  given: (σ) (i)
  proof: (mvPolynomialBasis_repr_symm_single R σ i 1).trans (one_smul _ _)

中文:
引理 KaehlerDifferential.mvPolynomialBasis_apply
  条件: (σ) (i)
  证明: (mvPolynomialBasis_repr_symm_single R σ i 1).trans (one_smul _ _)

Depends on / 依赖: mvPolynomialBasis_repr_symm_single, one_smul
-/
lemma KaehlerDifferential.mvPolynomialBasis_apply (σ) (i) :
    mvPolynomialBasis R σ i = D R (MvPolynomial σ R) (.X i) :=
  (mvPolynomialBasis_repr_symm_single R σ i 1).trans (one_smul _ _)

instance (σ) : Module.Free (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  .of_basis (KaehlerDifferential.mvPolynomialBasis R σ)

end MvPolynomial

section Polynomial

open Polynomial

/--
lemma `KaehlerDifferential.polynomial_D_apply` / 引理 `KaehlerDifferential.polynomial_D_apply`

English:
lemma KaehlerDifferential.polynomial_D_apply
  given: (P : R[X])
  proof: by
  rw [← aeval_X_left_apply P]; rw [(D R R[X]).map_aeval, aeval_X_left_apply, aeval_X_left_apply]

中文:
引理 KaehlerDifferential.polynomial_D_apply
  条件: (P : R[X])
  证明: by
  rw [← aeval_X_left_apply P]; rw [(D R R[X]).map_aeval, aeval_X_left_apply, aeval_X_left_apply]

Depends on / 依赖: aeval_X_left_apply, map_aeval
-/
lemma KaehlerDifferential.polynomial_D_apply (P : R[X]) :
    D R R[X] P = derivative P • D R R[X] X := by
  rw [← aeval_X_left_apply P]; rw [(D R R[X]).map_aeval, aeval_X_left_apply, aeval_X_left_apply]

/--
Definition of `KaehlerDifferential.polynomialEquiv` / `KaehlerDifferential.polynomialEquiv` 的定义

English:
definition KaehlerDifferential.polynomialEquiv
  signature: : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where
  body: derivative'.liftKaehlerDifferential
  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [ma

中文:
定义 KaehlerDifferential.polynomialEquiv
  签名: : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where
  定义体: derivative'.liftKaehlerDifferential
  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [ma

Depends on / 依赖: derivative, liftKaehlerDifferential
-/
def KaehlerDifferential.polynomialEquiv : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where
  __ := derivative'.liftKaehlerDifferential
  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.flip_apply,
        AlgHom.toLinearMap_apply, lsmul_coe] at *; simp only [*]
    | single x y => simp [polynomial_D_apply _ x]
  right_inv x := by simp

/--
lemma `KaehlerDifferential.polynomialEquiv_comp_D` / 引理 `KaehlerDifferential.polynomialEquiv_comp_D`

English:
lemma KaehlerDifferential.polynomialEquiv_comp_D
  proof: Derivation.liftKaehlerDifferential_comp _

@[simp]

中文:
引理 KaehlerDifferential.polynomialEquiv_comp_D
  证明: Derivation.liftKaehlerDifferential_comp _

@[simp]

Depends on / 依赖: Derivation, Derivation.liftKaehlerDifferential_comp, liftKaehlerDifferential_comp
-/
lemma KaehlerDifferential.polynomialEquiv_comp_D :
    (polynomialEquiv R).compDer (D R R[X]) = derivative' :=
  Derivation.liftKaehlerDifferential_comp _

@[simp]
/--
lemma `KaehlerDifferential.polynomialEquiv_D` / 引理 `KaehlerDifferential.polynomialEquiv_D`

English:
lemma KaehlerDifferential.polynomialEquiv_D
  given: (P)
  proof: Derivation.congr_fun (polynomialEquiv_comp_D R) P

@[simp]

中文:
引理 KaehlerDifferential.polynomialEquiv_D
  条件: (P)
  证明: Derivation.congr_fun (polynomialEquiv_comp_D R) P

@[simp]

Depends on / 依赖: Derivation, Derivation.congr_fun, congr_fun, polynomialEquiv_comp_D
-/
lemma KaehlerDifferential.polynomialEquiv_D (P) :
    polynomialEquiv R (D R R[X] P) = derivative P :=
  Derivation.congr_fun (polynomialEquiv_comp_D R) P

@[simp]
/--
lemma `KaehlerDifferential.polynomialEquiv_symm` / 引理 `KaehlerDifferential.polynomialEquiv_symm`

English:
lemma KaehlerDifferential.polynomialEquiv_symm
  given: (P)
  proof: rfl

中文:
引理 KaehlerDifferential.polynomialEquiv_symm
  条件: (P)
  证明: rfl
-/
lemma KaehlerDifferential.polynomialEquiv_symm (P) :
    (polynomialEquiv R).symm P = P • D R R[X] X := rfl

end Polynomial
