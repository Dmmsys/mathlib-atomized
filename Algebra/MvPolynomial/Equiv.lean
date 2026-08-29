/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Elias Judin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Fin
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Finsupp.Option
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

@[expose] public section


noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : Nat} {s : σ ->₀ Nat}

section Equiv

variable (R) [CommSemiring R]

/-- The algebra isomorphism between multivariable polynomials indexed by a type with a unique
element and polynomials over the ground ring. -/
@[simps]
/--
Definition of `uniqueAlgEquiv` / `uniqueAlgEquiv` 的定义

English:
definition uniqueAlgEquiv
  signature: (σ : Type*) [Unique σ]
  body: eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X default)
  left_inv := by
    let f : R[X] ->+* MvPolynomial σ R := Polynomial.eval₂RingHom MvPolynomial.C (X default)
    let g : MvPolynomial σ R ->+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    change forall p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C]; rw [Polynomial.eval₂_C]
    · intro i
      dsimp [f, g]
      rw [eval₂_X]; rw [Polynomial.eval₂_X]
      rw [← Unique.eq_default i]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_pow]; rw [Polynomial.eval₂_X]; rw [Polynomial.eval₂_C]; rw [eval₂_mul]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _

中文:
定义 uniqueAlgEquiv
  签名: (σ : 类型) [唯一 σ]
  定义体: eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X default)
  left_inv := by
    let f : R[X] ->+* MvPolynomial σ R := Polynomial.eval₂RingHom MvPolynomial.C (X default)
    let g : MvPolynomial σ R ->+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    change forall p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C]; rw [Polynomial.eval₂_C]
    · intro i
      dsimp [f, g]
      rw [eval₂_X]; rw [Polynomial.eval₂_X]
      rw [← Unique.eq_default i]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_pow]; rw [Polynomial.eval₂_X]; rw [Polynomial.eval₂_C]; rw [eval₂_mul]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _

Depends on / 依赖: Polynomial, Polynomial.C, Polynomial.X
-/
def uniqueAlgEquiv (σ : Type*) [Unique σ] : MvPolynomial σ R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X default)
  left_inv := by
    let f : R[X] ->+* MvPolynomial σ R := Polynomial.eval₂RingHom MvPolynomial.C (X default)
    let g : MvPolynomial σ R ->+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    change forall p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C]; rw [Polynomial.eval₂_C]
    · intro i
      dsimp [f, g]
      rw [eval₂_X]; rw [Polynomial.eval₂_X]
      rw [← Unique.eq_default i]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul]; rw [Polynomial.eval₂_pow]; rw [Polynomial.eval₂_X]; rw [Polynomial.eval₂_C]; rw [eval₂_mul]; rw [eval₂_C]; rw [eval₂_pow]; rw [eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _

/--
theorem `uniqueAlgEquiv_monomial` / 定理 `uniqueAlgEquiv_monomial`

English:
theorem uniqueAlgEquiv_monomial
  given: [Unique σ] {d : σ ->₀ Nat} {r : R}
  proof: by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

中文:
定理 uniqueAlgEquiv_monomial
  条件: [唯一 σ] {d : σ ->₀ 自然数} {r : R}
  证明: by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

Depends on / 依赖: C_mul_X_pow_eq_monomial, Polynomial, Polynomial.C_mul_X_pow_eq_monomial
-/
theorem uniqueAlgEquiv_monomial [Unique σ] {d : σ ->₀ Nat} {r : R} :
    (MvPolynomial.uniqueAlgEquiv R σ) (MvPolynomial.monomial d r)
      = Polynomial.monomial (d default) r := by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

/--
theorem `uniqueAlgEquiv_symm_monomial` / 定理 `uniqueAlgEquiv_symm_monomial`

English:
theorem uniqueAlgEquiv_symm_monomial
  given: [Unique σ] {d : σ ->₀ Nat} {r : R}
  proof: by
  simp [MvPolynomial.monomial_eq]

中文:
定理 uniqueAlgEquiv_symm_monomial
  条件: [唯一 σ] {d : σ ->₀ 自然数} {r : R}
  证明: by
  simp [MvPolynomial.monomial_eq]

Depends on / 依赖: MvPolynomial, MvPolynomial.monomial_eq, monomial_eq
-/
theorem uniqueAlgEquiv_symm_monomial [Unique σ] {d : σ ->₀ Nat} {r : R} :
    (MvPolynomial.uniqueAlgEquiv R σ).symm (Polynomial.monomial (d default) r)
      = MvPolynomial.monomial d r := by
  simp [MvPolynomial.monomial_eq]

/--
theorem `coeff_uniqueAlgEquiv` / 定理 `coeff_uniqueAlgEquiv`

English:
theorem coeff_uniqueAlgEquiv
  given: [Unique σ] (P : MvPolynomial σ R) (n : Nat)
  proof: by
  induction P using induction_on' with
  | monomial d r =>
      rw [uniqueAlgEquiv_monomial]; rw [Finsupp.unique_single d]
      simp [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  | add P Q hP hQ =>
      simpa using congrArg₂ (· + ·) hP hQ

中文:
定理 coeff_uniqueAlgEquiv
  条件: [唯一 σ] (P : 多元多项式 σ R) (n : 自然数)
  证明: by
  induction P using induction_on' with
  | monomial d r =>
      rw [uniqueAlgEquiv_monomial]; rw [Finsupp.unique_single d]
      simp [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  | add P Q hP hQ =>
      simpa using congrArg₂ (· + ·) hP hQ

Depends on / 依赖: Finsupp, Finsupp.unique_single, MvPolynomial, MvPolynomial.coeff_monomial, Polynomial, Polynomial.coeff_monomial, coeff_monomial, induction_on, monomial, uniqueAlgEquiv_monomial, unique_single
-/
theorem coeff_uniqueAlgEquiv [Unique σ] (P : MvPolynomial σ R) (n : Nat) :
    (MvPolynomial.uniqueAlgEquiv R σ P : Polynomial R).coeff n =
      coeff (Finsupp.single default n) P := by
  induction P using induction_on' with
  | monomial d r =>
      rw [uniqueAlgEquiv_monomial]; rw [Finsupp.unique_single d]
      simp [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  | add P Q hP hQ =>
      simpa using congrArg₂ (· + ·) hP hQ

/--
theorem `coeff_uniqueAlgEquiv_symm` / 定理 `coeff_uniqueAlgEquiv_symm`

English:
theorem coeff_uniqueAlgEquiv_symm
  given: [Unique σ] (P : Polynomial R) (d : σ ->₀ Nat)
  proof: by
  rw [Finsupp.unique_single d]; rw [← coeff_uniqueAlgEquiv R]; rw [AlgEquiv.apply_symm_apply]; rw [Finsupp.single_eq_same]

中文:
定理 coeff_uniqueAlgEquiv_symm
  条件: [唯一 σ] (P : 多项式 R) (d : σ ->₀ 自然数)
  证明: by
  rw [Finsupp.unique_single d]; rw [← coeff_uniqueAlgEquiv R]; rw [AlgEquiv.apply_symm_apply]; rw [Finsupp.single_eq_same]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, Finsupp, Finsupp.single_eq_same, Finsupp.unique_single, apply_symm_apply, coeff_uniqueAlgEquiv, single_eq_same, unique_single
-/
theorem coeff_uniqueAlgEquiv_symm [Unique σ] (P : Polynomial R) (d : σ ->₀ Nat) :
    coeff d ((MvPolynomial.uniqueAlgEquiv R σ).symm P) = P.coeff (d default) := by
  rw [Finsupp.unique_single d]; rw [← coeff_uniqueAlgEquiv R]; rw [AlgEquiv.apply_symm_apply]; rw [Finsupp.single_eq_same]

/-- The algebra isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring. -/
@[deprecated uniqueAlgEquiv (since := "2026-04-15")]
/--
Definition of `pUnitAlgEquiv` / `pUnitAlgEquiv` 的定义

English:
abbreviation pUnitAlgEquiv
  body: uniqueAlgEquiv (R := R) PUnit

@[deprecated uniqueAlgEquiv_monomial (since := "2026-04-15")]

中文:
缩写 pUnitAlgEquiv
  定义体: uniqueAlgEquiv (R := R) PUnit

@[deprecated uniqueAlgEquiv_monomial (since := "2026-04-15")]

Depends on / 依赖: uniqueAlgEquiv
-/
abbrev pUnitAlgEquiv := uniqueAlgEquiv (R := R) PUnit

@[deprecated uniqueAlgEquiv_monomial (since := "2026-04-15")]
/--
theorem `pUnitAlgEquiv_monomial` / 定理 `pUnitAlgEquiv_monomial`

English:
theorem pUnitAlgEquiv_monomial
  given: {d : PUnit ->₀ Nat} {r : R}
  proof: uniqueAlgEquiv_monomial _

@[deprecated uniqueAlgEquiv_symm_monomial (since := "2026-04-15")]

中文:
定理 pUnitAlgEquiv_monomial
  条件: {d : 命题单元 ->₀ 自然数} {r : R}
  证明: uniqueAlgEquiv_monomial _

@[deprecated uniqueAlgEquiv_symm_monomial (since := "2026-04-15")]

Depends on / 依赖: uniqueAlgEquiv_monomial
-/
theorem pUnitAlgEquiv_monomial {d : PUnit ->₀ Nat} {r : R} :
    MvPolynomial.pUnitAlgEquiv R (MvPolynomial.monomial d r)
      = Polynomial.monomial (d ()) r :=
  uniqueAlgEquiv_monomial _

@[deprecated uniqueAlgEquiv_symm_monomial (since := "2026-04-15")]
/--
theorem `pUnitAlgEquiv_symm_monomial` / 定理 `pUnitAlgEquiv_symm_monomial`

English:
theorem pUnitAlgEquiv_symm_monomial
  given: {d : PUnit ->₀ Nat} {r : R}
  proof: uniqueAlgEquiv_symm_monomial _

中文:
定理 pUnitAlgEquiv_symm_monomial
  条件: {d : 命题单元 ->₀ 自然数} {r : R}
  证明: uniqueAlgEquiv_symm_monomial _

Depends on / 依赖: uniqueAlgEquiv_symm_monomial
-/
theorem pUnitAlgEquiv_symm_monomial {d : PUnit ->₀ Nat} {r : R} :
    (MvPolynomial.pUnitAlgEquiv R).symm (Polynomial.monomial (d ()) r)
      = MvPolynomial.monomial d r :=
  uniqueAlgEquiv_symm_monomial _

section Map

variable {R} (σ)

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂)
  body: AddMonoidAlgebra.mapRingEquiv _ e

@[simp]

中文:
定义 mapEquiv
  签名: [交换半环 S₁] [交换半环 S₂] (e : S₁ ≃+* S₂)
  定义体: AddMonoidAlgebra.mapRingEquiv _ e

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapRingEquiv, mapRingEquiv
-/
def mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    MvPolynomial σ S₁ ≃+* MvPolynomial σ S₂ :=
  AddMonoidAlgebra.mapRingEquiv _ e

@[simp]
/--
lemma `mapEquiv_apply` / 引理 `mapEquiv_apply`

English:
lemma mapEquiv_apply
  statement: [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂)
  proof: rfl

@[simp]

中文:
引理 mapEquiv_apply
  结论: [交换半环 S₁] [交换半环 S₂] (e : S₁ ≃+* S₂)
  证明: rfl

@[simp]
-/
lemma mapEquiv_apply [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂)
    (x : MvPolynomial σ S₁) :
    mapEquiv σ e x = map e x := rfl

@[simp]
/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  statement: mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _
  proof: RingEquiv.ext map_id

@[simp]

中文:
定理 mapEquiv_refl
  结论: mapEquiv σ (环等价.refl R) = 环等价.refl _
  证明: RingEquiv.ext map_id

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.ext, map_id
-/
theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext map_id

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  given: [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂)
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm
  条件: [交换半环 S₁] [交换半环 S₂] (e : S₁ ≃+* S₂)
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm :=
  rfl

@[simp]
/--
theorem `mapEquiv_trans` / 定理 `mapEquiv_trans`

English:
theorem mapEquiv_trans
  statement: [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
  proof: (AddMonoidAlgebra.mapRingEquiv_trans _ _).symm

中文:
定理 mapEquiv_trans
  结论: [交换半环 S₁] [交换半环 S₂] [交换半环 S₃] (e : S₁ ≃+* S₂)
  证明: (AddMonoidAlgebra.mapRingEquiv_trans _ _).symm

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapRingEquiv_trans, mapRingEquiv_trans
-/
theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  (AddMonoidAlgebra.mapRingEquiv_trans _ _).symm

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (e : A₁ ≃ₐ[R] A₂)
  body: AddMonoidAlgebra.mapAlgEquiv _ _ e

@[simp]

中文:
定义 mapAlgEquiv
  签名: (e : A₁ ≃ₐ[R] A₂)
  定义体: AddMonoidAlgebra.mapAlgEquiv _ _ e

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapAlgEquiv, mapAlgEquiv
-/
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ :=
  AddMonoidAlgebra.mapAlgEquiv _ _ e

@[simp]
/--
lemma `mapAlgEquiv_apply` / 引理 `mapAlgEquiv_apply`

English:
lemma mapAlgEquiv_apply
  given: (e : A₁ ≃ₐ[R] A₂) (x : MvPolynomial σ A₁)
  proof: rfl

@[simp]

中文:
引理 mapAlgEquiv_apply
  条件: (e : A₁ ≃ₐ[R] A₂) (x : 多元多项式 σ A₁)
  证明: rfl

@[simp]
-/
lemma mapAlgEquiv_apply (e : A₁ ≃ₐ[R] A₂) (x : MvPolynomial σ A₁) :
    mapAlgEquiv σ e x = map e x :=
  rfl

@[simp]
/--
theorem `mapAlgEquiv_refl` / 定理 `mapAlgEquiv_refl`

English:
theorem mapAlgEquiv_refl
  statement: mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl
  proof: AlgEquiv.ext map_id

@[simp]

中文:
定理 mapAlgEquiv_refl
  结论: mapAlgEquiv σ (代数等价.refl : A₁ ≃ₐ[R] A₁) = 代数等价.refl
  证明: AlgEquiv.ext map_id

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext, map_id
-/
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id

@[simp]
/--
theorem `mapAlgEquiv_symm` / 定理 `mapAlgEquiv_symm`

English:
theorem mapAlgEquiv_symm
  given: (e : A₁ ≃ₐ[R] A₂)
  statement: (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm
  proof: rfl

@[simp]

中文:
定理 mapAlgEquiv_symm
  条件: (e : A₁ ≃ₐ[R] A₂)
  结论: (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm
  证明: rfl

@[simp]
-/
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl

@[simp]
/--
theorem `mapAlgEquiv_trans` / 定理 `mapAlgEquiv_trans`

English:
theorem mapAlgEquiv_trans
  given: (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃)
  proof: (AddMonoidAlgebra.mapAlgEquiv_trans _ _).symm

中文:
定理 mapAlgEquiv_trans
  条件: (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃)
  证明: (AddMonoidAlgebra.mapAlgEquiv_trans _ _).symm

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mapAlgEquiv_trans, mapAlgEquiv_trans
-/
theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) :=
  (AddMonoidAlgebra.mapAlgEquiv_trans _ _).symm

end Map

section Eval

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/--
theorem `eval₂_uniqueAlgEquiv` / 定理 `eval₂_uniqueAlgEquiv`

English:
theorem eval₂_uniqueAlgEquiv
  statement: [Unique σ] {f : MvPolynomial σ R} {φ : R ->+* S}
  proof: by
  simp only [MvPolynomial.uniqueAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [← MvPolynomial.uniqueAlgEquiv_apply (R := R) (σ := σ)]; rw [uniqueAlgEquiv_monomial]
    simp only [Polynomial.eval₂_monomial, eval₂_monomial]
    rw [Finsupp.unique_single d]; rw [Finsupp.prod_single_index]
    · simp
    · simp only [pow_zero]
  | add f g hf hg => simp only [eval₂_add, Polynomial.eval₂_add, hf, hg]

中文:
定理 eval₂_uniqueAlgEquiv
  结论: [唯一 σ] {f : 多元多项式 σ R} {φ : R ->+* S}
  证明: by
  simp only [MvPolynomial.uniqueAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [← MvPolynomial.uniqueAlgEquiv_apply (R := R) (σ := σ)]; rw [uniqueAlgEquiv_monomial]
    simp only [Polynomial.eval₂_monomial, eval₂_monomial]
    rw [Finsupp.unique_single d]; rw [Finsupp.prod_single_index]
    · simp
    · simp only [pow_zero]
  | add f g hf hg => simp only [eval₂_add, Polynomial.eval₂_add, hf, hg]

Depends on / 依赖: Finsupp, Finsupp.prod_single_index, Finsupp.unique_single, MvPolynomial, MvPolynomial.induction_on, MvPolynomial.uniqueAlgEquiv_apply, Polynomial, Polynomial.eval, induction_on, monomial, pow_zero, prod_single_index, uniqueAlgEquiv_apply, uniqueAlgEquiv_monomial, unique_single
-/
theorem eval₂_uniqueAlgEquiv [Unique σ] {f : MvPolynomial σ R} {φ : R ->+* S}
    {a : σ -> S} :
    ((MvPolynomial.uniqueAlgEquiv R σ) f : Polynomial R).eval₂ φ (a default) =
      f.eval₂ φ a := by
  simp only [MvPolynomial.uniqueAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [← MvPolynomial.uniqueAlgEquiv_apply (R := R) (σ := σ)]; rw [uniqueAlgEquiv_monomial]
    simp only [Polynomial.eval₂_monomial, eval₂_monomial]
    rw [Finsupp.unique_single d]; rw [Finsupp.prod_single_index]
    · simp
    · simp only [pow_zero]
  | add f g hf hg => simp only [eval₂_add, Polynomial.eval₂_add, hf, hg]

/--
theorem `eval₂_uniqueAlgEquiv_symm` / 定理 `eval₂_uniqueAlgEquiv_symm`

English:
theorem eval₂_uniqueAlgEquiv_symm
  statement: [Unique σ] {f : Polynomial R} {φ : R ->+* S}
  proof: by
  rw [(eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := (MvPolynomial.uniqueAlgEquiv R σ).symm f)
    (φ := φ) (a := a)).symm]
  rw [AlgEquiv.apply_symm_apply]

中文:
定理 eval₂_uniqueAlgEquiv_symm
  结论: [唯一 σ] {f : 多项式 R} {φ : R ->+* S}
  证明: by
  rw [(eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := (MvPolynomial.uniqueAlgEquiv R σ).symm f)
    (φ := φ) (a := a)).symm]
  rw [AlgEquiv.apply_symm_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, MvPolynomial, MvPolynomial.uniqueAlgEquiv, apply_symm_apply, uniqueAlgEquiv
-/
theorem eval₂_uniqueAlgEquiv_symm [Unique σ] {f : Polynomial R} {φ : R ->+* S}
    {a : σ -> S} :
    ((MvPolynomial.uniqueAlgEquiv R σ).symm f : MvPolynomial σ R).eval₂ φ a =
      f.eval₂ φ (a default) := by
  rw [(eval₂_uniqueAlgEquiv (R := R) (σ := σ) (f := (MvPolynomial.uniqueAlgEquiv R σ).symm f)
    (φ := φ) (a := a)).symm]
  rw [AlgEquiv.apply_symm_apply]

/--
theorem `eval₂_const_uniqueAlgEquiv_symm` / 定理 `eval₂_const_uniqueAlgEquiv_symm`

English:
theorem eval₂_const_uniqueAlgEquiv_symm
  statement: [Unique σ] {f : Polynomial R}
  proof: by
  rw [eval₂_uniqueAlgEquiv_symm]

中文:
定理 eval₂_const_uniqueAlgEquiv_symm
  结论: [唯一 σ] {f : 多项式 R}
  证明: by
  rw [eval₂_uniqueAlgEquiv_symm]
-/
theorem eval₂_const_uniqueAlgEquiv_symm [Unique σ] {f : Polynomial R}
    {φ : R ->+* S} {a : S} :
    ((MvPolynomial.uniqueAlgEquiv R σ).symm f : MvPolynomial σ R).eval₂ φ (fun _ => a) =
      f.eval₂ φ a := by
  rw [eval₂_uniqueAlgEquiv_symm]

/--
theorem `eval₂_const_uniqueAlgEquiv` / 定理 `eval₂_const_uniqueAlgEquiv`

English:
theorem eval₂_const_uniqueAlgEquiv
  statement: [Unique σ] {f : MvPolynomial σ R}
  proof: by
  rw [← eval₂_uniqueAlgEquiv]

@[deprecated eval₂_uniqueAlgEquiv_symm (since := "2026-04-15")]

中文:
定理 eval₂_const_uniqueAlgEquiv
  结论: [唯一 σ] {f : 多元多项式 σ R}
  证明: by
  rw [← eval₂_uniqueAlgEquiv]

@[deprecated eval₂_uniqueAlgEquiv_symm (since := "2026-04-15")]
-/
theorem eval₂_const_uniqueAlgEquiv [Unique σ] {f : MvPolynomial σ R}
    {φ : R ->+* S} {a : S} :
    ((MvPolynomial.uniqueAlgEquiv R σ) f : Polynomial R).eval₂ φ a =
      f.eval₂ φ (fun _ => a) := by
  rw [← eval₂_uniqueAlgEquiv]

@[deprecated eval₂_uniqueAlgEquiv_symm (since := "2026-04-15")]
/--
theorem `eval₂_pUnitAlgEquiv_symm` / 定理 `eval₂_pUnitAlgEquiv_symm`

English:
theorem eval₂_pUnitAlgEquiv_symm
  given: {f : Polynomial R} {φ : R ->+* S} {a : Unit -> S}
  proof: eval₂_uniqueAlgEquiv_symm

@[deprecated eval₂_const_uniqueAlgEquiv_symm (since := "2026-04-15")]

中文:
定理 eval₂_pUnitAlgEquiv_symm
  条件: {f : 多项式 R} {φ : R ->+* S} {a : 单元 -> S}
  证明: eval₂_uniqueAlgEquiv_symm

@[deprecated eval₂_const_uniqueAlgEquiv_symm (since := "2026-04-15")]
-/
theorem eval₂_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R ->+* S} {a : Unit -> S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ a =
      f.eval₂ φ (a ()) :=
  eval₂_uniqueAlgEquiv_symm

@[deprecated eval₂_const_uniqueAlgEquiv_symm (since := "2026-04-15")]
/--
theorem `eval₂_const_pUnitAlgEquiv_symm` / 定理 `eval₂_const_pUnitAlgEquiv_symm`

English:
theorem eval₂_const_pUnitAlgEquiv_symm
  given: {f : Polynomial R} {φ : R ->+* S} {a : S}
  proof: eval₂_const_uniqueAlgEquiv_symm

@[deprecated eval₂_uniqueAlgEquiv (since := "2026-04-15")]

中文:
定理 eval₂_const_pUnitAlgEquiv_symm
  条件: {f : 多项式 R} {φ : R ->+* S} {a : S}
  证明: eval₂_const_uniqueAlgEquiv_symm

@[deprecated eval₂_uniqueAlgEquiv (since := "2026-04-15")]
-/
theorem eval₂_const_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R ->+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ (fun _ => a) =
      f.eval₂ φ a :=
  eval₂_const_uniqueAlgEquiv_symm

@[deprecated eval₂_uniqueAlgEquiv (since := "2026-04-15")]
/--
theorem `eval₂_pUnitAlgEquiv` / 定理 `eval₂_pUnitAlgEquiv`

English:
theorem eval₂_pUnitAlgEquiv
  given: {f : MvPolynomial PUnit R} {φ : R ->+* S} {a : PUnit -> S}
  proof: eval₂_uniqueAlgEquiv

@[deprecated eval₂_const_uniqueAlgEquiv (since := "2026-04-15")]

中文:
定理 eval₂_pUnitAlgEquiv
  条件: {f : 多元多项式 命题单元 R} {φ : R ->+* S} {a : 命题单元 -> S}
  证明: eval₂_uniqueAlgEquiv

@[deprecated eval₂_const_uniqueAlgEquiv (since := "2026-04-15")]
-/
theorem eval₂_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R ->+* S} {a : PUnit -> S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ (a default) = f.eval₂ φ a :=
  eval₂_uniqueAlgEquiv

@[deprecated eval₂_const_uniqueAlgEquiv (since := "2026-04-15")]
/--
theorem `eval₂_const_pUnitAlgEquiv` / 定理 `eval₂_const_pUnitAlgEquiv`

English:
theorem eval₂_const_pUnitAlgEquiv
  given: {f : MvPolynomial PUnit R} {φ : R ->+* S} {a : S}
  proof: eval₂_const_uniqueAlgEquiv

中文:
定理 eval₂_const_pUnitAlgEquiv
  条件: {f : 多元多项式 命题单元 R} {φ : R ->+* S} {a : S}
  证明: eval₂_const_uniqueAlgEquiv
-/
theorem eval₂_const_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R ->+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ a = f.eval₂ φ (fun _ => a) :=
  eval₂_const_uniqueAlgEquiv

end Eval

section

variable (S₁ S₂ S₃)

section isEmptyRingEquiv
variable [IsEmpty σ]

variable (σ) in
/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
/--
Definition of `isEmptyAlgEquiv` / `isEmptyAlgEquiv` 的定义

English:
definition isEmptyAlgEquiv
  signature: : MvPolynomial σ R ≃ₐ[R] R
  body: AddMonoidAlgebra.uniqueAlgEquiv ..

中文:
定义 isEmptyAlgEquiv
  签名: : 多元多项式 σ R ≃ₐ[R] R
  定义体: AddMonoidAlgebra.uniqueAlgEquiv ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.uniqueAlgEquiv, uniqueAlgEquiv
-/
def isEmptyAlgEquiv : MvPolynomial σ R ≃ₐ[R] R := AddMonoidAlgebra.uniqueAlgEquiv ..

variable {R S₁} in
@[simp]
/--
lemma `aeval_injective_iff_of_isEmpty` / 引理 `aeval_injective_iff_of_isEmpty`

English:
lemma aeval_injective_iff_of_isEmpty
  given: [CommSemiring S₁] [Algebra R S₁] {f : σ -> S₁}
  proof: by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this]; rw [← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

中文:
引理 aeval_injective_iff_of_isEmpty
  条件: [交换半环 S₁] [代数 R S₁] {f : σ -> S₁}
  证明: by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this]; rw [← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

Depends on / 依赖: Algebra, Algebra.ofId, Injective, Injective.of_comp_iff, IsEmpty, IsEmpty.elim, bijective, isEmptyAlgEquiv, of_comp_iff, toAlgHom
-/
lemma aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ -> S₁} :
    Function.Injective (aeval f : MvPolynomial σ R ->ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this]; rw [← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

variable (σ) in
/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
/--
Definition of `isEmptyRingEquiv` / `isEmptyRingEquiv` 的定义

English:
definition isEmptyRingEquiv
  signature: : MvPolynomial σ R ≃+* R
  body: AddMonoidAlgebra.uniqueRingEquiv _

中文:
定义 isEmptyRingEquiv
  签名: : 多元多项式 σ R ≃+* R
  定义体: AddMonoidAlgebra.uniqueRingEquiv _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.uniqueRingEquiv, uniqueRingEquiv
-/
def isEmptyRingEquiv : MvPolynomial σ R ≃+* R := AddMonoidAlgebra.uniqueRingEquiv _

variable (σ) in
/--
lemma `isEmptyRingEquiv_symm_apply` / 引理 `isEmptyRingEquiv_symm_apply`

English:
lemma isEmptyRingEquiv_symm_apply
  given: (r : R)
  statement: (isEmptyRingEquiv R σ).symm r = C r
  proof: AddMonoidAlgebra.uniqueRingEquiv_symm_apply ..

中文:
引理 isEmptyRingEquiv_symm_apply
  条件: (r : R)
  结论: (isEmptyRingEquiv R σ).symm r = C r
  证明: AddMonoidAlgebra.uniqueRingEquiv_symm_apply ..
-/
@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r :=
  AddMonoidAlgebra.uniqueRingEquiv_symm_apply ..

/--
lemma `isEmptyRingEquiv_symm_toRingHom` / 引理 `isEmptyRingEquiv_symm_toRingHom`

English:
lemma isEmptyRingEquiv_symm_toRingHom
  statement: (isEmptyRingEquiv R σ).symm.toRingHom = C
  proof: by ext; simp

中文:
引理 isEmptyRingEquiv_symm_toRingHom
  结论: (isEmptyRingEquiv R σ).symm.toRingHom = C
  证明: by ext; simp
-/
lemma isEmptyRingEquiv_symm_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := by ext; simp

/--
lemma `isEmptyRingEquiv_eq_coeff_zero` / 引理 `isEmptyRingEquiv_eq_coeff_zero`

English:
lemma isEmptyRingEquiv_eq_coeff_zero
  given: {x : MvPolynomial σ R}
  statement: isEmptyRingEquiv R σ x = x.coeff 0
  proof: rfl

中文:
引理 isEmptyRingEquiv_eq_coeff_zero
  条件: {x : 多元多项式 σ R}
  结论: isEmptyRingEquiv R σ x = x.coeff 0
  证明: rfl
-/
lemma isEmptyRingEquiv_eq_coeff_zero {x : MvPolynomial σ R} : isEmptyRingEquiv R σ x = x.coeff 0 :=
  rfl

/--
lemma `isEmptyAlgEquiv_symm_apply` / 引理 `isEmptyAlgEquiv_symm_apply`

English:
lemma isEmptyAlgEquiv_symm_apply
  given: (r : R)
  statement: (isEmptyAlgEquiv R σ).symm r = C r
  proof: isEmptyRingEquiv_symm_apply ..

中文:
引理 isEmptyAlgEquiv_symm_apply
  条件: (r : R)
  结论: (isEmptyAlgEquiv R σ).symm r = C r
  证明: isEmptyRingEquiv_symm_apply ..
-/
@[simp] lemma isEmptyAlgEquiv_symm_apply (r : R) : (isEmptyAlgEquiv R σ).symm r = C r :=
  isEmptyRingEquiv_symm_apply ..

/--
lemma `isEmptyAlgEquiv_symm_toRingHom` / 引理 `isEmptyAlgEquiv_symm_toRingHom`

English:
lemma isEmptyAlgEquiv_symm_toRingHom
  statement: (isEmptyAlgEquiv R σ).symm.toRingHom = C
  proof: isEmptyRingEquiv_symm_toRingHom _

中文:
引理 isEmptyAlgEquiv_symm_toRingHom
  结论: (isEmptyAlgEquiv R σ).symm.toRingHom = C
  证明: isEmptyRingEquiv_symm_toRingHom _

Depends on / 依赖: isEmptyRingEquiv_symm_toRingHom
-/
lemma isEmptyAlgEquiv_symm_toRingHom : (isEmptyAlgEquiv R σ).symm.toRingHom = C :=
  isEmptyRingEquiv_symm_toRingHom _

end isEmptyRingEquiv

/-- A helper function for `sumRingEquiv`. -/
@[simps]
/--
Definition of `mvPolynomialEquivMvPolynomial` / `mvPolynomialEquivMvPolynomial` 的定义

English:
definition mvPolynomialEquivMvPolynomial
  signature: [CommSemiring S₃] (f : MvPolynomial S₁ R ->+* MvPolynomial S₂ S₃)
  body: f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add

中文:
定义 mvPolynomialEquivMvPolynomial
  签名: [交换半环 S₃] (f : 多元多项式 S₁ R ->+* 多元多项式 S₂ S₃)
  定义体: f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add
-/
def mvPolynomialEquivMvPolynomial [CommSemiring S₃] (f : MvPolynomial S₁ R ->+* MvPolynomial S₂ S₃)
    (g : MvPolynomial S₂ S₃ ->+* MvPolynomial S₁ R) (hfgC : (f.comp g).comp C = C)
    (hfgX : forall n, f (g (X n)) = X n) (hgfC : (g.comp f).comp C = C) (hgfX : forall n, g (f (X n)) = X n) :
    MvPolynomial S₁ R ≃+* MvPolynomial S₂ S₃ where
  toFun := f
  invFun := g
  left_inv := is_id (RingHom.comp _ _) hgfC hgfX
  right_inv := is_id (RingHom.comp _ _) hfgC hfgX
  map_mul' := f.map_mul
  map_add' := f.map_add

/--
Definition of `sumRingEquiv` / `sumRingEquiv` 的定义

English:
definition sumRingEquiv
  signature: : MvPolynomial (S₁ oplus S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R)
  body: (mapDomainRingEquiv _ sumFinsuppAddEquivProdFinsupp).trans curryRingEquiv

@[simp]

中文:
定义 sumRingEquiv
  签名: : 多元多项式 (S₁ oplus S₂) R ≃+* 多元多项式 S₁ (多元多项式 S₂ R)
  定义体: (mapDomainRingEquiv _ sumFinsuppAddEquivProdFinsupp).trans curryRingEquiv

@[simp]

Depends on / 依赖: curryRingEquiv, mapDomainRingEquiv, sumFinsuppAddEquivProdFinsupp
-/
def sumRingEquiv : MvPolynomial (S₁ oplus S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  (mapDomainRingEquiv _ sumFinsuppAddEquivProdFinsupp).trans curryRingEquiv

@[simp]
/--
lemma `sumRingEquiv_C` / 引理 `sumRingEquiv_C`

English:
lemma sumRingEquiv_C
  given: (r : R)
  statement: sumRingEquiv R S₁ S₂ (C r) = C (C r)
  proof: by
  unfold sumRingEquiv C MvPolynomial; simp [monomial]

@[simp]

中文:
引理 sumRingEquiv_C
  条件: (r : R)
  结论: sumRingEquiv R S₁ S₂ (C r) = C (C r)
  证明: by
  unfold sumRingEquiv C MvPolynomial; simp [monomial]

@[simp]

Depends on / 依赖: MvPolynomial, monomial, sumRingEquiv
-/
lemma sumRingEquiv_C (r : R) : sumRingEquiv R S₁ S₂ (C r) = C (C r) := by
  unfold sumRingEquiv C MvPolynomial; simp [monomial]

@[simp]
/--
lemma `sumRingEquiv_X_inl` / 引理 `sumRingEquiv_X_inl`

English:
lemma sumRingEquiv_X_inl
  given: (s : S₁)
  statement: sumRingEquiv R S₁ S₂ (X <| .inl s) = X s
  proof: by
  unfold sumRingEquiv X MvPolynomial; simp [monomial, AddMonoidAlgebra.one_def]

@[simp]

中文:
引理 sumRingEquiv_X_inl
  条件: (s : S₁)
  结论: sumRingEquiv R S₁ S₂ (X <| .inl s) = X s
  证明: by
  unfold sumRingEquiv X MvPolynomial; simp [monomial, AddMonoidAlgebra.one_def]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.one_def, MvPolynomial, monomial, one_def, sumRingEquiv
-/
lemma sumRingEquiv_X_inl (s : S₁) : sumRingEquiv R S₁ S₂ (X <| .inl s) = X s := by
  unfold sumRingEquiv X MvPolynomial; simp [monomial, AddMonoidAlgebra.one_def]

@[simp]
/--
lemma `sumRingEquiv_X_inr` / 引理 `sumRingEquiv_X_inr`

English:
lemma sumRingEquiv_X_inr
  given: (s : S₂)
  statement: sumRingEquiv R S₁ S₂ (X <| .inr s) = C (X s)
  proof: by
  unfold sumRingEquiv C X MvPolynomial; simp [monomial]

@[simp]

中文:
引理 sumRingEquiv_X_inr
  条件: (s : S₂)
  结论: sumRingEquiv R S₁ S₂ (X <| .inr s) = C (X s)
  证明: by
  unfold sumRingEquiv C X MvPolynomial; simp [monomial]

@[simp]

Depends on / 依赖: MvPolynomial, monomial, sumRingEquiv
-/
lemma sumRingEquiv_X_inr (s : S₂) : sumRingEquiv R S₁ S₂ (X <| .inr s) = C (X s) := by
  unfold sumRingEquiv C X MvPolynomial; simp [monomial]

@[simp]
/--
lemma `sumRingEquiv_symm_C_C` / 引理 `sumRingEquiv_symm_C_C`

English:
lemma sumRingEquiv_symm_C_C
  given: (r : R)
  statement: (sumRingEquiv R S₁ S₂).symm (C <| C r) = C r
  proof: by
  simp [← sumRingEquiv_C]

@[simp]

中文:
引理 sumRingEquiv_symm_C_C
  条件: (r : R)
  结论: (sumRingEquiv R S₁ S₂).symm (C <| C r) = C r
  证明: by
  simp [← sumRingEquiv_C]

@[simp]

Depends on / 依赖: sumRingEquiv_C
-/
lemma sumRingEquiv_symm_C_C (r : R) : (sumRingEquiv R S₁ S₂).symm (C <| C r) = C r := by
  simp [← sumRingEquiv_C]

@[simp]
/--
lemma `sumRingEquiv_symm_X` / 引理 `sumRingEquiv_symm_X`

English:
lemma sumRingEquiv_symm_X
  given: (s : S₁)
  statement: (sumRingEquiv R S₁ S₂).symm (X s) = X (.inl s)
  proof: by
  simp [← sumRingEquiv_X_inl]

@[simp]

中文:
引理 sumRingEquiv_symm_X
  条件: (s : S₁)
  结论: (sumRingEquiv R S₁ S₂).symm (X s) = X (.inl s)
  证明: by
  simp [← sumRingEquiv_X_inl]

@[simp]

Depends on / 依赖: sumRingEquiv_X_inl
-/
lemma sumRingEquiv_symm_X (s : S₁) : (sumRingEquiv R S₁ S₂).symm (X s) = X (.inl s) := by
  simp [← sumRingEquiv_X_inl]

@[simp]
/--
lemma `sumRingEquiv_symm_C_X` / 引理 `sumRingEquiv_symm_C_X`

English:
lemma sumRingEquiv_symm_C_X
  given: (s : S₂)
  statement: (sumRingEquiv R S₁ S₂).symm (C <| X s) = X (.inr s)
  proof: by
  simp [← sumRingEquiv_X_inr]

中文:
引理 sumRingEquiv_symm_C_X
  条件: (s : S₂)
  结论: (sumRingEquiv R S₁ S₂).symm (C <| X s) = X (.inr s)
  证明: by
  simp [← sumRingEquiv_X_inr]

Depends on / 依赖: sumRingEquiv_X_inr
-/
lemma sumRingEquiv_symm_C_X (s : S₂) : (sumRingEquiv R S₁ S₂).symm (C <| X s) = X (.inr s) := by
  simp [← sumRingEquiv_X_inr]

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
@[deprecated sumRingEquiv (since := "2026-06-18")]
/--
Definition of `sumToIter` / `sumToIter` 的定义

English:
definition sumToIter
  signature: : MvPolynomial (S₁ oplus S₂) R ->+* MvPolynomial S₁ (MvPolynomial S₂ R)
  body: eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)

@[deprecated sumRingEquiv_C (since := "2026-06-18")]

中文:
定义 sumToIter
  签名: : 多元多项式 (S₁ oplus S₂) R ->+* 多元多项式 S₁ (多元多项式 S₂ R)
  定义体: eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)

@[deprecated sumRingEquiv_C (since := "2026-06-18")]

Depends on / 依赖: C.comp, Sum.recOn
-/
def sumToIter : MvPolynomial (S₁ oplus S₂) R ->+* MvPolynomial S₁ (MvPolynomial S₂ R) :=
  eval₂Hom (C.comp C) fun bc => Sum.recOn bc X (C ∘ X)

@[deprecated sumRingEquiv_C (since := "2026-06-18")]
/--
theorem `sumToIter_C` / 定理 `sumToIter_C`

English:
theorem sumToIter_C
  given: (a : R)
  statement: sumToIter R S₁ S₂ (C a) = C (C a)
  proof: eval₂_C _ _ a

@[deprecated sumRingEquiv_X_inl (since := "2026-06-18")]

中文:
定理 sumToIter_C
  条件: (a : R)
  结论: sumToIter R S₁ S₂ (C a) = C (C a)
  证明: eval₂_C _ _ a

@[deprecated sumRingEquiv_X_inl (since := "2026-06-18")]
-/
theorem sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a) :=
  eval₂_C _ _ a

@[deprecated sumRingEquiv_X_inl (since := "2026-06-18")]
/--
theorem `sumToIter_Xl` / 定理 `sumToIter_Xl`

English:
theorem sumToIter_Xl
  given: (b : S₁)
  statement: sumToIter R S₁ S₂ (X (Sum.inl b)) = X b
  proof: eval₂_X _ _ (Sum.inl b)

@[deprecated sumRingEquiv_X_inr (since := "2026-06-18")]

中文:
定理 sumToIter_Xl
  条件: (b : S₁)
  结论: sumToIter R S₁ S₂ (X (和.inl b)) = X b
  证明: eval₂_X _ _ (Sum.inl b)

@[deprecated sumRingEquiv_X_inr (since := "2026-06-18")]

Depends on / 依赖: Sum.inl
-/
theorem sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b :=
  eval₂_X _ _ (Sum.inl b)

@[deprecated sumRingEquiv_X_inr (since := "2026-06-18")]
/--
theorem `sumToIter_Xr` / 定理 `sumToIter_Xr`

English:
theorem sumToIter_Xr
  given: (c : S₂)
  statement: sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c)
  proof: eval₂_X _ _ (Sum.inr c)

中文:
定理 sumToIter_Xr
  条件: (c : S₂)
  结论: sumToIter R S₁ S₂ (X (和.inr c)) = C (X c)
  证明: eval₂_X _ _ (Sum.inr c)

Depends on / 依赖: Sum.inr
-/
theorem sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c) :=
  eval₂_X _ _ (Sum.inr c)

/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
@[deprecated sumRingEquiv (since := "2026-06-18")]
/--
Definition of `iterToSum` / `iterToSum` 的定义

English:
definition iterToSum
  signature: : MvPolynomial S₁ (MvPolynomial S₂ R) ->+* MvPolynomial (S₁ oplus S₂) R
  body: eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)

@[deprecated sumRingEquiv_symm_C_C (since := "2026-06-18")]

中文:
定义 iterToSum
  签名: : 多元多项式 S₁ (多元多项式 S₂ R) ->+* 多元多项式 (S₁ oplus S₂) R
  定义体: eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)

@[deprecated sumRingEquiv_symm_C_C (since := "2026-06-18")]

Depends on / 依赖: Sum.inl, Sum.inr
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) ->+* MvPolynomial (S₁ oplus S₂) R :=
  eval₂Hom (eval₂Hom C (X ∘ Sum.inr)) (X ∘ Sum.inl)

@[deprecated sumRingEquiv_symm_C_C (since := "2026-06-18")]
/--
theorem `iterToSum_C_C` / 定理 `iterToSum_C_C`

English:
theorem iterToSum_C_C
  given: (a : R)
  statement: iterToSum R S₁ S₂ (C (C a)) = C a
  proof: Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

@[deprecated sumRingEquiv_symm_X (since := "2026-06-18")]

中文:
定理 iterToSum_C_C
  条件: (a : R)
  结论: iterToSum R S₁ S₂ (C (C a)) = C a
  证明: Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

@[deprecated sumRingEquiv_symm_X (since := "2026-06-18")]

Depends on / 依赖: Eq.trans
-/
theorem iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a :=
  Eq.trans (eval₂_C _ _ (C a)) (eval₂_C _ _ _)

@[deprecated sumRingEquiv_symm_X (since := "2026-06-18")]
/--
theorem `iterToSum_X` / 定理 `iterToSum_X`

English:
theorem iterToSum_X
  given: (b : S₁)
  statement: iterToSum R S₁ S₂ (X b) = X (Sum.inl b)
  proof: eval₂_X _ _ _

@[deprecated sumRingEquiv_symm_C_X (since := "2026-06-18")]

中文:
定理 iterToSum_X
  条件: (b : S₁)
  结论: iterToSum R S₁ S₂ (X b) = X (和.inl b)
  证明: eval₂_X _ _ _

@[deprecated sumRingEquiv_symm_C_X (since := "2026-06-18")]
-/
theorem iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b) :=
  eval₂_X _ _ _

@[deprecated sumRingEquiv_symm_C_X (since := "2026-06-18")]
/--
theorem `iterToSum_C_X` / 定理 `iterToSum_C_X`

English:
theorem iterToSum_C_X
  given: (c : S₂)
  statement: iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c)
  proof: Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

@[deprecated (since := "2026-06-18")] alias iterToSum_sumToIter := RingEquiv.symm_apply_apply
@[deprecated (since := "2026-06-18")] alias sumToIter_iterToSum := RingEquiv.apply_symm_apply

中文:
定理 iterToSum_C_X
  条件: (c : S₂)
  结论: iterToSum R S₁ S₂ (C (X c)) = X (和.inr c)
  证明: Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

@[deprecated (since := "2026-06-18")] alias iterToSum_sumToIter := RingEquiv.symm_apply_apply
@[deprecated (since := "2026-06-18")] alias sumToIter_iterToSum := RingEquiv.apply_symm_apply

Depends on / 依赖: Eq.trans
-/
theorem iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c) :=
  Eq.trans (eval₂_C _ _ (X c)) (eval₂_X _ _ _)

@[deprecated (since := "2026-06-18")] alias iterToSum_sumToIter := RingEquiv.symm_apply_apply
@[deprecated (since := "2026-06-18")] alias sumToIter_iterToSum := RingEquiv.apply_symm_apply

set_option backward.isDefEq.respectTransparency false in
/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
@[simps!]
/--
Definition of `sumAlgEquiv` / `sumAlgEquiv` 的定义

English:
definition sumAlgEquiv
  signature: : MvPolynomial (S₁ oplus S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R)
  body: (domCongr _ _ sumFinsuppAddEquivProdFinsupp).trans (curryAlgEquiv _)

@[simp]

中文:
定义 sumAlgEquiv
  签名: : 多元多项式 (S₁ oplus S₂) R ≃ₐ[R] 多元多项式 S₁ (多元多项式 S₂ R)
  定义体: (domCongr _ _ sumFinsuppAddEquivProdFinsupp).trans (curryAlgEquiv _)

@[simp]

Depends on / 依赖: curryAlgEquiv, domCongr, sumFinsuppAddEquivProdFinsupp
-/
def sumAlgEquiv : MvPolynomial (S₁ oplus S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  (domCongr _ _ sumFinsuppAddEquivProdFinsupp).trans (curryAlgEquiv _)

@[simp]
/--
lemma `sumAlgEquiv_C_inl` / 引理 `sumAlgEquiv_C_inl`

English:
lemma sumAlgEquiv_C_inl
  given: (r : R)
  statement: sumAlgEquiv R S₁ S₂ (C r) = C (C r)
  proof: by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]

中文:
引理 sumAlgEquiv_C_inl
  条件: (r : R)
  结论: sumAlgEquiv R S₁ S₂ (C r) = C (C r)
  证明: by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]

Depends on / 依赖: monomial, sumAlgEquiv
-/
lemma sumAlgEquiv_C_inl (r : R) : sumAlgEquiv R S₁ S₂ (C r) = C (C r) := by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]
/--
lemma `sumAlgEquiv_symm_C_C` / 引理 `sumAlgEquiv_symm_C_C`

English:
lemma sumAlgEquiv_symm_C_C
  given: (r : R)
  statement: (sumAlgEquiv R S₁ S₂).symm (C <| C r) = C r
  proof: by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]

中文:
引理 sumAlgEquiv_symm_C_C
  条件: (r : R)
  结论: (sumAlgEquiv R S₁ S₂).symm (C <| C r) = C r
  证明: by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]

Depends on / 依赖: monomial, sumAlgEquiv
-/
lemma sumAlgEquiv_symm_C_C (r : R) : (sumAlgEquiv R S₁ S₂).symm (C <| C r) = C r := by
  ext; simp [sumAlgEquiv, C, monomial, coeff]

@[simp]
/--
lemma `sumAlgEquiv_X_inl` / 引理 `sumAlgEquiv_X_inl`

English:
lemma sumAlgEquiv_X_inl
  given: (c : S₁)
  statement: sumAlgEquiv R S₁ S₂ (X <| .inl c) = X c
  proof: by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]

中文:
引理 sumAlgEquiv_X_inl
  条件: (c : S₁)
  结论: sumAlgEquiv R S₁ S₂ (X <| .inl c) = X c
  证明: by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.one_def, monomial, one_def, sumAlgEquiv
-/
lemma sumAlgEquiv_X_inl (c : S₁) : sumAlgEquiv R S₁ S₂ (X <| .inl c) = X c := by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]
/--
lemma `sumAlgEquiv_symm_X` / 引理 `sumAlgEquiv_symm_X`

English:
lemma sumAlgEquiv_symm_X
  given: (c : S₁)
  statement: (sumAlgEquiv R S₁ S₂).symm (X c) = (X <| .inl c)
  proof: by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]

中文:
引理 sumAlgEquiv_symm_X
  条件: (c : S₁)
  结论: (sumAlgEquiv R S₁ S₂).symm (X c) = (X <| .inl c)
  证明: by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.one_def, monomial, one_def, sumAlgEquiv
-/
lemma sumAlgEquiv_symm_X (c : S₁) : (sumAlgEquiv R S₁ S₂).symm (X c) = (X <| .inl c) := by
  ext; simp [sumAlgEquiv, X, monomial, coeff, AddMonoidAlgebra.one_def]

@[simp]
/--
lemma `sumAlgEquiv_X_inr` / 引理 `sumAlgEquiv_X_inr`

English:
lemma sumAlgEquiv_X_inr
  given: (c : S₂)
  statement: sumAlgEquiv R S₁ S₂ (X <| .inr c) = C (X c)
  proof: by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

@[simp]

中文:
引理 sumAlgEquiv_X_inr
  条件: (c : S₂)
  结论: sumAlgEquiv R S₁ S₂ (X <| .inr c) = C (X c)
  证明: by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

@[simp]

Depends on / 依赖: monomial, sumAlgEquiv
-/
lemma sumAlgEquiv_X_inr (c : S₂) : sumAlgEquiv R S₁ S₂ (X <| .inr c) = C (X c) := by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

@[simp]
/--
lemma `sumAlgEquiv_symm_C_X` / 引理 `sumAlgEquiv_symm_C_X`

English:
lemma sumAlgEquiv_symm_C_X
  given: (c : S₂)
  statement: (sumAlgEquiv R S₁ S₂).symm (C <| X c) = X (.inr c)
  proof: by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

中文:
引理 sumAlgEquiv_symm_C_X
  条件: (c : S₂)
  结论: (sumAlgEquiv R S₁ S₂).symm (C <| X c) = X (.inr c)
  证明: by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

Depends on / 依赖: monomial, sumAlgEquiv
-/
lemma sumAlgEquiv_symm_C_X (c : S₂) : (sumAlgEquiv R S₁ S₂).symm (C <| X c) = X (.inr c) := by
  ext; simp [sumAlgEquiv, C, X, monomial, coeff]

/--
lemma `sumAlgEquiv_comp_rename_inr` / 引理 `sumAlgEquiv_comp_rename_inr`

English:
lemma sumAlgEquiv_comp_rename_inr
  proof: by
  ext; simp

中文:
引理 sumAlgEquiv_comp_rename_inr
  证明: by
  ext; simp
-/
lemma sumAlgEquiv_comp_rename_inr :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inr) = IsScalarTower.toAlgHom R
        (MvPolynomial S₂ R) (MvPolynomial S₁ (MvPolynomial S₂ R)) := by
  ext; simp

/--
lemma `sumAlgEquiv_comp_rename_inl` / 引理 `sumAlgEquiv_comp_rename_inl`

English:
lemma sumAlgEquiv_comp_rename_inl
  proof: by
  ext; simp

中文:
引理 sumAlgEquiv_comp_rename_inl
  证明: by
  ext; simp
-/
lemma sumAlgEquiv_comp_rename_inl :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename .inl) =
      MvPolynomial.mapAlgHom (Algebra.ofId _ _) := by
  ext; simp

section commAlgEquiv
variable {R S₁ S₂ : Type*} [CommSemiring R]

variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
noncomputable
/--
Definition of `commAlgEquiv` / `commAlgEquiv` 的定义

English:
definition commAlgEquiv
  signature: : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R)
  body: AddMonoidAlgebra.commAlgEquiv _

中文:
定义 commAlgEquiv
  签名: : 多元多项式 S₁ (多元多项式 S₂ R) ≃ₐ[R] 多元多项式 S₂ (多元多项式 S₁ R)
  定义体: AddMonoidAlgebra.commAlgEquiv _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.commAlgEquiv, commAlgEquiv
-/
def commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) :=
  AddMonoidAlgebra.commAlgEquiv _

/--
lemma `commAlgEquiv_C` / 引理 `commAlgEquiv_C`

English:
lemma commAlgEquiv_C
  given: (p)
  statement: commAlgEquiv R S₁ S₂ (.C p) = .map C p
  proof: by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext; simp [commAlgEquiv, mapAlgHom, X, C, monomial, coeff, AddMonoidAlgebra.one_def]

中文:
引理 commAlgEquiv_C
  条件: (p)
  结论: commAlgEquiv R S₁ S₂ (.C p) = .map C p
  证明: by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext; simp [commAlgEquiv, mapAlgHom, X, C, monomial, coeff, AddMonoidAlgebra.one_def]
-/
@[simp] lemma commAlgEquiv_C (p) : commAlgEquiv R S₁ S₂ (.C p) = .map C p := by
  suffices (commAlgEquiv R S₁ S₂).toAlgHom.comp
      (IsScalarTower.toAlgHom R (MvPolynomial S₂ R) _) = mapAlgHom (Algebra.ofId _ _) by
    exact DFunLike.congr_fun this p
  ext; simp [commAlgEquiv, mapAlgHom, X, C, monomial, coeff, AddMonoidAlgebra.one_def]

/--
lemma `commAlgEquiv_C_X` / 引理 `commAlgEquiv_C_X`

English:
lemma commAlgEquiv_C_X
  given: (i)
  statement: commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i
  proof: by simp [map, X, monomial]

中文:
引理 commAlgEquiv_C_X
  条件: (i)
  结论: commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i
  证明: by simp [map, X, monomial]

Depends on / 依赖: monomial
-/
lemma commAlgEquiv_C_X (i) : commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by simp [map, X, monomial]

/--
lemma `commAlgEquiv_X` / 引理 `commAlgEquiv_X`

English:
lemma commAlgEquiv_X
  given: (i)
  statement: commAlgEquiv R S₁ S₂ (.X i) = .C (.X i)
  proof: by
  ext x y; simp [X, C, monomial, commAlgEquiv]

中文:
引理 commAlgEquiv_X
  条件: (i)
  结论: commAlgEquiv R S₁ S₂ (.X i) = .C (.X i)
  证明: by
  ext x y; simp [X, C, monomial, commAlgEquiv]
-/
@[simp] lemma commAlgEquiv_X (i) : commAlgEquiv R S₁ S₂ (.X i) = .C (.X i) := by
  ext x y; simp [X, C, monomial, commAlgEquiv]

end commAlgEquiv

section optionEquivLeft

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
@[simps! -isSimp]
/--
Definition of `optionEquivLeft` / `optionEquivLeft` 的定义

English:
definition optionEquivLeft
  signature: : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R)
  body: AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by ext : 2 <;> simp) (by ext i : 2; cases i <;> simp)

@[simp]

中文:
定义 optionEquivLeft
  签名: : 多元多项式 (选项类型 S₁) R ≃ₐ[R] 多项式 (多元多项式 S₁ R)
  定义体: AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by ext : 2 <;> simp) (by ext i : 2; cases i <;> simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, MvPolynomial, MvPolynomial.aeval, MvPolynomial.rename, Polynomial, Polynomial.C, Polynomial.X, Polynomial.aevalTower, aevalTower, o.elim, ofAlgHom
-/
def optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R) :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by ext : 2 <;> simp) (by ext i : 2; cases i <;> simp)

@[simp]
/--
lemma `optionEquivLeft_X_some` / 引理 `optionEquivLeft_X_some`

English:
lemma optionEquivLeft_X_some
  given: (x : S₁)
  statement: optionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x)
  proof: by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]

中文:
引理 optionEquivLeft_X_some
  条件: (x : S₁)
  结论: optionEquivLeft R S₁ (X (some x)) = 多项式.C (X x)
  证明: by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]

Depends on / 依赖: aeval_X, optionEquivLeft_apply
-/
lemma optionEquivLeft_X_some (x : S₁) : optionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x) := by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]
/--
lemma `optionEquivLeft_X_none` / 引理 `optionEquivLeft_X_none`

English:
lemma optionEquivLeft_X_none
  statement: optionEquivLeft R S₁ (X none) = Polynomial.X
  proof: by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]

中文:
引理 optionEquivLeft_X_none
  结论: optionEquivLeft R S₁ (X none) = 多项式.X
  证明: by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]

Depends on / 依赖: aeval_X, optionEquivLeft_apply
-/
lemma optionEquivLeft_X_none : optionEquivLeft R S₁ (X none) = Polynomial.X := by
  simp [optionEquivLeft_apply, aeval_X]

@[simp]
/--
lemma `optionEquivLeft_C` / 引理 `optionEquivLeft_C`

English:
lemma optionEquivLeft_C
  given: (r : R)
  statement: optionEquivLeft R S₁ (C r) = Polynomial.C (C r)
  proof: by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

中文:
引理 optionEquivLeft_C
  条件: (r : R)
  结论: optionEquivLeft R S₁ (C r) = 多项式.C (C r)
  证明: by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

Depends on / 依赖: Polynomial, Polynomial.algebraMap_apply, aeval_C, algebraMap_apply, algebraMap_eq, optionEquivLeft_apply
-/
lemma optionEquivLeft_C (r : R) : optionEquivLeft R S₁ (C r) = Polynomial.C (C r) := by
  simp only [optionEquivLeft_apply, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq]

/--
theorem `optionEquivLeft_monomial` / 定理 `optionEquivLeft_monomial`

English:
theorem optionEquivLeft_monomial
  given: (m : Option S₁ ->₀ Nat) (r : R)
  proof: by
  rw [optionEquivLeft_apply]; rw [aeval_monomial]; rw [prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

@[simp]

中文:
定理 optionEquivLeft_monomial
  条件: (m : 选项类型 S₁ ->₀ 自然数) (r : R)
  证明: by
  rw [optionEquivLeft_apply]; rw [aeval_monomial]; rw [prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

@[simp]

Depends on / 依赖: C_mul_X_pow_eq_monomial, MvPolynomial, MvPolynomial.monomial_eq, Option.elim_none, Option.elim_some, Polynomial, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.algebraMap_apply, aeval_monomial, algebraMap_apply, algebraMap_eq, elim_none, elim_some, intros, map_finsuppProd, map_mul, map_pow, monomial_eq, mul_assoc, mul_comm
-/
theorem optionEquivLeft_monomial (m : Option S₁ ->₀ Nat) (r : R) :
    optionEquivLeft R S₁ (monomial m r) = .monomial (m none) (monomial m.some r) := by
  rw [optionEquivLeft_apply]; rw [aeval_monomial]; rw [prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.algebraMap_apply, algebraMap_eq, Option.elim_none, Option.elim_some,
      map_mul, mul_assoc]
    simp only [mul_comm, map_finsuppProd, map_pow]
  · simp
  · intros; rw [pow_add]

@[simp]
/--
lemma `optionEquivLeft_symm_C_X` / 引理 `optionEquivLeft_symm_C_X`

English:
lemma optionEquivLeft_symm_C_X
  given: (x : S₁)
  proof: by
  simp [optionEquivLeft]

@[simp]

中文:
引理 optionEquivLeft_symm_C_X
  条件: (x : S₁)
  证明: by
  simp [optionEquivLeft]

@[simp]

Depends on / 依赖: optionEquivLeft
-/
lemma optionEquivLeft_symm_C_X (x : S₁) :
    (optionEquivLeft R S₁).symm (.C (X x)) = .X (.some x) := by
  simp [optionEquivLeft]

@[simp]
/--
lemma `optionEquivLeft_symm_C_C` / 引理 `optionEquivLeft_symm_C_C`

English:
lemma optionEquivLeft_symm_C_C
  given: (x : R)
  proof: by simp [optionEquivLeft]

@[simp]

中文:
引理 optionEquivLeft_symm_C_C
  条件: (x : R)
  证明: by simp [optionEquivLeft]

@[simp]

Depends on / 依赖: optionEquivLeft
-/
lemma optionEquivLeft_symm_C_C (x : R) :
    (optionEquivLeft R S₁).symm (.C (.C x)) = .C x := by simp [optionEquivLeft]

@[simp]
/--
lemma `optionEquivLeft_symm_X` / 引理 `optionEquivLeft_symm_X`

English:
lemma optionEquivLeft_symm_X
  proof: by simp [optionEquivLeft]

中文:
引理 optionEquivLeft_symm_X
  证明: by simp [optionEquivLeft]

Depends on / 依赖: optionEquivLeft
-/
lemma optionEquivLeft_symm_X :
    (optionEquivLeft R S₁).symm .X = .X .none := by simp [optionEquivLeft]

/--
theorem `optionEquivLeft_coeff_some_coeff_none` / 定理 `optionEquivLeft_coeff_some_coeff_none`

English:
theorem optionEquivLeft_coeff_some_coeff_none
  proof: by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using! hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

中文:
定理 optionEquivLeft_coeff_some_coeff_none
  证明: by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using! hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

Depends on / 依赖: False.elim, Finsupp, Finsupp.ext_iff, MvPolynomial, MvPolynomial.coeff_monomial, MvPolynomial.induction_on, Option.forall, Polynomial, Polynomial.coeff_monomial, apply_ite, classical, coeff_monomial, coeff_zero, ext_iff, generalizing, hj_none, hj_some, if_neg, induction_on, ite_eq_right_iff
-/
theorem optionEquivLeft_coeff_some_coeff_none
    (n : Option S₁ ->₀ Nat) (f : MvPolynomial (Option S₁) R) :
    coeff n.some (Polynomial.coeff (optionEquivLeft R S₁ f) (n none)) = coeff n f := by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using! hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

/--
theorem `optionEquivLeft_elim_eval` / 定理 `optionEquivLeft_elim_eval`

English:
theorem optionEquivLeft_elim_eval
  given: (s : S₁ -> R) (y : R) (f : MvPolynomial (Option S₁) R)
  proof: by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (fun x => Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom, comp_apply,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some,
    Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true, and_self, φ]

中文:
定理 optionEquivLeft_elim_eval
  条件: (s : S₁ -> R) (y : R) (f : 多元多项式 (选项类型 S₁) R)
  证明: by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (fun x => Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom, comp_apply,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some,
    Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true, and_self, φ]
-/
theorem optionEquivLeft_elim_eval (s : S₁ -> R) (y : R) (f : MvPolynomial (Option S₁) R) :
    eval (fun x => Option.elim x y s) f =
      Polynomial.eval y (Polynomial.map (eval s) (optionEquivLeft R S₁ f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (fun x => Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom, comp_apply,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some,
    Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true, and_self, φ]

/--
theorem `mem_support_coeff_optionEquivLeft` / 定理 `mem_support_coeff_optionEquivLeft`

English:
theorem mem_support_coeff_optionEquivLeft
  given: {f : MvPolynomial (Option σ) R} {i : Nat} {m : σ ->₀ Nat}
  proof: by
  simp [← optionEquivLeft_coeff_some_coeff_none]

中文:
定理 mem_support_coeff_optionEquivLeft
  条件: {f : 多元多项式 (选项类型 σ) R} {i : 自然数} {m : σ ->₀ 自然数}
  证明: by
  simp [← optionEquivLeft_coeff_some_coeff_none]

Depends on / 依赖: optionEquivLeft_coeff_some_coeff_none
-/
theorem mem_support_coeff_optionEquivLeft {f : MvPolynomial (Option σ) R} {i : Nat} {m : σ ->₀ Nat} :
    m in ((optionEquivLeft R σ f).coeff i).support ↔ m.optionElim i in f.support := by
  simp [← optionEquivLeft_coeff_some_coeff_none]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `support_optionEquivLeft` / 引理 `support_optionEquivLeft`

English:
lemma support_optionEquivLeft
  given: (p : MvPolynomial (Option σ) R)
  proof: by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨optionElim i m, by simpa using! hm, optionElim_apply_none _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨some m, h⟩

中文:
引理 support_optionEquivLeft
  条件: (p : 多元多项式 (选项类型 σ) R)
  证明: by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨optionElim i m, by simpa using! hm, optionElim_apply_none _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨some m, h⟩

Depends on / 依赖: Finset, Finset.mem_image, MvPolynomial, MvPolynomial.ext_iff, Polynomial, Polynomial.mem_support_iff, coeff_zero, ext_iff, mem_image, mem_support_iff, ne_eq, not_forall, optionElim, optionElim_apply_none, optionEquivLeft_coeff_some_coeff_none
-/
lemma support_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    (optionEquivLeft R σ p).support = Finset.image (fun m => m none) p.support := by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨optionElim i m, by simpa using! hm, optionElim_apply_none _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨some m, h⟩

/--
theorem `nonempty_support_optionEquivLeft` / 定理 `nonempty_support_optionEquivLeft`

English:
theorem nonempty_support_optionEquivLeft
  given: {f : MvPolynomial (Option σ) R} (h : f != 0)
  proof: by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

中文:
定理 nonempty_support_optionEquivLeft
  条件: {f : 多元多项式 (选项类型 σ) R} (h : f != 0)
  证明: by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_zero_iff, Polynomial, Polynomial.support_nonempty, map_ne_zero_iff, support_nonempty
-/
theorem nonempty_support_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f != 0) :
    (optionEquivLeft R σ f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

/--
theorem `degree_optionEquivLeft` / 定理 `degree_optionEquivLeft`

English:
theorem degree_optionEquivLeft
  given: {f : MvPolynomial (Option σ) R} (h : f != 0)
  proof: by
  have h' : ((optionEquivLeft R σ f).support.sup fun x => x) = degreeOf none f := by
    rw [degreeOf_eq_sup]; rw [support_optionEquivLeft]; rw [Finset.sup_image]; rw [Function.comp_def]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_optionEquivLeft R h)]; rw [Finset.max_eq_sup_coe]; rw [Function.comp_def]

@[simp]

中文:
定理 degree_optionEquivLeft
  条件: {f : 多元多项式 (选项类型 σ) R} (h : f != 0)
  证明: by
  have h' : ((optionEquivLeft R σ f).support.sup fun x => x) = degreeOf none f := by
    rw [degreeOf_eq_sup]; rw [support_optionEquivLeft]; rw [Finset.sup_image]; rw [Function.comp_def]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_optionEquivLeft R h)]; rw [Finset.max_eq_sup_coe]; rw [Function.comp_def]

@[simp]

Depends on / 依赖: Finset, Finset.coe_sup_of_nonempty, Finset.max_eq_sup_coe, Finset.sup_image, Function, Function.comp_def, Nat.cast_withBot, Polynomial, Polynomial.degree, cast_withBot, coe_sup_of_nonempty, comp_def, degree, degreeOf, degreeOf_eq_sup, max_eq_sup_coe, nonempty_support_optionEquivLeft, optionEquivLeft, sup_image, support
-/
theorem degree_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f != 0) :
    (optionEquivLeft R σ f).degree = degreeOf none f := by
  have h' : ((optionEquivLeft R σ f).support.sup fun x => x) = degreeOf none f := by
    rw [degreeOf_eq_sup]; rw [support_optionEquivLeft]; rw [Finset.sup_image]; rw [Function.comp_def]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_optionEquivLeft R h)]; rw [Finset.max_eq_sup_coe]; rw [Function.comp_def]

@[simp]
/--
lemma `natDegree_optionEquivLeft` / 引理 `natDegree_optionEquivLeft`

English:
lemma natDegree_optionEquivLeft
  given: (p : MvPolynomial (Option σ) R)
  proof: by
  by_cases c : p = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_optionEquivLeft R c, Nat.cast_withBot, WithBot.unbotD_coe]

中文:
引理 natDegree_optionEquivLeft
  条件: (p : 多元多项式 (选项类型 σ) R)
  证明: by
  by_cases c : p = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_optionEquivLeft R c, Nat.cast_withBot, WithBot.unbotD_coe]

Depends on / 依赖: Nat.cast_withBot, Polynomial, Polynomial.natDegree, Polynomial.natDegree_zero, WithBot, WithBot.unbotD_coe, cast_withBot, degreeOf_zero, degree_optionEquivLeft, map_zero, natDegree, natDegree_zero, unbotD_coe
-/
lemma natDegree_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    Polynomial.natDegree (optionEquivLeft R σ p) = p.degreeOf none := by
  by_cases c : p = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_optionEquivLeft R c, Nat.cast_withBot, WithBot.unbotD_coe]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `totalDegree_coeff_optionEquivLeft_add_le` / 引理 `totalDegree_coeff_optionEquivLeft_add_le`

English:
lemma totalDegree_coeff_optionEquivLeft_add_le
  proof: by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree]; rw [add_comm]; rw [Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

中文:
引理 totalDegree_coeff_optionEquivLeft_add_le
  证明: by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree]; rw [add_comm]; rw [Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

Depends on / 依赖: Finset, Finset.add_sup, Finset.le_sup, Finset.sup_le_iff, Finsupp, Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm, add_sup, classical, embDomain, le_sup, le_trans, mem_support_iff, optionEquivLeft, optionEquivLeft_coeff_some_coeff_none, single, sum_add_index, sum_embDomain, sup_le_iff
-/
lemma totalDegree_coeff_optionEquivLeft_add_le
    (p : MvPolynomial (Option S₁) R) (i : Nat) (hi : i <= p.totalDegree) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree + i <= p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simpa
  rw [totalDegree]; rw [add_comm]; rw [Finset.add_sup (by simpa only [support_nonempty]), Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain, add_comm i]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

set_option backward.isDefEq.respectTransparency false in
/--
lemma `totalDegree_coeff_optionEquivLeft_le` / 引理 `totalDegree_coeff_optionEquivLeft_le`

English:
lemma totalDegree_coeff_optionEquivLeft_le
  proof: by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree]; rw [Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

中文:
引理 totalDegree_coeff_optionEquivLeft_le
  证明: by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree]; rw [Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le_iff, Finsupp, Finsupp.sum_add_index, Finsupp.sum_embDomain, classical, embDomain, le_sup, le_trans, mem_support_iff, optionEquivLeft, optionEquivLeft_coeff_some_coeff_none, single, sum_add_index, sum_embDomain, sup_le_iff, totalDegree
-/
lemma totalDegree_coeff_optionEquivLeft_le
    (p : MvPolynomial (Option S₁) R) (i : Nat) :
    ((optionEquivLeft R S₁ p).coeff i).totalDegree <= p.totalDegree := by
  classical
  by_cases hpi : (optionEquivLeft R S₁ p).coeff i = 0
  · rw [hpi]; simp
  rw [totalDegree]; rw [Finset.sup_le_iff]
  intro σ hσ
  refine le_trans ?_ (Finset.le_sup (b := σ.embDomain .some + .single .none i) ?_)
  · simp [Finsupp.sum_add_index, Finsupp.sum_embDomain]
  · simpa [mem_support_iff, ← optionEquivLeft_coeff_some_coeff_none R S₁] using hσ

/--
theorem `optionEquivLeft_coeff_coeff` / 定理 `optionEquivLeft_coeff_coeff`

English:
theorem optionEquivLeft_coeff_coeff
  proof: by
  rw [← optionEquivLeft_coeff_some_coeff_none]
  congr <;> simp

中文:
定理 optionEquivLeft_coeff_coeff
  证明: by
  rw [← optionEquivLeft_coeff_some_coeff_none]
  congr <;> simp

Depends on / 依赖: optionEquivLeft_coeff_some_coeff_none
-/
theorem optionEquivLeft_coeff_coeff
    (p : MvPolynomial (Option σ) R) (m : Nat) (d : σ ->₀ Nat) :
    coeff d (((optionEquivLeft R σ) p).coeff m) = p.coeff (d.optionElim m) := by
  rw [← optionEquivLeft_coeff_some_coeff_none]
  congr <;> simp

end optionEquivLeft

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
@[simps!]
/--
Definition of `optionEquivRight` / `optionEquivRight` 的定义

English:
definition optionEquivRight
  signature: : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X]
  body: AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          aevalTower_X, AlgHom.coe_id, id])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])

中文:
定义 optionEquivRight
  签名: : 多元多项式 (选项类型 S₁) R ≃ₐ[R] 多元多项式 S₁ R[X]
  定义体: AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          aevalTower_X, AlgHom.coe_id, id])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.coe, AlgHom.coe_comp, AlgHom.coe_id, AlgHom.id_comp, IsScalarTower, IsScalarTower.coe_toAlgHom, MvPolynomial, MvPolynomial.aeval, MvPolynomial.aevalTower, MvPolynomial.algebraMap_eq, Option.elim, Option.some, Polynomial, Polynomial.X, Polynomial.aeval, Polynomial.aeval_X, aevalTower
-/
def optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X] :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          aevalTower_X, AlgHom.coe_id, id])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])

/--
lemma `optionEquivRight_X_some` / 引理 `optionEquivRight_X_some`

English:
lemma optionEquivRight_X_some
  given: (x : S₁)
  statement: optionEquivRight R S₁ (X (some x)) = X x
  proof: by
  simp [optionEquivRight_apply, aeval_X]

中文:
引理 optionEquivRight_X_some
  条件: (x : S₁)
  结论: optionEquivRight R S₁ (X (some x)) = X x
  证明: by
  simp [optionEquivRight_apply, aeval_X]

Depends on / 依赖: aeval_X, optionEquivRight_apply
-/
lemma optionEquivRight_X_some (x : S₁) : optionEquivRight R S₁ (X (some x)) = X x := by
  simp [optionEquivRight_apply, aeval_X]

/--
lemma `optionEquivRight_X_none` / 引理 `optionEquivRight_X_none`

English:
lemma optionEquivRight_X_none
  statement: optionEquivRight R S₁ (X none) = C Polynomial.X
  proof: by
  simp [optionEquivRight_apply, aeval_X]

中文:
引理 optionEquivRight_X_none
  结论: optionEquivRight R S₁ (X none) = C 多项式.X
  证明: by
  simp [optionEquivRight_apply, aeval_X]

Depends on / 依赖: aeval_X, optionEquivRight_apply
-/
lemma optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X := by
  simp [optionEquivRight_apply, aeval_X]

/--
lemma `optionEquivRight_C` / 引理 `optionEquivRight_C`

English:
lemma optionEquivRight_C
  given: (r : R)
  statement: optionEquivRight R S₁ (C r) = C (Polynomial.C r)
  proof: by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

中文:
引理 optionEquivRight_C
  条件: (r : R)
  结论: optionEquivRight R S₁ (C r) = C (多项式.C r)
  证明: by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

Depends on / 依赖: Polynomial, Polynomial.algebraMap_eq, aeval_C, algebraMap_apply, algebraMap_eq, optionEquivRight_apply
-/
lemma optionEquivRight_C (r : R) : optionEquivRight R S₁ (C r) = C (Polynomial.C r) := by
  simp only [optionEquivRight_apply, aeval_C, algebraMap_apply, Polynomial.algebraMap_eq]

variable (n : Nat)

/--
Definition of `finSuccEquiv` / `finSuccEquiv` 的定义

English:
definition finSuccEquiv
  signature: : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)
  body: (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))

中文:
定义 finSuccEquiv
  签名: : 多元多项式 (有限集 (n + 1)) R ≃ₐ[R] 多项式 (多元多项式 (有限集 n) R)
  定义体: (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))

Depends on / 依赖: _root_, _root_.finSuccEquiv, finSuccEquiv, optionEquivLeft, renameEquiv
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))

/--
theorem `finSuccEquiv_eq` / 定理 `finSuccEquiv_eq`

English:
theorem finSuccEquiv_eq
  proof: by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, finSuccEquiv]

中文:
定理 finSuccEquiv_eq
  证明: by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, finSuccEquiv]

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_trans, Fin.cases, RingHom, RingHom.coe_coe, RingHom.coe_comp, aeval_C, coe_coe, coe_comp, coe_trans, comp_apply, finSuccEquiv, optionEquivLeft_apply, renameEquiv_apply, rename_C
-/
theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R ->+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R ->+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i := by
  ext i : 2
  · simp only [finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, finSuccEquiv]

/--
theorem `finSuccEquiv_apply` / 定理 `finSuccEquiv_apply`

English:
theorem finSuccEquiv_apply
  given: (p : MvPolynomial (Fin (n + 1)) R)
  proof: by
  rw [← finSuccEquiv_eq]; rw [RingHom.coe_coe]

中文:
定理 finSuccEquiv_apply
  条件: (p : 多元多项式 (有限集 (n + 1)) R)
  证明: by
  rw [← finSuccEquiv_eq]; rw [RingHom.coe_coe]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, finSuccEquiv_eq
-/
theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R ->+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p := by
  rw [← finSuccEquiv_eq]; rw [RingHom.coe_coe]

/--
theorem `finSuccEquiv_comp_C_eq_C` / 定理 `finSuccEquiv_comp_C_eq_C`

English:
theorem finSuccEquiv_comp_C_eq_C
  given: {R : Type u} [CommSemiring R] (n : Nat)
  proof: by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

中文:
定理 finSuccEquiv_comp_C_eq_C
  条件: {R : 类型u} [交换半环 R] (n : 自然数)
  证明: by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

Depends on / 依赖: MvPolynomial, MvPolynomial.eval, MvPolynomial.finSuccEquiv, MvPolynomial.finSuccEquiv_apply, RingHom, RingHom.comp_apply, RingHom.ext, Trans.trans, apply_symm_apply, comp_apply, finSuccEquiv, finSuccEquiv_apply, injective
-/
theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : Nat) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) ->+* _).comp
        (Polynomial.C.comp MvPolynomial.C) =
      (MvPolynomial.C : R ->+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

variable {n} {R}

/--
theorem `finSuccEquiv_X_zero` / 定理 `finSuccEquiv_X_zero`

English:
theorem finSuccEquiv_X_zero
  statement: finSuccEquiv R n (X 0) = Polynomial.X
  proof: by simp [finSuccEquiv_apply]

中文:
定理 finSuccEquiv_X_zero
  结论: finSuccEquiv R n (X 0) = 多项式.X
  证明: by simp [finSuccEquiv_apply]

Depends on / 依赖: finSuccEquiv_apply
-/
theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]

/--
theorem `finSuccEquiv_X_succ` / 定理 `finSuccEquiv_X_succ`

English:
theorem finSuccEquiv_X_succ
  given: {j : Fin n}
  statement: finSuccEquiv R n (X j.succ) = Polynomial.C (X j)
  proof: by
  simp [finSuccEquiv_apply]

中文:
定理 finSuccEquiv_X_succ
  条件: {j : 有限集 n}
  结论: finSuccEquiv R n (X j.succ) = 多项式.C (X j)
  证明: by
  simp [finSuccEquiv_apply]

Depends on / 依赖: finSuccEquiv_apply
-/
theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp [finSuccEquiv_apply]

/--
theorem `finSuccEquiv_coeff_coeff` / 定理 `finSuccEquiv_coeff_coeff`

English:
theorem finSuccEquiv_coeff_coeff
  given: (m : Fin n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat)
  proof: by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← _root_.map_prod, ← map_pow, Function.comp_apply]
    rw [← mul_boole]; rw [mul_comm (Polynomial.X ^ j 0)]; rw [Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using! coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m != j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using!
        coeff_monomial m j.tail (1 : R)

中文:
定理 finSuccEquiv_coeff_coeff
  条件: (m : 有限集 n ->₀ 自然数) (f : 多元多项式 (有限集 (n + 1)) R) (i : 自然数)
  证明: by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← _root_.map_prod, ← map_pow, Function.comp_apply]
    rw [← mul_boole]; rw [mul_comm (Polynomial.X ^ j 0)]; rw [Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using! coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m != j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using!
        coeff_monomial m j.tail (1 : R)

Depends on / 依赖: Fin.cases_succ, Fin.cases_zero, Fin.prod_univ_succ, Finsupp, Finsupp.prod_pow, Function, Function.comp_apply, MvPolynomial, MvPolynomial.induction_on, Polynomial, Polynomial.X, Polynomial.coeff_C_mu, Polynomial.coeff_C_mul, Polynomial.coeff_add, RingHom, RingHom.coe_comp, _root_, _root_.map_prod, cases_succ, cases_zero
-/
theorem finSuccEquiv_coeff_coeff (m : Fin n ->₀ Nat) (f : MvPolynomial (Fin (n + 1)) R) (i : Nat) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← _root_.map_prod, ← map_pow, Function.comp_apply]
    rw [← mul_boole]; rw [mul_comm (Polynomial.X ^ j 0)]; rw [Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using! coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m != j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using!
        coeff_monomial m j.tail (1 : R)

/--
theorem `eval_eq_eval_mv_eval'` / 定理 `eval_eq_eval_mv_eval'`

English:
theorem eval_eq_eval_mv_eval'
  given: (s : Fin n -> R) (y : R) (f : MvPolynomial (Fin (n + 1)) R)
  proof: by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (Fin.cons y s : Fin (n + 1) -> R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [aeval_X, Fin.cons_zero, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom,
    comp_apply, finSuccEquiv_apply, eval₂Hom_X', Fin.cases_zero, Polynomial.map_X,
    Polynomial.eval_X, Fin.cons_succ, Fin.cases_succ, Polynomial.map_C, eval_X, Polynomial.eval_C,
    implies_true, and_self, φ]

中文:
定理 eval_eq_eval_mv_eval'
  条件: (s : 有限集 n -> R) (y : R) (f : 多元多项式 (有限集 (n + 1)) R)
  证明: by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (Fin.cons y s : Fin (n + 1) -> R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [aeval_X, Fin.cons_zero, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom,
    comp_apply, finSuccEquiv_apply, eval₂Hom_X', Fin.cases_zero, Polynomial.map_X,
    Polynomial.eval_X, Fin.cons_succ, Fin.cases_succ, Polynomial.map_C, eval_X, Polynomial.eval_C,
    implies_true, and_self, φ]
-/
theorem eval_eq_eval_mv_eval' (s : Fin n -> R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) -> R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] ->ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert! Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    aeval (Fin.cons y s : Fin (n + 1) -> R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [aeval_X, Fin.cons_zero, AlgHom.coe_comp, Polynomial.coe_aeval_eq_eval,
    AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgEquiv.coe_toAlgHom,
    comp_apply, finSuccEquiv_apply, eval₂Hom_X', Fin.cases_zero, Polynomial.map_X,
    Polynomial.eval_X, Fin.cons_succ, Fin.cases_succ, Polynomial.map_C, eval_X, Polynomial.eval_C,
    implies_true, and_self, φ]

/--
theorem `coeff_eval_eq_eval_coeff` / 定理 `coeff_eval_eq_eval_coeff`

English:
theorem coeff_eval_eq_eval_coeff
  statement: (s' : S₁ -> R) (f : Polynomial (MvPolynomial S₁ R))
  proof: by
  simp only [Polynomial.coeff_map]

中文:
定理 coeff_eval_eq_eval_coeff
  结论: (s' : S₁ -> R) (f : 多项式 (多元多项式 S₁ R))
  证明: by
  simp only [Polynomial.coeff_map]

Depends on / 依赖: Polynomial, Polynomial.coeff_map, coeff_map
-/
theorem coeff_eval_eq_eval_coeff (s' : S₁ -> R) (f : Polynomial (MvPolynomial S₁ R))
    (i : Nat) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  simp only [Polynomial.coeff_map]

/--
theorem `mem_support_coeff_finSuccEquiv` / 定理 `mem_support_coeff_finSuccEquiv`

English:
theorem mem_support_coeff_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {m : Fin n ->₀ Nat}
  proof: by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h

中文:
定理 mem_support_coeff_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} {i : 自然数} {m : 有限集 n ->₀ 自然数}
  证明: by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h

Depends on / 依赖: Iff.intro, finSuccEquiv_coeff_coeff, mem_support_iff
-/
theorem mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {m : Fin n ->₀ Nat} :
    m in ((finSuccEquiv R n f).coeff i).support ↔ m.cons i in f.support := by
  apply Iff.intro
  · intro h
    simpa [← finSuccEquiv_coeff_coeff] using h
  · intro h
    simpa [mem_support_iff, ← finSuccEquiv_coeff_coeff m f i] using h

/--
lemma `totalDegree_coeff_finSuccEquiv_add_le` / 引理 `totalDegree_coeff_finSuccEquiv_add_le`

English:
lemma totalDegree_coeff_finSuccEquiv_add_le
  statement: (f : MvPolynomial (Fin (n + 1)) R) (i : Nat)
  proof: by
  have hf'_sup : ((finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n + 1) ->₀ Nat := cons i σ
  convert! le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← mem_support_coeff_finSuccEquiv]
    exact hσ1

中文:
引理 totalDegree_coeff_finSuccEquiv_add_le
  结论: (f : 多元多项式 (有限集 (n + 1)) R) (i : 自然数)
  证明: by
  have hf'_sup : ((finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n + 1) ->₀ Nat := cons i σ
  convert! le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← mem_support_coeff_finSuccEquiv]
    exact hσ1

Depends on / 依赖: Finset, Finset.nonempty_iff_ne_empty, Nonempty, _sup, finSuccEquiv, ne_eq, nonempty_iff_ne_empty, support, support.Nonempty, support_eq_empty
-/
lemma totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : Nat)
    (hi : (finSuccEquiv R n f).coeff i != 0) :
    totalDegree ((finSuccEquiv R n f).coeff i) + i <= totalDegree f := by
  have hf'_sup : ((finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rw [ne_eq]; rw [support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n + 1) ->₀ Nat := cons i σ
  convert! le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← mem_support_coeff_finSuccEquiv]
    exact hσ1

set_option backward.isDefEq.respectTransparency false in
/--
theorem `support_finSuccEquiv` / 定理 `support_finSuccEquiv`

English:
theorem support_finSuccEquiv
  given: (f : MvPolynomial (Fin (n + 1)) R)
  proof: by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, finSuccEquiv_coeff_coeff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨cons i m, hm, cons_zero _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨tail m, by simpa using h⟩

中文:
定理 support_finSuccEquiv
  条件: (f : 多元多项式 (有限集 (n + 1)) R)
  证明: by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, finSuccEquiv_coeff_coeff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨cons i m, hm, cons_zero _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨tail m, by simpa using h⟩

Depends on / 依赖: Finset, Finset.mem_image, MvPolynomial, MvPolynomial.ext_iff, Polynomial, Polynomial.mem_support_iff, coeff_zero, cons_zero, ext_iff, finSuccEquiv_coeff_coeff, mem_image, mem_support_iff, ne_eq, not_forall
-/
theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) ->₀ Nat => m 0) f.support := by
  ext i
  simp only [Polynomial.mem_support_iff, ne_eq, MvPolynomial.ext_iff, coeff_zero, not_forall,
    Finset.mem_image, mem_support_iff, finSuccEquiv_coeff_coeff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨cons i m, hm, cons_zero _ _⟩
  · rintro ⟨m, h, rfl⟩
    exact ⟨tail m, by simpa using h⟩

/--
theorem `mem_support_finSuccEquiv` / 定理 `mem_support_finSuccEquiv`

English:
theorem mem_support_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} {x}
  proof: by
  simpa using congr(x in $(support_finSuccEquiv f))

中文:
定理 mem_support_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} {x}
  证明: by
  simpa using congr(x in $(support_finSuccEquiv f))

Depends on / 依赖: support_finSuccEquiv
-/
theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x in (finSuccEquiv R n f).support ↔ x in (fun m : Fin (n + 1) ->₀ _ => m 0) '' f.support := by
  simpa using congr(x in $(support_finSuccEquiv f))

/--
theorem `image_support_finSuccEquiv` / 定理 `image_support_finSuccEquiv`

English:
theorem image_support_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} {i : Nat}
  proof: by
  ext m
  rw [Finset.mem_filter]; rw [Finset.mem_image]; rw [mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff]; rw [finSuccEquiv_coeff_coeff]; rw [Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2]; rw [cons_tail]
    simp [h.1]

中文:
定理 image_support_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} {i : 自然数}
  证明: by
  ext m
  rw [Finset.mem_filter]; rw [Finset.mem_image]; rw [mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff]; rw [finSuccEquiv_coeff_coeff]; rw [Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2]; rw [cons_tail]
    simp [h.1]

Depends on / 依赖: Finset, Finset.mem_filter, Finset.mem_image, cons_tail, cons_zero, conv_lhs, finSuccEquiv_coeff_coeff, mem_filter, mem_image, mem_support_iff
-/
theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} :
    ((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m in f.support | m 0 = i} := by
  ext m
  rw [Finset.mem_filter]; rw [Finset.mem_image]; rw [mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff]; rw [finSuccEquiv_coeff_coeff]; rw [Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2]; rw [cons_tail]
    simp [h.1]

/--
lemma `mem_image_support_coeff_finSuccEquiv` / 引理 `mem_image_support_coeff_finSuccEquiv`

English:
lemma mem_image_support_coeff_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {x}
  proof: by
  simpa using congr(x in $image_support_finSuccEquiv)

中文:
引理 mem_image_support_coeff_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} {i : 自然数} {x}
  证明: by
  simpa using congr(x in $image_support_finSuccEquiv)

Depends on / 依赖: image_support_finSuccEquiv
-/
lemma mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : Nat} {x} :
    x in Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔
      x in f.support ∧ x 0 = i := by
  simpa using congr(x in $image_support_finSuccEquiv)

-- TODO: generalize `finSuccEquiv R n` to an arbitrary ZeroHom
/--
theorem `nonempty_support_finSuccEquiv` / 定理 `nonempty_support_finSuccEquiv`

English:
theorem nonempty_support_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0)
  proof: by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

中文:
定理 nonempty_support_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} (h : f != 0)
  证明: by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_zero_iff, Polynomial, Polynomial.support_nonempty, map_ne_zero_iff, support_nonempty
-/
theorem nonempty_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

/--
theorem `degree_finSuccEquiv` / 定理 `degree_finSuccEquiv`

English:
theorem degree_finSuccEquiv
  given: {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0)
  proof: by
  -- TODO: these should be lemmas
  have h₀ : forall {α β : Type _} (f : α -> β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : forall {α β : Type _} (f : α -> β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup]; rw [support_finSuccEquiv]; rw [Finset.sup_image]; rw [h₀]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_finSuccEquiv h)]; rw [Finset.max_eq_sup_coe]; rw [h₁]

中文:
定理 degree_finSuccEquiv
  条件: {f : 多元多项式 (有限集 (n + 1)) R} (h : f != 0)
  证明: by
  -- TODO: these should be lemmas
  have h₀ : forall {α β : Type _} (f : α -> β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : forall {α β : Type _} (f : α -> β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup]; rw [support_finSuccEquiv]; rw [Finset.sup_image]; rw [h₀]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_finSuccEquiv h)]; rw [Finset.max_eq_sup_coe]; rw [h₁]
-/
theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f != 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : forall {α β : Type _} (f : α -> β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : forall {α β : Type _} (f : α -> β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup]; rw [support_finSuccEquiv]; rw [Finset.sup_image]; rw [h₀]
  rw [Polynomial.degree]; rw [← h']; rw [Nat.cast_withBot]; rw [Finset.coe_sup_of_nonempty (nonempty_support_finSuccEquiv h)]; rw [Finset.max_eq_sup_coe]; rw [h₁]

/--
theorem `natDegree_finSuccEquiv` / 定理 `natDegree_finSuccEquiv`

English:
theorem natDegree_finSuccEquiv
  given: (f : MvPolynomial (Fin (n + 1)) R)
  proof: by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

中文:
定理 natDegree_finSuccEquiv
  条件: (f : 多元多项式 (有限集 (n + 1)) R)
  证明: by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

Depends on / 依赖: Nat.cast_withBot, Polynomial, Polynomial.natDegree, Polynomial.natDegree_zero, WithBot, WithBot.unbotD_coe, cast_withBot, degreeOf_zero, degree_finSuccEquiv, map_zero, natDegree, natDegree_zero, unbotD_coe
-/
theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquiv c, Nat.cast_withBot, WithBot.unbotD_coe]

/--
lemma `degreeOf_eq_natDegree` / 引理 `degreeOf_eq_natDegree`

English:
lemma degreeOf_eq_natDegree
  given: [DecidableEq σ] (a : σ) (p : MvPolynomial σ R)
  proof: by
  rw [natDegree_optionEquivLeft]; rw [eq_comm]
  convert! degreeOf_rename_of_injective (Equiv.injective (Equiv.optionSubtypeNe a).symm) a
  rw [Equiv.optionSubtypeNe_symm_apply]; rw [dif_pos rfl]

中文:
引理 degreeOf_eq_natDegree
  条件: [DecidableEq σ] (a : σ) (p : 多元多项式 σ R)
  证明: by
  rw [natDegree_optionEquivLeft]; rw [eq_comm]
  convert! degreeOf_rename_of_injective (Equiv.injective (Equiv.optionSubtypeNe a).symm) a
  rw [Equiv.optionSubtypeNe_symm_apply]; rw [dif_pos rfl]

Depends on / 依赖: Equiv.injective, Equiv.optionSubtypeNe, Equiv.optionSubtypeNe_symm_apply, convert, degreeOf_rename_of_injective, dif_pos, eq_comm, injective, natDegree_optionEquivLeft, optionSubtypeNe, optionSubtypeNe_symm_apply
-/
lemma degreeOf_eq_natDegree [DecidableEq σ] (a : σ) (p : MvPolynomial σ R) :
    degreeOf a p =
      (optionEquivLeft R {b // b != a} (rename (Equiv.optionSubtypeNe a).symm p)).natDegree := by
  rw [natDegree_optionEquivLeft]; rw [eq_comm]
  convert! degreeOf_rename_of_injective (Equiv.injective (Equiv.optionSubtypeNe a).symm) a
  rw [Equiv.optionSubtypeNe_symm_apply]; rw [dif_pos rfl]

/--
theorem `degreeOf_coeff_finSuccEquiv` / 定理 `degreeOf_coeff_finSuccEquiv`

English:
theorem degreeOf_coeff_finSuccEquiv
  given: (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : Nat)
  proof: by
  rw [degreeOf_eq_sup]; rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) ->₀ Nat) => g (Fin.succ j))
    (mem_support_coeff_finSuccEquiv.1 hm)

中文:
定理 degreeOf_coeff_finSuccEquiv
  条件: (p : 多元多项式 (有限集 (n + 1)) R) (j : 有限集 n) (i : 自然数)
  证明: by
  rw [degreeOf_eq_sup]; rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) ->₀ Nat) => g (Fin.succ j))
    (mem_support_coeff_finSuccEquiv.1 hm)

Depends on / 依赖: Fin.succ, Finset, Finset.le_sup, Finset.sup_le_iff, Finsupp, Finsupp.cons_succ, Nat.succ, cons_succ, degreeOf_eq_sup, le_sup, mem_support_coeff_finSuccEquiv, sup_le_iff
-/
theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : Nat) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) <= degreeOf j.succ p := by
  rw [degreeOf_eq_sup]; rw [degreeOf_eq_sup]; rw [Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) ->₀ Nat) => g (Fin.succ j))
    (mem_support_coeff_finSuccEquiv.1 hm)

/--
lemma `finSuccEquiv_rename_finSuccEquiv` / 引理 `finSuccEquiv_rename_finSuccEquiv`

English:
lemma finSuccEquiv_rename_finSuccEquiv
  given: (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R)
  proof: by
  suffices (finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [finSuccEquiv_apply, optionEquivLeft_apply]

中文:
引理 finSuccEquiv_rename_finSuccEquiv
  条件: (e : σ ≃ 有限集 n) (φ : 多元多项式 (选项类型 σ) R)
  证明: by
  suffices (finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [finSuccEquiv_apply, optionEquivLeft_apply]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Equiv.optionCongr, Polynomial, Polynomial.algebraMap_apply, Polynomial.mapRingHom, _root_, _root_.finSuccEquiv, algebraMap_apply, algebraMap_eq, congr_fun, finSuccEquiv, finSuccEquiv_apply, mapRingHom, optionCongr, optionEquivLeft, optionEquivLeft_apply, ringHom_ext, toRingEquiv, toRingEquiv.toRingHom.comp
-/
lemma finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  suffices (finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [finSuccEquiv_apply, optionEquivLeft_apply]

end

@[simp]
/--
theorem `rename_polynomial_aeval_X` / 定理 `rename_polynomial_aeval_X`

English:
theorem rename_polynomial_aeval_X
  given: {σ τ : Type*} (f : σ -> τ) (i : σ) (p : R[X])
  proof: by
  rw [← aeval_algHom_apply]; rw [rename_X]

中文:
定理 rename_polynomial_aeval_X
  条件: {σ τ : 类型} (f : σ -> τ) (i : σ) (p : R[X])
  证明: by
  rw [← aeval_algHom_apply]; rw [rename_X]

Depends on / 依赖: aeval_algHom_apply, rename_X
-/
theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ -> τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  rw [← aeval_algHom_apply]; rw [rename_X]

end Equiv

end MvPolynomial

section toMvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/--
Definition of `Polynomial.toMvPolynomial` / `Polynomial.toMvPolynomial` 的定义

English:
definition Polynomial.toMvPolynomial
  signature: (i : σ)
  body: aeval (MvPolynomial.X i)

@[simp]

中文:
定义 多项式.toMvPolynomial
  签名: (i : σ)
  定义体: aeval (MvPolynomial.X i)

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.X
-/
noncomputable def Polynomial.toMvPolynomial (i : σ) : R[X] ->ₐ[R] MvPolynomial σ R :=
  aeval (MvPolynomial.X i)

@[simp]
/--
lemma `Polynomial.toMvPolynomial_C` / 引理 `Polynomial.toMvPolynomial_C`

English:
lemma Polynomial.toMvPolynomial_C
  given: (i : σ) (r : R)
  statement: (C r).toMvPolynomial i = MvPolynomial.C r
  proof: by
  simp [toMvPolynomial]

@[simp]

中文:
引理 多项式.toMvPolynomial_C
  条件: (i : σ) (r : R)
  结论: (C r).toMvPolynomial i = 多元多项式.C r
  证明: by
  simp [toMvPolynomial]

@[simp]

Depends on / 依赖: toMvPolynomial
-/
lemma Polynomial.toMvPolynomial_C (i : σ) (r : R) : (C r).toMvPolynomial i = MvPolynomial.C r := by
  simp [toMvPolynomial]

@[simp]
/--
lemma `Polynomial.toMvPolynomial_X` / 引理 `Polynomial.toMvPolynomial_X`

English:
lemma Polynomial.toMvPolynomial_X
  given: (i : σ)
  statement: X.toMvPolynomial i = MvPolynomial.X (R := R) i
  proof: by
  simp [toMvPolynomial]

中文:
引理 多项式.toMvPolynomial_X
  条件: (i : σ)
  结论: X.toMvPolynomial i = 多元多项式.X (R := R) i
  证明: by
  simp [toMvPolynomial]

Depends on / 依赖: toMvPolynomial
-/
lemma Polynomial.toMvPolynomial_X (i : σ) : X.toMvPolynomial i = MvPolynomial.X (R := R) i := by
  simp [toMvPolynomial]

/--
lemma `Polynomial.toMvPolynomial_eq_rename_comp` / 引理 `Polynomial.toMvPolynomial_eq_rename_comp`

English:
lemma Polynomial.toMvPolynomial_eq_rename_comp
  given: (i : σ)
  proof: by
  ext
  simp

中文:
引理 多项式.toMvPolynomial_eq_rename_comp
  条件: (i : σ)
  证明: by
  ext
  simp
-/
lemma Polynomial.toMvPolynomial_eq_rename_comp (i : σ) :
    toMvPolynomial (R := R) i =
      (MvPolynomial.rename (fun _ : Unit => i)).comp (MvPolynomial.uniqueAlgEquiv R Unit).symm := by
  ext
  simp

/--
lemma `Polynomial.toMvPolynomial_injective` / 引理 `Polynomial.toMvPolynomial_injective`

English:
lemma Polynomial.toMvPolynomial_injective
  given: (i : σ)
  proof: by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x => i) fun _ _ _ => rfl

中文:
引理 多项式.toMvPolynomial_injective
  条件: (i : σ)
  证明: by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x => i) fun _ _ _ => rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, EquivLike, EquivLike.injective_comp, MvPolynomial, MvPolynomial.rename_injective, coe_comp, coe_toAlgHom, injective_comp, rename_injective, toMvPolynomial_eq_rename_comp
-/
lemma Polynomial.toMvPolynomial_injective (i : σ) :
    Function.Injective (toMvPolynomial (R := R) i) := by
  simp only [toMvPolynomial_eq_rename_comp, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.injective_comp]
  exact MvPolynomial.rename_injective (fun x => i) fun _ _ _ => rfl

/--
lemma `Polynomial.toMvPolynomial_inj` / 引理 `Polynomial.toMvPolynomial_inj`

English:
lemma Polynomial.toMvPolynomial_inj
  given: {i : σ} {p q : R[X]}
  proof: ⟨fun h => Polynomial.toMvPolynomial_injective i h, fun h => by rw [h]⟩

@[simp]

中文:
引理 多项式.toMvPolynomial_inj
  条件: {i : σ} {p q : R[X]}
  证明: ⟨fun h => Polynomial.toMvPolynomial_injective i h, fun h => by rw [h]⟩

@[simp]

Depends on / 依赖: toMvPolynomial
-/
lemma Polynomial.toMvPolynomial_inj {i : σ} {p q : R[X]} :
    toMvPolynomial (R := R) i p = toMvPolynomial i q ↔ p = q :=
  ⟨fun h => Polynomial.toMvPolynomial_injective i h, fun h => by rw [h]⟩

@[simp]
/--
lemma `MvPolynomial.eval_comp_toMvPolynomial` / 引理 `MvPolynomial.eval_comp_toMvPolynomial`

English:
lemma MvPolynomial.eval_comp_toMvPolynomial
  given: (f : σ -> R) (i : σ)
  proof: by
  ext <;> simp

@[simp]

中文:
引理 多元多项式.eval_comp_toMvPolynomial
  条件: (f : σ -> R) (i : σ)
  证明: by
  ext <;> simp

@[simp]

Depends on / 依赖: Polynomial, Polynomial.evalRingHom, evalRingHom
-/
lemma MvPolynomial.eval_comp_toMvPolynomial (f : σ -> R) (i : σ) :
    (eval f).comp (toMvPolynomial (R := R) i) = Polynomial.evalRingHom (f i) := by
  ext <;> simp

@[simp]
/--
lemma `MvPolynomial.eval_toMvPolynomial` / 引理 `MvPolynomial.eval_toMvPolynomial`

English:
lemma MvPolynomial.eval_toMvPolynomial
  given: (f : σ -> R) (i : σ) (p : R[X])
  proof: DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

@[simp]

中文:
引理 多元多项式.eval_toMvPolynomial
  条件: (f : σ -> R) (i : σ) (p : R[X])
  证明: DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, eval_comp_toMvPolynomial
-/
lemma MvPolynomial.eval_toMvPolynomial (f : σ -> R) (i : σ) (p : R[X]) :
    eval f (p.toMvPolynomial i) = Polynomial.eval (f i) p :=
  DFunLike.congr_fun (eval_comp_toMvPolynomial ..) p

@[simp]
/--
lemma `MvPolynomial.aeval_comp_toMvPolynomial` / 引理 `MvPolynomial.aeval_comp_toMvPolynomial`

English:
lemma MvPolynomial.aeval_comp_toMvPolynomial
  given: (f : σ -> S) (i : σ)
  proof: by
  ext
  simp

@[simp]

中文:
引理 多元多项式.aeval_comp_toMvPolynomial
  条件: (f : σ -> S) (i : σ)
  证明: by
  ext
  simp

@[simp]

Depends on / 依赖: Polynomial, Polynomial.aeval, toMvPolynomial
-/
lemma MvPolynomial.aeval_comp_toMvPolynomial (f : σ -> S) (i : σ) :
    (aeval (R := R) f).comp (toMvPolynomial i) = Polynomial.aeval (f i) := by
  ext
  simp

@[simp]
/--
lemma `MvPolynomial.aeval_toMvPolynomial` / 引理 `MvPolynomial.aeval_toMvPolynomial`

English:
lemma MvPolynomial.aeval_toMvPolynomial
  given: (f : σ -> S) (i : σ) (p : R[X])
  proof: DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

@[simp]

中文:
引理 多元多项式.aeval_toMvPolynomial
  条件: (f : σ -> S) (i : σ) (p : R[X])
  证明: DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, aeval_comp_toMvPolynomial, congr_fun
-/
lemma MvPolynomial.aeval_toMvPolynomial (f : σ -> S) (i : σ) (p : R[X]) :
    aeval f (p.toMvPolynomial i) = Polynomial.aeval (f i) p :=
  DFunLike.congr_fun (aeval_comp_toMvPolynomial ..) p

@[simp]
/--
lemma `MvPolynomial.rename_comp_toMvPolynomial` / 引理 `MvPolynomial.rename_comp_toMvPolynomial`

English:
lemma MvPolynomial.rename_comp_toMvPolynomial
  given: (f : σ -> τ) (a : σ)
  proof: by
  ext
  simp

@[simp]

中文:
引理 多元多项式.rename_comp_toMvPolynomial
  条件: (f : σ -> τ) (a : σ)
  证明: by
  ext
  simp

@[simp]

Depends on / 依赖: Polynomial, Polynomial.toMvPolynomial, toMvPolynomial
-/
lemma MvPolynomial.rename_comp_toMvPolynomial (f : σ -> τ) (a : σ) :
    (rename (R := R) f).comp (Polynomial.toMvPolynomial a) = Polynomial.toMvPolynomial (f a) := by
  ext
  simp

@[simp]
/--
lemma `MvPolynomial.rename_toMvPolynomial` / 引理 `MvPolynomial.rename_toMvPolynomial`

English:
lemma MvPolynomial.rename_toMvPolynomial
  given: (f : σ -> τ) (a : σ) (p : R[X])
  proof: DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

中文:
引理 多元多项式.rename_toMvPolynomial
  条件: (f : σ -> τ) (a : σ) (p : R[X])
  证明: DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

Depends on / 依赖: p.toMvPolynomial, toMvPolynomial
-/
lemma MvPolynomial.rename_toMvPolynomial (f : σ -> τ) (a : σ) (p : R[X]) :
    (rename (R := R) f) (p.toMvPolynomial a) = p.toMvPolynomial (f a) :=
  DFunLike.congr_fun (rename_comp_toMvPolynomial ..) p

end toMvPolynomial
