/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# The coalgebra structure on monoid algebras

Given a type `X`, a commutative semiring `R` and a semiring `A` which is also an `R`-coalgebra,
this file collects results about the `R`-coalgebra instance on `A[X]` inherited from the
corresponding structure on its coefficients, defined in `Mathlib/RingTheory/Coalgebra/Basic.lean`.

## Main definitions

* `(Add)MonoidAlgebra.instCoalgebra`: the `R`-coalgebra structure on `A[X]` when `A` is an
  `R`-coalgebra.
* `LaurentPolynomial.instCoalgebra`: the `R`-coalgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-coalgebra.
-/

public section

noncomputable section

open Coalgebra

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
  {X : Type*} [Module R A] [Coalgebra R A]

variable (R A X) in
@[to_additive]
/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R A[X]
  body: coeffEquiv.coalgebra _

@[to_additive]

中文:
实例 instCoalgebra
  签名: : Coalgebra R A[X]
  定义体: coeffEquiv.coalgebra _

@[to_additive]

Depends on / 依赖: coalgebra, coeffEquiv, coeffEquiv.coalgebra
-/
instance instCoalgebra : Coalgebra R A[X] := coeffEquiv.coalgebra _

@[to_additive]
/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: [IsCocomm R A]
  body: coeffEquiv.coalgebraIsCocomm _

@[to_additive (attr := simp)]

中文:
实例 instIsCocomm
  签名: [IsCocomm R A]
  定义体: coeffEquiv.coalgebraIsCocomm _

@[to_additive (attr := simp)]

Depends on / 依赖: coalgebraIsCocomm, coeffEquiv, coeffEquiv.coalgebraIsCocomm
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R A[X] := coeffEquiv.coalgebraIsCocomm _

@[to_additive (attr := simp)]
/--
lemma `counit_single` / 引理 `counit_single`

English:
lemma counit_single
  given: (x : X) (a : A)
  proof: Finsupp.counit_single _ _ _ _ _

@[to_additive]

中文:
引理 counit_single
  条件: (x : X) (a : A)
  证明: Finsupp.counit_single _ _ _ _ _

@[to_additive]
-/
lemma counit_single (x : X) (a : A) :
    Coalgebra.counit (single x a) = Coalgebra.counit (R := R) a :=
  Finsupp.counit_single _ _ _ _ _

@[to_additive]
/--
lemma `comul_def` / 引理 `comul_def`

English:
lemma comul_def
  proof: rfl

@[to_additive (dont_translate := R) (attr := simp)]

中文:
引理 comul_def
  证明: rfl

@[to_additive (dont_translate := R) (attr := simp)]
-/
lemma comul_def :
    Coalgebra.comul (R := R) (A := A[X]) =
      TensorProduct.map (coeffLinearEquiv R).symm.toLinearMap (coeffLinearEquiv R).symm.toLinearMap
        ∘ₗ comul ∘ₗ (coeffLinearEquiv R).toLinearMap := rfl

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `comul_single` / 引理 `comul_single`

English:
lemma comul_single
  given: (x : X) (a : A)
  proof: by
  simp [comul_def, TensorProduct.map_map]; rfl

中文:
引理 comul_single
  条件: (x : X) (a : A)
  证明: by
  simp [comul_def, TensorProduct.map_map]; rfl

Depends on / 依赖: single
-/
lemma comul_single (x : X) (a : A) :
    Coalgebra.comul (R := R) (single x a) =
      TensorProduct.map (lsingle x) (lsingle x) (Coalgebra.comul a) := by
  simp [comul_def, TensorProduct.map_map]; rfl

end MonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Module R A] [Coalgebra R A]

/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra R A[T;T⁻¹]
  body: inferInstanceAs Coalgebra R A[Int]

中文:
实例 instCoalgebra
  签名: : Coalgebra R A[T;T⁻¹]
  定义体: inferInstanceAs Coalgebra R A[Int]

Depends on / 依赖: Coalgebra
-/
instance instCoalgebra : Coalgebra R A[T;T⁻¹] := inferInstanceAs Coalgebra R A[Int]

/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: [IsCocomm R A]
  body: inferInstanceAs IsCocomm R A[Int]

中文:
实例 instIsCocomm
  签名: [IsCocomm R A]
  定义体: inferInstanceAs IsCocomm R A[Int]

Depends on / 依赖: IsCocomm
-/
instance instIsCocomm [IsCocomm R A] : IsCocomm R A[T;T⁻¹] := inferInstanceAs IsCocomm R A[Int]

variable {R A}

@[simp]
/--
theorem `comul_C` / 定理 `comul_C`

English:
theorem comul_C
  given: (a : A)
  proof: comul_single _ _

@[simp]

中文:
定理 comul_C
  条件: (a : A)
  证明: comul_single _ _

@[simp]
-/
theorem comul_C (a : A) :
    Coalgebra.comul (R := R) (C a) =
      TensorProduct.map (lsingle 0) (lsingle 0) (Coalgebra.comul (R := R) a) :=
  comul_single _ _

@[simp]
/--
theorem `comul_C_mul_T` / 定理 `comul_C_mul_T`

English:
theorem comul_C_mul_T
  given: (a : A) (n : Int)
  proof: by
  simp [← single_eq_C_mul_T]

中文:
定理 comul_C_mul_T
  条件: (a : A) (n : 整数)
  证明: by
  simp [← single_eq_C_mul_T]
-/
theorem comul_C_mul_T (a : A) (n : Int) :
    Coalgebra.comul (R := R) (C a * T n) =
      TensorProduct.map (lsingle n) (lsingle n) (Coalgebra.comul (R := R) a) := by
  simp [← single_eq_C_mul_T]

/--
theorem `comul_C_mul_T_self` / 定理 `comul_C_mul_T_self`

English:
theorem comul_C_mul_T_self
  given: (a : R) (n : Int)
  proof: by
  simp

@[simp]

中文:
定理 comul_C_mul_T_self
  条件: (a : R) (n : 整数)
  证明: by
  simp

@[simp]
-/
theorem comul_C_mul_T_self (a : R) (n : Int) :
    Coalgebra.comul (C a * T n) = T n otimesₜ[R] (C a * T n) := by
  simp

@[simp]
/--
theorem `counit_C` / 定理 `counit_C`

English:
theorem counit_C
  given: (a : A)
  proof: counit_single _ _

@[simp]

中文:
定理 counit_C
  条件: (a : A)
  证明: counit_single _ _

@[simp]

Depends on / 依赖: Coalgebra, Coalgebra.counit, counit
-/
theorem counit_C (a : A) :
    Coalgebra.counit (R := R) (C a) = Coalgebra.counit (R := R) a :=
  counit_single _ _

@[simp]
/--
theorem `counit_C_mul_T` / 定理 `counit_C_mul_T`

English:
theorem counit_C_mul_T
  given: (a : A) (n : Int)
  proof: by
  simp [← single_eq_C_mul_T]

中文:
定理 counit_C_mul_T
  条件: (a : A) (n : 整数)
  证明: by
  simp [← single_eq_C_mul_T]

Depends on / 依赖: Coalgebra, Coalgebra.counit, counit, single_eq_C_mul_T
-/
theorem counit_C_mul_T (a : A) (n : Int) :
    Coalgebra.counit (R := R) (C a * T n) = Coalgebra.counit (R := R) a := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial
