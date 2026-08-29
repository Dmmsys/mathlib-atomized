/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra structure on group algebras

Given a group `G`, a commutative semiring `R` and an `R`-Hopf algebra `A`, this file collects
results about the `R`-Hopf algebra instance on `A[G]`, building upon results in
`Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean` about the bialgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instHopfAlgebra`: the `R`-Hopf algebra structure on `A[G]` when `G` is an
  (add) group and `A` is an `R`-Hopf algebra.
* `LaurentPolynomial.instHopfAlgebra`: the `R`-Hopf algebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-Hopf algebra. When `A = R` this corresponds to the fact that `𝔾ₘ/R`
  is a group scheme.
-/

public section

noncomputable section

open HopfAlgebra

namespace MonoidAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
variable {G : Type*} [Group G]

variable (R A G) in
set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := R)]
/--
Instance `instHopfAlgebraStruct` / 实例 `instHopfAlgebraStruct`

English:
instance instHopfAlgebraStruct
  signature: : HopfAlgebraStruct R A[G] where
  body: Finsupp.lsum R (fun g => lsingle g⁻¹ ∘ₗ antipode R) ∘ₗ (coeffLinearEquiv _).toLinearMap

中文:
实例 instHopfAlgebraStruct
  签名: : HopfAlgebraStruct R A[G] where
  定义体: Finsupp.lsum R (fun g => lsingle g⁻¹ ∘ₗ antipode R) ∘ₗ (coeffLinearEquiv _).toLinearMap

Depends on / 依赖: Finsupp, Finsupp.lsum, antipode, coeffLinearEquiv, lsingle, toLinearMap
-/
instance instHopfAlgebraStruct : HopfAlgebraStruct R A[G] where
  antipode := Finsupp.lsum R (fun g => lsingle g⁻¹ ∘ₗ antipode R) ∘ₗ (coeffLinearEquiv _).toLinearMap

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `antipode_single` / 引理 `antipode_single`

English:
lemma antipode_single
  given: (g : G) (a : A)
  statement: antipode R (single g a) = single g⁻¹ (antipode R a)
  proof: by
  simp [antipode]

中文:
引理 antipode_single
  条件: (g : G) (a : A)
  结论: antipode R (single g a) = single g⁻¹ (antipode R a)
  证明: by
  simp [antipode]

Depends on / 依赖: antipode
-/
lemma antipode_single (g : G) (a : A) : antipode R (single g a) = single g⁻¹ (antipode R a) := by
  simp [antipode]

open Coalgebra in
@[to_additive (dont_translate := R A)]
/--
Instance `instHopfAlgebra` / 实例 `instHopfAlgebra`

English:
instance instHopfAlgebra
  signature: : HopfAlgebra R A[G] where
  body: by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_antipode_mul_eq_algebraMap_counit (ℛ R b)))
  mul_antipode_lTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_mul_antipode_eq_algebraMap_counit (ℛ R b)))

中文:
实例 instHopfAlgebra
  签名: : HopfAlgebra R A[G] where
  定义体: by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_antipode_mul_eq_algebraMap_counit (ℛ R b)))
  mul_antipode_lTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_mul_antipode_eq_algebraMap_counit (ℛ R b)))

Depends on / 依赖: lsingle, mul_antipode_lTensor_comul, sum_antipode_mul_eq_algebraMap_counit, sum_mul_antipode_eq_algebraMap_counit
-/
instance instHopfAlgebra : HopfAlgebra R A[G] where
  mul_antipode_rTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_antipode_mul_eq_algebraMap_counit (ℛ R b)))
  mul_antipode_lTensor_comul := by
    ext a b : 2
    simpa [← (ℛ R b).eq] using congr(lsingle (R := R) (1 : G)
 (sum_mul_antipode_eq_algebraMap_counit (ℛ R b)))

end MonoidAlgebra

namespace LaurentPolynomial

open Finsupp

variable (R A : Type*) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/--
Instance `instHopfAlgebra` / 实例 `instHopfAlgebra`

English:
instance instHopfAlgebra
  signature: : HopfAlgebra R A[T;T⁻¹]
  body: inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A Int)

中文:
实例 instHopfAlgebra
  签名: : HopfAlgebra R A[T;T⁻¹]
  定义体: inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A Int)

Depends on / 依赖: AddMonoidAlgebra, HopfAlgebra
-/
instance instHopfAlgebra : HopfAlgebra R A[T;T⁻¹] :=
  inferInstanceAs (HopfAlgebra R <| AddMonoidAlgebra A Int)

variable {R A}

@[simp]
/--
theorem `antipode_C` / 定理 `antipode_C`

English:
theorem antipode_C
  given: (a : A)
  proof: by
  rw [← single_eq_C]; rw [AddMonoidAlgebra.antipode_single]
  simp

@[simp]

中文:
定理 antipode_C
  条件: (a : A)
  证明: by
  rw [← single_eq_C]; rw [AddMonoidAlgebra.antipode_single]
  simp

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.antipode_single, antipode_single, single_eq_C
-/
theorem antipode_C (a : A) :
    HopfAlgebra.antipode R (C a) = C (HopfAlgebra.antipode R a) := by
  rw [← single_eq_C]; rw [AddMonoidAlgebra.antipode_single]
  simp

@[simp]
/--
theorem `antipode_T` / 定理 `antipode_T`

English:
theorem antipode_T
  given: (n : Int)
  proof: by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]

中文:
定理 antipode_T
  条件: (n : 整数)
  证明: by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.antipode_single, HopfAlgebra, HopfAlgebra.antipode_one, antipode_one, antipode_single, map_one, one_mul, single_eq_C_mul_T
-/
theorem antipode_T (n : Int) :
    HopfAlgebra.antipode R (T n : A[T;T⁻¹]) = T (-n) := by
  unfold T
  rw [AddMonoidAlgebra.antipode_single]
  simp only [HopfAlgebra.antipode_one, single_eq_C_mul_T, map_one, one_mul]

@[simp]
/--
theorem `antipode_C_mul_T` / 定理 `antipode_C_mul_T`

English:
theorem antipode_C_mul_T
  given: (a : A) (n : Int)
  proof: by
  simp [← single_eq_C_mul_T]

中文:
定理 antipode_C_mul_T
  条件: (a : A) (n : 整数)
  证明: by
  simp [← single_eq_C_mul_T]

Depends on / 依赖: single_eq_C_mul_T
-/
theorem antipode_C_mul_T (a : A) (n : Int) :
    HopfAlgebra.antipode R (C a * T n) = C (HopfAlgebra.antipode R a) * T (-n) := by
  simp [← single_eq_C_mul_T]

end LaurentPolynomial
