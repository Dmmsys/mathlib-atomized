/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Hopf algebras

In this file we define `HopfAlgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toHopfAlgebra`

## Main definitions

* `HopfAlgebra R A` : the Hopf algebra structure on an `R`-bialgebra `A`.
* `HopfAlgebra.antipode` : the `R`-linear map `A →ₗ[R] A`.
* `HopfAlgebra.ofConvInverse` : construct a Hopf algebra from a two-sided convolution inverse
  of the identity.
* `HopfAlgebra.ofAlgHom` : the same for commutative `A`, with `AlgHom` hypotheses.

## Main results

* `HopfAlgebra.antipode_one` : the antipode of the unit is the unit.
* `HopfAlgebra.antipode_mul` : the antipode is an antihomomorphism: `S(ab) = S(b)S(a)`.

## TODO

* Uniqueness of Hopf algebra structure on a bialgebra (i.e. if the algebra and coalgebra structures
  agree then the antipodes must also agree).

* If `A` is commutative then `antipode` is an algebra homomorphism.

* If `A` is commutative then `antipode` is necessarily a bijection and its square is
  the identity.

(Note that all three facts have been proved for Hopf bimonoids in an arbitrary braided category,
so we could deduce the facts here from an equivalence `HopfAlgCat R ≌ Hopf (ModuleCat R)`.)

## References

* <https://en.wikipedia.org/wiki/Hopf_algebra>

* [C. Kassel, *Quantum Groups* (§III.3)][Kassel1995]


-/

public section

open Bialgebra

universe u v w

/--
Definition of `HopfAlgebraStruct` / `HopfAlgebraStruct` 的定义

English:
class HopfAlgebraStruct
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
  extends: Bialgebra R A
  axioms and operations (1):
    - antipode((R)) : A ->ₗ[R] A

中文:
类 HopfAlgebraStruct
  参数: (R : 类型u) (A : 类型v) [交换半环 R] [半环 A]
  继承: 双代数 R A
  公理与运算 (1 个):
    - antipode((R)) : A ->ₗ[R] A
-/
class HopfAlgebraStruct (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends Bialgebra R A where
  /-- The antipode of the Hopf algebra. -/
  antipode (R) : A ->ₗ[R] A

/--
Definition of `HopfAlgebra` / `HopfAlgebra` 的定义

English:
class HopfAlgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
  axioms and operations (2):
    - mul_antipode_rTensor_comul : LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
    - mul_antipode_lTensor_comul : LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

中文:
类 Hopf代数
  参数: (R : 类型u) (A : 类型v) [交换半环 R] [半环 A]
  公理与运算 (2 个):
    - mul_antipode_rTensor_comul : 线性映射.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (代数.linearMap R A) ∘ₗ counit
    - mul_antipode_lTensor_comul : 线性映射.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (代数.linearMap R A) ∘ₗ counit
-/
class HopfAlgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    HopfAlgebraStruct R A where
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_rTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.rTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit
  /-- One of the antipode axioms for a Hopf algebra. -/
  mul_antipode_lTensor_comul :
    LinearMap.mul' R A ∘ₗ antipode.lTensor A ∘ₗ comul = (Algebra.linearMap R A) ∘ₗ counit

namespace HopfAlgebra

export HopfAlgebraStruct (antipode)

variable {R : Type u} {A : Type v} {ι : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {a : A}

@[simp]
/--
theorem `mul_antipode_rTensor_comul_apply` / 定理 `mul_antipode_rTensor_comul_apply`

English:
theorem mul_antipode_rTensor_comul_apply
  given: (a : A)
  proof: LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]

中文:
定理 mul_antipode_rTensor_comul_apply
  条件: (a : A)
  证明: LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, mul_antipode_rTensor_comul
-/
theorem mul_antipode_rTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_rTensor_comul a

@[simp]
/--
theorem `mul_antipode_lTensor_comul_apply` / 定理 `mul_antipode_lTensor_comul_apply`

English:
theorem mul_antipode_lTensor_comul_apply
  given: (a : A)
  proof: LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]

中文:
定理 mul_antipode_lTensor_comul_apply
  条件: (a : A)
  证明: LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, mul_antipode_lTensor_comul
-/
theorem mul_antipode_lTensor_comul_apply (a : A) :
    LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a)) =
    algebraMap R A (Coalgebra.counit a) :=
  LinearMap.congr_fun mul_antipode_lTensor_comul a

@[simp]
/--
theorem `antipode_one` / 定理 `antipode_one`

English:
theorem antipode_one
  proof: by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

中文:
定理 antipode_one
  证明: by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, mul_antipode_rTensor_comul_apply, one_def
-/
theorem antipode_one :
    HopfAlgebra.antipode R (1 : A) = 1 := by
  simpa [Algebra.TensorProduct.one_def] using mul_antipode_rTensor_comul_apply (R := R) (1 : A)

open Coalgebra

/--
lemma `sum_antipode_mul_eq_algebraMap_counit` / 引理 `sum_antipode_mul_eq_algebraMap_counit`

English:
lemma sum_antipode_mul_eq_algebraMap_counit
  given: (repr : Repr R a ι)
  proof: by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

中文:
引理 sum_antipode_mul_eq_algebraMap_counit
  条件: (repr : Repr R a ι)
  证明: by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

Depends on / 依赖: map_sum, mul_antipode_rTensor_comul, repr.eq
-/
lemma sum_antipode_mul_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i in repr.index, antipode R (repr.left i) * repr.right i =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_rTensor_comul (R := R)) a)

/--
lemma `sum_mul_antipode_eq_algebraMap_counit` / 引理 `sum_mul_antipode_eq_algebraMap_counit`

English:
lemma sum_mul_antipode_eq_algebraMap_counit
  given: (repr : Repr R a ι)
  proof: by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

中文:
引理 sum_mul_antipode_eq_algebraMap_counit
  条件: (repr : Repr R a ι)
  证明: by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

Depends on / 依赖: map_sum, mul_antipode_lTensor_comul, repr.eq
-/
lemma sum_mul_antipode_eq_algebraMap_counit (repr : Repr R a ι) :
    ∑ i in repr.index, repr.left i * antipode R (repr.right i) =
      algebraMap R A (counit a) := by
  simpa [← repr.eq, map_sum] using congr($(mul_antipode_lTensor_comul (R := R)) a)

/--
lemma `sum_antipode_mul_eq_smul` / 引理 `sum_antipode_mul_eq_smul`

English:
lemma sum_antipode_mul_eq_smul
  given: (repr : Repr R a ι)
  proof: by
  rw [sum_antipode_mul_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

中文:
引理 sum_antipode_mul_eq_smul
  条件: (repr : Repr R a ι)
  证明: by
  rw [sum_antipode_mul_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_one, smul_def, sum_antipode_mul_eq_algebraMap_counit
-/
lemma sum_antipode_mul_eq_smul (repr : Repr R a ι) :
    ∑ i in repr.index, antipode R (repr.left i) * repr.right i =
      counit (R := R) a • 1 := by
  rw [sum_antipode_mul_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

/--
lemma `sum_mul_antipode_eq_smul` / 引理 `sum_mul_antipode_eq_smul`

English:
lemma sum_mul_antipode_eq_smul
  given: (repr : Repr R a ι)
  proof: by
  rw [sum_mul_antipode_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

中文:
引理 sum_mul_antipode_eq_smul
  条件: (repr : Repr R a ι)
  证明: by
  rw [sum_mul_antipode_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_one, smul_def, sum_mul_antipode_eq_algebraMap_counit
-/
lemma sum_mul_antipode_eq_smul (repr : Repr R a ι) :
    ∑ i in repr.index, repr.left i * antipode R (repr.right i) =
      counit (R := R) a • 1 := by
  rw [sum_mul_antipode_eq_algebraMap_counit]; rw [Algebra.smul_def]; rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `counit_antipode` / 引理 `counit_antipode`

English:
lemma counit_antipode
  given: (a : A)
  statement: counit (R := R) (antipode R a) = counit a
  proof: by
  calc
        counit (antipode R a)
    _ = counit (∑ i in (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq

中文:
引理 counit_antipode
  条件: (a : A)
  结论: counit (R := R) (antipode R a) = counit a
  证明: by
  calc
        counit (antipode R a)
    _ = counit (∑ i in (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq
-/
@[simp] lemma counit_antipode (a : A) : counit (R := R) (antipode R a) = counit a := by
  calc
        counit (antipode R a)
    _ = counit (∑ i in (ℛ R a).index, (ℛ R a).left i * antipode R ((ℛ R a).right i)) := by
      simp_rw [map_sum, counit_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_counit_smul]
    _ = counit a := by simpa using congr(counit (R := R) $(sum_mul_antipode_eq_smul (ℛ R a)))

/--
lemma `counit_comp_antipode` / 引理 `counit_comp_antipode`

English:
lemma counit_comp_antipode
  statement: counit ∘ₗ antipode R = counit (A := A)
  proof: by
  ext; exact counit_antipode _

中文:
引理 counit_comp_antipode
  结论: counit ∘ₗ antipode R = counit (A := A)
  证明: by
  ext; exact counit_antipode _
-/
@[simp] lemma counit_comp_antipode : counit ∘ₗ antipode R = counit (A := A) := by
  ext; exact counit_antipode _

end HopfAlgebra

namespace CommSemiring

variable (R : Type u) [CommSemiring R]

open HopfAlgebra

/--
Instance `toHopfAlgebra` / 实例 `toHopfAlgebra`

English:
instance toHopfAlgebra
  signature: : HopfAlgebra R R where
  body: .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]

中文:
实例 toHopfAlgebra
  签名: : Hopf代数 R R where
  定义体: .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
-/
instance toHopfAlgebra : HopfAlgebra R R where
  antipode := .id
  mul_antipode_rTensor_comul := by ext; simp
  mul_antipode_lTensor_comul := by ext; simp

@[simp]
/--
theorem `antipode_eq_id` / 定理 `antipode_eq_id`

English:
theorem antipode_eq_id
  statement: antipode R (A := R) = .id
  proof: rfl

中文:
定理 antipode_eq_id
  结论: antipode R (A := R) = .id
  证明: rfl
-/
theorem antipode_eq_id : antipode R (A := R) = .id := rfl

end CommSemiring

namespace HopfAlgebra

variable {R A : Type*}

open Coalgebra WithConv LinearMap

/--
Definition of `ofConvInverse` / `ofConvInverse` 的定义

English:
abbreviation ofConvInverse
  signature: [CommSemiring R] [Semiring A] [Bialgebra R A]
  body: antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

中文:
缩写 ofConvInverse
  签名: [交换半环 R] [半环 A] [双代数 R A]
  定义体: antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

Depends on / 依赖: antipode
-/
noncomputable abbrev ofConvInverse [CommSemiring R] [Semiring A] [Bialgebra R A]
    (antipode : A ->ₗ[R] A)
    (antipode_convMul_id : toConv antipode * toConv LinearMap.id = 1)
    (id_convMul_antipode : toConv LinearMap.id * toConv antipode = 1) :
    HopfAlgebra R A where
  antipode := antipode
  mul_antipode_rTensor_comul := by simpa using! congr(($antipode_convMul_id).ofConv)
  mul_antipode_lTensor_comul := by simpa using! congr(($id_convMul_antipode).ofConv)

/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
abbreviation ofAlgHom
  signature: [CommSemiring R] [CommSemiring A] [Bialgebra R A]
  body: ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_co

中文:
缩写 ofAlgHom
  签名: [交换半环 R] [交换半环 A] [双代数 R A]
  定义体: ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_co

Depends on / 依赖: Algebra, Algebra.TensorProduct.lmul, TensorProduct, WithConv, WithConv.ext, _comp_map, antipode, antipode.toLinearMap, mul_antipode_lTensor_comul, mul_antipode_rTensor_comul, ofConvInverse, toLinearMap
-/
noncomputable abbrev ofAlgHom [CommSemiring R] [CommSemiring A] [Bialgebra R A]
    (antipode : A ->ₐ[R] A)
    (mul_antipode_rTensor_comul :
      ((Algebra.TensorProduct.lift antipode (.id R A) fun _ => Commute.all _).comp
        (Bialgebra.comulAlgHom R A)) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A))
    (mul_antipode_lTensor_comul :
      (Algebra.TensorProduct.lift (.id R A) antipode fun _ _ => Commute.all _ _).comp
        (Bialgebra.comulAlgHom R A) = (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R A)) :
    HopfAlgebra R A :=
  ofConvInverse antipode.toLinearMap
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_rTensor_comul).toLinearMap))
    (WithConv.ext <| by
      simpa [← Algebra.TensorProduct.lmul'_comp_map]
        using! congr(($mul_antipode_lTensor_comul).toLinearMap))

end HopfAlgebra
