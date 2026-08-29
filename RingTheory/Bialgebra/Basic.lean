/-
Copyright (c) 2024 Ali Ramsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ali Ramsey, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebras

In this file we define `Bialgebra`s.

## Main definitions

* `Bialgebra R A`: the structure of a bialgebra on the `R`-algebra `A`;
* `CommSemiring.toBialgebra`: a commutative semiring is a bialgebra over itself.

## Implementation notes

Rather than the "obvious" axiom `∀ a b, counit (a * b) = counit a * counit b`, the far
more convoluted `mul_compr₂_counit` is used as a structure field; this says that
the corresponding two maps `A →ₗ[R] A →ₗ[R] R` are equal; a similar trick is
used for comultiplication as well. An alternative constructor `Bialgebra.mk'` is provided
with the more easily-readable axioms. The argument for using the more convoluted axioms
is that in practice there is evidence that they will be easier to prove (especially
when dealing with things like tensor products of bialgebras). This does make the definition
more surprising to mathematicians, however mathlib is no stranger to definitions which
are surprising to mathematicians -- see for example its definition of a group.
Note that this design decision is also compatible with that of `Coalgebra`. The lengthy
docstring for these convoluted fields attempts to explain what is going on.

The constructor `Bialgebra.ofAlgHom` is dual to the default constructor: For `R` is a commutative
semiring and `A` an `R`-algebra, it consumes the counit and comultiplication as algebra
homomorphisms that satisfy the coalgebra axioms to define a bialgebra structure on `A`.

## References

* <https://en.wikipedia.org/wiki/Bialgebra>

## Tags

bialgebra
-/

@[expose] public section

universe u v w

open Function
open scoped TensorProduct

/--
Definition of `Bialgebra` / `Bialgebra` 的定义

English:
class Bialgebra
  parameters: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
  axioms and operations (4):
    - counit_one : counit 1 = 1
    - mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
    - comul_one : comul 1 = 1
    - mul_compr₂_comul : (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A otimes[R] A)).compl₁₂ comul comul

中文:
类 Bialgebra
  参数: (R : 类型u) (A : 类型v) [CommSemiring R] [Semiring A]
  公理与运算 (4 个):
    - counit_one : counit 1 = 1
    - mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
    - comul_one : comul 1 = 1
    - mul_compr₂_comul : (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A otimes[R] A)).compl₁₂ comul comul
-/
class Bialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends
    Algebra R A, Coalgebra R A where
  -- The counit is an algebra morphism
  /-- The counit on a bialgebra preserves 1. -/
  counit_one : counit 1 = 1
  /-- The counit on a bialgebra preserves multiplication. Note that this is written
  in a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R]` are equal.
  The two corresponding equal linear maps `A ⊗[R] A →ₗ[R]`
  are the following: the first factors through `A` and is multiplication on `A` followed
  by `counit`. The second factors through `R ⊗[R] R`, and is `counit ⊗ counit` followed by
  multiplication on `R`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses
  the more familiar but mathematically equivalent `counit (a * b) = counit a * counit b`. -/
  mul_compr₂_counit : (LinearMap.mul R A).compr₂ counit = (LinearMap.mul R R).compl₁₂ counit counit
  -- The comultiplication is an algebra morphism
  /-- The comultiplication on a bialgebra preserves `1`. -/
  comul_one : comul 1 = 1
  /-- The comultiplication on a bialgebra preserves multiplication. This is written in
  a rather obscure way: it says that two bilinear maps `A →ₗ[R] A →ₗ[R] (A ⊗[R] A)`
  are equal. The corresponding equal linear maps `A ⊗[R] A →ₗ[R] A ⊗[R] A`
  are firstly multiplication followed by `comul`, and secondly `comul ⊗ comul` followed
  by multiplication on `A ⊗[R] A`.

  See `Bialgebra.mk'` for a constructor for bialgebras which uses the more familiar
  but mathematically equivalent `comul (a * b) = comul a * comul b`. -/
  mul_compr₂_comul :
    (LinearMap.mul R A).compr₂ comul = (LinearMap.mul R (A otimes[R] A)).compl₁₂ comul comul

namespace Bialgebra

open Coalgebra

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Semiring A] [Bialgebra R A]

/--
lemma `counit_mul` / 引理 `counit_mul`

English:
lemma counit_mul
  given: (a b : A)
  statement: counit (R := R) (a * b) = counit a * counit b
  proof: DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b

中文:
引理 counit_mul
  条件: (a b : A)
  结论: counit (R := R) (a * b) = counit a * counit b
  证明: DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b

Depends on / 依赖: counit
-/
lemma counit_mul (a b : A) : counit (R := R) (a * b) = counit a * counit b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_counit a) b

/--
lemma `comul_mul` / 引理 `comul_mul`

English:
lemma comul_mul
  given: (a b : A)
  statement: comul (R := R) (a * b) = comul a * comul b
  proof: DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b

中文:
引理 comul_mul
  条件: (a b : A)
  结论: comul (R := R) (a * b) = comul a * comul b
  证明: DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b

Depends on / 依赖: H.pos.ne
-/
lemma comul_mul (a b : A) : comul (R := R) (a * b) = comul a * comul b :=
  DFunLike.congr_fun (DFunLike.congr_fun mul_compr₂_comul a) b

attribute [simp] counit_one comul_one counit_mul comul_mul

/-- If `R` is a field (or even a commutative semiring) and `A`
is an `R`-algebra with a coalgebra structure, then `Bialgebra.mk'`
consumes proofs that the counit and comultiplication preserve
the identity and multiplication, and produces a bialgebra
structure on `A`. -/
@[instance_reducible]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
  body: counit_one
  mul_compr₂_counit := by ext; exact counit_mul
  comul_one := comul_one
  mul_compr₂_comul := by ext; exact comul_mul

中文:
定义 mk'
  签名: (R : 类型u) (A : 类型v) [CommSemiring R] [Semiring A]
  定义体: counit_one
  mul_compr₂_counit := by ext; exact counit_mul
  comul_one := comul_one
  mul_compr₂_comul := by ext; exact comul_mul

Depends on / 依赖: counit_one
-/
def mk' (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Algebra R A] [C : Coalgebra R A] (counit_one : C.counit 1 = 1)
    (counit_mul : forall {a b}, C.counit (a * b) = C.counit a * C.counit b)
    (comul_one : C.comul 1 = 1)
    (comul_mul : forall {a b}, C.comul (a * b) = C.comul a * C.comul b) :
    Bialgebra R A where
  counit_one := counit_one
  mul_compr₂_counit := by ext; exact counit_mul
  comul_one := comul_one
  mul_compr₂_comul := by ext; exact comul_mul

variable (R A)

/-- `counitAlgHom R A` is the counit of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
/--
Definition of `counitAlgHom` / `counitAlgHom` 的定义

English:
definition counitAlgHom
  signature: : A ->ₐ[R] R
  body: .ofLinearMap counit counit_one counit_mul

中文:
定义 counitAlgHom
  签名: : A ->ₐ[R] R
  定义体: .ofLinearMap counit counit_one counit_mul

Depends on / 依赖: counit, counit_mul, counit_one, ofLinearMap
-/
def counitAlgHom : A ->ₐ[R] R :=
  .ofLinearMap counit counit_one counit_mul

/-- `comulAlgHom R A` is the comultiplication of the `R`-bialgebra `A`, as an `R`-algebra map. -/
@[simps!]
/--
Definition of `comulAlgHom` / `comulAlgHom` 的定义

English:
definition comulAlgHom
  signature: : A ->ₐ[R] A otimes[R] A
  body: .ofLinearMap comul comul_one comul_mul

中文:
定义 comulAlgHom
  签名: : A ->ₐ[R] A otimes[R] A
  定义体: .ofLinearMap comul comul_one comul_mul

Depends on / 依赖: comul_mul, comul_one, ofLinearMap
-/
def comulAlgHom : A ->ₐ[R] A otimes[R] A :=
  .ofLinearMap comul comul_one comul_mul

variable {R A}

/--
lemma `toLinearMap_counitAlgHom` / 引理 `toLinearMap_counitAlgHom`

English:
lemma toLinearMap_counitAlgHom
  statement: (counitAlgHom R A).toLinearMap = counit
  proof: rfl

中文:
引理 toLinearMap_counitAlgHom
  结论: (counitAlgHom R A).toLinearMap = counit
  证明: rfl
-/
@[simp] lemma toLinearMap_counitAlgHom : (counitAlgHom R A).toLinearMap = counit := rfl
/--
lemma `toLinearMap_comulAlgHom` / 引理 `toLinearMap_comulAlgHom`

English:
lemma toLinearMap_comulAlgHom
  statement: (comulAlgHom R A).toLinearMap = comul
  proof: rfl

中文:
引理 toLinearMap_comulAlgHom
  结论: (comulAlgHom R A).toLinearMap = comul
  证明: rfl
-/
@[simp] lemma toLinearMap_comulAlgHom : (comulAlgHom R A).toLinearMap = comul := rfl

/--
lemma `counit_algebraMap` / 引理 `counit_algebraMap`

English:
lemma counit_algebraMap
  given: (r : R)
  statement: counit (R := R) (algebraMap R A r) = r
  proof: (counitAlgHom R A).commutes r

中文:
引理 counit_algebraMap
  条件: (r : R)
  结论: counit (R := R) (algebraMap R A r) = r
  证明: (counitAlgHom R A).commutes r
-/
@[simp] lemma counit_algebraMap (r : R) : counit (R := R) (algebraMap R A r) = r :=
  (counitAlgHom R A).commutes r

/--
lemma `comul_algebraMap` / 引理 `comul_algebraMap`

English:
lemma comul_algebraMap
  given: (r : R)
  proof: (comulAlgHom R A).commutes r

中文:
引理 comul_algebraMap
  条件: (r : R)
  证明: (comulAlgHom R A).commutes r
-/
@[simp] lemma comul_algebraMap (r : R) :
    comul (R := R) (algebraMap R A r) = algebraMap R (A otimes[R] A) r :=
  (comulAlgHom R A).commutes r

/--
lemma `counit_natCast` / 引理 `counit_natCast`

English:
lemma counit_natCast
  given: (n : Nat)
  statement: counit (R := R) (n : A) = n
  proof: map_natCast (counitAlgHom R A) _

中文:
引理 counit_natCast
  条件: (n : 自然数)
  结论: counit (R := R) (n : A) = n
  证明: map_natCast (counitAlgHom R A) _
-/
@[simp] lemma counit_natCast (n : Nat) : counit (R := R) (n : A) = n :=
  map_natCast (counitAlgHom R A) _

/--
lemma `comul_natCast` / 引理 `comul_natCast`

English:
lemma comul_natCast
  given: (n : Nat)
  statement: comul (R := R) (n : A) = n
  proof: map_natCast (comulAlgHom R A) _

中文:
引理 comul_natCast
  条件: (n : 自然数)
  结论: comul (R := R) (n : A) = n
  证明: map_natCast (comulAlgHom R A) _
-/
@[simp] lemma comul_natCast (n : Nat) : comul (R := R) (n : A) = n :=
  map_natCast (comulAlgHom R A) _

/--
lemma `counit_pow` / 引理 `counit_pow`

English:
lemma counit_pow
  given: (a : A) (n : Nat)
  statement: counit (R := R) (a ^ n) = counit a ^ n
  proof: map_pow (counitAlgHom R A) a n

中文:
引理 counit_pow
  条件: (a : A) (n : 自然数)
  结论: counit (R := R) (a ^ n) = counit a ^ n
  证明: map_pow (counitAlgHom R A) a n
-/
@[simp] lemma counit_pow (a : A) (n : Nat) : counit (R := R) (a ^ n) = counit a ^ n :=
  map_pow (counitAlgHom R A) a n

/--
lemma `comul_pow` / 引理 `comul_pow`

English:
lemma comul_pow
  given: (a : A) (n : Nat)
  statement: comul (R := R) (a ^ n) = comul a ^ n
  proof: map_pow (comulAlgHom R A) a n

中文:
引理 comul_pow
  条件: (a : A) (n : 自然数)
  结论: comul (R := R) (a ^ n) = comul a ^ n
  证明: map_pow (comulAlgHom R A) a n
-/
@[simp] lemma comul_pow (a : A) (n : Nat) : comul (R := R) (a ^ n) = comul a ^ n :=
  map_pow (comulAlgHom R A) a n

end Bialgebra

namespace CommSemiring
variable (R : Type u) [CommSemiring R]

open Bialgebra

/--
Instance `toBialgebra` / 实例 `toBialgebra`

English:
instance toBialgebra
  signature: : Bialgebra R R where
  body: by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

中文:
实例 toBialgebra
  签名: : Bialgebra R R where
  定义体: by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

Depends on / 依赖: comul_one, counit_one
-/
instance toBialgebra : Bialgebra R R where
  mul_compr₂_counit := by ext; simp
  counit_one := rfl
  mul_compr₂_comul := by ext; simp
  comul_one := rfl

end CommSemiring

namespace Bialgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/--
lemma `counitAlgHom_self` / 引理 `counitAlgHom_self`

English:
lemma counitAlgHom_self
  statement: counitAlgHom R R = .id R R
  proof: rfl

中文:
引理 counitAlgHom_self
  结论: counitAlgHom R R = .id R R
  证明: rfl
-/
@[simp] lemma counitAlgHom_self : counitAlgHom R R = .id R R := rfl

/--
Definition of `ofAlgHom` / `ofAlgHom` 的定义

English:
abbreviation ofAlgHom
  signature: (comul : A ->ₐ[R] (A otimes[R] A)) (counit : A ->ₐ[R] R)
  body: letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map

中文:
缩写 ofAlgHom
  签名: (comul : A ->ₐ[R] (A otimes[R] A)) (counit : A ->ₐ[R] R)
  定义体: letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map

Depends on / 依赖: Coalgebra, coassoc, counit, h_coassoc, h_lTensor, h_rTensor, lTensor_counit_comp_comul, map_mul, map_one, rTensor_counit_comp_comul, toLinearMap
-/
abbrev ofAlgHom (comul : A ->ₐ[R] (A otimes[R] A)) (counit : A ->ₐ[R] R)
    (h_coassoc : (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (.id R A)).comp comul)
      = (Algebra.TensorProduct.map (.id R A) comul).comp comul)
    (h_rTensor : (Algebra.TensorProduct.map counit (.id R A)).comp comul
      = (Algebra.TensorProduct.lid R A).symm)
    (h_lTensor : (Algebra.TensorProduct.map (.id R A) counit).comp comul
      = (Algebra.TensorProduct.rid R R A).symm) :
    Bialgebra R A :=
  letI : Coalgebra R A := {
    comul := comul
    counit := counit
    coassoc := congr(($h_coassoc).toLinearMap)
    rTensor_counit_comp_comul := congr(($h_rTensor).toLinearMap)
    lTensor_counit_comp_comul := congr(($h_lTensor).toLinearMap)
  }
  .mk' _ _ (map_one counit) (map_mul counit _ _) (map_one comul) (map_mul comul _ _)

end Bialgebra

namespace Bialgebra
variable {R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

variable (A) in
/--
lemma `algebraMap_injective` / 引理 `algebraMap_injective`

English:
lemma algebraMap_injective
  statement: Injective (algebraMap R A)
  proof: RightInverse.injective counit_algebraMap

中文:
引理 algebraMap_injective
  结论: Injective (algebraMap R A)
  证明: RightInverse.injective counit_algebraMap

Depends on / 依赖: RightInverse, RightInverse.injective, counit_algebraMap, injective
-/
lemma algebraMap_injective : Injective (algebraMap R A) := RightInverse.injective counit_algebraMap

/--
lemma `counit_surjective` / 引理 `counit_surjective`

English:
lemma counit_surjective
  statement: Surjective (Coalgebra.counit : A ->ₗ[R] R)
  proof: RightInverse.surjective counit_algebraMap

include R in

中文:
引理 counit_surjective
  结论: Surjective (Coalgebra.counit : A ->ₗ[R] R)
  证明: RightInverse.surjective counit_algebraMap

include R in

Depends on / 依赖: RightInverse, RightInverse.surjective, counit_algebraMap, surjective
-/
lemma counit_surjective : Surjective (Coalgebra.counit : A ->ₗ[R] R) :=
  RightInverse.surjective counit_algebraMap

include R in
variable (R) in
/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  given: [Nontrivial R]
  statement: Nontrivial A
  proof: (algebraMap_injective (R := R) _).nontrivial

中文:
引理 nontrivial
  条件: [Nontrivial R]
  结论: Nontrivial A
  证明: (algebraMap_injective (R := R) _).nontrivial

Depends on / 依赖: algebraMap_injective, nontrivial
-/
lemma nontrivial [Nontrivial R] : Nontrivial A := (algebraMap_injective (R := R) _).nontrivial

end Bialgebra
