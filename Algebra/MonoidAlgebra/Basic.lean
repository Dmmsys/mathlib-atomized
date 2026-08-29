/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Algebra structure on monoid algebras

-/

@[expose] public noncomputable section

open Finset

open Finsupp hiding single mapDomain

variable {R S T A B C M N O : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/


section NonUnitalNonAssocAlgebra

variable (R) [Semiring R] [Mul M] [NonUnitalNonAssocSemiring A]

/-- A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/
@[to_additive (dont_translate := R) /--
A non-unital `R`-algebra homomorphism from `R[M]` is uniquely defined by its
values on the monomials `single a 1`. -/]
/--
theorem `nonUnitalAlgHom_ext` / 定理 `nonUnitalAlgHom_ext`

English:
theorem nonUnitalAlgHom_ext
  statement: [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  proof: NonUnitalAlgHom.to_distribMulActionHom_injective
    MonoidAlgebra.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

中文:
定理 nonUnitalAlgHom_ext
  结论: [分配乘法作用 R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  证明: NonUnitalAlgHom.to_distribMulActionHom_injective
    MonoidAlgebra.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.ext_ring, MonoidAlgebra, MonoidAlgebra.distribMulActionHom_ext, NonUnitalAlgHom, NonUnitalAlgHom.to_distribMulActionHom_injective, distribMulActionHom_ext, ext_ring, to_distribMulActionHom_injective
-/
theorem nonUnitalAlgHom_ext [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
    (h : forall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
NonUnitalAlgHom.to_distribMulActionHom_injective
    MonoidAlgebra.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `nonUnitalAlgHom_ext'` / 定理 `nonUnitalAlgHom_ext'`

English:
theorem nonUnitalAlgHom_ext'
  statement: [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  proof: nonUnitalAlgHom_ext R DFunLike.congr_fun h

中文:
定理 nonUnitalAlgHom_ext'
  结论: [分配乘法作用 R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  证明: nonUnitalAlgHom_ext R DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, nonUnitalAlgHom_ext
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
nonUnitalAlgHom_ext R DFunLike.congr_fun h

set_option backward.isDefEq.respectTransparency false in
/-- The functor `M ↦ R[M]`, from the category of magmas to the category of non-unital,
non-associative algebras over `R` is adjoint to the forgetful functor in the other direction. -/
@[simps apply_apply symm_apply]
/--
Definition of `liftMagma` / `liftMagma` 的定义

English:
definition liftMagma
  signature: [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  body: {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
    

中文:
定义 liftMagma
  签名: [模 R A] [标量塔 R A A] [标量交换类 R A A]
  定义体: {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
    
-/
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (M ->ₙ* A) ≃ (R[M] ->ₙₐ[R] A) where
  toFun f := {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
        smul_mul_smul_comm] using Finsupp.sum_comm ..
  }
  invFun F := F.toMulHom.comp (ofMagma R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section Algebra
variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

set_option backward.defeqAttrib.useBackward true in
/-- The instance `Algebra R A[M]` whenever we have `Algebra R A`.

In particular this provides the instance `Algebra R R[M]`. -/
@[to_additive (dont_translate := R A)
/-- The instance `Algebra R R[M]` whenever we have `Algebra R R`.

In particular this provides the instance `Algebra R R[M]`. -/]
/--
Instance `algebra` / 实例 `algebra`

English:
instance algebra
  signature: : Algebra R A[M] where
  body: singleOneRingHom.comp (algebraMap R A)
  smul_def' r a := by ext; simp [coeff_single_one_mul, Algebra.smul_def]
  commutes' r f := by ext; simp [coeff_single_one_mul, coeff_mul_single_one, Algebra.commutes]

中文:
实例 algebra
  签名: : 代数 R A[M] where
  定义体: singleOneRingHom.comp (algebraMap R A)
  smul_def' r a := by ext; simp [coeff_single_one_mul, Algebra.smul_def]
  commutes' r f := by ext; simp [coeff_single_one_mul, coeff_mul_single_one, Algebra.commutes]

Depends on / 依赖: algebraMap, singleOneRingHom, singleOneRingHom.comp
-/
instance algebra : Algebra R A[M] where
  algebraMap := singleOneRingHom.comp (algebraMap R A)
  smul_def' r a := by ext; simp [coeff_single_one_mul, Algebra.smul_def]
  commutes' r f := by ext; simp [coeff_single_one_mul, coeff_mul_single_one, Algebra.commutes]

/-- `MonoidAlgebra.single 1` as an `AlgHom` -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- `AddMonoidAlgebra.single 0` as an `AlgHom` -/]
/--
Definition of `singleOneAlgHom` / `singleOneAlgHom` 的定义

English:
definition singleOneAlgHom
  signature: : A ->ₐ[R] A[M] where
  body: singleOneRingHom
  commutes' r := by ext; simp; rfl

@[to_additive (attr := simp)]

中文:
定义 singleOneAlgHom
  签名: : A ->ₐ[R] A[M] where
  定义体: singleOneRingHom
  commutes' r := by ext; simp; rfl

@[to_additive (attr := simp)]

Depends on / 依赖: singleOneRingHom
-/
def singleOneAlgHom : A ->ₐ[R] A[M] where
  __ := singleOneRingHom
  commutes' r := by ext; simp; rfl

@[to_additive (attr := simp)]
/--
lemma `coe_algebraMap` / 引理 `coe_algebraMap`

English:
lemma coe_algebraMap
  statement: ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A
  proof: rfl

中文:
引理 coe_algebraMap
  结论: ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A
  证明: rfl
-/
lemma coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A := rfl

/--
lemma `single_eq_algebraMap_mul_of` / 引理 `single_eq_algebraMap_mul_of`

English:
lemma single_eq_algebraMap_mul_of
  given: (m : M) (r : R)
  proof: by simp

中文:
引理 single_eq_algebraMap_mul_of
  条件: (m : M) (r : R)
  证明: by simp
-/
lemma single_eq_algebraMap_mul_of (m : M) (r : R) :
    single m r = algebraMap R R[M] r * of R M m := by simp

/--
theorem `single_algebraMap_eq_algebraMap_mul_of` / 定理 `single_algebraMap_eq_algebraMap_mul_of`

English:
theorem single_algebraMap_eq_algebraMap_mul_of
  given: (m : M) (r : R)
  proof: by simp

@[to_additive]

中文:
定理 single_algebraMap_eq_algebraMap_mul_of
  条件: (m : M) (r : R)
  证明: by simp

@[to_additive]
-/
theorem single_algebraMap_eq_algebraMap_mul_of (m : M) (r : R) :
    single m (algebraMap R A r) = algebraMap R A[M] r * of A M m := by simp

@[to_additive]
/--
Instance `isLocalHom_singleOneAlgHom` / 实例 `isLocalHom_singleOneAlgHom`

English:
instance isLocalHom_singleOneAlgHom
  signature: : IsLocalHom (singleOneAlgHom : A ->ₐ[R] A[M]) where
  body: isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := R)]

中文:
实例 isLocalHom_singleOneAlgHom
  签名: : 是Local态射 (singleOneAlgHom : A ->ₐ[R] A[M]) where
  定义体: isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := R)]

Depends on / 依赖: isLocalHom_singleOneRingHom, isLocalHom_singleOneRingHom.map_nonunit, map_nonunit
-/
instance isLocalHom_singleOneAlgHom : IsLocalHom (singleOneAlgHom : A ->ₐ[R] A[M]) where
  map_nonunit := isLocalHom_singleOneRingHom.map_nonunit

@[to_additive (dont_translate := R)]
/--
Instance `isLocalHom_algebraMap` / 实例 `isLocalHom_algebraMap`

English:
instance isLocalHom_algebraMap
  signature: [IsLocalHom (algebraMap R A)]
  body: .of_map _ _ isLocalHom_singleOneAlgHom (R := R).map_nonunit _ hx

中文:
实例 isLocalHom_algebraMap
  签名: [是Local态射 (algebraMap R A)]
  定义体: .of_map _ _ isLocalHom_singleOneAlgHom (R := R).map_nonunit _ hx

Depends on / 依赖: isLocalHom_singleOneAlgHom, map_nonunit, of_map
-/
instance isLocalHom_algebraMap [IsLocalHom (algebraMap R A)] :
    IsLocalHom (algebraMap R A[M]) where
map_nonunit _ hx := .of_map _ _ isLocalHom_singleOneAlgHom (R := R).map_nonunit _ hx

variable (R M) in
/-- The trivial monoid algebra is the base ring. -/
@[to_additive (dont_translate := R A)
/-- The trivial monoid algebra is the base ring. -/]
/--
Definition of `uniqueAlgEquiv` / `uniqueAlgEquiv` 的定义

English:
definition uniqueAlgEquiv
  signature: [Subsingleton M]
  body: uniqueRingEquiv _
  commutes' r := by simp

中文:
定义 uniqueAlgEquiv
  签名: [子单例 M]
  定义体: uniqueRingEquiv _
  commutes' r := by simp

Depends on / 依赖: uniqueRingEquiv
-/
def uniqueAlgEquiv [Subsingleton M] : A[M] ≃ₐ[R] A where
  toRingEquiv := uniqueRingEquiv _
  commutes' r := by simp

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
@[to_additive (dont_translate := A) (attr := simp)]
/--
lemma `uniqueAlgEquiv_symm_apply` / 引理 `uniqueAlgEquiv_symm_apply`

English:
lemma uniqueAlgEquiv_symm_apply
  given: [Subsingleton M] (a : A)
  proof: by ext; simp [uniqueAlgEquiv]

中文:
引理 uniqueAlgEquiv_symm_apply
  条件: [子单例 M] (a : A)
  证明: by ext; simp [uniqueAlgEquiv]

Depends on / 依赖: uniqueAlgEquiv
-/
lemma uniqueAlgEquiv_symm_apply [Subsingleton M] (a : A) :
    (uniqueAlgEquiv R M).symm a = single 1 a := by ext; simp [uniqueAlgEquiv]

-- We want this lemma to fire before `uniqueAlgEquiv_symm_apply`.
@[to_additive (dont_translate := A) (attr := simp↓ high)]
/--
lemma `coeff_uniqueAlgEquiv_symm` / 引理 `coeff_uniqueAlgEquiv_symm`

English:
lemma coeff_uniqueAlgEquiv_symm
  given: [Subsingleton M] (a : A) (m : M)
  proof: by simp [Subsingleton.elim m 1]

中文:
引理 coeff_uniqueAlgEquiv_symm
  条件: [子单例 M] (a : A) (m : M)
  证明: by simp [Subsingleton.elim m 1]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma coeff_uniqueAlgEquiv_symm [Subsingleton M] (a : A) (m : M) :
    ((uniqueAlgEquiv R M).symm a).coeff m = a := by simp [Subsingleton.elim m 1]

variable (R M) in
@[to_additive (attr := simp)]
/--
lemma `toRingEquiv_uniqueAlgEquiv` / 引理 `toRingEquiv_uniqueAlgEquiv`

English:
lemma toRingEquiv_uniqueAlgEquiv
  given: [Unique M]
  proof: rfl

中文:
引理 toRingEquiv_uniqueAlgEquiv
  条件: [唯一 M]
  证明: rfl
-/
lemma toRingEquiv_uniqueAlgEquiv [Unique M] :
    RingEquivClass.toRingEquiv (uniqueAlgEquiv R (A := A) M) =
      uniqueRingEquiv (R := A) M := rfl

variable (R M) in
@[to_additive (attr := simp)]
/--
lemma `toRingEquiv_symm_uniqueAlgEquiv` / 引理 `toRingEquiv_symm_uniqueAlgEquiv`

English:
lemma toRingEquiv_symm_uniqueAlgEquiv
  given: [Unique M]
  proof: rfl

中文:
引理 toRingEquiv_symm_uniqueAlgEquiv
  条件: [唯一 M]
  证明: rfl
-/
lemma toRingEquiv_symm_uniqueAlgEquiv [Unique M] :
    RingEquivClass.toRingEquiv (uniqueAlgEquiv R (A := A) M).symm =
      (uniqueRingEquiv (R := A) M).symm := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- A product monoid algebra is a nested monoid algebra. -/
@[to_additive (dont_translate := R A)
/-- A product monoid algebra is a nested monoid algebra. -/]
/--
Definition of `curryAlgEquiv` / `curryAlgEquiv` 的定义

English:
definition curryAlgEquiv
  signature: : A[M × N] ≃ₐ[R] A[N][M] where
  body: curryRingEquiv
  commutes' r := by
    ext
    simp [curryRingEquiv, curryAddEquiv, algebraMap, algebraMap, Algebra.algebraMap,
      singleOneRingHom, singleAddHom, curryAddEquiv, ← ofCoeff_single]

@[to_additive (attr := simp)]

中文:
定义 curryAlgEquiv
  签名: : A[M × N] ≃ₐ[R] A[N][M] where
  定义体: curryRingEquiv
  commutes' r := by
    ext
    simp [curryRingEquiv, curryAddEquiv, algebraMap, algebraMap, Algebra.algebraMap,
      singleOneRingHom, singleAddHom, curryAddEquiv, ← ofCoeff_single]

@[to_additive (attr := simp)]

Depends on / 依赖: curryRingEquiv
-/
def curryAlgEquiv : A[M × N] ≃ₐ[R] A[N][M] where
  toRingEquiv := curryRingEquiv
  commutes' r := by
    ext
    simp [curryRingEquiv, curryAddEquiv, algebraMap, algebraMap, Algebra.algebraMap,
      singleOneRingHom, singleAddHom, curryAddEquiv, ← ofCoeff_single]

@[to_additive (attr := simp)]
/--
lemma `curryAlgEquiv_single` / 引理 `curryAlgEquiv_single`

English:
lemma curryAlgEquiv_single
  given: (m : M) (n : N) (a : A)
  proof: by simp [curryAlgEquiv]

中文:
引理 curryAlgEquiv_single
  条件: (m : M) (n : N) (a : A)
  证明: by simp [curryAlgEquiv]

Depends on / 依赖: curryAlgEquiv
-/
lemma curryAlgEquiv_single (m : M) (n : N) (a : A) :
    curryAlgEquiv R (single (m, n) a) = single m (single n a) := by simp [curryAlgEquiv]

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive (attr := simp)]
/--
lemma `curryAlgEquiv_symm_single` / 引理 `curryAlgEquiv_symm_single`

English:
lemma curryAlgEquiv_symm_single
  given: (m : M) (n : N) (a : A)
  proof: by
  simp [curryAlgEquiv]

中文:
引理 curryAlgEquiv_symm_single
  条件: (m : M) (n : N) (a : A)
  证明: by
  simp [curryAlgEquiv]

Depends on / 依赖: curryAlgEquiv
-/
lemma curryAlgEquiv_symm_single (m : M) (n : N) (a : A) :
    (curryAlgEquiv R).symm (single m <| single n a) = (single (m, n) a) := by
  simp [curryAlgEquiv]

end Algebra

variable (R A) in
/-- If `f : M → N` is a homomorphism between two magmas, then `MonoidAlgebra.mapDomain f`
is a non-unital algebra homomorphism between their magma algebras. -/
@[to_additive (dont_translate := R A) (attr := simps apply)
/-- If `f : M → N` is a homomorphism between two additive magmas,
then `AddMonoidAlgebra.mapDomain f` is a non-unital algebra homomorphism
between their additive magma algebras. -/]
/--
Definition of `mapDomainNonUnitalAlgHom` / `mapDomainNonUnitalAlgHom` 的定义

English:
definition mapDomainNonUnitalAlgHom
  signature: [CommSemiring R] [Semiring A] [Algebra R A]
  body: mapDomainNonUnitalRingHom A f
  map_mul' := mapDomain_mul f
  map_smul' _ _ := mapDomain_smul ..

中文:
定义 mapDomainNonUnitalAlgHom
  签名: [交换半环 R] [半环 A] [代数 R A]
  定义体: mapDomainNonUnitalRingHom A f
  map_mul' := mapDomain_mul f
  map_smul' _ _ := mapDomain_smul ..

Depends on / 依赖: mapDomainNonUnitalRingHom
-/
def mapDomainNonUnitalAlgHom [CommSemiring R] [Semiring A] [Algebra R A]
    [Mul M] [Mul N] (f : M ->ₙ* N) : A[M] ->ₙₐ[R] A[N] where
  __ := mapDomainNonUnitalRingHom A f
  map_mul' := mapDomain_mul f
  map_smul' _ _ := mapDomain_smul ..

variable (A) in
@[to_additive]
/--
theorem `mapDomain_algebraMap` / 定理 `mapDomain_algebraMap`

English:
theorem mapDomain_algebraMap
  statement: {F : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  proof: by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

中文:
定理 mapDomain_algebraMap
  结论: {F : 类型} [交换半环 R] [半环 A] [代数 R A]
  证明: by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

Depends on / 依赖: coe_algebraMap, mapDomain_single, map_one
-/
theorem mapDomain_algebraMap {F : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F) (r : R) :
    mapDomain f (algebraMap R A[M] r) = algebraMap R A[N] r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

section lift
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

/--
Definition of `liftNCAlgHom` / `liftNCAlgHom` 的定义

English:
definition liftNCAlgHom
  signature: (f : A ->ₐ[R] B) (g : M ->* B) (h_comm : forall x y, Commute (f x) (g y))
  body: { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

中文:
定义 liftNCAlgHom
  签名: (f : A ->ₐ[R] B) (g : M ->* B) (h_comm : 对任意 x y, Commute (f x) (g y))
  定义体: { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

Depends on / 依赖: commutes, h_comm, liftNCRingHom
-/
def liftNCAlgHom (f : A ->ₐ[R] B) (g : M ->* B) (h_comm : forall x y, Commute (f x) (g y)) :
    A[M] ->ₐ[R] B :=
  { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/--
lemma `coe_liftNCAlgHom` / 引理 `coe_liftNCAlgHom`

English:
lemma coe_liftNCAlgHom
  given: (f : A ->ₐ[R] B) (g : M ->* B) (h_comm)
  proof: rfl

中文:
引理 coe_liftNCAlgHom
  条件: (f : A ->ₐ[R] B) (g : M ->* B) (h_comm)
  证明: rfl
-/
@[simp] lemma coe_liftNCAlgHom (f : A ->ₐ[R] B) (g : M ->* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

-- The priority must be `high`.
/-- A `R`-algebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `MonoidHom`s because `of` doesn't additivise. -/
@[to_additive (dont_translate := R A B) (attr := ext high) /--
A `R`-algebra homomorphism from `A[M]` is uniquely defined by its
values on the functions `single m 1` and `single 1 a`.

See note [partially-applied ext lemmas]. Note that the first assumption isn't written as an
equality of `AddMonoidHom`s because `of` doesn't multiplicativise. -/]
/--
lemma `algHom_ext` / 引理 `algHom_ext`

English:
lemma algHom_ext
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐ[R] B⦄ (single_one_right : forall m, φ₁ (single m 1) = φ₂ (single m 1))
  proof: by
  ext x
  induction x using induction_linear with
  | zero => simp
  | add => simp_all
  | single m a => simpa [← map_mul] using congr($(single_one_right m) * $single_one_left a)

中文:
引理 algHom_ext
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐ[R] B⦄ (single_one_right : 对任意 m, φ₁ (single m 1) = φ₂ (single m 1))
  证明: by
  ext x
  induction x using induction_linear with
  | zero => simp
  | add => simp_all
  | single m a => simpa [← map_mul] using congr($(single_one_right m) * $single_one_left a)

Depends on / 依赖: induction_linear, map_mul, single, single_one_left, single_one_right
-/
lemma algHom_ext ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄ (single_one_right : forall m, φ₁ (single m 1) = φ₂ (single m 1))
    (single_one_left : φ₁.comp singleOneAlgHom = φ₂.comp singleOneAlgHom) :
    φ₁ = φ₂ := by
  ext x
  induction x using induction_linear with
  | zero => simp
  | add => simp_all
  | single m a => simpa [← map_mul] using congr($(single_one_right m) * $single_one_left a)

/--
lemma `algHom_ext'` / 引理 `algHom_ext'`

English:
lemma algHom_ext'
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐ[R] B⦄
  proof: algHom_ext (congr($single_one_right ·)) single_one_left

中文:
引理 algHom_ext'
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐ[R] B⦄
  证明: algHom_ext (congr($single_one_right ·)) single_one_left

Depends on / 依赖: algHom_ext, single_one_left, single_one_right
-/
lemma algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄
    (single_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
    (single_one_left : φ₁.comp singleOneAlgHom = φ₂.comp singleOneAlgHom) : φ₁ = φ₂ :=
  algHom_ext (congr($single_one_right ·)) single_one_left

set_option backward.isDefEq.respectTransparency false in
variable (R A M) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (M ->* A) ≃ (R[M] ->ₐ[R] A) where
  body: liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

中文:
定义 lift
  签名: : (M ->* A) ≃ (R[M] ->ₐ[R] A) where
  定义体: liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.ofId, commutes, liftNCAlgHom
-/
def lift : (M ->* A) ≃ (R[M] ->ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

/--
theorem `lift_apply'` / 定理 `lift_apply'`

English:
theorem lift_apply'
  given: (F : M ->* A) (f : R[M])
  proof: rfl

中文:
定理 lift_apply'
  条件: (F : M ->* A) (f : R[M])
  证明: rfl
-/
theorem lift_apply' (F : M ->* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => algebraMap R A b * F a :=
  rfl

/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (F : M ->* A) (f : R[M])
  proof: by simp only [lift_apply', Algebra.smul_def]

中文:
定理 lift_apply
  条件: (F : M ->* A) (f : R[M])
  证明: by simp only [lift_apply', Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, lift_apply, smul_def
-/
theorem lift_apply (F : M ->* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

/--
theorem `lift_def` / 定理 `lift_def`

English:
theorem lift_def
  given: (F : M ->* A)
  statement: ⇑(lift R A M F) = liftNC (algebraMap R A) F
  proof: rfl

@[simp]

中文:
定理 lift_def
  条件: (F : M ->* A)
  结论: ⇑(lift R A M F) = liftNC (algebraMap R A) F
  证明: rfl

@[simp]
-/
theorem lift_def (F : M ->* A) : ⇑(lift R A M F) = liftNC (algebraMap R A) F := rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : R[M] ->ₐ[R] A) (m : M)
  statement: (lift R A M).symm F m = F (single m 1)
  proof: rfl

@[simp]

中文:
定理 lift_symm_apply
  条件: (F : R[M] ->ₐ[R] A) (m : M)
  结论: (lift R A M).symm F m = F (single m 1)
  证明: rfl

@[simp]
-/
theorem lift_symm_apply (F : R[M] ->ₐ[R] A) (m : M) : (lift R A M).symm F m = F (single m 1) := rfl

@[simp]
/--
theorem `lift_single` / 定理 `lift_single`

English:
theorem lift_single
  given: (F : M ->* A) (a b)
  statement: lift R A M F (single a b) = b • F a
  proof: by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

中文:
定理 lift_single
  条件: (F : M ->* A) (a b)
  结论: lift R A M F (single a b) = b • F a
  证明: by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, Algebra, Algebra.smul_def, coe_coe, liftNC_single, lift_def, smul_def
-/
theorem lift_single (F : M ->* A) (a b) : lift R A M F (single a b) = b • F a := by
  rw [lift_def]; rw [liftNC_single]; rw [Algebra.smul_def]; rw [AddMonoidHom.coe_coe]

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (F : M ->* A) (m : M)
  statement: lift R A M F (of R M m) = F m
  proof: by simp

中文:
定理 lift_of
  条件: (F : M ->* A) (m : M)
  结论: lift R A M F (of R M m) = F m
  证明: by simp
-/
theorem lift_of (F : M ->* A) (m : M) : lift R A M F (of R M m) = F m := by simp

/--
theorem `lift_unique'` / 定理 `lift_unique'`

English:
theorem lift_unique'
  given: (F : R[M] ->ₐ[R] A)
  statement: F = lift R A M ((F : R[M] ->* A).comp (of R M))
  proof: ((lift R A M).apply_symm_apply F).symm

中文:
定理 lift_unique'
  条件: (F : R[M] ->ₐ[R] A)
  结论: F = lift R A M ((F : R[M] ->* A).comp (of R M))
  证明: ((lift R A M).apply_symm_apply F).symm

Depends on / 依赖: apply_symm_apply
-/
theorem lift_unique' (F : R[M] ->ₐ[R] A) : F = lift R A M ((F : R[M] ->* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (F : R[M] ->ₐ[R] A) (f : R[M])
  proof: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

中文:
定理 lift_unique
  条件: (F : R[M] ->ₐ[R] A) (f : R[M])
  证明: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

Depends on / 依赖: conv_lhs, lift_apply, lift_unique
-/
theorem lift_unique (F : R[M] ->ₐ[R] A) (f : R[M]) :
    F f = f.coeff.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/--
theorem `lift_mapRingHom_algebraMap` / 定理 `lift_mapRingHom_algebraMap`

English:
theorem lift_mapRingHom_algebraMap
  statement: [CommSemiring S] [Algebra S A]
  proof: by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

中文:
定理 lift_mapRingHom_algebraMap
  结论: [交换半环 S] [代数 S A]
  证明: by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

Depends on / 依赖: single_add
-/
theorem lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A]
    [Algebra R S] [IsScalarTower R S A]
    (f : M ->* A) (x : R[M]) :
    lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- If `f : M → N` is a monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an algebra
homomorphism between their monoid algebras. -/
@[to_additive (dont_translate := R A) (attr := simps! apply)
/-- If `f : M → N` is an additive monoid homomorphism, then `MonoidAlgebra.mapDomain f` is an
algebra homomorphism between their additive monoid algebras. -/]
/--
Definition of `mapDomainAlgHom` / `mapDomainAlgHom` 的定义

English:
definition mapDomainAlgHom
  signature: (f : M ->* N)
  body: mapDomainRingHom A f
  commutes' := by simp

中文:
定义 mapDomainAlgHom
  签名: (f : M ->* N)
  定义体: mapDomainRingHom A f
  commutes' := by simp

Depends on / 依赖: mapDomainRingHom
-/
def mapDomainAlgHom (f : M ->* N) : A[M] ->ₐ[R] A[N] where
  toRingHom := mapDomainRingHom A f
  commutes' := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := A) (attr := simp)]
/--
lemma `mapDomainAlgHom_id` / 引理 `mapDomainAlgHom_id`

English:
lemma mapDomainAlgHom_id
  statement: mapDomainAlgHom R A (.id M) = .id R A[M]
  proof: by ext <;> simp

中文:
引理 mapDomainAlgHom_id
  结论: mapDomainAlgHom R A (.id M) = .id R A[M]
  证明: by ext <;> simp
-/
lemma mapDomainAlgHom_id : mapDomainAlgHom R A (.id M) = .id R A[M] := by ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (dont_translate := A) (attr := simp)]
/--
lemma `mapDomainAlgHom_comp` / 引理 `mapDomainAlgHom_comp`

English:
lemma mapDomainAlgHom_comp
  given: (f : M ->* N) (g : N ->* O)
  proof: by
  ext <;> simp

中文:
引理 mapDomainAlgHom_comp
  条件: (f : M ->* N) (g : N ->* O)
  证明: by
  ext <;> simp
-/
lemma mapDomainAlgHom_comp (f : M ->* N) (g : N ->* O) :
    mapDomainAlgHom R A (g.comp f) = (mapDomainAlgHom R A g).comp (mapDomainAlgHom R A f) := by
  ext <;> simp

variable (R A) in
/-- If `e : M ≃* N` is a multiplicative equivalence between two monoids, then
`MonoidAlgebra.domCongr e` is an algebra equivalence between their monoid algebras. -/
@[to_additive (dont_translate := A)
/-- If `e : M ≃+ N` is an additive equivalence between two additive monoids, then
`AddMonoidAlgebra.domCongr e` is an algebra equivalence between their additive monoid algebras. -/]
/--
Definition of `domCongr` / `domCongr` 的定义

English:
definition domCongr
  signature: (e : M ≃* N)
  body: mapDomainRingEquiv A e
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]

中文:
定义 domCongr
  签名: (e : M ≃* N)
  定义体: mapDomainRingEquiv A e
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]

Depends on / 依赖: mapDomainRingEquiv
-/
def domCongr (e : M ≃* N) : A[M] ≃ₐ[R] A[N] where
  toRingEquiv := mapDomainRingEquiv A e
  commutes' _ := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `coeff_domCongr` / 引理 `coeff_domCongr`

English:
lemma coeff_domCongr
  given: (e : M ≃* N) (f : A[M]) (n : N)
  proof: by simp [domCongr]

@[deprecated (since := "2026-06-18")] alias domCongr_apply := coeff_domCongr

@[to_additive]

中文:
引理 coeff_domCongr
  条件: (e : M ≃* N) (f : A[M]) (n : N)
  证明: by simp [domCongr]

@[deprecated (since := "2026-06-18")] alias domCongr_apply := coeff_domCongr

@[to_additive]

Depends on / 依赖: domCongr
-/
lemma coeff_domCongr (e : M ≃* N) (f : A[M]) (n : N) :
    (domCongr R A e f).coeff n = f.coeff (e.symm n) := by simp [domCongr]

@[deprecated (since := "2026-06-18")] alias domCongr_apply := coeff_domCongr

@[to_additive]
/--
theorem `domCongr_toAlgHom` / 定理 `domCongr_toAlgHom`

English:
theorem domCongr_toAlgHom
  given: (e : M ≃* N)
  statement: (domCongr R A e).toAlgHom = mapDomainAlgHom R A e
  proof: rfl

中文:
定理 domCongr_toAlgHom
  条件: (e : M ≃* N)
  结论: (domCongr R A e).toAlgHom = mapDomainAlgHom R A e
  证明: rfl
-/
theorem domCongr_toAlgHom (e : M ≃* N) : (domCongr R A e).toAlgHom = mapDomainAlgHom R A e := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
lemma `domCongr_support` / 引理 `domCongr_support`

English:
lemma domCongr_support
  given: (e : M ≃* N) (x : A[M])
  proof: by simp [domCongr, equivMapDomain]

@[to_additive (attr := simp)]

中文:
引理 domCongr_support
  条件: (e : M ≃* N) (x : A[M])
  证明: by simp [domCongr, equivMapDomain]

@[to_additive (attr := simp)]

Depends on / 依赖: domCongr, equivMapDomain
-/
lemma domCongr_support (e : M ≃* N) (x : A[M]) :
    (domCongr R A e x).coeff.support = x.coeff.support.map e := by simp [domCongr, equivMapDomain]

@[to_additive (attr := simp)]
/--
theorem `domCongr_single` / 定理 `domCongr_single`

English:
theorem domCongr_single
  given: (e : M ≃* N) (m : M) (a : A)
  proof: by simp [domCongr]

@[to_additive (attr := simp)]

中文:
定理 domCongr_single
  条件: (e : M ≃* N) (m : M) (a : A)
  证明: by simp [domCongr]

@[to_additive (attr := simp)]

Depends on / 依赖: Pi.existsMulOfLe, domCongr, existsMulOfLe
-/
theorem domCongr_single (e : M ≃* N) (m : M) (a : A) :
    domCongr R A e (single m a) = single (e m) a := by simp [domCongr]

@[to_additive (attr := simp)]
/--
lemma `domCongr_comp_lsingle` / 引理 `domCongr_comp_lsingle`

English:
lemma domCongr_comp_lsingle
  given: (e : M ≃* N) (m : M)
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 domCongr_comp_lsingle
  条件: (e : M ≃* N) (m : M)
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma domCongr_comp_lsingle (e : M ≃* N) (m : M) :
    (domCongr R A e).toLinearMap ∘ₗ lsingle m = lsingle (e m) := by ext; simp

@[to_additive (attr := simp)]
/--
theorem `domCongr_refl` / 定理 `domCongr_refl`

English:
theorem domCongr_refl
  statement: domCongr R A (.refl M) = .refl
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
定理 domCongr_refl
  结论: domCongr R A (.refl M) = .refl
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
theorem domCongr_refl : domCongr R A (.refl M) = .refl := by ext; simp

@[to_additive (attr := simp)]
/--
theorem `domCongr_symm` / 定理 `domCongr_symm`

English:
theorem domCongr_symm
  given: (e : M ≃* N)
  statement: (domCongr R A e).symm = domCongr R A e.symm
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 domCongr_symm
  条件: (e : M ≃* N)
  结论: (domCongr R A e).symm = domCongr R A e.symm
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem domCongr_symm (e : M ≃* N) : (domCongr R A e).symm = domCongr R A e.symm := rfl

@[to_additive (attr := simp)]
/--
theorem `trans_domCongr_domCongr` / 定理 `trans_domCongr_domCongr`

English:
theorem trans_domCongr_domCongr
  given: (e : M ≃* N) (f : N ≃* O)
  proof: by
  ext
  simp

中文:
定理 trans_domCongr_domCongr
  条件: (e : M ≃* N) (f : N ≃* O)
  证明: by
  ext
  simp
-/
theorem trans_domCongr_domCongr (e : M ≃* N) (f : N ≃* O) :
    (domCongr R A e).trans (domCongr R A f) = domCongr R A (e.trans f) := by
  ext
  simp

/-- `MonoidAlgebra.domCongr` as a `MonoidHom` from `MulAut`. -/
@[simps]
/--
Definition of `domCongrAut` / `domCongrAut` 的定义

English:
definition domCongrAut
  signature: : MulAut M ->* A[M] ≃ₐ[R] A[M] where
  body: MonoidAlgebra.domCongr R A
  map_one' := by rw [MulAut.one_def, AlgEquiv.aut_one, domCongr_refl]
  map_mul' _ _ := by rw [MulAut.mul_def, AlgEquiv.aut_mul, trans_domCongr_domCongr]

中文:
定义 domCongrAut
  签名: : MulAut M ->* A[M] ≃ₐ[R] A[M] where
  定义体: MonoidAlgebra.domCongr R A
  map_one' := by rw [MulAut.one_def, AlgEquiv.aut_one, domCongr_refl]
  map_mul' _ _ := by rw [MulAut.mul_def, AlgEquiv.aut_mul, trans_domCongr_domCongr]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.domCongr, domCongr
-/
def domCongrAut : MulAut M ->* A[M] ≃ₐ[R] A[M] where
  toFun := MonoidAlgebra.domCongr R A
  map_one' := by rw [MulAut.one_def, AlgEquiv.aut_one, domCongr_refl]
  map_mul' _ _ := by rw [MulAut.mul_def, AlgEquiv.aut_mul, trans_domCongr_domCongr]

variable (R) in
/-- Nested monoid algebras can be taken in an arbitrary order. -/
@[to_additive
/-- Nested monoid algebras can be taken in an arbitrary order. -/]
/--
Definition of `commAlgEquiv` / `commAlgEquiv` 的定义

English:
definition commAlgEquiv
  signature: : A[M][N] ≃ₐ[R] A[N][M]
  body: (curryAlgEquiv _).symm.trans .trans (domCongr _ _ <| .prodComm ..) (curryAlgEquiv _)

@[to_additive (attr := simp)]

中文:
定义 commAlgEquiv
  签名: : A[M][N] ≃ₐ[R] A[N][M]
  定义体: (curryAlgEquiv _).symm.trans .trans (domCongr _ _ <| .prodComm ..) (curryAlgEquiv _)

@[to_additive (attr := simp)]

Depends on / 依赖: curryAlgEquiv, domCongr, prodComm, symm.trans
-/
def commAlgEquiv : A[M][N] ≃ₐ[R] A[N][M] :=
(curryAlgEquiv _).symm.trans .trans (domCongr _ _ <| .prodComm ..) (curryAlgEquiv _)

@[to_additive (attr := simp)]
/--
lemma `symm_commAlgEquiv` / 引理 `symm_commAlgEquiv`

English:
lemma symm_commAlgEquiv
  statement: (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAlgEquiv R
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 symm_commAlgEquiv
  结论: (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAlgEquiv R
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma symm_commAlgEquiv : (commAlgEquiv R : A[M][N] ≃ₐ[R] A[N][M]).symm = commAlgEquiv R := rfl

@[to_additive (attr := simp)]
/--
lemma `commAlgEquiv_single_single` / 引理 `commAlgEquiv_single_single`

English:
lemma commAlgEquiv_single_single
  given: (m : M) (n : N) (a : A)
  proof: commRingEquiv_single_single ..

@[to_additive (dont_translate := A) (attr := simp)]

中文:
引理 commAlgEquiv_single_single
  条件: (m : M) (n : N) (a : A)
  证明: commRingEquiv_single_single ..

@[to_additive (dont_translate := A) (attr := simp)]

Depends on / 依赖: commRingEquiv_single_single
-/
lemma commAlgEquiv_single_single (m : M) (n : N) (a : A) :
    commAlgEquiv R (single m <| single n a) = single n (single m a) :=
  commRingEquiv_single_single ..

@[to_additive (dont_translate := A) (attr := simp)]
/--
lemma `commAlgEquiv_single_one` / 引理 `commAlgEquiv_single_one`

English:
lemma commAlgEquiv_single_one
  given: (m : M)
  proof: commRingEquiv_single_one ..

中文:
引理 commAlgEquiv_single_one
  条件: (m : M)
  证明: commRingEquiv_single_one ..

Depends on / 依赖: commRingEquiv_single_one
-/
lemma commAlgEquiv_single_one (m : M) :
    commAlgEquiv R (single m (1 : A[N])) = single 1 (single m 1) := commRingEquiv_single_one ..

-- We want this lemma to be tried before `commAlgEquiv_single_single`.
@[to_additive (dont_translate := A) (attr := simp high)]
/--
lemma `commAlgEquiv_single_one_single` / 引理 `commAlgEquiv_single_one_single`

English:
lemma commAlgEquiv_single_one_single
  given: (m : M)
  proof: commRingEquiv_single_one_single ..

中文:
引理 commAlgEquiv_single_one_single
  条件: (m : M)
  证明: commRingEquiv_single_one_single ..

Depends on / 依赖: commRingEquiv_single_one_single
-/
lemma commAlgEquiv_single_one_single (m : M) :
    commAlgEquiv R (single 1 <| single m 1) = (single m (1 : A[N])) :=
  commRingEquiv_single_one_single ..

end lift

section mapRange
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C] [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
/--
lemma `mapDomainRingHom_comp_algebraMap` / 引理 `mapDomainRingHom_comp_algebraMap`

English:
lemma mapDomainRingHom_comp_algebraMap
  given: (f : M ->* N)
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
引理 mapDomainRingHom_comp_algebraMap
  条件: (f : M ->* N)
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
lemma mapDomainRingHom_comp_algebraMap (f : M ->* N) :
    (mapDomainRingHom A f).comp (algebraMap R A[M]) = algebraMap R A[N] := by ext; simp

@[to_additive (attr := simp)]
/--
lemma `mapRingHom_comp_algebraMap` / 引理 `mapRingHom_comp_algebraMap`

English:
lemma mapRingHom_comp_algebraMap
  given: (f : R ->+* S)
  proof: by ext; simp

@[deprecated (since := "2026-06-18")]
alias mapRangeRingHom_comp_algebraMap := mapRingHom_comp_algebraMap

中文:
引理 mapRingHom_comp_algebraMap
  条件: (f : R ->+* S)
  证明: by ext; simp

@[deprecated (since := "2026-06-18")]
alias mapRangeRingHom_comp_algebraMap := mapRingHom_comp_algebraMap

Depends on / 依赖: algebraMap
-/
lemma mapRingHom_comp_algebraMap (f : R ->+* S) :
    (mapRingHom (M := M) f).comp (algebraMap _ _) = (algebraMap _ _).comp f := by ext; simp

@[deprecated (since := "2026-06-18")]
alias mapRangeRingHom_comp_algebraMap := mapRingHom_comp_algebraMap

variable (M) in
/-- The algebra homomorphism of monoid algebras induced by a homomorphism of the base algebras. -/
@[to_additive
/-- The algebra homomorphism of additive monoid algebras induced by a homomorphism of the base
algebras. -/]
/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (f : A ->ₐ[R] B)
  body: mapRingHom M f
  commutes' := by simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom := mapAlgHom

中文:
定义 mapAlgHom
  签名: (f : A ->ₐ[R] B)
  定义体: mapRingHom M f
  commutes' := by simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom := mapAlgHom

Depends on / 依赖: mapRingHom
-/
noncomputable def mapAlgHom (f : A ->ₐ[R] B) : A[M] ->ₐ[R] B[M] where
  __ := mapRingHom M f
  commutes' := by simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom := mapAlgHom

variable (M) in
@[to_additive (attr := simp)]
/--
lemma `toRingHom_mapAlgHom` / 引理 `toRingHom_mapAlgHom`

English:
lemma toRingHom_mapAlgHom
  given: (f : A ->ₐ[R] B)
  proof: rfl

@[deprecated (since := "2026-06-18")] alias toRingHom_mapRangeAlgHom := toRingHom_mapAlgHom

@[to_additive (attr := simp)]

中文:
引理 toRingHom_mapAlgHom
  条件: (f : A ->ₐ[R] B)
  证明: rfl

@[deprecated (since := "2026-06-18")] alias toRingHom_mapRangeAlgHom := toRingHom_mapAlgHom

@[to_additive (attr := simp)]
-/
lemma toRingHom_mapAlgHom (f : A ->ₐ[R] B) :
    mapAlgHom M f = mapRingHom M f.toRingHom := rfl

@[deprecated (since := "2026-06-18")] alias toRingHom_mapRangeAlgHom := toRingHom_mapAlgHom

@[to_additive (attr := simp)]
/--
lemma `coeff_mapAlgHom` / 引理 `coeff_mapAlgHom`

English:
lemma coeff_mapAlgHom
  given: (f : A ->ₐ[R] B) (x : A[M]) (m : M)
  proof: by simp [mapAlgHom]

@[deprecated (since := "2026-06-18")] alias mapAlgHom_apply := coeff_mapAlgHom
@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_apply := coeff_mapAlgHom

@[to_additive (attr := simp)]

中文:
引理 coeff_mapAlgHom
  条件: (f : A ->ₐ[R] B) (x : A[M]) (m : M)
  证明: by simp [mapAlgHom]

@[deprecated (since := "2026-06-18")] alias mapAlgHom_apply := coeff_mapAlgHom
@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_apply := coeff_mapAlgHom

@[to_additive (attr := simp)]

Depends on / 依赖: mapAlgHom
-/
lemma coeff_mapAlgHom (f : A ->ₐ[R] B) (x : A[M]) (m : M) :
    (mapAlgHom M f x).coeff m = f (x.coeff m) := by simp [mapAlgHom]

@[deprecated (since := "2026-06-18")] alias mapAlgHom_apply := coeff_mapAlgHom
@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_apply := coeff_mapAlgHom

@[to_additive (attr := simp)]
/--
lemma `mapAlgHom_single` / 引理 `mapAlgHom_single`

English:
lemma mapAlgHom_single
  given: (f : A ->ₐ[R] B) (m : M) (a : A)
  proof: by
  classical ext; simp [single_apply, apply_ite f]

@[to_additive (dont_translate := A) (attr := simp)]

中文:
引理 mapAlgHom_single
  条件: (f : A ->ₐ[R] B) (m : M) (a : A)
  证明: by
  classical ext; simp [single_apply, apply_ite f]

@[to_additive (dont_translate := A) (attr := simp)]

Depends on / 依赖: apply_ite, classical, single_apply
-/
lemma mapAlgHom_single (f : A ->ₐ[R] B) (m : M) (a : A) :
    mapAlgHom M f (single m a) = single m (f a) := by
  classical ext; simp [single_apply, apply_ite f]

@[to_additive (dont_translate := A) (attr := simp)]
/--
lemma `mapAlgHom_id` / 引理 `mapAlgHom_id`

English:
lemma mapAlgHom_id
  statement: mapAlgHom M (.id R A) = .id R A[M]
  proof: by ext <;> simp

@[to_additive (dont_translate := A B C) (attr := simp)]

中文:
引理 mapAlgHom_id
  结论: mapAlgHom M (.id R A) = .id R A[M]
  证明: by ext <;> simp

@[to_additive (dont_translate := A B C) (attr := simp)]
-/
lemma mapAlgHom_id : mapAlgHom M (.id R A) = .id R A[M] := by ext <;> simp

@[to_additive (dont_translate := A B C) (attr := simp)]
/--
lemma `mapRangeAlgHom_comp` / 引理 `mapRangeAlgHom_comp`

English:
lemma mapRangeAlgHom_comp
  given: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  proof: by ext <;> simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_single := mapAlgHom_single

中文:
引理 mapRangeAlgHom_comp
  条件: (f : A ->ₐ[R] B) (g : B ->ₐ[R] C)
  证明: by ext <;> simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_single := mapAlgHom_single
-/
lemma mapRangeAlgHom_comp (f : A ->ₐ[R] B) (g : B ->ₐ[R] C) :
    mapAlgHom M (g.comp f) = (mapAlgHom M g).comp (mapAlgHom M f) := by ext <;> simp

@[deprecated (since := "2026-06-18")] alias mapRangeAlgHom_single := mapAlgHom_single

variable (R M) in
/-- The algebra isomorphism of monoid algebras induced by an isomorphism of the base algebras. -/
@[to_additive (attr := simps apply)
/-- The algebra isomorphism of additive monoid algebras induced by an isomorphism of the base
algebras. -/]
/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (e : A ≃ₐ[R] B)
  body: mapAlgHom M e
  invFun := mapAlgHom M (e.symm : B ->ₐ[R] A)
  left_inv _ := by aesop
  right_inv _ := by aesop

@[deprecated (since := "2026-06-18")] alias mapRangeAlgEquiv := mapAlgEquiv

@[to_additive (attr := simp)]

中文:
定义 mapAlgEquiv
  签名: (e : A ≃ₐ[R] B)
  定义体: mapAlgHom M e
  invFun := mapAlgHom M (e.symm : B ->ₐ[R] A)
  left_inv _ := by aesop
  right_inv _ := by aesop

@[deprecated (since := "2026-06-18")] alias mapRangeAlgEquiv := mapAlgEquiv

@[to_additive (attr := simp)]

Depends on / 依赖: mapAlgHom
-/
noncomputable def mapAlgEquiv (e : A ≃ₐ[R] B) : A[M] ≃ₐ[R] B[M] where
  __ := mapAlgHom M e
  invFun := mapAlgHom M (e.symm : B ->ₐ[R] A)
  left_inv _ := by aesop
  right_inv _ := by aesop

@[deprecated (since := "2026-06-18")] alias mapRangeAlgEquiv := mapAlgEquiv

@[to_additive (attr := simp)]
/--
lemma `symm_mapAlgEquiv` / 引理 `symm_mapAlgEquiv`

English:
lemma symm_mapAlgEquiv
  given: (e : A ≃ₐ[R] B)
  statement: (mapAlgEquiv R M e).symm = mapAlgEquiv R M e.symm
  proof: rfl

@[deprecated (since := "2026-06-18")] alias symm_mapRangeAlgEquiv := symm_mapAlgEquiv

@[to_additive (attr := simp)]

中文:
引理 symm_mapAlgEquiv
  条件: (e : A ≃ₐ[R] B)
  结论: (mapAlgEquiv R M e).symm = mapAlgEquiv R M e.symm
  证明: rfl

@[deprecated (since := "2026-06-18")] alias symm_mapRangeAlgEquiv := symm_mapAlgEquiv

@[to_additive (attr := simp)]
-/
lemma symm_mapAlgEquiv (e : A ≃ₐ[R] B) : (mapAlgEquiv R M e).symm = mapAlgEquiv R M e.symm := rfl

@[deprecated (since := "2026-06-18")] alias symm_mapRangeAlgEquiv := symm_mapAlgEquiv

@[to_additive (attr := simp)]
/--
lemma `mapAlgEquiv_trans` / 引理 `mapAlgEquiv_trans`

English:
lemma mapAlgEquiv_trans
  given: (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C)
  proof: by ext; simp

@[deprecated (since := "2026-03-27")] alias mapRangeAlgEquiv_trans := mapAlgEquiv_trans

中文:
引理 mapAlgEquiv_trans
  条件: (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C)
  证明: by ext; simp

@[deprecated (since := "2026-03-27")] alias mapRangeAlgEquiv_trans := mapAlgEquiv_trans
-/
lemma mapAlgEquiv_trans (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) :
    mapAlgEquiv R M (e₁.trans e₂) = (mapAlgEquiv R M e₁).trans (mapAlgEquiv R M e₂) := by ext; simp

@[deprecated (since := "2026-03-27")] alias mapRangeAlgEquiv_trans := mapAlgEquiv_trans

variable (R M) in
/-- `MonoidAlgebra.mapRangeAlgEquiv` as a `MonoidHom` from `A ≃ₐ[R] A`. -/
@[simps]
/--
Definition of `mapRangeAlgAut` / `mapRangeAlgAut` 的定义

English:
definition mapRangeAlgAut
  signature: : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  body: mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

中文:
定义 mapRangeAlgAut
  签名: : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  定义体: mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

Depends on / 依赖: mapAlgEquiv
-/
def mapRangeAlgAut : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  toFun f := mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end mapRange

section

variable (R) in
/--
Definition of `GroupSMul.linearMap` / `GroupSMul.linearMap` 的定义

English:
definition GroupSMul.linearMap
  signature: [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V] [Module R V]
  body: single g (1 : R) • v
  map_add' x y := smul_add (single g (1 : R)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

中文:
定义 GroupSMul.linearMap
  签名: [幺半群 M] [交换半环 R] (V : 类型) [加法交换幺半群 V] [模 R V]
  定义体: single g (1 : R) • v
  map_add' x y := smul_add (single g (1 : R)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

Depends on / 依赖: single
-/
def GroupSMul.linearMap [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V] [Module R V]
    [Module R[M] V] [IsScalarTower R R[M] V] (g : M) : V ->ₗ[R] V where
  toFun v := single g (1 : R) • v
  map_add' x y := smul_add (single g (1 : R)) x y
  map_smul' _c _x := smul_algebra_smul_comm _ _ _

variable (R) in
@[simp]
/--
theorem `GroupSMul.linearMap_apply` / 定理 `GroupSMul.linearMap_apply`

English:
theorem GroupSMul.linearMap_apply
  statement: [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V]
  proof: rfl

中文:
定理 GroupSMul.linearMap_apply
  结论: [幺半群 M] [交换半环 R] (V : 类型) [加法交换幺半群 V]
  证明: rfl
-/
theorem GroupSMul.linearMap_apply [Monoid M] [CommSemiring R] (V : Type*) [AddCommMonoid V]
    [Module R V] [Module R[M] V] [IsScalarTower R R[M] V] (g : M) (v : V) :
    (GroupSMul.linearMap R V g) v = single g (1 : R) • v :=
  rfl

variable [Monoid M] [CommSemiring R] {V W : Type*} [AddCommMonoid V] [Module R V]
  [Module R[M] V] [IsScalarTower R R[M] V] [AddCommMonoid W]
  [Module R W] [Module R[M] W] [IsScalarTower R R[M] W]
  (f : V ->ₗ[R] W)

/--
Definition of `equivariantOfLinearOfComm` / `equivariantOfLinearOfComm` 的定义

English:
definition equivariantOfLinearOfComm
  body: f
  map_add' v v' := by simp
  map_smul' c v := by
    refine induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul]; rw [algebraMap_smul]; rw [f.map_smul]; rw [of_apply]

中文:
定义 equivariantOfLinearOfComm
  定义体: f
  map_add' v v' := by simp
  map_smul' c v := by
    refine induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul]; rw [algebraMap_smul]; rw [f.map_smul]; rw [of_apply]
-/
def equivariantOfLinearOfComm
    (h : forall (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v) :
    V ->ₗ[R[M]] W where
  toFun := f
  map_add' v v' := by simp
  map_smul' c v := by
    refine induction c ?_ ?_
    · simp
    · intro g r c' _nm _nz w
      dsimp at *
      simp only [add_smul, f.map_add, w, single_eq_algebraMap_mul_of, ← smul_smul]
      rw [algebraMap_smul]; rw [algebraMap_smul]; rw [f.map_smul]; rw [of_apply]; rw [h g v]

variable (h : forall (g : M) (v : V), f (single g (1 : R) • v) = single g (1 : R) • f v)

@[simp]
/--
theorem `equivariantOfLinearOfComm_apply` / 定理 `equivariantOfLinearOfComm_apply`

English:
theorem equivariantOfLinearOfComm_apply
  given: (v : V)
  statement: (equivariantOfLinearOfComm f h) v = f v
  proof: rfl

中文:
定理 equivariantOfLinearOfComm_apply
  条件: (v : V)
  结论: (equivariantOfLinearOfComm f h) v = f v
  证明: rfl
-/
theorem equivariantOfLinearOfComm_apply (v : V) : (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end

variable [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- If `S` is an `R`-algebra, then `S[M]` is a `R[M]` algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/
@[to_additive
/-- If `S` is an `R`-algebra, then `S[M]` is an `R[M]`-algebra.

Warning: This produces a diamond for `Algebra R[M] S[M][M]` and another one for `Algebra R[M] R[M]`.
That's why it is not a global instance. -/]
/--
Definition of `algebraMonoidAlgebra` / `algebraMonoidAlgebra` 的定义

English:
abbreviation algebraMonoidAlgebra
  signature: : Algebra R[M] S[M]
  body: (mapRingHom M (algebraMap R S)).toAlgebra

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.algebraMonoidAlgebra
  AddMonoidAlgebra.algebraAddMonoidAlgebra

中文:
缩写 algebraMonoidAlgebra
  签名: : 代数 R[M] S[M]
  定义体: (mapRingHom M (algebraMap R S)).toAlgebra

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.algebraMonoidAlgebra
  AddMonoidAlgebra.algebraAddMonoidAlgebra

Depends on / 依赖: algebraMap, mapRingHom, toAlgebra
-/
noncomputable abbrev algebraMonoidAlgebra : Algebra R[M] S[M] :=
  (mapRingHom M (algebraMap R S)).toAlgebra

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.algebraMonoidAlgebra
  AddMonoidAlgebra.algebraAddMonoidAlgebra

open scoped AlgebraMonoidAlgebra

@[to_additive (attr := simp)]
/--
lemma `algebraMap_def` / 引理 `algebraMap_def`

English:
lemma algebraMap_def
  statement: algebraMap R[M] S[M] = mapRingHom M (algebraMap R S)
  proof: rfl

@[to_additive (dont_translate := R)]

中文:
引理 algebraMap_def
  结论: algebraMap R[M] S[M] = mapRingHom M (algebraMap R S)
  证明: rfl

@[to_additive (dont_translate := R)]
-/
lemma algebraMap_def : algebraMap R[M] S[M] = mapRingHom M (algebraMap R S) := rfl

@[to_additive (dont_translate := R)]
/--
lemma `isScalarTower_monoidAlgebra` / 引理 `isScalarTower_monoidAlgebra`

English:
lemma isScalarTower_monoidAlgebra
  statement: [CommSemiring T] [Algebra R T] [Algebra S T]
  proof: .of_algebraMap_eq' (mapAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

中文:
引理 isScalarTower_monoidAlgebra
  结论: [交换半环 T] [代数 R T] [代数 S T]
  证明: .of_algebraMap_eq' (mapAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, comp_algebraMap, comp_algebraMap.symm, mapAlgHom, of_algebraMap_eq, toAlgHom
-/
lemma isScalarTower_monoidAlgebra [CommSemiring T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] : IsScalarTower R S[M] T[M] :=
  .of_algebraMap_eq' (mapAlgHom _ (IsScalarTower.toAlgHom R S T)).comp_algebraMap.symm

scoped[AlgebraMonoidAlgebra] attribute [instance] MonoidAlgebra.isScalarTower_monoidAlgebra
  AddMonoidAlgebra.vaddAssocClass_addMonoidAlgebra

end MonoidAlgebra

namespace AddMonoidAlgebra

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

variable (R) [Semiring R] [Add M] [NonUnitalNonAssocSemiring A]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/--
theorem `nonUnitalAlgHom_ext'` / 定理 `nonUnitalAlgHom_ext'`

English:
theorem nonUnitalAlgHom_ext'
  statement: [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  proof: nonUnitalAlgHom_ext R DFunLike.congr_fun h

中文:
定理 nonUnitalAlgHom_ext'
  结论: [分配乘法作用 R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
  证明: nonUnitalAlgHom_ext R DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, nonUnitalAlgHom_ext
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] ->ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ :=
nonUnitalAlgHom_ext R DFunLike.congr_fun h

set_option backward.isDefEq.respectTransparency false in
/-- The functor `M ↦ R[M]`, from the category of magmas to the category of
non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the other
direction. -/
@[simps apply_apply symm_apply]
/--
Definition of `liftMagma` / `liftMagma` 的定义

English:
definition liftMagma
  signature: [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  body: {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f <| .ofAdd x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum

中文:
定义 liftMagma
  签名: [模 R A] [标量塔 R A A] [标量交换类 R A A]
  定义体: {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f <| .ofAdd x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum
-/
def liftMagma [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    (Multiplicative M ->ₙ* A) ≃ (R[M] ->ₙₐ[R] A) where
  toFun f := {
    toAddMonoidHom :=
      (liftAddHom fun x => (smulAddHom R A).flip (f <| .ofAdd x)).comp coeffAddEquiv.toAddMonoidHom
    map_smul' t' a := by simp [Finsupp.smul_sum, sum_smul_index', mul_smul]
    map_mul' a₁ a₂ := by
      simpa [mul_def, sum_sum_index, add_smul, Finsupp.mul_sum, Finsupp.sum_mul,
        smul_mul_smul_comm] using Finsupp.sum_comm ..
  }
  invFun F := F.toMulHom.comp (ofMagma R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

end NonUnitalNonAssocAlgebra

/-! #### Algebra structure -/

section lift

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/--
Definition of `liftNCAlgHom` / `liftNCAlgHom` 的定义

English:
definition liftNCAlgHom
  signature: (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm : forall x y, Commute (f x) (g y))
  body: { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

中文:
定义 liftNCAlgHom
  签名: (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm : 对任意 x y, Commute (f x) (g y))
  定义体: { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

Depends on / 依赖: commutes, h_comm, liftNCRingHom
-/
def liftNCAlgHom (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm : forall x y, Commute (f x) (g y)) :
    A[M] ->ₐ[R] B :=
  { liftNCRingHom (f : A ->+* B) g h_comm with
    commutes' := by simp [liftNCRingHom] }

/--
lemma `coe_liftNCAlgHom` / 引理 `coe_liftNCAlgHom`

English:
lemma coe_liftNCAlgHom
  given: (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm)
  proof: rfl

中文:
引理 coe_liftNCAlgHom
  条件: (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm)
  证明: rfl
-/
@[simp] lemma coe_liftNCAlgHom (f : A ->ₐ[R] B) (g : Multiplicative M ->* B) (h_comm) :
    ⇑(liftNCAlgHom f g h_comm) = liftNC f g := rfl

/--
lemma `algHom_ext'` / 引理 `algHom_ext'`

English:
lemma algHom_ext'
  given: ⦃φ₁ φ₂
  statement: A[M] ->ₐ[R] B⦄
  proof: algHom_ext (congr($single_one_right ·)) single_one_left

中文:
引理 algHom_ext'
  条件: ⦃φ₁ φ₂
  结论: A[M] ->ₐ[R] B⦄
  证明: algHom_ext (congr($single_one_right ·)) single_one_left

Depends on / 依赖: algHom_ext, single_one_left, single_one_right
-/
lemma algHom_ext' ⦃φ₁ φ₂ : A[M] ->ₐ[R] B⦄
    (single_one_right : (φ₁ : A[M] ->* B).comp (of A M) = (φ₂ : A[M] ->* B).comp (of A M))
    (single_one_left : φ₁.comp singleZeroAlgHom = φ₂.comp singleZeroAlgHom) : φ₁ = φ₂ :=
  algHom_ext (congr($single_one_right ·)) single_one_left

set_option backward.isDefEq.respectTransparency false in
variable (R M A) in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (Multiplicative M ->* A) ≃ (R[M] ->ₐ[R] A) where
  body: liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

中文:
定义 lift
  签名: : (Multiplicative M ->* A) ≃ (R[M] ->ₐ[R] A) where
  定义体: liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.ofId, commutes, liftNCAlgHom
-/
def lift : (Multiplicative M ->* A) ≃ (R[M] ->ₐ[R] A) where
  toFun F := liftNCAlgHom (Algebra.ofId R A) F fun _ _ => Algebra.commutes _ _
  invFun f := (f : R[M] ->* A).comp (of R M)
  left_inv f := by ext; simp
  right_inv F := by ext; simp

/--
theorem `lift_apply'` / 定理 `lift_apply'`

English:
theorem lift_apply'
  given: (F : Multiplicative M ->* A) (f : R[M])
  proof: rfl

中文:
定理 lift_apply'
  条件: (F : Multiplicative M ->* A) (f : R[M])
  证明: rfl
-/
theorem lift_apply' (F : Multiplicative M ->* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => algebraMap R A b * F (.ofAdd a) := rfl

/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (F : Multiplicative M ->* A) (f : R[M])
  proof: by
  simp only [lift_apply', Algebra.smul_def]

中文:
定理 lift_apply
  条件: (F : Multiplicative M ->* A) (f : R[M])
  证明: by
  simp only [lift_apply', Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, lift_apply, smul_def
-/
theorem lift_apply (F : Multiplicative M ->* A) (f : R[M]) :
    lift R A M F f = f.coeff.sum fun a b => b • F (.ofAdd a) := by
  simp only [lift_apply', Algebra.smul_def]

/--
theorem `lift_def` / 定理 `lift_def`

English:
theorem lift_def
  given: (F : Multiplicative M ->* A)
  proof: rfl

@[simp]

中文:
定理 lift_def
  条件: (F : Multiplicative M ->* A)
  证明: rfl

@[simp]
-/
theorem lift_def (F : Multiplicative M ->* A) :
    ⇑(lift R A M F) = liftNC ((algebraMap R A : R ->+* A) : R ->+ A) F :=
  rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (F : R[M] ->ₐ[R] A) (x : Multiplicative M)
  proof: rfl

中文:
定理 lift_symm_apply
  条件: (F : R[M] ->ₐ[R] A) (x : Multiplicative M)
  证明: rfl
-/
theorem lift_symm_apply (F : R[M] ->ₐ[R] A) (x : Multiplicative M) :
    (lift R A M).symm F x = F (single x.toAdd 1) :=
  rfl

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (F : Multiplicative M ->* A) (x : Multiplicative M)
  proof: MonoidAlgebra.lift_of F x

@[simp]

中文:
定理 lift_of
  条件: (F : Multiplicative M ->* A) (x : Multiplicative M)
  证明: MonoidAlgebra.lift_of F x

@[simp]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.lift_of, lift_of
-/
theorem lift_of (F : Multiplicative M ->* A) (x : Multiplicative M) :
    lift R A M F (of R M x) = F x := MonoidAlgebra.lift_of F x

@[simp]
/--
theorem `lift_single` / 定理 `lift_single`

English:
theorem lift_single
  given: (F : Multiplicative M ->* A) (a b)
  proof: MonoidAlgebra.lift_single F (.ofAdd a) b

中文:
定理 lift_single
  条件: (F : Multiplicative M ->* A) (a b)
  证明: MonoidAlgebra.lift_single F (.ofAdd a) b

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.lift_single, lift_single
-/
theorem lift_single (F : Multiplicative M ->* A) (a b) :
    lift R A M F (single a b) = b • F (Multiplicative.ofAdd a) :=
  MonoidAlgebra.lift_single F (.ofAdd a) b

/--
lemma `lift_of'` / 引理 `lift_of'`

English:
lemma lift_of'
  given: (F : Multiplicative M ->* A) (x : M)
  proof: lift_of F x

中文:
引理 lift_of'
  条件: (F : Multiplicative M ->* A) (x : M)
  证明: lift_of F x

Depends on / 依赖: lift_of
-/
lemma lift_of' (F : Multiplicative M ->* A) (x : M) :
    lift R A M F (of' R M x) = F (Multiplicative.ofAdd x) :=
  lift_of F x

/--
theorem `lift_unique'` / 定理 `lift_unique'`

English:
theorem lift_unique'
  given: (F : R[M] ->ₐ[R] A)
  proof: ((lift R A M).apply_symm_apply F).symm

中文:
定理 lift_unique'
  条件: (F : R[M] ->ₐ[R] A)
  证明: ((lift R A M).apply_symm_apply F).symm

Depends on / 依赖: apply_symm_apply
-/
theorem lift_unique' (F : R[M] ->ₐ[R] A) :
    F = lift R A M ((F : R[M] ->* A).comp (of R M)) :=
  ((lift R A M).apply_symm_apply F).symm

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (F : R[M] ->ₐ[R] A) (f : R[M])
  proof: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

中文:
定理 lift_unique
  条件: (F : R[M] ->ₐ[R] A) (f : R[M])
  证明: by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

Depends on / 依赖: conv_lhs, lift_apply, lift_unique
-/
theorem lift_unique (F : R[M] ->ₐ[R] A) (f : R[M]) :
    F f = f.coeff.sum fun m r => r • F (single m 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/--
lemma `lift_mapRingHom_algebraMap` / 引理 `lift_mapRingHom_algebraMap`

English:
lemma lift_mapRingHom_algebraMap
  statement: [CommSemiring S] [Algebra S A] [Algebra R S] [IsScalarTower R S A]
  proof: by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

中文:
引理 lift_mapRingHom_algebraMap
  结论: [交换半环 S] [代数 S A] [代数 R S] [标量塔 R S A]
  证明: by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

Depends on / 依赖: single_add
-/
lemma lift_mapRingHom_algebraMap [CommSemiring S] [Algebra S A] [Algebra R S] [IsScalarTower R S A]
    (f : Multiplicative M ->* A) (x : R[M]) :
    lift _ _ _ f (mapRingHom _ (algebraMap R S) x) = lift _ _ _ f x := by
  induction x using induction with
  | zero => simp
  | single_add a b f _ _ ih => simp [ih]

@[deprecated (since := "2026-06-18")]
alias lift_mapRangeRingHom_algebraMap := lift_mapRingHom_algebraMap

variable (R A) in
/-- `AddMonoidAlgebra.domCongr` as an `AddMonoidHom` from `AddAut`. -/
@[simps]
/--
Definition of `domCongrAut` / `domCongrAut` 的定义

English:
definition domCongrAut
  signature: : AddAut M ->+ Additive (A[M] ≃ₐ[R] A[M]) where
  body: .ofMul (AddMonoidAlgebra.domCongr R A f)
  map_zero' := by ext; simp [AddAut.zero_def]
  map_add' _ _ := by ext; simp [AddAut.add_def]

中文:
定义 domCongrAut
  签名: : AddAut M ->+ 加性 (A[M] ≃ₐ[R] A[M]) where
  定义体: .ofMul (AddMonoidAlgebra.domCongr R A f)
  map_zero' := by ext; simp [AddAut.zero_def]
  map_add' _ _ := by ext; simp [AddAut.add_def]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.domCongr, domCongr
-/
def domCongrAut : AddAut M ->+ Additive (A[M] ≃ₐ[R] A[M]) where
  toFun f := .ofMul (AddMonoidAlgebra.domCongr R A f)
  map_zero' := by ext; simp [AddAut.zero_def]
  map_add' _ _ := by ext; simp [AddAut.add_def]

end lift

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A]

variable (R M) in
/-- `AddMonoidAlgebra.mapAlgEquiv` as an `AddMonoidHom` from `R ≃ₐ[k] R`. -/
@[simps]
/--
Definition of `mapAlgAut` / `mapAlgAut` 的定义

English:
definition mapAlgAut
  signature: : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  body: mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

中文:
定义 mapAlgAut
  签名: : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  定义体: mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

Depends on / 依赖: mapAlgEquiv
-/
def mapAlgAut : (A ≃ₐ[R] A) ->* A[M] ≃ₐ[R] A[M] where
  toFun f := mapAlgEquiv _ _ f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end AddMonoidAlgebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

namespace AddMonoidAlgebra
variable [AddMonoid M]

variable (R A M) in
/-- The algebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
@[simps!]
/--
Definition of `toMultiplicativeAlgEquiv` / `toMultiplicativeAlgEquiv` 的定义

English:
definition toMultiplicativeAlgEquiv
  signature: : AddMonoidAlgebra A M ≃ₐ[R] MonoidAlgebra A (Multiplicative M) where
  body: toMultiplicative A M
  commutes' r := by ext; simp

@[simp]

中文:
定义 toMultiplicativeAlgEquiv
  签名: : 加法幺半群代数 A M ≃ₐ[R] 幺半群代数 A (Multiplicative M) where
  定义体: toMultiplicative A M
  commutes' r := by ext; simp

@[simp]

Depends on / 依赖: toMultiplicative
-/
def toMultiplicativeAlgEquiv : AddMonoidAlgebra A M ≃ₐ[R] MonoidAlgebra A (Multiplicative M) where
  toRingEquiv := toMultiplicative A M
  commutes' r := by ext; simp

@[simp]
/--
lemma `toMultiplicativeAlgEquiv_single` / 引理 `toMultiplicativeAlgEquiv_single`

English:
lemma toMultiplicativeAlgEquiv_single
  given: (m : M) (a : A)
  proof: by ext; simp

中文:
引理 toMultiplicativeAlgEquiv_single
  条件: (m : M) (a : A)
  证明: by ext; simp
-/
lemma toMultiplicativeAlgEquiv_single (m : M) (a : A) :
    toMultiplicativeAlgEquiv R A M (single m a) = .single (.ofAdd m) a := by ext; simp

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [Monoid M]

variable (R A M) in
/-- The algebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
@[simps!]
/--
Definition of `toAdditiveAlgEquiv` / `toAdditiveAlgEquiv` 的定义

English:
definition toAdditiveAlgEquiv
  signature: : MonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A (Additive M) where
  body: toAdditive A M
  commutes' r := by simp [toAdditive]

@[simp]

中文:
定义 toAdditiveAlgEquiv
  签名: : 幺半群代数 A M ≃ₐ[R] 加法幺半群代数 A (加性 M) where
  定义体: toAdditive A M
  commutes' r := by simp [toAdditive]

@[simp]

Depends on / 依赖: toAdditive
-/
def toAdditiveAlgEquiv : MonoidAlgebra A M ≃ₐ[R] AddMonoidAlgebra A (Additive M) where
  toRingEquiv := toAdditive A M
  commutes' r := by simp [toAdditive]

@[simp]
/--
lemma `toAdditiveAlgEquiv_single` / 引理 `toAdditiveAlgEquiv_single`

English:
lemma toAdditiveAlgEquiv_single
  given: (m : M) (a : A)
  proof: by ext; simp

中文:
引理 toAdditiveAlgEquiv_single
  条件: (m : M) (a : A)
  证明: by ext; simp
-/
lemma toAdditiveAlgEquiv_single (m : M) (a : A) :
    toAdditiveAlgEquiv R A M (single m a) = .single (.ofMul m) a := by ext; simp

end MonoidAlgebra
