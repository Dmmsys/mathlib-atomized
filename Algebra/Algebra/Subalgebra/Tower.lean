/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Subalgebras in towers of algebras

In this file we prove facts about subalgebras in towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

## Main results

* `IsScalarTower.Subalgebra`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S/S₀` is a tower
* `IsScalarTower.Subalgebra'`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S₀/R` is a tower
* `Subalgebra.restrictScalars`: turn an `S`-subalgebra of `A` into an `R`-subalgebra of `A`,
  given that `A/S/R` is a tower

-/

@[expose] public section


open scoped Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {A}

/--
theorem `lmul_algebraMap` / 定理 `lmul_algebraMap`

English:
theorem lmul_algebraMap
  given: (x : R)
  statement: Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x
  proof: Eq.symm LinearMap.ext smul_def x

中文:
定理 lmul_algebraMap
  条件: (x : R)
  结论: 代数.lmul R A (algebraMap R A x) = 代数.lsmul R R A x
  证明: Eq.symm LinearMap.ext smul_def x

Depends on / 依赖: Eq.symm, LinearMap, LinearMap.ext, smul_def
-/
theorem lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x :=
Eq.symm LinearMap.ext smul_def x

end Algebra

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A]
variable [Algebra R S] [Algebra S A]

/--
Instance `subalgebra` / 实例 `subalgebra`

English:
instance subalgebra
  signature: (S₀ : Subalgebra R S)
  body: of_algebraMap_eq fun _ => rfl

中文:
实例 subalgebra
  签名: (S₀ : 子代数 R S)
  定义体: of_algebraMap_eq fun _ => rfl

Depends on / 依赖: of_algebraMap_eq
-/
instance subalgebra (S₀ : Subalgebra R S) : IsScalarTower S₀ S A :=
  of_algebraMap_eq fun _ => rfl

variable [Algebra R A] [IsScalarTower R S A]

/--
Instance `subalgebra'` / 实例 `subalgebra'`

English:
instance subalgebra'
  signature: (S₀ : Subalgebra R S)
  body: @IsScalarTower.of_algebraMap_eq R S₀ A _ _ _ _ _ _ fun _ =>
    (IsScalarTower.algebraMap_apply R S A _ :)

中文:
实例 subalgebra'
  签名: (S₀ : 子代数 R S)
  定义体: @IsScalarTower.of_algebraMap_eq R S₀ A _ _ _ _ _ _ fun _ =>
    (IsScalarTower.algebraMap_apply R S A _ :)

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_eq, algebraMap_apply, of_algebraMap_eq
-/
instance subalgebra' (S₀ : Subalgebra R S) : IsScalarTower R S₀ A :=
  @IsScalarTower.of_algebraMap_eq R S₀ A _ _ _ _ _ _ fun _ =>
    (IsScalarTower.algebraMap_apply R S A _ :)

end Semiring

end IsScalarTower

namespace Subalgebra

open IsScalarTower

section Semiring

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (U : Subalgebra S A)
  body: { U with
    algebraMap_mem' := fun x => by
      rw [IsScalarTower.algebraMap_apply R S A]
      exact U.algebraMap_mem _ }

@[simp]

中文:
定义 restrictScalars
  签名: (U : 子代数 S A)
  定义体: { U with
    algebraMap_mem' := fun x => by
      rw [IsScalarTower.algebraMap_apply R S A]
      exact U.algebraMap_mem _ }

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, U.algebraMap_mem, algebraMap_apply, algebraMap_mem
-/
def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebraMap_mem' := fun x => by
      rw [IsScalarTower.algebraMap_apply R S A]
      exact U.algebraMap_mem _ }

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: {U : Subalgebra S A}
  statement: (restrictScalars R U : Set A) = (U : Set A)
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: {U : 子代数 S A}
  结论: (restrictScalars R U : 集合 A) = (U : 集合 A)
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars {U : Subalgebra S A} : (restrictScalars R U : Set A) = (U : Set A) :=
  rfl

@[simp]
/--
theorem `restrictScalars_top` / 定理 `restrictScalars_top`

English:
theorem restrictScalars_top
  statement: restrictScalars R (⊤ : Subalgebra S A) = ⊤
  proof: -- Porting note: `by dsimp` used to be `rfl`. This appears to work but causes
  -- this theorem to timeout in the kernel after minutes of thinking.
SetLike.coe_injective by dsimp

@[simp]

中文:
定理 restrictScalars_top
  结论: restrictScalars R (⊤ : 子代数 S A) = ⊤
  证明: -- Porting note: `by dsimp` used to be `rfl`. This appears to work but causes
  -- this theorem to timeout in the kernel after minutes of thinking.
SetLike.coe_injective by dsimp

@[simp]
-/
theorem restrictScalars_top : restrictScalars R (⊤ : Subalgebra S A) = ⊤ :=
  -- Porting note: `by dsimp` used to be `rfl`. This appears to work but causes
  -- this theorem to timeout in the kernel after minutes of thinking.
SetLike.coe_injective by dsimp

@[simp]
/--
theorem `restrictScalars_toSubmodule` / 定理 `restrictScalars_toSubmodule`

English:
theorem restrictScalars_toSubmodule
  given: {U : Subalgebra S A}
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 restrictScalars_toSubmodule
  条件: {U : 子代数 S A}
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem restrictScalars_toSubmodule {U : Subalgebra S A} :
    Subalgebra.toSubmodule (U.restrictScalars R) = U.toSubmodule.restrictScalars R :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `mem_restrictScalars` / 定理 `mem_restrictScalars`

English:
theorem mem_restrictScalars
  given: {U : Subalgebra S A} {x : A}
  statement: x in restrictScalars R U ↔ x in U
  proof: Iff.rfl

中文:
定理 mem_restrictScalars
  条件: {U : 子代数 S A} {x : A}
  结论: x in restrictScalars R U ↔ x in U
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_restrictScalars {U : Subalgebra S A} {x : A} : x in restrictScalars R U ↔ x in U :=
  Iff.rfl

/--
theorem `restrictScalars_injective` / 定理 `restrictScalars_injective`

English:
theorem restrictScalars_injective
  proof: fun U V H =>
  ext fun x => by rw [← mem_restrictScalars R, H, mem_restrictScalars]

中文:
定理 restrictScalars_injective
  证明: fun U V H =>
  ext fun x => by rw [← mem_restrictScalars R, H, mem_restrictScalars]
-/
theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : Subalgebra S A -> Subalgebra R A) := fun U V H =>
  ext fun x => by rw [← mem_restrictScalars R, H, mem_restrictScalars]

/-- Produces an `R`-algebra map from `U.restrictScalars R` given an `S`-algebra map from `U`.

This is a special case of `AlgHom.restrictScalars` that can be helpful in elaboration. -/
@[simp]
/--
Definition of `ofRestrictScalars` / `ofRestrictScalars` 的定义

English:
definition ofRestrictScalars
  signature: (U : Subalgebra S A) (f : U ->ₐ[S] B)
  body: f.restrictScalars R

中文:
定义 ofRestrictScalars
  签名: (U : 子代数 S A) (f : U ->ₐ[S] B)
  定义体: f.restrictScalars R

Depends on / 依赖: f.restrictScalars, restrictScalars
-/
def ofRestrictScalars (U : Subalgebra S A) (f : U ->ₐ[S] B) : U.restrictScalars R ->ₐ[R] B :=
  f.restrictScalars R

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A)

@[simp]
/--
theorem `restrictScalars_one` / 定理 `restrictScalars_one`

English:
theorem restrictScalars_one
  proof: by
  ext; simp

中文:
定理 restrictScalars_one
  证明: by
  ext; simp
-/
theorem restrictScalars_one :
    Submodule.restrictScalars R (1 : Submodule S A) = Subalgebra.toSubmodule S := by
  ext; simp

/--
theorem `codisjoint_one_iff` / 定理 `codisjoint_one_iff`

English:
theorem codisjoint_one_iff
  given: (I : Ideal A)
  proof: by
  simp [← Submodule.codisjoint_restrictScalars_iff R]

中文:
定理 codisjoint_one_iff
  条件: (I : 理想 A)
  证明: by
  simp [← Submodule.codisjoint_restrictScalars_iff R]

Depends on / 依赖: Submodule, Submodule.codisjoint_restrictScalars_iff, codisjoint_restrictScalars_iff
-/
theorem codisjoint_one_iff (I : Ideal A) :
    Codisjoint (1 : Submodule S A) (I.restrictScalars S) ↔
      Codisjoint (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  simp [← Submodule.codisjoint_restrictScalars_iff R]

/--
theorem `disjoint_one_iff` / 定理 `disjoint_one_iff`

English:
theorem disjoint_one_iff
  given: (I : Ideal A)
  proof: by
  simp [← Submodule.disjoint_restrictScalars_iff R]

@[simp]

中文:
定理 disjoint_one_iff
  条件: (I : 理想 A)
  证明: by
  simp [← Submodule.disjoint_restrictScalars_iff R]

@[simp]

Depends on / 依赖: Submodule, Submodule.disjoint_restrictScalars_iff, disjoint_restrictScalars_iff
-/
theorem disjoint_one_iff (I : Ideal A) :
    Disjoint (1 : Submodule S A) (I.restrictScalars S) ↔
      Disjoint (Subalgebra.toSubmodule S) (I.restrictScalars R) := by
  simp [← Submodule.disjoint_restrictScalars_iff R]

@[simp]
/--
lemma `range_isScalarTower_toAlgHom` / 引理 `range_isScalarTower_toAlgHom`

English:
lemma range_isScalarTower_toAlgHom
  proof: by
  ext
  simp [algebraMap_eq]

中文:
引理 range_isScalarTower_toAlgHom
  证明: by
  ext
  simp [algebraMap_eq]

Depends on / 依赖: algebraMap_eq
-/
lemma range_isScalarTower_toAlgHom :
    LinearMap.range (IsScalarTower.toAlgHom R S A : S ->ₗ[R] A) = Subalgebra.toSubmodule S := by
  ext
  simp [algebraMap_eq]

end CommSemiring

end Subalgebra

namespace IsScalarTower

open Subalgebra

variable [CommSemiring R] [CommSemiring S] [CommSemiring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/--
theorem `adjoin_range_toAlgHom` / 定理 `adjoin_range_toAlgHom`

English:
theorem adjoin_range_toAlgHom
  given: (t : Set A)
  proof: Subalgebra.ext fun z =>
    show z in Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) union t : Set A) ↔
         z in Subsemiring.closure (Set.range (algebraMap S A) union t : Set A) by simp

中文:
定理 adjoin_range_toAlgHom
  条件: (t : 集合 A)
  证明: Subalgebra.ext fun z =>
    show z in Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) union t : Set A) ↔
         z in Subsemiring.closure (Set.range (algebraMap S A) union t : Set A) by simp

Depends on / 依赖: Set.range, Subalgebra, Subalgebra.ext, Subsemiring, Subsemiring.closure, algebraMap, closure, toAlgHom
-/
theorem adjoin_range_toAlgHom (t : Set A) :
    (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R =
      (Algebra.adjoin S t).restrictScalars R :=
  Subalgebra.ext fun z =>
    show z in Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) union t : Set A) ↔
         z in Subsemiring.closure (Set.range (algebraMap S A) union t : Set A) by simp

end IsScalarTower
