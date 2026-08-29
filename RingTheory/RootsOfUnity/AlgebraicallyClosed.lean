/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is a separably closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characteristic zero,
this hold for all `n ≠ 0`.
-/

public section

variable (F : Type*) [Field F] (n k : Nat) [NeZero (n : F)]

namespace IsSepClosed

variable [IsSepClosed F]

/--
Instance `hasEnoughRootsOfUnity` / 实例 `hasEnoughRootsOfUnity`

English:
instance hasEnoughRootsOfUnity
  signature: : HasEnoughRootsOfUnity F n where
  body: by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {n} F fun _ h _ => Set.mem_singleton_iff.mp h ▸ ‹NeZero (n : F)›
    exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) F _ rfl (NeZero.ne _)
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUn

中文:
实例 hasEnoughRootsOfUnity
  签名: : 有EnoughRootsOfUnity F n where
  定义体: by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {n} F fun _ h _ => Set.mem_singleton_iff.mp h ▸ ‹NeZero (n : F)›
    exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) F _ rfl (NeZero.ne _)
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUn

Depends on / 依赖: IsCyclotomicExtension, IsCyclotomicExtension.exists_isPrimitiveRoot, NeZero, NeZero.ne, Set.mem_singleton_iff.mp, exists_isPrimitiveRoot, isCyclic, isCyclotomicExtension, mem_singleton_iff, of_neZero_natCast, rootsOfUnity, rootsOfUnity.isCyclic
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {n} F fun _ h _ => Set.mem_singleton_iff.mp h ▸ ‹NeZero (n : F)›
    exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) F _ rfl (NeZero.ne _)
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n

/--
Instance `hasEnoughRootsOfUnity_pow` / 实例 `hasEnoughRootsOfUnity_pow`

English:
instance hasEnoughRootsOfUnity_pow
  signature: : HasEnoughRootsOfUnity F (n ^ k)
  body: have : NeZero ((n ^ k : Nat) : F) := by exact_mod_cast ‹NeZero (n : F)›.pow
  inferInstance

中文:
实例 hasEnoughRootsOfUnity_pow
  签名: : 有EnoughRootsOfUnity F (n ^ k)
  定义体: have : NeZero ((n ^ k : Nat) : F) := by exact_mod_cast ‹NeZero (n : F)›.pow
  inferInstance

Depends on / 依赖: NeZero
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity F (n ^ k) :=
  have : NeZero ((n ^ k : Nat) : F) := by exact_mod_cast ‹NeZero (n : F)›.pow
  inferInstance

end IsSepClosed

namespace AlgebraicClosure

/--
Instance `hasEnoughRootsOfUnity` / 实例 `hasEnoughRootsOfUnity`

English:
instance hasEnoughRootsOfUnity
  signature: : HasEnoughRootsOfUnity (AlgebraicClosure F) n
  body: have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

中文:
实例 hasEnoughRootsOfUnity
  签名: : 有EnoughRootsOfUnity (代数闭包 F) n
  定义体: have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

Depends on / 依赖: AlgebraicClosure, NeZero, algebraMap, injective, of_injective
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (AlgebraicClosure F) n :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

/--
Instance `hasEnoughRootsOfUnity_pow` / 实例 `hasEnoughRootsOfUnity_pow`

English:
instance hasEnoughRootsOfUnity_pow
  signature: : HasEnoughRootsOfUnity (AlgebraicClosure F) (n ^ k)
  body: have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

中文:
实例 hasEnoughRootsOfUnity_pow
  签名: : 有EnoughRootsOfUnity (代数闭包 F) (n ^ k)
  定义体: have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

Depends on / 依赖: AlgebraicClosure, NeZero, algebraMap, injective, of_injective
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (AlgebraicClosure F) (n ^ k) :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

end AlgebraicClosure

namespace SeparableClosure

/--
Instance `hasEnoughRootsOfUnity` / 实例 `hasEnoughRootsOfUnity`

English:
instance hasEnoughRootsOfUnity
  signature: : HasEnoughRootsOfUnity (SeparableClosure F) n
  body: have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

中文:
实例 hasEnoughRootsOfUnity
  签名: : 有EnoughRootsOfUnity (可分闭包 F) n
  定义体: have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

Depends on / 依赖: NeZero, SeparableClosure, algebraMap, injective, of_injective
-/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (SeparableClosure F) n :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

/--
Instance `hasEnoughRootsOfUnity_pow` / 实例 `hasEnoughRootsOfUnity_pow`

English:
instance hasEnoughRootsOfUnity_pow
  signature: : HasEnoughRootsOfUnity (SeparableClosure F) (n ^ k)
  body: have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

中文:
实例 hasEnoughRootsOfUnity_pow
  签名: : 有EnoughRootsOfUnity (可分闭包 F) (n ^ k)
  定义体: have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

Depends on / 依赖: NeZero, SeparableClosure, algebraMap, injective, of_injective
-/
instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (SeparableClosure F) (n ^ k) :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

end SeparableClosure
