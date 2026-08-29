/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!

# Nontriviality of tensor product of algebras

This file contains some more results on nontriviality of tensor product of algebras.

-/

public section

open TensorProduct

namespace Algebra.TensorProduct

/--
theorem `nontrivial_of_algebraMap_injective_of_isDomain` / 定理 `nontrivial_of_algebraMap_injective_of_isDomain`

English:
theorem nontrivial_of_algebraMap_injective_of_isDomain
  proof: by
  have := ha.isDomain _
  let FR := FractionRing R
  let FA := FractionRing A
  let FB := FractionRing B
  let fa : FR ->ₐ[R] FA := IsFractionRing.liftAlgHom (g := Algebra.ofId R FA)
    ((IsFractionRing.injective A FA).comp ha)
  let fb : FR ->ₐ[R] FB := IsFractionRing.liftAlgHom (g := Algebra.o

中文:
定理 nontrivial_of_algebraMap_injective_of_isDomain
  证明: by
  have := ha.isDomain _
  let FR := FractionRing R
  let FA := FractionRing A
  let FB := FractionRing B
  let fa : FR ->ₐ[R] FA := IsFractionRing.liftAlgHom (g := Algebra.ofId R FA)
    ((IsFractionRing.injective A FA).comp ha)
  let fb : FR ->ₐ[R] FB := IsFractionRing.liftAlgHom (g := Algebra.o

Depends on / 依赖: Algebra, Algebra.TensorProduct.mapOfCompatibleSMul, Algebra.ofId, CompatibleSMul, CompatibleSMul.isScalarTower, FractionRing, IsFractionRing, IsFractionRing.injective, IsFractionRing.liftAlgHom, TensorProduct, algebraize_only, fa.toRingHom, fb.toRingHom, ha.isDomain, injective, isDomain, isScalarTower, liftAlgHom, mapOfCompatibleSMul, toRingHom
-/
theorem nontrivial_of_algebraMap_injective_of_isDomain
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B))
    [IsDomain A] [IsDomain B] : Nontrivial (A otimes[R] B) := by
  have := ha.isDomain _
  let FR := FractionRing R
  let FA := FractionRing A
  let FB := FractionRing B
  let fa : FR ->ₐ[R] FA := IsFractionRing.liftAlgHom (g := Algebra.ofId R FA)
    ((IsFractionRing.injective A FA).comp ha)
  let fb : FR ->ₐ[R] FB := IsFractionRing.liftAlgHom (g := Algebra.ofId R FB)
    ((IsFractionRing.injective B FB).comp hb)
  algebraize_only [fa.toRingHom, fb.toRingHom]
  let : CompatibleSMul FR R FA FB := CompatibleSMul.isScalarTower
.comp exact Algebra.TensorProduct.mapOfCompatibleSMul FR R R FA FB
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A FA) (IsScalarTower.toAlgHom R B FB))
.toRingHom.domain_nontrivial

end Algebra.TensorProduct
