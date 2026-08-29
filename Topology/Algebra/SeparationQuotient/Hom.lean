/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Lift of `MonoidHom M N` to `MonoidHom (SeparationQuotient M) N`

In this file we define the lift of a continuous monoid homomorphism `f` from `M` to `N` to
`SeparationQuotient M`, assuming that `f` maps two inseparable elements to the same element.
-/

@[expose] public section

namespace SeparationQuotient

section Monoid

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- The lift of a monoid hom from `M` to a monoid hom from `SeparationQuotient M`. -/
@[to_additive /-- The lift of an additive monoid hom from `M` to an additive monoid hom from
`SeparationQuotient M`. -/]
/--
Definition of `liftContinuousMonoidHom` / `liftContinuousMonoidHom` 的定义

English:
definition liftContinuousMonoidHom
  signature: [CommMonoid M] [ContinuousMul M] [CommMonoid N]
  body: SeparationQuotient.lift f hf
  map_one' := map_one f
map_mul' := Quotient.ind₂ map_mul f
  continuous_toFun := continuous_lift f.2

@[to_additive (attr := simp)]

中文:
定义 liftContinuousMonoidHom
  签名: [CommMonoid M] [ContinuousMul M] [CommMonoid N]
  定义体: SeparationQuotient.lift f hf
  map_one' := map_one f
map_mul' := Quotient.ind₂ map_mul f
  continuous_toFun := continuous_lift f.2

@[to_additive (attr := simp)]

Depends on / 依赖: SeparationQuotient, SeparationQuotient.lift
-/
noncomputable def liftContinuousMonoidHom [CommMonoid M] [ContinuousMul M] [CommMonoid N]
    (f : ContinuousMonoidHom M N) (hf : forall x y, Inseparable x y -> f x = f y) :
    ContinuousMonoidHom (SeparationQuotient M) N where
  toFun := SeparationQuotient.lift f hf
  map_one' := map_one f
map_mul' := Quotient.ind₂ map_mul f
  continuous_toFun := continuous_lift f.2

@[to_additive (attr := simp)]
/--
theorem `liftContinuousCommMonoidHom_mk` / 定理 `liftContinuousCommMonoidHom_mk`

English:
theorem liftContinuousCommMonoidHom_mk
  statement: [CommMonoid M] [ContinuousMul M] [CommMonoid N]
  proof: rfl

中文:
定理 liftContinuousCommMonoidHom_mk
  结论: [CommMonoid M] [ContinuousMul M] [CommMonoid N]
  证明: rfl
-/
theorem liftContinuousCommMonoidHom_mk [CommMonoid M] [ContinuousMul M] [CommMonoid N]
    (f : ContinuousMonoidHom M N) (hf : forall x y, Inseparable x y -> f x = f y) (x : M) :
    liftContinuousMonoidHom f hf (mk x) = f x := rfl

end Monoid

end SeparationQuotient
