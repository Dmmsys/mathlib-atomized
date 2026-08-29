/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, David Ledvinka
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Monoid

/-!
# Topological properties of units

This file contains lemmas about the topology of units in topological monoids,
including results about submonoid units and units of product spaces.
-/

@[expose] public section

open Units

/-- If a submonoid is open in a topological monoid, then its units form an open subset
of the units of the monoid. -/
@[to_additive /-- If a submonoid is open in a topological additive monoid,
then its additive units form an open subset of the additive units of the monoid. -/]
/--
lemma `Submonoid.isOpen_units` / 引理 `Submonoid.isOpen_units`

English:
lemma Submonoid.isOpen_units
  statement: {M : Type*} [TopologicalSpace M] [Monoid M]
  proof: (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

中文:
引理 Submonoid.isOpen_units
  结论: {M : 类型} [TopologicalSpace M] [Monoid M]
  证明: (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

Depends on / 依赖: Units.continuous_coe_inv, Units.continuous_val, continuous_coe_inv, continuous_val, hU.preimage, preimage
-/
lemma Submonoid.isOpen_units {M : Type*} [TopologicalSpace M] [Monoid M]
    {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)

/-- The isomorphism of topological groups between the units of a product and
the product of the units. -/
@[to_additive /-- The isomorphism of topological additive groups between the additive units of a
product and the product of the additive units. -/]
/--
Definition of `ContinuousMulEquiv.piUnits` / `ContinuousMulEquiv.piUnits` 的定义

English:
definition ContinuousMulEquiv.piUnits
  signature: {ι : Type*}
  body: MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ => Units.continuous_iff.mpr
.comp Units.continuous_val, ⟨continuous_apply _
.comp Units.continuous_coe_inv⟩ continuous_apply _
  continuous_invFun := Units.continuous_iff.mpr
⟨continuous_pi fun _ => Units.continuous_val.comp continuous_apply

中文:
定义 ContinuousMulEquiv.piUnits
  签名: {ι : 类型}
  定义体: MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ => Units.continuous_iff.mpr
.comp Units.continuous_val, ⟨continuous_apply _
.comp Units.continuous_coe_inv⟩ continuous_apply _
  continuous_invFun := Units.continuous_iff.mpr
⟨continuous_pi fun _ => Units.continuous_val.comp continuous_apply

Depends on / 依赖: MulEquiv, MulEquiv.piUnits, piUnits
-/
def ContinuousMulEquiv.piUnits {ι : Type*}
    {M : ι -> Type*} [(i : ι) -> Monoid (M i)] [(i : ι) -> TopologicalSpace (M i)] :
    (Π i, M i)ˣ ≃ₜ* Π i, (M i)ˣ where
  __ := MulEquiv.piUnits
  continuous_toFun := continuous_pi fun _ => Units.continuous_iff.mpr
.comp Units.continuous_val, ⟨continuous_apply _
.comp Units.continuous_coe_inv⟩ continuous_apply _
  continuous_invFun := Units.continuous_iff.mpr
⟨continuous_pi fun _ => Units.continuous_val.comp continuous_apply _,
continuous_pi fun _ => Units.continuous_coe_inv.comp continuous_apply _⟩

namespace Units

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Monoid M] [Monoid N]

/-- Any `ContinuousMulEquiv` induces a `ContinuousMulEquiv` on units. -/
@[simps! apply]
/--
Definition of `mapContinuousMulEquiv` / `mapContinuousMulEquiv` 的定义

English:
definition mapContinuousMulEquiv
  signature: (f : M ≃ₜ* N)
  body: { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]

中文:
定义 mapContinuousMulEquiv
  签名: (f : M ≃ₜ* N)
  定义体: { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]

Depends on / 依赖: Units.mapEquiv, continuous, continuous_invFun, continuous_toFun, f.continuous.units_map, f.symm.continuous.units_map, mapEquiv, units_map
-/
def mapContinuousMulEquiv (f : M ≃ₜ* N) : Mˣ ≃ₜ* Nˣ :=
  { __ := Units.mapEquiv f
    continuous_toFun := f.continuous.units_map _
    continuous_invFun := f.symm.continuous.units_map _ }

@[simp]
/--
theorem `symm_mapContinuousMulEquiv` / 定理 `symm_mapContinuousMulEquiv`

English:
theorem symm_mapContinuousMulEquiv
  given: (f : M ≃ₜ* N)
  proof: rfl

@[simp]

中文:
定理 symm_mapContinuousMulEquiv
  条件: (f : M ≃ₜ* N)
  证明: rfl

@[simp]
-/
theorem symm_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f).symm = mapContinuousMulEquiv f.symm := rfl

@[simp]
/--
theorem `toMulEquiv_mapContinuousMulEquiv` / 定理 `toMulEquiv_mapContinuousMulEquiv`

English:
theorem toMulEquiv_mapContinuousMulEquiv
  given: (f : M ≃ₜ* N)
  proof: rfl

中文:
定理 toMulEquiv_mapContinuousMulEquiv
  条件: (f : M ≃ₜ* N)
  证明: rfl
-/
theorem toMulEquiv_mapContinuousMulEquiv (f : M ≃ₜ* N) :
    (mapContinuousMulEquiv f : Mˣ ≃* Nˣ) = mapEquiv f := rfl

end Units
