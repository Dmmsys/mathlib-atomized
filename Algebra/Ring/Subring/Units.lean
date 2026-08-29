/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Order.GroupWithZero.Submonoid
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.Algebra.Group.Submonoid.Units

/-!

# Unit subgroups of a ring

-/

@[expose] public section

/--
Definition of `Units.posSubgroup` / `Units.posSubgroup` 的定义

English:
definition Units.posSubgroup
  signature: (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  body: { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }

@[simp]

中文:
定义 单位群.posSubgroup
  签名: (R : 类型) [半环 R] [线性序 R] [是StrictOrdered环 R]
  定义体: { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }

@[simp]

Depends on / 依赖: Submonoid, Submonoid.pos, Units.coeHom, Units.inv_pos.mpr, carrier, coeHom, inv_mem, inv_pos
-/
def Units.posSubgroup (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }

@[simp]
/--
theorem `Units.mem_posSubgroup` / 定理 `Units.mem_posSubgroup`

English:
theorem Units.mem_posSubgroup
  statement: {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: Iff.rfl

中文:
定理 单位群.mem_posSubgroup
  结论: {R : 类型} [半环 R] [线性序 R] [是StrictOrdered环 R]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Units.mem_posSubgroup {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (u : Rˣ) : u in Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl

namespace RingHom

variable {R T : Type*} [Semiring T]

/--
theorem `isUnit_eqLocusS_mk_iff` / 定理 `isUnit_eqLocusS_mk_iff`

English:
theorem isUnit_eqLocusS_mk_iff
  given: [Semiring R] (f g : R ->+* T) {r : R} (hr : f r = g r)
  proof: MonoidHom.isUnit_eqLocusM_mk_iff ..

中文:
定理 isUnit_eqLocusS_mk_iff
  条件: [半环 R] (f g : R ->+* T) {r : R} (hr : f r = g r)
  证明: MonoidHom.isUnit_eqLocusM_mk_iff ..

Depends on / 依赖: MonoidHom, MonoidHom.isUnit_eqLocusM_mk_iff, isUnit_eqLocusM_mk_iff
-/
theorem isUnit_eqLocusS_mk_iff [Semiring R] (f g : R ->+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocusS g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..

/--
theorem `isUnit_eqLocus_mk_iff` / 定理 `isUnit_eqLocus_mk_iff`

English:
theorem isUnit_eqLocus_mk_iff
  given: [Ring R] (f g : R ->+* T) {r : R} (hr : f r = g r)
  proof: MonoidHom.isUnit_eqLocusM_mk_iff ..

中文:
定理 isUnit_eqLocus_mk_iff
  条件: [环 R] (f g : R ->+* T) {r : R} (hr : f r = g r)
  证明: MonoidHom.isUnit_eqLocusM_mk_iff ..

Depends on / 依赖: MonoidHom, MonoidHom.isUnit_eqLocusM_mk_iff, isUnit_eqLocusM_mk_iff
-/
theorem isUnit_eqLocus_mk_iff [Ring R] (f g : R ->+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] (f g
  body: f.isUnit_eqLocusS_mk_iff g r.prop

中文:
实例 [半环
  签名: R] (f g
  定义体: f.isUnit_eqLocusS_mk_iff g r.prop

Depends on / 依赖: f.isUnit_eqLocusS_mk_iff, isUnit_eqLocusS_mk_iff, r.prop
-/
instance [Semiring R] (f g : R ->+* T) : IsLocalHom (f.eqLocusS g).subtype where
.2 map_nonunit r := f.isUnit_eqLocusS_mk_iff g r.prop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] (f g
  body: f.isUnit_eqLocus_mk_iff g r.prop

中文:
实例 [环
  签名: R] (f g
  定义体: f.isUnit_eqLocus_mk_iff g r.prop

Depends on / 依赖: f.isUnit_eqLocus_mk_iff, isUnit_eqLocus_mk_iff, r.prop
-/
instance [Ring R] (f g : R ->+* T) : IsLocalHom (f.eqLocus g).subtype where
.2 map_nonunit r := f.isUnit_eqLocus_mk_iff g r.prop

end RingHom
