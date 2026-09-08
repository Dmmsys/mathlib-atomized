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

/-- The subgroup of positive units of a linear ordered semiring. -/
/-
**Units.posSubgroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.posSubgroup (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrdere
dRing R] : Subgroup Rˣ
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of positive units of a linear ordered semiring.
-/
def Units.posSubgroup (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }

@[simp]
/-
**Units.mem_posSubgroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.mem_posSubgroup {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOr
deredRing R] (u : Rˣ) : u in Units.posSubgroup R ↔ (0 : R) < u
参数：u : Rˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Units.mem_posSubgroup {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (u : Rˣ) : u ∈ Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl

namespace RingHom

variable {R T : Type*} [Semiring T]

/-
**RingHom.isUnit_eqLocusS_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：isUnit_eqLocusS_mk_iff [Semiring R] (f g : R ->+* T) {r : R} (hr : f r = g
 r) : IsUnit (⟨r, hr⟩ : f.eqLocusS g) ↔ IsUnit r
参数：f g : R ->+* T；hr : f r = g r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.isUnit_eqLocusM_mk_iff`：MonoidHom.isUnit_eqLocusM_mk_iff {N : 
Type*} [Monoid N] (f g : M ->* N) {r : M} (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f
.eqLocusM g) ↔ IsUnit …
-/
theorem isUnit_eqLocusS_mk_iff [Semiring R] (f g : R →+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocusS g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..
/-
**RingHom.isUnit_eqLocus_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：isUnit_eqLocus_mk_iff [Ring R] (f g : R ->+* T) {r : R} (hr : f r = g r) :
 IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r
参数：f g : R ->+* T；hr : f r = g r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.isUnit_eqLocusM_mk_iff`：MonoidHom.isUnit_eqLocusM_mk_iff {N : 
Type*} [Monoid N] (f g : M ->* N) {r : M} (hr : f r = g r) : IsUnit (⟨r, hr⟩ : f
.eqLocusM g) ↔ IsUnit …
-/
theorem isUnit_eqLocus_mk_iff [Ring R] (f g : R →+* T) {r : R} (hr : f r = g r) :
    IsUnit (⟨r, hr⟩ : f.eqLocus g) ↔ IsUnit r :=
  MonoidHom.isUnit_eqLocusM_mk_iff ..
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] (f g : R →+* T) : IsLocalHom (f.eqLocusS g).subtype where
  map_nonunit r := f.isUnit_eqLocusS_mk_iff g r.prop |>.2
/-
**RingHom.** 是 Mathlib 中的一个实例，位于命名空间 `RingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] (f g : R →+* T) : IsLocalHom (f.eqLocus g).subtype where
  map_nonunit r := f.isUnit_eqLocus_mk_iff g r.prop |>.2

end RingHom

