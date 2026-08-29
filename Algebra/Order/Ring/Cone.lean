/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Artie Khovanov
-/
module

public import Mathlib.Algebra.Order.Group.Cone
public import Mathlib.Algebra.Ring.Subsemiring.Order

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone` that encodes axioms of ordered rings
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

@[expose] public section

/--
Definition of `RingConeClass` / `RingConeClass` 的定义

English:
class RingConeClass
  parameters: (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R]
  extends: AddGroupConeClass S R, SubsemiringClass S R
  (no additional axioms)

中文:
类 RingCone类
  参数: (S : 类型) (R : outParam 类型) [环 R] [集合状 S R]
  继承: 加法群锥类 S R, 子半环类 S R
  (无附加公理)
-/
class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R] : Prop
    extends AddGroupConeClass S R, SubsemiringClass S R

/--
Definition of `RingCone` / `RingCone` 的定义

English:
structure RingCone
  parameters: (R : Type*) [Ring R]
  extends: Subsemiring R, AddGroupCone R
  (no additional axioms)

中文:
结构 RingCone
  参数: (R : 类型) [环 R]
  继承: 子半环 R, 加法群锥 R
  (无附加公理)
-/
structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

/-- Interpret a cone in a ring as a cone in the underlying additive group. -/
add_decl_doc RingCone.toAddGroupCone

/--
Instance `RingCone.instSetLike` / 实例 `RingCone.instSetLike`

English:
instance RingCone.instSetLike
  signature: (R : Type*) [Ring R]
  body: C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

中文:
实例 RingCone.instSetLike
  签名: (R : 类型) [环 R]
  定义体: C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

Depends on / 依赖: C.carrier, carrier
-/
instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance (R : Type*) [Ring R] : PartialOrder (RingCone R) := .ofSetLike (RingCone R) R

/--
Instance `RingCone.instRingConeClass` / 实例 `RingCone.instRingConeClass`

English:
instance RingCone.instRingConeClass
  signature: (R : Type*) [Ring R]
  body: C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp]

中文:
实例 RingCone.instRingConeClass
  签名: (R : 类型) [环 R]
  定义体: C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp]

Depends on / 依赖: C.add_mem, add_mem
-/
instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

@[simp]
/--
theorem `RingCone.mem_mk` / 定理 `RingCone.mem_mk`

English:
theorem RingCone.mem_mk
  statement: {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
  proof: .rfl

@[simp]

中文:
定理 RingCone.mem_mk
  结论: {R : 类型} [环 R] {toSubsemiring : 子半环 R}
  证明: .rfl

@[simp]
-/
theorem RingCone.mem_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) {x : R} :
    x in mk toSubsemiring eq_zero_of_mem_of_neg_mem ↔ x in toSubsemiring := .rfl

@[simp]
/--
theorem `RingCone.coe_set_mk` / 定理 `RingCone.coe_set_mk`

English:
theorem RingCone.coe_set_mk
  statement: {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
  proof: rfl

中文:
定理 RingCone.coe_set_mk
  结论: {R : 类型} [环 R] {toSubsemiring : 子半环 R}
  证明: rfl
-/
theorem RingCone.coe_set_mk {R : Type*} [Ring R] {toSubsemiring : Subsemiring R}
    (eq_zero_of_mem_of_neg_mem) :
    (mk toSubsemiring eq_zero_of_mem_of_neg_mem : Set R) = toSubsemiring := rfl

namespace RingCone

variable {T : Type*} [Ring T] [PartialOrder T] [IsOrderedRing T] {a : T}

variable (T) in
/--
Definition of `nonneg` / `nonneg` 的定义

English:
definition nonneg
  signature: : RingCone T where
  body: Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

中文:
定义 nonneg
  签名: : RingCone T where
  定义体: Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

Depends on / 依赖: Subsemiring, Subsemiring.nonneg, nonneg
-/
def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

/--
lemma `nonneg_toSubsemiring` / 引理 `nonneg_toSubsemiring`

English:
lemma nonneg_toSubsemiring
  statement: (nonneg T).toSubsemiring = .nonneg T
  proof: rfl

中文:
引理 nonneg_toSubsemiring
  结论: (nonneg T).toSubsemiring = .nonneg T
  证明: rfl
-/
@[simp] lemma nonneg_toSubsemiring : (nonneg T).toSubsemiring = .nonneg T := rfl
/--
lemma `nonneg_toAddGroupCone` / 引理 `nonneg_toAddGroupCone`

English:
lemma nonneg_toAddGroupCone
  statement: (nonneg T).toAddGroupCone = .nonneg T
  proof: rfl

中文:
引理 nonneg_toAddGroupCone
  结论: (nonneg T).toAddGroupCone = .nonneg T
  证明: rfl
-/
@[simp] lemma nonneg_toAddGroupCone : (nonneg T).toAddGroupCone = .nonneg T := rfl
/--
lemma `mem_nonneg` / 引理 `mem_nonneg`

English:
lemma mem_nonneg
  statement: a in nonneg T ↔ 0 <= a
  proof: Iff.rfl

中文:
引理 mem_nonneg
  结论: a in nonneg T ↔ 0 <= a
  证明: Iff.rfl
-/
@[simp] lemma mem_nonneg : a in nonneg T ↔ 0 <= a := Iff.rfl
/--
lemma `coe_nonneg` / 引理 `coe_nonneg`

English:
lemma coe_nonneg
  statement: nonneg T = {x : T | 0 <= x}
  proof: rfl

中文:
引理 coe_nonneg
  结论: nonneg T = {x : T | 0 <= x}
  证明: rfl
-/
@[simp, norm_cast] lemma coe_nonneg : nonneg T = {x : T | 0 <= x} := rfl

/--
Instance `nonneg.hasMemOrNegMem` / 实例 `nonneg.hasMemOrNegMem`

English:
instance nonneg.hasMemOrNegMem
  signature: {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T]
  body: mem_or_neg_mem (AddGroupCone.nonneg T)

中文:
实例 nonneg.hasMemOrNegMem
  签名: {T : 类型} [环 T] [线性序 T] [是Ordered环 T]
  定义体: mem_or_neg_mem (AddGroupCone.nonneg T)

Depends on / 依赖: AddGroupCone, AddGroupCone.nonneg, mem_or_neg_mem, nonneg
-/
instance nonneg.hasMemOrNegMem {T : Type*} [Ring T] [LinearOrder T] [IsOrderedRing T] :
    HasMemOrNegMem (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

/--
lemma `IsOrderedRing.mkOfCone` / 引理 `IsOrderedRing.mkOfCone`

English:
lemma IsOrderedRing.mkOfCone
  given: [RingConeClass S R]
  proof: .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ in C by simp⟩
  .of_mul_nonneg fun x y xnn ynn => show _ in C by simpa using mul_mem xnn ynn

中文:
引理 是Ordered环.mkOfCone
  条件: [RingCone类 S R]
  证明: .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ in C by simp⟩
  .of_mul_nonneg fun x y xnn ynn => show _ in C by simpa using mul_mem xnn ynn

Depends on / 依赖: mkOfAddGroupCone
-/
lemma IsOrderedRing.mkOfCone [RingConeClass S R] :
    letI _ : PartialOrder R := .mkOfAddGroupCone C
    IsOrderedRing R :=
  letI _ : PartialOrder R := .mkOfAddGroupCone C
  haveI : IsOrderedAddMonoid R := .mkOfCone C
  haveI : ZeroLEOneClass R := ⟨show _ in C by simp⟩
  .of_mul_nonneg fun x y xnn ynn => show _ in C by simpa using mul_mem xnn ynn
