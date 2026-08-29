/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide the structure `GroupCone` and the predicate `IsMaxCone` that encode
the axioms of ordered groups in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

@[expose] public section

/--
Definition of `AddGroupConeClass` / `AddGroupConeClass` 的定义

English:
class AddGroupConeClass
  parameters: (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G]
  extends: AddSubmonoidClass S G
  axioms and operations (1):
    - eq_zero_of_mem_of_neg_mem({C : S} {a : G}) : a in C -> -a in C -> a = 0

中文:
类 加法群锥类
  参数: (S : 类型) (G : outParam 类型) [加法交换群 G] [集合状 S G]
  继承: 加法子幺半群类 S G
  公理与运算 (1 个):
    - eq_zero_of_mem_of_neg_mem({C : S} {a : G}) : a in C -> -a in C -> a = 0
-/
class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a in C -> -a in C -> a = 0

/-- `GroupConeClass S G` says that `S` is a type of cones in `G`. -/
@[to_additive]
/--
Definition of `GroupConeClass` / `GroupConeClass` 的定义

English:
class GroupConeClass
  parameters: (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G]
  extends: SubmonoidClass S G
  axioms and operations (1):
    - eq_one_of_mem_of_inv_mem({C : S} {a : G}) : a in C -> a⁻¹ in C -> a = 1

中文:
类 群锥类
  参数: (S : 类型) (G : outParam 类型) [交换群 G] [集合状 S G]
  继承: 子幺半群类 S G
  公理与运算 (1 个):
    - eq_one_of_mem_of_inv_mem({C : S} {a : G}) : a in C -> a⁻¹ in C -> a = 1
-/
class GroupConeClass (S : Type*) (G : outParam Type*) [CommGroup G] [SetLike S G] : Prop
    extends SubmonoidClass S G where
  eq_one_of_mem_of_inv_mem {C : S} {a : G} : a in C -> a⁻¹ in C -> a = 1

export GroupConeClass (eq_one_of_mem_of_inv_mem)
export AddGroupConeClass (eq_zero_of_mem_of_neg_mem)

/--
Definition of `AddGroupCone` / `AddGroupCone` 的定义

English:
structure AddGroupCone
  parameters: (G : Type*) [AddCommGroup G]
  extends: AddSubmonoid G
  axioms and operations (1):
    - eq_zero_of_mem_of_neg_mem'({a}) : a in carrier -> -a in carrier -> a = 0

中文:
结构 加法群锥
  参数: (G : 类型) [加法交换群 G]
  继承: 加法子幺半群 G
  公理与运算 (1 个):
    - eq_zero_of_mem_of_neg_mem'({a}) : a in carrier -> -a in carrier -> a = 0
-/
structure AddGroupCone (G : Type*) [AddCommGroup G] extends AddSubmonoid G where
  eq_zero_of_mem_of_neg_mem' {a} : a in carrier -> -a in carrier -> a = 0

/-- A (positive) cone in an abelian group is a submonoid that
does not contain both `a` and `a⁻¹` for any non-identity `a`.
This is equivalent to being the set of elements that are at least 1 in
some order making the group into a partially ordered group. -/
@[to_additive]
/--
Definition of `GroupCone` / `GroupCone` 的定义

English:
structure GroupCone
  parameters: (G : Type*) [CommGroup G]
  extends: Submonoid G
  axioms and operations (1):
    - eq_one_of_mem_of_inv_mem'({a}) : a in carrier -> a⁻¹ in carrier -> a = 1

中文:
结构 群锥
  参数: (G : 类型) [交换群 G]
  继承: 子幺半群 G
  公理与运算 (1 个):
    - eq_one_of_mem_of_inv_mem'({a}) : a in carrier -> a⁻¹ in carrier -> a = 1
-/
structure GroupCone (G : Type*) [CommGroup G] extends Submonoid G where
  eq_one_of_mem_of_inv_mem' {a} : a in carrier -> a⁻¹ in carrier -> a = 1

@[to_additive]
/--
Instance `GroupCone.instSetLike` / 实例 `GroupCone.instSetLike`

English:
instance GroupCone.instSetLike
  signature: (G : Type*) [CommGroup G]
  body: C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]

中文:
实例 群锥.instSetLike
  签名: (G : 类型) [交换群 G]
  定义体: C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]

Depends on / 依赖: C.carrier, carrier
-/
instance GroupCone.instSetLike (G : Type*) [CommGroup G] : SetLike (GroupCone G) G where
  coe C := C.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

@[to_additive]
instance (G : Type*) [CommGroup G] : PartialOrder (GroupCone G) := .ofSetLike (GroupCone G) G

@[to_additive]
/--
Instance `GroupCone.instGroupConeClass` / 实例 `GroupCone.instGroupConeClass`

English:
instance GroupCone.instGroupConeClass
  signature: (G : Type*) [CommGroup G]
  body: C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier -> coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier -> coe, as_prefix coe)

中文:
实例 群锥.instGroupConeClass
  签名: (G : 类型) [交换群 G]
  定义体: C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier -> coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier -> coe, as_prefix coe)

Depends on / 依赖: C.mul_mem, mul_mem
-/
instance GroupCone.instGroupConeClass (G : Type*) [CommGroup G] :
    GroupConeClass (GroupCone G) G where
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_one_of_mem_of_inv_mem {C} := C.eq_one_of_mem_of_inv_mem'

initialize_simps_projections GroupCone (carrier -> coe, as_prefix coe)
initialize_simps_projections AddGroupCone (carrier -> coe, as_prefix coe)

namespace GroupCone
variable {H : Type*} [CommGroup H] [PartialOrder H] [IsOrderedMonoid H] {a : H}

variable (H) in
/-- The cone of elements that are at least 1. -/
@[to_additive /-- The cone of non-negative elements. -/]
/--
Definition of `oneLE` / `oneLE` 的定义

English:
definition oneLE
  signature: : GroupCone H where
  body: Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp)]

中文:
定义 oneLE
  签名: : 群锥 H where
  定义体: Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.oneLE
-/
def oneLE : GroupCone H where
  __ := Submonoid.oneLE H
  eq_one_of_mem_of_inv_mem' {a} := by simpa using ge_antisymm

@[to_additive (attr := simp)]
/--
lemma `oneLE_toSubmonoid` / 引理 `oneLE_toSubmonoid`

English:
lemma oneLE_toSubmonoid
  statement: (oneLE H).toSubmonoid = .oneLE H
  proof: rfl
@[to_additive (attr := simp)]

中文:
引理 oneLE_toSubmonoid
  结论: (oneLE H).toSubmonoid = .oneLE H
  证明: rfl
@[to_additive (attr := simp)]
-/
lemma oneLE_toSubmonoid : (oneLE H).toSubmonoid = .oneLE H := rfl
@[to_additive (attr := simp)]
/--
lemma `mem_oneLE` / 引理 `mem_oneLE`

English:
lemma mem_oneLE
  statement: a in oneLE H ↔ 1 <= a
  proof: Iff.rfl
@[to_additive (attr := simp, norm_cast)]

中文:
引理 mem_oneLE
  结论: a in oneLE H ↔ 1 <= a
  证明: Iff.rfl
@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
lemma mem_oneLE : a in oneLE H ↔ 1 <= a := Iff.rfl
@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_oneLE` / 引理 `coe_oneLE`

English:
lemma coe_oneLE
  statement: oneLE H = {x : H | 1 <= x}
  proof: rfl

@[to_additive]

中文:
引理 coe_oneLE
  结论: oneLE H = {x : H | 1 <= x}
  证明: rfl

@[to_additive]
-/
lemma coe_oneLE : oneLE H = {x : H | 1 <= x} := rfl

@[to_additive]
/--
Instance `oneLE.hasMemOrInvMem` / 实例 `oneLE.hasMemOrInvMem`

English:
instance oneLE.hasMemOrInvMem
  signature: {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H]
  body: by simpa using le_total 1

中文:
实例 oneLE.hasMemOrInvMem
  签名: {H : 类型} [交换群 H] [线性序 H] [是Ordered幺半群 H]
  定义体: by simpa using le_total 1

Depends on / 依赖: le_total
-/
instance oneLE.hasMemOrInvMem {H : Type*} [CommGroup H] [LinearOrder H] [IsOrderedMonoid H] :
    HasMemOrInvMem (oneLE H) where
  mem_or_inv_mem := by simpa using le_total 1

end GroupCone

variable {S G : Type*} [CommGroup G] [SetLike S G] (C : S)

/-- Construct a partial order by designating a cone in an abelian group. -/
@[to_additive /-- Construct a partial order by designating a cone in an abelian group. -/]
/--
Definition of `PartialOrder.mkOfGroupCone` / `PartialOrder.mkOfGroupCone` 的定义

English:
abbreviation PartialOrder.mkOfGroupCone
  signature: [GroupConeClass S G]
  body: b / a in C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]

中文:
缩写 偏序.mkOfGroupCone
  签名: [群锥类 S G]
  定义体: b / a in C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
-/
abbrev PartialOrder.mkOfGroupCone [GroupConeClass S G] : PartialOrder G where
  le a b := b / a in C
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using eq_one_of_mem_of_inv_mem nab (by simpa using nba)

@[to_additive (attr := simp)]
/--
lemma `PartialOrder.mkOfGroupCone_le_iff` / 引理 `PartialOrder.mkOfGroupCone_le_iff`

English:
lemma PartialOrder.mkOfGroupCone_le_iff
  statement: {S G : Type*} [CommGroup G] [SetLike S G]
  proof: Iff.rfl

中文:
引理 偏序.mkOfGroupCone_le_iff
  结论: {S G : 类型} [交换群 G] [集合状 S G]
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma PartialOrder.mkOfGroupCone_le_iff {S G : Type*} [CommGroup G] [SetLike S G]
    [GroupConeClass S G] {C : S} {a b : G} :
    (mkOfGroupCone C).le a b ↔ b / a in C := Iff.rfl

/-- Construct a linear order by designating a maximal cone in an abelian group. -/
@[to_additive /-- Construct a linear order by designating a maximal cone in an abelian group. -/]
/--
Definition of `LinearOrder.mkOfGroupCone` / `LinearOrder.mkOfGroupCone` 的定义

English:
abbreviation LinearOrder.mkOfGroupCone
  body: PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

中文:
缩写 线性序.mkOfGroupCone
  定义体: PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

Depends on / 依赖: PartialOrder, PartialOrder.mkOfGroupCone, mkOfGroupCone
-/
abbrev LinearOrder.mkOfGroupCone
    [GroupConeClass S G] [HasMemOrInvMem C] [DecidablePred (· in C)] : LinearOrder G where
  __ := PartialOrder.mkOfGroupCone C
  le_total a b := by simpa using mem_or_inv_mem C (b / a)
  toDecidableLE _ := _

/-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/
@[to_additive
  /-- Construct a partially ordered abelian group by designating a cone in an abelian group. -/]
/--
lemma `IsOrderedMonoid.mkOfCone` / 引理 `IsOrderedMonoid.mkOfCone`

English:
lemma IsOrderedMonoid.mkOfCone
  given: [GroupConeClass S G]
  proof: PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c => by simpa [· <= ·] using nab }

中文:
引理 是Ordered幺半群.mkOfCone
  条件: [群锥类 S G]
  证明: PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c => by simpa [· <= ·] using nab }

Depends on / 依赖: PartialOrder, PartialOrder.mkOfGroupCone, mkOfGroupCone
-/
lemma IsOrderedMonoid.mkOfCone [GroupConeClass S G] :
    let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
    IsOrderedMonoid G :=
  let _ : PartialOrder G := PartialOrder.mkOfGroupCone C
  { mul_le_mul_left := fun a b nab c => by simpa [· <= ·] using nab }
