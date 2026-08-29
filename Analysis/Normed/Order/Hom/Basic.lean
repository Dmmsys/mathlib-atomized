/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Hom.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Constructing (semi)normed groups from (semi)normed homs

This file defines constructions that upgrade `(Comm)Group` to `(Semi)Normed(Comm)Group`
using a `Group(Semi)normClass` when the codomain is the reals.

See `Mathlib/Analysis/Normed/Order/Hom/Ultra.lean` for further upgrades to nonarchimedean normed
groups.
-/

public section

variable {F α : Type*} [FunLike F α Real]

/-- Constructs a `SeminormedGroup` structure from a `GroupSeminormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `SeminormedAddGroup` structure from an `AddGroupSeminormClass` on an
`AddGroup`. -/]
/--
Definition of `GroupSeminormClass.toSeminormedGroup` / `GroupSeminormClass.toSeminormedGroup` 的定义

English:
abbreviation GroupSeminormClass.toSeminormedGroup
  signature: [Group α] [GroupSeminormClass F α Real]
  body: f
  dist x y := f (x⁻¹ * y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp [← map_inv_eq_map f (x⁻¹ * y)]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group

@[to_additive]

中文:
缩写 群半范数类.toSeminormedGroup
  签名: [群 α] [群半范数类 F α 实数]
  定义体: f
  dist x y := f (x⁻¹ * y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp [← map_inv_eq_map f (x⁻¹ * y)]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group

@[to_additive]
-/
abbrev GroupSeminormClass.toSeminormedGroup [Group α] [GroupSeminormClass F α Real]
    (f : F) : SeminormedGroup α where
  norm := f
  dist x y := f (x⁻¹ * y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp [← map_inv_eq_map f (x⁻¹ * y)]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group

@[to_additive]
/--
lemma `GroupSeminormClass.toSeminormedGroup_norm_eq` / 引理 `GroupSeminormClass.toSeminormedGroup_norm_eq`

English:
lemma GroupSeminormClass.toSeminormedGroup_norm_eq
  statement: [Group α] [GroupSeminormClass F α Real]
  proof: rfl

中文:
引理 群半范数类.toSeminormedGroup_norm_eq
  结论: [群 α] [群半范数类 F α 实数]
  证明: rfl
-/
lemma GroupSeminormClass.toSeminormedGroup_norm_eq [Group α] [GroupSeminormClass F α Real]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedGroup f).toNorm x = f x := rfl

/-- Constructs a `SeminormedCommGroup` structure from a `GroupSeminormClass` on a `CommGroup`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `SeminormedAddCommGroup` structure from an `AddGroupSeminormClass`
on an `AddCommGroup`. -/]
/--
Definition of `GroupSeminormClass.toSeminormedCommGroup` / `GroupSeminormClass.toSeminormedCommGroup` 的定义

English:
abbreviation GroupSeminormClass.toSeminormedCommGroup
  signature: [CommGroup α] [GroupSeminormClass F α Real]
  body: GroupSeminormClass.toSeminormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]

中文:
缩写 群半范数类.toSeminormedCommGroup
  签名: [交换群 α] [群半范数类 F α 实数]
  定义体: GroupSeminormClass.toSeminormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]

Depends on / 依赖: GroupSeminormClass, GroupSeminormClass.toSeminormedGroup, toSeminormedGroup
-/
abbrev GroupSeminormClass.toSeminormedCommGroup [CommGroup α] [GroupSeminormClass F α Real]
    (f : F) : SeminormedCommGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]
/--
lemma `GroupSeminormClass.toSeminormedCommGroup_norm_eq` / 引理 `GroupSeminormClass.toSeminormedCommGroup_norm_eq`

English:
lemma GroupSeminormClass.toSeminormedCommGroup_norm_eq
  statement: [CommGroup α] [GroupSeminormClass F α Real]
  proof: rfl

中文:
引理 群半范数类.toSeminormedCommGroup_norm_eq
  结论: [交换群 α] [群半范数类 F α 实数]
  证明: rfl
-/
lemma GroupSeminormClass.toSeminormedCommGroup_norm_eq [CommGroup α] [GroupSeminormClass F α Real]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedCommGroup f).toNorm x = f x := rfl

/-- Constructs a `NormedGroup` structure from a `GroupNormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `NormedAddGroup` structure from an `AddGroupNormClass` on an
`AddGroup`. -/]
/--
Definition of `GroupNormClass.toNormedGroup` / `GroupNormClass.toNormedGroup` 的定义

English:
abbreviation GroupNormClass.toNormedGroup
  signature: [Group α] [GroupNormClass F α Real]
  body: GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := inv_mul_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive]

中文:
缩写 群范数类.toNormedGroup
  签名: [群 α] [群范数类 F α 实数]
  定义体: GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := inv_mul_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive]

Depends on / 依赖: GroupSeminormClass, GroupSeminormClass.toSeminormedGroup, toSeminormedGroup
-/
abbrev GroupNormClass.toNormedGroup [Group α] [GroupNormClass F α Real]
    (f : F) : NormedGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := inv_mul_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive]
/--
lemma `GroupNormClass.toNormedGroup_norm_eq` / 引理 `GroupNormClass.toNormedGroup_norm_eq`

English:
lemma GroupNormClass.toNormedGroup_norm_eq
  statement: [Group α] [GroupNormClass F α Real]
  proof: rfl

中文:
引理 群范数类.toNormedGroup_norm_eq
  结论: [群 α] [群范数类 F α 实数]
  证明: rfl
-/
lemma GroupNormClass.toNormedGroup_norm_eq [Group α] [GroupNormClass F α Real]
    (f : F) (x : α) : @norm _ (GroupNormClass.toNormedGroup f).toNorm x = f x := rfl

/-- Constructs a `NormedCommGroup` structure from a `GroupNormClass` on a `CommGroup`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `NormedAddCommGroup` structure from an `AddGroupNormClass` on an
`AddCommGroup`. -/]
/--
Definition of `GroupNormClass.toNormedCommGroup` / `GroupNormClass.toNormedCommGroup` 的定义

English:
abbreviation GroupNormClass.toNormedCommGroup
  signature: [CommGroup α] [GroupNormClass F α Real]
  body: GroupNormClass.toNormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]

中文:
缩写 群范数类.toNormedCommGroup
  签名: [交换群 α] [群范数类 F α 实数]
  定义体: GroupNormClass.toNormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]

Depends on / 依赖: GroupNormClass, GroupNormClass.toNormedGroup, toNormedGroup
-/
abbrev GroupNormClass.toNormedCommGroup [CommGroup α] [GroupNormClass F α Real]
    (f : F) : NormedCommGroup α where
  __ := GroupNormClass.toNormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]
/--
lemma `GroupNormClass.toNormedCommGroup_norm_eq` / 引理 `GroupNormClass.toNormedCommGroup_norm_eq`

English:
lemma GroupNormClass.toNormedCommGroup_norm_eq
  statement: [CommGroup α] [GroupNormClass F α Real]
  proof: rfl

中文:
引理 群范数类.toNormedCommGroup_norm_eq
  结论: [交换群 α] [群范数类 F α 实数]
  证明: rfl
-/
lemma GroupNormClass.toNormedCommGroup_norm_eq [CommGroup α] [GroupNormClass F α Real]
    (f : F) (x : α) : @norm _ (GroupNormClass.toNormedCommGroup f).toNorm x = f x := rfl
