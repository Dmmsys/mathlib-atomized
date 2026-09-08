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

variable {F α : Type*} [FunLike F α ℝ]

/-- Constructs a `SeminormedGroup` structure from a `GroupSeminormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `SeminormedAddGroup` structure from an `AddGroupSeminormClass` on an
`AddGroup`. -/]
/-
**GroupSeminormClass.toSeminormedGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GroupSeminormClass.toSeminormedGroup [Group α] [GroupSeminormClass F α Rea
l] (f : F) : SeminormedGroup α where norm
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev GroupSeminormClass.toSeminormedGroup [Group α] [GroupSeminormClass F α ℝ]
    (f : F) : SeminormedGroup α where
  norm := f
  dist x y := f (x⁻¹ * y)
  dist_eq _ _ := rfl
  dist_self _ := by simp
  dist_comm x y := by simp [← map_inv_eq_map f (x⁻¹ * y)]
  dist_triangle x y z := by convert! map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group

@[to_additive]
/-
**GroupSeminormClass.toSeminormedGroup_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupSeminormClass.toSeminormedGroup_norm_eq [Group α] [GroupSeminormClass
 F α Real] (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedGroup f).to
Norm x = f x
参数：f : F；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GroupSeminormClass.toSeminormedGroup_norm_eq [Group α] [GroupSeminormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedGroup f).toNorm x = f x := rfl

/-- Constructs a `SeminormedCommGroup` structure from a `GroupSeminormClass` on a `CommGroup`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `SeminormedAddCommGroup` structure from an `AddGroupSeminormClass`
on an `AddCommGroup`. -/]
/-
**GroupSeminormClass.toSeminormedCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GroupSeminormClass.toSeminormedCommGroup [CommGroup α] [GroupSeminormClass
 F α Real] (f : F) : SeminormedCommGroup α where __
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.mul_comm`：∀ {G : Type u} [self : CommGroup G] (a b : G), a * b
 = b * a
· 使用定理 `SeminormedGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedGroup E] (x 
y : E), dist x y = ‖x⁻¹ * y‖
-/
abbrev GroupSeminormClass.toSeminormedCommGroup [CommGroup α] [GroupSeminormClass F α ℝ]
    (f : F) : SeminormedCommGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]
/-
**GroupSeminormClass.toSeminormedCommGroup_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupSeminormClass.toSeminormedCommGroup_norm_eq [CommGroup α] [GroupSemin
ormClass F α Real] (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedCom
mGroup f).toNorm x = f x
参数：f : F；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GroupSeminormClass.toSeminormedCommGroup_norm_eq [CommGroup α] [GroupSeminormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupSeminormClass.toSeminormedCommGroup f).toNorm x = f x := rfl

/-- Constructs a `NormedGroup` structure from a `GroupNormClass` on a `Group`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `NormedAddGroup` structure from an `AddGroupNormClass` on an
`AddGroup`. -/]
/-
**GroupNormClass.toNormedGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GroupNormClass.toNormedGroup [Group α] [GroupNormClass F α Real] (f : F) :
 NormedGroup α where __
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupNormClass.toGroupSeminormClass`：∀ {F : Type u_7} {α : outParam (Typ
e u_8)} {β : outParam (Type u_9)} {inst : Group α} {inst_1 : AddCommMonoid β}   
{inst_2 : PartialOrder β}…
· 使用定理 `SeminormedGroup.dist_eq`：∀ {E : Type u_8} [self : SeminormedGroup E] (x 
y : E), dist x y = ‖x⁻¹ * y‖
-/
abbrev GroupNormClass.toNormedGroup [Group α] [GroupNormClass F α ℝ]
    (f : F) : NormedGroup α where
  __ := GroupSeminormClass.toSeminormedGroup f
  eq_of_dist_eq_zero h := inv_mul_eq_one.mp (eq_one_of_map_eq_zero f h)

@[to_additive]
/-
**GroupNormClass.toNormedGroup_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupNormClass.toNormedGroup_norm_eq [Group α] [GroupNormClass F α Real] (
f : F) (x : α) : @norm _ (GroupNormClass.toNormedGroup f).toNorm x = f x
参数：f : F；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GroupNormClass.toNormedGroup_norm_eq [Group α] [GroupNormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupNormClass.toNormedGroup f).toNorm x = f x := rfl

/-- Constructs a `NormedCommGroup` structure from a `GroupNormClass` on a `CommGroup`. -/
-- See note [reducible non-instances]
@[to_additive /-- Constructs a `NormedAddCommGroup` structure from an `AddGroupNormClass` on an
`AddCommGroup`. -/]
/-
**GroupNormClass.toNormedCommGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GroupNormClass.toNormedCommGroup [CommGroup α] [GroupNormClass F α Real] (
f : F) : NormedCommGroup α where __
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroup.mul_comm`：∀ {G : Type u} [self : CommGroup G] (a b : G), a * b
 = b * a
· 使用定理 `NormedGroup.dist_eq`：∀ {E : Type u_8} [self : NormedGroup E] (x y : E), 
dist x y = ‖x⁻¹ * y‖
-/
abbrev GroupNormClass.toNormedCommGroup [CommGroup α] [GroupNormClass F α ℝ]
    (f : F) : NormedCommGroup α where
  __ := GroupNormClass.toNormedGroup f
  __ : CommGroup α := inferInstance

@[to_additive]
/-
**GroupNormClass.toNormedCommGroup_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupNormClass.toNormedCommGroup_norm_eq [CommGroup α] [GroupNormClass F α
 Real] (f : F) (x : α) : @norm _ (GroupNormClass.toNormedCommGroup f).toNorm x =
 f x
参数：f : F；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GroupNormClass.toNormedCommGroup_norm_eq [CommGroup α] [GroupNormClass F α ℝ]
    (f : F) (x : α) : @norm _ (GroupNormClass.toNormedCommGroup f).toNorm x = f x := rfl
