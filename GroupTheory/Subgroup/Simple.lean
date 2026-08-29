/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Simple groups

This file defines `IsSimpleGroup G`, a class indicating that a group has exactly two normal
subgroups.

## Main definitions

- `IsSimpleGroup G`, a class indicating that a group has exactly two normal subgroups.

## Tags
subgroup, subgroups

-/

public section


variable {G : Type*} [Group G]
variable {A : Type*} [AddGroup A]

section

variable (G) (A)

/-- A `Group` is simple when it has exactly two normal `Subgroup`s. -/
@[mk_iff, wikidata Q571124]
/--
Definition of `IsSimpleGroup` / `IsSimpleGroup` 的定义

English:
class IsSimpleGroup
  parameters: : Prop extends Nontrivial G where
  extends: Nontrivial G
  axioms and operations (1):
    - eq_bot_or_eq_top_of_normal : forall H : Subgroup G, H.Normal -> H = ⊥ ∨ H = ⊤

中文:
类 是单群
  参数: : 命题 extends 非平凡 G where
  继承: 非平凡 G
  公理与运算 (1 个):
    - eq_bot_or_eq_top_of_normal : 对任意 H : 子群 G, H.正规 -> H = ⊥ ∨ H = ⊤
-/
class IsSimpleGroup : Prop extends Nontrivial G where
  /-- Any normal subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : forall H : Subgroup G, H.Normal -> H = ⊥ ∨ H = ⊤

attribute [instance 100] IsSimpleGroup.toNontrivial

/-- An `AddGroup` is simple when it has exactly two normal `AddSubgroup`s. -/
@[mk_iff]
/--
Definition of `IsSimpleAddGroup` / `IsSimpleAddGroup` 的定义

English:
class IsSimpleAddGroup
  parameters: : Prop extends Nontrivial A where
  extends: Nontrivial A
  axioms and operations (1):
    - eq_bot_or_eq_top_of_normal : forall H : AddSubgroup A, H.Normal -> H = ⊥ ∨ H = ⊤

中文:
类 是SimpleAdd群
  参数: : 命题 extends 非平凡 A where
  继承: 非平凡 A
  公理与运算 (1 个):
    - eq_bot_or_eq_top_of_normal : 对任意 H : 加法子群 A, H.正规 -> H = ⊥ ∨ H = ⊤
-/
class IsSimpleAddGroup : Prop extends Nontrivial A where
  /-- Any normal additive subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : forall H : AddSubgroup A, H.Normal -> H = ⊥ ∨ H = ⊤

attribute [instance 100] IsSimpleAddGroup.toNontrivial

attribute [to_additive existing] IsSimpleGroup isSimpleGroup_iff

variable {G} {A}

@[to_additive]
/--
theorem `Subgroup.Normal.eq_bot_or_eq_top` / 定理 `Subgroup.Normal.eq_bot_or_eq_top`

English:
theorem Subgroup.Normal.eq_bot_or_eq_top
  given: [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal)
  proof: IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn

@[to_additive]

中文:
定理 子群.正规.eq_bot_or_eq_top
  条件: [是单群 G] {H : 子群 G} (Hn : H.正规)
  证明: IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn

@[to_additive]

Depends on / 依赖: IsSimpleGroup, IsSimpleGroup.eq_bot_or_eq_top_of_normal, eq_bot_or_eq_top_of_normal
-/
theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal) :
    H = ⊥ ∨ H = ⊤ :=
  IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn

@[to_additive]
/--
lemma `Subgroup.isSimpleGroup_iff` / 引理 `Subgroup.isSimpleGroup_iff`

English:
lemma Subgroup.isSimpleGroup_iff
  given: {H : Subgroup G}
  proof: by
  rw [isSimpleGroup_iff]; rw [H.nontrivial_iff_ne_bot]; rw [Subgroup.forall]
  simp +contextual [disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq]

中文:
引理 子群.isSimpleGroup_iff
  条件: {H : 子群 G}
  证明: by
  rw [isSimpleGroup_iff]; rw [H.nontrivial_iff_ne_bot]; rw [Subgroup.forall]
  simp +contextual [disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq]
-/
protected lemma Subgroup.isSimpleGroup_iff {H : Subgroup G} :
    IsSimpleGroup ↥H ↔ H != ⊥ ∧ forall H' <= H, (H'.subgroupOf H).Normal -> H' = ⊥ ∨ H' = H := by
  rw [isSimpleGroup_iff]; rw [H.nontrivial_iff_ne_bot]; rw [Subgroup.forall]
  simp +contextual [disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq]

namespace IsSimpleGroup

@[to_additive]
instance {C : Type*} [CommGroup C] [IsSimpleGroup C] : IsSimpleOrder (Subgroup C) :=
  ⟨fun H => H.normal_of_isMulCommutative.eq_bot_or_eq_top⟩

open Subgroup

@[to_additive]
/--
theorem `isSimpleGroup_of_surjective` / 定理 `isSimpleGroup_of_surjective`

English:
theorem isSimpleGroup_of_surjective
  statement: {H : Type*} [Group H] [IsSimpleGroup G] [Nontrivial H]
  proof: ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩

@[to_additive]

中文:
定理 isSimpleGroup_of_surjective
  结论: {H : 类型} [群 H] [是单群 G] [非平凡 H]
  证明: ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩

@[to_additive]

Depends on / 依赖: comap_injective, comap_top, eq_bot_or_eq_top, eq_bot_or_eq_top.imp, iH.comap, map_bot, map_comap_eq_self_of_surjective
-/
theorem isSimpleGroup_of_surjective {H : Type*} [Group H] [IsSimpleGroup G] [Nontrivial H]
    (f : G ->* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩

@[to_additive]
/--
lemma `_root_.MulEquiv.isSimpleGroup` / 引理 `_root_.MulEquiv.isSimpleGroup`

English:
lemma _root_.MulEquiv.isSimpleGroup
  given: {H : Type*} [Group H] [IsSimpleGroup H] (e : G ≃* H)
  proof: haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

@[to_additive]

中文:
引理 _root_.乘法等价.isSimpleGroup
  条件: {H : 类型} [群 H] [是单群 H] (e : G ≃* H)
  证明: haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

@[to_additive]

Depends on / 依赖: Nontrivial, e.symm.surjective, e.symm.toMonoidHom, e.toEquiv.nontrivial, isSimpleGroup_of_surjective, nontrivial, surjective, toEquiv, toMonoidHom
-/
lemma _root_.MulEquiv.isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H] (e : G ≃* H) :
    IsSimpleGroup G :=
  haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

@[to_additive]
/--
lemma `_root_.MulEquiv.isSimpleGroup_congr` / 引理 `_root_.MulEquiv.isSimpleGroup_congr`

English:
lemma _root_.MulEquiv.isSimpleGroup_congr
  given: {H : Type*} [Group H] (e : G ≃* H)
  proof: e.symm.isSimpleGroup
  mpr _ := e.isSimpleGroup

中文:
引理 _root_.乘法等价.isSimpleGroup_congr
  条件: {H : 类型} [群 H] (e : G ≃* H)
  证明: e.symm.isSimpleGroup
  mpr _ := e.isSimpleGroup

Depends on / 依赖: e.symm.isSimpleGroup, isSimpleGroup
-/
lemma _root_.MulEquiv.isSimpleGroup_congr {H : Type*} [Group H] (e : G ≃* H) :
    IsSimpleGroup G ↔ IsSimpleGroup H where
  mp _ := e.symm.isSimpleGroup
  mpr _ := e.isSimpleGroup

end IsSimpleGroup

end
