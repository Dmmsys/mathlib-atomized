/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

public section

open CategoryTheory Limits

universe u

namespace GrpCat

@[to_additive]
/--
theorem `isZero_of_subsingleton` / 定理 `isZero_of_subsingleton`

English:
theorem isZero_of_subsingleton
  given: (G : GrpCat) [Subsingleton G]
  statement: IsZero G
  proof: by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]

中文:
定理 isZero_of_subsingleton
  条件: (G : 群范畴) [子单例 G]
  结论: 是零 G
  证明: by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_one, subsingleton
-/
theorem isZero_of_subsingleton (G : GrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject GrpCat
  body: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]

中文:
实例 :
  签名: 有ZeroObject 群范畴
  定义体: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]

Depends on / 依赖: isZero_of_subsingleton
-/
instance : HasZeroObject GrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
/--
lemma `subsingleton_of_isZero` / 引理 `subsingleton_of_isZero`

English:
lemma subsingleton_of_isZero
  given: {G : GrpCat} (h : Limits.IsZero G)
  proof: (h.iso (isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

@[to_additive]

中文:
引理 subsingleton_of_isZero
  条件: {G : 群范畴} (h : Limits.是零 G)
  证明: (h.iso (isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

@[to_additive]

Depends on / 依赖: groupIsoToMulEquiv, groupIsoToMulEquiv.subsingleton, h.iso, isZero_of_subsingleton, subsingleton
-/
lemma subsingleton_of_isZero {G : GrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

@[to_additive]
/--
lemma `isZero_iff_subsingleton` / 引理 `isZero_iff_subsingleton`

English:
lemma isZero_iff_subsingleton
  given: {G : GrpCat}
  statement: Limits.IsZero G ↔ Subsingleton G
  proof: ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]

中文:
引理 isZero_iff_subsingleton
  条件: {G : 群范畴}
  结论: Limits.是零 G ↔ 子单例 G
  证明: ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]

Depends on / 依赖: isZero_of_subsingleton, subsingleton_of_isZero
-/
lemma isZero_iff_subsingleton {G : GrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]
/--
lemma `isZero_of_iff_subsingleton` / 引理 `isZero_of_iff_subsingleton`

English:
lemma isZero_of_iff_subsingleton
  given: {G : Type*} [Group G]
  proof: isZero_iff_subsingleton

中文:
引理 isZero_of_iff_subsingleton
  条件: {G : 类型} [群 G]
  证明: isZero_iff_subsingleton

Depends on / 依赖: isZero_iff_subsingleton
-/
lemma isZero_of_iff_subsingleton {G : Type*} [Group G] :
    Limits.IsZero (GrpCat.of G) ↔ Subsingleton G :=
  isZero_iff_subsingleton

end GrpCat

namespace CommGrpCat

@[to_additive]
/--
theorem `isZero_of_subsingleton` / 定理 `isZero_of_subsingleton`

English:
theorem isZero_of_subsingleton
  given: (G : CommGrpCat) [Subsingleton G]
  statement: IsZero G
  proof: by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]

中文:
定理 isZero_of_subsingleton
  条件: (G : 交换群范畴) [子单例 G]
  结论: 是零 G
  证明: by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_one, subsingleton
-/
theorem isZero_of_subsingleton (G : CommGrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; rw [map_one]; rw [map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasZeroObject CommGrpCat
  body: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]

中文:
实例 :
  签名: 有ZeroObject 交换群范畴
  定义体: ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]

Depends on / 依赖: isZero_of_subsingleton
-/
instance : HasZeroObject CommGrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
/--
lemma `subsingleton_of_isZero` / 引理 `subsingleton_of_isZero`

English:
lemma subsingleton_of_isZero
  given: {G : CommGrpCat} (h : Limits.IsZero G)
  proof: (h.iso (isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

@[to_additive]

中文:
引理 subsingleton_of_isZero
  条件: {G : 交换群范畴} (h : Limits.是零 G)
  证明: (h.iso (isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

@[to_additive]

Depends on / 依赖: commGroupIsoToMulEquiv, commGroupIsoToMulEquiv.subsingleton, h.iso, isZero_of_subsingleton, subsingleton
-/
lemma subsingleton_of_isZero {G : CommGrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

@[to_additive]
/--
lemma `isZero_iff_subsingleton` / 引理 `isZero_iff_subsingleton`

English:
lemma isZero_iff_subsingleton
  given: {G : CommGrpCat}
  statement: Limits.IsZero G ↔ Subsingleton G
  proof: ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]

中文:
引理 isZero_iff_subsingleton
  条件: {G : 交换群范畴}
  结论: Limits.是零 G ↔ 子单例 G
  证明: ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]

Depends on / 依赖: isZero_of_subsingleton, subsingleton_of_isZero
-/
lemma isZero_iff_subsingleton {G : CommGrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h => subsingleton_of_isZero h, fun _ => isZero_of_subsingleton G⟩

@[to_additive]
/--
lemma `isZero_of_iff_subsingleton` / 引理 `isZero_of_iff_subsingleton`

English:
lemma isZero_of_iff_subsingleton
  given: {G : Type*} [CommGroup G]
  proof: isZero_iff_subsingleton

中文:
引理 isZero_of_iff_subsingleton
  条件: {G : 类型} [交换群 G]
  证明: isZero_iff_subsingleton

Depends on / 依赖: isZero_iff_subsingleton
-/
lemma isZero_of_iff_subsingleton {G : Type*} [CommGroup G] :
    Limits.IsZero (CommGrpCat.of G) ↔ Subsingleton G :=
  isZero_iff_subsingleton

end CommGrpCat
