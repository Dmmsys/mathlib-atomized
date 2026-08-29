/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject

/-!
# The graded object in a single degree

In this file, we define the functor `GradedObject.single j : C ⥤ GradedObject J C`
which sends an object `X : C` to the graded object which is `X` in degree `j` and
the initial object of `C` in other degrees.

-/

@[expose] public section

namespace CategoryTheory

open Limits

namespace GradedObject

variable {J : Type*} {C : Type*} [Category* C] [HasInitial C] [DecidableEq J]

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (j : J)
  body: if i = j then X else ⊥_ C
  map {X₁ X₂} f i :=
    if h : i = j then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else eqToHom (by dsimp; rw [if_neg h, if_neg h])

中文:
定义 single
  签名: (j : J)
  定义体: if i = j then X else ⊥_ C
  map {X₁ X₂} f i :=
    if h : i = j then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else eqToHom (by dsimp; rw [if_neg h, if_neg h])
-/
noncomputable def single (j : J) : C ⥤ GradedObject J C where
  obj X i := if i = j then X else ⊥_ C
  map {X₁ X₂} f i :=
    if h : i = j then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else eqToHom (by dsimp; rw [if_neg h, if_neg h])

variable (J) in
/--
Definition of `single₀` / `single₀` 的定义

English:
abbreviation single₀
  signature: [Zero J]
  body: single 0

中文:
缩写 single₀
  签名: [零 J]
  定义体: single 0

Depends on / 依赖: single
-/
noncomputable abbrev single₀ [Zero J] : C ⥤ GradedObject J C := single 0

/--
Definition of `singleObjApplyIsoOfEq` / `singleObjApplyIsoOfEq` 的定义

English:
definition singleObjApplyIsoOfEq
  signature: (j : J) (X : C) (i : J) (h : i = j)
  body: eqToIso (if_pos h)

中文:
定义 singleObjApplyIsoOfEq
  签名: (j : J) (X : C) (i : J) (h : i = j)
  定义体: eqToIso (if_pos h)

Depends on / 依赖: eqToIso, if_pos
-/
noncomputable def singleObjApplyIsoOfEq (j : J) (X : C) (i : J) (h : i = j) :
    (single j).obj X i ≅ X := eqToIso (if_pos h)

/--
Definition of `singleObjApplyIso` / `singleObjApplyIso` 的定义

English:
abbreviation singleObjApplyIso
  signature: (j : J) (X : C)
  body: singleObjApplyIsoOfEq j X j rfl

中文:
缩写 singleObjApplyIso
  签名: (j : J) (X : C)
  定义体: singleObjApplyIsoOfEq j X j rfl

Depends on / 依赖: singleObjApplyIsoOfEq
-/
noncomputable abbrev singleObjApplyIso (j : J) (X : C) :
    (single j).obj X j ≅ X := singleObjApplyIsoOfEq j X j rfl

/--
Definition of `isInitialSingleObjApply` / `isInitialSingleObjApply` 的定义

English:
definition isInitialSingleObjApply
  signature: (j : J) (X : C) (i : J) (h : i != j)
  body: by
  dsimp [single]
  rw [if_neg h]
  exact initialIsInitial

中文:
定义 isInitialSingleObjApply
  签名: (j : J) (X : C) (i : J) (h : i != j)
  定义体: by
  dsimp [single]
  rw [if_neg h]
  exact initialIsInitial

Depends on / 依赖: if_neg, initialIsInitial, single
-/
noncomputable def isInitialSingleObjApply (j : J) (X : C) (i : J) (h : i != j) :
    IsInitial ((single j).obj X i) := by
  dsimp [single]
  rw [if_neg h]
  exact initialIsInitial

/--
lemma `singleObjApplyIsoOfEq_inv_single_map` / 引理 `singleObjApplyIsoOfEq_inv_single_map`

English:
lemma singleObjApplyIsoOfEq_inv_single_map
  given: (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
  proof: by
  subst h
  simp [singleObjApplyIsoOfEq, single]

中文:
引理 singleObjApplyIsoOfEq_inv_single_map
  条件: (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
  证明: by
  subst h
  simp [singleObjApplyIsoOfEq, single]

Depends on / 依赖: single, singleObjApplyIsoOfEq
-/
lemma singleObjApplyIsoOfEq_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (singleObjApplyIsoOfEq j X i h).inv ≫ (single j).map f i =
      f ≫ (singleObjApplyIsoOfEq j Y i h).inv := by
  subst h
  simp [singleObjApplyIsoOfEq, single]

/--
lemma `single_map_singleObjApplyIsoOfEq_hom` / 引理 `single_map_singleObjApplyIsoOfEq_hom`

English:
lemma single_map_singleObjApplyIsoOfEq_hom
  given: (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
  proof: by
  subst h
  simp [singleObjApplyIsoOfEq, single]

@[reassoc (attr := simp)]

中文:
引理 single_map_singleObjApplyIsoOfEq_hom
  条件: (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j)
  证明: by
  subst h
  simp [singleObjApplyIsoOfEq, single]

@[reassoc (attr := simp)]

Depends on / 依赖: single, singleObjApplyIsoOfEq
-/
lemma single_map_singleObjApplyIsoOfEq_hom (j : J) {X Y : C} (f : X ⟶ Y) (i : J) (h : i = j) :
    (single j).map f i ≫ (singleObjApplyIsoOfEq j Y i h).hom =
      (singleObjApplyIsoOfEq j X i h).hom ≫ f := by
  subst h
  simp [singleObjApplyIsoOfEq, single]

@[reassoc (attr := simp)]
/--
lemma `singleObjApplyIso_inv_single_map` / 引理 `singleObjApplyIso_inv_single_map`

English:
lemma singleObjApplyIso_inv_single_map
  given: (j : J) {X Y : C} (f : X ⟶ Y)
  proof: by
  apply singleObjApplyIsoOfEq_inv_single_map

@[reassoc (attr := simp)]

中文:
引理 singleObjApplyIso_inv_single_map
  条件: (j : J) {X Y : C} (f : X ⟶ Y)
  证明: by
  apply singleObjApplyIsoOfEq_inv_single_map

@[reassoc (attr := simp)]

Depends on / 依赖: singleObjApplyIsoOfEq_inv_single_map
-/
lemma singleObjApplyIso_inv_single_map (j : J) {X Y : C} (f : X ⟶ Y) :
    (singleObjApplyIso j X).inv ≫ (single j).map f j = f ≫ (singleObjApplyIso j Y).inv := by
  apply singleObjApplyIsoOfEq_inv_single_map

@[reassoc (attr := simp)]
/--
lemma `single_map_singleObjApplyIso_hom` / 引理 `single_map_singleObjApplyIso_hom`

English:
lemma single_map_singleObjApplyIso_hom
  given: (j : J) {X Y : C} (f : X ⟶ Y)
  proof: by
  apply single_map_singleObjApplyIsoOfEq_hom

中文:
引理 single_map_singleObjApplyIso_hom
  条件: (j : J) {X Y : C} (f : X ⟶ Y)
  证明: by
  apply single_map_singleObjApplyIsoOfEq_hom

Depends on / 依赖: single_map_singleObjApplyIsoOfEq_hom
-/
lemma single_map_singleObjApplyIso_hom (j : J) {X Y : C} (f : X ⟶ Y) :
    (single j).map f j ≫ (singleObjApplyIso j Y).hom = (singleObjApplyIso j X).hom ≫ f := by
  apply single_map_singleObjApplyIsoOfEq_hom

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The composition of the single functor `single j : C ⥤ GradedObject J C` and the
evaluation functor `eval j` identifies to the identity functor. -/
@[simps!]
/--
Definition of `singleCompEval` / `singleCompEval` 的定义

English:
definition singleCompEval
  signature: (j : J)
  body: NatIso.ofComponents (singleObjApplyIso j) (by simp)

中文:
定义 singleCompEval
  签名: (j : J)
  定义体: NatIso.ofComponents (singleObjApplyIso j) (by simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, singleObjApplyIso
-/
noncomputable def singleCompEval (j : J) : single j ⋙ eval j ≅ 𝟭 C :=
  NatIso.ofComponents (singleObjApplyIso j) (by simp)

end GradedObject

end CategoryTheory
