/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Kim Morrison
-/
module

public import Mathlib.Data.Opposite
public import Mathlib.Tactic.ToDual

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a generalization of `Digraph V`, which can be thought of as "a proposition `a ⟶ b` of arrows".

-/

@[expose] public section

open Opposite

-- We use the same universe order as in category theory.
-- See note [category theory universes]
universe v v₁ v₂ u u₁ u₂

/--
Definition of `Quiver` / `Quiver` 的定义

English:
class Quiver
  parameters: (V : Type u)
  axioms and operations (1):
    - Hom : V -> V -> Type v

中文:
类 箭图
  参数: (V : 类型u)
  公理与运算 (1 个):
    - Hom : V -> V -> 类型v

Depends on / 依赖: Quiver, Quiver.Hom
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V -> V -> Type v

attribute [to_dual self (reorder := 3 4)] Quiver.Hom
attribute [to_dual self (reorder := Hom (1 2))] Quiver.mk

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

/--
Instance `opposite` / 实例 `opposite`

English:
instance opposite
  signature: {V} [Quiver V]
  body: ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

中文:
实例 opposite
  签名: {V} [箭图 V]
  定义体: ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩
-/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

/-- The opposite of an arrow in `V`. -/
@[implicit_reducible, to_dual self]
/--
Definition of `Hom.op` / `Hom.op` 的定义

English:
definition Hom.op
  signature: {V} [Quiver V] {X Y : V} (f : X ⟶ Y)
  body: ⟨f⟩

中文:
定义 态射.op
  签名: {V} [箭图 V] {X Y : V} (f : X ⟶ Y)
  定义体: ⟨f⟩
-/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
@[implicit_reducible, to_dual self]
/--
Definition of `Hom.unop` / `Hom.unop` 的定义

English:
definition Hom.unop
  signature: {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y)
  body: Opposite.unop f

中文:
定义 态射.unop
  签名: {V} [箭图 V] {X Y : Vᵒᵖ} (f : X ⟶ Y)
  定义体: Opposite.unop f

Depends on / 依赖: Opposite, Opposite.unop
-/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

/-- The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`. -/
@[simps, to_dual self]
/--
Definition of `Hom.opEquiv` / `Hom.opEquiv` 的定义

English:
definition Hom.opEquiv
  signature: {V} [Quiver V] {X Y : V}
  body: Opposite.op
  invFun := Opposite.unop

中文:
定义 态射.opEquiv
  签名: {V} [箭图 V] {X Y : V}
  定义体: Opposite.op
  invFun := Opposite.unop

Depends on / 依赖: Opposite, Opposite.op
-/
def Hom.opEquiv {V} [Quiver V] {X Y : V} : (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Opposite.op
  invFun := Opposite.unop

/--
Definition of `Empty` / `Empty` 的定义

English:
definition Empty
  signature: (V : Type u)
  body: V

中文:
定义 空
  签名: (V : 类型u)
  定义体: V
-/
def Empty (V : Type u) : Type u := V

/--
Instance `emptyQuiver` / 实例 `emptyQuiver`

English:
instance emptyQuiver
  signature: (V : Type u)
  body: ⟨fun _ _ => PEmpty⟩

@[simp, to_dual self]

中文:
实例 emptyQuiver
  签名: (V : 类型u)
  定义体: ⟨fun _ _ => PEmpty⟩

@[simp, to_dual self]

Depends on / 依赖: PEmpty
-/
instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩

@[simp, to_dual self]
/--
theorem `empty_arrow` / 定理 `empty_arrow`

English:
theorem empty_arrow
  given: {V : Type u} (a b : Empty V)
  statement: (a ⟶ b) = PEmpty
  proof: rfl

中文:
定理 empty_arrow
  条件: {V : 类型u} (a b : 空 V)
  结论: (a ⟶ b) = 命题空
  证明: rfl
-/
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty := rfl

/--
Definition of `IsThin` / `IsThin` 的定义

English:
abbreviation IsThin
  signature: (V : Type u) [Quiver V]
  body: forall a b : V, Subsingleton (a ⟶ b)

to_dual_insert_cast_fun IsThin := fun inst a b => inst b a, fun inst a b => inst b a

中文:
缩写 IsThin
  签名: (V : 类型u) [箭图 V]
  定义体: forall a b : V, Subsingleton (a ⟶ b)

to_dual_insert_cast_fun IsThin := fun inst a b => inst b a, fun inst a b => inst b a

Depends on / 依赖: Subsingleton
-/
abbrev IsThin (V : Type u) [Quiver V] : Prop := forall a b : V, Subsingleton (a ⟶ b)

to_dual_insert_cast_fun IsThin := fun inst a b => inst b a, fun inst a b => inst b a


section

variable {V : Type*} [Quiver V] {X Y X' Y' : V}

/-- An arrow in a quiver can be transported across equalities between the source and target
objects. -/
@[to_dual self (reorder := X Y, X' Y', hX hY)]
/--
Definition of `homOfEq` / `homOfEq` 的定义

English:
definition homOfEq
  signature: (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
  body: by
  subst hX hY
  exact f

@[simp, to_dual self]

中文:
定义 homOfEq
  签名: (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
  定义体: by
  subst hX hY
  exact f

@[simp, to_dual self]
-/
def homOfEq (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') : X' ⟶ Y' := by
  subst hX hY
  exact f

@[simp, to_dual self]
/--
lemma `homOfEq_trans` / 引理 `homOfEq_trans`

English:
lemma homOfEq_trans
  statement: (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
  proof: by
  subst hX hY hX' hY'
  rfl

@[to_dual self]

中文:
引理 homOfEq_trans
  结论: (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
  证明: by
  subst hX hY hX' hY'
  rfl

@[to_dual self]
-/
lemma homOfEq_trans (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
    {X'' Y'' : V} (hX' : X' = X'') (hY' : Y' = Y'') :
    homOfEq (homOfEq f hX hY) hX' hY' = homOfEq f (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

@[to_dual self]
/--
lemma `homOfEq_injective` / 引理 `homOfEq_injective`

English:
lemma homOfEq_injective
  statement: (hX : X = X') (hY : Y = Y')
  proof: by
  subst hX hY
  exact h

@[simp, to_dual self]

中文:
引理 homOfEq_injective
  结论: (hX : X = X') (hY : Y = Y')
  证明: by
  subst hX hY
  exact h

@[simp, to_dual self]
-/
lemma homOfEq_injective (hX : X = X') (hY : Y = Y')
    {f g : X ⟶ Y} (h : Quiver.homOfEq f hX hY = Quiver.homOfEq g hX hY) : f = g := by
  subst hX hY
  exact h

@[simp, to_dual self]
/--
lemma `homOfEq_rfl` / 引理 `homOfEq_rfl`

English:
lemma homOfEq_rfl
  given: (f : X ⟶ Y)
  statement: Quiver.homOfEq f rfl rfl = f
  proof: rfl

@[to_dual self]

中文:
引理 homOfEq_rfl
  条件: (f : X ⟶ Y)
  结论: 箭图.homOfEq f rfl rfl = f
  证明: rfl

@[to_dual self]
-/
lemma homOfEq_rfl (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl = f := rfl

@[to_dual self]
/--
lemma `heq_of_homOfEq_ext` / 引理 `heq_of_homOfEq_ext`

English:
lemma heq_of_homOfEq_ext
  statement: (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
  proof: by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

@[to_dual self]

中文:
引理 heq_of_homOfEq_ext
  结论: (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
  证明: by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

@[to_dual self]

Depends on / 依赖: Quiver, Quiver.homOfEq_rfl, homOfEq_rfl
-/
lemma heq_of_homOfEq_ext (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Quiver.homOfEq f hX hY = f') : f ≍ f' := by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

@[to_dual self]
/--
lemma `homOfEq_eq_iff` / 引理 `homOfEq_eq_iff`

English:
lemma homOfEq_eq_iff
  given: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
  proof: by
  subst hX hY; simp

@[to_dual self]

中文:
引理 homOfEq_eq_iff
  条件: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
  证明: by
  subst hX hY; simp

@[to_dual self]
-/
lemma homOfEq_eq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY = g ↔ f = Quiver.homOfEq g hX.symm hY.symm := by
  subst hX hY; simp

@[to_dual self]
/--
lemma `eq_homOfEq_iff` / 引理 `eq_homOfEq_iff`

English:
lemma eq_homOfEq_iff
  given: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y)
  proof: by
  subst hX hY; simp

@[to_dual self]

中文:
引理 eq_homOfEq_iff
  条件: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y)
  证明: by
  subst hX hY; simp

@[to_dual self]
-/
lemma eq_homOfEq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f = Quiver.homOfEq g hX hY ↔ Quiver.homOfEq f hX.symm hY.symm = g := by
  subst hX hY; simp

@[to_dual self]
/--
lemma `homOfEq_heq` / 引理 `homOfEq_heq`

English:
lemma homOfEq_heq
  given: (hX : X = X') (hY : Y = Y') (f : X ⟶ Y)
  statement: homOfEq f hX hY ≍ f
  proof: (heq_of_homOfEq_ext hX hY rfl).symm

@[to_dual self]

中文:
引理 homOfEq_heq
  条件: (hX : X = X') (hY : Y = Y') (f : X ⟶ Y)
  结论: homOfEq f hX hY ≍ f
  证明: (heq_of_homOfEq_ext hX hY rfl).symm

@[to_dual self]

Depends on / 依赖: heq_of_homOfEq_ext
-/
lemma homOfEq_heq (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) : homOfEq f hX hY ≍ f :=
  (heq_of_homOfEq_ext hX hY rfl).symm

@[to_dual self]
/--
lemma `homOfEq_heq_left_iff` / 引理 `homOfEq_heq_left_iff`

English:
lemma homOfEq_heq_left_iff
  given: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
  proof: by
  cases hX; cases hY; rfl

@[to_dual self]

中文:
引理 homOfEq_heq_left_iff
  条件: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
  证明: by
  cases hX; cases hY; rfl

@[to_dual self]
-/
lemma homOfEq_heq_left_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    homOfEq f hX hY ≍ g ↔ f ≍ g := by
  cases hX; cases hY; rfl

@[to_dual self]
/--
lemma `homOfEq_heq_right_iff` / 引理 `homOfEq_heq_right_iff`

English:
lemma homOfEq_heq_right_iff
  given: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y)
  proof: by
  cases hX; cases hY; rfl

中文:
引理 homOfEq_heq_right_iff
  条件: (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y)
  证明: by
  cases hX; cases hY; rfl
-/
lemma homOfEq_heq_right_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f ≍ homOfEq g hX hY ↔ f ≍ g := by
  cases hX; cases hY; rfl


end

end Quiver
