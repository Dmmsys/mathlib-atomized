/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.Order.Notation
public import Mathlib.Combinatorics.Quiver.Basic

/-!
## Wide subquivers

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/

@[expose] public section

universe v u

/--
Definition of `WideSubquiver` / `WideSubquiver` 的定义

English:
definition WideSubquiver
  signature: (V) [Quiver.{v} V]
  body: forall a b : V, Set (a ⟶ b)

中文:
定义 WideSubquiver
  签名: (V) [Quiver.{v} V]
  定义体: forall a b : V, Set (a ⟶ b)
-/
def WideSubquiver (V) [Quiver.{v} V] :=
  forall a b : V, Set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `WideSubquiver`. -/
@[nolint unusedArguments]
/--
Definition of `WideSubquiver.toType` / `WideSubquiver.toType` 的定义

English:
definition WideSubquiver.toType
  signature: (V) [Quiver V] (_ : WideSubquiver V)
  body: V

中文:
定义 WideSubquiver.toType
  签名: (V) [Quiver V] (_ : WideSubquiver V)
  定义体: V
-/
def WideSubquiver.toType (V) [Quiver V] (_ : WideSubquiver V) : Type u :=
  V

/--
Instance `wideSubquiverHasCoeToSort` / 实例 `wideSubquiverHasCoeToSort`

English:
instance wideSubquiverHasCoeToSort
  signature: {V} [Quiver V]
  body: WideSubquiver.toType V H

中文:
实例 wideSubquiverHasCoeToSort
  签名: {V} [Quiver V]
  定义体: WideSubquiver.toType V H

Depends on / 依赖: WideSubquiver, WideSubquiver.toType, toType
-/
instance wideSubquiverHasCoeToSort {V} [Quiver V] :
    CoeSort (WideSubquiver V) (Type u) where coe H := WideSubquiver.toType V H

/--
Instance `WideSubquiver.quiver` / 实例 `WideSubquiver.quiver`

English:
instance WideSubquiver.quiver
  signature: {V} [Quiver V] (H : WideSubquiver V)
  body: ⟨fun a b => { f // f in H a b }⟩

中文:
实例 WideSubquiver.quiver
  签名: {V} [Quiver V] (H : WideSubquiver V)
  定义体: ⟨fun a b => { f // f in H a b }⟩
-/
instance WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H :=
  ⟨fun a b => { f // f in H a b }⟩

namespace Quiver

instance {V} [Quiver V] : Bot (WideSubquiver V) :=
  ⟨fun _ _ => ∅⟩

instance {V} [Quiver V] : Top (WideSubquiver V) :=
  ⟨fun _ _ => Set.univ⟩

noncomputable instance {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

-- TODO Unify with `CategoryTheory.Arrow`? (The fields have been named to match.)
/-- `Total V` is the type of _all_ arrows of `V`. -/
@[ext]
/--
Definition of `Total` / `Total` 的定义

English:
structure Total
  parameters: (V : Type u) [Quiver.{v} V]
  axioms and operations (3):
    - left : V
    - right : V
    - hom : left ⟶ right

中文:
结构 Total
  参数: (V : 类型u) [Quiver.{v} V]
  公理与运算 (3 个):
    - left : V
    - right : V
    - hom : left ⟶ right
-/
structure Total (V : Type u) [Quiver.{v} V] : Type max u v where
  /-- the source vertex of an arrow -/
  left : V
  /-- the target vertex of an arrow -/
  right : V
  /-- an arrow -/
  hom : left ⟶ right

/--
Definition of `wideSubquiverEquivSetTotal` / `wideSubquiverEquivSetTotal` 的定义

English:
definition wideSubquiverEquivSetTotal
  signature: {V} [Quiver V]
  body: { e | e.hom in H e.left e.right }
  invFun S a b := { e | Total.mk a b e in S }

中文:
定义 wideSubquiverEquivSetTotal
  签名: {V} [Quiver V]
  定义体: { e | e.hom in H e.left e.right }
  invFun S a b := { e | Total.mk a b e in S }

Depends on / 依赖: e.hom, e.left, e.right
-/
def wideSubquiverEquivSetTotal {V} [Quiver V] :
    WideSubquiver V ≃
      Set (Total V) where
  toFun H := { e | e.hom in H e.left e.right }
  invFun S a b := { e | Total.mk a b e in S }

/--
Definition of `Labelling` / `Labelling` 的定义

English:
definition Labelling
  signature: (V : Type u) [Quiver V] (L : Sort*)
  body: forall ⦃a b : V⦄, (a ⟶ b) -> L

中文:
定义 Labelling
  签名: (V : 类型u) [Quiver V] (L : Sort*)
  定义体: forall ⦃a b : V⦄, (a ⟶ b) -> L
-/
def Labelling (V : Type u) [Quiver V] (L : Sort*) :=
  forall ⦃a b : V⦄, (a ⟶ b) -> L

instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (Labelling V L) :=
  ⟨fun _ _ _ => default⟩

end Quiver
