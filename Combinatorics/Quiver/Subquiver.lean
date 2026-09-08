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
A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
for every pair of vertices `a b`.
-/
/-
**WideSubquiver** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WideSubquiver (V) [Quiver.{v} V]
参数：V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
for every pair of vertices `a b`.
-/
def WideSubquiver (V) [Quiver.{v} V] :=
  ∀ a b : V, Set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `WideSubquiver`. -/
@[nolint unusedArguments]
/-
**WideSubquiver.toType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WideSubquiver.toType (V) [Quiver V] (_ : WideSubquiver V) : Type u
参数：V；_ : WideSubquiver V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `V`, when thought of as a quiver having only the arrows from
some `WideSubquiver`.
-/
def WideSubquiver.toType (V) [Quiver V] (_ : WideSubquiver V) : Type u :=
  V
/-
**wideSubquiverHasCoeToSort** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：wideSubquiverHasCoeToSort {V} [Quiver V] : CoeSort (WideSubquiver V) (Type
 u) where coe H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance wideSubquiverHasCoeToSort {V} [Quiver V] :
    CoeSort (WideSubquiver V) (Type u) where coe H := WideSubquiver.toType V H

/-- A wide subquiver viewed as a quiver on its own. -/
/-
**WideSubquiver.quiver** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H
参数：H : WideSubquiver V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide subquiver viewed as a quiver on its own.
-/
instance WideSubquiver.quiver {V} [Quiver V] (H : WideSubquiver V) : Quiver H :=
  ⟨fun a b ↦ { f // f ∈ H a b }⟩

namespace Quiver

/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V} [Quiver V] : Bot (WideSubquiver V) :=
  ⟨fun _ _ ↦ ∅⟩
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V} [Quiver V] : Top (WideSubquiver V) :=
  ⟨fun _ _ ↦ Set.univ⟩
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {V} [Quiver V] : Inhabited (WideSubquiver V) :=
  ⟨⊤⟩

-- TODO Unify with `CategoryTheory.Arrow`? (The fields have been named to match.)
/-- `Total V` is the type of _all_ arrows of `V`. -/
@[ext]
/-
**Quiver.Total** 是 Mathlib 中的一个归纳类型，位于命名空间 `Quiver`。
形式化陈述：(V : Type u) → [Quiver V] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Total V` is the type of _all_ arrows of `V`.
-/
structure Total (V : Type u) [Quiver.{v} V] : Type max u v where
  /-- the source vertex of an arrow -/
  left : V
  /-- the target vertex of an arrow -/
  right : V
  /-- an arrow -/
  hom : left ⟶ right

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
/-
**Quiver.wideSubquiverEquivSetTotal** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：wideSubquiverEquivSetTotal {V} [Quiver V] : WideSubquiver V ≃ Set (Total V
) where toFun H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide subquiver of `G` can equivalently be viewed as a total set of arrows.
-/
def wideSubquiverEquivSetTotal {V} [Quiver V] :
    WideSubquiver V ≃
      Set (Total V) where
  toFun H := { e | e.hom ∈ H e.left e.right }
  invFun S a b := { e | Total.mk a b e ∈ S }

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
/-
**Quiver.Labelling** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Labelling (V : Type u) [Quiver V] (L : Sort*)
参数：V : Type u；L : Sort*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `L`-labelling of a quiver assigns to every arrow an element of `L`.
-/
def Labelling (V : Type u) [Quiver V] (L : Sort*) :=
  ∀ ⦃a b : V⦄, (a ⟶ b) → L
/-
**Quiver.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {V : Type u} [Quiver V] (L) [Inhabited L] : Inhabited (Labelling V L) :=
  ⟨fun _ _ _ ↦ default⟩

end Quiver

