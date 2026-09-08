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

/-- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`. This is hence a form of directed multigraphs.

For graphs with no repeated edges, one can either use `Quiver.IsThin` to demand
that the hom sets are subsingletons, or `Digraph V` (where the hom sets
are Prop-valued).

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
/-
**Quiver** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：Quiver (V : Type u) where /-- The type of edges/arrows/morphisms between a
 given source and target. -/ Hom : V -> V -> Type v  attribute [to_dual self (re
order
参数：V : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertic
es
a type `a ⟶ b` of arrows from `a` to `b`. This is hence a form of directed multi
graphs.

For graphs with no repeated edges, one can either use `Quiver.IsThin` to demand
that the hom sets are subsingletons, or `Digraph V` (where the hom sets
are Prop-valued).

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` 
notation instead.
-/
class Quiver (V : Type u) where
  /-- The type of edges/arrows/morphisms between a given source and target. -/
  Hom : V → V → Type v

attribute [to_dual self (reorder := 3 4)] Quiver.Hom
attribute [to_dual self (reorder := Hom (1 2))] Quiver.mk

/--
Notation for the type of edges/arrows/morphisms between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
/-
**Quiver.opposite** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
形式化陈述：opposite {V} [Quiver V] : Quiver Vᵒᵖ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Vᵒᵖ` reverses the direction of all arrows of `V`.
-/
instance opposite {V} [Quiver V] : Quiver Vᵒᵖ :=
  ⟨fun a b => (unop b ⟶ unop a)ᵒᵖ⟩

/-- The opposite of an arrow in `V`. -/
@[implicit_reducible, to_dual self]
/-
**Quiver.Hom.op** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) → (Opposite.op Y 
⟶ Opposite.op X)
参数：X ⟶ Y；Opposite.op Y ⟶ Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of an arrow in `V`.
-/
def Hom.op {V} [Quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := ⟨f⟩

/-- Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`. -/
@[implicit_reducible, to_dual self]
/-
**Quiver.Hom.unop** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → {X Y : Vᵒᵖ} → (X ⟶ Y) → (Opposite.uno
p Y ⟶ Opposite.unop X)
参数：X ⟶ Y；Opposite.unop Y ⟶ Opposite.unop X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def Hom.unop {V} [Quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := Opposite.unop f

/-- The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`. -/
@[simps, to_dual self]
/-
**Quiver.Hom.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Hom`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → {X Y : V} → (X ⟶ Y) ≃ (Opposite.op Y 
⟶ Opposite.op X)
参数：X ⟶ Y；Opposite.op Y ⟶ Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ (op Y ⟶ op X)`.
-/
def Hom.opEquiv {V} [Quiver V] {X Y : V} : (X ⟶ Y) ≃ (Opposite.op Y ⟶ Opposite.op X) where
  toFun := Opposite.op
  invFun := Opposite.unop

/-- A type synonym for a quiver with no arrows. -/
/-
**Quiver.Empty** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：Empty (V : Type u) : Type u
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for a quiver with no arrows.
-/
def Empty (V : Type u) : Type u := V
/-
**Quiver.emptyQuiver** 是 Mathlib 中的一个实例，位于命名空间 `Quiver`。
形式化陈述：emptyQuiver (V : Type u) : Quiver.{u} (Empty V)
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance emptyQuiver (V : Type u) : Quiver.{u} (Empty V) := ⟨fun _ _ => PEmpty⟩

@[simp, to_dual self]
/-
**Quiver.empty_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty
参数：a b : Empty V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_arrow {V : Type u} (a b : Empty V) : (a ⟶ b) = PEmpty := rfl

/-- A quiver is thin if it has no parallel arrows. -/
/-
**Quiver.IsThin** 是 Mathlib 中的一个缩写定义，位于命名空间 `Quiver`。
形式化陈述：IsThin (V : Type u) [Quiver V] : Prop
参数：V : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quiver is thin if it has no parallel arrows.
-/
abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)

to_dual_insert_cast_fun IsThin := fun inst a b ↦ inst b a, fun inst a b ↦ inst b a


section

variable {V : Type*} [Quiver V] {X Y X' Y' : V}

/-- An arrow in a quiver can be transported across equalities between the source and target
objects. -/
@[to_dual self (reorder := X Y, X' Y', hX hY)]
/-
**Quiver.homOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：homOfEq (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') : X' ⟶ Y'
参数：f : X ⟶ Y；hX : X = X'；hY : Y = Y'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arrow in a quiver can be transported across equalities between the source and
 target
objects.
-/
def homOfEq (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') : X' ⟶ Y' := by
  subst hX hY
  exact f

@[simp, to_dual self]
/-
**Quiver.homOfEq_trans** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_trans (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') {X'' Y'' : V} (hX' :
 X' = X'') (hY' : Y' = Y'') : homOfEq (homOfEq f hX hY) hX' hY' = homOfEq f (hX.
trans hX') (hY.trans hY')
参数：f : X ⟶ Y；hX : X = X'；hY : Y = Y'；hX' : X' = X''；hY' : Y' = Y''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma homOfEq_trans (f : X ⟶ Y) (hX : X = X') (hY : Y = Y')
    {X'' Y'' : V} (hX' : X' = X'') (hY' : Y' = Y'') :
    homOfEq (homOfEq f hX hY) hX' hY' = homOfEq f (hX.trans hX') (hY.trans hY') := by
  subst hX hY hX' hY'
  rfl

@[to_dual self]
/-
**Quiver.homOfEq_injective** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_injective (hX : X = X') (hY : Y = Y') {f g : X ⟶ Y} (h : Quiver.ho
mOfEq f hX hY = Quiver.homOfEq g hX hY) : f = g
参数：hX : X = X'；hY : Y = Y'；h : Quiver.homOfEq f hX hY = Quiver.homOfEq g hX hY。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfEq_injective (hX : X = X') (hY : Y = Y')
    {f g : X ⟶ Y} (h : Quiver.homOfEq f hX hY = Quiver.homOfEq g hX hY) : f = g := by
  subst hX hY
  exact h

@[simp, to_dual self]
/-
**Quiver.homOfEq_rfl** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_rfl (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homOfEq_rfl (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl = f := rfl

@[to_dual self]
/-
**Quiver.heq_of_homOfEq_ext** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：heq_of_homOfEq_ext (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} 
(e : Quiver.homOfEq f hX hY = f') : f ≍ f'
参数：hX : X = X'；hY : Y = Y'；e : Quiver.homOfEq f hX hY = f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.homOfEq_rfl`：homOfEq_rfl (f : X ⟶ Y) : Quiver.homOfEq f rfl rfl =
 f
-/
lemma heq_of_homOfEq_ext (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Quiver.homOfEq f hX hY = f') : f ≍ f' := by
  subst hX hY
  rw [Quiver.homOfEq_rfl] at e
  rw [e]

@[to_dual self]
/-
**Quiver.homOfEq_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_eq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') : Qui
ver.homOfEq f hX hY = g ↔ f = Quiver.homOfEq g hX.symm hY.symm
参数：f : X ⟶ Y；g : X' ⟶ Y'；hX : X = X'；hY : Y = Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma homOfEq_eq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    Quiver.homOfEq f hX hY = g ↔ f = Quiver.homOfEq g hX.symm hY.symm := by
  subst hX hY; simp

@[to_dual self]
/-
**Quiver.eq_homOfEq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：eq_homOfEq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) : f =
 Quiver.homOfEq g hX hY ↔ Quiver.homOfEq f hX.symm hY.symm = g
参数：f : X ⟶ Y；g : X' ⟶ Y'；hX : X' = X；hY : Y' = Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eq_homOfEq_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f = Quiver.homOfEq g hX hY ↔ Quiver.homOfEq f hX.symm hY.symm = g := by
  subst hX hY; simp

@[to_dual self]
/-
**Quiver.homOfEq_heq** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_heq (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) : homOfEq f hX hY ≍ f
参数：hX : X = X'；hY : Y = Y'；f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HEq.symm`：∀ {α β : Sort u} {a : α} {b : β}, a ≍ b → b ≍ a
· 使用引理 `Quiver.heq_of_homOfEq_ext`：heq_of_homOfEq_ext (hX : X = X') (hY : Y = Y'
) {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Quiver.homOfEq f hX hY = f') : f ≍ f'
-/
lemma homOfEq_heq (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) : homOfEq f hX hY ≍ f :=
  (heq_of_homOfEq_ext hX hY rfl).symm

@[to_dual self]
/-
**Quiver.homOfEq_heq_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_heq_left_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y')
 : homOfEq f hX hY ≍ g ↔ f ≍ g
参数：f : X ⟶ Y；g : X' ⟶ Y'；hX : X = X'；hY : Y = Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma homOfEq_heq_left_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    homOfEq f hX hY ≍ g ↔ f ≍ g := by
  cases hX; cases hY; rfl

@[to_dual self]
/-
**Quiver.homOfEq_heq_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quiver`。
形式化陈述：homOfEq_heq_right_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y
) : f ≍ homOfEq g hX hY ↔ f ≍ g
参数：f : X ⟶ Y；g : X' ⟶ Y'；hX : X' = X；hY : Y' = Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma homOfEq_heq_right_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X' = X) (hY : Y' = Y) :
    f ≍ homOfEq g hX hY ↔ f ≍ g := by
  cases hX; cases hY; rfl


end

end Quiver

