/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The empty category

Defines a category structure on `PEmpty`, and the unique functor `PEmpty ⥤ C` for any category `C`.
-/

@[expose] public section

universe w v v' u u'
-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [IsEmpty α] : IsEmpty (Discrete α) := Function.isEmpty Discrete.as

/-- The (unique) functor from an empty category. -/
/-
**CategoryTheory.functorOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：functorOfIsEmpty [IsEmpty C] : C ⥤ D where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) functor from an empty category.
-/
def functorOfIsEmpty [IsEmpty C] : C ⥤ D where
  obj := isEmptyElim
  map := fun {X} ↦ isEmptyElim X
  map_id := fun {X} ↦ isEmptyElim X
  map_comp := fun {X} ↦ isEmptyElim X

variable {C D}

/-- Any two functors out of an empty category are isomorphic. -/
/-
**CategoryTheory.Functor.isEmptyExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] → [IsEmpty C] → (F G 
: CategoryTheory.Functor C D) → F ≅ G
参数：F G : CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two functors out of an empty category are isomorphic.
-/
def Functor.isEmptyExt [IsEmpty C] (F G : C ⥤ D) : F ≅ G :=
  NatIso.ofComponents isEmptyElim (fun {X} ↦ isEmptyElim X)

variable (C D)

/-- The equivalence between two empty categories. -/
/-
**CategoryTheory.equivalenceOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：equivalenceOfIsEmpty [IsEmpty C] [IsEmpty D] : C ≌ D where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between two empty categories.
-/
def equivalenceOfIsEmpty [IsEmpty C] [IsEmpty D] : C ≌ D where
  functor := functorOfIsEmpty C D
  inverse := functorOfIsEmpty D C
  unitIso := Functor.isEmptyExt _ _
  counitIso := Functor.isEmptyExt _ _
  functor_unitIso_comp := isEmptyElim

/-- Equivalence between two empty categories. -/
/-
**CategoryTheory.emptyEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)

--- 原说明 ---
Equivalence between two empty categories.
-/
def emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty := equivalenceOfIsEmpty _ _

namespace Functor

/-- The canonical functor out of the empty category. -/
/-
**CategoryTheory.Functor.empty** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：empty : Discrete.{w} PEmpty ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical functor out of the empty category.
-/
def empty : Discrete.{w} PEmpty ⥤ C :=
  Discrete.functor PEmpty.elim

variable {C}

/-- Any two functors out of the empty category are isomorphic. -/
/-
**CategoryTheory.Functor.emptyExt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：emptyExt (F G : Discrete.{w} PEmpty ⥤ C) : F ≅ G
参数：F G : Discrete.{w} PEmpty ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any two functors out of the empty category are isomorphic.
-/
def emptyExt (F G : Discrete.{w} PEmpty ⥤ C) : F ≅ G :=
  Discrete.natIso fun x => x.as.elim

/-- Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
/-
**CategoryTheory.Functor.uniqueFromEmpty** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：uniqueFromEmpty (F : Discrete.{w} PEmpty ⥤ C) : F ≅ empty C
参数：F : Discrete.{w} PEmpty ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor out of the empty category is isomorphic to the canonical functor fro
m the empty
category.
-/
def uniqueFromEmpty (F : Discrete.{w} PEmpty ⥤ C) : F ≅ empty C :=
  emptyExt _ _

/-- Any two functors out of the empty category are *equal*. You probably want to use
`emptyExt` instead of this.
-/
/-
**CategoryTheory.Functor.empty_ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：empty_ext' (F G : Discrete.{w} PEmpty ⥤ C) : F = G
参数：F G : Discrete.{w} PEmpty ⥤ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Any two functors out of the empty category are *equal*. You probably want to use
`emptyExt` instead of this.
-/
theorem empty_ext' (F G : Discrete.{w} PEmpty ⥤ C) : F = G :=
  Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim

end Functor

end CategoryTheory

