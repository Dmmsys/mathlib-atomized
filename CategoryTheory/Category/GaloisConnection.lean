/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Order.GaloisConnection.Defs

/-!

# Galois connections between preorders are adjunctions.

* `GaloisConnection.adjunction` is the adjunction associated to a Galois connection.

-/

@[expose] public section


universe u v

section

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- A Galois connection between preorders induces an adjunction between the associated categories.
-/
/-
**GaloisConnection.adjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GaloisConnection.adjunction {l : X -> Y} {u : Y -> X} (gc : GaloisConnecti
on l u) : gc.monotone_l.functor ⊣ gc.monotone_u.functor
参数：gc : GaloisConnection l u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u

--- 原说明 ---
A Galois connection between preorders induces an adjunction between the associat
ed categories.
-/
def GaloisConnection.adjunction {l : X → Y} {u : Y → X} (gc : GaloisConnection l u) :
    gc.monotone_l.functor ⊣ gc.monotone_u.functor :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => CategoryTheory.homOfLE (gc.le_u f.le)
          invFun := fun f => CategoryTheory.homOfLE (gc.l_le f.le)
          left_inv := by cat_disch
          right_inv := by cat_disch } }

end

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/-- An adjunction between preorder categories induces a Galois connection.
-/
/-
**CategoryTheory.Adjunction.gc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Adjunct
ion`。
形式化陈述：∀ {X : Type u} {Y : Type v} [inst : Preorder X] [inst_1 : Preorder Y] {L :
 CategoryTheory.Functor X Y}   {R : CategoryTheory.Functor Y X} (adj : L ⊣ R), G
aloisConnection L.obj R.obj
参数：adj : L ⊣ R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An adjunction between preorder categories induces a Galois connection.
-/
theorem Adjunction.gc {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R) : GaloisConnection L.obj R.obj :=
  fun x y =>
  ⟨fun h => ((adj.homEquiv x y).toFun h.hom).le, fun h => ((adj.homEquiv x y).invFun h.hom).le⟩

end CategoryTheory

