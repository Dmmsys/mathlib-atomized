/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.IsConnected

/-!
# Filtered categories are connected
-/

public section

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-
**CategoryTheory.IsFilteredOrEmpty.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsFilteredOrEmpty`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.I
sFilteredOrEmpty C],   CategoryTheory.IsPreconnected C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isPreconnected`：zigzag_isPreconnected (h : forall 
j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem IsFilteredOrEmpty.isPreconnected [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')
/-
**CategoryTheory.IsCofilteredOrEmpty.isPreconnected** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.IsCofilteredOrEmpty`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.I
sCofilteredOrEmpty C],   CategoryTheory.IsPreconnected C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isPreconnected`：zigzag_isPreconnected (h : forall 
j₁ j₂ : J, Zigzag j₁ j₂) : IsPreconnected J
· 使用定理 `CategoryTheory.Zigzag.trans`：∀ {J : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} J] {j₁ j₂ j₃ : J},   CategoryTheory.Zigzag j₁ j₂ → CategoryTheory.
Zigzag j₂ j₃ → Ca…
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem IsCofilteredOrEmpty.isPreconnected [IsCofilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

attribute [local instance] IsFiltered.nonempty in
/-
**CategoryTheory.IsFiltered.isConnected** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsFiltered`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.I
sFiltered C], CategoryTheory.IsConnected C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsFilteredOrEmpty.isPreconnected`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.IsFilteredOrEmpty C],   Catego
ryTheory.IsPreconnected C
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `CategoryTheory.IsFiltered.nonempty`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.IsFiltered C], Nonempty C
-/
theorem IsFiltered.isConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.isPreconnected C with }

attribute [local instance] IsCofiltered.nonempty in
/-
**CategoryTheory.IsCofiltered.isConnected** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsCofiltered`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.I
sCofiltered C], CategoryTheory.IsConnected C
参数：C : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.isPreconnected`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [CategoryTheory.IsCofilteredOrEmpty C],   Ca
tegoryTheory.IsPreconnected C
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.IsCofiltered.nonempty`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C], Nonempty C
-/
theorem IsCofiltered.isConnected [IsCofiltered C] : IsConnected C :=
  { IsCofilteredOrEmpty.isPreconnected C with }

end CategoryTheory

