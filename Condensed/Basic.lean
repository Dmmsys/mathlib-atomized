/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Category.CompHaus.EffectiveEpi

/-!

# Condensed Objects

This file defines the category of condensed objects in a category `C`, following the work
of Clausen-Scholze and Barwick-Haine.

## Implementation Details

We use the coherent Grothendieck topology on `CompHaus`, and define condensed objects in `C` to
be `C`-valued sheaves, with respect to this Grothendieck topology.

Note: Our definition more closely resembles "Pyknotic objects" in the sense of Barwick-Haine,
as we do not impose cardinality bounds, and manage universes carefully instead.

## References

- [barwickhaine2019]: *Pyknotic objects, I. Basic notions*, 2019.
- [scholze2019condensed]: *Lectures on Condensed Mathematics*, 2019.

-/

public section

open CategoryTheory Limits

open CategoryTheory

universe u v w

/--
`Condensed.{u} C` is the category of condensed objects in a category `C`, which are
defined as sheaves on `CompHaus.{u}` with respect to the coherent Grothendieck topology.
-/
/-
**Condensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Condensed (C : Type w) [Category.{v} C]
参数：C : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Condensed.{u} C` is the category of condensed objects in a category `C`, which 
are
defined as sheaves on `CompHaus.{u}` with respect to the coherent Grothendieck t
opology.
-/
abbrev Condensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology CompHaus.{u}) C

/--
Condensed sets (types) with the appropriate universe levels, i.e. `Type (u + 1)`-valued
sheaves on `CompHaus.{u}`.
-/
/-
**CondensedSet** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CondensedSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condensed sets (types) with the appropriate universe levels, i.e. `Type (u + 1)`
-valued
sheaves on `CompHaus.{u}`.
-/
abbrev CondensedSet := Condensed.{u} <| Type (u + 1)

namespace Condensed

variable {C : Type w} [Category.{v} C]

@[deprecated ObjectProperty.FullSubcategory.id_hom (since := "2026-04-08")]
/-
**Condensed.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：id_hom (X : Condensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _
参数：X : Condensed.{u} C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (X : Condensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
/-
**Condensed.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：comp_hom {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom =
 f.hom ≫ g.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
/-
**Condensed.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.app S =
 g.hom.app S) : f = g
参数：f g : X ⟶ Y；h : forall S, f.hom.app S = g.hom.app S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.hom.app S = g.hom.app S) :
    f = g := by
  ext
  exact h _

end Condensed

namespace CondensedSet

@[deprecated NatTrans.naturality_apply (since := "2026-03-19")]
/-
**CondensedSet.hom_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `CondensedSet`。
形式化陈述：hom_naturality_apply {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒ
ᵖ} (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.
hom.app S x)
参数：f : X ⟶ Y；g : S ⟶ T；x : X.obj.obj S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_naturality_apply {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) := by
  simp

end CondensedSet

