/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
/-!

# Light condensed objects

This file defines the category of light condensed objects in a category `C`, following the work
of Clausen-Scholze (see https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).

-/

public section

universe u v w

open CategoryTheory Limits

/--
`LightCondensed.{u} C` is the category of light condensed objects in a category `C`, which are
defined as sheaves on `LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
/-
**LightCondensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondensed (C : Type w) [Category.{v} C]
参数：C : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LightCondensed.{u} C` is the category of light condensed objects in a category 
`C`, which are
defined as sheaves on `LightProfinite.{u}` with respect to the coherent Grothend
ieck topology.
-/
abbrev LightCondensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology LightProfinite.{u}) C

/--
Light condensed sets. Because `LightProfinite` is an essentially small category, we don't need the
same universe bump as in `CondensedSet`.
-/
/-
**LightCondSet** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Light condensed sets. Because `LightProfinite` is an essentially small category,
 we don't need the
same universe bump as in `CondensedSet`.
-/
abbrev LightCondSet := LightCondensed.{u} <| Type u

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

@[deprecated ObjectProperty.FullSubcategory.id_hom (since := "2026-04-08")]
/-
**LightCondensed.id_hom** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：id_hom (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _
参数：X : LightCondensed.{u} C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma id_hom (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
/-
**LightCondensed.comp_hom** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：comp_hom {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).
hom = f.hom ≫ g.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_hom {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
/-
**LightCondensed.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.ap
p S = g.hom.app S) : f = g
参数：f g : X ⟶ Y；h : forall S, f.hom.app S = g.hom.app S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.hom_ext`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂}   [i
nst_1 : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : ∀ S, f.hom.app S = g.hom.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end LightCondensed

namespace LightCondSet

@[deprecated NatTrans.naturality_apply (since := "2026-03-19")]
/-
**LightCondSet.hom_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `LightCondSet`。
形式化陈述：hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProf
initeᵒᵖ} (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map
 g (f.hom.app S x)
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
lemma hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) := by
  simp

end LightCondSet

