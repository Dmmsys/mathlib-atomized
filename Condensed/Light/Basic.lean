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
Definition of `LightCondensed` / `LightCondensed` 的定义

English:
abbreviation LightCondensed
  signature: (C : Type w) [Category.{v} C]
  body: Sheaf (coherentTopology LightProfinite.{u}) C

中文:
缩写 LightCondensed
  签名: (C : Type w) [Category.{v} C]
  定义体: Sheaf (coherentTopology LightProfinite.{u}) C

Depends on / 依赖: LightProfinite, coherentTopology
-/
abbrev LightCondensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology LightProfinite.{u}) C

/--
Definition of `LightCondSet` / `LightCondSet` 的定义

English:
abbreviation LightCondSet
  body: LightCondensed.{u} Type u

中文:
缩写 LightCondSet
  定义体: LightCondensed.{u} Type u

Depends on / 依赖: LightCondensed
-/
abbrev LightCondSet := LightCondensed.{u} Type u

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

@[deprecated ObjectProperty.FullSubcategory.id_hom (since := "2026-04-08")]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (X : LightCondensed.{u} C)
  statement: (𝟙 X : X ⟶ X).hom = 𝟙 _
  proof: rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]

中文:
引理 id_hom
  条件: (X : LightCondensed.{u} C)
  结论: (𝟙 X : X ⟶ X).hom = 𝟙 _
  证明: rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
-/
lemma id_hom (X : LightCondensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]

中文:
引理 comp_hom
  条件: {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
-/
lemma comp_hom {X Y Z : LightCondensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.app S = g.hom.app S)
  proof: by
  apply Sheaf.hom_ext
  ext
  exact h _

中文:
引理 hom_ext
  条件: {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : 对任意 S, f.hom.app S = g.hom.app S)
  证明: by
  apply Sheaf.hom_ext
  ext
  exact h _

Depends on / 依赖: Sheaf.hom_ext, hom_ext
-/
lemma hom_ext {X Y : LightCondensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.app S = g.hom.app S) :
    f = g := by
  apply Sheaf.hom_ext
  ext
  exact h _

end LightCondensed

namespace LightCondSet

@[deprecated NatTrans.naturality_apply (since := "2026-03-19")]
/--
lemma `hom_naturality_apply` / 引理 `hom_naturality_apply`

English:
lemma hom_naturality_apply
  statement: {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
  proof: by
  simp

中文:
引理 hom_naturality_apply
  结论: {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
  证明: by
  simp
-/
lemma hom_naturality_apply {X Y : LightCondSet.{u}} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) := by
  simp

end LightCondSet
