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
Definition of `Condensed` / `Condensed` 的定义

English:
abbreviation Condensed
  signature: (C : Type w) [Category.{v} C]
  body: Sheaf (coherentTopology CompHaus.{u}) C

中文:
缩写 Condensed
  签名: (C : Type w) [Category.{v} C]
  定义体: Sheaf (coherentTopology CompHaus.{u}) C

Depends on / 依赖: CompHaus, coherentTopology
-/
abbrev Condensed (C : Type w) [Category.{v} C] :=
  Sheaf (coherentTopology CompHaus.{u}) C

/--
Definition of `CondensedSet` / `CondensedSet` 的定义

English:
abbreviation CondensedSet
  body: Condensed.{u} Type (u + 1)

中文:
缩写 CondensedSet
  定义体: Condensed.{u} Type (u + 1)

Depends on / 依赖: Condensed
-/
abbrev CondensedSet := Condensed.{u} Type (u + 1)

namespace Condensed

variable {C : Type w} [Category.{v} C]

@[deprecated ObjectProperty.FullSubcategory.id_hom (since := "2026-04-08")]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (X : Condensed.{u} C)
  statement: (𝟙 X : X ⟶ X).hom = 𝟙 _
  proof: rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]

中文:
引理 id_hom
  条件: (X : Condensed.{u} C)
  结论: (𝟙 X : X ⟶ X).hom = 𝟙 _
  证明: rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
-/
lemma id_hom (X : Condensed.{u} C) : (𝟙 X : X ⟶ X).hom = 𝟙 _ := rfl

@[deprecated ObjectProperty.FullSubcategory.comp_hom (since := "2026-04-08")]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g).hom = f.hom ≫ g.hom
  proof: rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]

中文:
引理 comp_hom
  条件: {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g).hom = f.hom ≫ g.hom
  证明: rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
-/
lemma comp_hom {X Y Z : Condensed.{u} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[deprecated (since := "2026-03-05")] alias id_val := id_hom
@[deprecated (since := "2026-03-05")] alias comp_val := comp_hom

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.app S = g.hom.app S)
  proof: by
  ext
  exact h _

中文:
引理 hom_ext
  条件: {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : 对任意 S, f.hom.app S = g.hom.app S)
  证明: by
  ext
  exact h _
-/
lemma hom_ext {X Y : Condensed.{u} C} (f g : X ⟶ Y) (h : forall S, f.hom.app S = g.hom.app S) :
    f = g := by
  ext
  exact h _

end Condensed

namespace CondensedSet

@[deprecated NatTrans.naturality_apply (since := "2026-03-19")]
/--
lemma `hom_naturality_apply` / 引理 `hom_naturality_apply`

English:
lemma hom_naturality_apply
  statement: {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
  proof: by
  simp

中文:
引理 hom_naturality_apply
  结论: {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
  证明: by
  simp
-/
lemma hom_naturality_apply {X Y : CondensedSet.{u}} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) := by
  simp

end CondensedSet
