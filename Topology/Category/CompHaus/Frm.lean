/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Frm
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Sets.Opens

/-! The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/

@[expose] public section

universe u

open TopologicalSpace Opposite CategoryTheory

/-- The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/
@[simps]
/--
Definition of `topCatOpToFrm` / `topCatOpToFrm` 的定义

English:
definition topCatOpToFrm
  signature: : TopCatᵒᵖ ⥤ Frm where
  body: Frm.of (Opens (unop X : TopCat))
map f := Frm.ofHom Opens.comap (Quiver.Hom.unop f).hom

中文:
定义 topCatOpToFrm
  签名: : TopCatᵒᵖ ⥤ 框架 where
  定义体: Frm.of (Opens (unop X : TopCat))
map f := Frm.ofHom Opens.comap (Quiver.Hom.unop f).hom

Depends on / 依赖: Frm.of, TopCat
-/
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where
  obj X := Frm.of (Opens (unop X : TopCat))
map f := Frm.ofHom Opens.comap (Quiver.Hom.unop f).hom

-- Note, `CompHaus` is too strong. We only need `T0Space`.
/--
Instance `CompHausOpToFrame.faithful` / 实例 `CompHausOpToFrame.faithful`

English:
instance CompHausOpToFrame.faithful
  signature: : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful
  body: ⟨fun {X _ _ _} h => Quiver.Hom.unop_inj ConcreteCategory.ext
Opens.comap_injective (β := (unop X).toTop) FrameHom.ext
      CategoryTheory.congr_fun h⟩

中文:
实例 CompHausOpToFrame.faithful
  签名: : (compHausToTop.op ⋙ topCatOpToFrm.{u}).忠实
  定义体: ⟨fun {X _ _ _} h => Quiver.Hom.unop_inj ConcreteCategory.ext
Opens.comap_injective (β := (unop X).toTop) FrameHom.ext
      CategoryTheory.congr_fun h⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, ConcreteCategory, ConcreteCategory.ext, FrameHom, FrameHom.ext, Opens.comap_injective, Quiver, Quiver.Hom.unop_inj, comap_injective, congr_fun, unop_inj
-/
instance CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful :=
⟨fun {X _ _ _} h => Quiver.Hom.unop_inj ConcreteCategory.ext
Opens.comap_injective (β := (unop X).toTop) FrameHom.ext
      CategoryTheory.congr_fun h⟩
