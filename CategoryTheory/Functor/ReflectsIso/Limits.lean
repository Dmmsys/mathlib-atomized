/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Exactness of families of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a conservative family of functors (i.e. they jointly
reflect isomorphisms). Let `G : J ⥤ C` be a functor that has a limit that
is preserved by the functors `Fᵢ`. In this file, we show that a cone for `G`
is a limit if it is so after applying the functors `Fᵢ`.

-/

@[expose] public section

namespace CategoryTheory.JointlyReflectIsomorphisms
open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I -> Type*} [forall i, Category (D i)]
  {F : forall i, C ⥤ D i} (hF : JointlyReflectIsomorphisms F)
  {J : Type*} [Category* J] {G : J ⥤ C}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `jointlyReflectsLimit` / `jointlyReflectsLimit` 的定义

English:
definition jointlyReflectsLimit
  body: by
  suffices IsIso (limit.lift _ c) from
    IsLimit.ofIsoLimit (limit.isLimit _)
      (Cone.ext (asIso (limit.lift _ c) :)).symm
  rw [hF.isIso_iff]
  intro i
  let H := isLimitOfPreserves (F i) (limit.isLimit G)
  let e := IsLimit.conePointUniqueUpToIso (hc i) H
  have : e.hom = (F i).map (limit.lift G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsLimit.conePointUniqueUpToIso_hom_comp (hc i) H j)
  rw [← this]
  infer_instance

中文:
定义 jointlyReflectsLimit
  定义体: by
  suffices IsIso (limit.lift _ c) from
    IsLimit.ofIsoLimit (limit.isLimit _)
      (Cone.ext (asIso (limit.lift _ c) :)).symm
  rw [hF.isIso_iff]
  intro i
  let H := isLimitOfPreserves (F i) (limit.isLimit G)
  let e := IsLimit.conePointUniqueUpToIso (hc i) H
  have : e.hom = (F i).map (limit.lift G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsLimit.conePointUniqueUpToIso_hom_comp (hc i) H j)
  rw [← this]
  infer_instance

Depends on / 依赖: Cone.ext, Functor, Functor.map_comp, H.hom_ext, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.conePointUniqueUpToIso_hom_comp, IsLimit.ofIsoLimit, conePointUniqueUpToIso, conePointUniqueUpToIso_hom_comp, e.hom, hF.isIso_iff, hom_ext, infer_instance, isIso_iff, isLimit, isLimitOfPreserves, limit.isLimit, limit.lift, map_comp
-/
noncomputable def jointlyReflectsLimit
    {c : Cone G} (hc : forall i, IsLimit ((F i).mapCone c))
    [HasLimit G] [forall i, PreservesLimit G (F i)] :
    IsLimit c := by
  suffices IsIso (limit.lift _ c) from
    IsLimit.ofIsoLimit (limit.isLimit _)
      (Cone.ext (asIso (limit.lift _ c) :)).symm
  rw [hF.isIso_iff]
  intro i
  let H := isLimitOfPreserves (F i) (limit.isLimit G)
  let e := IsLimit.conePointUniqueUpToIso (hc i) H
  have : e.hom = (F i).map (limit.lift G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsLimit.conePointUniqueUpToIso_hom_comp (hc i) H j)
  rw [← this]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `jointlyReflectsColimit` / `jointlyReflectsColimit` 的定义

English:
definition jointlyReflectsColimit
  body: by
  suffices IsIso (colimit.desc _ c) from
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (colimit.desc _ c) :))
  rw [hF.isIso_iff]
  intro i
  let H := isColimitOfPreserves (F i) (colimit.isColimit G)
  let e := IsColimit.coconePointUniqueUpToIso H (hc i)
  have : e.hom = (F i).map (colimit.desc G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsColimit.comp_coconePointUniqueUpToIso_hom H (hc i) j)
  rw [← this]
  infer_instance

中文:
定义 jointlyReflectsColimit
  定义体: by
  suffices IsIso (colimit.desc _ c) from
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (colimit.desc _ c) :))
  rw [hF.isIso_iff]
  intro i
  let H := isColimitOfPreserves (F i) (colimit.isColimit G)
  let e := IsColimit.coconePointUniqueUpToIso H (hc i)
  have : e.hom = (F i).map (colimit.desc G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsColimit.comp_coconePointUniqueUpToIso_hom H (hc i) j)
  rw [← this]
  infer_instance

Depends on / 依赖: Cocone, Cocone.ext, Functor, Functor.map_comp, H.hom_ext, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, IsColimit.ofIsoColimit, coconePointUniqueUpToIso, colimit, colimit.desc, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, e.hom, hF.isIso_iff, hom_ext, infer_instance, isColimit, isColimitOfPreserves
-/
noncomputable def jointlyReflectsColimit
    {c : Cocone G} (hc : forall i, IsColimit ((F i).mapCocone c))
    [HasColimit G] [forall i, PreservesColimit G (F i)] :
    IsColimit c := by
  suffices IsIso (colimit.desc _ c) from
    IsColimit.ofIsoColimit (colimit.isColimit _)
      (Cocone.ext (asIso (colimit.desc _ c) :))
  rw [hF.isIso_iff]
  intro i
  let H := isColimitOfPreserves (F i) (colimit.isColimit G)
  let e := IsColimit.coconePointUniqueUpToIso H (hc i)
  have : e.hom = (F i).map (colimit.desc G c) :=
    H.hom_ext (fun j => by
      simpa [← Functor.map_comp] using
        IsColimit.comp_coconePointUniqueUpToIso_hom H (hc i) j)
  rw [← this]
  infer_instance

end CategoryTheory.JointlyReflectIsomorphisms
