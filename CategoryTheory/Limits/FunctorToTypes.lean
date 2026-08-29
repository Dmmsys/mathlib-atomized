/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Concrete description of (co)limits in functor categories

Some of the concrete descriptions of (co)limits in `Type v` extend to (co)limits in the functor
category `K ⥤ Type v`.
-/

public section

namespace CategoryTheory.FunctorToTypes

open CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (F : J ⥤ K ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `jointly_surjective` / 定理 `jointly_surjective`

English:
theorem jointly_surjective
  statement: (k : K) {t : Cocone F} (h : IsColimit t) (x : t.pt.obj k)
  proof: by
  let hev := isColimitOfPreserves ((evaluation _ _).obj k) h
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ hev x
  exact ⟨j, y, by simp⟩

中文:
定理 jointly_surjective
  结论: (k : K) {t : 余锥 F} (h : 是余极限 t) (x : t.pt.obj k)
  证明: by
  let hev := isColimitOfPreserves ((evaluation _ _).obj k) h
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ hev x
  exact ⟨j, y, by simp⟩

Depends on / 依赖: Types.jointly_surjective, evaluation, isColimitOfPreserves, jointly_surjective
-/
theorem jointly_surjective (k : K) {t : Cocone F} (h : IsColimit t) (x : t.pt.obj k)
    [forall k, HasColimit (F.flip.obj k)] : exists j y, x = (t.ι.app j).app k y := by
  let hev := isColimitOfPreserves ((evaluation _ _).obj k) h
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective _ hev x
  exact ⟨j, y, by simp⟩

/--
theorem `jointly_surjective'` / 定理 `jointly_surjective'`

English:
theorem jointly_surjective'
  given: [forall k, HasColimit (F.flip.obj k)] (k : K) (x : (colimit F).obj k)
  proof: jointly_surjective _ _ (colimit.isColimit _) x

中文:
定理 jointly_surjective'
  条件: [对任意 k, 有余极限 (F.flip.obj k)] (k : K) (x : (colimit F).obj k)
  证明: jointly_surjective _ _ (colimit.isColimit _) x

Depends on / 依赖: colimit, colimit.isColimit, isColimit, jointly_surjective
-/
theorem jointly_surjective' [forall k, HasColimit (F.flip.obj k)] (k : K) (x : (colimit F).obj k) :
    exists j y, x = (colimit.ι F j).app k y :=
  jointly_surjective _ _ (colimit.isColimit _) x

/--
theorem `colimit.map_ι_apply` / 定理 `colimit.map_ι_apply`

English:
theorem colimit.map_ι_apply
  given: [HasColimit F] (j : J) {k k' : K} {f : k ⟶ k'} {x}
  proof: ConcreteCategory.congr_hom ((colimit.ι F j).naturality _).symm _

中文:
定理 colimit.map_ι_apply
  条件: [有余极限 F] (j : J) {k k' : K} {f : k ⟶ k'} {x}
  证明: ConcreteCategory.congr_hom ((colimit.ι F j).naturality _).symm _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, colimit, congr_hom, naturality
-/
theorem colimit.map_ι_apply [HasColimit F] (j : J) {k k' : K} {f : k ⟶ k'} {x} :
    (colimit F).map f ((colimit.ι F j).app _ x) = (colimit.ι F j).app _ ((F.obj j).map f x) :=
  ConcreteCategory.congr_hom ((colimit.ι F j).naturality _).symm _

end CategoryTheory.FunctorToTypes
