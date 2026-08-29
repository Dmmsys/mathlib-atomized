/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!

# Filtered colimits in the category of `R`-algebras

In this file we show that the forgetful functor from `R`-algebras to rings
creates filtered colimits.
-/

public section

universe w v u

open CategoryTheory Limits

variable {R : Type u} [CommRing R] {J : Type*} [Category* J] {F : J ⥤ AlgCat.{v} R}
  [PreservesColimitsOfShape J (forget RingCat.{v})]

section

variable {c : Cocone (F ⋙ forget₂ _ RingCat)} [IsFilteredOrEmpty J]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `AlgCat.algebraOfIsFiltered` / `AlgCat.algebraOfIsFiltered` 的定义

English:
abbreviation AlgCat.algebraOfIsFiltered
  signature: (hc : IsColimit c) (j : J)
  body: .toAlgebra' by (c.ι.app j).hom.comp (algebraMap R (F.obj j))
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    simp [← dsimp% c.w hjk, ← dsimp% (c.ι.app k).hom.map_mul, Algebra.commutes']

中文:
缩写 Alg范畴.algebraOfIsFiltered
  签名: (hc : 是余极限 c) (j : J)
  定义体: .toAlgebra' by (c.ι.app j).hom.comp (algebraMap R (F.obj j))
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    simp [← dsimp% c.w hjk, ← dsimp% (c.ι.app k).hom.map_mul, Algebra.commutes']
-/
private abbrev AlgCat.algebraOfIsFiltered (hc : IsColimit c) (j : J) : Algebra R c.pt :=
.toAlgebra' by (c.ι.app j).hom.comp (algebraMap R (F.obj j))
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    simp [← dsimp% c.w hjk, ← dsimp% (c.ι.app k).hom.map_mul, Algebra.commutes']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `AlgCat.coconeOfIsFiltered` / `AlgCat.coconeOfIsFiltered` 的定义

English:
definition AlgCat.coconeOfIsFiltered
  signature: (hc : IsColimit c) (j : J)
  body: letI : Algebra R c.pt := algebraOfIsFiltered hc j
    AlgCat.of R c.pt
  ι.app k := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply _ _

中文:
定义 Alg范畴.coconeOfIsFiltered
  签名: (hc : 是余极限 c) (j : J)
  定义体: letI : Algebra R c.pt := algebraOfIsFiltered hc j
    AlgCat.of R c.pt
  ι.app k := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply _ _
-/
private def AlgCat.coconeOfIsFiltered (hc : IsColimit c) (j : J) : Cocone F where
  pt :=
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    AlgCat.of R c.pt
  ι.app k := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← c.w (IsFiltered.leftToMax j k),
      ← c.w (IsFiltered.rightToMax j k)]
  ι.naturality k k' f := by
    ext
    exact c.ι.naturality_apply _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `AlgCat.isColimitCoconeOfIsFiltered` / `AlgCat.isColimitCoconeOfIsFiltered` 的定义

English:
definition AlgCat.isColimitCoconeOfIsFiltered
  signature: (hc : IsColimit c) (j : J)
  body: by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j => ?_) _)
    ext
    exact congr($(hm _) _)

中文:
定义 Alg范畴.isColimitCoconeOfIsFiltered
  签名: (hc : 是余极限 c) (j : J)
  定义体: by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j => ?_) _)
    ext
    exact congr($(hm _) _)
-/
private def AlgCat.isColimitCoconeOfIsFiltered (hc : IsColimit c) (j : J) :
    IsColimit (AlgCat.coconeOfIsFiltered hc j) where
  desc s := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    simp [RingHom.algebraMap_toAlgebra', ← ConcreteCategory.comp_apply]
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j => ?_) _)
    ext
    exact congr($(hm _) _)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: J] :
  body: createsColimitOfReflectsIso fun _ hc =>
    ⟨⟨AlgCat.coconeOfIsFiltered hc IsFiltered.nonempty.some, Iso.refl _⟩,
      AlgCat.isColimitCoconeOfIsFiltered _ _⟩

中文:
实例 [是Filtered
  签名: J] :
  定义体: createsColimitOfReflectsIso fun _ hc =>
    ⟨⟨AlgCat.coconeOfIsFiltered hc IsFiltered.nonempty.some, Iso.refl _⟩,
      AlgCat.isColimitCoconeOfIsFiltered _ _⟩
-/
@[no_expose] noncomputable instance [IsFiltered J] :
    CreatesColimitsOfShape J (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hc =>
    ⟨⟨AlgCat.coconeOfIsFiltered hc IsFiltered.nonempty.some, Iso.refl _⟩,
      AlgCat.isColimitCoconeOfIsFiltered _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiltered
  signature: J] [HasColimitsOfShape J RingCat.{v}] :
  body: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget₂ _ RingCat.{v})

中文:
实例 [是Filtered
  签名: J] [有形状余极限 J 环范畴.{v}] :
  定义体: hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget₂ _ RingCat.{v})

Depends on / 依赖: RingCat, hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
-/
noncomputable instance [IsFiltered J] [HasColimitsOfShape J RingCat.{v}] :
    HasColimitsOfShape J (AlgCat.{v} R) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget₂ _ RingCat.{v})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFilteredColimits (forget₂ (AlgCat.{v} R) RingCat.{v})
  body: inferInstance

中文:
实例 :
  签名: PreservesFilteredColimits (forget₂ (Alg范畴.{v} R) 环范畴.{v})
  定义体: inferInstance
-/
instance : PreservesFilteredColimits (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  preserves_filtered_colimits _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFilteredColimits (forget (AlgCat.{v} R))
  body: Limits.comp_preservesFilteredColimits (forget₂ _ _) (forget RingCat.{v})

中文:
实例 :
  签名: PreservesFilteredColimits (forget (Alg范畴.{v} R))
  定义体: Limits.comp_preservesFilteredColimits (forget₂ _ _) (forget RingCat.{v})

Depends on / 依赖: Limits, Limits.comp_preservesFilteredColimits, RingCat, comp_preservesFilteredColimits, forget
-/
instance : PreservesFilteredColimits (forget (AlgCat.{v} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ _ _) (forget RingCat.{v})
