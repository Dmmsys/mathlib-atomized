/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Colimits of LocallyRingedSpace

We construct the explicit coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forgetToSheafedSpace` preserves them.

-/

@[expose] public section


namespace AlgebraicGeometry

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace SheafedSpace

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [Category.{w'} J] [Small.{v} J] (F : J ⥤ SheafedSpace.{_, _, v} C)

/--
theorem `isColimit_exists_rep` / 定理 `isColimit_exists_rep`

English:
theorem isColimit_exists_rep
  given: [HasLimitsOfShape Jᵒᵖ C] {c : Cocone F} (hc : IsColimit c) (x : c.pt)
  proof: Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x

中文:
定理 isColimit_存在_rep
  条件: [有形状极限 Jᵒᵖ C] {c : 余锥 F} (hc : 是余极限 c) (x : c.pt)
  证明: Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x

Depends on / 依赖: Concrete, Concrete.isColimit_exists_rep, forget, isColimitOfPreserves, isColimit_exists_rep
-/
theorem isColimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] {c : Cocone F} (hc : IsColimit c) (x : c.pt) :
    exists (i : J) (y : F.obj i), (c.ι.app i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ forget C) (isColimitOfPreserves (forget C) hc) x

-- Porting note: argument `C` of colimit need to be made explicit, otherwise we get universe issues
/--
theorem `colimit_exists_rep` / 定理 `colimit_exists_rep`

English:
theorem colimit_exists_rep
  given: [HasLimitsOfShape Jᵒᵖ C] (x : colimit (C := SheafedSpace C) F)
  proof: Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x

中文:
定理 colimit_存在_rep
  条件: [有形状极限 Jᵒᵖ C] (x : colimit (C := Sheafed空间 C) F)
  证明: Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x

Depends on / 依赖: SheafedSpace
-/
theorem colimit_exists_rep [HasLimitsOfShape Jᵒᵖ C] (x : colimit (C := SheafedSpace C) F) :
    exists (i : J) (y : F.obj i), (colimit.ι F i).hom.base y = x :=
  Concrete.isColimit_exists_rep (F ⋙ SheafedSpace.forget C)
    (isColimitOfPreserves (SheafedSpace.forget _) (colimit.isColimit F)) x

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] {X Y
  body: by
  rw [← show _ = (coequalizer.π f g).hom.base from
      ι_comp_coequalizerComparison f g (SheafedSpace.forget C)]; rw [← PreservesCoequalizer.iso_hom]
  apply epi_comp

中文:
实例 [有极限
  签名: C] {X Y
  定义体: by
  rw [← show _ = (coequalizer.π f g).hom.base from
      ι_comp_coequalizerComparison f g (SheafedSpace.forget C)]; rw [← PreservesCoequalizer.iso_hom]
  apply epi_comp

Depends on / 依赖: PreservesCoequalizer, PreservesCoequalizer.iso_hom, SheafedSpace, SheafedSpace.forget, coequalizer, epi_comp, forget, hom.base, iso_hom
-/
instance [HasLimits C] {X Y : SheafedSpace C} (f g : X ⟶ Y) :
    Epi (coequalizer.π f g).hom.base := by
  rw [← show _ = (coequalizer.π f g).hom.base from
      ι_comp_coequalizerComparison f g (SheafedSpace.forget C)]; rw [← PreservesCoequalizer.iso_hom]
  apply epi_comp

end SheafedSpace

namespace LocallyRingedSpace

section HasCoproducts

variable {ι : Type v} [Small.{u} ι] (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/--
Definition of `coproduct` / `coproduct` 的定义

English:
definition coproduct
  signature: : LocallyRingedSpace where
  body: colimit (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
    (F ⋙ forgetToSheafedSpace)
  isLocalRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    have : IsLocalRing (((F ⋙ forgetToSheafedSpace).obj i).presheaf.stalk y) :=
      (F.obj i).isLocalRing _
    exact
      (asIso ((colimit.ι (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
        (F ⋙ forgetToSheafedSpace) i :).hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

中文:
定义 coproduct
  签名: : LocallyRinged空间 where
  定义体: colimit (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
    (F ⋙ forgetToSheafedSpace)
  isLocalRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    have : IsLocalRing (((F ⋙ forgetToSheafedSpace).obj i).presheaf.stalk y) :=
      (F.obj i).isLocalRing _
    exact
      (asIso ((colimit.ι (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
        (F ⋙ forgetToSheafedSpace) i :).hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

Depends on / 依赖: CommRingCat, SheafedSpace, colimit
-/
noncomputable def coproduct : LocallyRingedSpace where
  toSheafedSpace := colimit (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
    (F ⋙ forgetToSheafedSpace)
  isLocalRing x := by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
    have : IsLocalRing (((F ⋙ forgetToSheafedSpace).obj i).presheaf.stalk y) :=
      (F.obj i).isLocalRing _
    exact
      (asIso ((colimit.ι (C := SheafedSpace.{u + 1, u, u} CommRingCat.{u})
        (F ⋙ forgetToSheafedSpace) i :).hom.stalkMap y)).symm.commRingCatIsoToRingEquiv.isLocalRing

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coproductCofan` / `coproductCofan` 的定义

English:
definition coproductCofan
  signature: : Cocone F where
  body: coproduct F
  ι :=
    { app j := LocallyRingedSpace.homMk (colimit.ι (F ⋙ forgetToSheafedSpace) j)
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; simp }

中文:
定义 coproductCofan
  签名: : 余锥 F where
  定义体: coproduct F
  ι :=
    { app j := LocallyRingedSpace.homMk (colimit.ι (F ⋙ forgetToSheafedSpace) j)
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; simp }

Depends on / 依赖: coproduct
-/
noncomputable def coproductCofan : Cocone F where
  pt := coproduct F
  ι :=
    { app j := LocallyRingedSpace.homMk (colimit.ι (F ⋙ forgetToSheafedSpace) j)
      naturality := fun ⟨j⟩ ⟨j'⟩ ⟨⟨(f : j = j')⟩⟩ => by subst f; simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coproductCofanIsColimit` / `coproductCofanIsColimit` 的定义

English:
definition coproductCofanIsColimit
  signature: : IsColimit (coproductCofan F) where
  body: LocallyRingedSpace.homMk (colimit.desc
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) (by
        intro x
        obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
        have := PresheafedSpace.stalkMap.comp
          (colimit.ι (F ⋙ forgetToSheafedSpace) i).hom
          (colimit.desc (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)).hom y
        simp only [← IsIso.comp_inv_eq,
          ← InducedCategory.comp_hom,
          PresheafedSpace.stalkMap.congr_hom _ _
            (congr_arg (InducedCategory.Hom.hom) (colimit.ι_desc
              (forgetToSheafedSpace.mapCocone s) i))] at this
        rw [← this]
        dsimp
        infer_instance)
  fac _ _ :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
     (colimit.ι_desc (C := SheafedSpace _) _ _)
  uniq s f h :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.toShHom fun j =>
        congr_arg LocallyRingedSpace.Hom.toShHom (h j))

中文:
定义 coproductCofanIsColimit
  签名: : 是余极限 (coproductCofan F) where
  定义体: LocallyRingedSpace.homMk (colimit.desc
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) (by
        intro x
        obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
        have := PresheafedSpace.stalkMap.comp
          (colimit.ι (F ⋙ forgetToSheafedSpace) i).hom
          (colimit.desc (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)).hom y
        simp only [← IsIso.comp_inv_eq,
          ← InducedCategory.comp_hom,
          PresheafedSpace.stalkMap.congr_hom _ _
            (congr_arg (InducedCategory.Hom.hom) (colimit.ι_desc
              (forgetToSheafedSpace.mapCocone s) i))] at this
        rw [← this]
        dsimp
        infer_instance)
  fac _ _ :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
     (colimit.ι_desc (C := SheafedSpace _) _ _)
  uniq s f h :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.toShHom fun j =>
        congr_arg LocallyRingedSpace.Hom.toShHom (h j))

Depends on / 依赖: InducedCategory, InducedCategory.Hom.hom, InducedCategory.comp_hom, IsIso.comp_inv_eq, LocallyRingedSpace, LocallyRingedSpace.homMk, PresheafedSpace, PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.congr_hom, SheafedSpace, SheafedSpace.colimit_exists_rep, colimit, colimit.desc, colimit_exists_rep, comp_hom, comp_inv_eq, congr_arg, congr_hom, forgetToSheafedSpace, forgetToSheafedSpace.mapCocone
-/
noncomputable def coproductCofanIsColimit : IsColimit (coproductCofan F) where
  desc s :=
    LocallyRingedSpace.homMk (colimit.desc
      (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)) (by
        intro x
        obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forgetToSheafedSpace) x
        have := PresheafedSpace.stalkMap.comp
          (colimit.ι (F ⋙ forgetToSheafedSpace) i).hom
          (colimit.desc (F ⋙ forgetToSheafedSpace) (forgetToSheafedSpace.mapCocone s)).hom y
        simp only [← IsIso.comp_inv_eq,
          ← InducedCategory.comp_hom,
          PresheafedSpace.stalkMap.congr_hom _ _
            (congr_arg (InducedCategory.Hom.hom) (colimit.ι_desc
              (forgetToSheafedSpace.mapCocone s) i))] at this
        rw [← this]
        dsimp
        infer_instance)
  fac _ _ :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
     (colimit.ι_desc (C := SheafedSpace _) _ _)
  uniq s f h :=
    LocallyRingedSpace.forgetToSheafedSpace.map_injective
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.toShHom fun j =>
        congr_arg LocallyRingedSpace.Hom.toShHom (h j))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfShape (Discrete ι) LocallyRingedSpace.{u}
  body: ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

中文:
实例 :
  签名: 有形状余极限 (离散 ι) LocallyRinged空间.{u}
  定义体: ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

Depends on / 依赖: coproductCofanIsColimit
-/
instance : HasColimitsOfShape (Discrete ι) LocallyRingedSpace.{u} :=
  ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape (Discrete.{v} ι) forgetToSheafedSpace.{u}
  body: ⟨fun {G} =>
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit G)
      ((colimit.isColimit (C := SheafedSpace.{u+1, u, u} CommRingCat.{u}) _).ofIsoColimit
        (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _))⟩

中文:
实例 :
  签名: 保持形状余极限 (离散.{v} ι) forgetToSheafedSpace.{u}
  定义体: ⟨fun {G} =>
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit G)
      ((colimit.isColimit (C := SheafedSpace.{u+1, u, u} CommRingCat.{u}) _).ofIsoColimit
        (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _))⟩

Depends on / 依赖: Category, Category.comp_id, Cocone, Cocone.ext, CommRingCat, Iso.refl, SheafedSpace, colimit, colimit.isColimit, comp_id, coproductCofanIsColimit, isColimit, ofIsoColimit, preservesColimit_of_preserves_colimit_cocone
-/
noncomputable instance : PreservesColimitsOfShape (Discrete.{v} ι) forgetToSheafedSpace.{u} :=
  ⟨fun {G} =>
    preservesColimit_of_preserves_colimit_cocone (coproductCofanIsColimit G)
      ((colimit.isColimit (C := SheafedSpace.{u+1, u, u} CommRingCat.{u}) _).ofIsoColimit
        (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _))⟩

end HasCoproducts

section HasCoequalizer

variable {X Y : LocallyRingedSpace.{v}} (f g : X ⟶ Y)

namespace HasCoequalizer

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[instance]
/--
theorem `coequalizer_π_app_isLocalHom` / 定理 `coequalizer_π_app_isLocalHom`

English:
theorem coequalizer_π_app_isLocalHom
  proof: by
  have := ι_comp_coequalizerComparison f.toShHom g.toShHom SheafedSpace.forgetToPresheafedSpace
  dsimp at this
  rw [← PreservesCoequalizer.iso_hom] at this
  rw [← this]; rw [PresheafedSpace.comp_c_app]; rw [← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): this instance has to be manually added
  have : IsIso (PreservesCoequalizer.iso
      SheafedSpace.forgetToPresheafedSpace f.toShHom g.toShHom).hom.c :=
    inferInstance
  apply +allowSynthFailures RingHom.isLocalHom_comp
  · apply +allowSynthFailures RingHom.isLocalHom_comp
    · apply CommRingCat.equalizer_ι_isLocalHom'
    · apply isLocalHom_of_isIso
  · apply isLocalHom_of_isIso

中文:
定理 coequalizer_π_app_isLocalHom
  证明: by
  have := ι_comp_coequalizerComparison f.toShHom g.toShHom SheafedSpace.forgetToPresheafedSpace
  dsimp at this
  rw [← PreservesCoequalizer.iso_hom] at this
  rw [← this]; rw [PresheafedSpace.comp_c_app]; rw [← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): this instance has to be manually added
  have : IsIso (PreservesCoequalizer.iso
      SheafedSpace.forgetToPresheafedSpace f.toShHom g.toShHom).hom.c :=
    inferInstance
  apply +allowSynthFailures RingHom.isLocalHom_comp
  · apply +allowSynthFailures RingHom.isLocalHom_comp
    · apply CommRingCat.equalizer_ι_isLocalHom'
    · apply isLocalHom_of_isIso
  · apply isLocalHom_of_isIso

Depends on / 依赖: PreservesCoequalizer, PreservesCoequalizer.iso_hom, PresheafedSpace, PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_, PresheafedSpace.comp_c_app, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, comp_c_app, f.toShHom, forgetToPresheafedSpace, g.toShHom, iso_hom, toShHom
-/
theorem coequalizer_π_app_isLocalHom
    (U : TopologicalSpace.Opens (coequalizer f.toShHom g.toShHom).carrier) :
    IsLocalHom ((coequalizer.π f.toShHom g.toShHom :).hom.c.app (op U)).hom := by
  have := ι_comp_coequalizerComparison f.toShHom g.toShHom SheafedSpace.forgetToPresheafedSpace
  dsimp at this
  rw [← PreservesCoequalizer.iso_hom] at this
  rw [← this]; rw [PresheafedSpace.comp_c_app]; rw [← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10754): this instance has to be manually added
  have : IsIso (PreservesCoequalizer.iso
      SheafedSpace.forgetToPresheafedSpace f.toShHom g.toShHom).hom.c :=
    inferInstance
  apply +allowSynthFailures RingHom.isLocalHom_comp
  · apply +allowSynthFailures RingHom.isLocalHom_comp
    · apply CommRingCat.equalizer_ι_isLocalHom'
    · apply isLocalHom_of_isIso
  · apply isLocalHom_of_isIso

/-!
We roughly follow the construction given in [MR0302656]. Given a pair `f, g : X ⟶ Y` of morphisms
of locally ringed spaces, we want to show that the stalk map of
`π = coequalizer.π f g` (as sheafed space homs) is a local ring hom. It then follows that
`coequalizer f g` is indeed a locally ringed space, and `coequalizer.π f g` is a morphism of
locally ringed space.

Given a germ `⟨U, s⟩` of `x : coequalizer f g` such that `π꙳ x : Y` is invertible, we ought to show
that `⟨U, s⟩` is invertible. That is, there exists an open set `U' ⊆ U` containing `x` such that the
restriction of `s` onto `U'` is invertible. This `U'` is given by `π '' V`, where `V` is the
basic open set of `π⋆x`.

Since `f ⁻¹' V = Y.basic_open (f ≫ π)꙳ x = Y.basic_open (g ≫ π)꙳ x = g ⁻¹' V`, we have
`π ⁻¹' π '' V = V` (as the underlying set map is merely the set-theoretic coequalizer).
This shows that `π '' V` is indeed open, and `s` is invertible on `π '' V` as the components of `π꙳`
are local ring homs.
-/


variable (U : Opens (coequalizer f.toShHom g.toShHom).carrier)
variable (s : (coequalizer f.toShHom g.toShHom).presheaf.obj (op U))

/--
Definition of `imageBasicOpen` / `imageBasicOpen` 的定义

English:
definition imageBasicOpen
  signature: : Opens Y
  body: Y.toRingedSpace.basicOpen
    (show Y.presheaf.obj (op (unop _)) from
      ((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

中文:
定义 imageBasicOpen
  签名: : Opens Y
  定义体: Y.toRingedSpace.basicOpen
    (show Y.presheaf.obj (op (unop _)) from
      ((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

Depends on / 依赖: Y.presheaf.obj, Y.toRingedSpace.basicOpen, basicOpen, coequalizer, f.toShHom, g.toShHom, hom.c.app, presheaf, toRingedSpace, toShHom
-/
noncomputable def imageBasicOpen : Opens Y :=
  Y.toRingedSpace.basicOpen
    (show Y.presheaf.obj (op (unop _)) from
      ((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `imageBasicOpen_image_preimage` / 定理 `imageBasicOpen_image_preimage`

English:
theorem imageBasicOpen_image_preimage
  proof: by
  fapply Types.coequalizer_preimage_image_eq_of_preimage_eq (↾f.base)
    (↾g.base) (↾(coequalizer.π f.toShHom g.toShHom).hom.base)
  · ext
    simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 3
    exact SheafedSpace.forgetToPresheafedSpace.congr_map
      (coequalizer.condition f.toShHom g.toShHom)
  · exact isColimitCoforkMapOfIsColimit (forget TopCat) _
      (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _)
      _ (coequalizerIsCoequalizer f.toShHom g.toShHom))
  · suffices
      (TopologicalSpace.Opens.map f.base).obj (imageBasicOpen f g U s) =
        (TopologicalSpace.Opens.map g.base).obj (imageBasicOpen f g U s)
      by injection this
    delta imageBasicOpen
    rw [preimage_basicOpen f]; rw [preimage_basicOpen g]
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [← PresheafedSpace.comp_c_app]; rw [← CommRingCat.comp_apply]; rw [← PresheafedSpace.comp_c_app]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [SheafedSpace.congr_hom_app (coequalizer.condition f.toShHom g.toShHom),
      CommRingCat.comp_apply, X.toRingedSpace.basicOpen_res]
    apply inf_eq_right.mpr
    refine (RingedSpace.basicOpen_le _ _).trans ?_
    rw [coequalizer.condition f.toShHom g.toShHom]

中文:
定理 imageBasicOpen_image_preimage
  证明: by
  fapply Types.coequalizer_preimage_image_eq_of_preimage_eq (↾f.base)
    (↾g.base) (↾(coequalizer.π f.toShHom g.toShHom).hom.base)
  · ext
    simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 3
    exact SheafedSpace.forgetToPresheafedSpace.congr_map
      (coequalizer.condition f.toShHom g.toShHom)
  · exact isColimitCoforkMapOfIsColimit (forget TopCat) _
      (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _)
      _ (coequalizerIsCoequalizer f.toShHom g.toShHom))
  · suffices
      (TopologicalSpace.Opens.map f.base).obj (imageBasicOpen f g U s) =
        (TopologicalSpace.Opens.map g.base).obj (imageBasicOpen f g U s)
      by injection this
    delta imageBasicOpen
    rw [preimage_basicOpen f]; rw [preimage_basicOpen g]
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [← PresheafedSpace.comp_c_app]; rw [← CommRingCat.comp_apply]; rw [← PresheafedSpace.comp_c_app]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [SheafedSpace.congr_hom_app (coequalizer.condition f.toShHom g.toShHom),
      CommRingCat.comp_apply, X.toRingedSpace.basicOpen_res]
    apply inf_eq_right.mpr
    refine (RingedSpace.basicOpen_le _ _).trans ?_
    rw [coequalizer.condition f.toShHom g.toShHom]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, PresheafedSpace, PresheafedSpace.comp_base, SheafedSpace, SheafedSpace.forget, SheafedSpace.forgetToPresheafedSpace.congr_map, TopCat, TopCat.comp_app, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, Types.coequalizer_preimage_image_eq_of_preimage_eq, coe_mk, coequalizer, coequalizer.condition, coequalizer_preimage_image_eq_of_preimage_eq, comp_app, comp_apply, comp_base
-/
theorem imageBasicOpen_image_preimage :
    (coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base ''
        (imageBasicOpen f g U s).1) = (imageBasicOpen f g U s).1 := by
  fapply Types.coequalizer_preimage_image_eq_of_preimage_eq (↾f.base)
    (↾g.base) (↾(coequalizer.π f.toShHom g.toShHom).hom.base)
  · ext
    simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 3
    exact SheafedSpace.forgetToPresheafedSpace.congr_map
      (coequalizer.condition f.toShHom g.toShHom)
  · exact isColimitCoforkMapOfIsColimit (forget TopCat) _
      (isColimitCoforkMapOfIsColimit (SheafedSpace.forget _)
      _ (coequalizerIsCoequalizer f.toShHom g.toShHom))
  · suffices
      (TopologicalSpace.Opens.map f.base).obj (imageBasicOpen f g U s) =
        (TopologicalSpace.Opens.map g.base).obj (imageBasicOpen f g U s)
      by injection this
    delta imageBasicOpen
    rw [preimage_basicOpen f]; rw [preimage_basicOpen g]
    dsimp
    rw [← ConcreteCategory.comp_apply]; rw [← PresheafedSpace.comp_c_app]; rw [← CommRingCat.comp_apply]; rw [← PresheafedSpace.comp_c_app]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [SheafedSpace.congr_hom_app (coequalizer.condition f.toShHom g.toShHom),
      CommRingCat.comp_apply, X.toRingedSpace.basicOpen_res]
    apply inf_eq_right.mpr
    refine (RingedSpace.basicOpen_le _ _).trans ?_
    rw [coequalizer.condition f.toShHom g.toShHom]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `imageBasicOpen_image_open` / 定理 `imageBasicOpen_image_open`

English:
theorem imageBasicOpen_image_open
  proof: by
  rw [← (TopCat.homeoOfIso (PreservesCoequalizer.iso (SheafedSpace.forget _) f.toShHom
    g.toShHom)).isOpen_preimage]; rw [TopCat.coequalizer_isOpen_iff]; rw [← Set.preimage_comp]
  erw [← TopCat.coe_comp]
  rw [PreservesCoequalizer.iso_hom]; rw [ι_comp_coequalizerComparison]
  dsimp only [SheafedSpace.forget]
  rw [imageBasicOpen_image_preimage]
  exact (imageBasicOpen f g U s).2

中文:
定理 imageBasicOpen_image_open
  证明: by
  rw [← (TopCat.homeoOfIso (PreservesCoequalizer.iso (SheafedSpace.forget _) f.toShHom
    g.toShHom)).isOpen_preimage]; rw [TopCat.coequalizer_isOpen_iff]; rw [← Set.preimage_comp]
  erw [← TopCat.coe_comp]
  rw [PreservesCoequalizer.iso_hom]; rw [ι_comp_coequalizerComparison]
  dsimp only [SheafedSpace.forget]
  rw [imageBasicOpen_image_preimage]
  exact (imageBasicOpen f g U s).2

Depends on / 依赖: PreservesCoequalizer, PreservesCoequalizer.iso, PreservesCoequalizer.iso_hom, Set.preimage_comp, SheafedSpace, SheafedSpace.forget, TopCat, TopCat.coe_comp, TopCat.coequalizer_isOpen_iff, TopCat.homeoOfIso, coe_comp, coequalizer_isOpen_iff, f.toShHom, forget, g.toShHom, homeoOfIso, imageBasicOpen, imageBasicOpen_image_preimage, isOpen_preimage, iso_hom
-/
theorem imageBasicOpen_image_open :
    IsOpen ((coequalizer.π f.toShHom g.toShHom).hom.base '' (imageBasicOpen f g U s).1) := by
  rw [← (TopCat.homeoOfIso (PreservesCoequalizer.iso (SheafedSpace.forget _) f.toShHom
    g.toShHom)).isOpen_preimage]; rw [TopCat.coequalizer_isOpen_iff]; rw [← Set.preimage_comp]
  erw [← TopCat.coe_comp]
  rw [PreservesCoequalizer.iso_hom]; rw [ι_comp_coequalizerComparison]
  dsimp only [SheafedSpace.forget]
  rw [imageBasicOpen_image_preimage]
  exact (imageBasicOpen f g U s).2

set_option backward.isDefEq.respectTransparency false in
@[instance]
/--
theorem `coequalizer_π_stalk_isLocalHom` / 定理 `coequalizer_π_stalk_isLocalHom`

English:
theorem coequalizer_π_stalk_isLocalHom
  given: (x : Y)
  proof: by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.exists_germ_eq _ a with ⟨U, hU, s, rfl⟩
  rw [PresheafedSpace.stalkMap_germ_apply (coequalizer.π f.toShHom g.toShHom).hom U _ hU] at ha
  let V := imageBasicOpen f g U s
  have hV : (coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) = V.1 :=
    imageBasicOpen_image_preimage f g U s
  have hV' : V = ⟨(coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1), hV.symm ▸ V.2⟩ :=
    SetLike.ext' hV.symm
  have V_open : IsOpen ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) :=
    imageBasicOpen_image_open f g U s
  have VleU : ⟨(coequalizer.π f.toShHom g.toShHom).hom.base '' V.1, V_open⟩ <= U :=
    Set.image_subset_iff.mpr (Y.toRingedSpace.basicOpen_le _)
  have hxV : x in V := ⟨hU, ha⟩
  rw [← (coequalizer f.toShHom g.toShHom).presheaf.germ_res_apply (homOfLE VleU) _
      (@Set.mem_image_of_mem _ _ (coequalizer.π f.toShHom g.toShHom).hom.base x V.1 hxV) s]
  apply RingHom.isUnit_map
  rw [← isUnit_map_iff ((coequalizer.π f.toShHom g.toShHom).hom.c.app _).hom]; rw [← CommRingCat.comp_apply]; rw [NatTrans.naturality]; rw [CommRingCat.comp_apply]; rw [← isUnit_map_iff (Y.presheaf.map (eqToHom hV').op).hom]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  convert!
    @RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (unop _)
      (((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

中文:
定理 coequalizer_π_stalk_isLocalHom
  条件: (x : Y)
  证明: by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.exists_germ_eq _ a with ⟨U, hU, s, rfl⟩
  rw [PresheafedSpace.stalkMap_germ_apply (coequalizer.π f.toShHom g.toShHom).hom U _ hU] at ha
  let V := imageBasicOpen f g U s
  have hV : (coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) = V.1 :=
    imageBasicOpen_image_preimage f g U s
  have hV' : V = ⟨(coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1), hV.symm ▸ V.2⟩ :=
    SetLike.ext' hV.symm
  have V_open : IsOpen ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) :=
    imageBasicOpen_image_open f g U s
  have VleU : ⟨(coequalizer.π f.toShHom g.toShHom).hom.base '' V.1, V_open⟩ <= U :=
    Set.image_subset_iff.mpr (Y.toRingedSpace.basicOpen_le _)
  have hxV : x in V := ⟨hU, ha⟩
  rw [← (coequalizer f.toShHom g.toShHom).presheaf.germ_res_apply (homOfLE VleU) _
      (@Set.mem_image_of_mem _ _ (coequalizer.π f.toShHom g.toShHom).hom.base x V.1 hxV) s]
  apply RingHom.isUnit_map
  rw [← isUnit_map_iff ((coequalizer.π f.toShHom g.toShHom).hom.c.app _).hom]; rw [← CommRingCat.comp_apply]; rw [NatTrans.naturality]; rw [CommRingCat.comp_apply]; rw [← isUnit_map_iff (Y.presheaf.map (eqToHom hV').op).hom]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  convert!
    @RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (unop _)
      (((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

Depends on / 依赖: Presheaf, PresheafedSpace, PresheafedSpace.stalkMap_germ_apply, TopCat, TopCat.Presheaf.exists_germ_eq, coequalizer, exists_germ_eq, f.toShHom, g.toShHom, hV.s, hom.base, imageBasicOpen, imageBasicOpen_image_preimage, stalkMap_germ_apply, toShHom
-/
theorem coequalizer_π_stalk_isLocalHom (x : Y) :
    IsLocalHom ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap x).hom := by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.exists_germ_eq _ a with ⟨U, hU, s, rfl⟩
  rw [PresheafedSpace.stalkMap_germ_apply (coequalizer.π f.toShHom g.toShHom).hom U _ hU] at ha
  let V := imageBasicOpen f g U s
  have hV : (coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) = V.1 :=
    imageBasicOpen_image_preimage f g U s
  have hV' : V = ⟨(coequalizer.π f.toShHom g.toShHom).hom.base ⁻¹'
      ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1), hV.symm ▸ V.2⟩ :=
    SetLike.ext' hV.symm
  have V_open : IsOpen ((coequalizer.π f.toShHom g.toShHom).hom.base '' V.1) :=
    imageBasicOpen_image_open f g U s
  have VleU : ⟨(coequalizer.π f.toShHom g.toShHom).hom.base '' V.1, V_open⟩ <= U :=
    Set.image_subset_iff.mpr (Y.toRingedSpace.basicOpen_le _)
  have hxV : x in V := ⟨hU, ha⟩
  rw [← (coequalizer f.toShHom g.toShHom).presheaf.germ_res_apply (homOfLE VleU) _
      (@Set.mem_image_of_mem _ _ (coequalizer.π f.toShHom g.toShHom).hom.base x V.1 hxV) s]
  apply RingHom.isUnit_map
  rw [← isUnit_map_iff ((coequalizer.π f.toShHom g.toShHom).hom.c.app _).hom]; rw [← CommRingCat.comp_apply]; rw [NatTrans.naturality]; rw [CommRingCat.comp_apply]; rw [← isUnit_map_iff (Y.presheaf.map (eqToHom hV').op).hom]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  convert!
    @RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (unop _)
      (((coequalizer.π f.toShHom g.toShHom).hom.c.app (op U)) s)

end HasCoequalizer

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `coequalizer` / `coequalizer` 的定义

English:
definition coequalizer
  signature: : LocallyRingedSpace where
  body: Limits.coequalizer f.toShHom g.toShHom
  isLocalRing x := by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x
    exact ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap y).hom.domain_isLocalRing

中文:
定义 coequalizer
  签名: : LocallyRinged空间 where
  定义体: Limits.coequalizer f.toShHom g.toShHom
  isLocalRing x := by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x
    exact ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap y).hom.domain_isLocalRing

Depends on / 依赖: Limits, Limits.coequalizer, coequalizer, f.toShHom, g.toShHom, toShHom
-/
noncomputable def coequalizer : LocallyRingedSpace where
  toSheafedSpace := Limits.coequalizer f.toShHom g.toShHom
  isLocalRing x := by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x
    exact ((coequalizer.π f.toShHom g.toShHom :).hom.stalkMap y).hom.domain_isLocalRing

/--
Definition of `coequalizerCofork` / `coequalizerCofork` 的定义

English:
definition coequalizerCofork
  signature: : Cofork f g
  body: Cofork.ofπ (P := coequalizer f g)
    (homMk (coequalizer.π f.toShHom g.toShHom)
      -- Porting note: this used to be automatic
      (HasCoequalizer.coequalizer_π_stalk_isLocalHom _ _))
    (forgetToSheafedSpace.map_injective (coequalizer.condition f.toShHom g.toShHom))

中文:
定义 coequalizerCofork
  签名: : 余叉 f g
  定义体: Cofork.ofπ (P := coequalizer f g)
    (homMk (coequalizer.π f.toShHom g.toShHom)
      -- Porting note: this used to be automatic
      (HasCoequalizer.coequalizer_π_stalk_isLocalHom _ _))
    (forgetToSheafedSpace.map_injective (coequalizer.condition f.toShHom g.toShHom))

Depends on / 依赖: Cofork, Cofork.of, coequalizer, f.toShHom, g.toShHom, toShHom
-/
noncomputable def coequalizerCofork : Cofork f g :=
  Cofork.ofπ (P := coequalizer f g)
    (homMk (coequalizer.π f.toShHom g.toShHom)
      -- Porting note: this used to be automatic
      (HasCoequalizer.coequalizer_π_stalk_isLocalHom _ _))
    (forgetToSheafedSpace.map_injective (coequalizer.condition f.toShHom g.toShHom))

/--
theorem `isLocalHom_stalkMap_congr` / 定理 `isLocalHom_stalkMap_congr`

English:
theorem isLocalHom_stalkMap_congr
  statement: {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g) (x)
  proof: by
  rw [PresheafedSpace.stalkMap.congr_hom _ _ (congr_arg InducedCategory.Hom.hom H.symm) x]
  infer_instance

中文:
定理 isLocalHom_stalkMap_congr
  结论: {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g) (x)
  证明: by
  rw [PresheafedSpace.stalkMap.congr_hom _ _ (congr_arg InducedCategory.Hom.hom H.symm) x]
  infer_instance

Depends on / 依赖: H.symm, InducedCategory, InducedCategory.Hom.hom, PresheafedSpace, PresheafedSpace.stalkMap.congr_hom, congr_arg, congr_hom, infer_instance, stalkMap
-/
theorem isLocalHom_stalkMap_congr {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g) (x)
    (h : IsLocalHom (f.hom.stalkMap x).hom) :
    IsLocalHom (g.hom.stalkMap x).hom := by
  rw [PresheafedSpace.stalkMap.congr_hom _ _ (congr_arg InducedCategory.Hom.hom H.symm) x]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coequalizerCoforkIsColimit` / `coequalizerCoforkIsColimit` 的定义

English:
definition coequalizerCoforkIsColimit
  signature: : IsColimit (coequalizerCofork f g)
  body: by
  refine Cofork.IsColimit.mk' _ (fun s => ?_)
  have e : f.toShHom ≫ s.π.toShHom = g.toShHom ≫ s.π.toShHom := by
    simp only [← comp_toShHom, s.condition]
  refine ⟨⟨(coequalizer.desc s.π.toShHom e).hom, fun x => ?_⟩,
    ⟨Hom.ext' (Functor.congr_map SheafedSpace.forgetToPresheafedSpace
      (coequalizer.π_desc (Hom.toShHom s.π) e)),
      fun {m} hm => LocallyRingedSpace.forgetToSheafedSpace.map_injective
        (coequalizer.hom_ext ((LocallyRingedSpace.forgetToSheafedSpace.congr_map hm).trans
      ((coequalizer.π_desc _ _).symm)))⟩⟩
  rcases (TopCat.epi_iff_surjective
    (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x with ⟨y, rfl⟩
  -- Porting note: was `apply isLocalHom_of_comp _ (PresheafedSpace.stalkMap ...)`, this
  -- used to allow you to provide the proof that `... ≫ ...` is a local ring homomorphism later,
  -- but this is no longer possible
  set h := _
  change IsLocalHom h
  suffices _ : IsLocalHom (((coequalizerCofork f g).π.1.stalkMap _).hom.comp h) by
    apply isLocalHom_of_comp _ ((coequalizerCofork f g).π.1.stalkMap _).hom
  rw [← CommRingCat.hom_ofHom h]; rw [← CommRingCat.hom_comp]
  erw [← PresheafedSpace.stalkMap.comp]
  apply isLocalHom_stalkMap_congr _ _ (coequalizer.π_desc s.π.toShHom e).symm y
  change IsLocalHom (s.π.stalkMap y).hom
  infer_instance

中文:
定义 coequalizerCoforkIsColimit
  签名: : 是余极限 (coequalizerCofork f g)
  定义体: by
  refine Cofork.IsColimit.mk' _ (fun s => ?_)
  have e : f.toShHom ≫ s.π.toShHom = g.toShHom ≫ s.π.toShHom := by
    simp only [← comp_toShHom, s.condition]
  refine ⟨⟨(coequalizer.desc s.π.toShHom e).hom, fun x => ?_⟩,
    ⟨Hom.ext' (Functor.congr_map SheafedSpace.forgetToPresheafedSpace
      (coequalizer.π_desc (Hom.toShHom s.π) e)),
      fun {m} hm => LocallyRingedSpace.forgetToSheafedSpace.map_injective
        (coequalizer.hom_ext ((LocallyRingedSpace.forgetToSheafedSpace.congr_map hm).trans
      ((coequalizer.π_desc _ _).symm)))⟩⟩
  rcases (TopCat.epi_iff_surjective
    (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x with ⟨y, rfl⟩
  -- Porting note: was `apply isLocalHom_of_comp _ (PresheafedSpace.stalkMap ...)`, this
  -- used to allow you to provide the proof that `... ≫ ...` is a local ring homomorphism later,
  -- but this is no longer possible
  set h := _
  change IsLocalHom h
  suffices _ : IsLocalHom (((coequalizerCofork f g).π.1.stalkMap _).hom.comp h) by
    apply isLocalHom_of_comp _ ((coequalizerCofork f g).π.1.stalkMap _).hom
  rw [← CommRingCat.hom_ofHom h]; rw [← CommRingCat.hom_comp]
  erw [← PresheafedSpace.stalkMap.comp]
  apply isLocalHom_stalkMap_congr _ _ (coequalizer.π_desc s.π.toShHom e).symm y
  change IsLocalHom (s.π.stalkMap y).hom
  infer_instance

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, Decidable, Functor, Functor.congr_map, Hom.ext, Hom.toShHom, IsColimit, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace.congr_map, LocallyRingedSpace.forgetToSheafedSpace.map_injective, SheafedSpace, SheafedSpace.forgetToPresheafedSpace, coequalizer, coequalizer.desc, coequalizer.hom_ext, comp_toShHom, condition, congr_map, f.toShHom
-/
noncomputable def coequalizerCoforkIsColimit : IsColimit (coequalizerCofork f g) := by
  refine Cofork.IsColimit.mk' _ (fun s => ?_)
  have e : f.toShHom ≫ s.π.toShHom = g.toShHom ≫ s.π.toShHom := by
    simp only [← comp_toShHom, s.condition]
  refine ⟨⟨(coequalizer.desc s.π.toShHom e).hom, fun x => ?_⟩,
    ⟨Hom.ext' (Functor.congr_map SheafedSpace.forgetToPresheafedSpace
      (coequalizer.π_desc (Hom.toShHom s.π) e)),
      fun {m} hm => LocallyRingedSpace.forgetToSheafedSpace.map_injective
        (coequalizer.hom_ext ((LocallyRingedSpace.forgetToSheafedSpace.congr_map hm).trans
      ((coequalizer.π_desc _ _).symm)))⟩⟩
  rcases (TopCat.epi_iff_surjective
    (coequalizer.π f.toShHom g.toShHom).hom.base).mp inferInstance x with ⟨y, rfl⟩
  -- Porting note: was `apply isLocalHom_of_comp _ (PresheafedSpace.stalkMap ...)`, this
  -- used to allow you to provide the proof that `... ≫ ...` is a local ring homomorphism later,
  -- but this is no longer possible
  set h := _
  change IsLocalHom h
  suffices _ : IsLocalHom (((coequalizerCofork f g).π.1.stalkMap _).hom.comp h) by
    apply isLocalHom_of_comp _ ((coequalizerCofork f g).π.1.stalkMap _).hom
  rw [← CommRingCat.hom_ofHom h]; rw [← CommRingCat.hom_comp]
  erw [← PresheafedSpace.stalkMap.comp]
  apply isLocalHom_stalkMap_congr _ _ (coequalizer.π_desc s.π.toShHom e).symm y
  change IsLocalHom (s.π.stalkMap y).hom
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoequalizer f g
  body: ⟨⟨⟨_, coequalizerCoforkIsColimit f g⟩⟩⟩

中文:
实例 :
  签名: HasCoequalizer f g
  定义体: ⟨⟨⟨_, coequalizerCoforkIsColimit f g⟩⟩⟩

Depends on / 依赖: coequalizerCoforkIsColimit
-/
instance : HasCoequalizer f g :=
  ⟨⟨⟨_, coequalizerCoforkIsColimit f g⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCoequalizers LocallyRingedSpace
  body: hasCoequalizers_of_hasColimit_parallelPair _

中文:
实例 :
  签名: HasCoequalizers LocallyRinged空间
  定义体: hasCoequalizers_of_hasColimit_parallelPair _

Depends on / 依赖: hasCoequalizers_of_hasColimit_parallelPair
-/
instance : HasCoequalizers LocallyRingedSpace :=
  hasCoequalizers_of_hasColimit_parallelPair _

/--
Instance `preservesCoequalizer` / 实例 `preservesCoequalizer`

English:
instance preservesCoequalizer
  signature: :
  body: ⟨fun {F} => by
    -- Porting note: was `apply preservesColimitOfIsoDiagram ...` and the proof that preservation
    -- of colimit is provided later
    suffices PreservesColimit (parallelPair (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)) forgetToSheafedSpace from
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair F).symm
    apply preservesColimit_of_preserves_colimit_cocone (coequalizerCoforkIsColimit _ _)
    apply (isColimitMapCoconeCoforkEquiv _ _).symm _
    dsimp only [forgetToSheafedSpace]
    exact coequalizerIsCoequalizer _ _⟩

中文:
实例 preservesCoequalizer
  签名: :
  定义体: ⟨fun {F} => by
    -- Porting note: was `apply preservesColimitOfIsoDiagram ...` and the proof that preservation
    -- of colimit is provided later
    suffices PreservesColimit (parallelPair (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)) forgetToSheafedSpace from
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair F).symm
    apply preservesColimit_of_preserves_colimit_cocone (coequalizerCoforkIsColimit _ _)
    apply (isColimitMapCoconeCoforkEquiv _ _).symm _
    dsimp only [forgetToSheafedSpace]
    exact coequalizerIsCoequalizer _ _⟩
-/
noncomputable instance preservesCoequalizer :
    PreservesColimitsOfShape WalkingParallelPair forgetToSheafedSpace.{v} :=
  ⟨fun {F} => by
    -- Porting note: was `apply preservesColimitOfIsoDiagram ...` and the proof that preservation
    -- of colimit is provided later
    suffices PreservesColimit (parallelPair (F.map WalkingParallelPairHom.left)
        (F.map WalkingParallelPairHom.right)) forgetToSheafedSpace from
      preservesColimit_of_iso_diagram _ (diagramIsoParallelPair F).symm
    apply preservesColimit_of_preserves_colimit_cocone (coequalizerCoforkIsColimit _ _)
    apply (isColimitMapCoconeCoforkEquiv _ _).symm _
    dsimp only [forgetToSheafedSpace]
    exact coequalizerIsCoequalizer _ _⟩

end HasCoequalizer

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits LocallyRingedSpace
  body: has_colimits_of_hasCoequalizers_and_coproducts

中文:
实例 :
  签名: 有余极限 LocallyRinged空间
  定义体: has_colimits_of_hasCoequalizers_and_coproducts

Depends on / 依赖: has_colimits_of_hasCoequalizers_and_coproducts
-/
instance : HasColimits LocallyRingedSpace :=
  has_colimits_of_hasCoequalizers_and_coproducts

/--
Instance `preservesColimits_forgetToSheafedSpace` / 实例 `preservesColimits_forgetToSheafedSpace`

English:
instance preservesColimits_forgetToSheafedSpace
  signature: :
  body: preservesColimits_of_preservesCoequalizers_and_coproducts _

中文:
实例 preservesColimits_forgetToSheafedSpace
  签名: :
  定义体: preservesColimits_of_preservesCoequalizers_and_coproducts _

Depends on / 依赖: preservesColimits_of_preservesCoequalizers_and_coproducts
-/
noncomputable instance preservesColimits_forgetToSheafedSpace :
    PreservesColimits LocallyRingedSpace.forgetToSheafedSpace.{u} :=
  preservesColimits_of_preservesCoequalizers_and_coproducts _

end LocallyRingedSpace

end AlgebraicGeometry
