/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Exactness of colimits

In this file, we shall study exactness properties of colimits.
First, we translate the assumption that `colim : (J ⥤ C) ⥤ C`
preserves monomorphisms (resp. preserves epimorphisms, resp. is exact)
into statements involving arbitrary cocones instead of the ones
given by the colimit API. We also show that when an inductive system
involves only monomorphisms, then the "inclusion" morphism
into the colimit is also a monomorphism (assuming `J`
is filtered and `C` satisfies AB5).

-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : Type u'} [Category.{v'} J]

namespace Limits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `colim.map_mono'` / 引理 `colim.map_mono'`

English:
lemma colim.map_mono'
  statement: [HasColimitsOfShape J C]
  proof: by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    ((inferInstance : Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j => by
  

中文:
引理 colim.map_mono'
  结论: [有形状余极限 J C]
  证明: by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    ((inferInstance : Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j => by
  

Depends on / 依赖: Arrow.isoMk, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, MorphismProperty, MorphismProperty.monomorphisms, arrow_mk_iso_iff, coconePointUniqueUpToIso, colim.map, colimit, colimit.cocone_, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, comp_coconePointUniqueUpToIso_hom_assoc, hom_ext, isColimit, monomorphisms, reassoc_of
-/
lemma colim.map_mono' [HasColimitsOfShape J C]
    [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms]
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [Mono φ]
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : forall j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Mono f := by
  refine ((MorphismProperty.monomorphisms C).arrow_mk_iso_iff ?_).2
    ((inferInstance : Mono (colim.map φ)))
  exact Arrow.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (hc₁.hom_ext (fun j => by
      dsimp
      rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]; rw [colimit.cocone_ι]; rw [ι_colimMap]; rw [reassoc_of% (hf j)]; rw [IsColimit.comp_coconePointUniqueUpToIso_hom]; rw [colimit.cocone_ι]))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `colim.map_epi'` / 引理 `colim.map_epi'`

English:
lemma colim.map_epi'
  proof: hc₂.hom_ext (fun j => by
    rw [← cancel_epi (φ.app j)]; rw [← reassoc_of% hf]; rw [h]; rw [reassoc_of% hf])

中文:
引理 colim.map_epi'
  证明: hc₂.hom_ext (fun j => by
    rw [← cancel_epi (φ.app j)]; rw [← reassoc_of% hf]; rw [h]; rw [reassoc_of% hf])

Depends on / 依赖: cancel_epi, hom_ext, reassoc_of
-/
lemma colim.map_epi'
    {X₁ X₂ : J ⥤ C} (φ : X₁ ⟶ X₂) [forall j, Epi (φ.app j)]
    (c₁ : Cocone X₁) {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    (f : c₁.pt ⟶ c₂.pt) (hf : forall j, c₁.ι.app j ≫ f = φ.app j ≫ c₂.ι.app j) : Epi f where
  left_cancellation {Z} g₁ g₂ h := hc₂.hom_ext (fun j => by
    rw [← cancel_epi (φ.app j)]; rw [← reassoc_of% hf]; rw [h]; rw [reassoc_of% hf])

attribute [local instance] IsFiltered.isConnected

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsColimit.mono_ι_app_of_isFiltered` / 引理 `IsColimit.mono_ι_app_of_isFiltered`

English:
lemma IsColimit.mono_ι_app_of_isFiltered
  proof: by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((

中文:
引理 是余极限.mono_ι_app_of_isFiltered
  证明: by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.Final.isColimitWhiskerEquiv, Functor.const, NatTrans, NatTrans.mono_of_mono_app, Under.forget, Under.w, X.map, X.map_comp, X.obj, cat_disch, colim.map_mono, forget, id_comp, isColimitConstCocone, isColimitWhiskerEquiv, j.hom, map_comp
-/
lemma IsColimit.mono_ι_app_of_isFiltered
    {X : J ⥤ C} [forall (j j' : J) (φ : j ⟶ j'), Mono (X.map φ)]
    {c : Cocone X} (hc : IsColimit c) [IsFiltered J] (j₀ : J)
    [HasColimitsOfShape (Under j₀) C]
    [(colim : (Under j₀ ⥤ C) ⥤ C).PreservesMonomorphisms] :
    Mono (c.ι.app j₀) := by
  let f : (Functor.const _).obj (X.obj j₀) ⟶ Under.forget j₀ ⋙ X :=
    { app j := X.map j.hom
      naturality _ _ g := by
        dsimp
        simp only [Category.id_comp, ← X.map_comp, Under.w] }
  have := NatTrans.mono_of_mono_app f
  exact colim.map_mono' f (isColimitConstCocone _ _)
    ((Functor.Final.isColimitWhiskerEquiv _ _).symm hc) (c.ι.app j₀) (by cat_disch)

section

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] [HasZeroMorphisms C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : forall j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : forall j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `S : ShortComplex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`. -/
@[simps]
/--
Definition of `colim.mapShortComplex` / `colim.mapShortComplex` 的定义

English:
definition colim.mapShortComplex
  signature: : ShortComplex C
  body: ShortComplex.mk f g (hc₁.hom_ext (fun j => by
    rw [reassoc_of% (hf j)]; rw [hg j]; rw [comp_zero]; rw [← NatTrans.comp_app_assoc]; rw [S.zero]; rw [zero_app]; rw [zero_comp]))

中文:
定义 colim.mapShortComplex
  签名: : 短复形 C
  定义体: ShortComplex.mk f g (hc₁.hom_ext (fun j => by
    rw [reassoc_of% (hf j)]; rw [hg j]; rw [comp_zero]; rw [← NatTrans.comp_app_assoc]; rw [S.zero]; rw [zero_app]; rw [zero_comp]))

Depends on / 依赖: NatTrans, NatTrans.comp_app_assoc, S.zero, ShortComplex, ShortComplex.mk, comp_app_assoc, comp_zero, hom_ext, reassoc_of, zero_app, zero_comp
-/
def colim.mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j => by
    rw [reassoc_of% (hf j)]; rw [hg j]; rw [comp_zero]; rw [← NatTrans.comp_app_assoc]; rw [S.zero]; rw [zero_app]; rw [zero_comp]))

variable {S c₂ c₃}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc₂ hc₃ hS in
/--
lemma `colim.exact_mapShortComplex` / 引理 `colim.exact_mapShortComplex`

English:
lemma colim.exact_mapShortComplex
  proof: by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc

中文:
引理 colim.exact_mapShortComplex
  证明: by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUp, IsColimit.comp_coconePointUniqueUpToIso_hom_assoc, ShortComplex, ShortComplex.exact_iff_of_iso, ShortComplex.isoMk, coconePointUniqueUpToIso, colimit, colimit.cocone_, colimit.isColimit, comp_coconePointUniqueUp, comp_coconePointUniqueUpToIso_hom_assoc, exact_iff_of_iso, hS.map, hom_ext, isColimit, reassoc_of
-/
lemma colim.exact_mapShortComplex :
    (mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc₁.hom_ext (fun j => ?_)) (hc₂.hom_ext (fun j => ?_))
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]; rw [colimit.cocone_ι]; rw [ι_colimMap]; rw [reassoc_of% (hf j)]; rw [IsColimit.comp_coconePointUniqueUpToIso_hom]; rw [colimit.cocone_ι]
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]; rw [colimit.cocone_ι]; rw [ι_colimMap]; rw [reassoc_of% (hg j)]; rw [IsColimit.comp_coconePointUniqueUpToIso_hom]; rw [colimit.cocone_ι]

end

end Limits

namespace MorphismProperty

open Limits

open MorphismProperty

variable (J C) in
/--
Instance `isStableUnderColimitsOfShape_monomorphisms` / 实例 `isStableUnderColimitsOfShape_monomorphisms`

English:
instance isStableUnderColimitsOfShape_monomorphisms
  body: by
    have (j : J) : Mono (f.app j) := hf _
    have := NatTrans.mono_of_mono_app f
    apply colim.map_mono' f hc₁ hc₂ φ (by simp [hφ])

中文:
实例 isStableUnderColimitsOfShape_monomorphisms
  定义体: by
    have (j : J) : Mono (f.app j) := hf _
    have := NatTrans.mono_of_mono_app f
    apply colim.map_mono' f hc₁ hc₂ φ (by simp [hφ])

Depends on / 依赖: NatTrans, NatTrans.mono_of_mono_app, colim.map_mono, f.app, map_mono, mono_of_mono_app
-/
instance isStableUnderColimitsOfShape_monomorphisms
    [HasColimitsOfShape J C] [(colim : (J ⥤ C) ⥤ C).PreservesMonomorphisms] :
    (monomorphisms C).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    have (j : J) : Mono (f.app j) := hf _
    have := NatTrans.mono_of_mono_app f
    apply colim.map_mono' f hc₁ hc₂ φ (by simp [hφ])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoproducts.{u'}
  signature: C] [AB4OfSize.{u'} C] :

中文:
实例 [HasCoproducts.{u'}
  签名: C] [AB4OfSize.{u'} C] :
-/
instance [HasCoproducts.{u'} C] [AB4OfSize.{u'} C] :
    IsStableUnderCoproducts.{u'} (monomorphisms C) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFilteredColimitsOfSize.{v',
  signature: u'} C] [AB5OfSize.{v', u'} C] :
  body: by infer_instance

中文:
实例 [有FilteredColimitsOfSize.{v',
  签名: u'} C] [AB5OfSize.{v', u'} C] :
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance [HasFilteredColimitsOfSize.{v', u'} C] [AB5OfSize.{v', u'} C] :
    IsStableUnderFilteredColimits.{v', u'} (monomorphisms C) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

end MorphismProperty

end CategoryTheory
