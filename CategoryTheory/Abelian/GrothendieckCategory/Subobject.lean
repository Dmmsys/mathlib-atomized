/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Subobjects in Grothendieck abelian categories

We study the complete lattice of subobjects of `X : C`
when `C` is a Grothendieck abelian category. In particular,
for a functor `F : J ⥤ MonoOver X` from a filtered category,
we relate the colimit of `F` (computed in `C`) and the
supremum of the subobjects corresponding to the objects
in the image of `F`.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits

namespace IsGrothendieckAbelian

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

section

variable [IsFiltered J] {c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)}
  (hc : IsColimit c) (f : c.pt ⟶ X) (hf : forall (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hc hf

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_of_isColimit_monoOver` / 引理 `mono_of_isColimit_monoOver`

English:
lemma mono_of_isColimit_monoOver
  statement: Mono f
  proof: by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

中文:
引理 mono_of_isColimit_monoOver
  结论: Mono f
  证明: by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

Depends on / 依赖: F.obj, Functor, Functor.const, MonoOver, MonoOver.forget, NatTrans, NatTrans.mono_of_mono_app, Over.forget, colim.map_mono, forget, isColimitConstCocone, map_mono, mono_of_mono_app, obj.hom
-/
lemma mono_of_isColimit_monoOver : Mono f := by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `subobjectMk_of_isColimit_eq_iSup` / 引理 `subobjectMk_of_isColimit_eq_iSup`

English:
lemma subobjectMk_of_isColimit_eq_iSup
  proof: mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  have := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction s using Subobject.ind with | _ g
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.f

中文:
引理 subobjectMk_of_isColimit_eq_iSup
  证明: mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  have := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction s using Subobject.ind with | _ g
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.f

Depends on / 依赖: mono_of_isColimit_monoOver
-/
lemma subobjectMk_of_isColimit_eq_iSup :
    haveI := mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  have := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction s using Subobject.ind with | _ g
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _) := Cocone.mk _
      { app j := Subobject.ofMkLEMk _ _ (H j)
        naturality j j' f := by
          dsimp
          simpa only [← cancel_mono g, Category.assoc, Subobject.ofMkLEMk_comp,
            Category.comp_id] using MonoOver.w (F.map f) }
    exact Subobject.mk_le_mk_of_comm (hc.desc c')
      (hc.hom_ext (fun j => by rw [hc.fac_assoc c' j, hf, Subobject.ofMkLEMk_comp]))
  · rw [iSup_le_iff]
    intro j
    exact Subobject.mk_le_mk_of_comm (c.ι.app j) (hf j)

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitMapCoconeOfSubobjectMkEqISup` / `isColimitMapCoconeOfSubobjectMkEqISup` 的定义

English:
definition isColimitMapCoconeOfSubobjectMkEqISup
  body: by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  haveI := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobjectMk_of_is

中文:
定义 isColimitMapCoconeOfSubobjectMkEqISup
  定义体: by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  haveI := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobjectMk_of_is

Depends on / 依赖: Cocone, Cocone.ext, Cocone.mk, F.obj, IsColimit, IsColimit.ofIsoColimit, MonoOver, MonoOver.forget, Over.forget, Subobject, Subobject.isoOfMkEqMk, c.pt.hom, cancel_mono, colimit, colimit.desc, colimit.isColimit, forget, isColimit, isoOfMkEqMk, mono_of_isColimit_monoOver
-/
noncomputable def isColimitMapCoconeOfSubobjectMkEqISup
    [IsFiltered J] (c : Cocone (F ⋙ MonoOver.forget _)) [Mono c.pt.hom]
    (h : Subobject.mk c.pt.hom = ⨆ j, Subobject.mk (F.obj j).obj.hom) :
    IsColimit ((Over.forget _).mapCocone c) := by
  let f : colimit (F ⋙ MonoOver.forget X ⋙ Over.forget X) ⟶ X :=
    colimit.desc _ (Cocone.mk X
      { app j := (F.obj j).obj.hom
        naturality {j j'} g := by simp [MonoOver.forget] })
  haveI := mono_of_isColimit_monoOver F (colimit.isColimit _) f (by simp [f])
  have := subobjectMk_of_isColimit_eq_iSup F (colimit.isColimit _) f (by simp [f])
  rw [← h] at this
  refine IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (Subobject.isoOfMkEqMk _ _ this) (fun j => ?_))
  rw [← cancel_mono (c.pt.hom)]
  dsimp
  rw [Category.assoc]; rw [Subobject.ofMkLEMk_comp]; rw [Over.w]
  apply colimit.ι_desc

/--
lemma `exists_isIso_of_functor_from_monoOver` / 引理 `exists_isIso_of_functor_from_monoOver`

English:
lemma exists_isIso_of_functor_from_monoOver
  proof: by
  have := isFiltered_of_isCardinalFiltered J κ
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f]; rw [subobjectMk_of_isColimit_eq_iSup F hc f hf] at h
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  have h' : Function.Surjective (fun (j : J) => 

中文:
引理 exists_isIso_of_functor_from_monoOver
  证明: by
  have := isFiltered_of_isCardinalFiltered J κ
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f]; rw [subobjectMk_of_isColimit_eq_iSup F hc f hf] at h
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  have h' : Function.Surjective (fun (j : J) => 

Depends on / 依赖: F.obj, Function, Function.Surjective, HasCardinalLT, Set.range, Subobject, Subobject.epi_iff_mk_eq_top, Subobject.mk, Subtype, Subtype.val, Subtype.val_injective, Surjective, epi_iff_mk_eq_top, hasRightInverse, isFiltered_of_isCardinalFiltered, mono_of_isColimit_monoOver, obj.hom, of_injective, subobjectMk_of_isColimit_eq_iSup, val_injective
-/
lemma exists_isIso_of_functor_from_monoOver
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ)
    (c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)) (hc : IsColimit c)
    (f : c.pt ⟶ X) (hf : forall (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom) (h : Epi f) :
    exists (j : J), IsIso (F.obj j).obj.hom := by
  have := isFiltered_of_isCardinalFiltered J κ
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f]; rw [subobjectMk_of_isColimit_eq_iSup F hc f hf] at h
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  have h' : Function.Surjective (fun (j : J) => (⟨s j, _, rfl⟩ : Set.range s)) := by
    rintro ⟨_, j, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨σ, hσ⟩ := h'.hasRightInverse
  have hs : HasCardinalLT (Set.range s) κ :=
    hXκ.of_injective (f := Subtype.val) Subtype.val_injective
  refine ⟨IsCardinalFiltered.max σ hs, ?_⟩
  rw [Subobject.isIso_iff_mk_eq_top]; rw [← top_le_iff]; rw [← h]; rw [iSup_le_iff]
  intro j
  let t : Set.range s := ⟨_, j, rfl⟩
  trans Subobject.mk (F.obj (σ t)).obj.hom
  · exact (hσ t).symm.le
  · exact MonoOver.subobjectMk_le_mk_of_hom
      (F.map (IsCardinalFiltered.toMax σ hs t))

end IsGrothendieckAbelian

end CategoryTheory
