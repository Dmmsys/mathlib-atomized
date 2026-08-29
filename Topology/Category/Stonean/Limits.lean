/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.Topology.Category.CompHausLike.Limits
public import Mathlib.Topology.Category.Stonean.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `Stonean`.
-/

public section

universe w u

open CategoryTheory Limits CompHausLike Topology

namespace Stonean

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitFiniteCoproducts.{w, u} (fun Y => ExtremallyDisconnected Y)
  body: { hasProp := show ExtremallyDisconnected (Σ (_a : _), _) from inferInstance }

中文:
实例 :
  签名: 有ExplicitFiniteCoproducts.{w, u} (fun Y => ExtremallyDisconnected Y)
  定义体: { hasProp := show ExtremallyDisconnected (Σ (_a : _), _) from inferInstance }

Depends on / 依赖: ExtremallyDisconnected, hasProp
-/
instance : HasExplicitFiniteCoproducts.{w, u} (fun Y => ExtremallyDisconnected Y) where
  hasProp _ := { hasProp := show ExtremallyDisconnected (Σ (_a : _), _) from inferInstance }

variable {X Y Z : Stonean} {f : X ⟶ Z} (i : Y ⟶ Z) (hi : IsOpenEmbedding f)
include hi

/--
lemma `extremallyDisconnected_preimage` / 引理 `extremallyDisconnected_preimage`

English:
lemma extremallyDisconnected_preimage
  statement: ExtremallyDisconnected (i ⁻¹' (Set.range f)) where
  proof: by
    have h : IsClopen (i ⁻¹' (Set.range f)) :=
      ⟨IsClosed.preimage i.hom.hom.continuous (isCompact_range f.hom.hom.continuous).isClosed,
        IsOpen.preimage i.hom.hom.continuous hi.isOpen_range⟩
    rw [← (closure U).preimage_image_eq Subtype.coe_injective]; rw [← h.1.isClosedEmbedding_s

中文:
引理 extremallyDisconnected_preimage
  结论: ExtremallyDisconnected (i ⁻¹' (集合.range f)) where
  证明: by
    have h : IsClopen (i ⁻¹' (Set.range f)) :=
      ⟨IsClosed.preimage i.hom.hom.continuous (isCompact_range f.hom.hom.continuous).isClosed,
        IsOpen.preimage i.hom.hom.continuous hi.isOpen_range⟩
    rw [← (closure U).preimage_image_eq Subtype.coe_injective]; rw [← h.1.isClosedEmbedding_s

Depends on / 依赖: ExtremallyDisconnected, ExtremallyDisconnected.open_closure, IsClopen, IsClosed, IsClosed.preimage, IsOpen, IsOpen.preimage, Set.range, Subtype, Subtype.coe_injective, closure, closure_image_eq, coe_injective, continuous, f.hom.hom.continuous, hi.isOpen_range, i.hom.hom.continuous, isClosed, isClosedEmbedding_subtypeVal, isClosedEmbedding_subtypeVal.closure_image_eq
-/
lemma extremallyDisconnected_preimage : ExtremallyDisconnected (i ⁻¹' (Set.range f)) where
  open_closure U hU := by
    have h : IsClopen (i ⁻¹' (Set.range f)) :=
      ⟨IsClosed.preimage i.hom.hom.continuous (isCompact_range f.hom.hom.continuous).isClosed,
        IsOpen.preimage i.hom.hom.continuous hi.isOpen_range⟩
    rw [← (closure U).preimage_image_eq Subtype.coe_injective]; rw [← h.1.isClosedEmbedding_subtypeVal.closure_image_eq U]
    exact isOpen_induced (ExtremallyDisconnected.open_closure _
      (h.2.isOpenEmbedding_subtypeVal.isOpenMap U hU))

/--
lemma `extremallyDisconnected_pullback` / 引理 `extremallyDisconnected_pullback`

English:
lemma extremallyDisconnected_pullback
  statement: ExtremallyDisconnected {xy : X × Y | f xy.1 = i xy.2}
  proof: have := extremallyDisconnected_preimage i hi
  let e := (TopCat.pullbackHomeoPreimage i i.hom.hom.2 f hi.isEmbedding).symm
  let e' : {xy : X × Y | f xy.1 = i xy.2} ≃ₜ {xy : Y × X | i xy.1 = f xy.2} := by
    exact TopCat.homeoOfIso
      ((TopCat.pullbackIsoProdSubtype f.hom i.hom).symm ≪≫ pullback

中文:
引理 extremallyDisconnected_pullback
  结论: ExtremallyDisconnected {xy : X × Y | f xy.1 = i xy.2}
  证明: have := extremallyDisconnected_preimage i hi
  let e := (TopCat.pullbackHomeoPreimage i i.hom.hom.2 f hi.isEmbedding).symm
  let e' : {xy : X × Y | f xy.1 = i xy.2} ≃ₜ {xy : Y × X | i xy.1 = f xy.2} := by
    exact TopCat.homeoOfIso
      ((TopCat.pullbackIsoProdSubtype f.hom i.hom).symm ≪≫ pullback

Depends on / 依赖: TopCat, TopCat.homeoOfIso, TopCat.pullbackHomeoPreimage, TopCat.pullbackIsoProdSubtype, e.trans, extremallyDisconnected_of_homeo, extremallyDisconnected_preimage, f.hom, hi.isEmbedding, homeoOfIso, i.hom, i.hom.hom, isEmbedding, pullbackHomeoPreimage, pullbackIsoProdSubtype, pullbackSymmetry
-/
lemma extremallyDisconnected_pullback : ExtremallyDisconnected {xy : X × Y | f xy.1 = i xy.2} :=
  have := extremallyDisconnected_preimage i hi
  let e := (TopCat.pullbackHomeoPreimage i i.hom.hom.2 f hi.isEmbedding).symm
  let e' : {xy : X × Y | f xy.1 = i xy.2} ≃ₜ {xy : Y × X | i xy.1 = f xy.2} := by
    exact TopCat.homeoOfIso
      ((TopCat.pullbackIsoProdSubtype f.hom i.hom).symm ≪≫ pullbackSymmetry _ _ ≪≫
        (TopCat.pullbackIsoProdSubtype i.hom f.hom))
  extremallyDisconnected_of_homeo (e.trans e'.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitPullbacksOfInclusions (fun (Y : TopCat.{u}) => ExtremallyDisconnected Y)
  body: by
  apply CompHausLike.hasPullbacksOfInclusions
  intro _ _ _ _ _ hi
  exact ⟨extremallyDisconnected_pullback _ hi⟩

example : FinitaryExtensive Stonean.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts Stonean.toCompHaus := inferInstance

noncomputable example : PreservesFini

中文:
实例 :
  签名: 有ExplicitPullbacksOfInclusions (fun (Y : 顶元素范畴.{u}) => ExtremallyDisconnected Y)
  定义体: by
  apply CompHausLike.hasPullbacksOfInclusions
  intro _ _ _ _ _ hi
  exact ⟨extremallyDisconnected_pullback _ hi⟩

example : FinitaryExtensive Stonean.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts Stonean.toCompHaus := inferInstance

noncomputable example : PreservesFini

Depends on / 依赖: CompHausLike, CompHausLike.hasPullbacksOfInclusions, extremallyDisconnected_pullback, hasPullbacksOfInclusions
-/
instance : HasExplicitPullbacksOfInclusions (fun (Y : TopCat.{u}) => ExtremallyDisconnected Y) := by
  apply CompHausLike.hasPullbacksOfInclusions
  intro _ _ _ _ _ hi
  exact ⟨extremallyDisconnected_pullback _ hi⟩

example : FinitaryExtensive Stonean.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts Stonean.toCompHaus := inferInstance

noncomputable example : PreservesFiniteCoproducts Stonean.toProfinite := inferInstance

end Stonean
