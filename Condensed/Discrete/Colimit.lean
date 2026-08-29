/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Equivalence
public import Mathlib.Topology.Category.LightProfinite.Extend

/-!

# The condensed set given by left Kan extension from `FintypeCat` to `Profinite`.

This file provides the necessary API to prove that a condensed set `X` is discrete if and only if
for every profinite set `S = limᵢSᵢ`, `X(S) ≅ colimᵢX(Sᵢ)`, and the analogous result for light
condensed sets.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Functor Limits FintypeCat CompHausLike.LocallyConstant

namespace Condensed

section LocallyConstantAsColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {F : I ⥤ FintypeCat.{u}}
  (c : Cone <| F ⋙ toProfinite) (X : Type (u + 1))

/--
Definition of `locallyConstantPresheaf` / `locallyConstantPresheaf` 的定义

English:
abbreviation locallyConstantPresheaf
  signature: : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)
  body: CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

#adaptation_note

中文:
缩写 locallyConstantPresheaf
  签名: : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)
  定义体: CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

#adaptation_note

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstant.functorToPresheaves, LocallyConstant, functorToPresheaves
-/
abbrev locallyConstantPresheaf : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u + 1}.obj X

#adaptation_note
/--
In this declaration and `isColimitLocallyConstantPresheaf`, `coe_comp` interferes with rewriting via
`Cone.w`, so we needed to manually exclude it.
-/
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitLocallyConstantPresheaf` / `isColimitLocallyConstantPresheaf` 的定义

English:
definition isColimitLocallyConstantPresheaf
  signature: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  body: by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.c

中文:
定义 isColimitLocallyConstantPresheaf
  签名: (hc : IsLimit c) [对任意 i, Epi (c.π.app i)]
  定义体: by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.c

Depends on / 依赖: FilteredColimit, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, LocallyConstant, Profinite, Profinite.epi_iff_surjective, Profinite.exists_locallyConstant, Types.FilteredColimit.isColimitOf, c.pt, cone_objs, epi_iff_surjective, exists_locallyConstant, fi.comap, fj.comap, hom.hom, isColimitOf, ki.op, kj.op
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [forall i, Epi (c.π.app i)] :
IsColimit (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, u} c hc f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((Profinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    dsimp [- CompHausLike.coe_comp] -- `coe_comp` prevents rewriting with `c.w`
    rwa [dsimp% c.w, dsimp% c.w]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `isColimitLocallyConstantPresheaf_desc_apply` / 引理 `isColimitLocallyConstantPresheaf_desc_apply`

English:
lemma isColimitLocallyConstantPresheaf_desc_apply
  statement: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  proof: by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨i⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

中文:
引理 isColimitLocallyConstantPresheaf_desc_apply
  结论: (hc : IsLimit c) [对任意 i, Epi (c.π.app i)]
  证明: by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨i⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

Depends on / 依赖: c.op, isColimitLocallyConstantPresheaf, locallyConstantPresheaf, mapCocone
-/
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [forall i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toProfinite).op ⋙ locallyConstantPresheaf X))
    (i : I) (f : LocallyConstant (toProfinite.obj (F.obj i)) X) :
    dsimp% (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app i).hom.hom) =
      s.ι.app ⟨i⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨i⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

/--
Definition of `isColimitLocallyConstantPresheafDiagram` / `isColimitLocallyConstantPresheafDiagram` 的定义

English:
definition isColimitLocallyConstantPresheafDiagram
  signature: (S : Profinite)
  body: isColimitLocallyConstantPresheaf _ _ S.asLimit

@[simp]

中文:
定义 isColimitLocallyConstantPresheafDiagram
  签名: (S : Profinite)
  定义体: isColimitLocallyConstantPresheaf _ _ S.asLimit

@[simp]

Depends on / 依赖: S.asLimit, asLimit, isColimitLocallyConstantPresheaf
-/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : Profinite) :
IsColimit (locallyConstantPresheaf X).mapCocone S.asLimitCone.op :=
  isColimitLocallyConstantPresheaf _ _ S.asLimit

@[simp]
/--
lemma `isColimitLocallyConstantPresheafDiagram_desc_apply` / 引理 `isColimitLocallyConstantPresheafDiagram_desc_apply`

English:
lemma isColimitLocallyConstantPresheafDiagram_desc_apply
  statement: (S : Profinite)
  proof: isColimitLocallyConstantPresheaf_desc_apply S.asLimitCone X S.asLimit s i f

中文:
引理 isColimitLocallyConstantPresheafDiagram_desc_apply
  结论: (S : Profinite)
  证明: isColimitLocallyConstantPresheaf_desc_apply S.asLimitCone X S.asLimit s i f

Depends on / 依赖: S.asLimit, S.asLimitCone, asLimit, asLimitCone, isColimitLocallyConstantPresheaf_desc_apply
-/
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : Profinite)
    (s : Cocone (S.diagram.op ⋙ locallyConstantPresheaf X))
    (i : DiscreteQuotient S) (f : LocallyConstant (S.diagram.obj i) X) :
    dsimp% (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app i).hom.hom) = s.ι.app ⟨i⟩ f :=
  isColimitLocallyConstantPresheaf_desc_apply S.asLimitCone X S.asLimit s i f

end LocallyConstantAsColimit

/--
Definition of `lanPresheaf` / `lanPresheaf` 的定义

English:
abbreviation lanPresheaf
  signature: (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
  body: pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

中文:
缩写 lanPresheaf
  签名: (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
  定义体: pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

Depends on / 依赖: pointwiseLeftKanExtension, toProfinite, toProfinite.op
-/
abbrev lanPresheaf (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) : Profinite.{u}ᵒᵖ ⥤ Type (u + 1) :=
  pointwiseLeftKanExtension toProfinite.op (toProfinite.op ⋙ F)

/--
Definition of `lanPresheafExt` / `lanPresheafExt` 的定义

English:
definition lanPresheafExt
  signature: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
  body: leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

中文:
定义 lanPresheafExt
  签名: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
  定义体: leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

Depends on / 依赖: leftKanExtensionUniqueOfIso, pointwiseLeftKanExtensionUnit
-/
def lanPresheafExt {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafExt_hom` / 引理 `lanPresheafExt_hom`

English:
lemma lanPresheafExt_hom
  statement: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
  proof: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

中文:
引理 lanPresheafExt_hom
  结论: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
  证明: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext, lanPresheaf, lanPresheafExt, leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app
-/
lemma lanPresheafExt_hom {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.hom) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafExt_inv` / 引理 `lanPresheafExt_inv`

English:
lemma lanPresheafExt_inv
  statement: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
  proof: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

中文:
引理 lanPresheafExt_inv
  结论: {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
  证明: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext, lanPresheaf, lanPresheafExt, leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app
-/
lemma lanPresheafExt_inv {F G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)} (S : Profinite.{u}ᵒᵖ)
    (i : toProfinite.op ⋙ F ≅ toProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toProfinite.op S) i.inv) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : Profinite.{u}} {F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1)}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Final Profinite.Extend.functorOp S.asLimitCone
  body: Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

中文:
实例 :
  签名: Final Profinite.Extend.functorOp S.asLimitCone
  定义体: Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

Depends on / 依赖: Extend, Profinite, Profinite.Extend.functorOp_final, S.asLimit, S.asLimitCone, asLimit, asLimitCone, functorOp_final
-/
instance : Final Profinite.Extend.functorOp S.asLimitCone :=
  Profinite.Extend.functorOp_final S.asLimitCone S.asLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `lanPresheafIso` / `lanPresheafIso` 的定义

English:
definition lanPresheafIso
  signature: (hF : IsColimit <| F.mapCocone S.asLimitCone.op)
  body: (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

中文:
定义 lanPresheafIso
  签名: (hF : IsColimit <| F.mapCocone S.asLimitCone.op)
  定义体: (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

Depends on / 依赖: Extend, Functor, Functor.Final.colimitIso, Profinite, Profinite.Extend.functorOp, S.asLimitCone, asLimitCone, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitIso, functorOp, isColimit
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (Profinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafIso_hom` / 引理 `lanPresheafIso_hom`

English:
lemma lanPresheafIso_hom
  given: (hF : IsColimit <| F.mapCocone S.asLimitCone.op)
  proof: by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

中文:
引理 lanPresheafIso_hom
  条件: (hF : IsColimit <| F.mapCocone S.asLimitCone.op)
  证明: by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

Depends on / 依赖: Final.colimitIso, colimitIso, lanPresheafIso
-/
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone S.asLimitCone.op) :
    (lanPresheafIso hF).hom = colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lanPresheafNatIso` / `lanPresheafNatIso` 的定义

English:
definition lanPresheafNatIso
  signature: (hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
  body: NatIso.ofComponents (fun ⟨S⟩ => (lanPresheafIso (hF S)))
    fun _ => (by simpa using colimit.hom_ext fun _ => (by simp))

中文:
定义 lanPresheafNatIso
  签名: (hF : 对任意 S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
  定义体: NatIso.ofComponents (fun ⟨S⟩ => (lanPresheafIso (hF S)))
    fun _ => (by simpa using colimit.hom_ext fun _ => (by simp))

Depends on / 依赖: NatIso, NatIso.ofComponents, colimit, colimit.hom_ext, hom_ext, lanPresheafIso, ofComponents
-/
def lanPresheafNatIso (hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    lanPresheaf F ≅ F :=
  NatIso.ofComponents (fun ⟨S⟩ => (lanPresheafIso (hF S)))
    fun _ => (by simpa using colimit.hom_ext fun _ => (by simp))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lanPresheafNatIso_hom_app` / 引理 `lanPresheafNatIso_hom_app`

English:
lemma lanPresheafNatIso_hom_app
  statement: (hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
  proof: by
  simp [lanPresheafNatIso]

中文:
引理 lanPresheafNatIso_hom_app
  结论: (hF : 对任意 S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
  证明: by
  simp [lanPresheafNatIso]

Depends on / 依赖: lanPresheafNatIso
-/
lemma lanPresheafNatIso_hom_app (hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op)
    (S : Profiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (Profinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
Definition of `lanSheafProfinite` / `lanSheafProfinite` 的定义

English:
definition lanSheafProfinite
  signature: (X : Type (u + 1))
  body: lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u + 1}
      (hs := fun _ _ _ => ((Profinite.effectiveEpi_tfae _).out 0 2)

中文:
定义 lanSheafProfinite
  签名: (X : Type (u + 1))
  定义体: lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u + 1}
      (hs := fun _ _ _ => ((Profinite.effectiveEpi_tfae _).out 0 2)

Depends on / 依赖: lanPresheaf, locallyConstantPresheaf
-/
def lanSheafProfinite (X : Type (u + 1)) :
    Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)) where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact ((CompHausLike.LocallyConstant.functor.{u, u + 1}
      (hs := fun _ _ _ => ((Profinite.effectiveEpi_tfae _).out 0 2).mp)).obj X).property

/--
Definition of `lanCondensedSet` / `lanCondensedSet` 的定义

English:
definition lanCondensedSet
  signature: (X : Type (u + 1))
  body: (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

中文:
定义 lanCondensedSet
  签名: (X : Type (u + 1))
  定义体: (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

Depends on / 依赖: ProfiniteCompHaus, ProfiniteCompHaus.equivalence, equivalence, functor, functor.obj, lanSheafProfinite
-/
def lanCondensedSet (X : Type (u + 1)) : CondensedSet.{u} :=
  (ProfiniteCompHaus.equivalence _).functor.obj (lanSheafProfinite X)

variable (F : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`Profinite`.
-/
@[simps obj map]
/--
Definition of `finYoneda` / `finYoneda` 的定义

English:
definition finYoneda
  signature: : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where
  body: X.unop -> F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

中文:
定义 finYoneda
  签名: : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where
  定义体: X.unop -> F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

Depends on / 依赖: F.obj, X.unop, disjSum, toProfinite, toProfinite.op.obj, univ.disjSum
-/
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj X := X.unop -> F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

/-- `locallyConstantPresheaf` restricted to finite sets is isomorphic to `finYoneda F`. -/
@[simps! hom_app]
/--
Definition of `locallyConstantIsoFinYoneda` / `locallyConstantIsoFinYoneda` 的定义

English:
definition locallyConstantIsoFinYoneda
  signature: :
  body: NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

中文:
定义 locallyConstantIsoFinYoneda
  签名: :
  定义体: NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.of_discrete, NatIso, NatIso.ofComponents, ofComponents, of_discrete
-/
def locallyConstantIsoFinYoneda :
    toProfinite.op ⋙ (locallyConstantPresheaf (F.obj (toProfinite.op.obj
⟨of PUnit.{u + 1}⟩))) ≅
    finYoneda F :=
  NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/--
Definition of `fintypeCatAsCofan` / `fintypeCatAsCofan` 的定义

English:
definition fintypeCatAsCofan
  signature: (X : Profinite)
  body: Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

中文:
定义 fintypeCatAsCofan
  签名: (X : Profinite)
  定义体: Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

Depends on / 依赖: Cofan.mk, ConcreteCategory, ConcreteCategory.ofHom, ContinuousMap, ContinuousMap.const
-/
def fintypeCatAsCofan (X : Profinite) :
    Cofan (fun (_ : X) => (Profinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

/--
Definition of `fintypeCatAsCofanIsColimit` / `fintypeCatAsCofanIsColimit` 的定义

English:
definition fintypeCatAsCofanIsColimit
  signature: (X : Profinite) [Finite X]
  body: Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

中文:
定义 fintypeCatAsCofanIsColimit
  签名: (X : Profinite) [Finite X]
  定义体: Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, Cofan.IsColimit.mk, ConcreteCategory, ConcreteCategory.ofHom, IsColimit, PUnit.unit, congr_fun, continuous_of_discreteTopology, t.inj
-/
def fintypeCatAsCofanIsColimit (X : Profinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]

noncomputable instance (X : Profinite) [Finite X] :
    PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := .of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/--
Definition of `isoFinYonedaComponents` / `isoFinYonedaComponents` 的定义

English:
definition isoFinYonedaComponents
  signature: (X : Profinite.{u}) [Finite X]
  body: (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u + 1} fun _ => F.obj ⟨Profinite.of PUnit.{u + 1}⟩).2

@[simp]

中文:
定义 isoFinYonedaComponents
  签名: (X : Profinite.{u}) [Finite X]
  定义体: (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u + 1} fun _ => F.obj ⟨Profinite.of PUnit.{u + 1}⟩).2

@[simp]

Depends on / 依赖: Cofan.IsColimit.op, F.obj, IsColimit, Profinite, Profinite.of, Types.productLimitCone, conePointUniqueUpToIso, fintypeCatAsCofanIsColimit, isLimitFanMkObjOfIsLimit, productLimitCone
-/
def isoFinYonedaComponents (X : Profinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X -> F.obj ⟨Profinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u + 1} fun _ => F.obj ⟨Profinite.of PUnit.{u + 1}⟩).2

@[simp]
/--
lemma `isoFinYonedaComponents_hom` / 引理 `isoFinYonedaComponents_hom`

English:
lemma isoFinYonedaComponents_hom
  given: (X : Profinite.{u}) [Finite X]
  proof: rfl

中文:
引理 isoFinYonedaComponents_hom
  条件: (X : Profinite.{u}) [Finite X]
  证明: rfl
-/
lemma isoFinYonedaComponents_hom (X : Profinite.{u}) [Finite X] :
    (isoFinYonedaComponents F X).hom =
    ↾fun y x => F.map ((Profinite.of PUnit.{u + 1}).const x).op y :=
  rfl

/--
lemma `isoFinYonedaComponents_hom_apply` / 引理 `isoFinYonedaComponents_hom_apply`

English:
lemma isoFinYonedaComponents_hom_apply
  given: (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X)
  proof: rfl

中文:
引理 isoFinYonedaComponents_hom_apply
  条件: (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X)
  证明: rfl
-/
lemma isoFinYonedaComponents_hom_apply (X : Profinite.{u}) [Finite X] (y : F.obj ⟨X⟩) (x : X) :
    (isoFinYonedaComponents F X).hom y x =
      F.map ((Profinite.of PUnit.{u + 1}).const x).op y :=
  rfl

/--
lemma `isoFinYonedaComponents_inv_comp` / 引理 `isoFinYonedaComponents_inv_comp`

English:
lemma isoFinYonedaComponents_inv_comp
  statement: {X Y : Profinite.{u}} [Finite X] [Finite Y]
  proof: by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_appl

中文:
引理 isoFinYonedaComponents_inv_comp
  结论: {X Y : Profinite.{u}} [Finite X] [Finite Y]
  证明: by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_appl

Depends on / 依赖: CompHausLike, CompHausLike.const_comp, Function, Function.comp_apply, Functor, Functor.map_comp_apply, Iso.inv_hom_id_apply, comp_apply, const_comp, injective_of_mono, inv_hom_id_apply, isoFinYonedaComponents, isoFinYonedaComponents_hom_apply, map_comp_apply, op_comp
-/
lemma isoFinYonedaComponents_inv_comp {X Y : Profinite.{u}} [Finite X] [Finite Y]
    (f : Y -> F.obj ⟨Profinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_apply]

attribute [local simp] toProfinite_obj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps! +dsimpLhs]
/--
Definition of `isoFinYoneda` / `isoFinYoneda` 的定义

English:
definition isoFinYoneda
  signature: : toProfinite.op ⋙ F ≅ finYoneda F
  body: NatIso.ofComponents (fun X => isoFinYonedaComponents F (toProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofH

中文:
定义 isoFinYoneda
  签名: : toProfinite.op ⋙ F ≅ finYoneda F
  定义体: NatIso.ofComponents (fun X => isoFinYonedaComponents F (toProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofH

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_map, Functor.map_comp_apply, NatIso, NatIso.ofComponents, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, X.unop, coe_mk, comp_apply, comp_map, comp_obj, finYoneda_obj, hom_ofHom, isoFinYonedaComponents
-/
def isoFinYoneda : toProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X => isoFinYonedaComponents F (toProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, toProfinite_obj,
      ← Functor.map_comp_apply]
    rfl

/--
Definition of `isoLocallyConstantOfIsColimit` / `isoLocallyConstantOfIsColimit` 的定义

English:
definition isoLocallyConstantOfIsColimit
  body: (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

中文:
定义 isoLocallyConstantOfIsColimit
  定义体: (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

Depends on / 依赖: isColimitLocallyConstantPresheafDiagram, isoFinYoneda, lanPresheafExt, lanPresheafNatIso, locallyConstantIsoFinYoneda
-/
def isoLocallyConstantOfIsColimit
    (hF : forall S : Profinite, IsColimit <| F.mapCocone S.asLimitCone.op) :
    F ≅ locallyConstantPresheaf (F.obj (toProfinite.op.obj ⟨of <| PUnit.{u + 1}⟩)) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isoLocallyConstantOfIsColimit_inv` / 引理 `isoLocallyConstantOfIsColimit_inv`

English:
lemma isoLocallyConstantOfIsColimit_inv
  statement: (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
  proof: by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [lo

中文:
引理 isoLocallyConstantOfIsColimit_inv
  结论: (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
  证明: by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [lo

Depends on / 依赖: Category, Category.assoc, Iso.inv_comp_eq, Opposite, Opposite.unop, TypeCat, TypeCat.Fun.toFun_apply, X.map, colimit, colimit.hom_ext, counitApp, counitAppApp, functorToPresheaves_obj_obj, hom_ext, inv_comp_eq, isoFinYoneda, isoFinYonedaComponents, isoLocallyConstantOfIsColimit, locallyConstantIsoFinYoneda, locallyConstantPresheaf
-/
lemma isoLocallyConstantOfIsColimit_inv (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
    [PreservesFiniteProducts X]
    (hX : forall S : Profinite.{u}, (IsColimit <| X.mapCocone S.asLimitCone.op)) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u + 1} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u + 1} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  simp only [toProfinite_obj, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, counitApp_app]
  apply presheaf_ext.{u, u + 1} (X := X) (Y := X) (f := f)
  intro x
  dsimp [toProfinite_obj]
  rw [incl_of_counitAppApp.{u]; rw [u + 1}]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u + 1} f x) :=
    Finite.of_injective (sigmaIncl.{u, u + 1} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u + 1} f x)).hom
  ext y
  simp only [toProfinite_obj, isoFinYonedaComponents_hom, ConcreteCategory.hom_ofHom,
    TypeCat.Fun.coe_mk, ← Functor.map_comp_apply, ← op_comp]
  rw [show (Profinite.of PUnit.{u + 1}).const y ≫
    IsTerminal.from _ (fiber.{u]; rw [u + 1} f x) = 𝟙 _ from rfl]
  simp only [op_comp, Functor.map_comp_apply, op_id, Functor.map_id_apply]
  simpa [← dsimp% isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u + 1} f x),
    ← isoFinYonedaComponents_hom_apply, -isoFinYonedaComponents_hom] using! x.map_eq_image f y

end Condensed

namespace LightCondensed

section LocallyConstantAsColimit

variable {F : Natᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite) (X : Type u)

/--
Definition of `locallyConstantPresheaf` / `locallyConstantPresheaf` 的定义

English:
abbreviation locallyConstantPresheaf
  signature: : LightProfiniteᵒᵖ ⥤ Type u
  body: CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

中文:
缩写 locallyConstantPresheaf
  签名: : LightProfiniteᵒᵖ ⥤ 类型u
  定义体: CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstant.functorToPresheaves, LocallyConstant, functorToPresheaves
-/
abbrev locallyConstantPresheaf : LightProfiniteᵒᵖ ⥤ Type u :=
  CompHausLike.LocallyConstant.functorToPresheaves.{u, u}.obj X

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitLocallyConstantPresheaf` / `isColimitLocallyConstantPresheaf` 的定义

English:
definition isColimitLocallyConstantPresheaf
  signature: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  body: by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (f

中文:
定义 isColimitLocallyConstantPresheaf
  签名: (hc : IsLimit c) [对任意 i, Epi (c.π.app i)]
  定义体: by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (f

Depends on / 依赖: FilteredColimit, IsCofilteredOrEmpty, IsCofilteredOrEmpty.cone_objs, LightPr, LocallyConstant, Profinite, Profinite.exists_locallyConstant, Types.FilteredColimit.isColimitOf, c.pt, cone_objs, exists_locallyConstant, fi.comap, fj.comap, hom.hom, isColimitOf, isLimitOfPreserves, ki.op, kj.op, lightToProfinite, lightToProfinite.mapCone
-/
noncomputable def isColimitLocallyConstantPresheaf (hc : IsLimit c) [forall i, Epi (c.π.app i)] :
IsColimit (locallyConstantPresheaf X).mapCocone c.op := by
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (f : LocallyConstant c.pt X)
    obtain ⟨j, h⟩ := Profinite.exists_locallyConstant.{_, 0} (lightToProfinite.mapCone c)
      (isLimitOfPreserves lightToProfinite hc) f
    exact ⟨⟨j⟩, h⟩
  · intro ⟨i⟩ ⟨j⟩ (fi : LocallyConstant _ _) (fj : LocallyConstant _ _)
      (h : fi.comap (c.π.app i).hom.hom = fj.comap (c.π.app j).hom.hom)
    obtain ⟨k, ki, kj, _⟩ := IsCofilteredOrEmpty.cone_objs i j
    refine ⟨⟨k⟩, ki.op, kj.op, ?_⟩
    dsimp
    ext x
    obtain ⟨x, hx⟩ := ((LightProfinite.epi_iff_surjective (c.π.app k)).mp inferInstance) x
    rw [← hx]
    change fi ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x) =
      fj ((c.π.app k ≫ (F ⋙ toLightProfinite).map _) x)
    have h := LocallyConstant.congr_fun h x
    dsimp [- CompHausLike.coe_comp] -- `coe_comp` prevents rewriting with `c.w`
    rwa [dsimp% c.w, dsimp% c.w]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `isColimitLocallyConstantPresheaf_desc_apply` / 引理 `isColimitLocallyConstantPresheaf_desc_apply`

English:
lemma isColimitLocallyConstantPresheaf_desc_apply
  statement: (hc : IsLimit c) [forall i, Epi (c.π.app i)]
  proof: by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨n⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

中文:
引理 isColimitLocallyConstantPresheaf_desc_apply
  结论: (hc : IsLimit c) [对任意 i, Epi (c.π.app i)]
  证明: by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨n⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

Depends on / 依赖: c.op, isColimitLocallyConstantPresheaf, locallyConstantPresheaf, mapCocone
-/
lemma isColimitLocallyConstantPresheaf_desc_apply (hc : IsLimit c) [forall i, Epi (c.π.app i)]
    (s : Cocone ((F ⋙ toLightProfinite).op ⋙ locallyConstantPresheaf X))
    (n : Natᵒᵖ) (f : LocallyConstant (toLightProfinite.obj (F.obj n)) X) :
    dsimp% (isColimitLocallyConstantPresheaf c X hc).desc s (f.comap (c.π.app n).hom.hom) =
      s.ι.app ⟨n⟩ f := by
  change ((((locallyConstantPresheaf X).mapCocone c.op).ι.app ⟨n⟩) ≫
    (isColimitLocallyConstantPresheaf c X hc).desc s) _ = _
  rw [(isColimitLocallyConstantPresheaf c X hc).fac]

/--
Definition of `isColimitLocallyConstantPresheafDiagram` / `isColimitLocallyConstantPresheafDiagram` 的定义

English:
definition isColimitLocallyConstantPresheafDiagram
  signature: (S : LightProfinite)
  body: (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence Nat).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

中文:
定义 isColimitLocallyConstantPresheafDiagram
  签名: (S : LightProfinite)
  定义体: (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence Nat).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, S.asLimit, asLimit, inverse, isColimitLocallyConstantPresheaf, isColimitWhiskerEquiv, opOpEquivalence
-/
noncomputable def isColimitLocallyConstantPresheafDiagram (S : LightProfinite) :
IsColimit (locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone) :=
  (Functor.Final.isColimitWhiskerEquiv (opOpEquivalence Nat).inverse _).symm
    (isColimitLocallyConstantPresheaf _ _ S.asLimit)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `isColimitLocallyConstantPresheafDiagram_desc_apply` / 引理 `isColimitLocallyConstantPresheafDiagram_desc_apply`

English:
lemma isColimitLocallyConstantPresheafDiagram_desc_apply
  statement: (S : LightProfinite)
  proof: by
  change ((((locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)).ι.app n) ≫
    (isColimitLocallyConstantPresheafDiagram X S).desc s) _ = _
  rw [(isColimitLocallyConstantPresheafDiagram X S).fac]

中文:
引理 isColimitLocallyConstantPresheafDiagram_desc_apply
  结论: (S : LightProfinite)
  证明: by
  change ((((locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)).ι.app n) ≫
    (isColimitLocallyConstantPresheafDiagram X S).desc s) _ = _
  rw [(isColimitLocallyConstantPresheafDiagram X S).fac]

Depends on / 依赖: S.asLimitCone, asLimitCone, coconeRightOpOfCone, isColimitLocallyConstantPresheafDiagram, locallyConstantPresheaf, mapCocone
-/
lemma isColimitLocallyConstantPresheafDiagram_desc_apply (S : LightProfinite)
    (s : Cocone (S.diagram.rightOp ⋙ locallyConstantPresheaf X))
    (n : Nat) (f : LocallyConstant (S.diagram.obj ⟨n⟩) X) :
    dsimp% (isColimitLocallyConstantPresheafDiagram X S).desc s
      (f.comap (S.asLimitCone.π.app ⟨n⟩).hom.hom) = s.ι.app n f := by
  change ((((locallyConstantPresheaf X).mapCocone (coconeRightOpOfCone S.asLimitCone)).ι.app n) ≫
    (isColimitLocallyConstantPresheafDiagram X S).desc s) _ = _
  rw [(isColimitLocallyConstantPresheafDiagram X S).fac]

end LocallyConstantAsColimit

instance (S : LightProfinite.{u}ᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow toLightProfinite.op S) (Type u) :=
  hasColimitsOfShape_of_equivalence (asEquivalence (CostructuredArrow.pre Skeleton.incl.op _ S))

/--
Definition of `lanPresheaf` / `lanPresheaf` 的定义

English:
abbreviation lanPresheaf
  signature: (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)
  body: pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

中文:
缩写 lanPresheaf
  签名: (F : LightProfinite.{u}ᵒᵖ ⥤ 类型u)
  定义体: pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

Depends on / 依赖: pointwiseLeftKanExtension, toLightProfinite, toLightProfinite.op
-/
abbrev lanPresheaf (F : LightProfinite.{u}ᵒᵖ ⥤ Type u) : LightProfinite.{u}ᵒᵖ ⥤ Type u :=
  pointwiseLeftKanExtension toLightProfinite.op (toLightProfinite.op ⋙ F)

/--
Definition of `lanPresheafExt` / `lanPresheafExt` 的定义

English:
definition lanPresheafExt
  signature: {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
  body: leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

中文:
定义 lanPresheafExt
  签名: {F G : LightProfinite.{u}ᵒᵖ ⥤ 类型u}
  定义体: leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

Depends on / 依赖: leftKanExtensionUniqueOfIso, pointwiseLeftKanExtensionUnit
-/
def lanPresheafExt {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u}
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : lanPresheaf F ≅ lanPresheaf G :=
  leftKanExtensionUniqueOfIso _ (pointwiseLeftKanExtensionUnit _ _) i _
    (pointwiseLeftKanExtensionUnit _ _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafExt_hom` / 引理 `lanPresheafExt_hom`

English:
lemma lanPresheafExt_hom
  statement: {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
  proof: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

中文:
引理 lanPresheafExt_hom
  结论: {F G : LightProfinite.{u}ᵒᵖ ⥤ 类型u} (S : LightProfinite.{u}ᵒᵖ)
  证明: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext, lanPresheaf, lanPresheafExt, leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app
-/
lemma lanPresheafExt_hom {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).hom.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.hom) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_hom, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafExt_inv` / 引理 `lanPresheafExt_inv`

English:
lemma lanPresheafExt_inv
  statement: {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
  proof: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

中文:
引理 lanPresheafExt_inv
  结论: {F G : LightProfinite.{u}ᵒᵖ ⥤ 类型u} (S : LightProfinite.{u}ᵒᵖ)
  证明: by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

Depends on / 依赖: colimit, colimit.hom_ext, hom_ext, lanPresheaf, lanPresheafExt, leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app
-/
lemma lanPresheafExt_inv {F G : LightProfinite.{u}ᵒᵖ ⥤ Type u} (S : LightProfinite.{u}ᵒᵖ)
    (i : toLightProfinite.op ⋙ F ≅ toLightProfinite.op ⋙ G) : (lanPresheafExt i).inv.app S =
      colimMap (whiskerLeft (CostructuredArrow.proj toLightProfinite.op S) i.inv) := by
  simp only [lanPresheaf, lanPresheafExt,
    leftKanExtensionUniqueOfIso_inv, pointwiseLeftKanExtension_desc_app]
  apply colimit.hom_ext
  aesop

variable {S : LightProfinite.{u}} {F : LightProfinite.{u}ᵒᵖ ⥤ Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Final LightProfinite.Extend.functorOp S.asLimitCone
  body: LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

中文:
实例 :
  签名: Final LightProfinite.Extend.functorOp S.asLimitCone
  定义体: LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

Depends on / 依赖: Extend, LightProfinite, LightProfinite.Extend.functorOp_final, S.asLimit, S.asLimitCone, asLimit, asLimitCone, functorOp_final
-/
instance : Final LightProfinite.Extend.functorOp S.asLimitCone :=
  LightProfinite.Extend.functorOp_final S.asLimitCone S.asLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `lanPresheafIso` / `lanPresheafIso` 的定义

English:
definition lanPresheafIso
  signature: (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
  body: (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

中文:
定义 lanPresheafIso
  签名: (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
  定义体: (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

Depends on / 依赖: Extend, Functor, Functor.Final.colimitIso, LightProfinite, LightProfinite.Extend.functorOp, S.asLimitCone, asLimitCone, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitIso, functorOp, isColimit
-/
def lanPresheafIso (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheaf F).obj ⟨S⟩ ≅ F.obj ⟨S⟩ :=
  (Functor.Final.colimitIso (LightProfinite.Extend.functorOp S.asLimitCone) _).symm ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hF

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `lanPresheafIso_hom` / 引理 `lanPresheafIso_hom`

English:
lemma lanPresheafIso_hom
  given: (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
  proof: by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

中文:
引理 lanPresheafIso_hom
  条件: (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
  证明: by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

Depends on / 依赖: Final.colimitIso, colimitIso, lanPresheafIso
-/
lemma lanPresheafIso_hom (hF : IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    (lanPresheafIso hF).hom = colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafIso, Final.colimitIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lanPresheafNatIso` / `lanPresheafNatIso` 的定义

English:
definition lanPresheafNatIso
  body: by
  refine NatIso.ofComponents
    (fun ⟨S⟩ => (lanPresheafIso (hF S))) fun _ => ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ => (by simp)

中文:
定义 lanPresheafNatIso
  定义体: by
  refine NatIso.ofComponents
    (fun ⟨S⟩ => (lanPresheafIso (hF S))) fun _ => ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ => (by simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, Opposite, Opposite.op_unop, colimit, colimit.hom_ext, hom_ext, lanPresheaf, lanPresheafIso, lanPresheafIso_hom, ofComponents, op_unop, pointwiseLeftKanExtension_map
-/
def lanPresheafNatIso
    (hF : forall S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
    lanPresheaf F ≅ F := by
  refine NatIso.ofComponents
    (fun ⟨S⟩ => (lanPresheafIso (hF S))) fun _ => ?_
  simp only [lanPresheaf, pointwiseLeftKanExtension_map,
    lanPresheafIso_hom, Opposite.op_unop]
  exact colimit.hom_ext fun _ => (by simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `lanPresheafNatIso_hom_app` / 引理 `lanPresheafNatIso_hom_app`

English:
lemma lanPresheafNatIso_hom_app
  proof: by
  simp [lanPresheafNatIso]

中文:
引理 lanPresheafNatIso_hom_app
  证明: by
  simp [lanPresheafNatIso]

Depends on / 依赖: lanPresheafNatIso
-/
lemma lanPresheafNatIso_hom_app
    (hF : forall S : LightProfinite, IsColimit <| F.mapCocone (coconeRightOpOfCone S.asLimitCone))
    (S : LightProfiniteᵒᵖ) : (lanPresheafNatIso hF).hom.app S =
      colimit.desc _ (LightProfinite.Extend.cocone _ _) := by
  simp [lanPresheafNatIso]

/--
Definition of `lanLightCondSet` / `lanLightCondSet` 的定义

English:
definition lanLightCondSet
  signature: (X : Type u)
  body: lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ => ((LightProfinite.effectiveEpi_iff_surjective _

中文:
定义 lanLightCondSet
  签名: (X : 类型u)
  定义体: lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ => ((LightProfinite.effectiveEpi_iff_surjective _

Depends on / 依赖: lanPresheaf, locallyConstantPresheaf
-/
def lanLightCondSet (X : Type u) : LightCondSet.{u} where
  obj := lanPresheaf (locallyConstantPresheaf X)
  property := by
    rw [Presheaf.isSheaf_of_iso_iff (lanPresheafNatIso
      fun _ => isColimitLocallyConstantPresheafDiagram _ _)]
    exact (CompHausLike.LocallyConstant.functor.{u, u}
      (hs := fun _ _ _ => ((LightProfinite.effectiveEpi_iff_surjective _).mp)).obj X).property

variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/--
The functor which takes a finite set to the set of maps into `F(*)` for a presheaf `F` on
`LightProfinite`.
-/
@[simps]
/--
Definition of `finYoneda` / `finYoneda` 的定义

English:
definition finYoneda
  signature: : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  body: X.unop -> F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

中文:
定义 finYoneda
  签名: : FintypeCat.{u}ᵒᵖ ⥤ 类型u where
  定义体: X.unop -> F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

Depends on / 依赖: F.obj, X.unop, toLightProfinite, toLightProfinite.op.obj
-/
def finYoneda : FintypeCat.{u}ᵒᵖ ⥤ Type u where
  obj X := X.unop -> F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩)
  map f := ↾fun g => g ∘ f.unop

/--
Definition of `locallyConstantIsoFinYoneda` / `locallyConstantIsoFinYoneda` 的定义

English:
definition locallyConstantIsoFinYoneda
  signature: : toLightProfinite.op ⋙
  body: NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

中文:
定义 locallyConstantIsoFinYoneda
  签名: : toLightProfinite.op ⋙
  定义体: NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.of_discrete, NatIso, NatIso.ofComponents, ofComponents, of_discrete
-/
def locallyConstantIsoFinYoneda : toLightProfinite.op ⋙
    (locallyConstantPresheaf (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) ≅ finYoneda F :=
  NatIso.ofComponents fun Y => {
    hom := ↾fun f => f.1
    inv := ↾fun f => ⟨f, @IsLocallyConstant.of_discrete _ _ _ ⟨rfl⟩ _⟩ }

/--
Definition of `fintypeCatAsCofan` / `fintypeCatAsCofan` 的定义

English:
definition fintypeCatAsCofan
  signature: (X : LightProfinite)
  body: Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

中文:
定义 fintypeCatAsCofan
  签名: (X : LightProfinite)
  定义体: Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

Depends on / 依赖: Cofan.mk, ConcreteCategory, ConcreteCategory.ofHom, ContinuousMap, ContinuousMap.const
-/
def fintypeCatAsCofan (X : LightProfinite) :
    Cofan (fun (_ : X) => (LightProfinite.of (PUnit.{u + 1}))) :=
  Cofan.mk X (fun x => ConcreteCategory.ofHom (ContinuousMap.const _ x))

/--
Definition of `fintypeCatAsCofanIsColimit` / `fintypeCatAsCofanIsColimit` 的定义

English:
definition fintypeCatAsCofanIsColimit
  signature: (X : LightProfinite) [Finite X]
  body: Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

中文:
定义 fintypeCatAsCofanIsColimit
  签名: (X : LightProfinite) [Finite X]
  定义体: Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, Cofan.IsColimit.mk, ConcreteCategory, ConcreteCategory.ofHom, IsColimit, PUnit.unit, congr_fun, continuous_of_discreteTopology, t.inj
-/
def fintypeCatAsCofanIsColimit (X : LightProfinite) [Finite X] :
    IsColimit (fintypeCatAsCofan X) :=
  Cofan.IsColimit.mk _ (fun t => ConcreteCategory.ofHom ⟨fun x => t.inj x PUnit.unit,
    continuous_of_discreteTopology (α := X)⟩) (by aesop)
    (fun _ _ h => by ext x; exact CategoryTheory.congr_fun (h x) _)

variable [PreservesFiniteProducts F]

noncomputable instance (X : FintypeCat.{u}) : PreservesLimitsOfShape (Discrete X) F :=
  let X' := (Countable.toSmall.{0} X).equiv_small.choose
  let e : X ≃ X' := (Countable.toSmall X).equiv_small.choose_spec.some
  have : Finite X' := Finite.of_equiv X e
  preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F

/--
Definition of `isoFinYonedaComponents` / `isoFinYonedaComponents` 的定义

English:
definition isoFinYonedaComponents
  signature: (X : LightProfinite.{u}) [Finite X]
  body: (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u} fun _ => F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩).2

@[simp]

中文:
定义 isoFinYonedaComponents
  签名: (X : LightProfinite.{u}) [Finite X]
  定义体: (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u} fun _ => F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩).2

@[simp]

Depends on / 依赖: Cofan.IsColimit.op, F.obj, IsColimit, LightProfinite, LightProfinite.of, Types.productLimitCone, conePointUniqueUpToIso, fintypeCatAsCofanIsColimit, isLimitFanMkObjOfIsLimit, productLimitCone
-/
def isoFinYonedaComponents (X : LightProfinite.{u}) [Finite X] :
    F.obj ⟨X⟩ ≅ (X -> F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩) :=
  (isLimitFanMkObjOfIsLimit F _ _
    (Cofan.IsColimit.op (fintypeCatAsCofanIsColimit X))).conePointUniqueUpToIso
      (Types.productLimitCone.{u, u} fun _ => F.obj ⟨LightProfinite.of PUnit.{u + 1}⟩).2

@[simp]
/--
lemma `isoFinYonedaComponents_hom` / 引理 `isoFinYonedaComponents_hom`

English:
lemma isoFinYonedaComponents_hom
  given: (X : LightProfinite.{u}) [Finite X]
  proof: rfl

中文:
引理 isoFinYonedaComponents_hom
  条件: (X : LightProfinite.{u}) [Finite X]
  证明: rfl
-/
lemma isoFinYonedaComponents_hom (X : LightProfinite.{u}) [Finite X] :
    (isoFinYonedaComponents F X).hom =
    ↾fun y x => F.map ((LightProfinite.of PUnit.{u + 1}).const x).op y :=
  rfl

/--
lemma `isoFinYonedaComponents_hom_apply` / 引理 `isoFinYonedaComponents_hom_apply`

English:
lemma isoFinYonedaComponents_hom_apply
  statement: (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩)
  proof: rfl

中文:
引理 isoFinYonedaComponents_hom_apply
  结论: (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩)
  证明: rfl

Depends on / 依赖: MyHom.toFun
-/
lemma isoFinYonedaComponents_hom_apply (X : LightProfinite.{u}) [Finite X] (y : F.obj ⟨X⟩)
    (x : X) : (isoFinYonedaComponents F X).hom y x =
      F.map ((LightProfinite.of PUnit.{u + 1}).const x).op y := rfl

/--
lemma `isoFinYonedaComponents_inv_comp` / 引理 `isoFinYonedaComponents_inv_comp`

English:
lemma isoFinYonedaComponents_inv_comp
  statement: {X Y : LightProfinite.{u}} [Finite X] [Finite Y]
  proof: by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_appl

中文:
引理 isoFinYonedaComponents_inv_comp
  结论: {X Y : LightProfinite.{u}} [Finite X] [Finite Y]
  证明: by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_appl

Depends on / 依赖: CompHausLike, CompHausLike.const_comp, Function, Function.comp_apply, Functor, Functor.map_comp_apply, Iso.inv_hom_id_apply, comp_apply, const_comp, injective_of_mono, inv_hom_id_apply, isoFinYonedaComponents, isoFinYonedaComponents_hom_apply, map_comp_apply, op_comp
-/
lemma isoFinYonedaComponents_inv_comp {X Y : LightProfinite.{u}} [Finite X] [Finite Y]
    (f : Y -> F.obj ⟨LightProfinite.of PUnit⟩) (g : X ⟶ Y) :
    (isoFinYonedaComponents F X).inv (f ∘ g) = F.map g.op ((isoFinYonedaComponents F Y).inv f) := by
  apply injective_of_mono (isoFinYonedaComponents F X).hom
  simp only [Iso.inv_hom_id_apply]
  ext x
  rw [isoFinYonedaComponents_hom_apply]
  simp only [← Functor.map_comp_apply, ← op_comp, CompHausLike.const_comp,
    ← isoFinYonedaComponents_hom_apply, Iso.inv_hom_id_apply, Function.comp_apply]

attribute [local simp] toLightProfinite_obj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The restriction of a finite-product-preserving presheaf `F` on `Profinite` to the category of
finite sets is isomorphic to `finYoneda F`.
-/
@[simps! +dsimpLhs]
/--
Definition of `isoFinYoneda` / `isoFinYoneda` 的定义

English:
definition isoFinYoneda
  signature: : toLightProfinite.op ⋙ F ≅ finYoneda F
  body: NatIso.ofComponents (fun X => isoFinYonedaComponents F (toLightProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.ho

中文:
定义 isoFinYoneda
  签名: : toLightProfinite.op ⋙ F ≅ finYoneda F
  定义体: NatIso.ofComponents (fun X => isoFinYonedaComponents F (toLightProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.ho

Depends on / 依赖: CategoryTheory, CategoryTheory.comp_apply, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_map, Functor.map_comp_apply, NatIso, NatIso.ofComponents, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, X.unop, coe_mk, comp_apply, comp_map, comp_obj, finYoneda_obj, hom_ofHom, isoFinYonedaComponents
-/
def isoFinYoneda : toLightProfinite.op ⋙ F ≅ finYoneda F :=
  NatIso.ofComponents (fun X => isoFinYonedaComponents F (toLightProfinite.obj X.unop)) fun _ => by
    simp only [comp_obj, op_obj, finYoneda_obj, Functor.comp_map, op_map]
    ext
    simp only [isoFinYonedaComponents_hom, TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, toLightProfinite_obj,
      ← Functor.map_comp_apply]
    rfl

/--
Definition of `isoLocallyConstantOfIsColimit` / `isoLocallyConstantOfIsColimit` 的定义

English:
definition isoLocallyConstantOfIsColimit
  signature: (hF : forall S : LightProfinite, IsColimit <|
  body: (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

中文:
定义 isoLocallyConstantOfIsColimit
  签名: (hF : 对任意 S : LightProfinite, IsColimit <|
  定义体: (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

Depends on / 依赖: isColimitLocallyConstantPresheafDiagram, isoFinYoneda, lanPresheafExt, lanPresheafNatIso, locallyConstantIsoFinYoneda
-/
def isoLocallyConstantOfIsColimit (hF : forall S : LightProfinite, IsColimit <|
    F.mapCocone (coconeRightOpOfCone S.asLimitCone)) :
      F ≅ (locallyConstantPresheaf
        (F.obj (toLightProfinite.op.obj ⟨of PUnit.{u + 1}⟩))) :=
  (lanPresheafNatIso hF).symm ≪≫
    lanPresheafExt (isoFinYoneda F ≪≫ (locallyConstantIsoFinYoneda F).symm) ≪≫
      lanPresheafNatIso fun _ => isColimitLocallyConstantPresheafDiagram _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isoLocallyConstantOfIsColimit_inv` / 引理 `isoLocallyConstantOfIsColimit_inv`

English:
lemma isoLocallyConstantOfIsColimit_inv
  statement: (X : LightProfinite.{u}ᵒᵖ ⥤ Type u)
  proof: by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [lo

中文:
引理 isoLocallyConstantOfIsColimit_inv
  结论: (X : LightProfinite.{u}ᵒᵖ ⥤ 类型u)
  证明: by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [lo

Depends on / 依赖: Category, Category.assoc, Iso.inv_comp_eq, Opposite, Opposite.unop, X.map, colimit, colimit.hom_ext, counitApp, counitAppApp, functorToPresheaves_obj_obj, hom_ext, inv_comp_eq, isoFinYoneda, isoFinYonedaComponents, isoLocallyConstantOfIsColimit, locallyConstantIsoFinYoneda, locallyConstantPresheaf, naturality, op_obj
-/
lemma isoLocallyConstantOfIsColimit_inv (X : LightProfinite.{u}ᵒᵖ ⥤ Type u)
    [PreservesFiniteProducts X] (hX : forall S : LightProfinite.{u}, (IsColimit <|
      X.mapCocone (coconeRightOpOfCone S.asLimitCone))) :
    (isoLocallyConstantOfIsColimit X hX).inv =
      (CompHausLike.LocallyConstant.counitApp.{u, u} X) := by
  dsimp [isoLocallyConstantOfIsColimit]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  ext S : 2
  apply colimit.hom_ext
  intro ⟨Y, _, g⟩
  suffices _ ≫ (isoFinYonedaComponents _ _).inv ≫ X.map g =
    (locallyConstantPresheaf _).map g ≫ counitAppApp (Opposite.unop S) X by
      simpa [locallyConstantIsoFinYoneda, isoFinYoneda, counitApp]
  erw [(counitApp.{u, u} X).naturality]
  simp only [← Category.assoc, op_obj, functorToPresheaves_obj_obj]
  congr
  ext f
  apply presheaf_ext.{u, u} (X := X) (Y := X) (f := f)
  intro x
  dsimp [toLightProfinite_obj]
  rw [incl_of_counitAppApp]
  simp only [counitAppAppImage]
  have : Finite (fiber.{u, u} f x) :=
    Finite.of_injective (sigmaIncl.{u, u} f x).1 Subtype.val_injective
  apply injective_of_mono (isoFinYonedaComponents X (fiber.{u, u} f x)).hom
  ext y
  simp only [toLightProfinite_obj, isoFinYonedaComponents_hom, TypeCat.hom_ofHom,
    TypeCat.Fun.coe_mk, ← map_comp_apply, ← op_comp]
  rw [show (LightProfinite.of PUnit.{u + 1}).const y ≫
    IsTerminal.from _ (fiber.{u]; rw [u} f x) = 𝟙 _ from rfl]
  simpa [← dsimp% isoFinYonedaComponents_inv_comp X _ (sigmaIncl.{u, u} f x),
    ← isoFinYonedaComponents_hom_apply, -isoFinYonedaComponents_hom] using! x.map_eq_image f y

end LightCondensed
