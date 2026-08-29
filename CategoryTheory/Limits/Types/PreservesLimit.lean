/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Presheaves of types which preserves a limit

Let `F : J ⥤ Cᵒᵖ` be a functor. We show that a presheaf `P : Cᵒᵖ ⥤ Type w`
preserves the limit of `F` iff `P` is a local object with respect to a suitable
family of morphisms in `Cᵒᵖ ⥤ Type w` (this family contains `1` or `0` morphism
depending on whether the limit of `F` exists or not).

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

section

variable {C : Type u} [Category.{v} C]
  {J : Type u'} [Category.{v'} J] [LocallySmall.{w} C]
  {F : J ⥤ Cᵒᵖ} (c : Cone F) {c' : Cocone (F.leftOp ⋙ shrinkYoneda.{w})}
  (hc : IsLimit c) (hc' : IsColimit c') (P : Cᵒᵖ ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P} in
/-- Let `F : J ⥤ Cᵒᵖ` be a functor, `c'` a colimit cocone for `F.leftOp ⋙ shrinkYoneda.{w}`.
For any `P : Cᵒᵖ ⥤ Type w`, this is the bijection between `c'.pt ⟶ P` and the type
of sections of `F ⋙ P`. -/
@[simps -isSimp symm_apply apply_coe]
/--
Definition of `coconeCompShrinkYonedaHomEquiv` / `coconeCompShrinkYonedaHomEquiv` 的定义

English:
definition coconeCompShrinkYonedaHomEquiv
  signature: :
  body: { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        dsimp
        rw [← dsimp% c'.w g.op]; rw [Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        apply map_shrinkYonedaEquiv }
  invFun s := hc'.

中文:
定义 coconeCompShrinkYonedaHomEquiv
  签名: :
  定义体: { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        dsimp
        rw [← dsimp% c'.w g.op]; rw [Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        apply map_shrinkYonedaEquiv }
  invFun s := hc'.

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cocone, Cocone.mk, cat_disch, comp_id, conv_rhs, f.unop, g.op, hom_ext, invFun, j.unop, left_inv, map_shrinkYonedaEquiv, naturality, property, right_inv, s.property, s.val
-/
noncomputable def coconeCompShrinkYonedaHomEquiv :
    (c'.pt ⟶ P) ≃ (F ⋙ P).sections where
  toFun f :=
    { val j := shrinkYonedaEquiv (c'.ι.app (op j) ≫ f)
      property {X X'} g := by
        dsimp
        rw [← dsimp% c'.w g.op]; rw [Category.assoc]
        conv_rhs => rw [shrinkYonedaEquiv_comp]
        rw [shrinkYonedaEquiv_shrinkYoneda_map]
        apply map_shrinkYonedaEquiv }
  invFun s := hc'.desc (Cocone.mk _
    { app j := shrinkYonedaEquiv.symm (s.val j.unop)
      naturality j₁ j₂ f := by
        rw [← s.property f.unop]
        dsimp
        rw [shrinkYonedaEquiv_symm_map]; rw [Category.comp_id] })
  left_inv f := hc'.hom_ext (by simp)
  right_inv u := by cat_disch

/--
Definition of `coconePtToShrinkYoneda` / `coconePtToShrinkYoneda` 的定义

English:
definition coconePtToShrinkYoneda
  signature: :
  body: hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

中文:
定义 coconePtToShrinkYoneda
  签名: :
  定义体: hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

Depends on / 依赖: coconeLeftOpOfCone, mapCocone, shrinkYoneda
-/
noncomputable def coconePtToShrinkYoneda :
    c'.pt ⟶ shrinkYoneda.{w}.obj c.pt.unop :=
  hc'.desc (shrinkYoneda.{w}.mapCocone (coconeLeftOpOfCone c))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {P} in
@[reassoc]
/--
lemma `coconePtToShrinkYoneda_comp` / 引理 `coconePtToShrinkYoneda_comp`

English:
lemma coconePtToShrinkYoneda_comp
  given: (x : P.obj c.pt)
  proof: by
  refine hc'.hom_ext (fun _ => ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc]; rw [hc'.fac]
  exact (shrinkYonedaEquiv_symm_map _ _).symm

中文:
引理 coconePtToShrinkYoneda_comp
  条件: (x : P.obj c.pt)
  证明: by
  refine hc'.hom_ext (fun _ => ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc]; rw [hc'.fac]
  exact (shrinkYonedaEquiv_symm_map _ _).symm

Depends on / 依赖: coconeCompShrinkYonedaHomEquiv_symm_apply, coconePtToShrinkYoneda, fac_assoc, hom_ext, shrinkYonedaEquiv_symm_map
-/
lemma coconePtToShrinkYoneda_comp (x : P.obj c.pt) :
    coconePtToShrinkYoneda c hc' ≫ shrinkYonedaEquiv.symm x =
      (coconeCompShrinkYonedaHomEquiv hc').symm
        (Types.sectionOfCone (P.mapCone c) x) := by
  refine hc'.hom_ext (fun _ => ?_)
  dsimp [coconePtToShrinkYoneda, coconeCompShrinkYonedaHomEquiv_symm_apply]
  rw [hc'.fac_assoc]; rw [hc'.fac]
  exact (shrinkYonedaEquiv_symm_map _ _).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `nonempty_isLimit_mapCone_iff` / 引理 `nonempty_isLimit_mapCone_iff`

English:
lemma nonempty_isLimit_mapCone_iff
  proof: by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [MorphismProperty.isLocal_single_iff_bijective]; rw [← Function.Bijective.of_comp_iff' (coconeCompShrinkYonedaHomEquiv hc').symm.bijective]; rw [← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1

中文:
引理 nonempty_isLimit_mapCone_iff
  证明: by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [MorphismProperty.isLocal_single_iff_bijective]; rw [← Function.Bijective.of_comp_iff' (coconeCompShrinkYonedaHomEquiv hc').symm.bijective]; rw [← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1

Depends on / 依赖: Bijective, Function, Function.Bijective.of_comp_iff, Iff.rfl, MorphismProperty, MorphismProperty.isLocal_single_iff_bijective, Types.isLimit_iff_bijective_sectionOfCone, bijective, coconeCompShrinkYonedaHomEquiv, coconePtToShrinkYoneda_comp, convert, isLimit_iff_bijective_sectionOfCone, isLocal_single_iff_bijective, of_comp_iff, shrinkYonedaEquiv, shrinkYonedaEquiv.bijective, symm.bijective
-/
lemma nonempty_isLimit_mapCone_iff :
    Nonempty (IsLimit (P.mapCone c)) ↔
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal P := by
  rw [Types.isLimit_iff_bijective_sectionOfCone]; rw [MorphismProperty.isLocal_single_iff_bijective]; rw [← Function.Bijective.of_comp_iff' (coconeCompShrinkYonedaHomEquiv hc').symm.bijective]; rw [← Function.Bijective.of_comp_iff _ shrinkYonedaEquiv.bijective]
  convert Iff.rfl using 2
  ext : 1
  simp [← coconePtToShrinkYoneda_comp]

variable {c}

include hc in
/--
lemma `preservesLimit_eq_isLocal_single` / 引理 `preservesLimit_eq_isLocal_single`

English:
lemma preservesLimit_eq_isLocal_single
  proof: by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ => ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ => preservesLimit_of_preserves_limit_cone hc h⟩

中文:
引理 preservesLimit_eq_isLocal_single
  证明: by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ => ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ => preservesLimit_of_preserves_limit_cone hc h⟩

Depends on / 依赖: isLimitOfPreserves, nonempty_isLimit_mapCone_iff, preservesLimit_of_preserves_limit_cone
-/
lemma preservesLimit_eq_isLocal_single :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.single (coconePtToShrinkYoneda c hc')).isLocal := by
  ext P
  rw [← nonempty_isLimit_mapCone_iff c hc' P]
  exact ⟨fun _ => ⟨isLimitOfPreserves P hc⟩,
    fun ⟨h⟩ => preservesLimit_of_preserves_limit_cone hc h⟩

variable (F) [Small.{w} J]

/--
Definition of `preservesLimitHomFamilySrc` / `preservesLimitHomFamilySrc` 的定义

English:
abbreviation preservesLimitHomFamilySrc
  body: colimit (F.leftOp ⋙ shrinkYoneda)

中文:
缩写 preservesLimitHomFamilySrc
  定义体: colimit (F.leftOp ⋙ shrinkYoneda)

Depends on / 依赖: F.leftOp, colimit, leftOp, shrinkYoneda
-/
noncomputable abbrev preservesLimitHomFamilySrc :=
  colimit (F.leftOp ⋙ shrinkYoneda)

/--
Definition of `preservesLimitHomFamilyTgt` / `preservesLimitHomFamilyTgt` 的定义

English:
abbreviation preservesLimitHomFamilyTgt
  signature: (h : PLift (HasLimit F))
  body: letI := h.down
  shrinkYoneda.obj (limit F).unop

中文:
缩写 preservesLimitHomFamilyTgt
  签名: (h : 命题层提升 (有极限 F))
  定义体: letI := h.down
  shrinkYoneda.obj (limit F).unop

Depends on / 依赖: h.down, shrinkYoneda, shrinkYoneda.obj
-/
noncomputable abbrev preservesLimitHomFamilyTgt (h : PLift (HasLimit F)) :=
  letI := h.down
  shrinkYoneda.obj (limit F).unop

/--
Definition of `preservesLimitHomFamily` / `preservesLimitHomFamily` 的定义

English:
abbreviation preservesLimitHomFamily
  signature: (h : PLift (HasLimit F))
  body: letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)

中文:
缩写 preservesLimitHomFamily
  签名: (h : 命题层提升 (有极限 F))
  定义体: letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)

Depends on / 依赖: coconePtToShrinkYoneda, colimit, colimit.isColimit, h.down, isColimit, limit.cone
-/
noncomputable abbrev preservesLimitHomFamily (h : PLift (HasLimit F)) :
    preservesLimitHomFamilySrc F ⟶ preservesLimitHomFamilyTgt F h :=
  letI := h.down
  coconePtToShrinkYoneda (limit.cone F) (colimit.isColimit _)

/--
lemma `preservesLimit_eq_isLocal` / 引理 `preservesLimit_eq_isLocal`

English:
lemma preservesLimit_eq_isLocal
  proof: by
  ext
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext
    exact ⟨fun ⟨_⟩ => ⟨⟨⟩⟩, fun ⟨_⟩ => ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ => (hF h.down).elim,
      fun _ => ⟨fun hc => (hF ⟨_, hc⟩).elim⟩⟩

中文:
引理 preservesLimit_eq_isLocal
  证明: by
  ext
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext
    exact ⟨fun ⟨_⟩ => ⟨⟨⟩⟩, fun ⟨_⟩ => ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ => (hF h.down).elim,
      fun _ => ⟨fun hc => (hF ⟨_, hc⟩).elim⟩⟩

Depends on / 依赖: HasLimit, Iff.rfl, colimit, colimit.isColimit, convert, h.down, isColimit, isLimit, limit.isLimit, preservesLimit_eq_isLocal_single
-/
lemma preservesLimit_eq_isLocal :
    ObjectProperty.preservesLimit F =
      (MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  ext
  by_cases hF : HasLimit F
  · rw [preservesLimit_eq_isLocal_single (limit.isLimit F) (colimit.isColimit _)]
    convert Iff.rfl
    ext
    exact ⟨fun ⟨_⟩ => ⟨⟨⟩⟩, fun ⟨_⟩ => ⟨⟨hF⟩⟩⟩
  · exact ⟨fun _ _ _ _ ⟨h⟩ => (hF h.down).elim,
      fun _ => ⟨fun hc => (hF ⟨_, hc⟩).elim⟩⟩

/--
lemma `preservesLimitsOfShape_eq_isLocal` / 引理 `preservesLimitsOfShape_eq_isLocal`

English:
lemma preservesLimitsOfShape_eq_isLocal
  proof: by
  simp only [ObjectProperty.preservesLimitsOfShape_eq_iSup,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

中文:
引理 preservesLimitsOfShape_eq_isLocal
  证明: by
  simp only [ObjectProperty.preservesLimitsOfShape_eq_iSup,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

Depends on / 依赖: MorphismProperty, MorphismProperty.isLocal_iSup, ObjectProperty, ObjectProperty.preservesLimitsOfShape_eq_iSup, isLocal_iSup, preservesLimit_eq_isLocal, preservesLimitsOfShape_eq_iSup
-/
lemma preservesLimitsOfShape_eq_isLocal :
    ObjectProperty.preservesLimitsOfShape J =
      (⨆ (F : J ⥤ Cᵒᵖ), MorphismProperty.ofHoms (preservesLimitHomFamily F)).isLocal := by
  simp only [ObjectProperty.preservesLimitsOfShape_eq_iSup,
    MorphismProperty.isLocal_iSup, preservesLimit_eq_isLocal]

end

end Presheaf

end CategoryTheory
