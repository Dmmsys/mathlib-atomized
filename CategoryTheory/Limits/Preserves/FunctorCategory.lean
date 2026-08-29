/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Preservation of (co)limits in the functor category

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
  for `F : C ⥤ D` preserves colimits.

  The idea of the proof is simply that products and colimits in the functor category are computed
  pointwise, so pointwise preservation implies general preservation.
* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

## References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

@[expose] public section


universe w w' v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

section

variable {C : Type u} [Category.{v₁} C]
variable {D : Type u₂} [Category.{u} D]
variable {E : Type u} [Category.{v₂} E]

/--
lemma `FunctorCategory.prod_preservesColimits` / 引理 `FunctorCategory.prod_preservesColimits`

English:
lemma FunctorCategory.prod_preservesColimits
  statement: [HasBinaryProducts D] [HasColimits D]
  proof: {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let :=
   

中文:
引理 FunctorCategory.prod_preservesColimits
  结论: [HasBinaryProducts D] [HasColimits D]
  证明: {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let :=
   

Depends on / 依赖: Cocone, F.obj, IsColimit, IsColimit.mapCoconeEquiv, NatIso, NatIso.ofComponents, evaluation, evaluationJointlyReflectsColimits, functor, isColimitOfPreserves, mapCocone, mapCoconeEquiv, ofComponents, preserves, preservesColimit, prod.functor.obj, prodComparison, prodComparison_n
-/
lemma FunctorCategory.prod_preservesColimits [HasBinaryProducts D] [HasColimits D]
    [forall X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F) where
  preservesColimitsOfShape {J : Type u} [Category.{u, u} J] :=
    {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let :=
              isColimitOfPreserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply IsColimit.mapCoconeEquiv _ this
            apply (NatIso.ofComponents _ _).symm
            · intro G
              apply asIso (prodComparison ((evaluation C D).obj k) F G)
            · intro G G'
              apply prodComparison_natural ((evaluation C D).obj k) (𝟙 F)⟩ }) }

end

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/--
Instance `whiskeringLeft_preservesLimitsOfShape` / 实例 `whiskeringLeft_preservesLimitsOfShape`

English:
instance whiskeringLeft_preservesLimitsOfShape
  signature: (J : Type u) [Category.{v} J]
  body: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro Y
      change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

中文:
实例 whiskeringLeft_preservesLimitsOfShape
  签名: (J : 类型u) [Category.{v} J]
  定义体: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro Y
      change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

Depends on / 依赖: F.obj, IsLimit, evaluation, evaluationJointlyReflectsLimits, isLimitOfPreserves, mapCone
-/
instance whiskeringLeft_preservesLimitsOfShape (J : Type u) [Category.{v} J]
    [HasLimitsOfShape J D] (F : C ⥤ E) :
    PreservesLimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits
      intro Y
      change IsLimit (((evaluation E D).obj (F.obj Y)).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

/--
Instance `whiskeringLeft_preservesColimitsOfShape` / 实例 `whiskeringLeft_preservesColimitsOfShape`

English:
instance whiskeringLeft_preservesColimitsOfShape
  signature: (J : Type u) [Category.{v} J]
  body: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro Y
      change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

中文:
实例 whiskeringLeft_preservesColimitsOfShape
  签名: (J : 类型u) [Category.{v} J]
  定义体: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro Y
      change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

Depends on / 依赖: F.obj, IsColimit, evaluation, evaluationJointlyReflectsColimits, isColimitOfPreserves, mapCocone
-/
instance whiskeringLeft_preservesColimitsOfShape (J : Type u) [Category.{v} J]
    [HasColimitsOfShape J D] (F : C ⥤ E) :
    PreservesColimitsOfShape J ((whiskeringLeft C E D).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits
      intro Y
      change IsColimit (((evaluation E D).obj (F.obj Y)).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

/--
Instance `whiskeringLeft_preservesLimits` / 实例 `whiskeringLeft_preservesLimits`

English:
instance whiskeringLeft_preservesLimits
  signature: [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E)
  body: ⟨fun {J} _ => whiskeringLeft_preservesLimitsOfShape J F⟩

中文:
实例 whiskeringLeft_preservesLimits
  签名: [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E)
  定义体: ⟨fun {J} _ => whiskeringLeft_preservesLimitsOfShape J F⟩

Depends on / 依赖: whiskeringLeft_preservesLimitsOfShape
-/
instance whiskeringLeft_preservesLimits [HasLimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesLimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesLimitsOfShape J F⟩

/--
Instance `whiskeringLeft_preservesColimit` / 实例 `whiskeringLeft_preservesColimit`

English:
instance whiskeringLeft_preservesColimit
  signature: [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E)
  body: ⟨fun {J} _ => whiskeringLeft_preservesColimitsOfShape J F⟩

中文:
实例 whiskeringLeft_preservesColimit
  签名: [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E)
  定义体: ⟨fun {J} _ => whiskeringLeft_preservesColimitsOfShape J F⟩

Depends on / 依赖: whiskeringLeft_preservesColimitsOfShape
-/
instance whiskeringLeft_preservesColimit [HasColimitsOfSize.{w, w'} D] (F : C ⥤ E) :
    PreservesColimitsOfSize.{w, w'} ((whiskeringLeft C E D).obj F) :=
  ⟨fun {J} _ => whiskeringLeft_preservesColimitsOfShape J F⟩

instance (F : C ⥤ D) [HasFiniteLimits E] :
    PreservesFiniteLimits ((Functor.whiskeringLeft C D E).obj F) where
  preservesFiniteLimits _ _ _ := inferInstance

instance (F : C ⥤ D) [HasFiniteColimits E] :
    PreservesFiniteColimits ((Functor.whiskeringLeft C D E).obj F) where
  preservesFiniteColimits _ _ _ := inferInstance

/--
Instance `whiskeringRight_preservesLimitsOfShape` / 实例 `whiskeringRight_preservesLimitsOfShape`

English:
instance whiskeringRight_preservesLimitsOfShape
  signature: {C : Type*} [Category* C] {D : Type*}
  body: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

中文:
实例 whiskeringRight_preservesLimitsOfShape
  签名: {C : 类型} [Category* C] {D : 类型}
  定义体: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

Depends on / 依赖: IsLimit, evaluation, evaluationJointlyReflectsLimits, isLimitOfPreserves, mapCone
-/
instance whiskeringRight_preservesLimitsOfShape {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsLimits _ (fun k => ?_)
      change IsLimit (((evaluation _ _).obj k ⋙ F).mapCone c)
      exact isLimitOfPreserves _ hc⟩⟩⟩

instance {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [F.ReflectsIsomorphisms] [PreservesLimitsOfShape J F] :
    ReflectsLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

instance {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J E] (F : D ⥤ E) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} => ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsLimits _ (fun k => ?_)
    apply isLimitOfReflects F
    exact isLimitOfPreserves ((evaluation C E).obj k) hc⟩⟩⟩

/--
Definition of `limitCompWhiskeringRightIsoLimitComp` / `limitCompWhiskeringRightIsoLimitComp` 的定义

English:
definition limitCompWhiskeringRightIsoLimitComp
  signature: {C : Type*} [Category* C] {D : Type*}
  body: (preservesLimitIso _ _).symm

中文:
定义 limitCompWhiskeringRightIsoLimitComp
  签名: {C : 类型} [Category* C] {D : 类型}
  定义体: (preservesLimitIso _ _).symm

Depends on / 依赖: preservesLimitIso
-/
def limitCompWhiskeringRightIsoLimitComp {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    limit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ limit G ⋙ F :=
  (preservesLimitIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limitCompWhiskeringRightIsoLimitComp_inv_π` / 定理 `limitCompWhiskeringRightIsoLimitComp_inv_π`

English:
theorem limitCompWhiskeringRightIsoLimitComp_inv_π
  statement: {C : Type*} [Category* C] {D : Type*}
  proof: by
  simp [limitCompWhiskeringRightIsoLimitComp]

中文:
定理 limitCompWhiskeringRightIsoLimitComp_inv_π
  结论: {C : 类型} [Category* C] {D : 类型}
  证明: by
  simp [limitCompWhiskeringRightIsoLimitComp]

Depends on / 依赖: limitCompWhiskeringRightIsoLimitComp
-/
theorem limitCompWhiskeringRightIsoLimitComp_inv_π {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).inv ≫
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j = whiskerRight (limit.π G j) F := by
  simp [limitCompWhiskeringRightIsoLimitComp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π` / 定理 `limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π`

English:
theorem limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π
  proof: by
  simp [← Iso.eq_inv_comp]

中文:
定理 limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π
  证明: by
  simp [← Iso.eq_inv_comp]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp
-/
theorem limitCompWhiskeringRightIsoLimitComp_hom_whiskerRight_π
    {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    (limitCompWhiskeringRightIsoLimitComp F G).hom ≫ whiskerRight (limit.π G j) F =
      limit.π (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [← Iso.eq_inv_comp]

/--
Instance `whiskeringRight_preservesColimitsOfShape` / 实例 `whiskeringRight_preservesColimitsOfShape`

English:
instance whiskeringRight_preservesColimitsOfShape
  signature: {C : Type*} [Category* C] {D : Type*}
  body: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun k => ?_)
      change IsColimit (((evaluation _ _).obj k ⋙ F).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

中文:
实例 whiskeringRight_preservesColimitsOfShape
  签名: {C : 类型} [Category* C] {D : 类型}
  定义体: ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun k => ?_)
      change IsColimit (((evaluation _ _).obj k ⋙ F).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

Depends on / 依赖: IsColimit, evaluation, evaluationJointlyReflectsColimits, isColimitOfPreserves, mapCocone
-/
instance whiskeringRight_preservesColimitsOfShape {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J ((whiskeringRight C D E).obj F) :=
  ⟨fun {K} =>
    ⟨fun c {hc} => ⟨by
      apply evaluationJointlyReflectsColimits _ (fun k => ?_)
      change IsColimit (((evaluation _ _).obj k ⋙ F).mapCocone c)
      exact isColimitOfPreserves _ hc⟩⟩⟩

/--
Definition of `colimitCompWhiskeringRightIsoColimitComp` / `colimitCompWhiskeringRightIsoColimitComp` 的定义

English:
definition colimitCompWhiskeringRightIsoColimitComp
  signature: {C : Type*} [Category* C] {D : Type*}
  body: (preservesColimitIso _ _).symm

中文:
定义 colimitCompWhiskeringRightIsoColimitComp
  签名: {C : 类型} [Category* C] {D : 类型}
  定义体: (preservesColimitIso _ _).symm

Depends on / 依赖: preservesColimitIso
-/
def colimitCompWhiskeringRightIsoColimitComp {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    colimit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ colimit G ⋙ F :=
  (preservesColimitIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_colimitCompWhiskeringRightIsoColimitComp_hom` / 定理 `ι_colimitCompWhiskeringRightIsoColimitComp_hom`

English:
theorem ι_colimitCompWhiskeringRightIsoColimitComp_hom
  statement: {C : Type*} [Category* C] {D : Type*}
  proof: by
  simp [colimitCompWhiskeringRightIsoColimitComp]

中文:
定理 ι_colimitCompWhiskeringRightIsoColimitComp_hom
  结论: {C : 类型} [Category* C] {D : 类型}
  证明: by
  simp [colimitCompWhiskeringRightIsoColimitComp]

Depends on / 依赖: colimitCompWhiskeringRightIsoColimitComp
-/
theorem ι_colimitCompWhiskeringRightIsoColimitComp_hom {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j ≫
      (colimitCompWhiskeringRightIsoColimitComp F G).hom = whiskerRight (colimit.ι G j) F := by
  simp [colimitCompWhiskeringRightIsoColimitComp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv` / 定理 `whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv`

English:
theorem whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv
  statement: {C : Type*} [Category* C]
  proof: by
  simp [Iso.comp_inv_eq]

中文:
定理 whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv
  结论: {C : 类型} [Category* C]
  证明: by
  simp [Iso.comp_inv_eq]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem whiskerRight_ι_colimitCompWhiskeringRightIsoColimitComp_inv {C : Type*} [Category* C]
    {D : Type*} [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasColimitsOfShape J D] (F : D ⥤ E) [PreservesColimitsOfShape J F] (G : J ⥤ C ⥤ D) (j : J) :
    whiskerRight (colimit.ι G j) F ≫ (colimitCompWhiskeringRightIsoColimitComp F G).inv =
      colimit.ι (G ⋙ (whiskeringRight _ _ _).obj F) j := by
  simp [Iso.comp_inv_eq]

/--
Instance `whiskeringRightPreservesLimits` / 实例 `whiskeringRightPreservesLimits`

English:
instance whiskeringRightPreservesLimits
  signature: {C : Type*} [Category* C] {D : Type*} [Category* D]
  body: ⟨inferInstance⟩

中文:
实例 whiskeringRightPreservesLimits
  签名: {C : 类型} [Category* C] {D : 类型} [Category* D]
  定义体: ⟨inferInstance⟩
-/
instance whiskeringRightPreservesLimits {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : D ⥤ E) [HasLimitsOfSize.{w, w'} D]
    [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩

/--
Instance `whiskeringRightPreservesColimits` / 实例 `whiskeringRightPreservesColimits`

English:
instance whiskeringRightPreservesColimits
  signature: {C : Type*} [Category* C] {D : Type*} [Category* D]
  body: ⟨inferInstance⟩

中文:
实例 whiskeringRightPreservesColimits
  签名: {C : 类型} [Category* C] {D : 类型} [Category* D]
  定义体: ⟨inferInstance⟩
-/
instance whiskeringRightPreservesColimits {C : Type*} [Category* C] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (F : D ⥤ E) [HasColimitsOfSize.{w, w'} D]
    [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} ((whiskeringRight C D E).obj F) :=
  ⟨inferInstance⟩

/--
lemma `preservesLimit_of_lan_preservesLimit` / 引理 `preservesLimit_of_lan_preservesLimit`

English:
lemma preservesLimit_of_lan_preservesLimit
  statement: {C D : Type u} [SmallCategory C]
  proof: letI := preservesLimitsOfShape_of_natIso (J := J)
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm
  preservesLimitsOfShape_of_reflects_of_preserves F uliftYoneda.{u}

中文:
引理 preservesLimit_of_lan_preservesLimit
  结论: {C D : 类型u} [SmallCategory C]
  证明: letI := preservesLimitsOfShape_of_natIso (J := J)
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm
  preservesLimitsOfShape_of_reflects_of_preserves F uliftYoneda.{u}

Depends on / 依赖: Presheaf, Presheaf.compULiftYonedaIsoULiftYonedaCompLan, compULiftYonedaIsoULiftYonedaCompLan, preservesLimitsOfShape_of_natIso, preservesLimitsOfShape_of_reflects_of_preserves, uliftYoneda
-/
lemma preservesLimit_of_lan_preservesLimit {C D : Type u} [SmallCategory C]
    [SmallCategory D] (F : C ⥤ D) (J : Type u) [SmallCategory J]
    [PreservesLimitsOfShape J (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u)] : PreservesLimitsOfShape J F :=
  letI := preservesLimitsOfShape_of_natIso (J := J)
    (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u} F).symm
  preservesLimitsOfShape_of_reflects_of_preserves F uliftYoneda.{u}

/--
lemma `preservesFiniteLimits_of_evaluation` / 引理 `preservesFiniteLimits_of_evaluation`

English:
lemma preservesFiniteLimits_of_evaluation
  statement: {D : Type*} [Category* D] {E : Type*} [Category* E]
  proof: ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteLimits _⟩

中文:
引理 preservesFiniteLimits_of_evaluation
  结论: {D : 类型} [Category* D] {E : 类型} [Category* E]
  证明: ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteLimits _⟩

Depends on / 依赖: preservesFiniteLimits, preservesLimitsOfShape_of_evaluation
-/
lemma preservesFiniteLimits_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : C ⥤ D ⥤ E) (h : forall d : D, PreservesFiniteLimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteLimits F :=
  ⟨fun J _ _ => preservesLimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteLimits _⟩

/--
lemma `preservesFiniteColimits_of_evaluation` / 引理 `preservesFiniteColimits_of_evaluation`

English:
lemma preservesFiniteColimits_of_evaluation
  statement: {D : Type*} [Category* D] {E : Type*} [Category* E]
  proof: ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteColimits _⟩

中文:
引理 preservesFiniteColimits_of_evaluation
  结论: {D : 类型} [Category* D] {E : 类型} [Category* E]
  证明: ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteColimits _⟩

Depends on / 依赖: preservesColimitsOfShape_of_evaluation, preservesFiniteColimits
-/
lemma preservesFiniteColimits_of_evaluation {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : C ⥤ D ⥤ E) (h : forall d : D, PreservesFiniteColimits (F ⋙ (evaluation D E).obj d)) :
    PreservesFiniteColimits F :=
  ⟨fun J _ _ => preservesColimitsOfShape_of_evaluation F J fun k => (h k).preservesFiniteColimits _⟩

end

section

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable {D : Type u₃} [Category.{v₃} D]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape J (colim : (K ⥤ D ⥤ C) ⥤ _)
  body: preservesLimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (colim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        colimit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (colimitObjIsoColimitCompEvaluation _ _) ≪≫
          (by exact

中文:
实例 :
  签名: PreservesLimitsOfShape J (colim : (K ⥤ D ⥤ C) ⥤ _)
  定义体: preservesLimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (colim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        colimit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (colimitObjIsoColimitCompEvaluation _ _) ≪≫
          (by exact

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, Iso.refl, NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app_assoc, colimit, colimitFlipIsoCompCol, colimitObjIsoColimitCompEvaluation, colimit_obj_ext, comp_app_assoc, evaluation, isoOfNatIso, ofComponents, preservesLimitsOfShape_of_evaluation, preservesLimitsOfShape_of_natIso, whiskeringRight
-/
noncomputable instance : PreservesLimitsOfShape J (colim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesLimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (colim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        colimit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (colimitObjIsoColimitCompEvaluation _ _) ≪≫
          (by exact HasColimit.isoOfNatIso (Iso.refl _)) ≪≫
          (colimitObjIsoColimitCompEvaluation _ _).symm)
        (fun {F G} η => colimit_obj_ext (fun j => by simp [← NatTrans.comp_app_assoc]))
    preservesLimitsOfShape_of_natIso (i ≪≫ colimitFlipIsoCompColim _).symm)

end

section

variable [HasColimitsOfShape J C] [HasLimitsOfShape K C]
variable [PreservesColimitsOfShape J (lim : (K ⥤ C) ⥤ _)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (lim : (K ⥤ D ⥤ C) ⥤ _)
  body: preservesColimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (lim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        limit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (limitObjIsoLimitCompEvaluation _ _) ≪≫
          (by exact HasLi

中文:
实例 :
  签名: PreservesColimitsOfShape J (lim : (K ⥤ D ⥤ C) ⥤ _)
  定义体: preservesColimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (lim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        limit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (limitObjIsoLimitCompEvaluation _ _) ≪≫
          (by exact HasLi

Depends on / 依赖: HasLimit, HasLimit.isoOfNatIso, Iso.refl, NatIso, NatIso.ofComponents, NatTrans, NatTrans.comp_app, comp_app, evaluation, isoOfNatIso, limitFlipIsoCompLim, limitObjIsoLimitCompEvaluation, limit_obj_ext, ofComponents, preservesColimitsOfShape_of_evaluation, preservesColimitsOfShape_of_natIso, whiskeringRight
-/
noncomputable instance : PreservesColimitsOfShape J (lim : (K ⥤ D ⥤ C) ⥤ _) :=
  preservesColimitsOfShape_of_evaluation _ _ (fun d =>
    let i : (lim : (K ⥤ D ⥤ C) ⥤ _) ⋙ (evaluation D C).obj d ≅
        limit ((whiskeringRight K (D ⥤ C) C).obj ((evaluation D C).obj d)).flip :=
      NatIso.ofComponents (fun X => (limitObjIsoLimitCompEvaluation _ _) ≪≫
          (by exact HasLimit.isoOfNatIso (Iso.refl _)) ≪≫
          (limitObjIsoLimitCompEvaluation _ _).symm)
        (fun {F G} η => limit_obj_ext (fun j => by simp [← NatTrans.comp_app]))
    preservesColimitsOfShape_of_natIso (i ≪≫ limitFlipIsoCompLim _).symm)

end

end

end CategoryTheory
