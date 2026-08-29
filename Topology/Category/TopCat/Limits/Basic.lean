/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison, Mario Carneiro, Andrew Yang
-/
module

public import Mathlib.Topology.Category.TopCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The category of topological spaces has all limits and colimits

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

@[expose] public section


open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

universe v u u' w

noncomputable section

local notation "forget" => forget TopCat

namespace TopCat

section Limits

variable {J : Type v} [Category.{w} J]

attribute [local fun_prop] continuous_subtype_val
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: (F : J ⥤ TopCat.{max v u})
  body: TopCat.of { u : forall j : J, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (cont

中文:
定义 limitCone
  签名: (F : J ⥤ TopCat.{max v u})
  定义体: TopCat.of { u : forall j : J, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (cont

Depends on / 依赖: F.map, F.obj, TopCat, TopCat.of
-/
def limitCone (F : J ⥤ TopCat.{max v u}) : Cone F where
  pt := TopCat.of { u : forall j : J, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j }
  π :=
    { app := fun j => ofHom
        { toFun := fun u => u.val j
          -- Porting note: `continuity` from the original mathlib3 proof failed here.
          continuous_toFun := Continuous.comp (continuous_apply _) (continuous_subtype_val) }
      naturality := fun X Y f => by
        ext a
        exact (a.2 f).symm }

/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: (F : J ⥤ TopCat.{max v u})
  body: ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
 

中文:
定义 limitConeIsLimit
  签名: (F : J ⥤ TopCat.{max v u})
  定义体: ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
 
-/
def limitConeIsLimit (F : J ⥤ TopCat.{max v u}) : IsLimit (limitCone.{v, u} F) where
  lift S := ofHom
    { toFun := fun x =>
        ⟨fun _ => S.π.app _ x, fun f => by
          dsimp
          rw [← S.w f]
          rfl⟩
      continuous_toFun :=
        Continuous.subtype_mk (continuous_pi fun j => (S.π.app j).hom.2) fun x i j f => by
          dsimp
          rw [← S.w f]
          rfl }
  uniq S m h := by
    ext a
    simp [← h]
    rfl

section

variable {F : J ⥤ TopCat.{u}} (c : Cone (F ⋙ forget))

/--
Definition of `conePtOfConeForget` / `conePtOfConeForget` 的定义

English:
definition conePtOfConeForget
  signature: : Type _
  body: c.pt

中文:
定义 conePtOfConeForget
  签名: : Type _
  定义体: c.pt

Depends on / 依赖: c.pt
-/
def conePtOfConeForget : Type _ := c.pt

/--
Instance `topologicalSpaceConePtOfConeForget` / 实例 `topologicalSpaceConePtOfConeForget`

English:
instance topologicalSpaceConePtOfConeForget
  signature: :
  body: (⨅ j, (F.obj j).str.induced (c.π.app j))

中文:
实例 topologicalSpaceConePtOfConeForget
  签名: :
  定义体: (⨅ j, (F.obj j).str.induced (c.π.app j))

Depends on / 依赖: F.obj, induced, str.induced
-/
instance topologicalSpaceConePtOfConeForget :
    TopologicalSpace (conePtOfConeForget c) :=
  (⨅ j, (F.obj j).str.induced (c.π.app j))

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cone `c : Cone (F ⋙ forget)`
of the underlying functor to types, this is a cone for `F` whose point is
`c.pt` with the infimum of the induced topologies by the maps `c.π.app j`. -/
@[simps pt π_app]
/--
Definition of `coneOfConeForget` / `coneOfConeForget` 的定义

English:
definition coneOfConeForget
  signature: : Cone F where
  body: of (conePtOfConeForget c)
  π :=
    { app j := ofHom (ContinuousMap.mk (c.π.app j) (by
        rw [continuous_iff_le_induced]
        exact iInf_le _ _ ))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.π.naturality φ) }

中文:
定义 coneOfConeForget
  签名: : Cone F where
  定义体: of (conePtOfConeForget c)
  π :=
    { app j := ofHom (ContinuousMap.mk (c.π.app j) (by
        rw [continuous_iff_le_induced]
        exact iInf_le _ _ ))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.π.naturality φ) }

Depends on / 依赖: conePtOfConeForget
-/
def coneOfConeForget : Cone F where
  pt := of (conePtOfConeForget c)
  π :=
    { app j := ofHom (ContinuousMap.mk (c.π.app j) (by
        rw [continuous_iff_le_induced]
        exact iInf_le _ _ ))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.π.naturality φ) }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitConeOfForget` / `isLimitConeOfForget` 的定义

English:
definition isLimitConeOfForget
  signature: (c : Cone (F ⋙ forget)) (hc : IsLimit c)
  body: by
  refine IsLimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.lift ((forget).mapCone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_coinduced_le]
  dsimp [topologicalSpaceConePtOfConeForget]
  rw [le_iInf_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced_compo

中文:
定义 isLimitConeOfForget
  签名: (c : Cone (F ⋙ forget)) (hc : IsLimit c)
  定义体: by
  refine IsLimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.lift ((forget).mapCone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_coinduced_le]
  dsimp [topologicalSpaceConePtOfConeForget]
  rw [le_iInf_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced_compo

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext_iff.mp, ContinuousMap, ContinuousMap.mk, IsLimit, IsLimit.ofFaithful, coinduced_le_iff_le_induced, continuous, continuous_iff_coinduced_le, continuous_iff_le_induced, convert, forget, hc.fac, hc.lift, hom.continuous, hom_ext_iff, induced_compose, le_iInf_iff, mapCone, ofFaithful
-/
def isLimitConeOfForget (c : Cone (F ⋙ forget)) (hc : IsLimit c) :
    IsLimit (coneOfConeForget c) := by
  refine IsLimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.lift ((forget).mapCone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_coinduced_le]
  dsimp [topologicalSpaceConePtOfConeForget]
  rw [le_iInf_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced_compose]
  convert! continuous_iff_le_induced.1 (s.π.app j).hom.continuous
  ext x
  exact ConcreteCategory.hom_ext_iff.mp (hc.fac ((forget).mapCone s) j) x

end

section IsLimit

variable {F : J ⥤ TopCat.{u}} (c : Cone F) (hc : IsLimit c)

include hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `induced_of_isLimit` / 定理 `induced_of_isLimit`

English:
theorem induced_of_isLimit
  proof: by
  let c' := coneOfConeForget ((forget).mapCone c)
  let hc' : IsLimit c' := isLimitConeOfForget _ (isLimitOfPreserves forget hc)
  let e := IsLimit.conePointUniqueUpToIso hc' hc
  have he (j : J) : e.inv ≫ c'.π.app j = c.π.app j :=
    IsLimit.conePointUniqueUpToIso_inv_comp hc' hc j
  apply (hom

中文:
定理 induced_of_isLimit
  证明: by
  let c' := coneOfConeForget ((forget).mapCone c)
  let hc' : IsLimit c' := isLimitConeOfForget _ (isLimitOfPreserves forget hc)
  let e := IsLimit.conePointUniqueUpToIso hc' hc
  have he (j : J) : e.inv ≫ c'.π.app j = c.π.app j :=
    IsLimit.conePointUniqueUpToIso_inv_comp hc' hc j
  apply (hom

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.conePointUniqueUpToIso_inv_comp, coneOfConeForget, coneOfConeForget_pt, conePointUniqueUpToIso, conePointUniqueUpToIso_inv_comp, conv_rhs, e.inv, e.symm, forget, homeoOfIso, induced_compose, induced_eq, induced_eq.symm.trans, isLimitConeOfForget, isLimitOfPreserves, mapCone, topologicalSpaceConePtOfConeForget
-/
theorem induced_of_isLimit :
    c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  let c' := coneOfConeForget ((forget).mapCone c)
  let hc' : IsLimit c' := isLimitConeOfForget _ (isLimitOfPreserves forget hc)
  let e := IsLimit.conePointUniqueUpToIso hc' hc
  have he (j : J) : e.inv ≫ c'.π.app j = c.π.app j :=
    IsLimit.conePointUniqueUpToIso_inv_comp hc' hc j
  apply (homeoOfIso e.symm).induced_eq.symm.trans
  dsimp [coneOfConeForget_pt, c', topologicalSpaceConePtOfConeForget]
  conv_rhs => simp only [← he]
  simp [← induced_compose, homeoOfIso, c']

end IsLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `nonempty_isLimit_iff_eq_induced` / 引理 `nonempty_isLimit_iff_eq_induced`

English:
lemma nonempty_isLimit_iff_eq_induced
  statement: {F : J ⥤ TopCat.{u}} (c : Cone F)
  proof: by
  refine ⟨fun ⟨hc⟩ => induced_of_isLimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoLimit (isLimitConeOfForget _ hc) (Cone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

中文:
引理 nonempty_isLimit_iff_eq_induced
  结论: {F : J ⥤ TopCat.{u}} (c : Cone F)
  证明: by
  refine ⟨fun ⟨hc⟩ => induced_of_isLimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoLimit (isLimitConeOfForget _ hc) (Cone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

Depends on / 依赖: Cone.ext, TopCat, TopCat.isoOfHomeo, continuous_invFun, continuous_toFun, fun_prop, induced_of_isLimit, isLimitConeOfForget, isoOfHomeo, ofIsoLimit, toEquiv
-/
lemma nonempty_isLimit_iff_eq_induced {F : J ⥤ TopCat.{u}} (c : Cone F)
    (hc : IsLimit ((forget).mapCone c)) :
    Nonempty (IsLimit c) ↔ c.pt.str = ⨅ j, (F.obj j).str.induced (c.π.app j) := by
  refine ⟨fun ⟨hc⟩ => induced_of_isLimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoLimit (isLimitConeOfForget _ hc) (Cone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

variable (F : J ⥤ TopCat.{u})

/--
theorem `limit_topology` / 定理 `limit_topology`

English:
theorem limit_topology
  given: [HasLimit F]
  proof: induced_of_isLimit _ (limit.isLimit _)

中文:
定理 limit_topology
  条件: [HasLimit F]
  证明: induced_of_isLimit _ (limit.isLimit _)

Depends on / 依赖: induced_of_isLimit, isLimit, limit.isLimit
-/
theorem limit_topology [HasLimit F] :
    (limit F).str = ⨅ j, (F.obj j).str.induced (limit.π F j) :=
  induced_of_isLimit _ (limit.isLimit _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hasLimit_iff_small_sections` / 引理 `hasLimit_iff_small_sections`

English:
lemma hasLimit_iff_small_sections
  proof: by
  rw [← Types.hasLimit_iff_small_sections]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isLimitConeOfForget _ (limit.isLimit _)⟩⟩

中文:
引理 hasLimit_iff_small_sections
  证明: by
  rw [← Types.hasLimit_iff_small_sections]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isLimitConeOfForget _ (limit.isLimit _)⟩⟩

Depends on / 依赖: Types.hasLimit_iff_small_sections, hasLimit_iff_small_sections, infer_instance, isLimit, isLimitConeOfForget, limit.isLimit
-/
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} ((F ⋙ forget).sections) := by
  rw [← Types.hasLimit_iff_small_sections]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isLimitConeOfForget _ (limit.isLimit _)⟩⟩

/--
Instance `topCat_hasLimitsOfShape` / 实例 `topCat_hasLimitsOfShape`

English:
instance topCat_hasLimitsOfShape
  signature: (J : Type v) [Category* J] [Small.{u} J]
  body: fun F => by
    rw [hasLimit_iff_small_sections]
    infer_instance

中文:
实例 topCat_hasLimitsOfShape
  签名: (J : 类型v) [Category* J] [Small.{u} J]
  定义体: fun F => by
    rw [hasLimit_iff_small_sections]
    infer_instance

Depends on / 依赖: hasLimit_iff_small_sections, infer_instance
-/
instance topCat_hasLimitsOfShape (J : Type v) [Category* J] [Small.{u} J] :
    HasLimitsOfShape J TopCat.{u} where
  has_limit := fun F => by
    rw [hasLimit_iff_small_sections]
    infer_instance

/--
Instance `topCat_hasLimitsOfSize` / 实例 `topCat_hasLimitsOfSize`

English:
instance topCat_hasLimitsOfSize
  signature: [UnivLE.{v, u}]

中文:
实例 topCat_hasLimitsOfSize
  签名: [UnivLE.{v, u}]
-/
instance topCat_hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} TopCat.{u} where

/--
Instance `topCat_hasLimits` / 实例 `topCat_hasLimits`

English:
instance topCat_hasLimits
  signature: : HasLimits TopCat.{u}
  body: TopCat.topCat_hasLimitsOfSize.{u, u}

中文:
实例 topCat_hasLimits
  签名: : HasLimits TopCat.{u}
  定义体: TopCat.topCat_hasLimitsOfSize.{u, u}

Depends on / 依赖: TopCat, TopCat.topCat_hasLimitsOfSize, topCat_hasLimitsOfSize
-/
instance topCat_hasLimits : HasLimits TopCat.{u} :=
  TopCat.topCat_hasLimitsOfSize.{u, u}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: :

中文:
实例 forget_preservesLimitsOfSize
  签名: :
-/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget : TopCat.{u} ⥤ _) where

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget : TopCat.{u} ⥤ _) where
-/
instance forget_preservesLimits : PreservesLimits (forget : TopCat.{u} ⥤ _) where

end Limits

section Colimits

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

section

variable (c : Cocone (F ⋙ forget))

/--
Definition of `coconePtOfCoconeForget` / `coconePtOfCoconeForget` 的定义

English:
definition coconePtOfCoconeForget
  signature: : Type _
  body: c.pt

中文:
定义 coconePtOfCoconeForget
  签名: : Type _
  定义体: c.pt

Depends on / 依赖: c.pt
-/
def coconePtOfCoconeForget : Type _ := c.pt

/--
Instance `topologicalSpaceCoconePtOfCoconeForget` / 实例 `topologicalSpaceCoconePtOfCoconeForget`

English:
instance topologicalSpaceCoconePtOfCoconeForget
  signature: :
  body: (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

中文:
实例 topologicalSpaceCoconePtOfCoconeForget
  签名: :
  定义体: (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

Depends on / 依赖: F.obj, coinduced, str.coinduced
-/
instance topologicalSpaceCoconePtOfCoconeForget :
    TopologicalSpace (coconePtOfCoconeForget c) :=
  (⨆ j, (F.obj j).str.coinduced (c.ι.app j))

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a functor `F : J ⥤ TopCat` and a cocone `c : Cocone (F ⋙ forget)`
of the underlying cocone of types, this is a cocone for `F` whose point is
`c.pt` with the supremum of the coinduced topologies by the maps `c.ι.app j`. -/
@[simps pt ι_app]
/--
Definition of `coconeOfCoconeForget` / `coconeOfCoconeForget` 的定义

English:
definition coconeOfCoconeForget
  signature: : Cocone F where
  body: of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (ContinuousMap.mk (c.ι.app j) (by
        rw [continuous_iff_coinduced_le]
        dsimp [topologicalSpaceCoconePtOfCoconeForget]
        exact le_iSup (fun j => (F.obj j).str.coinduced _) j))
      naturality j j' φ := by
        ext
       

中文:
定义 coconeOfCoconeForget
  签名: : Cocone F where
  定义体: of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (ContinuousMap.mk (c.ι.app j) (by
        rw [continuous_iff_coinduced_le]
        dsimp [topologicalSpaceCoconePtOfCoconeForget]
        exact le_iSup (fun j => (F.obj j).str.coinduced _) j))
      naturality j j' φ := by
        ext
       

Depends on / 依赖: coconePtOfCoconeForget
-/
def coconeOfCoconeForget : Cocone F where
  pt := of (coconePtOfCoconeForget c)
  ι :=
    { app j := ofHom (ContinuousMap.mk (c.ι.app j) (by
        rw [continuous_iff_coinduced_le]
        dsimp [topologicalSpaceCoconePtOfCoconeForget]
        exact le_iSup (fun j => (F.obj j).str.coinduced _) j))
      naturality j j' φ := by
        ext
        apply ConcreteCategory.congr_hom (c.ι.naturality φ) }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isColimitCoconeOfForget` / `isColimitCoconeOfForget` 的定义

English:
definition isColimitCoconeOfForget
  signature: (c : Cocone (F ⋙ forget)) (hc : IsColimit c)
  body: by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_le_induced]
  dsimp [topologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced

中文:
定义 isColimitCoconeOfForget
  签名: (c : Cocone (F ⋙ forget)) (hc : IsColimit c)
  定义体: by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_le_induced]
  dsimp [topologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext_iff.mp, ContinuousMap, ContinuousMap.mk, IsColimit, IsColimit.ofFaithful, coinduced_le_iff_le_induced, continuous, continuous_iff_le_induced, convert, forget, hc.desc, hc.fac, hom.continuous, hom_ext_iff, iSup_le_iff, induced_compose, mapCocone, ofFaithful, topologicalSpaceCoconePtOfCoconeForget
-/
def isColimitCoconeOfForget (c : Cocone (F ⋙ forget)) (hc : IsColimit c) :
    IsColimit (coconeOfCoconeForget c) := by
  refine IsColimit.ofFaithful forget (ht := hc)
    (fun s => ofHom (ContinuousMap.mk (hc.desc ((forget).mapCocone s)) ?_)) (fun _ => rfl)
  rw [continuous_iff_le_induced]
  dsimp [topologicalSpaceCoconePtOfCoconeForget]
  rw [iSup_le_iff]
  intro j
  rw [coinduced_le_iff_le_induced]; rw [induced_compose]
  convert! continuous_iff_le_induced.1 (s.ι.app j).hom.continuous
  ext x
  exact ConcreteCategory.hom_ext_iff.mp (hc.fac ((forget).mapCocone s) j) x

end

section IsColimit

variable (c : Cocone F) (hc : IsColimit c)

include hc

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `coinduced_of_isColimit` / 定理 `coinduced_of_isColimit`

English:
theorem coinduced_of_isColimit
  proof: by
  let c' := coconeOfCoconeForget ((forget).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfForget _ (isColimitOfPreserves forget hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom

中文:
定理 coinduced_of_isColimit
  证明: by
  let c' := coconeOfCoconeForget ((forget).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfForget _ (isColimitOfPreserves forget hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, coconeOfCoconeForget, coconeOfCoconeForget_pt, coconePointUniqueUpToIso, coinduced_eq, coinduced_eq.symm.trans, coinduced_iSup, comp_coconePointUniqueUpToIso_hom, conv_rhs, e.hom, forget, homeoOfIso, isColimitCoconeOfForget, isColimitOfPreserves, mapCocone, topologicalSpaceCoconePtOfCoconeForget
-/
theorem coinduced_of_isColimit :
    c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  let c' := coconeOfCoconeForget ((forget).mapCocone c)
  let hc' : IsColimit c' := isColimitCoconeOfForget _ (isColimitOfPreserves forget hc)
  let e := IsColimit.coconePointUniqueUpToIso hc' hc
  have he (j : J) : c'.ι.app j ≫ e.hom = c.ι.app j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc j
  apply (homeoOfIso e).coinduced_eq.symm.trans
  dsimp [coconeOfCoconeForget_pt, c', topologicalSpaceCoconePtOfCoconeForget]
  simp only [coinduced_iSup]
  conv_rhs => simp only [← he]
  rfl

/--
lemma `isOpen_iff_of_isColimit` / 引理 `isOpen_iff_of_isColimit`

English:
lemma isOpen_iff_of_isColimit
  given: (X : Set c.pt)
  proof: by
  trans (⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← coinduced_of_isColimit c hc, isOpen_fold]
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

中文:
引理 isOpen_iff_of_isColimit
  条件: (X : Set c.pt)
  证明: by
  trans (⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← coinduced_of_isColimit c hc, isOpen_fold]
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

Depends on / 依赖: F.obj, IsOpen, coinduced, coinduced_of_isColimit, isOpen_coinduced, isOpen_fold, isOpen_iSup_iff, str.coinduced
-/
lemma isOpen_iff_of_isColimit (X : Set c.pt) :
    IsOpen X ↔ forall (j : J), IsOpen (c.ι.app j ⁻¹' X) := by
  trans (⨆ (j : J), (F.obj j).str.coinduced (c.ι.app j)).IsOpen X
  · rw [← coinduced_of_isColimit c hc, isOpen_fold]
  · simp only [← isOpen_coinduced]
    apply isOpen_iSup_iff

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isClosed_iff_of_isColimit` / 引理 `isClosed_iff_of_isColimit`

English:
lemma isClosed_iff_of_isColimit
  given: (X : Set c.pt)
  proof: by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]

中文:
引理 isClosed_iff_of_isColimit
  条件: (X : Set c.pt)
  证明: by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]

Depends on / 依赖: Functor, Functor.const_obj_obj, Set.preimage_compl, const_obj_obj, isOpen_compl_iff, isOpen_iff_of_isColimit, preimage_compl
-/
lemma isClosed_iff_of_isColimit (X : Set c.pt) :
    IsClosed X ↔ forall (j : J), IsClosed (c.ι.app j ⁻¹' X) := by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isColimit _ hc,
    Functor.const_obj_obj, Set.preimage_compl]

/--
lemma `continuous_iff_of_isColimit` / 引理 `continuous_iff_of_isColimit`

English:
lemma continuous_iff_of_isColimit
  given: {X : Type u'} [TopologicalSpace X] (f : c.pt -> X)
  proof: by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

中文:
引理 continuous_iff_of_isColimit
  条件: {X : 类型u'} [TopologicalSpace X] (f : c.pt -> X)
  证明: by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

Depends on / 依赖: continuous_def, isOpen_iff_of_isColimit
-/
lemma continuous_iff_of_isColimit {X : Type u'} [TopologicalSpace X] (f : c.pt -> X) :
    Continuous f ↔ forall (j : J), Continuous (f ∘ c.ι.app j) := by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

end IsColimit

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `nonempty_isColimit_iff_eq_coinduced` / 引理 `nonempty_isColimit_iff_eq_coinduced`

English:
lemma nonempty_isColimit_iff_eq_coinduced
  given: (c : Cocone F) (hc : IsColimit ((forget).mapCocone c))
  proof: by
  refine ⟨fun ⟨hc⟩ => coinduced_of_isColimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoColimit (isColimitCoconeOfForget _ hc) (Cocone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro

中文:
引理 nonempty_isColimit_iff_eq_coinduced
  条件: (c : Cocone F) (hc : IsColimit ((forget).mapCocone c))
  证明: by
  refine ⟨fun ⟨hc⟩ => coinduced_of_isColimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoColimit (isColimitCoconeOfForget _ hc) (Cocone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro

Depends on / 依赖: Cocone, Cocone.ext, TopCat, TopCat.isoOfHomeo, coinduced_of_isColimit, continuous_invFun, continuous_toFun, fun_prop, isColimitCoconeOfForget, isoOfHomeo, ofIsoColimit, toEquiv
-/
lemma nonempty_isColimit_iff_eq_coinduced (c : Cocone F) (hc : IsColimit ((forget).mapCocone c)) :
    Nonempty (IsColimit c) ↔ c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  refine ⟨fun ⟨hc⟩ => coinduced_of_isColimit _ hc, fun h => ⟨?_⟩⟩
  refine .ofIsoColimit (isColimitCoconeOfForget _ hc) (Cocone.ext ?_ ?_)
  · refine TopCat.isoOfHomeo
      { toEquiv := .refl _,
        continuous_toFun := h ▸ by fun_prop,
        continuous_invFun := h ▸ by fun_prop }
  · intro; rfl

variable (F)

/--
theorem `colimit_topology` / 定理 `colimit_topology`

English:
theorem colimit_topology
  given: (F : J ⥤ TopCat.{u}) [HasColimit F]
  proof: coinduced_of_isColimit _ (colimit.isColimit _)

中文:
定理 colimit_topology
  条件: (F : J ⥤ TopCat.{u}) [HasColimit F]
  证明: coinduced_of_isColimit _ (colimit.isColimit _)

Depends on / 依赖: coinduced_of_isColimit, colimit, colimit.isColimit, isColimit
-/
theorem colimit_topology (F : J ⥤ TopCat.{u}) [HasColimit F] :
    (colimit F).str = ⨆ j, (F.obj j).str.coinduced (colimit.ι F j) :=
  coinduced_of_isColimit _ (colimit.isColimit _)

/--
theorem `colimit_isOpen_iff` / 定理 `colimit_isOpen_iff`

English:
theorem colimit_isOpen_iff
  statement: (F : J ⥤ TopCat.{u}) [HasColimit F]
  proof: by
  apply isOpen_iff_of_isColimit _ (colimit.isColimit _)

中文:
定理 colimit_isOpen_iff
  结论: (F : J ⥤ TopCat.{u}) [HasColimit F]
  证明: by
  apply isOpen_iff_of_isColimit _ (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isOpen_iff_of_isColimit
-/
theorem colimit_isOpen_iff (F : J ⥤ TopCat.{u}) [HasColimit F]
    (U : Set ((colimit F : _) : Type u)) :
    IsOpen U ↔ forall j, IsOpen (colimit.ι F j ⁻¹' U) := by
  apply isOpen_iff_of_isColimit _ (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hasColimit_iff_small_colimitType` / 引理 `hasColimit_iff_small_colimitType`

English:
lemma hasColimit_iff_small_colimitType
  proof: by
  rw [← Types.hasColimit_iff_small_colimitType]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩

中文:
引理 hasColimit_iff_small_colimitType
  证明: by
  rw [← Types.hasColimit_iff_small_colimitType]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩

Depends on / 依赖: Types.hasColimit_iff_small_colimitType, colimit, colimit.isColimit, hasColimit_iff_small_colimitType, infer_instance, isColimit, isColimitCoconeOfForget
-/
lemma hasColimit_iff_small_colimitType :
    HasColimit F ↔ Small.{u} (F ⋙ forget).ColimitType := by
  rw [← Types.hasColimit_iff_small_colimitType]
  constructor <;> intro
  · infer_instance
  · exact ⟨⟨_, isColimitCoconeOfForget _ (colimit.isColimit _)⟩⟩

/--
Instance `topCat_hasColimitsOfShape` / 实例 `topCat_hasColimitsOfShape`

English:
instance topCat_hasColimitsOfShape
  signature: (J : Type v) [Category* J] [Small.{u} J]
  body: fun F => by
    rw [hasColimit_iff_small_colimitType]
    infer_instance

中文:
实例 topCat_hasColimitsOfShape
  签名: (J : 类型v) [Category* J] [Small.{u} J]
  定义体: fun F => by
    rw [hasColimit_iff_small_colimitType]
    infer_instance

Depends on / 依赖: hasColimit_iff_small_colimitType, infer_instance
-/
instance topCat_hasColimitsOfShape (J : Type v) [Category* J] [Small.{u} J] :
    HasColimitsOfShape J TopCat.{u} where
  has_colimit := fun F => by
    rw [hasColimit_iff_small_colimitType]
    infer_instance

/--
Instance `topCat_hasColimitsOfSize` / 实例 `topCat_hasColimitsOfSize`

English:
instance topCat_hasColimitsOfSize
  signature: [UnivLE.{v, u}]

中文:
实例 topCat_hasColimitsOfSize
  签名: [UnivLE.{v, u}]
-/
instance topCat_hasColimitsOfSize [UnivLE.{v, u}] : HasColimitsOfSize.{w, v} TopCat.{u} where

/--
Instance `topCat_hasColimits` / 实例 `topCat_hasColimits`

English:
instance topCat_hasColimits
  signature: : HasColimits TopCat.{u}
  body: TopCat.topCat_hasColimitsOfSize.{u, u}

中文:
实例 topCat_hasColimits
  签名: : HasColimits TopCat.{u}
  定义体: TopCat.topCat_hasColimitsOfSize.{u, u}

Depends on / 依赖: TopCat, TopCat.topCat_hasColimitsOfSize, topCat_hasColimitsOfSize
-/
instance topCat_hasColimits : HasColimits TopCat.{u} :=
  TopCat.topCat_hasColimitsOfSize.{u, u}

/--
Instance `forget_preservesColimitsOfSize` / 实例 `forget_preservesColimitsOfSize`

English:
instance forget_preservesColimitsOfSize
  signature: :

中文:
实例 forget_preservesColimitsOfSize
  签名: :
-/
instance forget_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w, v} (forget : TopCat.{u} ⥤ _) where

/--
Instance `forget_preservesColimits` / 实例 `forget_preservesColimits`

English:
instance forget_preservesColimits
  signature: : PreservesColimits (forget : TopCat.{u} ⥤ Type u) where

中文:
实例 forget_preservesColimits
  签名: : PreservesColimits (forget : TopCat.{u} ⥤ 类型u) where
-/
instance forget_preservesColimits : PreservesColimits (forget : TopCat.{u} ⥤ Type u) where

end Colimits

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
definition isTerminalPUnit
  signature: : IsTerminal (TopCat.of PUnit.{u + 1})
  body: haveI : forall X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  Limits.IsTerminal.ofUnique _

中文:
定义 isTerminalPUnit
  签名: : IsTerminal (TopCat.of PUnit.{u + 1})
  定义体: haveI : forall X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  Limits.IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.ofUnique, PUnit.unit, TopCat, TopCat.of, Unique, continuous_const, ofUnique
-/
def isTerminalPUnit : IsTerminal (TopCat.of PUnit.{u + 1}) :=
  haveI : forall X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
    ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  Limits.IsTerminal.ofUnique _

/--
Definition of `terminalIsoPUnit` / `terminalIsoPUnit` 的定义

English:
definition terminalIsoPUnit
  signature: : ⊤_ TopCat.{u} ≅ TopCat.of PUnit
  body: terminalIsTerminal.uniqueUpToIso isTerminalPUnit

中文:
定义 terminalIsoPUnit
  签名: : ⊤_ TopCat.{u} ≅ TopCat.of PUnit
  定义体: terminalIsTerminal.uniqueUpToIso isTerminalPUnit

Depends on / 依赖: isTerminalPUnit, terminalIsTerminal, terminalIsTerminal.uniqueUpToIso, uniqueUpToIso
-/
def terminalIsoPUnit : ⊤_ TopCat.{u} ≅ TopCat.of PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit

/--
Definition of `isInitialPEmpty` / `isInitialPEmpty` 的定义

English:
definition isInitialPEmpty
  signature: : IsInitial (TopCat.of PEmpty.{u + 1})
  body: haveI : forall X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨ofHom ⟨fun x => x.elim, by fun_prop⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _

中文:
定义 isInitialPEmpty
  签名: : IsInitial (TopCat.of PEmpty.{u + 1})
  定义体: haveI : forall X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨ofHom ⟨fun x => x.elim, by fun_prop⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofUnique, PEmpty, TopCat, TopCat.of, Unique, fun_prop, ofUnique, x.elim
-/
def isInitialPEmpty : IsInitial (TopCat.of PEmpty.{u + 1}) :=
  haveI : forall X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
    ⟨⟨ofHom ⟨fun x => x.elim, by fun_prop⟩⟩, fun f => by ext ⟨⟩⟩
  Limits.IsInitial.ofUnique _

/--
Definition of `initialIsoPEmpty` / `initialIsoPEmpty` 的定义

English:
definition initialIsoPEmpty
  signature: : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty
  body: initialIsInitial.uniqueUpToIso isInitialPEmpty

中文:
定义 initialIsoPEmpty
  签名: : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty
  定义体: initialIsInitial.uniqueUpToIso isInitialPEmpty

Depends on / 依赖: initialIsInitial, initialIsInitial.uniqueUpToIso, isInitialPEmpty, uniqueUpToIso
-/
def initialIsoPEmpty : ⊥_ TopCat.{u} ≅ TopCat.of PEmpty :=
  initialIsInitial.uniqueUpToIso isInitialPEmpty

/--
lemma `IsInducing.empty` / 引理 `IsInducing.empty`

English:
lemma IsInducing.empty
  given: (X : TopCat)
  statement: Topology.IsInducing (TopCat.isInitialPEmpty.to X) where
  proof: by ext; simp

中文:
引理 IsInducing.empty
  条件: (X : TopCat)
  结论: Topology.IsInducing (TopCat.isInitialPEmpty.to X) where
  证明: by ext; simp
-/
lemma IsInducing.empty (X : TopCat) : Topology.IsInducing (TopCat.isInitialPEmpty.to X) where
  eq_induced := by ext; simp

end TopCat
