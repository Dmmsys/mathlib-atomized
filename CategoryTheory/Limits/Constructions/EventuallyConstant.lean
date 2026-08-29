/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits of eventually constant functors

If `F : J ⥤ C` is a functor from a cofiltered category, and `j : J`,
we introduce a property `F.IsEventuallyConstantTo j` which says
that for any `f : i ⟶ j`, the induced morphism `F.map f` is an isomorphism.
Under this assumption, it is shown that `F` admits `F.obj j` as a limit
(`Functor.IsEventuallyConstantTo.isLimitCone`).

A typeclass `Cofiltered.IsEventuallyConstant` is also introduced, and
the dual results for filtered categories and colimits are also obtained.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category* J] [Category* C] (F : J ⥤ C)

namespace Functor

/--
Definition of `IsEventuallyConstantTo` / `IsEventuallyConstantTo` 的定义

English:
definition IsEventuallyConstantTo
  signature: (j : J)
  body: forall ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

中文:
定义 IsEventuallyConstantTo
  签名: (j : J)
  定义体: forall ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

Depends on / 依赖: F.map
-/
def IsEventuallyConstantTo (j : J) : Prop :=
  forall ⦃i : J⦄ (f : i ⟶ j), IsIso (F.map f)

/--
Definition of `IsEventuallyConstantFrom` / `IsEventuallyConstantFrom` 的定义

English:
definition IsEventuallyConstantFrom
  signature: (i : J)
  body: forall ⦃j : J⦄ (f : i ⟶ j), IsIso (F.map f)

中文:
定义 IsEventuallyConstantFrom
  签名: (i : J)
  定义体: forall ⦃j : J⦄ (f : i ⟶ j), IsIso (F.map f)

Depends on / 依赖: F.map
-/
def IsEventuallyConstantFrom (i : J) : Prop :=
  forall ⦃j : J⦄ (f : i ⟶ j), IsIso (F.map f)

namespace IsEventuallyConstantTo

variable {F} {i₀ : J} (h : F.IsEventuallyConstantTo i₀)

include h

/--
lemma `isIso_map` / 引理 `isIso_map`

English:
lemma isIso_map
  given: {i j : J} (φ : i ⟶ j) (π : j ⟶ i₀)
  statement: IsIso (F.map φ)
  proof: by
  have := h π
  have := h (φ ≫ π)
  exact IsIso.of_isIso_fac_right (F.map_comp φ π).symm

中文:
引理 isIso_map
  条件: {i j : J} (φ : i ⟶ j) (π : j ⟶ i₀)
  结论: IsIso (F.map φ)
  证明: by
  have := h π
  have := h (φ ≫ π)
  exact IsIso.of_isIso_fac_right (F.map_comp φ π).symm

Depends on / 依赖: F.map_comp, IsIso.of_isIso_fac_right, map_comp, of_isIso_fac_right
-/
lemma isIso_map {i j : J} (φ : i ⟶ j) (π : j ⟶ i₀) : IsIso (F.map φ) := by
  have := h π
  have := h (φ ≫ π)
  exact IsIso.of_isIso_fac_right (F.map_comp φ π).symm

/--
lemma `precomp` / 引理 `precomp`

English:
lemma precomp
  given: {j : J} (f : j ⟶ i₀)
  statement: F.IsEventuallyConstantTo j
  proof: fun _ φ => h.isIso_map φ f

中文:
引理 precomp
  条件: {j : J} (f : j ⟶ i₀)
  结论: F.IsEventuallyConstantTo j
  证明: fun _ φ => h.isIso_map φ f

Depends on / 依赖: h.isIso_map, isIso_map
-/
lemma precomp {j : J} (f : j ⟶ i₀) : F.IsEventuallyConstantTo j :=
  fun _ φ => h.isIso_map φ f

section

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (j ⟶ i₀))

/-- The isomorphism `F.obj i ≅ F.obj j` induced by `φ : i ⟶ j`,
when `h : F.IsEventuallyConstantTo i₀` and there exists a map `j ⟶ i₀`. -/
@[simps! hom]
/--
Definition of `isoMap` / `isoMap` 的定义

English:
definition isoMap
  signature: : F.obj i ≅ F.obj j
  body: have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]

中文:
定义 isoMap
  签名: : F.obj i ≅ F.obj j
  定义体: have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, h.isIso_map, isIso_map
-/
noncomputable def isoMap : F.obj i ≅ F.obj j :=
  have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]
/--
lemma `isoMap_hom_inv_id` / 引理 `isoMap_hom_inv_id`

English:
lemma isoMap_hom_inv_id
  statement: F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _
  proof: (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoMap_hom_inv_id
  结论: F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _
  证明: (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: h.isoMap, hom_inv_id, isoMap
-/
lemma isoMap_hom_inv_id : F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _ :=
  (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoMap_inv_hom_id` / 引理 `isoMap_inv_hom_id`

English:
lemma isoMap_inv_hom_id
  statement: (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
  proof: (h.isoMap φ hφ).inv_hom_id

中文:
引理 isoMap_inv_hom_id
  结论: (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
  证明: (h.isoMap φ hφ).inv_hom_id

Depends on / 依赖: h.isoMap, inv_hom_id, isoMap
-/
lemma isoMap_inv_hom_id : (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _ :=
  (h.isoMap φ hφ).inv_hom_id

end

variable [IsCofiltered J]
open IsCofiltered

/--
Definition of `coneπApp` / `coneπApp` 的定义

English:
definition coneπApp
  signature: (j : J)
  body: (h.isoMap (minToLeft i₀ j) ⟨𝟙 _⟩).inv ≫ F.map (minToRight i₀ j)

中文:
定义 coneπApp
  签名: (j : J)
  定义体: (h.isoMap (minToLeft i₀ j) ⟨𝟙 _⟩).inv ≫ F.map (minToRight i₀ j)

Depends on / 依赖: F.map, h.isoMap, isoMap, minToLeft, minToRight
-/
noncomputable def coneπApp (j : J) : F.obj i₀ ⟶ F.obj j :=
  (h.isoMap (minToLeft i₀ j) ⟨𝟙 _⟩).inv ≫ F.map (minToRight i₀ j)

/--
lemma `coneπApp_eq` / 引理 `coneπApp_eq`

English:
lemma coneπApp_eq
  given: (j j' : J) (α : j' ⟶ i₀) (β : j' ⟶ j)
  proof: by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsCofiltered.bowtie
    (IsCofiltered.minToRight i₀ j) β (IsCofiltered.minToLeft i₀ j) α
  dsimp [coneπApp]
  rw [← cancel_epi ((h.isoMap α ⟨𝟙 _⟩).hom)]; rw [isoMap_hom]; rw [isoMap_hom_inv_id_assoc]; rw [← cancel_epi (h.isoMap δ ⟨α⟩).hom]; rw [isoMap_hom]; rw [← F.m

中文:
引理 coneπApp_eq
  条件: (j j' : J) (α : j' ⟶ i₀) (β : j' ⟶ j)
  证明: by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsCofiltered.bowtie
    (IsCofiltered.minToRight i₀ j) β (IsCofiltered.minToLeft i₀ j) α
  dsimp [coneπApp]
  rw [← cancel_epi ((h.isoMap α ⟨𝟙 _⟩).hom)]; rw [isoMap_hom]; rw [isoMap_hom_inv_id_assoc]; rw [← cancel_epi (h.isoMap δ ⟨α⟩).hom]; rw [isoMap_hom]; rw [← F.m

Depends on / 依赖: F.map_comp, F.map_comp_assoc, IsCofiltered, IsCofiltered.bowtie, IsCofiltered.minToLeft, IsCofiltered.minToRight, bowtie, cancel_epi, h.isoMap, isoMap, isoMap_hom, isoMap_hom_inv_id_assoc, map_comp, map_comp_assoc, minToLeft, minToRight
-/
lemma coneπApp_eq (j j' : J) (α : j' ⟶ i₀) (β : j' ⟶ j) :
    h.coneπApp j = (h.isoMap α ⟨𝟙 _⟩).inv ≫ F.map β := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsCofiltered.bowtie
    (IsCofiltered.minToRight i₀ j) β (IsCofiltered.minToLeft i₀ j) α
  dsimp [coneπApp]
  rw [← cancel_epi ((h.isoMap α ⟨𝟙 _⟩).hom)]; rw [isoMap_hom]; rw [isoMap_hom_inv_id_assoc]; rw [← cancel_epi (h.isoMap δ ⟨α⟩).hom]; rw [isoMap_hom]; rw [← F.map_comp δ β]; rw [← h₁]; rw [F.map_comp]; rw [← F.map_comp_assoc]; rw [← h₂]; rw [F.map_comp_assoc]; rw [isoMap_hom_inv_id_assoc]

@[simp]
/--
lemma `coneπApp_eq_id` / 引理 `coneπApp_eq_id`

English:
lemma coneπApp_eq_id
  statement: h.coneπApp i₀ = 𝟙 _
  proof: by
  rw [h.coneπApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_inv_hom_id]

中文:
引理 coneπApp_eq_id
  结论: h.coneπApp i₀ = 𝟙 _
  证明: by
  rw [h.coneπApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_inv_hom_id]

Depends on / 依赖: h.cone, h.isoMap_inv_hom_id, isoMap_inv_hom_id
-/
lemma coneπApp_eq_id : h.coneπApp i₀ = 𝟙 _ := by
  rw [h.coneπApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_inv_hom_id]

set_option backward.defeqAttrib.useBackward true in
/-- Given `h : F.IsEventuallyConstantTo i₀`, this is the (limit) cone for `F` whose
point is `F.obj i₀`. -/
@[simps]
/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: : Cone F where
  body: F.obj i₀
  π :=
    { app := h.coneπApp
      naturality := fun j j' φ => by
        dsimp
        rw [id_comp]
        let i := IsCofiltered.min i₀ j
        let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
        let β : i ⟶ j := IsCofiltered.minToRight _ _
        rw [h.coneπApp_eq j _ α β]; rw [ass

中文:
定义 cone
  签名: : Cone F where
  定义体: F.obj i₀
  π :=
    { app := h.coneπApp
      naturality := fun j j' φ => by
        dsimp
        rw [id_comp]
        let i := IsCofiltered.min i₀ j
        let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
        let β : i ⟶ j := IsCofiltered.minToRight _ _
        rw [h.coneπApp_eq j _ α β]; rw [ass

Depends on / 依赖: F.obj
-/
noncomputable def cone : Cone F where
  pt := F.obj i₀
  π :=
    { app := h.coneπApp
      naturality := fun j j' φ => by
        dsimp
        rw [id_comp]
        let i := IsCofiltered.min i₀ j
        let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
        let β : i ⟶ j := IsCofiltered.minToRight _ _
        rw [h.coneπApp_eq j _ α β]; rw [assoc]; rw [h.coneπApp_eq j' _ α (β ≫ φ)]; rw [map_comp] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitCone` / `isLimitCone` 的定义

English:
definition isLimitCone
  signature: : IsLimit h.cone where
  body: s.π.app i₀
  fac s j := by
    dsimp [coneπApp]
    rw [← s.w (IsCofiltered.minToLeft i₀ j)]; rw [← s.w (IsCofiltered.minToRight i₀ j)]; rw [assoc]; rw [isoMap_hom_inv_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cone_π_app, coneπApp_eq_id, cone_pt, comp_id]

中文:
定义 isLimitCone
  签名: : IsLimit h.cone where
  定义体: s.π.app i₀
  fac s j := by
    dsimp [coneπApp]
    rw [← s.w (IsCofiltered.minToLeft i₀ j)]; rw [← s.w (IsCofiltered.minToRight i₀ j)]; rw [assoc]; rw [isoMap_hom_inv_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cone_π_app, coneπApp_eq_id, cone_pt, comp_id]
-/
noncomputable def isLimitCone : IsLimit h.cone where
  lift s := s.π.app i₀
  fac s j := by
    dsimp [coneπApp]
    rw [← s.w (IsCofiltered.minToLeft i₀ j)]; rw [← s.w (IsCofiltered.minToRight i₀ j)]; rw [assoc]; rw [isoMap_hom_inv_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cone_π_app, coneπApp_eq_id, cone_pt, comp_id]

/--
lemma `hasLimit` / 引理 `hasLimit`

English:
lemma hasLimit
  statement: HasLimit F
  proof: ⟨_, h.isLimitCone⟩

中文:
引理 hasLimit
  结论: HasLimit F
  证明: ⟨_, h.isLimitCone⟩

Depends on / 依赖: h.isLimitCone, isLimitCone
-/
lemma hasLimit : HasLimit F := ⟨_, h.isLimitCone⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isIso_π_of_isLimit` / 引理 `isIso_π_of_isLimit`

English:
lemma isIso_π_of_isLimit
  given: {c : Cone F} (hc : IsLimit c)
  proof: by
  simp only [← IsLimit.conePointUniqueUpToIso_hom_comp hc h.isLimitCone i₀,
    cone_π_app, coneπApp_eq_id, cone_pt, comp_id]
  infer_instance

中文:
引理 isIso_π_of_isLimit
  条件: {c : Cone F} (hc : IsLimit c)
  证明: by
  simp only [← IsLimit.conePointUniqueUpToIso_hom_comp hc h.isLimitCone i₀,
    cone_π_app, coneπApp_eq_id, cone_pt, comp_id]
  infer_instance

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, comp_id, conePointUniqueUpToIso_hom_comp, cone_pt, h.isLimitCone, infer_instance, isLimitCone
-/
lemma isIso_π_of_isLimit {c : Cone F} (hc : IsLimit c) :
    IsIso (c.π.app i₀) := by
  simp only [← IsLimit.conePointUniqueUpToIso_hom_comp hc h.isLimitCone i₀,
    cone_π_app, coneπApp_eq_id, cone_pt, comp_id]
  infer_instance

/--
lemma `isIso_π_of_isLimit'` / 引理 `isIso_π_of_isLimit'`

English:
lemma isIso_π_of_isLimit'
  given: {c : Cone F} (hc : IsLimit c) (j : J) (π : j ⟶ i₀)
  proof: (h.precomp π).isIso_π_of_isLimit hc

中文:
引理 isIso_π_of_isLimit'
  条件: {c : Cone F} (hc : IsLimit c) (j : J) (π : j ⟶ i₀)
  证明: (h.precomp π).isIso_π_of_isLimit hc

Depends on / 依赖: h.precomp, precomp
-/
lemma isIso_π_of_isLimit' {c : Cone F} (hc : IsLimit c) (j : J) (π : j ⟶ i₀) :
    IsIso (c.π.app j) :=
  (h.precomp π).isIso_π_of_isLimit hc

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitOfIsIso` / `isLimitOfIsIso` 的定义

English:
definition isLimitOfIsIso
  signature: (c : Cone F) [IsIso (c.π.app i₀)]
  body: IsLimit.ofIsoLimit h.isLimitCone (by
    refine Cone.ext (asIso (c.π.app i₀)).symm (fun j => ?_)
    let i := IsCofiltered.min i₀ j
    let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
    let β : i ⟶ j := IsCofiltered.minToRight _ _
    dsimp
    rw [IsIso.eq_inv_comp]; rw [← c.w α]; rw [← c.w β]; rw [

中文:
定义 isLimitOfIsIso
  签名: (c : Cone F) [IsIso (c.π.app i₀)]
  定义体: IsLimit.ofIsoLimit h.isLimitCone (by
    refine Cone.ext (asIso (c.π.app i₀)).symm (fun j => ?_)
    let i := IsCofiltered.min i₀ j
    let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
    let β : i ⟶ j := IsCofiltered.minToRight _ _
    dsimp
    rw [IsIso.eq_inv_comp]; rw [← c.w α]; rw [← c.w β]; rw [

Depends on / 依赖: Cone.ext, IsCofiltered, IsCofiltered.min, IsCofiltered.minToLeft, IsCofiltered.minToRight, IsIso.eq_inv_comp, IsLimit, IsLimit.ofIsoLimit, eq_inv_comp, h.cone, h.isLimitCone, isLimitCone, isoMap_hom_inv_id_assoc, minToLeft, minToRight, ofIsoLimit
-/
noncomputable def isLimitOfIsIso (c : Cone F) [IsIso (c.π.app i₀)] : IsLimit c :=
  IsLimit.ofIsoLimit h.isLimitCone (by
    refine Cone.ext (asIso (c.π.app i₀)).symm (fun j => ?_)
    let i := IsCofiltered.min i₀ j
    let α : i ⟶ i₀ := IsCofiltered.minToLeft _ _
    let β : i ⟶ j := IsCofiltered.minToRight _ _
    dsimp
    rw [IsIso.eq_inv_comp]; rw [← c.w α]; rw [← c.w β]; rw [h.coneπApp_eq j _ α β]; rw [assoc]; rw [isoMap_hom_inv_id_assoc])

end IsEventuallyConstantTo

namespace IsEventuallyConstantFrom

variable {F} {i₀ : J} (h : F.IsEventuallyConstantFrom i₀)

include h

/--
lemma `isIso_map` / 引理 `isIso_map`

English:
lemma isIso_map
  given: {i j : J} (φ : i ⟶ j) (ι : i₀ ⟶ i)
  statement: IsIso (F.map φ)
  proof: by
  have := h ι
  have := h (ι ≫ φ)
  exact IsIso.of_isIso_fac_left (F.map_comp ι φ).symm

中文:
引理 isIso_map
  条件: {i j : J} (φ : i ⟶ j) (ι : i₀ ⟶ i)
  结论: IsIso (F.map φ)
  证明: by
  have := h ι
  have := h (ι ≫ φ)
  exact IsIso.of_isIso_fac_left (F.map_comp ι φ).symm

Depends on / 依赖: F.map_comp, IsIso.of_isIso_fac_left, map_comp, of_isIso_fac_left
-/
lemma isIso_map {i j : J} (φ : i ⟶ j) (ι : i₀ ⟶ i) : IsIso (F.map φ) := by
  have := h ι
  have := h (ι ≫ φ)
  exact IsIso.of_isIso_fac_left (F.map_comp ι φ).symm

/--
lemma `postcomp` / 引理 `postcomp`

English:
lemma postcomp
  given: {j : J} (f : i₀ ⟶ j)
  statement: F.IsEventuallyConstantFrom j
  proof: fun _ φ => h.isIso_map φ f

中文:
引理 postcomp
  条件: {j : J} (f : i₀ ⟶ j)
  结论: F.IsEventuallyConstantFrom j
  证明: fun _ φ => h.isIso_map φ f

Depends on / 依赖: h.isIso_map, isIso_map
-/
lemma postcomp {j : J} (f : i₀ ⟶ j) : F.IsEventuallyConstantFrom j :=
  fun _ φ => h.isIso_map φ f

section

variable {i j : J} (φ : i ⟶ j) (hφ : Nonempty (i₀ ⟶ i))

/-- The isomorphism `F.obj i ≅ F.obj j` induced by `φ : i ⟶ j`,
when `h : F.IsEventuallyConstantFrom i₀` and there exists a map `i₀ ⟶ i`. -/
@[simps! hom]
/--
Definition of `isoMap` / `isoMap` 的定义

English:
definition isoMap
  signature: : F.obj i ≅ F.obj j
  body: have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]

中文:
定义 isoMap
  签名: : F.obj i ≅ F.obj j
  定义体: have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]

Depends on / 依赖: F.map, h.isIso_map, isIso_map
-/
noncomputable def isoMap : F.obj i ≅ F.obj j :=
  have := h.isIso_map φ hφ.some
  asIso (F.map φ)

@[reassoc (attr := simp)]
/--
lemma `isoMap_hom_inv_id` / 引理 `isoMap_hom_inv_id`

English:
lemma isoMap_hom_inv_id
  statement: F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _
  proof: (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoMap_hom_inv_id
  结论: F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _
  证明: (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: h.isoMap, hom_inv_id, isoMap
-/
lemma isoMap_hom_inv_id : F.map φ ≫ (h.isoMap φ hφ).inv = 𝟙 _ :=
  (h.isoMap φ hφ).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoMap_inv_hom_id` / 引理 `isoMap_inv_hom_id`

English:
lemma isoMap_inv_hom_id
  statement: (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
  proof: (h.isoMap φ hφ).inv_hom_id

中文:
引理 isoMap_inv_hom_id
  结论: (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _
  证明: (h.isoMap φ hφ).inv_hom_id

Depends on / 依赖: h.isoMap, inv_hom_id, isoMap
-/
lemma isoMap_inv_hom_id : (h.isoMap φ hφ).inv ≫ F.map φ = 𝟙 _ :=
  (h.isoMap φ hφ).inv_hom_id

end

variable [IsFiltered J]
open IsFiltered

/--
Definition of `coconeιApp` / `coconeιApp` 的定义

English:
definition coconeιApp
  signature: (j : J)
  body: F.map (rightToMax i₀ j) ≫ (h.isoMap (leftToMax i₀ j) ⟨𝟙 _⟩).inv

中文:
定义 coconeιApp
  签名: (j : J)
  定义体: F.map (rightToMax i₀ j) ≫ (h.isoMap (leftToMax i₀ j) ⟨𝟙 _⟩).inv

Depends on / 依赖: F.map, h.isoMap, isoMap, leftToMax, rightToMax
-/
noncomputable def coconeιApp (j : J) : F.obj j ⟶ F.obj i₀ :=
  F.map (rightToMax i₀ j) ≫ (h.isoMap (leftToMax i₀ j) ⟨𝟙 _⟩).inv

/--
lemma `coconeιApp_eq` / 引理 `coconeιApp_eq`

English:
lemma coconeιApp_eq
  given: (j j' : J) (α : j ⟶ j') (β : i₀ ⟶ j')
  proof: by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsFiltered.bowtie
    (IsFiltered.leftToMax i₀ j) β (IsFiltered.rightToMax i₀ j) α
  dsimp [coconeιApp]
  rw [← cancel_mono ((h.isoMap β ⟨𝟙 _⟩).hom)]; rw [assoc]; rw [assoc]; rw [isoMap_hom]; rw [isoMap_inv_hom_id]; rw [comp_id]; rw [← cancel_mono (h.isoMap δ ⟨β⟩).ho

中文:
引理 coconeιApp_eq
  条件: (j j' : J) (α : j ⟶ j') (β : i₀ ⟶ j')
  证明: by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsFiltered.bowtie
    (IsFiltered.leftToMax i₀ j) β (IsFiltered.rightToMax i₀ j) α
  dsimp [coconeιApp]
  rw [← cancel_mono ((h.isoMap β ⟨𝟙 _⟩).hom)]; rw [assoc]; rw [assoc]; rw [isoMap_hom]; rw [isoMap_inv_hom_id]; rw [comp_id]; rw [← cancel_mono (h.isoMap δ ⟨β⟩).ho

Depends on / 依赖: F.map_comp, IsFiltered, IsFiltered.bowtie, IsFiltered.leftToMax, IsFiltered.rightToMax, bowtie, cancel_mono, comp_id, h.isoMap, isoMap, isoMap_hom, isoMap_inv_hom_id, isoMap_inv_hom_id_assoc, leftToMax, map_comp, rightToMax
-/
lemma coconeιApp_eq (j j' : J) (α : j ⟶ j') (β : i₀ ⟶ j') :
    h.coconeιApp j = F.map α ≫ (h.isoMap β ⟨𝟙 _⟩).inv := by
  obtain ⟨s, γ, δ, h₁, h₂⟩ := IsFiltered.bowtie
    (IsFiltered.leftToMax i₀ j) β (IsFiltered.rightToMax i₀ j) α
  dsimp [coconeιApp]
  rw [← cancel_mono ((h.isoMap β ⟨𝟙 _⟩).hom)]; rw [assoc]; rw [assoc]; rw [isoMap_hom]; rw [isoMap_inv_hom_id]; rw [comp_id]; rw [← cancel_mono (h.isoMap δ ⟨β⟩).hom]; rw [isoMap_hom]; rw [assoc]; rw [assoc]; rw [← F.map_comp α δ]; rw [← h₂]; rw [F.map_comp]; rw [← F.map_comp β δ]; rw [← h₁]; rw [F.map_comp]; rw [isoMap_inv_hom_id_assoc]

@[simp]
/--
lemma `coconeιApp_eq_id` / 引理 `coconeιApp_eq_id`

English:
lemma coconeιApp_eq_id
  statement: h.coconeιApp i₀ = 𝟙 _
  proof: by
  rw [h.coconeιApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_hom_inv_id]

中文:
引理 coconeιApp_eq_id
  结论: h.coconeιApp i₀ = 𝟙 _
  证明: by
  rw [h.coconeιApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_hom_inv_id]

Depends on / 依赖: h.cocone, h.isoMap_hom_inv_id, isoMap_hom_inv_id
-/
lemma coconeιApp_eq_id : h.coconeιApp i₀ = 𝟙 _ := by
  rw [h.coconeιApp_eq i₀ i₀ (𝟙 _) (𝟙 _)]; rw [h.isoMap_hom_inv_id]

set_option backward.defeqAttrib.useBackward true in
/-- Given `h : F.IsEventuallyConstantFrom i₀`, this is the (limit) cocone for `F` whose
point is `F.obj i₀`. -/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone F where
  body: F.obj i₀
  ι :=
    { app := h.coconeιApp
      naturality := fun j j' φ => by
        dsimp
        rw [comp_id]
        let i := IsFiltered.max i₀ j'
        let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
        let β : j' ⟶ i := IsFiltered.rightToMax _ _
        rw [h.coconeιApp_eq j' _ β α]; rw [h.

中文:
定义 cocone
  签名: : Cocone F where
  定义体: F.obj i₀
  ι :=
    { app := h.coconeιApp
      naturality := fun j j' φ => by
        dsimp
        rw [comp_id]
        let i := IsFiltered.max i₀ j'
        let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
        let β : j' ⟶ i := IsFiltered.rightToMax _ _
        rw [h.coconeιApp_eq j' _ β α]; rw [h.

Depends on / 依赖: F.obj
-/
noncomputable def cocone : Cocone F where
  pt := F.obj i₀
  ι :=
    { app := h.coconeιApp
      naturality := fun j j' φ => by
        dsimp
        rw [comp_id]
        let i := IsFiltered.max i₀ j'
        let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
        let β : j' ⟶ i := IsFiltered.rightToMax _ _
        rw [h.coconeιApp_eq j' _ β α]; rw [h.coconeιApp_eq j _ (φ ≫ β) α]; rw [map_comp]; rw [assoc] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  signature: : IsColimit h.cocone where
  body: s.ι.app i₀
  fac s j := by
    dsimp [coconeιApp]
    rw [← s.w (IsFiltered.rightToMax i₀ j)]; rw [← s.w (IsFiltered.leftToMax i₀ j)]; rw [assoc]; rw [isoMap_inv_hom_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cocone_ι_app, coconeιApp_eq_id, id_comp]

中文:
定义 isColimitCocone
  签名: : IsColimit h.cocone where
  定义体: s.ι.app i₀
  fac s j := by
    dsimp [coconeιApp]
    rw [← s.w (IsFiltered.rightToMax i₀ j)]; rw [← s.w (IsFiltered.leftToMax i₀ j)]; rw [assoc]; rw [isoMap_inv_hom_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cocone_ι_app, coconeιApp_eq_id, id_comp]
-/
noncomputable def isColimitCocone : IsColimit h.cocone where
  desc s := s.ι.app i₀
  fac s j := by
    dsimp [coconeιApp]
    rw [← s.w (IsFiltered.rightToMax i₀ j)]; rw [← s.w (IsFiltered.leftToMax i₀ j)]; rw [assoc]; rw [isoMap_inv_hom_id_assoc]
  uniq s m hm := by simp only [← hm i₀, cocone_ι_app, coconeιApp_eq_id, id_comp]

/--
lemma `hasColimit` / 引理 `hasColimit`

English:
lemma hasColimit
  statement: HasColimit F
  proof: ⟨_, h.isColimitCocone⟩

中文:
引理 hasColimit
  结论: HasColimit F
  证明: ⟨_, h.isColimitCocone⟩

Depends on / 依赖: h.isColimitCocone, isColimitCocone
-/
lemma hasColimit : HasColimit F := ⟨_, h.isColimitCocone⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_ι_of_isColimit` / 引理 `isIso_ι_of_isColimit`

English:
lemma isIso_ι_of_isColimit
  given: {c : Cocone F} (hc : IsColimit c)
  proof: by
  simp only [← IsColimit.comp_coconePointUniqueUpToIso_inv hc h.isColimitCocone i₀,
    cocone_ι_app, coconeιApp_eq_id, id_comp]
  infer_instance

中文:
引理 isIso_ι_of_isColimit
  条件: {c : Cocone F} (hc : IsColimit c)
  证明: by
  simp only [← IsColimit.comp_coconePointUniqueUpToIso_inv hc h.isColimitCocone i₀,
    cocone_ι_app, coconeιApp_eq_id, id_comp]
  infer_instance

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, comp_coconePointUniqueUpToIso_inv, h.isColimitCocone, id_comp, infer_instance, isColimitCocone
-/
lemma isIso_ι_of_isColimit {c : Cocone F} (hc : IsColimit c) :
    IsIso (c.ι.app i₀) := by
  simp only [← IsColimit.comp_coconePointUniqueUpToIso_inv hc h.isColimitCocone i₀,
    cocone_ι_app, coconeιApp_eq_id, id_comp]
  infer_instance

/--
lemma `isIso_ι_of_isColimit'` / 引理 `isIso_ι_of_isColimit'`

English:
lemma isIso_ι_of_isColimit'
  given: {c : Cocone F} (hc : IsColimit c) (j : J) (ι : i₀ ⟶ j)
  proof: (h.postcomp ι).isIso_ι_of_isColimit hc

中文:
引理 isIso_ι_of_isColimit'
  条件: {c : Cocone F} (hc : IsColimit c) (j : J) (ι : i₀ ⟶ j)
  证明: (h.postcomp ι).isIso_ι_of_isColimit hc

Depends on / 依赖: h.postcomp, postcomp
-/
lemma isIso_ι_of_isColimit' {c : Cocone F} (hc : IsColimit c) (j : J) (ι : i₀ ⟶ j) :
    IsIso (c.ι.app j) :=
  (h.postcomp ι).isIso_ι_of_isColimit hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitOfIsIso` / `isColimitOfIsIso` 的定义

English:
definition isColimitOfIsIso
  signature: (c : Cocone F) [IsIso (c.ι.app i₀)]
  body: IsColimit.ofIsoColimit h.isColimitCocone (by
    refine Cocone.ext (asIso (c.ι.app i₀)) (fun j => ?_)
    let i := IsFiltered.max i₀ j
    let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
    let β : j ⟶ i := IsFiltered.rightToMax _ _
    dsimp
    rw [← c.w α]; rw [← c.w β]; rw [h.coconeιApp_eq j _ β α];

中文:
定义 isColimitOfIsIso
  签名: (c : Cocone F) [IsIso (c.ι.app i₀)]
  定义体: IsColimit.ofIsoColimit h.isColimitCocone (by
    refine Cocone.ext (asIso (c.ι.app i₀)) (fun j => ?_)
    let i := IsFiltered.max i₀ j
    let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
    let β : j ⟶ i := IsFiltered.rightToMax _ _
    dsimp
    rw [← c.w α]; rw [← c.w β]; rw [h.coconeιApp_eq j _ β α];

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, IsFiltered, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, h.cocone, h.isColimitCocone, isColimitCocone, isoMap_inv_hom_id_assoc, leftToMax, ofIsoColimit, rightToMax
-/
noncomputable def isColimitOfIsIso (c : Cocone F) [IsIso (c.ι.app i₀)] : IsColimit c :=
  IsColimit.ofIsoColimit h.isColimitCocone (by
    refine Cocone.ext (asIso (c.ι.app i₀)) (fun j => ?_)
    let i := IsFiltered.max i₀ j
    let α : i₀ ⟶ i := IsFiltered.leftToMax _ _
    let β : j ⟶ i := IsFiltered.rightToMax _ _
    dsimp
    rw [← c.w α]; rw [← c.w β]; rw [h.coconeιApp_eq j _ β α]; rw [assoc]; rw [isoMap_inv_hom_id_assoc])

end IsEventuallyConstantFrom

end Functor

namespace IsCofiltered

/--
Definition of `IsEventuallyConstant` / `IsEventuallyConstant` 的定义

English:
class IsEventuallyConstant
  parameters: : Prop where
  axioms and operations (1):
    - exists_isEventuallyConstantTo : exists (j : J), F.IsEventuallyConstantTo j

中文:
类 IsEventuallyConstant
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_isEventuallyConstantTo : 存在 (j : J), F.IsEventuallyConstantTo j
-/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantTo : exists (j : J), F.IsEventuallyConstantTo j

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hF
  signature: : IsEventuallyConstant F] [IsCofiltered J] : HasLimit F
  body: by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantTo
  exact h.hasLimit

中文:
实例 [hF
  签名: : IsEventuallyConstant F] [IsCofiltered J] : HasLimit F
  定义体: by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantTo
  exact h.hasLimit

Depends on / 依赖: exists_isEventuallyConstantTo, h.hasLimit, hF.exists_isEventuallyConstantTo, hasLimit
-/
instance [hF : IsEventuallyConstant F] [IsCofiltered J] : HasLimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantTo
  exact h.hasLimit

end IsCofiltered

namespace IsFiltered

/--
Definition of `IsEventuallyConstant` / `IsEventuallyConstant` 的定义

English:
class IsEventuallyConstant
  parameters: : Prop where
  axioms and operations (1):
    - exists_isEventuallyConstantFrom : exists (i : J), F.IsEventuallyConstantFrom i

中文:
类 IsEventuallyConstant
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_isEventuallyConstantFrom : 存在 (i : J), F.IsEventuallyConstantFrom i
-/
class IsEventuallyConstant : Prop where
  exists_isEventuallyConstantFrom : exists (i : J), F.IsEventuallyConstantFrom i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hF
  signature: : IsEventuallyConstant F] [IsFiltered J] : HasColimit F
  body: by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantFrom
  exact h.hasColimit

中文:
实例 [hF
  签名: : IsEventuallyConstant F] [IsFiltered J] : HasColimit F
  定义体: by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantFrom
  exact h.hasColimit

Depends on / 依赖: exists_isEventuallyConstantFrom, h.hasColimit, hF.exists_isEventuallyConstantFrom, hasColimit
-/
instance [hF : IsEventuallyConstant F] [IsFiltered J] : HasColimit F := by
  obtain ⟨j, h⟩ := hF.exists_isEventuallyConstantFrom
  exact h.hasColimit

end IsFiltered

end CategoryTheory
