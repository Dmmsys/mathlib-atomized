/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# Gluing structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued presheafed space.
  This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
  can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing that `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `Mathlib/Topology/Gluing.lean`, and it
remains to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the limit of `diagram_over_open`, the components of the structure
sheaves of the spaces in the gluing diagram, we need to construct a map
`ιInvApp_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following docstrings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpace

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: extends CategoryTheory.GlueData (PresheafedSpace.{v, u, v} C)
  extends: CategoryTheory.GlueData (PresheafedSpace.{v, u, v} C)
  axioms and operations (1):
    - f_open : forall i j, IsOpenImmersion (f i j)

中文:
结构 粘合数据
  参数: extends 范畴论.粘合数据 (Presheafed空间.{v, u, v} C)
  继承: 范畴论.粘合数据 (Presheafed空间.{v, u, v} C)
  公理与运算 (1 个):
    - f_open : 对任意 i j, 是开浸入 (f i j)
-/
structure GlueData extends CategoryTheory.GlueData (PresheafedSpace.{v, u, v} C) where
  f_open : forall i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData.{v, u} C)

local notation "𝖣" => D.toGlueData

local notation "π₁ " i ", " j ", " k => pullback.fst (D.f i j) (D.f i k)

local notation "π₂ " i ", " j ", " k => pullback.snd (D.f i j) (D.f i k)

set_option quotPrecheck false
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

set_option quotPrecheck false
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

/--
Definition of `toTopGlueData` / `toTopGlueData` 的定义

English:
abbreviation toTopGlueData
  signature: : TopCat.GlueData
  body: { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }

中文:
缩写 toTopGlueData
  签名: : 顶元素范畴.粘合数据
  定义体: { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }

Depends on / 依赖: D.f_open, base_open, f_open, forget, mapGlueData, toGlueData
-/
abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ι_isOpenEmbedding` / 定理 `ι_isOpenEmbedding`

English:
theorem ι_isOpenEmbedding
  given: [HasLimits C] (i : D.J)
  statement: IsOpenEmbedding (𝖣.ι i).base
  proof: by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]; rw [TopCat.coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)

中文:
定理 ι_isOpenEmbedding
  条件: [有极限 C] (i : D.J)
  结论: 是开嵌入 (𝖣.ι i).base
  证明: by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]; rw [TopCat.coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)

Depends on / 依赖: D.toTopGlueData, PresheafedSpace, PresheafedSpace.forget, TopCat, TopCat.coe_comp, TopCat.homeoOfIso, coe_comp, forget, gluedIso, homeoOfIso, isOpenEmbedding, isOpenEmbedding.comp, toTopGlueData
-/
theorem ι_isOpenEmbedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _]; rw [TopCat.coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_base` / 定理 `pullback_base`

English:
theorem pullback_base
  given: (i j k : D.J) (S : Set (D.V (i, j)).carrier)
  proof: by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁]; rw [← eq₂]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]; rw [Set.image_preimage_eq]
  · simp only [forget_obj, forget_map, TopCat.pullback_snd_image_fst_preimage]
  rw [← TopCat.epi_iff_surjective]
  infer_instance

中文:
定理 pullback_base
  条件: (i j k : D.J) (S : 集合 (D.V (i, j)).carrier)
  证明: by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁]; rw [← eq₂]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]; rw [Set.image_preimage_eq]
  · simp only [forget_obj, forget_map, TopCat.pullback_snd_image_fst_preimage]
  rw [← TopCat.epi_iff_surjective]
  infer_instance

Depends on / 依赖: PreservesPullback, PreservesPullback.iso_hom_fst, PreservesPullback.iso_hom_snd, Set.image_comp, Set.image_preimage_eq, Set.preimage_comp, TopCat, TopCat.coe_comp, TopCat.epi_iff_surjective, TopCat.pullback_snd_image_fst_preimage, coe_comp, epi_iff_surjective, forget, forget_map, forget_obj, image_comp, image_preimage_eq, infer_instance, iso_hom_fst, iso_hom_snd
-/
theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' (π₁ i, j, k) ⁻¹' S = D.f i k ⁻¹' D.f i j '' S := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁]; rw [← eq₂]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [TopCat.coe_comp]; rw [Set.preimage_comp]; rw [Set.image_preimage_eq]
  · simp only [forget_obj, forget_map, TopCat.pullback_snd_image_fst_preimage]
  rw [← TopCat.epi_iff_surjective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
@[simp, reassoc]
/--
theorem `f_invApp_f_app` / 定理 `f_invApp_f_app`

English:
theorem f_invApp_f_app
  given: (i j k : D.J) (U : Opens (D.V (i, j)).carrier)
  proof: by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp _ U))]; rw [IsIso.inv_hom_id_assoc]; rw [IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  convert! (Category.comp_id _).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl

中文:
定理 f_invApp_f_app
  条件: (i j k : D.J) (U : Opens (D.V (i, j)).carrier)
  证明: by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp _ U))]; rw [IsIso.inv_hom_id_assoc]; rw [IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  convert! (Category.comp_id _).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl

Depends on / 依赖: Catego, Category, Category.assoc, D.f_open, Functor, Functor.map_comp_assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion, IsOpenImmersion.app_invApp_assoc, IsOpenImmersion.inv_invApp, IsOpenImmersion.inv_naturality_assoc, PresheafedSpace, PresheafedSpace.congr_app, app_invApp_assoc, c.naturality_assoc, cancel_epi, comp_c_app, condition, congr_app, convert
-/
theorem f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) :
    (D.f_open i j).invApp _ U ≫ (D.f i k).c.app _ =
      (π₁ i, j, k).c.app (op U) ≫
        (π₂⁻¹ i, j, k) (unop _) ≫
          (D.V _).presheaf.map
            (eqToHom
              (by
                delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
                dsimp only [Functor.op, IsOpenMap.functor, Opens.map, unop_op]
                congr
                apply pullback_base)) := by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp _ U))]; rw [IsIso.inv_hom_id_assoc]; rw [IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  convert! (Category.comp_id _).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `snd_invApp_t_app'` / 定理 `snd_invApp_t_app'`

English:
theorem snd_invApp_t_app'
  given: (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier)
  proof: by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
    dsimp only [Functor.op, Opens.map_def, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr 2
    have := (𝖣.t_fac k i j).symm
    rw [← IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    replace this := congr_arg (TopCat.Hom.hom ·) this
    replace this := congr_arg (ContinuousMap.toFun ·) this
    dsimp at this
    rw [this]; rw [Set.image_comp]; rw [Set.image_comp]; rw [Set.preimage_image_eq]
    swap
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [D.t_inv]; rw [id_base]; rw [ConcreteCategory.id_apply]
    refine congr_arg (_ '' ·) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.inv_hom_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.hom_inv_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    dsimp
    rw [← comp_c_app]; rw [congr_app (D.t_fac k i j)]; rw [comp_c_app]
    dsimp
    simp_rw [Category.assoc]
    rw [IsOpenImmersion.inv_naturality]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_inv_app'_assoc]
    · simp_rw [← (𝖣.V (k, i)).presheaf.map_comp]; rfl
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv]; rw [id_base]; rw [TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 3
    rw [IsIso.inv_comp_eq]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv]; rw [Category.comp_id]

中文:
定理 snd_invApp_t_app'
  条件: (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier)
  证明: by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
    dsimp only [Functor.op, Opens.map_def, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr 2
    have := (𝖣.t_fac k i j).symm
    rw [← IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    replace this := congr_arg (TopCat.Hom.hom ·) this
    replace this := congr_arg (ContinuousMap.toFun ·) this
    dsimp at this
    rw [this]; rw [Set.image_comp]; rw [Set.image_comp]; rw [Set.preimage_image_eq]
    swap
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [D.t_inv]; rw [id_base]; rw [ConcreteCategory.id_apply]
    refine congr_arg (_ '' ·) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.inv_hom_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.hom_inv_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    dsimp
    rw [← comp_c_app]; rw [congr_app (D.t_fac k i j)]; rw [comp_c_app]
    dsimp
    simp_rw [Category.assoc]
    rw [IsOpenImmersion.inv_naturality]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_inv_app'_assoc]
    · simp_rw [← (𝖣.V (k, i)).presheaf.map_comp]; rfl
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv]; rw [id_base]; rw [TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 3
    rw [IsIso.inv_comp_eq]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv]; rw [Category.comp_id]

Depends on / 依赖: fconstructor
-/
theorem snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    exists eq,
      (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eqToHom eq) =
        (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) := by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
    dsimp only [Functor.op, Opens.map_def, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr 2
    have := (𝖣.t_fac k i j).symm
    rw [← IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    replace this := congr_arg (TopCat.Hom.hom ·) this
    replace this := congr_arg (ContinuousMap.toFun ·) this
    dsimp at this
    rw [this]; rw [Set.image_comp]; rw [Set.image_comp]; rw [Set.preimage_image_eq]
    swap
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [D.t_inv]; rw [id_base]; rw [ConcreteCategory.id_apply]
    refine congr_arg (_ '' ·) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.inv_hom_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
    · intro x
      rw [← ConcreteCategory.comp_apply]; rw [← comp_base]; rw [IsIso.hom_inv_id]; rw [id_base]; rw [ConcreteCategory.id_apply]
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    dsimp
    rw [← comp_c_app]; rw [congr_app (D.t_fac k i j)]; rw [comp_c_app]
    dsimp
    simp_rw [Category.assoc]
    rw [IsOpenImmersion.inv_naturality]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_inv_app'_assoc]
    · simp_rw [← (𝖣.V (k, i)).presheaf.map_comp]; rfl
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv]; rw [id_base]; rw [TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 3
    rw [IsIso.inv_comp_eq]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv]; rw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in -- Needed in ιInvApp
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
@[simp, reassoc]
/--
theorem `snd_invApp_t_app` / 定理 `snd_invApp_t_app`

English:
theorem snd_invApp_t_app
  given: (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier)
  proof: by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]

中文:
定理 snd_invApp_t_app
  条件: (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier)
  证明: by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]

Depends on / 依赖: D.snd_invApp_t_app, choose_spec, eqToHom_map, reassoc_of, replace, snd_invApp_t_app
-/
theorem snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ =
      (D.t' k i j).c.app _ ≫
        (π₁⁻¹ k, j, i) (unop _) ≫
          (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k U).choose.symm) := by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]

variable [HasLimits C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `ι_image_preimage_eq` / 定理 `ι_image_preimage_eq`

English:
theorem ι_image_preimage_eq
  given: (i j : D.J) (U : Opens (D.U i).carrier)
  proof: by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i]; rw [←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  rw [TopCat.coe_comp]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [Set.preimage_comp]; rw [Set.preimage_image_eq]
  · refine Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) ?_
    dsimp
    rw [Set.image_comp]
    refine congr_arg (_ '' ·) ?_
    rw [Set.eq_preimage_iff_image_eq]; rw [← Set.image_comp]
    swap
    · exact CategoryTheory.ConcreteCategory.bijective_of_isIso (C := TopCat) _
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [← TopCat.mono_iff_injective]
    infer_instance

中文:
定理 ι_image_preimage_eq
  条件: (i j : D.J) (U : Opens (D.U i).carrier)
  证明: by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i]; rw [←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  rw [TopCat.coe_comp]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [Set.preimage_comp]; rw [Set.preimage_image_eq]
  · refine Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) ?_
    dsimp
    rw [Set.image_comp]
    refine congr_arg (_ '' ·) ?_
    rw [Set.eq_preimage_iff_image_eq]; rw [← Set.image_comp]
    swap
    · exact CategoryTheory.ConcreteCategory.bijective_of_isIso (C := TopCat) _
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [← TopCat.mono_iff_injective]
    infer_instance

Depends on / 依赖: D.toTopGlueData.preimage_image_eq_image, Eq.trans, IsOpenMap, IsOpenMap.coe_functor_obj, Opens.map_coe, PresheafedSpace, PresheafedSpace.forget, Set.eq_preimage_iff_image_eq, Set.image_comp, Set.preimage_comp, Set.preimage_image_eq, TopCat, TopCat.coe_comp, coe_comp, coe_functor_obj, congr_arg, eq_preimage_iff_image_eq, forget, image_comp, map_coe
-/
theorem ι_image_preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) :
    (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).functor.obj U) =
      (opensFunctor (D.f j i)).obj
        ((Opens.map (𝖣.t j i).base).obj ((Opens.map (𝖣.f i j).base).obj U)) := by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i]; rw [←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  rw [TopCat.coe_comp]; rw [TopCat.coe_comp]; rw [Set.image_comp]; rw [Set.preimage_comp]; rw [Set.preimage_image_eq]
  · refine Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) ?_
    dsimp
    rw [Set.image_comp]
    refine congr_arg (_ '' ·) ?_
    rw [Set.eq_preimage_iff_image_eq]; rw [← Set.image_comp]
    swap
    · exact CategoryTheory.ConcreteCategory.bijective_of_isIso (C := TopCat) _
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [← TopCat.mono_iff_injective]
    infer_instance

/--
Definition of `opensImagePreimageMap` / `opensImagePreimageMap` 的定义

English:
definition opensImagePreimageMap
  signature: (i j : D.J) (U : Opens (D.U i).carrier)
  body: (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp _ (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op

中文:
定义 opensImagePreimageMap
  签名: (i j : D.J) (U : Opens (D.U i).carrier)
  定义体: (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp _ (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op

Depends on / 依赖: D.f_open, c.app, eqToHom, f_open, invApp, presheaf, presheaf.map
-/
def opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶
    (D.U j).presheaf.obj (op <|
      (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).functor.obj U)) :=
  (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp _ (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op

set_option backward.isDefEq.respectTransparency false in
/--
theorem `opensImagePreimageMap_app'` / 定理 `opensImagePreimageMap_app'`

English:
theorem opensImagePreimageMap_app'
  given: (i j k : D.J) (U : Opens (D.U i).carrier)
  proof: by
  constructor
  · delta opensImagePreimageMap
    simp_rw [Category.assoc]
    rw [(D.f j k).c.naturality]; rw [f_invApp_f_app_assoc]
    · erw [← (D.V (j, k)).presheaf.map_comp]
      · simp_rw [← Category.assoc]
        erw [← comp_c_app, ← comp_c_app]
        · simp_rw [Category.assoc]
          dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
          rw [eqToHom_map (Opens.map _)]; rw [eqToHom_op]; rw [eqToHom_trans]
          congr

中文:
定理 opensImagePreimageMap_app'
  条件: (i j k : D.J) (U : Opens (D.U i).carrier)
  证明: by
  constructor
  · delta opensImagePreimageMap
    simp_rw [Category.assoc]
    rw [(D.f j k).c.naturality]; rw [f_invApp_f_app_assoc]
    · erw [← (D.V (j, k)).presheaf.map_comp]
      · simp_rw [← Category.assoc]
        erw [← comp_c_app, ← comp_c_app]
        · simp_rw [Category.assoc]
          dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
          rw [eqToHom_map (Opens.map _)]; rw [eqToHom_op]; rw [eqToHom_trans]
          congr

Depends on / 依赖: Category, Category.assoc, Functor, Functor.op, Opens.map, Quiver, Quiver.Hom.unop_op, c.naturality, comp_c_app, eqToHom_map, eqToHom_op, eqToHom_trans, f_invApp_f_app_assoc, map_comp, naturality, opensImagePreimageMap, presheaf, presheaf.map_comp, simp_rw, unop_op
-/
theorem opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) :
    exists eq,
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
        ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
          (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom eq) := by
  constructor
  · delta opensImagePreimageMap
    simp_rw [Category.assoc]
    rw [(D.f j k).c.naturality]; rw [f_invApp_f_app_assoc]
    · erw [← (D.V (j, k)).presheaf.map_comp]
      · simp_rw [← Category.assoc]
        erw [← comp_c_app, ← comp_c_app]
        · simp_rw [Category.assoc]
          dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
          rw [eqToHom_map (Opens.map _)]; rw [eqToHom_op]; rw [eqToHom_trans]
          congr

/--
theorem `opensImagePreimageMap_app` / 定理 `opensImagePreimageMap_app`

English:
theorem opensImagePreimageMap_app
  given: (i j k : D.J) (U : Opens (D.U i).carrier)
  proof: (opensImagePreimageMap_app' D i j k U).choose_spec

中文:
定理 opensImagePreimageMap_app
  条件: (i j k : D.J) (U : Opens (D.U i).carrier)
  证明: (opensImagePreimageMap_app' D i j k U).choose_spec

Depends on / 依赖: choose_spec, opensImagePreimageMap_app
-/
theorem opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).choose) :=
  (opensImagePreimageMap_app' D i j k U).choose_spec

set_option backward.isDefEq.respectTransparency false in
-- This is proved separately since `reassoc` somehow timeouts.
/--
theorem `opensImagePreimageMap_app_assoc` / 定理 `opensImagePreimageMap_app_assoc`

English:
theorem opensImagePreimageMap_app_assoc
  statement: (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
  proof: by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)

中文:
定理 opensImagePreimageMap_app_assoc
  结论: (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
  证明: by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)

Depends on / 依赖: Category, Category.assoc, congr_arg, opensImagePreimageMap_app
-/
theorem opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
    (f' : _ ⟶ X') :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map
            (eqToHom (opensImagePreimageMap_app' D i j k U).choose) ≫ f' := by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)

/--
Definition of `diagramOverOpen` / `diagramOverOpen` 的定义

English:
abbreviation diagramOverOpen
  signature: {i : D.J} (U : Opens (D.U i).carrier)
  body: componentwiseDiagram 𝖣.diagram.multispan ((D.ι_isOpenEmbedding i).functor.obj U)

中文:
缩写 diagramOverOpen
  签名: {i : D.J} (U : Opens (D.U i).carrier)
  定义体: componentwiseDiagram 𝖣.diagram.multispan ((D.ι_isOpenEmbedding i).functor.obj U)

Depends on / 依赖: componentwiseDiagram, diagram, diagram.multispan, functor, functor.obj, multispan
-/
abbrev diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) :
    (WalkingMultispan (.prod D.J))ᵒᵖ ⥤ C :=
  componentwiseDiagram 𝖣.diagram.multispan ((D.ι_isOpenEmbedding i).functor.obj U)

/--
Definition of `diagramOverOpenπ` / `diagramOverOpenπ` 的定义

English:
abbreviation diagramOverOpenπ
  signature: {i : D.J} (U : Opens (D.U i).carrier) (j : D.J)
  body: limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))

中文:
缩写 diagramOverOpenπ
  签名: {i : D.J} (U : Opens (D.U i).carrier) (j : D.J)
  定义体: limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))

Depends on / 依赖: D.diagramOverOpen, WalkingMultispan, WalkingMultispan.right, diagramOverOpen
-/
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ιInvAppπApp` / `ιInvAppπApp` 的定义

English:
definition ιInvAppπApp
  signature: {i : D.J} (U : Opens (D.U i).carrier) (j)
  body: by
  rcases j with (⟨j, k⟩ | j)
  · refine
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom ?_)
    rw [Functor.op_obj]
    congr 1; ext1
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.coe_functor_obj]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    congr 4
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
  · exact D.opensImagePreimageMap i j U

中文:
定义 ιInvAppπApp
  签名: {i : D.J} (U : Opens (D.U i).carrier) (j)
  定义体: by
  rcases j with (⟨j, k⟩ | j)
  · refine
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom ?_)
    rw [Functor.op_obj]
    congr 1; ext1
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.coe_functor_obj]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    congr 4
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
  · exact D.opensImagePreimageMap i j U

Depends on / 依赖: D.opensImagePreimageMap, Functor, Functor.op_obj, IsOpenMap, IsOpenMap.coe_functor_obj, Opens.map_coe, Set.preimage_preimage, WalkingMultispan, WalkingMultispan.Hom.fst, c.app, coe_functor_obj, colimit, colimit.w, diagram, diagram.multispan, eqToHom, map_coe, multispan, op_obj, opensImagePreimageMap
-/
def ιInvAppπApp {i : D.J} (U : Opens (D.U i).carrier) (j) :
    (𝖣.U i).presheaf.obj (op U) ⟶ (D.diagramOverOpen U).obj (op j) := by
  rcases j with (⟨j, k⟩ | j)
  · refine
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom ?_)
    rw [Functor.op_obj]
    congr 1; ext1
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.coe_functor_obj]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    congr 4
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
  · exact D.opensImagePreimageMap i j U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ιInvApp` / `ιInvApp` 的定义

English:
definition ιInvApp
  signature: {i : D.J} (U : Opens (D.U i).carrier)
  body: limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X with | op X => ?_
            induction Y with | op Y => ?_
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              congr 1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            rw [opensImagePreimageMap_app_assoc]
            simp_rw [Category.assoc]
            rw [opensImagePreimageMap_app_assoc]; rw [(D.t j k).c.naturality_assoc]; rw [snd_invApp_t_app_assoc]; rw [← PresheafedSpace.comp_c_app_assoc]
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc]; rw [𝖣.t'_comp_eq_pullbackSymmetry_assoc]; rw [pullbackSymmetry_hom_comp_snd_assoc]; rw [pullback.condition]; rw [𝖣.t_fac_assoc]
            rw [congr_app this]; rw [PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp]; rw [IsOpenImmersion.inv_invApp]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]
            simp_rw [Functor.op_obj]
            rw [← PresheafedSpace.comp_c_app_assoc]; rw [congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc, Functor.op_obj, comp_base, Opens.map_comp_obj,
              TopCat.Presheaf.pushforward_obj_map]
            rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_invApp_assoc]
            repeat rw [← (D.V (j, k)).presheaf.map_comp]
            rfl } }

中文:
定义 ιInvApp
  签名: {i : D.J} (U : Opens (D.U i).carrier)
  定义体: limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X with | op X => ?_
            induction Y with | op Y => ?_
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              congr 1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            rw [opensImagePreimageMap_app_assoc]
            simp_rw [Category.assoc]
            rw [opensImagePreimageMap_app_assoc]; rw [(D.t j k).c.naturality_assoc]; rw [snd_invApp_t_app_assoc]; rw [← PresheafedSpace.comp_c_app_assoc]
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc]; rw [𝖣.t'_comp_eq_pullbackSymmetry_assoc]; rw [pullbackSymmetry_hom_comp_snd_assoc]; rw [pullback.condition]; rw [𝖣.t_fac_assoc]
            rw [congr_app this]; rw [PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp]; rw [IsOpenImmersion.inv_invApp]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]
            simp_rw [Functor.op_obj]
            rw [← PresheafedSpace.comp_c_app_assoc]; rw [congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc, Functor.op_obj, comp_base, Opens.map_comp_obj,
              TopCat.Presheaf.pushforward_obj_map]
            rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_invApp_assoc]
            repeat rw [← (D.V (j, k)).presheaf.map_comp]
            rfl } }

Depends on / 依赖: Category, Category.id_comp, D.diagramOverOpen, Functor, Functor.const_obj_map, Functor.const_obj_obj, clear_value, const_obj_map, const_obj_obj, diagramOverOpen, f.op, id_comp, limit.lift, naturality, presheaf, presheaf.obj
-/
def ιInvApp {i : D.J} (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ limit (D.diagramOverOpen U) :=
  limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X with | op X => ?_
            induction Y with | op Y => ?_
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              congr 1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            rw [opensImagePreimageMap_app_assoc]
            simp_rw [Category.assoc]
            rw [opensImagePreimageMap_app_assoc]; rw [(D.t j k).c.naturality_assoc]; rw [snd_invApp_t_app_assoc]; rw [← PresheafedSpace.comp_c_app_assoc]
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc]; rw [𝖣.t'_comp_eq_pullbackSymmetry_assoc]; rw [pullbackSymmetry_hom_comp_snd_assoc]; rw [pullback.condition]; rw [𝖣.t_fac_assoc]
            rw [congr_app this]; rw [PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp]; rw [IsOpenImmersion.inv_invApp]; rw [Category.assoc]; rw [NatTrans.naturality_assoc]
            simp_rw [Functor.op_obj]
            rw [← PresheafedSpace.comp_c_app_assoc]; rw [congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc, Functor.op_obj, comp_base, Opens.map_comp_obj,
              TopCat.Presheaf.pushforward_obj_map]
            rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.inv_naturality_assoc]; rw [IsOpenImmersion.app_invApp_assoc]
            repeat rw [← (D.V (j, k)).presheaf.map_comp]
            rfl } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `ιInvApp_π` / 定理 `ιInvApp_π`

English:
theorem ιInvApp_π
  given: {i : D.J} (U : Opens (D.U i).carrier)
  proof: by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · congr; ext1; change _ = _ ⁻¹' _ '' _; ext1 x
    simp only [SetLike.mem_coe, unop_op, Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨y, h1, h2⟩
    convert! h1 using 1
    delta ι Multicoequalizer.π at h2
    apply_fun (D.ι _).base
    · exact h2.symm
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      dsimp at this
      rw [← this]; rw [TopCat.coe_comp]
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      rw [← TopCat.mono_iff_injective]
      infer_instance
  delta ιInvApp
  rw [limit.lift_π]
  change D.opensImagePreimageMap i i U = _
  dsimp [opensImagePreimageMap]
  rw [congr_app (D.t_id _)]; rw [id_c_app]; rw [← Functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  · simp only [eqToHom_op, ← Functor.map_comp]
    rfl
  · rw [Set.range_eq_univ.mpr _]
    · simp
    · rw [← TopCat.epi_iff_surjective]
      infer_instance

中文:
定理 ιInvApp_π
  条件: {i : D.J} (U : Opens (D.U i).carrier)
  证明: by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · congr; ext1; change _ = _ ⁻¹' _ '' _; ext1 x
    simp only [SetLike.mem_coe, unop_op, Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨y, h1, h2⟩
    convert! h1 using 1
    delta ι Multicoequalizer.π at h2
    apply_fun (D.ι _).base
    · exact h2.symm
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      dsimp at this
      rw [← this]; rw [TopCat.coe_comp]
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      rw [← TopCat.mono_iff_injective]
      infer_instance
  delta ιInvApp
  rw [limit.lift_π]
  change D.opensImagePreimageMap i i U = _
  dsimp [opensImagePreimageMap]
  rw [congr_app (D.t_id _)]; rw [id_c_app]; rw [← Functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  · simp only [eqToHom_op, ← Functor.map_comp]
    rfl
  · rw [Set.range_eq_univ.mpr _]
    · simp
    · rw [← TopCat.epi_iff_surjective]
      infer_instance

Depends on / 依赖: fconstructor
-/
theorem ιInvApp_π {i : D.J} (U : Opens (D.U i).carrier) :
    exists eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).presheaf.map (eqToHom eq) := by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · congr; ext1; change _ = _ ⁻¹' _ '' _; ext1 x
    simp only [SetLike.mem_coe, unop_op, Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨y, h1, h2⟩
    convert! h1 using 1
    delta ι Multicoequalizer.π at h2
    apply_fun (D.ι _).base
    · exact h2.symm
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      dsimp at this
      rw [← this]; rw [TopCat.coe_comp]
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      rw [← TopCat.mono_iff_injective]
      infer_instance
  delta ιInvApp
  rw [limit.lift_π]
  change D.opensImagePreimageMap i i U = _
  dsimp [opensImagePreimageMap]
  rw [congr_app (D.t_id _)]; rw [id_c_app]; rw [← Functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  · simp only [eqToHom_op, ← Functor.map_comp]
    rfl
  · rw [Set.range_eq_univ.mpr _]
    · simp
    · rw [← TopCat.epi_iff_surjective]
      infer_instance

/--
Definition of `ιInvAppπEqMap` / `ιInvAppπEqMap` 的定义

English:
abbreviation ιInvAppπEqMap
  signature: {i : D.J} (U : Opens (D.U i).carrier)
  body: (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv

中文:
缩写 ιInvAppπEqMap
  签名: {i : D.J} (U : Opens (D.U i).carrier)
  定义体: (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv

Depends on / 依赖: eqToIso, presheaf, presheaf.map
-/
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `π_ιInvApp_π` / 定理 `π_ιInvApp_π`

English:
theorem π_ιInvApp_π
  given: (i j : D.J) (U : Opens (D.U i).carrier)
  proof: by
  rw [← @cancel_mono
          (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
            (Quiver.Hom.op (WalkingMultispan.Hom.snd (i]; rw [j))) ≫ 𝟙 _) ..]
  · simp_rw [Category.assoc]
    rw [limit.w_assoc]
    erw [limit.lift_π_assoc]
    rw [Category.comp_id]; rw [Category.comp_id]
    change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
    rw [congr_app (D.t_id _)]; rw [id_c_app]
    simp_rw [Category.assoc]
    rw [← Functor.map_comp_assoc]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [IsOpenImmersion.inv_naturality_assoc]
    erw [IsOpenImmersion.app_invApp_assoc]
    iterate 3 rw [← Functor.map_comp_assoc]
    rw [NatTrans.naturality_assoc]
    erw [← (D.V (i, j)).presheaf.map_comp]
    convert!
      limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
  · rw [Category.comp_id]
    apply +allowSynthFailures mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply +allowSynthFailures mono_comp
    · erw [D.ι_image_preimage_eq i j U]
      infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance

中文:
定理 π_ιInvApp_π
  条件: (i j : D.J) (U : Opens (D.U i).carrier)
  证明: by
  rw [← @cancel_mono
          (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
            (Quiver.Hom.op (WalkingMultispan.Hom.snd (i]; rw [j))) ≫ 𝟙 _) ..]
  · simp_rw [Category.assoc]
    rw [limit.w_assoc]
    erw [limit.lift_π_assoc]
    rw [Category.comp_id]; rw [Category.comp_id]
    change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
    rw [congr_app (D.t_id _)]; rw [id_c_app]
    simp_rw [Category.assoc]
    rw [← Functor.map_comp_assoc]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [IsOpenImmersion.inv_naturality_assoc]
    erw [IsOpenImmersion.app_invApp_assoc]
    iterate 3 rw [← Functor.map_comp_assoc]
    rw [NatTrans.naturality_assoc]
    erw [← (D.V (i, j)).presheaf.map_comp]
    convert!
      limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
  · rw [Category.comp_id]
    apply +allowSynthFailures mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply +allowSynthFailures mono_comp
    · erw [D.ι_image_preimage_eq i j U]
      infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance

Depends on / 依赖: Category, Category.assoc, Category.comp_id, D.t_id, Functor, Functor.map_comp_assoc, Quiver, Quiver.Hom.op, WalkingMultispan, WalkingMultispan.Hom.snd, cancel_mono, comp_id, componentwiseDiagram, congr_app, diagram, diagram.multispan, id_c_app, limit.lift_, limit.w_assoc, map_comp_assoc
-/
theorem π_ιInvApp_π (i j : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U ≫ D.diagramOverOpenπ U j =
      D.diagramOverOpenπ U j := by
  rw [← @cancel_mono
          (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
            (Quiver.Hom.op (WalkingMultispan.Hom.snd (i]; rw [j))) ≫ 𝟙 _) ..]
  · simp_rw [Category.assoc]
    rw [limit.w_assoc]
    erw [limit.lift_π_assoc]
    rw [Category.comp_id]; rw [Category.comp_id]
    change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
    rw [congr_app (D.t_id _)]; rw [id_c_app]
    simp_rw [Category.assoc]
    rw [← Functor.map_comp_assoc]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [IsOpenImmersion.inv_naturality_assoc]
    erw [IsOpenImmersion.app_invApp_assoc]
    iterate 3 rw [← Functor.map_comp_assoc]
    rw [NatTrans.naturality_assoc]
    erw [← (D.V (i, j)).presheaf.map_comp]
    convert!
      limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
  · rw [Category.comp_id]
    apply +allowSynthFailures mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply +allowSynthFailures mono_comp
    · erw [D.ι_image_preimage_eq i j U]
      infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `π_ιInvApp_eq_id` / 定理 `π_ιInvApp_eq_id`

English:
theorem π_ιInvApp_eq_id
  given: (i : D.J) (U : Opens (D.U i).carrier)
  proof: by
  ext j
  induction j with | op j => ?_
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ιInvApp_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ιInvApp_π

中文:
定理 π_ιInvApp_eq_id
  条件: (i : D.J) (U : Opens (D.U i).carrier)
  证明: by
  ext j
  induction j with | op j => ?_
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ιInvApp_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ιInvApp_π

Depends on / 依赖: Category, Category.assoc, Category.id_comp, Quiver, Quiver.Hom.op, WalkingMultispan, WalkingMultispan.Hom.fst, componentwiseDiagram, diagram, diagram.multispan, id_comp, limit.w, multispan, simp_rw
-/
theorem π_ιInvApp_eq_id (i : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U = 𝟙 _ := by
  ext j
  induction j with | op j => ?_
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ιInvApp_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ιInvApp_π

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `componentwise_diagram_π_isIso` / 实例 `componentwise_diagram_π_isIso`

English:
instance componentwise_diagram_π_isIso
  signature: (i : D.J) (U : Opens (D.U i).carrier)
  body: by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  constructor
  · apply π_ιInvApp_eq_id
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))

中文:
实例 componentwise_diagram_π_isIso
  签名: (i : D.J) (U : Opens (D.U i).carrier)
  定义体: by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  constructor
  · apply π_ιInvApp_eq_id
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id, choose_spec, eqToIso, inv_hom_id, mapIso, presheaf, presheaf.mapIso
-/
instance componentwise_diagram_π_isIso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) := by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  constructor
  · apply π_ιInvApp_eq_id
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ιIsOpenImmersion` / 实例 `ιIsOpenImmersion`

English:
instance ιIsOpenImmersion
  signature: (i : D.J)
  body: D.ι_isOpenEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance

中文:
实例 ιIsOpenImmersion
  签名: (i : D.J)
  定义体: D.ι_isOpenEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance
-/
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) where
  base_open := D.ι_isOpenEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `vPullbackConeIsLimit` / `vPullbackConeIsLimit` 的定义

English:
definition vPullbackConeIsLimit
  signature: (i j : D.J)
  body: PullbackCone.isLimitAux' _ fun s => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst ?_
      erw [← D.toTopGlueData.preimage_range j i]
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]; rw [←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base]; rw [comp_base] at this
        replace this := reassoc_of% this
        exact this _
      simp only [mapGlueData_U, forget_obj]
      rw [← Set.image_subset_iff]; rw [← Set.image_univ]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [← TopCat.coe_comp]; rw [this]; rw [TopCat.coe_comp]; rw [← Set.image_univ]; rw [Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ _
      rw [← cancel_mono (D.f i j)]
      simp only [lift_fac]
      tauto

中文:
定义 vPullbackConeIsLimit
  签名: (i j : D.J)
  定义体: PullbackCone.isLimitAux' _ fun s => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst ?_
      erw [← D.toTopGlueData.preimage_range j i]
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]; rw [←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base]; rw [comp_base] at this
        replace this := reassoc_of% this
        exact this _
      simp only [mapGlueData_U, forget_obj]
      rw [← Set.image_subset_iff]; rw [← Set.image_univ]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [← TopCat.coe_comp]; rw [this]; rw [TopCat.coe_comp]; rw [← Set.image_univ]; rw [Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ _
      rw [← cancel_mono (D.f i j)]
      simp only [lift_fac]
      tauto

Depends on / 依赖: D.toTopGlueData, D.toTopGlueData.preimage_range, IsOpenImmersion, PresheafedSpace, PresheafedSpace.Hom.base, PresheafedSpace.IsOpenImmersion.lift, PresheafedSpace.forget, PullbackCone, PullbackCone.isLimitAux, comp_base, condition, congr_arg, forget, isLimitAux, preimage_range, reassoc_of, replace, s.condition, s.fst, s.fst.base
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst ?_
      erw [← D.toTopGlueData.preimage_range j i]
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]; rw [←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base]; rw [comp_base] at this
        replace this := reassoc_of% this
        exact this _
      simp only [mapGlueData_U, forget_obj]
      rw [← Set.image_subset_iff]; rw [← Set.image_univ]; rw [← Set.image_comp]; rw [Set.image_univ]; rw [← TopCat.coe_comp]; rw [this]; rw [TopCat.coe_comp]; rw [← Set.image_univ]; rw [Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ _
      rw [← cancel_mono (D.f i j)]
      simp only [lift_fac]
      tauto

/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  given: (x : 𝖣.glued)
  statement: exists (i : D.J) (y : D.U i), (𝖣.ι i).base y = x
  proof: 𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

中文:
定理 ι_jointly_surjective
  条件: (x : 𝖣.glued)
  结论: 存在 (i : D.J) (y : D.U i), (𝖣.ι i).base y = x
  证明: 𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, PresheafedSpace, PresheafedSpace.forget, TopCat, forget
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : exists (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

end GlueData

end PresheafedSpace

namespace SheafedSpace

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: extends CategoryTheory.GlueData (SheafedSpace.{u, v, v} C)
  extends: CategoryTheory.GlueData (SheafedSpace.{u, v, v} C)
  axioms and operations (1):
    - f_open : forall i j, SheafedSpace.IsOpenImmersion (f i j)

中文:
结构 粘合数据
  参数: extends 范畴论.粘合数据 (Sheafed空间.{u, v, v} C)
  继承: 范畴论.粘合数据 (Sheafed空间.{u, v, v} C)
  公理与运算 (1 个):
    - f_open : 对任意 i j, Sheafed空间.是开浸入 (f i j)
-/
structure GlueData extends CategoryTheory.GlueData (SheafedSpace.{u, v, v} C) where
  f_open : forall i j, SheafedSpace.IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData C)

local notation "𝖣" => D.toGlueData

/--
Definition of `toPresheafedSpaceGlueData` / `toPresheafedSpaceGlueData` 的定义

English:
abbreviation toPresheafedSpaceGlueData
  signature: : PresheafedSpace.GlueData C
  body: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }

中文:
缩写 toPresheafedSpaceGlueData
  签名: : Presheafed空间.粘合数据 C
  定义体: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }

Depends on / 依赖: D.f_open, f_open, forgetToPresheafedSpace, mapGlueData, toGlueData
-/
abbrev toPresheafedSpaceGlueData : PresheafedSpace.GlueData C :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }

variable [HasLimits C]

/--
Definition of `isoPresheafedSpace` / `isoPresheafedSpace` 的定义

English:
abbreviation isoPresheafedSpace
  signature: :
  body: 𝖣.gluedIso forgetToPresheafedSpace

中文:
缩写 isoPresheafedSpace
  签名: :
  定义体: 𝖣.gluedIso forgetToPresheafedSpace

Depends on / 依赖: forgetToPresheafedSpace, gluedIso
-/
abbrev isoPresheafedSpace :
    𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToPresheafedSpace

/--
theorem `ι_isoPresheafedSpace_inv` / 定理 `ι_isoPresheafedSpace_inv`

English:
theorem ι_isoPresheafedSpace_inv
  given: (i : D.J)
  proof: 𝖣.ι_gluedIso_inv _ _

中文:
定理 ι_isoPresheafedSpace_inv
  条件: (i : D.J)
  证明: 𝖣.ι_gluedIso_inv _ _
-/
theorem ι_isoPresheafedSpace_inv (i : D.J) :
    D.toPresheafedSpaceGlueData.toGlueData.ι i ≫ D.isoPresheafedSpace.inv = (𝖣.ι i).hom :=
  𝖣.ι_gluedIso_inv _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ιIsOpenImmersion` / 实例 `ιIsOpenImmersion`

English:
instance ιIsOpenImmersion
  signature: (i : D.J)
  body: by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoPresheafedSpace_inv]
  have := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i
  infer_instance

中文:
实例 ιIsOpenImmersion
  签名: (i : D.J)
  定义体: by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoPresheafedSpace_inv]
  have := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i
  infer_instance

Depends on / 依赖: D.toPresheafedSpaceGlueData, IsOpenImmersion, infer_instance, toPresheafedSpaceGlueData
-/
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoPresheafedSpace_inv]
  have := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i
  infer_instance

/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  given: (x : 𝖣.glued)
  statement: exists (i : D.J) (y : D.U i), (𝖣.ι i).hom.base y = x
  proof: 𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

中文:
定理 ι_jointly_surjective
  条件: (x : 𝖣.glued)
  结论: 存在 (i : D.J) (y : D.U i), (𝖣.ι i).hom.base y = x
  证明: 𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, SheafedSpace, SheafedSpace.forget, TopCat, forget
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : exists (i : D.J) (y : D.U i), (𝖣.ι i).hom.base y = x :=
  𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

/--
Definition of `vPullbackConeIsLimit` / `vPullbackConeIsLimit` 的定义

English:
definition vPullbackConeIsLimit
  signature: (i j : D.J)
  body: 𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)

中文:
定义 vPullbackConeIsLimit
  签名: (i j : D.J)
  定义体: 𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)

Depends on / 依赖: D.toPresheafedSpaceGlueData.vPullbackConeIsLimit, forgetToPresheafedSpace, toPresheafedSpaceGlueData, vPullbackConeIsLimit, vPullbackConeIsLimitOfMap
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)

end GlueData

end SheafedSpace

namespace LocallyRingedSpace

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: extends CategoryTheory.GlueData LocallyRingedSpace
  extends: CategoryTheory.GlueData LocallyRingedSpace
  axioms and operations (1):
    - f_open : forall i j, LocallyRingedSpace.IsOpenImmersion (f i j)

中文:
结构 粘合数据
  参数: extends 范畴论.粘合数据 LocallyRinged空间
  继承: 范畴论.粘合数据 LocallyRinged空间
  公理与运算 (1 个):
    - f_open : 对任意 i j, LocallyRinged空间.是开浸入 (f i j)
-/
structure GlueData extends CategoryTheory.GlueData LocallyRingedSpace where
  f_open : forall i j, LocallyRingedSpace.IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/--
Definition of `toSheafedSpaceGlueData` / `toSheafedSpaceGlueData` 的定义

English:
abbreviation toSheafedSpaceGlueData
  signature: : SheafedSpace.GlueData CommRingCat
  body: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }

中文:
缩写 toSheafedSpaceGlueData
  签名: : Sheafed空间.粘合数据 交换环范畴
  定义体: { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }

Depends on / 依赖: D.f_open, f_open, forgetToSheafedSpace, mapGlueData, toGlueData
-/
abbrev toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }

/--
Definition of `isoSheafedSpace` / `isoSheafedSpace` 的定义

English:
abbreviation isoSheafedSpace
  signature: : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued
  body: 𝖣.gluedIso forgetToSheafedSpace

@[reassoc]

中文:
缩写 isoSheafedSpace
  签名: : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued
  定义体: 𝖣.gluedIso forgetToSheafedSpace

@[reassoc]

Depends on / 依赖: forgetToSheafedSpace, gluedIso
-/
abbrev isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToSheafedSpace

@[reassoc]
/--
theorem `ι_isoSheafedSpace_inv` / 定理 `ι_isoSheafedSpace_inv`

English:
theorem ι_isoSheafedSpace_inv
  given: (i : D.J)
  proof: 𝖣.ι_gluedIso_inv forgetToSheafedSpace i

中文:
定理 ι_isoSheafedSpace_inv
  条件: (i : D.J)
  证明: 𝖣.ι_gluedIso_inv forgetToSheafedSpace i

Depends on / 依赖: forgetToSheafedSpace
-/
theorem ι_isoSheafedSpace_inv (i : D.J) :
    D.toSheafedSpaceGlueData.toGlueData.ι i ≫ D.isoSheafedSpace.inv =
      (𝖣.ι i).toShHom :=
  𝖣.ι_gluedIso_inv forgetToSheafedSpace i

/--
Instance `ι_isOpenImmersion` / 实例 `ι_isOpenImmersion`

English:
instance ι_isOpenImmersion
  signature: (i : D.J)
  body: by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoSheafedSpace_inv]
  -- Porting note: the next lines were a single `apply_instance`
  apply +allowSynthFailures PresheafedSpace.IsOpenImmersion.comp
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i

中文:
实例 ι_isOpenImmersion
  签名: (i : D.J)
  定义体: by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoSheafedSpace_inv]
  -- Porting note: the next lines were a single `apply_instance`
  apply +allowSynthFailures PresheafedSpace.IsOpenImmersion.comp
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i

Depends on / 依赖: IsOpenImmersion
-/
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoSheafedSpace_inv]
  -- Porting note: the next lines were a single `apply_instance`
  apply +allowSynthFailures PresheafedSpace.IsOpenImmersion.comp
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i

instance (i j k : D.J) : PreservesLimit (cospan (𝖣.f i j) (𝖣.f i k)) forgetToSheafedSpace :=
  inferInstance

/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  given: (x : 𝖣.glued)
  statement: exists (i : D.J) (y : D.U i), (𝖣.ι i).base y = x
  proof: 𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCat.{u}) ⋙
      forget TopCat.{u}) x

中文:
定理 ι_jointly_surjective
  条件: (x : 𝖣.glued)
  结论: 存在 (i : D.J) (y : D.U i), (𝖣.ι i).base y = x
  证明: 𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCat.{u}) ⋙
      forget TopCat.{u}) x

Depends on / 依赖: CommRingCat, LocallyRingedSpace, LocallyRingedSpace.forgetToSheafedSpace, SheafedSpace, SheafedSpace.forget, TopCat, forget, forgetToSheafedSpace
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : exists (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCat.{u}) ⋙
      forget TopCat.{u}) x

/--
Definition of `vPullbackConeIsLimit` / `vPullbackConeIsLimit` 的定义

English:
definition vPullbackConeIsLimit
  signature: (i j : D.J)
  body: 𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)

中文:
定义 vPullbackConeIsLimit
  签名: (i j : D.J)
  定义体: 𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)

Depends on / 依赖: D.toSheafedSpaceGlueData.vPullbackConeIsLimit, forgetToSheafedSpace, toSheafedSpaceGlueData, vPullbackConeIsLimit, vPullbackConeIsLimitOfMap
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)

end GlueData

end LocallyRingedSpace

end AlgebraicGeometry
