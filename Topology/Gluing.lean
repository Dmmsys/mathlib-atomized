/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.GlueData
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Gluing Topological spaces

Given a family of gluing data (see `Mathlib/CategoryTheory/GlueData.lean`), we can then glue them
together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `TopCat.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `TopCat.GlueData.Rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `TopCat.GlueData.ι_eq_iff_rel`.
* `TopCat.GlueData.mk`: A constructor of `GlueData` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `TopCat.GlueData.ofOpenSubsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`TopCat.GlueData.openCoverGlueHomeo`).

## Main results

* `TopCat.GlueData.isOpen_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `TopCat.GlueData.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `TopCat.GlueData.rel_equiv`: `Rel` is an equivalence relation.
* `TopCat.GlueData.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `TopCat.GlueData.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `TopCat.GlueData.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `TopCat.GlueData.preimage_image_eq_image`: The preimage of the image of some `U ⊆ U i` is
    given by XXX.
* `TopCat.GlueData.ι_isOpenEmbedding`: Each of the `ι i`s are open embeddings.

-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe v u

open CategoryTheory.Limits

namespace TopCat

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: extends CategoryTheory.GlueData TopCat
  extends: CategoryTheory.GlueData TopCat
  axioms and operations (2):
    - f_open : forall i j, IsOpenEmbedding (f i j)
    - f_mono(i j) : = (TopCat.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective

中文:
结构 粘合数据
  参数: extends 范畴论.粘合数据 顶元素范畴
  继承: 范畴论.粘合数据 顶元素范畴
  公理与运算 (2 个):
    - f_open : 对任意 i j, 是开嵌入 (f i j)
    - f_mono(i j) : = (顶元素范畴.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective

Depends on / 依赖: TopCat, TopCat.mono_iff_injective, f_open, injective, isEmbedding, isEmbedding.injective, mono_iff_injective
-/
structure GlueData extends CategoryTheory.GlueData TopCat where
  f_open : forall i j, IsOpenEmbedding (f i j)
  f_mono i j := (TopCat.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/--
theorem `π_surjective` / 定理 `π_surjective`

English:
theorem π_surjective
  statement: Function.Surjective 𝖣.π
  proof: (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance

中文:
定理 π_surjective
  结论: 函数.满射 𝖣.π
  证明: (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance

Depends on / 依赖: TopCat, TopCat.epi_iff_surjective, epi_iff_surjective
-/
theorem π_surjective : Function.Surjective 𝖣.π :=
  (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: (U : Set 𝖣.glued)
  statement: IsOpen U ↔ forall i, IsOpen (𝖣.ι i ⁻¹' U)
  proof: by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff]; rw [colimit_isOpen_iff.{u}]
  tauto

中文:
定理 isOpen_iff
  条件: (U : 集合 𝖣.glued)
  结论: 是开集 U ↔ 对任意 i, 是开集 (𝖣.ι i ⁻¹' U)
  证明: by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff]; rw [colimit_isOpen_iff.{u}]
  tauto

Depends on / 依赖: CategoryTheory, CategoryTheory.GlueData, GlueData, Multicoequalizer, Multicoequalizer.isoCoequalizer, coequalizer_isOpen_iff, colimit_isOpen_iff, diagram, homeoOfIso, isOpen_preimage, isoCoequalizer, simp_rw
-/
theorem isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ forall i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff]; rw [colimit_isOpen_iff.{u}]
  tauto

/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  given: (x : 𝖣.glued)
  statement: exists (i : _) (y : D.U i), 𝖣.ι i y = x
  proof: 𝖣.ι_jointly_surjective (forget TopCat) x

中文:
定理 ι_jointly_surjective
  条件: (x : 𝖣.glued)
  结论: 存在 (i : _) (y : D.U i), 𝖣.ι i y = x
  证明: 𝖣.ι_jointly_surjective (forget TopCat) x

Depends on / 依赖: TopCat, forget
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : exists (i : _) (y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget TopCat) x

/--
Definition of `Rel` / `Rel` 的定义

English:
definition Rel
  signature: (a b : Σ i, ((D.U i : TopCat) : Type _))
  body: exists x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

中文:
定义 关系
  签名: (a b : Σ i, ((D.U i : 顶元素范畴) : 类型 _))
  定义体: exists x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2
-/
def Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop :=
  exists x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

/--
theorem `rel_equiv` / 定理 `rel_equiv`

English:
theorem rel_equiv
  statement: Equivalence D.Rel
  proof: ⟨fun x => ⟨inv (D.f _ _) x.2, IsIso.inv_hom_id_apply (D.f x.fst x.fst) _,
    by simp [IsIso.inv_hom_id_apply (D.f x.fst x.fst)]⟩, by
    rintro a b ⟨x, e₁, e₂⟩
    exact ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩, by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ⟨x, e₁, e₂⟩
    rintro ⟨y, e₃, e₄⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      rw [pullbackIsoProdSubtype_inv_fst_apply]; rw [D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp +instances only at *
    subst eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨CategoryTheory.congr_fun h₁ z, CategoryTheory.congr_fun h₂ z⟩⟩

中文:
定理 rel_equiv
  结论: 等价 D.关系
  证明: ⟨fun x => ⟨inv (D.f _ _) x.2, IsIso.inv_hom_id_apply (D.f x.fst x.fst) _,
    by simp [IsIso.inv_hom_id_apply (D.f x.fst x.fst)]⟩, by
    rintro a b ⟨x, e₁, e₂⟩
    exact ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩, by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ⟨x, e₁, e₂⟩
    rintro ⟨y, e₃, e₄⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      rw [pullbackIsoProdSubtype_inv_fst_apply]; rw [D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp +instances only at *
    subst eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨CategoryTheory.congr_fun h₁ z, CategoryTheory.congr_fun h₂ z⟩⟩

Depends on / 依赖: D.t_inv_apply, IsIso.inv_hom_id_apply, coe_of, inv_hom_id_apply, pullback, pullback.fst, pullbackIsoProdSubtype, pullbackIsoProdSubtype_inv_fst_apply, t_inv_apply, x.fst
-/
theorem rel_equiv : Equivalence D.Rel :=
  ⟨fun x => ⟨inv (D.f _ _) x.2, IsIso.inv_hom_id_apply (D.f x.fst x.fst) _,
    by simp [IsIso.inv_hom_id_apply (D.f x.fst x.fst)]⟩, by
    rintro a b ⟨x, e₁, e₂⟩
    exact ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩, by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ⟨x, e₁, e₂⟩
    rintro ⟨y, e₃, e₄⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      rw [pullbackIsoProdSubtype_inv_fst_apply]; rw [D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp +instances only at *
    subst eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc]; rw [𝖣.t_fac_assoc]; rw [𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨CategoryTheory.congr_fun h₁ z, CategoryTheory.congr_fun h₂ z⟩⟩

open CategoryTheory.Limits.WalkingParallelPair

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eqvGen_of_π_eq` / 定理 `eqvGen_of_π_eq`

English:
theorem eqvGen_of_π_eq
  proof: by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h : coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap x =
      coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap y :=
    (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π] at h
    rw [← ι_preservesColimitIso_hom]; rw [ConcreteCategory.forget_map_eq_ofHom]; rw [types_comp_apply]
    simp_all
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  simp only [eqToHom_refl, colimit.ι_map_assoc, diagramIsoParallelPair_hom_app,
    colimit.isoColimitCocone_ι_hom, Category.id_comp] at this
  exact Quot.eq.1 this

中文:
定理 eqvGen_of_π_eq
  证明: by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h : coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap x =
      coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap y :=
    (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π] at h
    rw [← ι_preservesColimitIso_hom]; rw [ConcreteCategory.forget_map_eq_ofHom]; rw [types_comp_apply]
    simp_all
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  simp only [eqToHom_refl, colimit.ι_map_assoc, diagramIsoParallelPair_hom_app,
    colimit.isoColimitCocone_ι_hom, Category.id_comp] at this
  exact Quot.eq.1 this

Depends on / 依赖: D.diagram.fstSigmaMap, D.diagram.sndSigmaMap, GlueData, Multicoequalizer, Multicoequalizer.isoCoequalizer, Multicoequalizer.sigma, TopCat, TopCat.mono_iff_injective, coequalizer, colimit, diagram, diagram.fstSigmaMap, diagram.sndSigmaMap, forget, fstSigmaMap, isoCoequalizer, mono_iff_injective, parallelPair, replace, sndSigmaMap
-/
theorem eqvGen_of_π_eq
    {x y : ↑(∐ D.U)} (h : 𝖣.π x = 𝖣.π y) :
    Relation.EqvGen
      (Function.Coequalizer.Rel 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap) x y := by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h : coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap x =
      coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap y :=
    (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π] at h
    rw [← ι_preservesColimitIso_hom]; rw [ConcreteCategory.forget_map_eq_ofHom]; rw [types_comp_apply]
    simp_all
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  simp only [eqToHom_refl, colimit.ι_map_assoc, diagramIsoParallelPair_hom_app,
    colimit.isoColimitCocone_ι_hom, Category.id_comp] at this
  exact Quot.eq.1 this

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ι_eq_iff_rel` / 定理 `ι_eq_iff_rel`

English:
theorem ι_eq_iff_rel
  given: (i j : D.J) (x : D.U i) (y : D.U j)
  proof: by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine Relation.EqvGen.mono ?_ _ _ (D.eqvGen_of_π_eq h :)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    rw [sigmaIsoSigma_inv_apply]
    -- `rw [← ConcreteCategory.comp_apply]` succeeds but rewrites the wrong expression
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc]
      -- previous line now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact ⟨y, ⟨rfl, rfl⟩⟩
  · rintro ⟨z, e₁, e₂⟩
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂] at *
    rw [D.glue_condition_apply]

中文:
定理 ι_eq_iff_rel
  条件: (i j : D.J) (x : D.U i) (y : D.U j)
  证明: by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine Relation.EqvGen.mono ?_ _ _ (D.eqvGen_of_π_eq h :)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    rw [sigmaIsoSigma_inv_apply]
    -- `rw [← ConcreteCategory.comp_apply]` succeeds but rewrites the wrong expression
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc]
      -- previous line now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact ⟨y, ⟨rfl, rfl⟩⟩
  · rintro ⟨z, e₁, e₂⟩
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂] at *
    rw [D.glue_condition_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, D.Rel, D.eqvGen_of_, D.rel_equiv, EqvGen, GlueData, InvImage, InvImage.equivalence, Multicoequalizer, Relation, Relation.EqvGen.mono, Sigma.mk, congr_hom, equivalence, eqvGen_iff, inv_hom_id, rel_equiv, sigmaIsoSigma, simp_rw
-/
theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_]; rw [u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine Relation.EqvGen.mono ?_ _ _ (D.eqvGen_of_π_eq h :)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    rw [sigmaIsoSigma_inv_apply]
    -- `rw [← ConcreteCategory.comp_apply]` succeeds but rewrites the wrong expression
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc]
      -- previous line now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact ⟨y, ⟨rfl, rfl⟩⟩
  · rintro ⟨z, e₁, e₂⟩
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂] at *
    rw [D.glue_condition_apply]

/--
theorem `ι_injective` / 定理 `ι_injective`

English:
theorem ι_injective
  given: (i : D.J)
  statement: Function.Injective (𝖣.ι i)
  proof: by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with ⟨_, e₁, e₂⟩
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂]
    simp

中文:
定理 ι_injective
  条件: (i : D.J)
  结论: 函数.单射 (𝖣.ι i)
  证明: by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with ⟨_, e₁, e₂⟩
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂]
    simp
-/
theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with ⟨_, e₁, e₂⟩
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁]; rw [← e₂]
    simp

/--
Instance `ι_mono` / 实例 `ι_mono`

English:
instance ι_mono
  signature: (i : D.J)
  body: (TopCat.mono_iff_injective _).mpr (D.ι_injective _)

中文:
实例 ι_mono
  签名: (i : D.J)
  定义体: (TopCat.mono_iff_injective _).mpr (D.ι_injective _)

Depends on / 依赖: TopCat, TopCat.mono_iff_injective, mono_iff_injective
-/
instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)

/--
theorem `image_inter` / 定理 `image_inter`

English:
theorem image_inter
  given: (i j : D.J)
  proof: by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · subst eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx

中文:
定理 image_inter
  条件: (i j : D.J)
  证明: by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · subst eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx

Depends on / 依赖: D.glue_condition_apply, glue_condition_apply
-/
theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) inter Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · subst eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx

/--
theorem `preimage_range` / 定理 `preimage_range`

English:
theorem preimage_range
  given: (i j : D.J)
  statement: 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i)
  proof: by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j)]; rw [← Set.image_univ]; rw [←
    Set.image_univ]; rw [← Set.image_comp]; rw [← coe_comp]; rw [Set.image_univ]; rw [Set.image_univ]; rw [← image_inter]; rw [Set.preimage_range_inter]

中文:
定理 preimage_range
  条件: (i j : D.J)
  结论: 𝖣.ι j ⁻¹' 集合.range (𝖣.ι i) = 集合.range (D.f j i)
  证明: by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j)]; rw [← Set.image_univ]; rw [←
    Set.image_univ]; rw [← Set.image_comp]; rw [← coe_comp]; rw [Set.image_univ]; rw [Set.image_univ]; rw [← image_inter]; rw [Set.preimage_range_inter]

Depends on / 依赖: Set.image_comp, Set.image_univ, Set.preimage_image_eq, Set.preimage_range_inter, Set.range, coe_comp, image_comp, image_inter, image_univ, preimage_image_eq, preimage_range_inter
-/
theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j)]; rw [← Set.image_univ]; rw [←
    Set.image_univ]; rw [← Set.image_comp]; rw [← coe_comp]; rw [Set.image_univ]; rw [Set.image_univ]; rw [← image_inter]; rw [Set.preimage_range_inter]

/--
theorem `preimage_image_eq_image` / 定理 `preimage_image_eq_image`

English:
theorem preimage_image_eq_image
  given: (i j : D.J) (U : Set (𝖣.U i))
  proof: by
  have : D.f _ _ ⁻¹' 𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    simp
  rw [← this]; rw [Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)

中文:
定理 preimage_image_eq_image
  条件: (i j : D.J) (U : 集合 (𝖣.U i))
  证明: by
  have : D.f _ _ ⁻¹' 𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    simp
  rw [← this]; rw [Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)

Depends on / 依赖: D.preimage_range, Set.image_preimage_eq_inter_range, Set.image_subset_range, Set.inter_eq_self_of_subset_left, Set.preimage_image_eq, Set.preimage_mono, conv_rhs, image_preimage_eq_inter_range, image_subset_range, inter_eq_self_of_subset_left, preimage_image_eq, preimage_mono, preimage_range
-/
theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' 𝖣.ι i '' U = D.f _ _ '' (D.t j i ≫ D.f _ _) ⁻¹' U := by
  have : D.f _ _ ⁻¹' 𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    simp
  rw [← this]; rw [Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)

/--
theorem `preimage_image_eq_image'` / 定理 `preimage_image_eq_image'`

English:
theorem preimage_image_eq_image'
  given: (i j : D.J) (U : Set (𝖣.U i))
  proof: by
  convert! D.preimage_image_eq_image i j U using 1
  rw [coe_comp]; rw [coe_comp]; rw [Set.image_comp]
  congr! 1
  rw [← Set.eq_preimage_iff_image_eq]; rw [Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [bijective_iff_isIso_ofHom]
  apply (forget TopCat).map_isIso

中文:
定理 preimage_image_eq_image'
  条件: (i j : D.J) (U : 集合 (𝖣.U i))
  证明: by
  convert! D.preimage_image_eq_image i j U using 1
  rw [coe_comp]; rw [coe_comp]; rw [Set.image_comp]
  congr! 1
  rw [← Set.eq_preimage_iff_image_eq]; rw [Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [bijective_iff_isIso_ofHom]
  apply (forget TopCat).map_isIso

Depends on / 依赖: D.preimage_image_eq_image, Set.eq_preimage_iff_image_eq, Set.image_comp, Set.preimage_preimage, TopCat, bijective_iff_isIso_ofHom, coe_comp, convert, eq_preimage_iff_image_eq, forget, image_comp, map_isIso, preimage_image_eq_image, preimage_preimage, t_inv_assoc
-/
theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t i j ≫ D.f _ _) '' D.f _ _ ⁻¹' U := by
  convert! D.preimage_image_eq_image i j U using 1
  rw [coe_comp]; rw [coe_comp]; rw [Set.image_comp]
  congr! 1
  rw [← Set.eq_preimage_iff_image_eq]; rw [Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [bijective_iff_isIso_ofHom]
  apply (forget TopCat).map_isIso

/--
theorem `open_image_open` / 定理 `open_image_open`

English:
theorem open_image_open
  given: (i : D.J) (U : Opens (𝖣.U i))
  statement: IsOpen (𝖣.ι i '' U)
  proof: by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).hom.continuous_toFun.isOpen_preimage
  exact U.isOpen

中文:
定理 open_image_open
  条件: (i : D.J) (U : Opens (𝖣.U i))
  结论: 是开集 (𝖣.ι i '' U)
  证明: by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).hom.continuous_toFun.isOpen_preimage
  exact U.isOpen

Depends on / 依赖: D.f_open, U.isOpen, continuous_toFun, f_open, hom.continuous_toFun.isOpen_preimage, isOpen, isOpenMap, isOpen_iff, isOpen_preimage, preimage_image_eq_image
-/
theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' U) := by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).hom.continuous_toFun.isOpen_preimage
  exact U.isOpen

/--
theorem `ι_isOpenEmbedding` / 定理 `ι_isOpenEmbedding`

English:
theorem ι_isOpenEmbedding
  given: (i : D.J)
  statement: IsOpenEmbedding (𝖣.ι i)
  proof: .of_continuous_injective_isOpenMap (𝖣.ι i).hom.continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

中文:
定理 ι_isOpenEmbedding
  条件: (i : D.J)
  结论: 是开嵌入 (𝖣.ι i)
  证明: .of_continuous_injective_isOpenMap (𝖣.ι i).hom.continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

Depends on / 依赖: D.open_image_open, continuous_toFun, hom.continuous_toFun, of_continuous_injective_isOpenMap, open_image_open
-/
theorem ι_isOpenEmbedding (i : D.J) : IsOpenEmbedding (𝖣.ι i) :=
  .of_continuous_injective_isOpenMap (𝖣.ι i).hom.continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

/--
Definition of `MkCore` / `MkCore` 的定义

English:
structure MkCore
  parameters: where
  axioms and operations (8):
    - {J : Type u}
    - U : J -> TopCat.{u}
    - V : forall i, J -> Opens (U i)
    - t : forall i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
    - V_id : forall i, V i i = ⊤
    - t_id : forall i, ⇑(t i i) = id
    - t_inter : forall ⦃i j⦄ (k) (x : V i j), ↑x in V i k -> (((↑) : (V j i) -> (U j)) (t i j x)) in V j k
    - cocycle : forall (i j k) (x : V i j) (h : ↑x in V i k), (((↑) : (V k j) -> (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) -> (U k)) (t i k ⟨x, h⟩)

中文:
结构 MkCore
  参数: where
  公理与运算 (8 个):
    - {J : 类型u}
    - U : J -> 顶元素范畴.{u}
    - V : 对任意 i, J -> Opens (U i)
    - t : 对任意 i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
    - V_id : 对任意 i, V i i = ⊤
    - t_id : 对任意 i, ⇑(t i i) = id
    - t_inter : 对任意 ⦃i j⦄ (k) (x : V i j), ↑x in V i k -> (((↑) : (V j i) -> (U j)) (t i j x)) in V j k
    - cocycle : 对任意 (i j k) (x : V i j) (h : ↑x in V i k), (((↑) : (V k j) -> (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) -> (U k)) (t i k ⟨x, h⟩)
-/
structure MkCore where
  /-- The index type `J` -/
  {J : Type u}
  /-- For each `i : J`, a bundled topological space `U i` -/
  U : J -> TopCat.{u}
  /-- For each `i j : J`, an open set `V i j ⊆ U i` -/
  V : forall i, J -> Opens (U i)
  /-- For each `i j : ι`, a transition map `t i j : V i j ⟶ V j i` -/
  t : forall i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
  V_id : forall i, V i i = ⊤
  t_id : forall i, ⇑(t i i) = id
  t_inter : forall ⦃i j⦄ (k) (x : V i j), ↑x in V i k -> (((↑) : (V j i) -> (U j)) (t i j x)) in V j k
  cocycle :
    forall (i j k) (x : V i j) (h : ↑x in V i k),
      (((↑) : (V k j) -> (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) -> (U k)) (t i k ⟨x, h⟩)

/--
theorem `MkCore.t_inv` / 定理 `MkCore.t_inv`

English:
theorem MkCore.t_inv
  given: (h : MkCore) (i j : h.J) (x : h.V j i)
  statement: h.t i j ((h.t j i) x) = x
  proof: by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert! Subtype.ext this
  rw [h.V_id]
  trivial

中文:
定理 MkCore.t_inv
  条件: (h : MkCore) (i j : h.J) (x : h.V j i)
  结论: h.t i j ((h.t j i) x) = x
  证明: by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert! Subtype.ext this
  rw [h.V_id]
  trivial

Depends on / 依赖: Subtype, Subtype.ext, V_id, cocycle, convert, h.V_id, h.cocycle, h.t_id, t_id
-/
theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert! Subtype.ext this
  rw [h.V_id]
  trivial

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]

/--
Definition of `MkCore.t'` / `MkCore.t'` 的定义

English:
definition MkCore.t'
  signature: (h : MkCore.{u}) (i j k : h.J)
  body: by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ofHom ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop

中文:
定义 MkCore.t'
  签名: (h : MkCore.{u}) (i j k : h.J)
  定义体: by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ofHom ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop

Depends on / 依赖: fun_prop, h.t_inter, pullbackIsoProdSubtype, t_inter
-/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion' (h.V i k).inclusion' ⟶
      pullback (h.V j k).inclusion' (h.V j i).inclusion' := by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ofHom ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (h : MkCore.{u})
  body: h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc]; rw [Category.assoc]; rw [pullbackIsoProdSubtype_inv_snd]; rw [← Iso.eq_inv_comp]; rw [pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp]; rw [Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    dsimp only [Opens.coe_inclusion', hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, hom_id, ContinuousMap.id_apply]
    rw [Subtype.mk_eq_mk]; rw [Prod.mk_inj]; rw [Subtype.mk_eq_mk]; rw [Subtype.ext_iff]; rw [and_self_iff]
    convert! congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

中文:
定义 mk'
  签名: (h : MkCore.{u})
  定义体: h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc]; rw [Category.assoc]; rw [pullbackIsoProdSubtype_inv_snd]; rw [← Iso.eq_inv_comp]; rw [pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp]; rw [Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    dsimp only [Opens.coe_inclusion', hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, hom_id, ContinuousMap.id_apply]
    rw [Subtype.mk_eq_mk]; rw [Prod.mk_inj]; rw [Subtype.mk_eq_mk]; rw [Subtype.ext_iff]; rw [and_self_iff]
    convert! congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h
-/
def mk' (h : MkCore.{u}) : TopCat.GlueData where
  J := h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc]; rw [Category.assoc]; rw [pullbackIsoProdSubtype_inv_snd]; rw [← Iso.eq_inv_comp]; rw [pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp]; rw [Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    dsimp only [Opens.coe_inclusion', hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, hom_id, ContinuousMap.id_apply]
    rw [Subtype.mk_eq_mk]; rw [Prod.mk_inj]; rw [Subtype.mk_eq_mk]; rw [Subtype.ext_iff]; rw [and_self_iff]
    convert! congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J -> Opens α)

/-- We may construct a glue data from a family of open sets. -/
@[simps! toGlueData_J toGlueData_U toGlueData_V toGlueData_t toGlueData_f]
/--
Definition of `ofOpenSubsets` / `ofOpenSubsets` 的定义

English:
definition ofOpenSubsets
  signature: : TopCat.GlueData.{u}
  body: mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ofHom ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by fun_prop⟩
      V_id := fun i => by simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }

中文:
定义 ofOpenSubsets
  签名: : 顶元素范畴.粘合数据.{u}
  定义体: mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ofHom ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by fun_prop⟩
      V_id := fun i => by simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }

Depends on / 依赖: Opens.inclusion, Opens.map, Opens.toTopCat, TopCat, TopCat.of, V_id, cocycle, fun_prop, inclusion, t_id, t_inter, toTopCat
-/
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ofHom ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by fun_prop⟩
      V_id := fun i => by simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }

/--
Definition of `fromOpenSubsetsGlue` / `fromOpenSubsetsGlue` 的定义

English:
definition fromOpenSubsetsGlue
  signature: : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α
  body: Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)

@[simp, elementwise nosimp]

中文:
定义 fromOpenSubsetsGlue
  签名: : (ofOpenSubsets U).toGlueData.glued ⟶ 顶元素范畴.of α
  定义体: Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)

@[simp, elementwise nosimp]

Depends on / 依赖: Multicoequalizer, Multicoequalizer.desc, Opens.inclusion, inclusion
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)

@[simp, elementwise nosimp]
/--
theorem `ι_fromOpenSubsetsGlue` / 定理 `ι_fromOpenSubsetsGlue`

English:
theorem ι_fromOpenSubsetsGlue
  given: (i : J)
  proof: Multicoequalizer.π_desc _ _ _ _ _

中文:
定理 ι_fromOpenSubsetsGlue
  条件: (i : J)
  证明: Multicoequalizer.π_desc _ _ _ _ _

Depends on / 依赖: Multicoequalizer
-/
theorem ι_fromOpenSubsetsGlue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion' _ :=
  Multicoequalizer.π_desc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `fromOpenSubsetsGlue_injective` / 定理 `fromOpenSubsetsGlue_injective`

English:
theorem fromOpenSubsetsGlue_injective
  statement: Function.Injective (fromOpenSubsetsGlue U)
  proof: by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  rw [ι_fromOpenSubsetsGlue_apply]; rw [ι_fromOpenSubsetsGlue_apply] at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

中文:
定理 fromOpenSubsetsGlue_injective
  结论: 函数.单射 (fromOpenSubsetsGlue U)
  证明: by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  rw [ι_fromOpenSubsetsGlue_apply]; rw [ι_fromOpenSubsetsGlue_apply] at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

Depends on / 依赖: ofOpenSubsets
-/
theorem fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  rw [ι_fromOpenSubsetsGlue_apply]; rw [ι_fromOpenSubsetsGlue_apply] at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fromOpenSubsetsGlue_isOpenMap` / 定理 `fromOpenSubsetsGlue_isOpenMap`

English:
theorem fromOpenSubsetsGlue_isOpenMap
  statement: IsOpenMap (fromOpenSubsetsGlue U)
  proof: by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s inter Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert! hs i using 1
    rw [← ι_fromOpenSubsetsGlue]; rw [coe_comp]; rw [Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self (f := (Opens.inclusion' _).hom) ⟨x, hx'⟩

中文:
定理 fromOpenSubsetsGlue_isOpenMap
  结论: 是开映射 (fromOpenSubsetsGlue U)
  证明: by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s inter Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert! hs i using 1
    rw [← ι_fromOpenSubsetsGlue]; rw [coe_comp]; rw [Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self (f := (Opens.inclusion' _).hom) ⟨x, hx'⟩

Depends on / 依赖: Opens.inclusion, Opens.isOpenEmbedding, Set.image_preimage_eq_inter_range, Set.inter_subset_left, Set.preimage_comp, Set.range, TopCat, TopCat.of, coe_comp, convert, fromOpenSubsetsGlue, image_preimage_eq_inter_range, inclusion, inter_subset_left, isOpenEmbedding, isOpenMap, isOpen_iff, isOpen_iff_forall_mem_open, ofOpenSubsets, preimage_comp
-/
theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s inter Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert! hs i using 1
    rw [← ι_fromOpenSubsetsGlue]; rw [coe_comp]; rw [Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self (f := (Opens.inclusion' _).hom) ⟨x, hx'⟩

/--
theorem `fromOpenSubsetsGlue_isOpenEmbedding` / 定理 `fromOpenSubsetsGlue_isOpenEmbedding`

English:
theorem fromOpenSubsetsGlue_isOpenEmbedding
  statement: IsOpenEmbedding (fromOpenSubsetsGlue U)
  proof: .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)

中文:
定理 fromOpenSubsetsGlue_isOpenEmbedding
  结论: 是开嵌入 (fromOpenSubsetsGlue U)
  证明: .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_toFun, continuous_toFun, fromOpenSubsetsGlue_injective, fromOpenSubsetsGlue_isOpenMap, of_continuous_injective_isOpenMap
-/
theorem fromOpenSubsetsGlue_isOpenEmbedding : IsOpenEmbedding (fromOpenSubsetsGlue U) :=
  .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `range_fromOpenSubsetsGlue` / 定理 `range_fromOpenSubsetsGlue`

English:
theorem range_fromOpenSubsetsGlue
  statement: Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α)
  proof: by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩

中文:
定理 range_fromOpenSubsetsGlue
  结论: 集合.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : 集合 α)
  证明: by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩

Depends on / 依赖: Set.subset_iUnion, ofOpenSubsets, rename_i, subset_iUnion, toGlueData
-/
theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩

/--
Definition of `openCoverGlueHomeo` / `openCoverGlueHomeo` 的定义

English:
definition openCoverGlueHomeo
  signature: (h : ⋃ i, (U i : Set α) = Set.univ)
  body: Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).hom.2 (fromOpenSubsetsGlue_isOpenMap U)

中文:
定义 openCoverGlueHomeo
  签名: (h : ⋃ i, (U i : 集合 α) = 集合.univ)
  定义体: Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).hom.2 (fromOpenSubsetsGlue_isOpenMap U)

Depends on / 依赖: Equiv.ofBijective, Equiv.toHomeomorphOfContinuousOpen, Set.range_eq_univ.mp, fromOpenSubsetsGlue, fromOpenSubsetsGlue_injective, fromOpenSubsetsGlue_isOpenMap, ofBijective, range_eq_univ, range_fromOpenSubsetsGlue, toHomeomorphOfContinuousOpen
-/
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).hom.2 (fromOpenSubsetsGlue_isOpenMap U)

end GlueData

end TopCat
