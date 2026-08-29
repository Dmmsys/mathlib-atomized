/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Smooth manifolds as locally ringed spaces

This file equips a smooth manifold with the structure of a locally ringed space.

## Main results

* `smoothSheafCommRing.isUnit_stalk_iff`: The units of the stalk at `x` of the sheaf of smooth
  functions from a smooth manifold `M` to its scalar field `𝕜`, considered as a sheaf of commutative
  rings, are the functions whose values at `x` are nonzero.

## Main definitions

* `ChartedSpace.locallyRingedSpace`: A smooth manifold can be considered as a locally ringed space.
* `ChartedSpace.locallyRingedSpaceMap`: A smooth map between smooth manifolds induces a morphism
  of locally ringed spaces.

## TODO

- Show that every morphism of locally ringed spaces between two smooth manifolds is induced
  by a smooth map via `ChartedSpace.locallyRingedSpaceMap`.

-/

@[expose] public section

noncomputable section
universe u

open scoped ContDiff

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
  {M : Type u} [TopologicalSpace M] [ChartedSpace HM M]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HN : Type*} [TopologicalSpace HN] (IN : ModelWithCorners 𝕜 EN HN)
  {N : Type u} [TopologicalSpace N] [ChartedSpace HN N]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  {P : Type u} [TopologicalSpace P] [ChartedSpace HP P]

open AlgebraicGeometry Manifold TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `smoothSheafCommRing.isUnit_stalk_iff` / 定理 `smoothSheafCommRing.isUnit_stalk_iff`

English:
theorem smoothSheafCommRing.isUnit_stalk_iff
  statement: {x : M}
  proof: by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
   

中文:
定理 smoothSheafCommRing.isUnit_stalk_iff
  结论: {x : M}
  证明: by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
   

Depends on / 依赖: congr_arg, presheaf, smoothSheafCommRing, smoothSheafCommRing.eval
-/
theorem smoothSheafCommRing.isUnit_stalk_iff {x : M}
    (f : (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) :
    IsUnit f ↔ f ∉ RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ (h' : smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x f = 0)
    simpa [h'] using congr_arg (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) hf
  · let S := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf
    -- Suppose that `f`, in the stalk at `x`, is nonzero at `x`
    rintro (hf : _ != 0)
    -- Represent `f` as the germ of some function (also called `f`) on an open neighbourhood `U` of
    -- `x`, which is nonzero at `x`
    obtain ⟨U : Opens M, hxU, f : C^∞⟮IM, U; 𝓘(𝕜), 𝕜⟯, rfl⟩ := S.exists_germ_eq f
    have hf' : f ⟨x, hxU⟩ != 0 := by
      convert! hf
      exact (smoothSheafCommRing.eval_germ U x hxU f).symm
    -- In fact, by continuity, `f` is nonzero on a neighbourhood `V` of `x`
    have H : forallᶠ (z : U) in 𝓝 ⟨x, hxU⟩, f z != 0 := f.2.continuous.continuousAt.eventually_ne hf'
    rw [eventually_nhds_iff] at H
    obtain ⟨V₀, hV₀f, hV₀, hxV₀⟩ := H
    let V : Opens M := ⟨Subtype.val '' V₀, U.2.isOpenMap_subtype_val V₀ hV₀⟩
    have hUV : V <= U := Subtype.coe_image_subset (U : Set M) V₀
    have hV : V₀ = Set.range (Set.inclusion hUV) := by
      convert! (Set.range_inclusion hUV).symm
      ext y
      change _ ↔ y in Subtype.val ⁻¹' Subtype.val '' V₀
      rw [Set.preimage_image_eq _ Subtype.coe_injective]
    clear_value V
    subst hV
    have hxV : x in (V : Set M) := by
      obtain ⟨x₀, hxx₀⟩ := hxV₀
      convert! x₀.2
      exact congr_arg Subtype.val hxx₀.symm
    have hVf : forall y : V, f (Set.inclusion hUV y) != 0 :=
      fun y => hV₀f (Set.inclusion hUV y) (Set.mem_range_self y)
    -- Let `g` be the pointwise inverse of `f` on `V`, which is smooth since `f` is nonzero there
    let g : C^∞⟮IM, V; 𝓘(𝕜), 𝕜⟯ := ⟨(f ∘ Set.inclusion hUV)⁻¹, ?_⟩
    -- The germ of `g` is inverse to the germ of `f`, so `f` is a unit
    · refine ⟨⟨S.germ _ x (hxV) (ContMDiffMap.restrictRingHom IM 𝓘(𝕜) 𝕜 hUV f), S.germ _ x hxV g,
        ?_, ?_⟩, S.germ_res_apply hUV.hom x hxV f⟩
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply mul_inv_cancel₀
        exact hVf y
      · rw [← map_mul]
        -- Qualified the name to avoid Lean not finding a `OneHomClass` https://github.com/leanprover-community/mathlib4/pull/8386
        convert! RingHom.map_one _
        apply Subtype.ext
        ext y
        apply inv_mul_cancel₀
        exact hVf y
    · intro y
      exact (((contDiffAt_inv _ (hVf y)).contMDiffAt).comp y
        (f.contMDiff.comp (contMDiff_inclusion hUV)).contMDiffAt :)

/--
theorem `smoothSheafCommRing.nonunits_stalk` / 定理 `smoothSheafCommRing.nonunits_stalk`

English:
theorem smoothSheafCommRing.nonunits_stalk
  given: (x : M)
  proof: by
  ext1 f
  rw [mem_nonunits_iff]; rw [not_iff_comm]; rw [Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

中文:
定理 smoothSheafCommRing.nonunits_stalk
  条件: (x : M)
  证明: by
  ext1 f
  rw [mem_nonunits_iff]; rw [not_iff_comm]; rw [Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

Depends on / 依赖: Iff.comm, isUnit_stalk_iff, mem_nonunits_iff, not_iff_comm, smoothSheafCommRing, smoothSheafCommRing.isUnit_stalk_iff
-/
theorem smoothSheafCommRing.nonunits_stalk (x : M) :
    nonunits ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x)
    = RingHom.ker (smoothSheafCommRing.eval IM 𝓘(𝕜) M 𝕜 x) := by
  ext1 f
  rw [mem_nonunits_iff]; rw [not_iff_comm]; rw [Iff.comm]
  apply smoothSheafCommRing.isUnit_stalk_iff

/--
Instance `smoothSheafCommRing.instLocalRing_stalk` / 实例 `smoothSheafCommRing.instLocalRing_stalk`

English:
instance smoothSheafCommRing.instLocalRing_stalk
  signature: (x : M)
  body: by
  apply IsLocalRing.of_nonunits_add
  rw [smoothSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

中文:
实例 smoothSheafCommRing.instLocalRing_stalk
  签名: (x : M)
  定义体: by
  apply IsLocalRing.of_nonunits_add
  rw [smoothSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

Depends on / 依赖: Ideal.add_mem, IsLocalRing, IsLocalRing.of_nonunits_add, add_mem, nonunits_stalk, of_nonunits_add, smoothSheafCommRing, smoothSheafCommRing.nonunits_stalk
-/
instance smoothSheafCommRing.instLocalRing_stalk (x : M) :
    IsLocalRing ((smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).presheaf.stalk x) := by
  apply IsLocalRing.of_nonunits_add
  rw [smoothSheafCommRing.nonunits_stalk]
  intro f g
  exact Ideal.add_mem _

variable (M)

/-- A smooth manifold can be considered as a locally ringed space. -/
@[implicit_reducible]
/--
Definition of `ChartedSpace.locallyRingedSpace` / `ChartedSpace.locallyRingedSpace` 的定义

English:
definition ChartedSpace.locallyRingedSpace
  signature: : LocallyRingedSpace where
  body: TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).property
  isLocalRing x := smoothSheafCommRing.instLocalRing_stalk IM x

@[deprecated (since := "2026-04-01")]
alias IsManifold.locallyRingedSpace := ChartedSpace.locallyRingedSpace

中文:
定义 ChartedSpace.locallyRingedSpace
  签名: : LocallyRingedSpace where
  定义体: TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).property
  isLocalRing x := smoothSheafCommRing.instLocalRing_stalk IM x

@[deprecated (since := "2026-04-01")]
alias IsManifold.locallyRingedSpace := ChartedSpace.locallyRingedSpace

Depends on / 依赖: TopCat, TopCat.of
-/
def ChartedSpace.locallyRingedSpace : LocallyRingedSpace where
  carrier := TopCat.of M
  presheaf := smoothPresheafCommRing IM 𝓘(𝕜) M 𝕜
  IsSheaf := (smoothSheafCommRing IM 𝓘(𝕜) M 𝕜).property
  isLocalRing x := smoothSheafCommRing.instLocalRing_stalk IM x

@[deprecated (since := "2026-04-01")]
alias IsManifold.locallyRingedSpace := ChartedSpace.locallyRingedSpace

open CategoryTheory Limits

variable {M IM IN}

/--
Definition of `ChartedSpace.locallyRingedSpaceMapAux` / `ChartedSpace.locallyRingedSpaceMapAux` 的定义

English:
definition ChartedSpace.locallyRingedSpaceMapAux
  signature: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  body: TopCat.ofHom ⟨f, hf.continuous⟩
  c := (hf.smoothSheafCommRingHom _ _ f).hom

中文:
定义 ChartedSpace.locallyRingedSpaceMapAux
  签名: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  定义体: TopCat.ofHom ⟨f, hf.continuous⟩
  c := (hf.smoothSheafCommRingHom _ _ f).hom

Depends on / 依赖: TopCat, TopCat.ofHom, continuous, hf.continuous
-/
def ChartedSpace.locallyRingedSpaceMapAux (f : M -> N) (hf : ContMDiff IM IN ∞ f) :
    (locallyRingedSpace IM M).toPresheafedSpace ⟶
      (locallyRingedSpace IN N).toPresheafedSpace where
  base := TopCat.ofHom ⟨f, hf.continuous⟩
  c := (hf.smoothSheafCommRingHom _ _ f).hom

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ChartedSpace.stalkMap_locallyRingedSpaceMapAux` / 引理 `ChartedSpace.stalkMap_locallyRingedSpaceMapAux`

English:
lemma ChartedSpace.stalkMap_locallyRingedSpaceMapAux
  statement: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  proof: by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext a
  refine Eq.trans ?_ (smoothSheafCommRing.evalHom_germ _ _ _ _ _ _ _ a).symm
  apply smoothSheafCommRing.evalHom_germ

中文:
引理 ChartedSpace.stalkMap_locallyRingedSpaceMapAux
  结论: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  证明: by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext a
  refine Eq.trans ?_ (smoothSheafCommRing.evalHom_germ _ _ _ _ _ _ _ a).symm
  apply smoothSheafCommRing.evalHom_germ

Depends on / 依赖: Eq.trans, Presheaf, PresheafedSpace, PresheafedSpace.stalkMap_germ_assoc, TopCat, TopCat.Presheaf.stalk_hom_ext, evalHom_germ, smoothSheafCommRing, smoothSheafCommRing.evalHom_germ, stalkMap_germ_assoc, stalk_hom_ext
-/
lemma ChartedSpace.stalkMap_locallyRingedSpaceMapAux (f : M -> N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMapAux f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  rw [PresheafedSpace.stalkMap_germ_assoc]
  ext a
  refine Eq.trans ?_ (smoothSheafCommRing.evalHom_germ _ _ _ _ _ _ _ a).symm
  apply smoothSheafCommRing.evalHom_germ

set_option backward.isDefEq.respectTransparency false in
/-- A smooth function of manifolds `f : M → N` induces a morphism of locally ringed spaces. -/
@[simps! base]
/--
Definition of `ChartedSpace.locallyRingedSpaceMap` / `ChartedSpace.locallyRingedSpaceMap` 的定义

English:
definition ChartedSpace.locallyRingedSpaceMap
  signature: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  body: locallyRingedSpaceMapAux f hf
  prop x := by
    refine ⟨fun a ha => ?_⟩
    rw [smoothSheafCommRing.isUnit_stalk_iff]; rw [RingHom.mem_ker] at ha ⊢
    convert! ha
    exact (congr($(stalkMap_locallyRingedSpaceMapAux f hf x) a)).symm

@[reassoc (attr := simp)]

中文:
定义 ChartedSpace.locallyRingedSpaceMap
  签名: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  定义体: locallyRingedSpaceMapAux f hf
  prop x := by
    refine ⟨fun a ha => ?_⟩
    rw [smoothSheafCommRing.isUnit_stalk_iff]; rw [RingHom.mem_ker] at ha ⊢
    convert! ha
    exact (congr($(stalkMap_locallyRingedSpaceMapAux f hf x) a)).symm

@[reassoc (attr := simp)]

Depends on / 依赖: locallyRingedSpaceMapAux
-/
def ChartedSpace.locallyRingedSpaceMap (f : M -> N) (hf : ContMDiff IM IN ∞ f) :
    locallyRingedSpace IM M ⟶ locallyRingedSpace IN N where
  __ := locallyRingedSpaceMapAux f hf
  prop x := by
    refine ⟨fun a ha => ?_⟩
    rw [smoothSheafCommRing.isUnit_stalk_iff]; rw [RingHom.mem_ker] at ha ⊢
    convert! ha
    exact (congr($(stalkMap_locallyRingedSpaceMapAux f hf x) a)).symm

@[reassoc (attr := simp)]
/--
lemma `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom` / 引理 `ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom`

English:
lemma ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom
  statement: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  proof: stalkMap_locallyRingedSpaceMapAux f hf x

中文:
引理 ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom
  结论: (f : M -> N) (hf : ContMDiff IM IN ∞ f)
  证明: stalkMap_locallyRingedSpaceMapAux f hf x

Depends on / 依赖: stalkMap_locallyRingedSpaceMapAux
-/
lemma ChartedSpace.stalkMap_locallyRingedSpaceMap_evalHom (f : M -> N) (hf : ContMDiff IM IN ∞ f)
    (x : M) :
    (locallyRingedSpaceMap f hf).stalkMap x ≫
      smoothSheafCommRing.evalHom IM 𝓘(𝕜) M 𝕜 x =
      smoothSheafCommRing.evalHom IN 𝓘(𝕜) N 𝕜 (f x) :=
  stalkMap_locallyRingedSpaceMapAux f hf x

variable (IM M) in
/--
lemma `ChartedSpace.locallyRingedSpace_id` / 引理 `ChartedSpace.locallyRingedSpace_id`

English:
lemma ChartedSpace.locallyRingedSpace_id
  proof: rfl

中文:
引理 ChartedSpace.locallyRingedSpace_id
  证明: rfl

Depends on / 依赖: contMDiff_id
-/
lemma ChartedSpace.locallyRingedSpace_id :
    locallyRingedSpaceMap (IM := IM) (IN := IM) (M := M) id contMDiff_id = 𝟙 _ :=
  rfl

/--
lemma `ChartedSpace.locallyRingedSpace_comp` / 引理 `ChartedSpace.locallyRingedSpace_comp`

English:
lemma ChartedSpace.locallyRingedSpace_comp
  statement: {f : M -> N} (hf : ContMDiff IM IN ∞ f)
  proof: rfl

中文:
引理 ChartedSpace.locallyRingedSpace_comp
  结论: {f : M -> N} (hf : ContMDiff IM IN ∞ f)
  证明: rfl
-/
lemma ChartedSpace.locallyRingedSpace_comp {f : M -> N} (hf : ContMDiff IM IN ∞ f)
    {g : N -> P} (hg : ContMDiff IN IP ∞ g) :
    locallyRingedSpaceMap (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap f hf ≫ locallyRingedSpaceMap g hg :=
  rfl

-- TODO: This holds more generally if `U` is replaced by an open embedding that
-- is also a smooth immersion.
instance (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (ChartedSpace.locallyRingedSpaceMap _ (contMDiff_subtype_val (I := IM) (U := U))) where
  base_open := U.isOpenEmbedding'
  c_iso V := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => Subtype.ext ?_, fun ⟨g, hg⟩ => ?_⟩
    · ext ⟨x, y, hy, rfl⟩
      exact congr($(hab).1 ⟨y, ⟨y, hy, rfl⟩⟩)
    · let a : TopCat.of U ⟶ TopCat.of M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      have ha : IsOpenEmbedding a.hom := U.isOpenEmbedding'
      let V' : Opens U := (Opens.map a).obj (ha.isOpenMap.functor.obj V)
      let b : V' ≃ₜ ha.isOpenMap.functor.obj V :=
U.isOpenEmbedding'.homeomorphOfSubsetRange Set.image_subset_range _ V.1
refine ⟨⟨g ∘ b.symm, ContMDiff.comp hg ?_⟩, Subtype.ext funext fun _ => ?_⟩
      · refine (ContMDiff.subtypeVal_comp_iff V' _).mp ?_
        rw [← ContMDiff.subtypeVal_comp_iff]
        convert! contMDiff_subtype_val
        ext x
        exact congr($(b.apply_symm_apply x).1)
      · change g _ = _
        congr
        apply b.symm_apply_apply

/-- Viewing a manifold as a locally ringed space commutes with restriction to open subsets. -/
@[simps]
/--
Definition of `ChartedSpace.restrictLocallyRingedSpaceIso` / `ChartedSpace.restrictLocallyRingedSpaceIso` 的定义

English:
definition ChartedSpace.restrictLocallyRingedSpaceIso
  signature: (U : Opens M)
  body: LocallyRingedSpace.IsOpenImmersion.lift
    (locallyRingedSpaceMap _ contMDiff_subtype_val)
    (LocallyRingedSpace.ofRestrict _ _) (by rfl)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)
    (locallyRingedSpaceMap _ contMDiff_subtype_va

中文:
定义 ChartedSpace.restrictLocallyRingedSpaceIso
  签名: (U : Opens M)
  定义体: LocallyRingedSpace.IsOpenImmersion.lift
    (locallyRingedSpaceMap _ contMDiff_subtype_val)
    (LocallyRingedSpace.ofRestrict _ _) (by rfl)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)
    (locallyRingedSpaceMap _ contMDiff_subtype_va

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion.lift
-/
def ChartedSpace.restrictLocallyRingedSpaceIso (U : Opens M) :
    (locallyRingedSpace IM M).restrict U.isOpenEmbedding ≅
      locallyRingedSpace IM U where
  hom := LocallyRingedSpace.IsOpenImmersion.lift
    (locallyRingedSpaceMap _ contMDiff_subtype_val)
    (LocallyRingedSpace.ofRestrict _ _) (by rfl)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)
    (locallyRingedSpaceMap _ contMDiff_subtype_val) (by rfl)
  hom_inv_id := by
    simp [← cancel_mono ((locallyRingedSpace IM M).ofRestrict U.isOpenEmbedding)]
  inv_hom_id := by
    simp [← cancel_mono (locallyRingedSpaceMap _ contMDiff_subtype_val)]
