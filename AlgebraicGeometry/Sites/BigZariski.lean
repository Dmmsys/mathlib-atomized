/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.CoproductSheafCondition
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.Topology.Category.TopCat.GrothendieckTopology

/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

TODO:
* If `Y : Scheme.{u}`, define a continuous functor from the category of opens of `Y`
  to `Over Y`, and show that a presheaf on `Over Y` is a sheaf for the Zariski topology
  iff its "restriction" to the topological space `Z` is a sheaf for all `Z : Over Y`.
* We should have good notions of (pre)sheaves of `Type (u + 1)` (e.g. associated
  sheaf functor, pushforward, pullbacks) on `Scheme.{u}` for this topology. However,
  some constructions in the `CategoryTheory.Sites` folder currently assume that
  the site is a small category: this should be generalized. As a result,
  this big Zariski site can considered as a test case of the Grothendieck topology API
  for future applications to étale cohomology.

-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

/--
Definition of `zariskiPretopology` / `zariskiPretopology` 的定义

English:
definition zariskiPretopology
  signature: : Pretopology Scheme.{u}
  body: pretopology @IsOpenImmersion

中文:
定义 zariskiPretopology
  签名: : Pretopology 概形.{u}
  定义体: pretopology @IsOpenImmersion

Depends on / 依赖: IsOpenImmersion, pretopology
-/
def zariskiPretopology : Pretopology Scheme.{u} :=
  pretopology @IsOpenImmersion

/--
Definition of `zariskiTopology` / `zariskiTopology` 的定义

English:
abbreviation zariskiTopology
  signature: : GrothendieckTopology Scheme.{u}
  body: grothendieckTopology IsOpenImmersion

中文:
缩写 zariskiTopology
  签名: : Grothendieck拓扑 概形.{u}
  定义体: grothendieckTopology IsOpenImmersion

Depends on / 依赖: IsOpenImmersion, grothendieckTopology
-/
abbrev zariskiTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology IsOpenImmersion

/--
lemma `zariskiTopology_eq` / 引理 `zariskiTopology_eq`

English:
lemma zariskiTopology_eq
  statement: zariskiTopology.{u} = zariskiPretopology.toGrothendieck
  proof: Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

中文:
引理 zariskiTopology_eq
  结论: zariskiTopology.{u} = zariskiPretopology.toGrothendieck
  证明: Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm, toGrothendieck_toPretopology_eq_toGrothendieck
-/
lemma zariskiTopology_eq : zariskiTopology.{u} = zariskiPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `subcanonical_zariskiTopology` / 实例 `subcanonical_zariskiTopology`

English:
instance subcanonical_zariskiTopology
  signature: : zariskiTopology.Subcanonical
  body: by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hS
let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.f _) (.mk

中文:
实例 subcanonical_zariskiTopology
  签名: : zariskiTopology.子典范
  定义体: by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hS
let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.f _) (.mk

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, Limits, Limits.pullback.condition, OpenCover, Precoverage, Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange, Subcanonical, condition, exists_cover_of_mem_pretopology, glueMorphisms, hom_ext, isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange, of_isSheaf_yoneda_obj, pullback
-/
instance subcanonical_zariskiTopology : zariskiTopology.Subcanonical := by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro X
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS x hx
  obtain ⟨(𝓤 : OpenCover Y), rfl⟩ := exists_cover_of_mem_pretopology hS
let e : Y ⟶ X := 𝓤.glueMorphisms (fun j => x (𝓤.f _) (.mk _)) by
    intro i j
    apply hx
    exact Limits.pullback.condition
  refine ⟨e, ?_, ?_⟩
  · rintro Z e ⟨j⟩
    dsimp [e]
    rw [𝓤.ι_glueMorphisms]
  · intro e' h
    apply 𝓤.hom_ext
    intro j
    rw [𝓤.ι_glueMorphisms]
    exact h (𝓤.f j) (.mk j)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Scheme.forgetToTop.{u}.IsContinuous zariskiTopology TopCat.grothendieckTopology
  body: by
  rw [zariskiTopology]; rw [grothendieckTopology]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR => ⟨fun _ _ f _ hf _ => ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPr

中文:
实例 :
  签名: 概形.forgetToTop.{u}.是连续 zariskiTopology 顶元素范畴.grothendieckTopology
  定义体: by
  rw [zariskiTopology]; rw [grothendieckTopology]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR => ⟨fun _ _ f _ hf _ => ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPr

Depends on / 依赖: Functor, Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy, IsOpenImmersion, MorphismProperty, MorphismProperty.comap_precoverage, MorphismProperty.precovera, Precoverage, Precoverage.comap_comp, Precoverage.comap_inf, PullbacksPreservedBy, TopCat, TopCat.precoverage, comap_comp, comap_inf, comap_precoverage, forgetToTop, forgetToTop_comp_forget, grothendieckTopology, infer_instance, isContinuous_toGrothendieck_of_pullbacksPreservedBy
-/
instance : Scheme.forgetToTop.{u}.IsContinuous zariskiTopology TopCat.grothendieckTopology := by
  rw [zariskiTopology]; rw [grothendieckTopology]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR => ⟨fun _ _ f _ hf _ => ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [TopCat.precoverage]; rw [Precoverage.comap_inf]; rw [precoverage]
  gcongr
  · rw [← Precoverage.comap_comp, forgetToTop_comp_forget]
  · rw [MorphismProperty.comap_precoverage]
    exact MorphismProperty.precoverage_monotone fun X Y f hf => f.isOpenEmbedding

set_option backward.isDefEq.respectTransparency.types false in
/-- A Zariski-`1`-hypercover of a scheme where all components are affine. -/
@[simps! toPreOneHypercover_toPreZeroHypercover]
noncomputable
/--
Definition of `affineOneHypercover` / `affineOneHypercover` 的定义

English:
definition affineOneHypercover
  signature: (X : Scheme.{u})
  body: .mk'
    (X.affineCover.refineOneHypercover fun i j =>
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j => by simpa using! Cover.mem_grothendieckTopology _

中文:
定义 affineOneHypercover
  签名: (X : 概形.{u})
  定义体: .mk'
    (X.affineCover.refineOneHypercover fun i j =>
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j => by simpa using! Cover.mem_grothendieckTopology _

Depends on / 依赖: Cover.mem_grothendieckTopology, X.affineCover.f, X.affineCover.mem_grothendieckTopology, X.affineCover.refineOneHypercover, affineCover, affineCover.toPreZeroHypercover, mem_grothendieckTopology, pullback, refineOneHypercover, toPreZeroHypercover
-/
def affineOneHypercover (X : Scheme.{u}) : zariskiTopology.OneHypercover X :=
  .mk'
    (X.affineCover.refineOneHypercover fun i j =>
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j => by simpa using! Cover.mem_grothendieckTopology _

end Scheme

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology` / 引理 `preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology`

English:
lemma preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
  statement: {F : Scheme.{u}ᵒᵖ ⥤ Type v}
  proof: by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor <| unop ∘ X)) i) :=
inferInstanceAs Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sig

中文:
引理 preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
  结论: {F : 概形.{u}ᵒᵖ ⥤ 类型v}
  证明: by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor <| unop ∘ X)) i) :=
inferInstanceAs Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sig

Depends on / 依赖: Cofan.inj, Discrete, Discrete.functor, Presieve, Presieve.preservesProduct_of_isSheafFor, Scheme, Sigma.cocone, allowSynthFailures, bot_mem_grothendieckTopology, cocone, config, convert, coproductIsCoproduct, eq_bot_iff, functor, hF.isSheafFor, i.elim, initialIsInitial, isSheafFor, preservesLimitsOfShape_of_discrete
-/
lemma preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology {F : Scheme.{u}ᵒᵖ ⥤ Type v}
    {ι : Type*} [Small.{u} ι] [Small.{v} ι] (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesLimitsOfShape (Discrete ι) F := by
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor <| unop ∘ X)) i) :=
inferInstanceAs Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sigma.cocone (Discrete.functor <| unop ∘ X)) (coproductIsCoproduct' _) ?_ ?_
  · apply hF.isSheafFor
    convert! (⊥_ Scheme).bot_mem_grothendieckTopology
    rw [eq_bot_iff]
    rintro Y f ⟨g, _, _, ⟨i⟩, _⟩
    exact i.elim
  · intro i j
    exact CoproductDisjoint.isPullback_of_isInitial
      (coproductIsCoproduct' <| Discrete.functor <| unop ∘ X) initialIsInitial
  · exact hF.isSheafFor _ (sigmaOpenCover _).mem_grothendieckTopology

/--
lemma `ofArrows_ι_mem_zariskiTopology_of_isColimit` / 引理 `ofArrows_ι_mem_zariskiTopology_of_isColimit`

English:
lemma ofArrows_ι_mem_zariskiTopology_of_isColimit
  statement: {J : Type*} [Category J]
  proof: by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := iso.inv)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
 

中文:
引理 ofArrows_ι_mem_zariskiTopology_of_isColimit
  结论: {J : 类型} [范畴 J]
  证明: by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := iso.inv)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
 

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.pullback_mem_iff_of_isIso, GrothendieckTopology.superset_covering, IsLocallyDirected, Scheme, Scheme.IsLocallyDirected.openCover, Sieve.generate_le_iff, Sieve.ofArrows, c.pt, coconePointUniqueUpToIso, colimit, colimit.isColimit, generate_le_iff, hc.coconePointUniqueUpToIso, isColimit, iso.inv, mem_grothendieckTopology, ofArrows, openCover, pullback_mem_iff_of_isIso
-/
lemma ofArrows_ι_mem_zariskiTopology_of_isColimit {J : Type*} [Category J]
    (F : J ⥤ Scheme.{u}) [forall {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)]
    [(F.comp Scheme.forget).IsLocallyDirected] [Quiver.IsThin J] [Small.{u} J]
    (c : Cocone F) (hc : IsColimit c) :
    Sieve.ofArrows _ c.ι.app in Scheme.zariskiTopology c.pt := by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_mem_iff_of_isIso (i := iso.inv)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    exact ⟨_, 𝟙 _, c.ι.app i, ⟨i⟩, by simp [iso]⟩
  · exact (Scheme.IsLocallyDirected.openCover F).mem_grothendieckTopology

-- TODO: This holds more generally if `𝒰.J` is `u`-small and can be generalized
-- when we have `PreExtensive` categories
/--
lemma `Scheme.Cover.isSheafFor_sigma_iff` / 引理 `Scheme.Cover.isSheafFor_sigma_iff`

English:
lemma Scheme.Cover.isSheafFor_sigma_iff
  statement: {P : MorphismProperty Scheme.{u}}
  proof: by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  let c : Cofan 𝒰.X := Cofan.mk _ (Sigma.ι 𝒰.X)
  

中文:
引理 概形.Cover.isSheafFor_sigma_iff
  结论: {P : MorphismProperty 概形.{u}}
  证明: by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  let c : Cofan 𝒰.X := Cofan.mk _ (Sigma.ι 𝒰.X)
  

Depends on / 依赖: Cofan.mk, Discrete, FinitaryExtensive, FinitaryExtensive.isVanKampen_finiteCoproducts, PreZeroHypercover, PreZeroHypercover.presieve, PreservesLimitsOfShape, Presieve, Presieve.isSheafFor_sigmaDesc_iff, coproductIsCoproduct, isSheafFor_sigmaDesc_iff, isUniversal, isVanKampen_finiteCoproducts, preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology
-/
lemma Scheme.Cover.isSheafFor_sigma_iff {P : MorphismProperty Scheme.{u}}
    {F : Scheme.{u}ᵒᵖ ⥤ Type*} [IsZariskiLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Finite 𝒰.I₀] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.X 𝒰.f) := by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  let c : Cofan 𝒰.X := Cofan.mk _ (Sigma.ι 𝒰.X)
  rw [← Presieve.isSheafFor_sigmaDesc_iff 𝒰.f (coproductIsCoproduct _)
    (FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct _)).isUniversal]
  congr!
  rw [← PreZeroHypercover.presieve₀]; rw [𝒰.presieve₀_sigma]
  rfl

end AlgebraicGeometry
