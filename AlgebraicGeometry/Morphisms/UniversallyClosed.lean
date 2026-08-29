/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally closed morphism

A morphism of schemes `f : X ⟶ Y` is universally closed if `X ×[Y] Y' ⟶ Y'` is a closed map
for all base change `Y' ⟶ Y`.
This implies that `f` is topologically proper (`AlgebraicGeometry.Scheme.Hom.isProperMap`).

We show that being universally closed is local at the target, and is stable under compositions and
base changes.

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty

/-- A morphism of schemes `f : X ⟶ Y` is universally closed if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is (topologically) a closed map.
-/
@[mk_iff]
/--
Definition of `UniversallyClosed` / `UniversallyClosed` 的定义

English:
class UniversallyClosed
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - universally_isClosedMap : universally (topologically @IsClosedMap) f

中文:
类 UniversallyClosed
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - universally_isClosedMap : universally (topologically @IsClosedMap) f
-/
class UniversallyClosed (f : X ⟶ Y) : Prop where
  universally_isClosedMap : universally (topologically @IsClosedMap) f

@[deprecated (since := "2026-01-20")]
alias UniversallyClosed.out := UniversallyClosed.universally_isClosedMap

/--
lemma `Scheme.Hom.isClosedMap` / 引理 `Scheme.Hom.isClosedMap`

English:
lemma Scheme.Hom.isClosedMap
  given: {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f]
  proof: UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd

中文:
引理 Scheme.Hom.isClosedMap
  条件: {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f]
  证明: UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd

Depends on / 依赖: IsPullback, IsPullback.of_id_snd, UniversallyClosed, UniversallyClosed.universally_isClosedMap, of_id_snd, universally_isClosedMap
-/
lemma Scheme.Hom.isClosedMap {X Y : Scheme} (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f := UniversallyClosed.universally_isClosedMap _ _ _ IsPullback.of_id_snd

/--
theorem `universallyClosed_eq` / 定理 `universallyClosed_eq`

English:
theorem universallyClosed_eq
  statement: @UniversallyClosed = universally (topologically @IsClosedMap)
  proof: by
  ext X Y f; rw [universallyClosed_iff]

中文:
定理 universallyClosed_eq
  结论: @UniversallyClosed = universally (topologically @IsClosedMap)
  证明: by
  ext X Y f; rw [universallyClosed_iff]

Depends on / 依赖: universallyClosed_iff
-/
theorem universallyClosed_eq : @UniversallyClosed = universally (topologically @IsClosedMap) := by
  ext X Y f; rw [universallyClosed_iff]

instance (priority := 900) [IsClosedImmersion f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' hf
  have hf' : IsClosedImmersion f' :=
    MorphismProperty.of_isPullback hf.flip inferInstance
  exact f'.isClosedEmbedding.isClosedMap

/--
theorem `universallyClosed_respectsIso` / 定理 `universallyClosed_respectsIso`

English:
theorem universallyClosed_respectsIso
  statement: RespectsIso @UniversallyClosed
  proof: universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

中文:
定理 universallyClosed_respectsIso
  结论: RespectsIso @UniversallyClosed
  证明: universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

Depends on / 依赖: IsClosedMap, topologically, universallyClosed_eq, universallyClosed_eq.symm, universally_respectsIso
-/
theorem universallyClosed_respectsIso : RespectsIso @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_respectsIso (topologically @IsClosedMap)

/--
Instance `universallyClosed_isStableUnderBaseChange` / 实例 `universallyClosed_isStableUnderBaseChange`

English:
instance universallyClosed_isStableUnderBaseChange
  signature: : IsStableUnderBaseChange @UniversallyClosed
  body: universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)

中文:
实例 universallyClosed_isStableUnderBaseChange
  签名: : IsStableUnderBaseChange @UniversallyClosed
  定义体: universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)

Depends on / 依赖: IsClosedMap, topologically, universallyClosed_eq, universallyClosed_eq.symm, universally_isStableUnderBaseChange
-/
instance universallyClosed_isStableUnderBaseChange : IsStableUnderBaseChange @UniversallyClosed :=
  universallyClosed_eq.symm ▸ universally_isStableUnderBaseChange (topologically @IsClosedMap)

/--
Instance `isClosedMap_isStableUnderComposition` / 实例 `isClosedMap_isStableUnderComposition`

English:
instance isClosedMap_isStableUnderComposition
  signature: :
  body: IsClosedMap.comp (f := f) (g := g) hg hf

中文:
实例 isClosedMap_isStableUnderComposition
  签名: :
  定义体: IsClosedMap.comp (f := f) (g := g) hg hf

Depends on / 依赖: IsClosedMap, IsClosedMap.comp
-/
instance isClosedMap_isStableUnderComposition :
    IsStableUnderComposition (topologically @IsClosedMap) where
  comp_mem f g hf hg := IsClosedMap.comp (f := f) (g := g) hg hf

/--
Instance `universallyClosed_isStableUnderComposition` / 实例 `universallyClosed_isStableUnderComposition`

English:
instance universallyClosed_isStableUnderComposition
  signature: :
  body: by
  rw [universallyClosed_eq]
  infer_instance

中文:
实例 universallyClosed_isStableUnderComposition
  签名: :
  定义体: by
  rw [universallyClosed_eq]
  infer_instance

Depends on / 依赖: infer_instance, universallyClosed_eq
-/
instance universallyClosed_isStableUnderComposition :
    IsStableUnderComposition @UniversallyClosed := by
  rw [universallyClosed_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `UniversallyClosed.of_comp_surjective` / 引理 `UniversallyClosed.of_comp_surjective`

English:
lemma UniversallyClosed.of_comp_surjective
  statement: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this

中文:
引理 UniversallyClosed.of_comp_surjective
  结论: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this

Depends on / 依赖: IsClosedMap, IsClosedMap.of_comp_surjective, IsPullback, IsPullback.of_hasPullback, MorphismProperty, MorphismProperty.pullback_fst, Scheme, Scheme.Hom.continuous, Surjective, UniversallyClosed, UniversallyClosed.universally_isClosedMap, continuous, of_comp_surjective, of_hasPullback, paste_horiz, pullback_fst, universally_isClosedMap
-/
lemma UniversallyClosed.of_comp_surjective {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed (f ≫ g)] [Surjective f] : UniversallyClosed g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have := UniversallyClosed.universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsClosedMap.of_comp_surjective (MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›).1
    (Scheme.Hom.continuous _) this

/--
Instance `universallyClosedTypeComp` / 实例 `universallyClosedTypeComp`

English:
instance universallyClosedTypeComp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  body: comp_mem _ _ _ hf hg

中文:
实例 universallyClosedTypeComp
  签名: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: comp_mem _ _ _ hf hg

Depends on / 依赖: comp_mem
-/
instance universallyClosedTypeComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : UniversallyClosed f] [hg : UniversallyClosed g] : UniversallyClosed (f ≫ g) :=
  comp_mem _ _ _ hf hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @UniversallyClosed
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @UniversallyClosed
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @UniversallyClosed where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `universallyClosed_fst` / 实例 `universallyClosed_fst`

English:
instance universallyClosed_fst
  signature: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g]
  body: MorphismProperty.pullback_fst f g hg

中文:
实例 universallyClosed_fst
  签名: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g]
  定义体: MorphismProperty.pullback_fst f g hg

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance universallyClosed_fst {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hg : UniversallyClosed g] :
    UniversallyClosed (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g hg

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `universallyClosed_snd` / 实例 `universallyClosed_snd`

English:
instance universallyClosed_snd
  signature: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f]
  body: MorphismProperty.pullback_snd f g hf

中文:
实例 universallyClosed_snd
  签名: {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f]
  定义体: MorphismProperty.pullback_snd f g hf

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance universallyClosed_snd {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [hf : UniversallyClosed f] :
    UniversallyClosed (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g hf

/--
Instance `universallyClosed_isZariskiLocalAtTarget` / 实例 `universallyClosed_isZariskiLocalAtTarget`

English:
instance universallyClosed_isZariskiLocalAtTarget
  signature: : IsZariskiLocalAtTarget @UniversallyClosed
  body: by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H

中文:
实例 universallyClosed_isZariskiLocalAtTarget
  签名: : IsZariskiLocalAtTarget @UniversallyClosed
  定义体: by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H

Depends on / 依赖: hU.isClosedMap_iff_restrictPreimage.mpr, isClosedMap_iff_restrictPreimage, morphismRestrict_base, simp_rw, topologically, universallyClosed_eq, universally_isZariskiLocalAtTarget
-/
instance universallyClosed_isZariskiLocalAtTarget : IsZariskiLocalAtTarget @UniversallyClosed := by
  rw [universallyClosed_eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact hU.isClosedMap_iff_restrictPreimage.mpr H

instance (f : X ⟶ Y) (V : Y.Opens) [UniversallyClosed f] : UniversallyClosed (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

open Scheme.Pullback _root_.PrimeSpectrum MvPolynomial in
/--
lemma `compactSpace_of_universallyClosed` / 引理 `compactSpace_of_universallyClosed`

English:
lemma compactSpace_of_universallyClosed
  proof: by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let

中文:
引理 compactSpace_of_universallyClosed
  证明: by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, IsClosed, MvPolynomial, MvPolynomial.C, MvPolynomial.X, OpenCover, Scheme, Spec.map, T.Opens, X.OpenCover, X.Opens, X.affineCover, affineCover, basicOpen, classical, opensRange, pullback, pullback.fst, pullback.snd
-/
lemma compactSpace_of_universallyClosed
    {K} [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] : CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.affineCover
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q :) := (⨆ i, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i => (fT.continuous.1 _ (Ti i).2).inter (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT '' Z)ᶜ, (fT.isClosedMap _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.I₀ K ->ₐ[K] K := MvPolynomial.aeval (fun _ => 1)
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : 𝒰.I₀) : t in Ti i := show ψ (.X i) != 0 by simp [ψ]
  have htZc : t in Zc := by
    intro ⟨z, hz, hzt⟩
    suffices exists i, fT z in Ti i ∧ p z in U i from hz (by simpa)
    exact ⟨𝒰.idx (p z), hzt ▸ ht _, by simpa [U] using 𝒰.covers (p z)⟩
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ := Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.I₀ := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.I₀ K ->+* MvPolynomial 𝒰.I₀ K :=
    (MvPolynomial.aeval fun i : 𝒰.I₀ => if i in σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' in PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT '' Z := hU'le ht'g
  suffices ⋃ i in σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ => isCompact_range (𝒰.f i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ := exists_preimage_pullback x t' (Subsingleton.elim (f x) (q t'))
  suffices forall i, t in (Ti i).comap ⟨_, continuous_comap φ⟩ -> p z ∉ U i from
    ⟨z, by simpa [Z, p, fT, hzr], hzr⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen]; rw [show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂), basicOpen_zero] at hi₁
  cases hi₁

set_option backward.isDefEq.respectTransparency false in
@[stacks 04XU]
/--
lemma `Scheme.Hom.isProperMap` / 引理 `Scheme.Hom.isProperMap`

English:
lemma Scheme.Hom.isProperMap
  given: (f : X ⟶ Y) [UniversallyClosed f]
  statement: IsProperMap f
  proof: by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y => ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField]; rw [← Scheme.Pullback.range_fst]
  exact isCompact_range (S

中文:
引理 Scheme.Hom.isProperMap
  条件: (f : X ⟶ Y) [UniversallyClosed f]
  结论: Is命题erMap f
  证明: by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y => ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField]; rw [← Scheme.Pullback.range_fst]
  exact isCompact_range (S

Depends on / 依赖: Pullback, Scheme, Scheme.Hom.continuous, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField, Y.fromSpecResidueField, compactSpace_of_universallyClosed, continuous, f.continuous, f.isClosedMap, fromSpecResidueField, isClosedMap, isCompact_range, isProperMap_iff_isClosedMap_and_compact_fibers, pullback, pullback.snd, range_fromSpecResidueField, range_fst
-/
lemma Scheme.Hom.isProperMap (f : X ⟶ Y) [UniversallyClosed f] : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨f.continuous, f.isClosedMap, fun y => ?_⟩
  have := compactSpace_of_universallyClosed (pullback.snd f (Y.fromSpecResidueField y))
  rw [← Scheme.range_fromSpecResidueField]; rw [← Scheme.Pullback.range_fst]
  exact isCompact_range (Scheme.Hom.continuous _)

instance (priority := 900) [UniversallyClosed f] : QuasiCompact f where
  isCompact_preimage _ _ := f.isProperMap.isCompact_preimage

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `universallyClosed_eq_universallySpecializing` / 引理 `universallyClosed_eq_universallySpecializing`

English:
lemma universallyClosed_eq_universallySpecializing
  proof: by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance]; rw [← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H => ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClos

中文:
引理 universallyClosed_eq_universallySpecializing
  证明: by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance]; rw [← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H => ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClos

Depends on / 依赖: QuasiCompact, UniversallyClosed, f.isClosedMap.specializingMap, isClosedMap, isClosedMap_iff_specializingMap, le_antisymm, specializingMap, universallyClosed_eq, universally_eq_iff, universally_inf, universally_mono
-/
lemma universallyClosed_eq_universallySpecializing :
    @UniversallyClosed = (topologically @SpecializingMap).universally ⊓ @QuasiCompact := by
  rw [← universally_eq_iff (P := @QuasiCompact).mpr inferInstance]; rw [← universally_inf]
  apply le_antisymm
  · rw [← universally_eq_iff (P := @UniversallyClosed).mpr inferInstance]
    exact universally_mono fun X Y f H => ⟨f.isClosedMap.specializingMap, inferInstance⟩
  · rw [universallyClosed_eq]
    exact universally_mono fun X Y f ⟨h₁, h₂⟩ => (isClosedMap_iff_specializingMap _).mpr h₁

instance (priority := low) Surjective.of_universallyClosed_of_isDominant
    [UniversallyClosed f] [IsDominant f] : Surjective f := by
  rw [surjective_iff]; rw [← Set.range_eq_univ]; rw [← f.denseRange.closure_range]; rw [f.isClosedMap.isClosed_range.closure_eq]

end AlgebraicGeometry
