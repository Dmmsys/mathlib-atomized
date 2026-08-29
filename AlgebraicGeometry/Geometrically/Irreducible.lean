/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically Irreducible Schemes

## Main results
- `AlgebraicGeometry.GeometricallyIrreducible`:
  We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is irreducible.
  We also provide the fact that this is stable under base change (by `infer_instance`)
- `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber`:
  A scheme is geometrically irreducible over `S` iff the fibers of all
  `s : S` are geometrically irreducible.
- `AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace`:
  If `X` is geometrically irreducible and universally open (e.g. when flat + finite presentation),
  over an irreducible scheme, then `X` is also irreducible.
  In particular, the base change of a geometrically irreducible and universally open scheme to an
  irreducible scheme is irreducible (by `infer_instance`).
-/

universe u

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically irreducible if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is irreducible. -/
@[mk_iff]
/--
Definition of `GeometricallyIrreducible` / `GeometricallyIrreducible` 的定义

English:
class GeometricallyIrreducible
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - geometrically_irreducibleSpace : geometrically (IrreducibleSpace ·) f

中文:
类 几何不可约
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - geometrically_irreducibleSpace : geometrically (不可约空间 ·) f
-/
class GeometricallyIrreducible (f : X ⟶ Y) : Prop where
  geometrically_irreducibleSpace : geometrically (IrreducibleSpace ·) f

/--
lemma `GeometricallyIrreducible.eq_geometrically` / 引理 `GeometricallyIrreducible.eq_geometrically`

English:
lemma GeometricallyIrreducible.eq_geometrically
  proof: by
  ext; exact geometricallyIrreducible_iff _

中文:
引理 几何不可约.eq_geometrically
  证明: by
  ext; exact geometricallyIrreducible_iff _

Depends on / 依赖: geometricallyIrreducible_iff
-/
lemma GeometricallyIrreducible.eq_geometrically :
    @GeometricallyIrreducible = geometrically (IrreducibleSpace ·) := by
  ext; exact geometricallyIrreducible_iff _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @GeometricallyIrreducible
  body: GeometricallyIrreducible.eq_geometrically ▸ inferInstance

中文:
实例 :
  签名: 是StableUnderBaseChange @几何不可约
  定义体: GeometricallyIrreducible.eq_geometrically ▸ inferInstance

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.eq_geometrically, eq_geometrically
-/
instance : IsStableUnderBaseChange @GeometricallyIrreducible :=
  GeometricallyIrreducible.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIrreducible
  signature: g] : GeometricallyIrreducible (pullback.fst f g)
  body: MorphismProperty.pullback_fst f g inferInstance

中文:
实例 [几何不可约
  签名: g] : 几何不可约 (pullback.fst f g)
  定义体: MorphismProperty.pullback_fst f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, SimplexCategory, SimplexCategory.mono_iff_injective, homEquiv, injective, mono_iff_injective, pullback_fst
-/
instance [GeometricallyIrreducible g] : GeometricallyIrreducible (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIrreducible
  signature: f] : GeometricallyIrreducible (pullback.snd f g)
  body: MorphismProperty.pullback_snd f g inferInstance

中文:
实例 [几何不可约
  签名: f] : 几何不可约 (pullback.snd f g)
  定义体: MorphismProperty.pullback_snd f g inferInstance

Depends on / 依赖: Functor, Functor.map_comp, MorphismProperty, MorphismProperty.pullback_snd, cancel_mono, map_comp, map_injective, pullback_snd, toSimplexCategory, toSimplexCategory.map, toSimplexCategory.map_injective
-/
instance [GeometricallyIrreducible f] : GeometricallyIrreducible (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyIrreducible f] : GeometricallyIrreducible (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (s : S) [GeometricallyIrreducible f] :
    GeometricallyIrreducible (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyIrreducible f] : IrreducibleSpace (f.fiber s) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)

instance (priority := low) [GeometricallyIrreducible f] : Surjective f :=
  ⟨fun x => ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩

/--
lemma `Scheme.Hom.isIrreducible_preimage` / 引理 `Scheme.Hom.isIrreducible_preimage`

English:
lemma Scheme.Hom.isIrreducible_preimage
  proof: by
  wlog H : exists x, s = {x} generalizing s
  · refine hs.preimage_of_isPreirreducible_fiber _ hf
      (fun x => (this isIrreducible_singleton ⟨_, rfl⟩).isPreirreducible) ?_
    rw [Set.range_eq_univ.mpr f.surjective]; rw [Set.inter_univ]
    exact hs.nonempty
  obtain ⟨s, rfl⟩ := H
  rw [← f.ra

中文:
引理 概形.态射.isIrreducible_preimage
  证明: by
  wlog H : exists x, s = {x} generalizing s
  · refine hs.preimage_of_isPreirreducible_fiber _ hf
      (fun x => (this isIrreducible_singleton ⟨_, rfl⟩).isPreirreducible) ?_
    rw [Set.range_eq_univ.mpr f.surjective]; rw [Set.inter_univ]
    exact hs.nonempty
  obtain ⟨s, rfl⟩ := H
  rw [← f.ra

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, Set.image_univ, Set.inter_univ, Set.range_eq_univ.mpr, continuous, continuous.continuousOn, continuousOn, f.fiber, f.range_fiber, f.surjective, generalizing, hs.nonempty, hs.preimage_of_isPreirreducible_fiber, image_univ, inter_univ, isIrreducible_singleton, isIrreducible_univ, isPreirreducible, nonempty
-/
lemma Scheme.Hom.isIrreducible_preimage
    [GeometricallyIrreducible f] (hf : IsOpenMap f)
    {s : Set S} (hs : IsIrreducible s) : IsIrreducible (f ⁻¹' s) := by
  wlog H : exists x, s = {x} generalizing s
  · refine hs.preimage_of_isPreirreducible_fiber _ hf
      (fun x => (this isIrreducible_singleton ⟨_, rfl⟩).isPreirreducible) ?_
    rw [Set.range_eq_univ.mpr f.surjective]; rw [Set.inter_univ]
    exact hs.nonempty
  obtain ⟨s, rfl⟩ := H
  rw [← f.range_fiberι]; rw [← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι _).continuous.continuousOn

/-- If `f : X ⟶ S` is geometrically irreducible and open,
then `f` induces an equivalence between the irreducible components of `X` and `S`. -/
@[simps!]
/--
Definition of `Scheme.Hom.irreducibleComponentsEquiv` / `Scheme.Hom.irreducibleComponentsEquiv` 的定义

English:
definition Scheme.Hom.irreducibleComponentsEquiv
  signature: [GeometricallyIrreducible f] (hf : IsOpenMap f)
  body: (irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous hf
    (fun _ => (f.isIrreducible_preimage hf isIrreducible_singleton).isPreirreducible)
    f.surjective).symm.toEquiv

中文:
定义 概形.态射.irreducibleComponentsEquiv
  签名: [几何不可约 f] (hf : 是开映射 f)
  定义体: (irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous hf
    (fun _ => (f.isIrreducible_preimage hf isIrreducible_singleton).isPreirreducible)
    f.surjective).symm.toEquiv

Depends on / 依赖: continuous, f.continuous, f.isIrreducible_preimage, f.surjective, irreducibleComponentsEquivOfIsPreirreducibleFiber, isIrreducible_preimage, isIrreducible_singleton, isPreirreducible, surjective, symm.toEquiv, toEquiv
-/
def Scheme.Hom.irreducibleComponentsEquiv [GeometricallyIrreducible f] (hf : IsOpenMap f) :
    irreducibleComponents X ≃ irreducibleComponents S :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber f f.continuous hf
    (fun _ => (f.isIrreducible_preimage hf isIrreducible_singleton).isPreirreducible)
    f.surjective).symm.toEquiv

/--
lemma `GeometricallyIrreducible.irreducibleSpace` / 引理 `GeometricallyIrreducible.irreducibleSpace`

English:
lemma GeometricallyIrreducible.irreducibleSpace
  proof: by
  simpa [irreducibleSpace_def] using
    f.isIrreducible_preimage hf (IrreducibleSpace.isIrreducible_univ _)

中文:
引理 几何不可约.irreducibleSpace
  证明: by
  simpa [irreducibleSpace_def] using
    f.isIrreducible_preimage hf (IrreducibleSpace.isIrreducible_univ _)

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, f.isIrreducible_preimage, irreducibleSpace_def, isIrreducible_preimage, isIrreducible_univ
-/
lemma GeometricallyIrreducible.irreducibleSpace
    [GeometricallyIrreducible f] [IrreducibleSpace S] (hf : IsOpenMap f) : IrreducibleSpace X := by
  simpa [irreducibleSpace_def] using
    f.isIrreducible_preimage hf (IrreducibleSpace.isIrreducible_univ _)

/--
lemma `GeometricallyIrreducible.irreducibleSpace_of_subsingleton` / 引理 `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`

English:
lemma GeometricallyIrreducible.irreducibleSpace_of_subsingleton
  proof: have : IrreducibleSpace S := ⟨‹_›⟩
  GeometricallyIrreducible.irreducibleSpace (f := f) fun _ _ => isOpen_discrete _

中文:
引理 几何不可约.irreducibleSpace_of_subsingleton
  证明: have : IrreducibleSpace S := ⟨‹_›⟩
  GeometricallyIrreducible.irreducibleSpace (f := f) fun _ _ => isOpen_discrete _

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace, IrreducibleSpace, irreducibleSpace, isOpen_discrete
-/
lemma GeometricallyIrreducible.irreducibleSpace_of_subsingleton
    [GeometricallyIrreducible f] [Subsingleton S] [Nonempty S] : IrreducibleSpace X :=
  have : IrreducibleSpace S := ⟨‹_›⟩
  GeometricallyIrreducible.irreducibleSpace (f := f) fun _ _ => isOpen_discrete _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIrreducible
  signature: f] [UniversallyOpen f] [IrreducibleSpace Y] :
  body: GeometricallyIrreducible.irreducibleSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

中文:
实例 [几何不可约
  签名: f] [普遍开 f] [不可约空间 Y] :
  定义体: GeometricallyIrreducible.irreducibleSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace, irreducibleSpace, isOpenMap, pullback, pullback.snd
-/
instance [GeometricallyIrreducible f] [UniversallyOpen f] [IrreducibleSpace Y] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIrreducible
  signature: g] [UniversallyOpen g] [IrreducibleSpace X] :
  body: GeometricallyIrreducible.irreducibleSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

中文:
实例 [几何不可约
  签名: g] [普遍开 g] [不可约空间 X] :
  定义体: GeometricallyIrreducible.irreducibleSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace, irreducibleSpace, isOpenMap, pullback, pullback.fst
-/
instance [GeometricallyIrreducible g] [UniversallyOpen g] [IrreducibleSpace X] :
    IrreducibleSpace ↥(pullback f g) :=
  GeometricallyIrreducible.irreducibleSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

/--
lemma `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber` / 引理 `GeometricallyIrreducible.iff_geometricallyIrreducible_fiber`

English:
lemma GeometricallyIrreducible.iff_geometricallyIrreducible_fiber
  proof: by
  simp only [GeometricallyIrreducible.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

中文:
引理 几何不可约.iff_geometricallyIrreducible_fiber
  证明: by
  simp only [GeometricallyIrreducible.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.eq_geometrically, eq_geometrically, geometrically_iff_forall_fiberToSpecResidueField
-/
lemma GeometricallyIrreducible.iff_geometricallyIrreducible_fiber :
    GeometricallyIrreducible f ↔ forall s, GeometricallyIrreducible (f.fiberToSpecResidueField s) := by
  simp only [GeometricallyIrreducible.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

/--
lemma `GeometricallyIrreducible.comp` / 引理 `GeometricallyIrreducible.comp`

English:
lemma GeometricallyIrreducible.comp
  proof: by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

中文:
引理 几何不可约.comp
  证明: by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

Depends on / 依赖: geometrically_iff_of_isClosedUnderIsomorphisms, geometrically_iff_of_isClosedUnderIsomorphisms.mpr, hom.homeomorph.irreducibleSpace_iff, homeomorph, infer_instance, irreducibleSpace_iff, pullbackRightPullbackFstIso
-/
lemma GeometricallyIrreducible.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyIrreducible f] [GeometricallyIrreducible g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyIrreducible (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.irreducibleSpace_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If an open subscheme `U` of `X` surjects onto `S` and `X` is geometrically irreducible over `S`,
then also `U` is geometrically irreducible over `S`. -/
instance {U : Scheme.{u}} {f : U ⟶ X} {g : X ⟶ S} [IsOpenImmersion f] [GeometricallyIrreducible g]
    [Surjective (f ≫ g)] :
    GeometricallyIrreducible (f ≫ g) := by
  rw [GeometricallyIrreducible.iff_geometricallyIrreducible_fiber]
  intro s
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  let i : pullback ((f ≫ g).fiberToSpecResidueField s) x ⟶
      pullback (g.fiberToSpecResidueField s) x :=
    pullback.map _ _ _ _ (pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp) (by simp)) (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)
  have : Nonempty ((f ≫ g).fiber s) := by
    rw [((f ≫ g).fiberHomeo s).nonempty_congr]; rw [Set.nonempty_coe_sort]
    exact (Set.singleton_nonempty s).preimage (f ≫ g).surjective
  exact i.isOpenEmbedding.irreducibleSpace

end AlgebraicGeometry
