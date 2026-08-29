/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Kraenzle, Judith Ludwig, Bryan Wang, Christian Merten,
  Yannis Monbru, Alireza Shavali, Chenyi Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Geometrically connected schemes

In this file we define geometrically connected morphisms of schemes. A morphism `f : X ⟶ Y` is
geometrically connected if for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
In the case where `Y = Spec K` for some field `K` this recovers the standard definition
of a geometrically connected scheme over a field.

## Main results

- `AlgebraicGeometry.GeometricallyConnected`: A morphism `f : X ⟶ Y` is geometrically connected if
  for all `Spec K ⟶ Y` with `K` a field, `X ×[Y] Spec K` is connected.
- `GeometricallyConnected.iff_geometricallyConnected_fiber`: A scheme is geometrically connected
  over `S` iff the fibers of all `s : S` are geometrically connected.

-/

@[expose] public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that a morphism `f : X ⟶ Y` is geometrically connected if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is connected. -/
@[mk_iff]
/--
Definition of `GeometricallyConnected` / `GeometricallyConnected` 的定义

English:
class GeometricallyConnected
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - geometrically_connectedSpace : geometrically (ConnectedSpace ·) f

中文:
类 几何连通
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - geometrically_connectedSpace : geometrically (连通空间 ·) f
-/
class GeometricallyConnected (f : X ⟶ Y) : Prop where
  geometrically_connectedSpace : geometrically (ConnectedSpace ·) f

/--
lemma `GeometricallyConnected.eq_geometrically` / 引理 `GeometricallyConnected.eq_geometrically`

English:
lemma GeometricallyConnected.eq_geometrically
  proof: by
  ext; exact geometricallyConnected_iff _

中文:
引理 几何连通.eq_geometrically
  证明: by
  ext; exact geometricallyConnected_iff _

Depends on / 依赖: geometricallyConnected_iff
-/
lemma GeometricallyConnected.eq_geometrically :
    @GeometricallyConnected = geometrically (ConnectedSpace ·) := by
  ext; exact geometricallyConnected_iff _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @GeometricallyConnected
  body: GeometricallyConnected.eq_geometrically ▸ inferInstance

中文:
实例 :
  签名: 是StableUnderBaseChange @几何连通
  定义体: GeometricallyConnected.eq_geometrically ▸ inferInstance

Depends on / 依赖: GeometricallyConnected, GeometricallyConnected.eq_geometrically, eq_geometrically
-/
instance : IsStableUnderBaseChange @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyConnected
  signature: g] : GeometricallyConnected (pullback.fst f g)
  body: MorphismProperty.pullback_fst f g inferInstance

中文:
实例 [几何连通
  签名: g] : 几何连通 (pullback.fst f g)
  定义体: MorphismProperty.pullback_fst f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance [GeometricallyConnected g] : GeometricallyConnected (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyConnected
  signature: f] : GeometricallyConnected (pullback.snd f g)
  body: MorphismProperty.pullback_snd f g inferInstance

中文:
实例 [几何连通
  签名: f] : 几何连通 (pullback.snd f g)
  定义体: MorphismProperty.pullback_snd f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance [GeometricallyConnected f] : GeometricallyConnected (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyConnected f] : GeometricallyConnected (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (s : S) [GeometricallyConnected f] :
    GeometricallyConnected (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyConnected f] : ConnectedSpace (f.fiber s) :=
  GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)

instance (priority := low) [GeometricallyConnected f] : Surjective f :=
  ⟨fun x => ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩

/--
lemma `Scheme.Hom.isConnected_preimage_singleton` / 引理 `Scheme.Hom.isConnected_preimage_singleton`

English:
lemma Scheme.Hom.isConnected_preimage_singleton
  given: [GeometricallyConnected f] (x : S)
  proof: by
  rw [← f.range_fiberι]; rw [← Set.image_univ]
  exact isConnected_univ.image _ (f.fiberι _).continuous.continuousOn

中文:
引理 概形.态射.isConnected_preimage_singleton
  条件: [几何连通 f] (x : S)
  证明: by
  rw [← f.range_fiberι]; rw [← Set.image_univ]
  exact isConnected_univ.image _ (f.fiberι _).continuous.continuousOn

Depends on / 依赖: Set.image_univ, continuous, continuous.continuousOn, continuousOn, f.fiber, f.range_fiber, image_univ, isConnected_univ, isConnected_univ.image
-/
lemma Scheme.Hom.isConnected_preimage_singleton [GeometricallyConnected f] (x : S) :
    _root_.IsConnected (f ⁻¹' {x}) := by
  rw [← f.range_fiberι]; rw [← Set.image_univ]
  exact isConnected_univ.image _ (f.fiberι _).continuous.continuousOn

/--
lemma `Scheme.Hom.isConnected_preimage` / 引理 `Scheme.Hom.isConnected_preimage`

English:
lemma Scheme.Hom.isConnected_preimage
  statement: [GeometricallyConnected f] (hf : IsOpenMap f)
  proof: by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed f.isConnected_preimage_singleton
    ?_ hs' hs
  exact (hf.isQuotientMap f.continuous f.surjective).isCoinducing

中文:
引理 概形.态射.isConnected_preimage
  结论: [几何连通 f] (hf : 是开映射 f)
  证明: by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed f.isConnected_preimage_singleton
    ?_ hs' hs
  exact (hf.isQuotientMap f.continuous f.surjective).isCoinducing

Depends on / 依赖: IsCoinducing, Topology, Topology.IsCoinducing.isConnected_preimage_of_isClosed, continuous, f.continuous, f.isConnected_preimage_singleton, f.surjective, hf.isQuotientMap, isCoinducing, isConnected_preimage_of_isClosed, isConnected_preimage_singleton, isQuotientMap, surjective
-/
lemma Scheme.Hom.isConnected_preimage [GeometricallyConnected f] (hf : IsOpenMap f)
    {s : Set S} (hs : _root_.IsConnected s) (hs' : IsClosed s) : _root_.IsConnected (f ⁻¹' s) := by
  refine Topology.IsCoinducing.isConnected_preimage_of_isClosed f.isConnected_preimage_singleton
    ?_ hs' hs
  exact (hf.isQuotientMap f.continuous f.surjective).isCoinducing

/-- If `f : X ⟶ S` is geometrically connected and open,
then `f` induces a homeomorphism between the connected components of `X` and `S`. -/
@[simps! apply]
noncomputable
/--
Definition of `Scheme.Hom.connectedComponentsHomeomorph` / `Scheme.Hom.connectedComponentsHomeomorph` 的定义

English:
definition Scheme.Hom.connectedComponentsHomeomorph
  signature: [GeometricallyConnected f] (hf : IsOpenMap f)
  body: (hf.isQuotientMap f.continuous f.surjective).isCoinducing.connectedComponentsHomeomorph
    f.isConnected_preimage_singleton

中文:
定义 概形.态射.connectedComponentsHomeomorph
  签名: [几何连通 f] (hf : 是开映射 f)
  定义体: (hf.isQuotientMap f.continuous f.surjective).isCoinducing.connectedComponentsHomeomorph
    f.isConnected_preimage_singleton

Depends on / 依赖: connectedComponentsHomeomorph, continuous, f.continuous, f.isConnected_preimage_singleton, f.surjective, hf.isQuotientMap, isCoinducing, isCoinducing.connectedComponentsHomeomorph, isConnected_preimage_singleton, isQuotientMap, surjective
-/
def Scheme.Hom.connectedComponentsHomeomorph [GeometricallyConnected f] (hf : IsOpenMap f) :
    ConnectedComponents X ≃ₜ ConnectedComponents S :=
  (hf.isQuotientMap f.continuous f.surjective).isCoinducing.connectedComponentsHomeomorph
    f.isConnected_preimage_singleton

/--
lemma `GeometricallyConnected.connectedSpace` / 引理 `GeometricallyConnected.connectedSpace`

English:
lemma GeometricallyConnected.connectedSpace
  statement: [GeometricallyConnected f] [ConnectedSpace S]
  proof: by
  simpa [connectedSpace_iff_univ] using f.isConnected_preimage hf isConnected_univ

中文:
引理 几何连通.connectedSpace
  结论: [几何连通 f] [连通空间 S]
  证明: by
  simpa [connectedSpace_iff_univ] using f.isConnected_preimage hf isConnected_univ

Depends on / 依赖: connectedSpace_iff_univ, f.isConnected_preimage, isConnected_preimage, isConnected_univ, mono_of_mono_fac
-/
lemma GeometricallyConnected.connectedSpace [GeometricallyConnected f] [ConnectedSpace S]
    (hf : IsOpenMap f) :
    ConnectedSpace X := by
  simpa [connectedSpace_iff_univ] using f.isConnected_preimage hf isConnected_univ

/--
lemma `GeometricallyConnected.connectedSpace_of_subsingleton` / 引理 `GeometricallyConnected.connectedSpace_of_subsingleton`

English:
lemma GeometricallyConnected.connectedSpace_of_subsingleton
  proof: have : ConnectedSpace S := ⟨‹_›⟩
  GeometricallyConnected.connectedSpace (f := f) fun _ _ => isOpen_discrete _

中文:
引理 几何连通.connectedSpace_of_subsingleton
  证明: have : ConnectedSpace S := ⟨‹_›⟩
  GeometricallyConnected.connectedSpace (f := f) fun _ _ => isOpen_discrete _

Depends on / 依赖: ConnectedSpace, GeometricallyConnected, GeometricallyConnected.connectedSpace, connectedSpace, epi_of_epi_fac, isOpen_discrete
-/
lemma GeometricallyConnected.connectedSpace_of_subsingleton
    [GeometricallyConnected f] [Subsingleton S] [Nonempty S] : ConnectedSpace X :=
  have : ConnectedSpace S := ⟨‹_›⟩
  GeometricallyConnected.connectedSpace (f := f) fun _ _ => isOpen_discrete _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyConnected
  signature: f] [UniversallyOpen f] [ConnectedSpace Y] :
  body: GeometricallyConnected.connectedSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

中文:
实例 [几何连通
  签名: f] [普遍开 f] [连通空间 Y] :
  定义体: GeometricallyConnected.connectedSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

Depends on / 依赖: GeometricallyConnected, GeometricallyConnected.connectedSpace, connectedSpace, isOpenMap, pullback, pullback.snd
-/
instance [GeometricallyConnected f] [UniversallyOpen f] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.snd _ _) (pullback.snd f g).isOpenMap

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyConnected
  signature: g] [UniversallyOpen g] [ConnectedSpace X] :
  body: GeometricallyConnected.connectedSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

中文:
实例 [几何连通
  签名: g] [普遍开 g] [连通空间 X] :
  定义体: GeometricallyConnected.connectedSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

Depends on / 依赖: GeometricallyConnected, GeometricallyConnected.connectedSpace, connectedSpace, isOpenMap, pullback, pullback.fst
-/
instance [GeometricallyConnected g] [UniversallyOpen g] [ConnectedSpace X] :
    ConnectedSpace ↥(pullback f g) :=
  GeometricallyConnected.connectedSpace (pullback.fst _ _) (pullback.fst f g).isOpenMap

/--
lemma `GeometricallyConnected.iff_geometricallyConnected_fiber` / 引理 `GeometricallyConnected.iff_geometricallyConnected_fiber`

English:
lemma GeometricallyConnected.iff_geometricallyConnected_fiber
  proof: by
  simp only [eq_geometrically, ← geometrically_iff_forall_fiberToSpecResidueField]

中文:
引理 几何连通.iff_geometricallyConnected_fiber
  证明: by
  simp only [eq_geometrically, ← geometrically_iff_forall_fiberToSpecResidueField]

Depends on / 依赖: eq_geometrically, geometrically_iff_forall_fiberToSpecResidueField
-/
lemma GeometricallyConnected.iff_geometricallyConnected_fiber :
    GeometricallyConnected f ↔ forall s, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  simp only [eq_geometrically, ← geometrically_iff_forall_fiberToSpecResidueField]

/--
lemma `GeometricallyConnected.comp` / 引理 `GeometricallyConnected.comp`

English:
lemma GeometricallyConnected.comp
  proof: by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  infer_instance

中文:
引理 几何连通.comp
  证明: by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  infer_instance

Depends on / 依赖: connectedSpace_iff, geometrically_iff_of_isClosedUnderIsomorphisms, geometrically_iff_of_isClosedUnderIsomorphisms.mpr, hom.homeomorph.connectedSpace_iff, homeomorph, infer_instance, pullbackRightPullbackFstIso
-/
lemma GeometricallyConnected.comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected f] [GeometricallyConnected g]
    [UniversallyOpen f] [UniversallyOpen g] :
    GeometricallyConnected (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  rw [← (pullbackRightPullbackFstIso g x f).hom.homeomorph.connectedSpace_iff]
  infer_instance

end AlgebraicGeometry
