/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Geometrically Reduced Schemes

## Main results
- `AlgebraicGeometry.GeometricallyReduced`:
  We say that morphism `f : X ⟶ Y` is geometrically reduced if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is reduced.
  We also provide the fact that this is stable under base change (by `infer_instance`)
- `GeometricallyReduced.iff_geometricallyReduced_fiber`:
  A scheme is geometrically reduced over `S` iff the fibers of all
  `s : S` are geometrically reduced.
- `AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`:
  If `X` is geometrically reduced and flat over a reduced and locally noetherian scheme,
  then `X` is also reduced.
  In particular, the base change of a geometrically reduced and flat scheme to an
  reduced and locally noetherian scheme is reduced (by `infer_instance`).

## TODO
Get rid of the noetherian assumption.
-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically reduced if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is reduced. -/
@[mk_iff]
/--
Definition of `GeometricallyReduced` / `GeometricallyReduced` 的定义

English:
class GeometricallyReduced
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - geometrically_isReduced : geometrically IsReduced f

中文:
类 几何既约
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - geometrically_isReduced : geometrically 是既约 f
-/
class GeometricallyReduced (f : X ⟶ Y) : Prop where
  geometrically_isReduced : geometrically IsReduced f

/--
lemma `GeometricallyReduced.eq_geometrically` / 引理 `GeometricallyReduced.eq_geometrically`

English:
lemma GeometricallyReduced.eq_geometrically
  proof: by
  ext; exact geometricallyReduced_iff _

中文:
引理 几何既约.eq_geometrically
  证明: by
  ext; exact geometricallyReduced_iff _

Depends on / 依赖: geometricallyReduced_iff
-/
lemma GeometricallyReduced.eq_geometrically :
    @GeometricallyReduced = geometrically IsReduced := by
  ext; exact geometricallyReduced_iff _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @GeometricallyReduced
  body: GeometricallyReduced.eq_geometrically ▸ inferInstance

中文:
实例 :
  签名: 是StableUnderBaseChange @几何既约
  定义体: GeometricallyReduced.eq_geometrically ▸ inferInstance

Depends on / 依赖: GeometricallyReduced, GeometricallyReduced.eq_geometrically, eq_geometrically
-/
instance : IsStableUnderBaseChange @GeometricallyReduced :=
  GeometricallyReduced.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyReduced
  signature: g] : GeometricallyReduced (pullback.fst f g)
  body: MorphismProperty.pullback_fst f g inferInstance

中文:
实例 [几何既约
  签名: g] : 几何既约 (pullback.fst f g)
  定义体: MorphismProperty.pullback_fst f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance [GeometricallyReduced g] : GeometricallyReduced (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyReduced
  signature: f] : GeometricallyReduced (pullback.snd f g)
  body: MorphismProperty.pullback_snd f g inferInstance

中文:
实例 [几何既约
  签名: f] : 几何既约 (pullback.snd f g)
  定义体: MorphismProperty.pullback_snd f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance [GeometricallyReduced f] : GeometricallyReduced (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyReduced f] : GeometricallyReduced (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (s : S) [GeometricallyReduced f] :
    GeometricallyReduced (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyReduced f] : IsReduced (f.fiber s) :=
  GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents` / 引理 `GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents`

English:
lemma GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
  proof: by
  let pt (Z : irreducibleComponents Y) := Y.presheaf.stalk Z.property.1.genericPoint
  have hpt (Z : _) : IsField (pt Z) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ _ (by
      rw [Z.property.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.property)]
      exact 

中文:
引理 几何既约.isReduced_of_flat_of_finite_irreducibleComponents
  证明: by
  let pt (Z : irreducibleComponents Y) := Y.presheaf.stalk Z.property.1.genericPoint
  have hpt (Z : _) : IsField (pt Z) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ _ (by
      rw [Z.property.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.property)]
      exact 

Depends on / 依赖: Finite, IsField, QuasiCompact, Sigma.desc, Y.fromSpecStalk, Y.presheaf.stalk, Z.property, closure_genericPoint, finite_iff, finite_iff.mp, fromSpecStalk, genericPoint, irreducibleComponents, isClosed_of_mem_irreducibleComponents, isField_stalk_of_closure_mem_irreducibleComponents, presheaf, property, sigmaMk, toField
-/
lemma GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents
    (f : X ⟶ Y) [GeometricallyReduced f] [Flat f]
    [IsReduced Y] [Finite (irreducibleComponents Y)] : IsReduced X := by
  let pt (Z : irreducibleComponents Y) := Y.presheaf.stalk Z.property.1.genericPoint
  have hpt (Z : _) : IsField (pt Z) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ _ (by
      rw [Z.property.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.property)]
      exact Z.property)
  let (Z : _) := (hpt Z).toField
  let Z := ∐ fun Z => Spec (pt Z)
  let g : Z ⟶ Y := Sigma.desc fun Z => Y.fromSpecStalk _
  have : Finite Z := (sigmaMk _).finite_iff.mp inferInstance
  have : QuasiCompact g := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have H : IsSchemeTheoreticallyDominant g := by
    rw [isSchemeTheoreticallyDominant_iff_isDominant]; rw [isDominant_iff]; rw [denseRange_iff_closure_range]; rw [Set.eq_univ_iff_forall]
    intro y
    let z : Z := Sigma.ι (fun Z => Spec (pt Z)) ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
      (IsLocalRing.closedPoint _)
    have hz : g z ⤳ y := by
      simp only [g, z, Z, ← Scheme.Hom.comp_apply, Sigma.ι_desc, pt,
        Scheme.fromSpecStalk_closedPoint]
      exact (IsIrreducible.isGenericPoint_genericPoint _
        isClosed_irreducibleComponent).specializes mem_irreducibleComponent
    exact hz.mem_closed isClosed_closure (subset_closure ⟨_, rfl⟩)
  suffices IsReduced (pullback f g) from IsSchemeTheoreticallyDominant.isReduced (pullback.fst f g)
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (X := fun Z => Spec (pt Z))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    (fun Z => Y.fromSpecStalk _) g f _ _ (fun _ => .of_hasPullback _ _) (coproductIsCoproduct _)
  apply +allowSynthFailures @isReduced_of_isOpenImmersion (f := H.isoPullback.inv)
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := sigmaOpenCover _)
  exact fun i => GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian` / 引理 `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`

English:
lemma GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
  proof: by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have : Finite ↑(irreducibleComponents ↥(Y.affineCover.X i)) := by
    let : IsNoetherian (Y.affineCover.X i) 

中文:
引理 几何既约.isReduced_of_flat_of_isLocallyNoetherian
  证明: by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have : Finite ↑(irreducibleComponents ↥(Y.affineCover.X i)) := by
    let : IsNoetherian (Y.affineCover.X i) 

Depends on / 依赖: Finite, IsNoetherian, IsReduced, IsReduced.of_openCover, NoetherianSpace, TopologicalSpace, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents, Y.affineCover.X, Y.affineCover.f, Y.affineCover.pullback, affineCover, allowSynthFailures, finite_irreducibleComponents, irreducibleComponents, isReduced_of_flat_of_finite_irreducibleComponents, isReduced_of_isOpenImmersion, of_openCover, pullback, pullback.snd
-/
lemma GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (f : X ⟶ Y) [GeometricallyReduced f] [Flat f]
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced X := by
  apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := Y.affineCover.pullback₁ f)
  intro i
  have : IsReduced (Y.affineCover.X i) := isReduced_of_isOpenImmersion (Y.affineCover.f i)
  have : Finite ↑(irreducibleComponents ↥(Y.affineCover.X i)) := by
    let : IsNoetherian (Y.affineCover.X i) := {}
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact isReduced_of_flat_of_finite_irreducibleComponents (pullback.snd _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyReduced
  signature: f] [Flat f] [IsReduced Y] [IsLocallyNoetherian Y] :
  body: GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd _ _)

中文:
实例 [几何既约
  签名: f] [平坦 f] [是既约 Y] [是LocallyNoetherian Y] :
  定义体: GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd _ _)

Depends on / 依赖: GeometricallyReduced, GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian, isReduced_of_flat_of_isLocallyNoetherian, pullback, pullback.snd
-/
instance [GeometricallyReduced f] [Flat f] [IsReduced Y] [IsLocallyNoetherian Y] :
    IsReduced (pullback f g) :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyReduced
  signature: g] [Flat g] [IsReduced X] [IsLocallyNoetherian X] :
  body: GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.fst _ _)

中文:
实例 [几何既约
  签名: g] [平坦 g] [是既约 X] [是LocallyNoetherian X] :
  定义体: GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.fst _ _)

Depends on / 依赖: GeometricallyReduced, GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian, isReduced_of_flat_of_isLocallyNoetherian, pullback, pullback.fst
-/
instance [GeometricallyReduced g] [Flat g] [IsReduced X] [IsLocallyNoetherian X] :
    IsReduced (pullback f g) :=
  GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.fst _ _)

end AlgebraicGeometry
