/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally injective morphism

A morphism of schemes `f : X ⟶ Y` is universally injective if `X ×[Y] Y' ⟶ Y'` is injective
for all base changes `Y' ⟶ Y`. This is equivalent to the diagonal morphism being surjective
(`AlgebraicGeometry.UniversallyInjective.iff_diagonal`).

We show that being universally injective is local at the target, and is stable under
compositions and base changes.

We also prove that universally injective is equivalent to being injective with
purely inseparable residue field extensions (also known as a radical morphism), see
`AlgebraicGeometry.tfae_universallyInjective` and Stacks tag 01S4.

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty Function

/--
A morphism of schemes `f : X ⟶ Y` is universally injective if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is injective (on points).
-/
@[mk_iff]
/--
Definition of `UniversallyInjective` / `UniversallyInjective` 的定义

English:
class UniversallyInjective
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - universally_injective : universally (topologically (Injective ·)) f

中文:
类 UniversallyInjective
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - universally_injective : universally (topologically (Injective ·)) f
-/
class UniversallyInjective (f : X ⟶ Y) : Prop where
  universally_injective : universally (topologically (Injective ·)) f

/--
theorem `Scheme.Hom.injective` / 定理 `Scheme.Hom.injective`

English:
theorem Scheme.Hom.injective
  given: (f : X ⟶ Y) [UniversallyInjective f]
  proof: UniversallyInjective.universally_injective _ _ _ .of_id_snd

中文:
定理 Scheme.Hom.injective
  条件: (f : X ⟶ Y) [UniversallyInjective f]
  证明: UniversallyInjective.universally_injective _ _ _ .of_id_snd

Depends on / 依赖: UniversallyInjective, UniversallyInjective.universally_injective, of_id_snd, universally_injective
-/
theorem Scheme.Hom.injective (f : X ⟶ Y) [UniversallyInjective f] :
    Function.Injective f :=
  UniversallyInjective.universally_injective _ _ _ .of_id_snd

/--
theorem `universallyInjective_eq` / 定理 `universallyInjective_eq`

English:
theorem universallyInjective_eq
  proof: by
  ext X Y f; rw [universallyInjective_iff]

中文:
定理 universallyInjective_eq
  证明: by
  ext X Y f; rw [universallyInjective_iff]

Depends on / 依赖: universallyInjective_iff
-/
theorem universallyInjective_eq :
    @UniversallyInjective = universally (topologically (Injective ·)) := by
  ext X Y f; rw [universallyInjective_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `universallyInjective_eq_diagonal` / 定理 `universallyInjective_eq_diagonal`

English:
theorem universallyInjective_eq_diagonal
  proof: by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x => ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply]; rw [pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),


中文:
定理 universallyInjective_eq_diagonal
  证明: by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x => ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply]; rw [pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),


Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, IsStableUnderBaseChange, Pullback, Scheme, Scheme.Hom.comp_appl, Scheme.Hom.comp_apply, Scheme.Pullback.exists_preimage_pullback, Surjective, comp_appl, comp_apply, diagonal, diagonal_fst, exists_preimage_pullback, le_antisymm, of_hasPullback, pullback, pullback.diagonal_fst, pullback.fst, universallyInjective_eq
-/
theorem universallyInjective_eq_diagonal :
    @UniversallyInjective = diagonal @Surjective := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x => ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply]; rw [pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),
      universallyInjective_eq]
    apply universally_mono
    intro X Y f hf x₁ x₂ e
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    obtain ⟨t, rfl⟩ := hf.1 t
    rw [← ht₁]; rw [← ht₂]; rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply]; rw [pullback.diagonal_fst]; rw [pullback.diagonal_snd]

/--
theorem `UniversallyInjective.iff_diagonal` / 定理 `UniversallyInjective.iff_diagonal`

English:
theorem UniversallyInjective.iff_diagonal
  proof: by
  rw [universallyInjective_eq_diagonal]; rfl

中文:
定理 UniversallyInjective.iff_diagonal
  证明: by
  rw [universallyInjective_eq_diagonal]; rfl

Depends on / 依赖: universallyInjective_eq_diagonal
-/
theorem UniversallyInjective.iff_diagonal :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) := by
  rw [universallyInjective_eq_diagonal]; rfl

instance (priority := 900) [Mono f] : UniversallyInjective f :=
  have := (pullback.isIso_diagonal_iff f).mpr inferInstance
  (UniversallyInjective.iff_diagonal f).mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `UniversallyInjective.respectsIso` / 定理 `UniversallyInjective.respectsIso`

English:
theorem UniversallyInjective.respectsIso
  statement: RespectsIso @UniversallyInjective
  proof: universallyInjective_eq_diagonal.symm ▸ inferInstance

中文:
定理 UniversallyInjective.respectsIso
  结论: RespectsIso @UniversallyInjective
  证明: universallyInjective_eq_diagonal.symm ▸ inferInstance

Depends on / 依赖: universallyInjective_eq_diagonal, universallyInjective_eq_diagonal.symm
-/
theorem UniversallyInjective.respectsIso : RespectsIso @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `UniversallyInjective.isStableUnderBaseChange` / 实例 `UniversallyInjective.isStableUnderBaseChange`

English:
instance UniversallyInjective.isStableUnderBaseChange
  signature: :
  body: universallyInjective_eq_diagonal.symm ▸ inferInstance

中文:
实例 UniversallyInjective.isStableUnderBaseChange
  签名: :
  定义体: universallyInjective_eq_diagonal.symm ▸ inferInstance

Depends on / 依赖: universallyInjective_eq_diagonal, universallyInjective_eq_diagonal.symm
-/
instance UniversallyInjective.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

/--
Instance `universallyInjective_isStableUnderComposition` / 实例 `universallyInjective_isStableUnderComposition`

English:
instance universallyInjective_isStableUnderComposition
  signature: :
  body: universallyInjective_eq ▸ inferInstance

中文:
实例 universallyInjective_isStableUnderComposition
  签名: :
  定义体: universallyInjective_eq ▸ inferInstance

Depends on / 依赖: universallyInjective_eq
-/
instance universallyInjective_isStableUnderComposition :
    IsStableUnderComposition @UniversallyInjective :=
  universallyInjective_eq ▸ inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @UniversallyInjective
  body: inferInstance

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @UniversallyInjective
  定义体: inferInstance
-/
instance : MorphismProperty.IsMultiplicative @UniversallyInjective where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `universallyInjective_isZariskiLocalAtTarget` / 实例 `universallyInjective_isZariskiLocalAtTarget`

English:
instance universallyInjective_isZariskiLocalAtTarget
  signature: :
  body: universallyInjective_eq_diagonal.symm ▸ inferInstance

中文:
实例 universallyInjective_isZariskiLocalAtTarget
  签名: :
  定义体: universallyInjective_eq_diagonal.symm ▸ inferInstance

Depends on / 依赖: universallyInjective_eq_diagonal, universallyInjective_eq_diagonal.symm
-/
instance universallyInjective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[stacks 01S4]
/--
theorem `tfae_universallyInjective` / 定理 `tfae_universallyInjective`

English:
theorem tfae_universallyInjective
  proof: by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 -> 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    dsimp at e h
    simp only [Scheme.d

中文:
定理 tfae_universallyInjective
  证明: by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 -> 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    dsimp at e h
    simp only [Scheme.d

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff, IsLocalRing, IsLocalRing.closedPoint, Scheme, Scheme.SpecToEquivOfField_eq_iff, Scheme.SpecToEquivOfField_eq_iff.mp, Scheme.descResidueField_stalkClosedPointTo_comp, SpecToEquivOfField, SpecToEquivOfField_eq_iff, UniversallyInjective, UniversallyInjective.iff_diagonal, X.SpecToEquivOfField, Y.SpecToEquivOfField, _assoc, closedPoint, descResidueField_stalkClosedPointTo_comp, f.residueFieldMap_congr, h_inj, hom_ext_iff
-/
theorem tfae_universallyInjective :
    List.TFAE [
      UniversallyInjective f,
      forall (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X => g ≫ f),
      Function.Injective f ∧ forall x, (f.residueFieldMap x).hom.IsPurelyInseparable,
      Surjective (pullback.diagonal f) ] := by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 -> 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    dsimp at e h
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp] at e h
    rw [← f.residueFieldMap_congr'_assoc (h_inj e)]; rw [CommRingCat.hom_ext_iff] at h
    rw [Scheme.SpecToEquivOfField_eq_iff]
    let x := g₁ (IsLocalRing.closedPoint K)
    have hfx := hf x
    algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
    refine ⟨h_inj e, CommRingCat.hom_ext ?_⟩
    exact IsPurelyInseparable.injective_comp_algebraMap
      (Y.residueField (f x)) (X.residueField x) _ h
  tfae_have 2 -> 4 := fun h => by
    rw [surjective_iff]
    intro z
    let φ := (pullback f f).fromSpecResidueField z
    have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
      h ((pullback f f).residueField z) (by simp [pullback.condition])
    have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by cat_disch
    refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply]; rw [← hφ₂]; rw [Scheme.fromSpecResidueField_apply]
  tfae_have 4 -> 3 := fun hf => by
    have := tfae_1_iff_4.mpr hf
    refine ⟨f.injective, ?_⟩
    rw [surjective_iff] at hf
    intro x
    algebraize [(f.residueFieldMap x).hom]
    rw [RingHom.IsPurelyInseparable]; rw [isPurelyInseparable_iff_subsingleton_emb]; rw [subsingleton_iff]
    intro σ₁ σ₂
    apply AlgHom.coe_ringHom_injective
    let g₁ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₁.toRingHom⟩
    let g₂ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₂.toRingHom⟩
    suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by
      rw [Equiv.apply_symm_apply]; rw [Equiv.apply_symm_apply] at this
      exact congr($(this).2.hom)
let q := pullback.lift (f := f) (g := f) g₁ g₂ by
      simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
        Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
      congr 2
      ext a
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm
    have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    rw [Scheme.SpecToEquivOfField_eq_iff]; rw [← q_fst]; rw [← q_snd]
    obtain ⟨u, hu⟩ := hf (q (IsLocalRing.closedPoint _))
    have hux : u = x := by
      have := congr(pullback.fst f f $(hu))
      rw [← Scheme.Hom.comp_apply]; rw [← Scheme.Hom.comp_apply] at this
      simpa [Scheme.SpecToEquivOfField_symm_apply, q_fst, g₁] using this
    refine ⟨by simp [g₁, g₂, q_fst, q_snd], ?_⟩
    dsimp
    simp only [Scheme.descResidueField_stalkClosedPointTo_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.residueFieldCongr (hux ▸ hu).symm).hom]
    have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) x) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    simp [← cancel_mono ((pullback.diagonal f).residueFieldMap x), ← Scheme.residueFieldMap_comp,
      (pullback.fst f f).residueFieldMap_congr', (pullback.snd f f).residueFieldMap_congr'_assoc,
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)]
  tfae_finish

end AlgebraicGeometry
