/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Scheme-theoretically dominant morphisms

In this file, we define scheme-theoretically dominant morphisms as morphisms with trivial kernel.

## Main results
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant`:
  The class of scheme-theoretically dominant morphisms.
- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant`:
  If the target is reduced and the map is quasi-compact, then scheme-theoretically dominant
  is equivalent to dominant.
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`:
  quasicompact + scheme-theoretically dominant is stable under flat base change.

-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- A morphism is scheme-theoretically dominant if its kernel is trivial. -/
@[mk_iff]
/--
Definition of `IsSchemeTheoreticallyDominant` / `IsSchemeTheoreticallyDominant` 的定义

English:
class IsSchemeTheoreticallyDominant
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - ker_eq_bot((f)) : f.ker = ⊥

中文:
类 是SchemeTheoreticallyDominant
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - ker_eq_bot((f)) : f.ker = ⊥

Depends on / 依赖: IsSchemeTheoreticallyDominant, IsSchemeTheoreticallyDominant.ker_eq_bot, ker_eq_bot
-/
class IsSchemeTheoreticallyDominant (f : X ⟶ Y) : Prop where
  ker_eq_bot (f) : f.ker = ⊥

alias Scheme.Hom.ker_eq_bot := IsSchemeTheoreticallyDominant.ker_eq_bot

instance (priority := low) [IsIso f] : IsSchemeTheoreticallyDominant f :=
  ⟨by simp⟩

instance (priority := low) [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    IsDominant f := by
  rw [isDominant_iff]; rw [DenseRange]; rw [dense_iff_closure_eq]; rw [← Scheme.Hom.support_ker]; rw [f.ker_eq_bot]; rw [Scheme.IdealSheafData.support_bot]; rw [TopologicalSpace.Closeds.coe_top]

instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsSchemeTheoreticallyDominant f]
    [IsSchemeTheoreticallyDominant g] :
    IsSchemeTheoreticallyDominant (f ≫ g) := by
  rw [isSchemeTheoreticallyDominant_iff]; rw [Scheme.Hom.ker_comp]; rw [f.ker_eq_bot]; rw [Scheme.IdealSheafData.map_bot]; rw [g.ker_eq_bot]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative @IsSchemeTheoreticallyDominant
  body: inferInstance
  comp_mem _ _ _ _ := inferInstance

中文:
实例 :
  签名: 是Multiplicative @是SchemeTheoreticallyDominant
  定义体: inferInstance
  comp_mem _ _ _ _ := inferInstance
-/
instance : IsMultiplicative @IsSchemeTheoreticallyDominant where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/--
lemma `IsSchemeTheoreticallyDominant.of_isDominant` / 引理 `IsSchemeTheoreticallyDominant.of_isDominant`

English:
lemma IsSchemeTheoreticallyDominant.of_isDominant
  given: (f : X ⟶ Y) [IsDominant f] [IsReduced Y]
  proof: by
  rw [isSchemeTheoreticallyDominant_iff]; rw [← Scheme.IdealSheafData.support_eq_top_iff]; rw [← SetLike.coe_injective.eq_iff]; rw [TopologicalSpace.Closeds.coe_top]; rw [← Set.univ_subset_iff]; rw [← f.denseRange.closure_eq]; rw [f.ker.support.isClosed.closure_subset_iff]
  exact f.range_subset_

中文:
引理 是SchemeTheoreticallyDominant.of_isDominant
  条件: (f : X ⟶ Y) [是Dominant f] [是既约 Y]
  证明: by
  rw [isSchemeTheoreticallyDominant_iff]; rw [← Scheme.IdealSheafData.support_eq_top_iff]; rw [← SetLike.coe_injective.eq_iff]; rw [TopologicalSpace.Closeds.coe_top]; rw [← Set.univ_subset_iff]; rw [← f.denseRange.closure_eq]; rw [f.ker.support.isClosed.closure_subset_iff]
  exact f.range_subset_

Depends on / 依赖: Closeds, IdealSheafData, Scheme, Scheme.IdealSheafData.support_eq_top_iff, Set.univ_subset_iff, SetLike, SetLike.coe_injective.eq_iff, TopologicalSpace, TopologicalSpace.Closeds.coe_top, closure_eq, closure_subset_iff, coe_injective, coe_top, denseRange, eq_iff, f.denseRange.closure_eq, f.ker.support.isClosed.closure_subset_iff, f.range_subset_ker_support, isClosed, isSchemeTheoreticallyDominant_iff
-/
lemma IsSchemeTheoreticallyDominant.of_isDominant (f : X ⟶ Y) [IsDominant f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f := by
  rw [isSchemeTheoreticallyDominant_iff]; rw [← Scheme.IdealSheafData.support_eq_top_iff]; rw [← SetLike.coe_injective.eq_iff]; rw [TopologicalSpace.Closeds.coe_top]; rw [← Set.univ_subset_iff]; rw [← f.denseRange.closure_eq]; rw [f.ker.support.isClosed.closure_subset_iff]
  exact f.range_subset_ker_support

/--
lemma `isSchemeTheoreticallyDominant_iff_isDominant` / 引理 `isSchemeTheoreticallyDominant_iff_isDominant`

English:
lemma isSchemeTheoreticallyDominant_iff_isDominant
  given: (f : X ⟶ Y) [QuasiCompact f] [IsReduced Y]
  proof: ⟨fun _ => inferInstance, fun _ => .of_isDominant _⟩

中文:
引理 isSchemeTheoreticallyDominant_iff_isDominant
  条件: (f : X ⟶ Y) [拟紧 f] [是既约 Y]
  证明: ⟨fun _ => inferInstance, fun _ => .of_isDominant _⟩

Depends on / 依赖: of_isDominant
-/
lemma isSchemeTheoreticallyDominant_iff_isDominant (f : X ⟶ Y) [QuasiCompact f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f ↔ IsDominant f :=
  ⟨fun _ => inferInstance, fun _ => .of_isDominant _⟩

/--
lemma `Scheme.Hom.app_injective` / 引理 `Scheme.Hom.app_injective`

English:
lemma Scheme.Hom.app_injective
  statement: (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
  proof: by
  wlog hU : IsAffineOpen U generalizing U; swap
  · rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, f.ker_eq_bot]
    simp
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Y.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= U⟩ :=
    Y.isBasis_affine

中文:
引理 概形.态射.app_injective
  结论: (f : X ⟶ Y) [是SchemeTheoreticallyDominant f] [拟紧 f]
  证明: by
  wlog hU : IsAffineOpen U generalizing U; swap
  · rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, f.ker_eq_bot]
    simp
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Y.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= U⟩ :=
    Y.isBasis_affine

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, IsAffineOpen, IsSheaf, RingHom, RingHom.injective_iff_ker_eq_bot, U.isOpen, Y.IsSheaf.section_ext, Y.isBasis_affineOpens.exists_subset_of_mem_open, comp_apply, exists_subset_of_mem_open, f.ker_apply, f.ker_eq_bot, f.naturality, generalizing, injective_iff_ker_eq_bot, injective_iff_map_eq_zero, isBasis_affineOpens, isOpen, ker_apply
-/
lemma Scheme.Hom.app_injective (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (U : Y.Opens) :
    Function.Injective (f.app U) := by
  wlog hU : IsAffineOpen U generalizing U; swap
  · rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, f.ker_eq_bot]
    simp
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Y.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V <= U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨V, hVU, hxV, this V hV ?_⟩
  rw [← ConcreteCategory.comp_apply]; rw [f.naturality]
  simp [hs]

/--
lemma `IsSchemeTheoreticallyDominant.isReduced` / 引理 `IsSchemeTheoreticallyDominant.isReduced`

English:
lemma IsSchemeTheoreticallyDominant.isReduced
  statement: (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f]
  proof: ⟨fun _ => isReduced_of_injective _ (f.app_injective _)⟩

中文:
引理 是SchemeTheoreticallyDominant.isReduced
  结论: (f : X ⟶ Y) [是SchemeTheoreticallyDominant f]
  证明: ⟨fun _ => isReduced_of_injective _ (f.app_injective _)⟩

Depends on / 依赖: app_injective, f.app_injective, isReduced_of_injective
-/
lemma IsSchemeTheoreticallyDominant.isReduced (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f]
    [QuasiCompact f] [IsReduced X] : IsReduced Y :=
  ⟨fun _ => isReduced_of_injective _ (f.app_injective _)⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `IsSchemeTheoreticallyDominant.pullbackSnd` / 实例 `IsSchemeTheoreticallyDominant.pullbackSnd`

English:
instance IsSchemeTheoreticallyDominant.pullbackSnd
  signature: (f : X ⟶ S) (g : Y ⟶ S)
  body: by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U => ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨V, ⟨U, hU⟩⟩, hV, hVU : V <= g ⁻¹ᵁ U⟩
  simp 

中文:
实例 是SchemeTheoreticallyDominant.pullbackSnd
  签名: (f : X ⟶ S) (g : Y ⟶ S)
  定义体: by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U => ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨V, ⟨U, hU⟩⟩, hV, hVU : V <= g ⁻¹ᵁ U⟩
  simp 

Depends on / 依赖: IdealSheafData, Pi.bot_apply, S.isBasis_affineOpens.isOpenCover.comap, Scheme, Scheme.Hom.ker_apply, Scheme.IdealSheafData.ext_of_iSup_eq_top, Scheme.IdealSheafData.ideal_bot, Y.isBasis_affineOpens.isOpenCover_mem_and_le, bot_apply, ext_of_iSup_eq_top, g.base.hom, ideal_bot, isBasis_affineOpens, isOpenCover, isOpenCover_mem_and_le, isSchemeTheoreticallyDominant_iff, ker_apply, le_bot_iff, mono_pushoutSection_of_isCompact_of_flat_right, of_hasPullback
-/
instance IsSchemeTheoreticallyDominant.pullbackSnd (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant (pullback.snd f g) := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U => ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨V, ⟨U, hU⟩⟩, hV, hVU : V <= g ⁻¹ᵁ U⟩
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro x hx
  have := mono_pushoutSection_of_isCompact_of_flat_right
    (.of_hasPullback f g) (UY := pullback.snd f g ⁻¹ᵁ V) hVU le_rfl (by
      grw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, right_eq_inf,
        hVU]) hU hV (f.isCompact_preimage hU.isCompact)
  rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
  refine CommRingCat.inr_injective_of_flat (f.appLE U (f ⁻¹ᵁ U) le_rfl) (g.appLE U V hVU)
    (by simpa [Scheme.Hom.appLE] using f.app_injective U) (g.flat_appLE hU hV hVU) ?_
  apply this
  simpa [← CommRingCat.comp_apply, ← Scheme.Hom.app_eq_appLE] using hx

/--
lemma `IsSchemeTheoreticallyDominant.of_isPullback` / 引理 `IsSchemeTheoreticallyDominant.of_isPullback`

English:
lemma IsSchemeTheoreticallyDominant.of_isPullback
  statement: {f : X ⟶ S} {g : Y ⟶ S}
  proof: by
  rw [← H.isoPullback_hom_snd]
  infer_instance

中文:
引理 是SchemeTheoreticallyDominant.of_isPullback
  结论: {f : X ⟶ S} {g : Y ⟶ S}
  证明: by
  rw [← H.isoPullback_hom_snd]
  infer_instance

Depends on / 依赖: H.isoPullback_hom_snd, infer_instance, isoPullback_hom_snd
-/
lemma IsSchemeTheoreticallyDominant.of_isPullback {f : X ⟶ S} {g : Y ⟶ S}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} (H : IsPullback pX pY f g)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant pY := by
  rw [← H.isoPullback_hom_snd]
  infer_instance

/--
Instance `IsSchemeTheoreticallyDominant.pullbackFst` / 实例 `IsSchemeTheoreticallyDominant.pullbackFst`

English:
instance IsSchemeTheoreticallyDominant.pullbackFst
  signature: (f : X ⟶ S) (g : Y ⟶ S)
  body: .of_isPullback (.flip <| .of_hasPullback _ _)

中文:
实例 是SchemeTheoreticallyDominant.pullbackFst
  签名: (f : X ⟶ S) (g : Y ⟶ S)
  定义体: .of_isPullback (.flip <| .of_hasPullback _ _)

Depends on / 依赖: of_hasPullback, of_isPullback
-/
instance IsSchemeTheoreticallyDominant.pullbackFst (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g] [Flat f] :
    IsSchemeTheoreticallyDominant (pullback.fst f g) :=
  .of_isPullback (.flip <| .of_hasPullback _ _)

end AlgebraicGeometry
