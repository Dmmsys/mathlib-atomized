/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!

# Immersions of schemes

A morphism of schemes `f : X ⟶ Y` is an immersion if the underlying map of topological spaces
is a locally closed embedding, and the induced morphisms of stalks are all surjective. This is true
if and only if it can be factored into a closed immersion followed by an open immersion.

## Main results
- `isImmersion_iff_exists`:
  A morphism is a (locally-closed) immersion if and only if it can be factored into
  a closed immersion followed by a (dominant) open immersion.
- `isImmersion_iff_exists_of_quasiCompact`:
  A quasicompact morphism is a (locally-closed) immersion if and only if it can be factored into
  an open immersion followed by a closed immersion.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is an immersion if
1. the underlying map of topological spaces is an embedding
2. the range of the map is locally closed
3. the induced morphisms of stalks are all surjective. -/
@[mk_iff]
/--
Definition of `IsImmersion` / `IsImmersion` 的定义

English:
class IsImmersion
  parameters: (f : X ⟶ Y)
  extends: IsPreimmersion f
  axioms and operations (1):
    - isLocallyClosed_range : IsLocallyClosed (Set.range f)

中文:
类 IsImmersion
  参数: (f : X ⟶ Y)
  继承: IsPreimmersion f
  公理与运算 (1 个):
    - isLocallyClosed_range : IsLocallyClosed (Set.range f)
-/
class IsImmersion (f : X ⟶ Y) : Prop extends IsPreimmersion f where
  isLocallyClosed_range : IsLocallyClosed (Set.range f)

/--
lemma `Scheme.Hom.isLocallyClosed_range` / 引理 `Scheme.Hom.isLocallyClosed_range`

English:
lemma Scheme.Hom.isLocallyClosed_range
  given: (f : X ⟶ Y) [IsImmersion f]
  proof: IsImmersion.isLocallyClosed_range

中文:
引理 Scheme.Hom.isLocallyClosed_range
  条件: (f : X ⟶ Y) [IsImmersion f]
  证明: IsImmersion.isLocallyClosed_range

Depends on / 依赖: IsImmersion, IsImmersion.isLocallyClosed_range, isLocallyClosed_range
-/
lemma Scheme.Hom.isLocallyClosed_range (f : X ⟶ Y) [IsImmersion f] :
    IsLocallyClosed (Set.range f) :=
  IsImmersion.isLocallyClosed_range

/--
Definition of `Scheme.Hom.coborderRange` / `Scheme.Hom.coborderRange` 的定义

English:
definition Scheme.Hom.coborderRange
  signature: (f : X ⟶ Y) [IsImmersion f]
  body: ⟨coborder (Set.range f), f.isLocallyClosed_range.isOpen_coborder⟩

中文:
定义 Scheme.Hom.coborderRange
  签名: (f : X ⟶ Y) [IsImmersion f]
  定义体: ⟨coborder (Set.range f), f.isLocallyClosed_range.isOpen_coborder⟩

Depends on / 依赖: Set.range, coborder, f.isLocallyClosed_range.isOpen_coborder, isLocallyClosed_range, isOpen_coborder
-/
def Scheme.Hom.coborderRange (f : X ⟶ Y) [IsImmersion f] : Y.Opens :=
  ⟨coborder (Set.range f), f.isLocallyClosed_range.isOpen_coborder⟩

/--
The first part of the factorization of an immersion `f : X ⟶ Y` to a closed immersion
`f.liftCoborder : X ⟶ f.coborderRange` and a dominant open immersion `f.coborderRange.ι`.
-/
noncomputable
/--
Definition of `Scheme.Hom.liftCoborder` / `Scheme.Hom.liftCoborder` 的定义

English:
definition Scheme.Hom.liftCoborder
  signature: (f : X ⟶ Y) [IsImmersion f]
  body: IsOpenImmersion.lift f.coborderRange.ι f (by simpa using! subset_coborder)

中文:
定义 Scheme.Hom.liftCoborder
  签名: (f : X ⟶ Y) [IsImmersion f]
  定义体: IsOpenImmersion.lift f.coborderRange.ι f (by simpa using! subset_coborder)

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift, coborderRange, f.coborderRange, subset_coborder
-/
def Scheme.Hom.liftCoborder (f : X ⟶ Y) [IsImmersion f] : X ⟶ f.coborderRange :=
  IsOpenImmersion.lift f.coborderRange.ι f (by simpa using! subset_coborder)

/--
Any (locally-closed) immersion can be factored into
a closed immersion followed by a (dominant) open immersion.
-/
@[reassoc (attr := simp)]
/--
lemma `Scheme.Hom.liftCoborder_ι` / 引理 `Scheme.Hom.liftCoborder_ι`

English:
lemma Scheme.Hom.liftCoborder_ι
  given: (f : X ⟶ Y) [IsImmersion f]
  proof: IsOpenImmersion.lift_fac _ _ _

中文:
引理 Scheme.Hom.liftCoborder_ι
  条件: (f : X ⟶ Y) [IsImmersion f]
  证明: IsOpenImmersion.lift_fac _ _ _

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift_fac, lift_fac
-/
lemma Scheme.Hom.liftCoborder_ι (f : X ⟶ Y) [IsImmersion f] :
    f.liftCoborder ≫ f.coborderRange.ι = f :=
  IsOpenImmersion.lift_fac _ _ _

/--
lemma `Scheme.Hom.liftCoborder_preimage` / 引理 `Scheme.Hom.liftCoborder_preimage`

English:
lemma Scheme.Hom.liftCoborder_preimage
  given: [IsImmersion f] (U : f.coborderRange.toScheme.Opens)
  proof: by
  conv_rhs => enter [1]; rw [← f.liftCoborder_ι]
  rw [Scheme.Hom.comp_preimage]; rw [Scheme.Hom.preimage_image_eq]

中文:
引理 Scheme.Hom.liftCoborder_preimage
  条件: [IsImmersion f] (U : f.coborderRange.toScheme.Opens)
  证明: by
  conv_rhs => enter [1]; rw [← f.liftCoborder_ι]
  rw [Scheme.Hom.comp_preimage]; rw [Scheme.Hom.preimage_image_eq]

Depends on / 依赖: Scheme, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq, comp_preimage, conv_rhs, f.liftCoborder_, preimage_image_eq
-/
lemma Scheme.Hom.liftCoborder_preimage [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder ⁻¹ᵁ U = f ⁻¹ᵁ f.coborderRange.ι ''ᵁ U := by
  conv_rhs => enter [1]; rw [← f.liftCoborder_ι]
  rw [Scheme.Hom.comp_preimage]; rw [Scheme.Hom.preimage_image_eq]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `liftCoborder_app` / 引理 `liftCoborder_app`

English:
lemma liftCoborder_app
  given: [IsImmersion f] (U : f.coborderRange.toScheme.Opens)
  proof: by
  rw [Scheme.Hom.congr_app (f.liftCoborder_ι).symm (f.coborderRange.ι ''ᵁ U)]
  simp [Scheme.Hom.app_eq f.liftCoborder (f.coborderRange.ι.preimage_image_eq U),
    ← Functor.map_comp_assoc, -Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

中文:
引理 liftCoborder_app
  条件: [IsImmersion f] (U : f.coborderRange.toScheme.Opens)
  证明: by
  rw [Scheme.Hom.congr_app (f.liftCoborder_ι).symm (f.coborderRange.ι ''ᵁ U)]
  simp [Scheme.Hom.app_eq f.liftCoborder (f.coborderRange.ι.preimage_image_eq U),
    ← Functor.map_comp_assoc, -Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_comp_assoc, Scheme, Scheme.Hom.app_eq, Scheme.Hom.congr_app, Subsingleton, Subsingleton.elim, app_eq, coborderRange, congr_app, f.coborderRange, f.liftCoborder, f.liftCoborder_, liftCoborder, map_comp, map_comp_assoc, preimage_image_eq
-/
lemma liftCoborder_app [IsImmersion f] (U : f.coborderRange.toScheme.Opens) :
    f.liftCoborder.app U = f.app (f.coborderRange.ι ''ᵁ U) ≫
      X.presheaf.map (eqToHom <| f.liftCoborder_preimage U).op := by
  rw [Scheme.Hom.congr_app (f.liftCoborder_ι).symm (f.coborderRange.ι ''ᵁ U)]
  simp [Scheme.Hom.app_eq f.liftCoborder (f.coborderRange.ι.preimage_image_eq U),
    ← Functor.map_comp_assoc, -Functor.map_comp, Subsingleton.elim _ (𝟙 _)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsImmersion
  signature: f] : IsClosedImmersion f.liftCoborder
  body: by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert! isClosed_preimage_val_coborder
  apply Set.i

中文:
实例 [IsImmersion
  签名: f] : IsClosedImmersion f.liftCoborder
  定义体: by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert! isClosed_preimage_val_coborder
  apply Set.i

Depends on / 依赖: IsPreimmersion, Scheme, Scheme.Hom.comp_base, Scheme.Hom.liftCoborder_, Set.image_injective.mpr, Set.image_preimage_eq_of_subset, Set.range_comp, TopCat, TopCat.coe_comp, coborderRange, coe_comp, comp_base, convert, f.coborderRange, f.liftCoborder, f.liftCoborder_, image_injective, image_preimage_eq_of_subset, infer_instance, injective
-/
instance [IsImmersion f] : IsClosedImmersion f.liftCoborder := by
  have : IsPreimmersion (f.liftCoborder ≫ f.coborderRange.ι) := by
    simp only [Scheme.Hom.liftCoborder_ι]; infer_instance
  have : IsPreimmersion f.liftCoborder := .of_comp f.liftCoborder f.coborderRange.ι
  refine .of_isPreimmersion _ ?_
  convert! isClosed_preimage_val_coborder
  apply Set.image_injective.mpr f.coborderRange.ι.isEmbedding.injective
  rw [← Set.range_comp]; rw [← TopCat.coe_comp]; rw [← Scheme.Hom.comp_base]; rw [f.liftCoborder_ι]
  exact (Set.image_preimage_eq_of_subset (by simpa using! subset_coborder)).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsImmersion
  signature: f] : IsDominant f.coborderRange.ι
  body: by
  rw [isDominant_iff]; rw [DenseRange]; rw [Scheme.Opens.range_ι]
  exact dense_coborder

中文:
实例 [IsImmersion
  签名: f] : IsDominant f.coborderRange.ι
  定义体: by
  rw [isDominant_iff]; rw [DenseRange]; rw [Scheme.Opens.range_ι]
  exact dense_coborder

Depends on / 依赖: DenseRange, Scheme, Scheme.Opens.range_, dense_coborder, isDominant_iff
-/
instance [IsImmersion f] : IsDominant f.coborderRange.ι := by
  rw [isDominant_iff]; rw [DenseRange]; rw [Scheme.Opens.range_ι]
  exact dense_coborder

/--
lemma `isImmersion_eq_inf` / 引理 `isImmersion_eq_inf`

English:
lemma isImmersion_eq_inf
  statement: @IsImmersion = (@IsPreimmersion ⊓
  proof: by
  ext; exact isImmersion_iff _

中文:
引理 isImmersion_eq_inf
  结论: @IsImmersion = (@IsPreimmersion ⊓
  证明: by
  ext; exact isImmersion_iff _

Depends on / 依赖: isImmersion_iff
-/
lemma isImmersion_eq_inf : @IsImmersion = (@IsPreimmersion ⊓
    topologically fun {_ _} _ _ f => IsLocallyClosed (Set.range f) : MorphismProperty Scheme) := by
  ext; exact isImmersion_iff _

namespace IsImmersion

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @IsImmersion
  body: by
  suffices IsZariskiLocalAtTarget
      (topologically fun {X Y} _ _ f => IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply +allowSynthFailures topologically_isZariskiLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      cha

中文:
实例 :
  签名: IsZariskiLocalAtTarget @IsImmersion
  定义体: by
  suffices IsZariskiLocalAtTarget
      (topologically fun {X Y} _ _ f => IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply +allowSynthFailures topologically_isZariskiLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      cha

Depends on / 依赖: IsLocallyClo, IsLocallyClosed, IsZariskiLocalAtTarget, Scheme, Scheme.Hom.comp_base, Set.image_univ, Set.range, Set.range_comp, Set.range_eq_univ.mpr, TopCat, TopCat.coe_comp, allowSynthFailures, coe_comp, comp_base, i.surjective, image_univ, isImmersion_eq_inf, postcomp, precomp, range_comp
-/
instance : IsZariskiLocalAtTarget @IsImmersion := by
  suffices IsZariskiLocalAtTarget
      (topologically fun {X Y} _ _ f => IsLocallyClosed (Set.range f)) from
    isImmersion_eq_inf ▸ inferInstance
  apply +allowSynthFailures topologically_isZariskiLocalAtTarget'
  · refine { precomp := ?_, postcomp := ?_ }
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr i.surjective, Set.image_univ]
    · intro X Y Z i hi f hf
      change IsIso i at hi
      change IsLocallyClosed _
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      refine hf.image i.homeomorph.isInducing ?_
      rw [Set.range_eq_univ.mpr i.surjective]
      exact isOpen_univ.isLocallyClosed
  · simp_rw [Set.range_restrictPreimage]
    exact fun _ _ _ hU _ => hU.isLocallyClosed_iff_coe_preimage

instance (priority := 900) (f : X ⟶ Y) [IsOpenImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isOpenEmbedding.2.isLocallyClosed

instance (priority := 900) (f : X ⟶ Y) [IsClosedImmersion f] : IsImmersion f where
  isLocallyClosed_range := f.isClosedEmbedding.2.isLocallyClosed

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsImmersion
  body: inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := (inferInstance : IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact f.isLocallyClosed_range.image g.isEmbedding.isInducing g.isLocallyClosed_range

中文:
实例 :
  签名: Morphism命题erty.IsMultiplicative @IsImmersion
  定义体: inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := (inferInstance : IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact f.isLocallyClosed_range.image g.isEmbedding.isInducing g.isLocallyClosed_range
-/
instance : MorphismProperty.IsMultiplicative @IsImmersion where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine { __ := (inferInstance : IsPreimmersion (f ≫ g)), isLocallyClosed_range := ?_ }
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact f.isLocallyClosed_range.image g.isEmbedding.isInducing g.isLocallyClosed_range

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `comp` / 实例 `comp`

English:
instance comp
  signature: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
  body: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

中文:
实例 comp
  签名: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
  定义体: MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

Depends on / 依赖: IsStableUnderComposition, MorphismProperty, MorphismProperty.IsStableUnderComposition.comp_mem, comp_mem
-/
instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion f]
    [IsImmersion g] : IsImmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

variable {f} in
/--
lemma `isImmersion_iff_exists` / 引理 `isImmersion_iff_exists`

English:
lemma isImmersion_iff_exists
  statement: IsImmersion f ↔ exists (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
  proof: ⟨fun _ => ⟨_, f.liftCoborder, f.coborderRange.ι, inferInstance, inferInstance, f.liftCoborder_ι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

中文:
引理 isImmersion_iff_exists
  结论: IsImmersion f ↔ 存在 (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
  证明: ⟨fun _ => ⟨_, f.liftCoborder, f.coborderRange.ι, inferInstance, inferInstance, f.liftCoborder_ι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

Depends on / 依赖: coborderRange, f.coborderRange, f.liftCoborder, f.liftCoborder_, liftCoborder
-/
lemma isImmersion_iff_exists : IsImmersion f ↔ exists (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
    IsClosedImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ => ⟨_, f.liftCoborder, f.coborderRange.ι, inferInstance, inferInstance, f.liftCoborder_ι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isStableUnderBaseChange` / 实例 `isStableUnderBaseChange`

English:
instance isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @IsImmersion where
  body: by
    intro X Y Y' S f g f' g' H hg
    let Z := Limits.pullback f g.coborderRange.ι
    let e : Y' ⟶ Z := Limits.pullback.lift g' (f' ≫ g.liftCoborder) (by simpa using H.w.symm)
    have : IsClosedImmersion e := by
      have := (IsPullback.paste_horiz_iff (.of_hasPullback f g.coborderRange.ι)
   

中文:
实例 isStableUnderBaseChange
  签名: : Morphism命题erty.IsStableUnderBaseChange @IsImmersion where
  定义体: by
    intro X Y Y' S f g f' g' H hg
    let Z := Limits.pullback f g.coborderRange.ι
    let e : Y' ⟶ Z := Limits.pullback.lift g' (f' ≫ g.liftCoborder) (by simpa using H.w.symm)
    have : IsClosedImmersion e := by
      have := (IsPullback.paste_horiz_iff (.of_hasPullback f g.coborderRange.ι)
   

Depends on / 依赖: H.flip, H.w.symm, IsClosedImmersion, IsPullback, IsPullback.paste_horiz_iff, Limits, Limits.pullback, Limits.pullback.lift, Limits.pullback.lift_fst, Limits.pullback.lift_snd, Limits.pullback.snd, MorphismProperty, MorphismProperty.of_isPullback, coborde, coborderRange, g.coborde, g.coborderRange, g.liftCoborder, liftCoborder, lift_fst
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsImmersion where
  of_isPullback := by
    intro X Y Y' S f g f' g' H hg
    let Z := Limits.pullback f g.coborderRange.ι
    let e : Y' ⟶ Z := Limits.pullback.lift g' (f' ≫ g.liftCoborder) (by simpa using H.w.symm)
    have : IsClosedImmersion e := by
      have := (IsPullback.paste_horiz_iff (.of_hasPullback f g.coborderRange.ι)
        (show e ≫ Limits.pullback.snd _ _ = _ from Limits.pullback.lift_snd _ _ _)).mp ?_
      · exact MorphismProperty.of_isPullback this.flip inferInstance
      · simpa [e] using H.flip
    rw [← Limits.pullback.lift_fst (f := f) (g := g.coborderRange.ι) g' (f' ≫ g.liftCoborder)
      (by simpa using H.w.symm)]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion g] : IsImmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Z) (g : Y ⟶ Z) [IsImmersion f] : IsImmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›

instance (f : X ⟶ Y) (V : Y.Opens) [IsImmersion f] : IsImmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsImmersion f] :
    IsImmersion (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

instance (priority := 900) (f : X ⟶ Y) [IsImmersion f] : LocallyOfFiniteType f := by
  rw [← f.liftCoborder_ι]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
open Limits Scheme.Pullback in
/-- The diagonal morphism is always an immersion. -/
@[stacks 01KJ]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsImmersion (pullback.diagonal f)
  body: by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ => range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCo

中文:
实例 :
  签名: IsImmersion (pullback.diagonal f)
  定义体: by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ => range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCo

Depends on / 依赖: IsImmersion, MorphismProperty, MorphismProperty.cancel_l, Scheme, Scheme.Opens, Scheme.topIso_hom, Y.affineCover, affineCover, cancel_l, diagonal, diagonalCoverDiagonalRange, isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange, pullback, pullback.diagonal, range_diagonal_subset_diagonalCoverDiagonalRange, topIso_hom, top_le_iff, top_le_iff.mp
-/
instance : IsImmersion (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ => range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱
  have : IsImmersion ((pullback.diagonal f ∣_
    diagonalCoverDiagonalRange f 𝒰 𝒱) ≫ Scheme.Opens.ι _) := inferInstance
  rwa [morphismRestrict_ι, H, ← Scheme.topIso_hom,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)] at this

/-- The map `X ×[S] Y ⟶ X ×[T] Y` induced by any `S ⟶ T` is always an immersion. -/
instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) :
    IsImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i) inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsImmersion ⊤
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsImmersion _)

中文:
实例 :
  签名: Morphism命题erty.HasOfPostcomp命题erty @IsImmersion ⊤
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsImmersion _)

Depends on / 依赖: IsImmersion, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsImmersion ⊤ :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsImmersion _)

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)]
  proof: MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := ⊤) _ g trivial ‹_›

中文:
引理 of_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)]
  证明: MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := ⊤) _ g trivial ‹_›

Depends on / 依赖: HasOfPostcompProperty, MorphismProperty, MorphismProperty.HasOfPostcompProperty.of_postcomp, of_postcomp
-/
lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion (f ≫ g)] :
    IsImmersion f :=
  MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := ⊤) _ g trivial ‹_›

/--
theorem `comp_iff` / 定理 `comp_iff`

English:
theorem comp_iff
  given: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g]
  proof: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

中文:
定理 comp_iff
  条件: {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g]
  证明: ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsImmersion g] :
    IsImmersion (f ≫ g) ↔ IsImmersion f :=
  ⟨fun _ => of_comp f g, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsImmersion (prod.lift (𝟙 X) (𝟙 X))
  body: by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert! (inferInstance : IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp

中文:
实例 :
  签名: IsImmersion (prod.lift (𝟙 X) (𝟙 X))
  定义体: by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert! (inferInstance : IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp

Depends on / 依赖: IsImmersion, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, cancel_right_of_respectsIso, convert, diagonal, prodIsoPullback, pullback, pullback.diagonal, terminal, terminal.from
-/
instance : IsImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ (prodIsoPullback X X).hom]
  convert! (inferInstance : IsImmersion (pullback.diagonal (terminal.from X)))
  ext : 1 <;> simp

instance (f g : X ⟶ Y) : IsImmersion (equalizer.ι f g) :=
  MorphismProperty.of_isPullback (P := @IsImmersion)
    (isPullback_equalizer_prod f g).flip inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsImmersion
  signature: f] : IsImmersion f.toImage
  body: have : IsImmersion (f.toImage ≫ f.imageι) := by simpa
  IsImmersion.of_comp f.toImage f.imageι

中文:
实例 [IsImmersion
  签名: f] : IsImmersion f.toImage
  定义体: have : IsImmersion (f.toImage ≫ f.imageι) := by simpa
  IsImmersion.of_comp f.toImage f.imageι

Depends on / 依赖: IsImmersion, IsImmersion.of_comp, f.image, f.toImage, of_comp, toImage
-/
instance [IsImmersion f] : IsImmersion f.toImage :=
  have : IsImmersion (f.toImage ≫ f.imageι) := by simpa
  IsImmersion.of_comp f.toImage f.imageι

set_option backward.isDefEq.respectTransparency false in
open Scheme in
/--
lemma `isPullback_toImage_liftCoborder` / 引理 `isPullback_toImage_liftCoborder`

English:
lemma isPullback_toImage_liftCoborder
  given: [IsImmersion f] [QuasiCompact f]
  proof: by
  refine (isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_).flip
  rw [Hom.imageι]; rw [IdealSheafData.ker_subschemeι]
  ext U : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso, Iso.refl_inv,
    Hom.ker_apply, RingHom.comap_ker, ← CommRingCat.hom_comp]
  dsimp [O

中文:
引理 isPullback_toImage_liftCoborder
  条件: [IsImmersion f] [QuasiCompact f]
  证明: by
  refine (isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_).flip
  rw [Hom.imageι]; rw [IdealSheafData.ker_subschemeι]
  ext U : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso, Iso.refl_inv,
    Hom.ker_apply, RingHom.comap_ker, ← CommRingCat.hom_comp]
  dsimp [O

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, ConcreteCategory, ConcreteCategory.mono_iff_injective_of_preservesPullback, Hom.image, Hom.ker_apply, IdealSheafData, IdealSheafData.ideal_comap_of_isOpenImmersion, IdealSheafData.ker_subscheme, Iso.refl_inv, Opens.toScheme_presheaf_obj, RingHom, RingHom.comap_ker, RingHom.ker_comp_of_injective, RingHomCompTriple, RingHomCompTriple.comp_eq, comap_ker, comp_eq, hom_comp, ideal_comap_of_isOpenImmersion
-/
lemma isPullback_toImage_liftCoborder [IsImmersion f] [QuasiCompact f] :
    IsPullback f.toImage f.liftCoborder f.imageι f.coborderRange.ι := by
  refine (isPullback_of_isClosedImmersion _ _ _ _ (by simp) ?_).flip
  rw [Hom.imageι]; rw [IdealSheafData.ker_subschemeι]
  ext U : 2
  simp only [IdealSheafData.ideal_comap_of_isOpenImmersion, Opens.ι_appIso, Iso.refl_inv,
    Hom.ker_apply, RingHom.comap_ker, ← CommRingCat.hom_comp]
  dsimp [Opens.toScheme_presheaf_obj]
  rw [RingHomCompTriple.comp_eq]; rw [liftCoborder_app]; rw [CommRingCat.hom_comp]; rw [RingHom.ker_comp_of_injective]
  rw [← ConcreteCategory.mono_iff_injective_of_preservesPullback]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsImmersion
  signature: f] [QuasiCompact f] : IsOpenImmersion f.toImage
  body: MorphismProperty.of_isPullback (IsImmersion.isPullback_toImage_liftCoborder f).flip inferInstance

中文:
实例 [IsImmersion
  签名: f] [QuasiCompact f] : IsOpenImmersion f.toImage
  定义体: MorphismProperty.of_isPullback (IsImmersion.isPullback_toImage_liftCoborder f).flip inferInstance

Depends on / 依赖: IsImmersion, IsImmersion.isPullback_toImage_liftCoborder, MorphismProperty, MorphismProperty.of_isPullback, isPullback_toImage_liftCoborder, of_isPullback
-/
instance [IsImmersion f] [QuasiCompact f] : IsOpenImmersion f.toImage :=
  MorphismProperty.of_isPullback (IsImmersion.isPullback_toImage_liftCoborder f).flip inferInstance

variable {f} in
/--
lemma `isImmersion_iff_exists_of_quasiCompact` / 引理 `isImmersion_iff_exists_of_quasiCompact`

English:
lemma isImmersion_iff_exists_of_quasiCompact
  given: [QuasiCompact f]
  proof: ⟨fun _ => ⟨_, f.toImage, f.imageι, inferInstance, inferInstance, f.toImage_imageι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

中文:
引理 isImmersion_iff_exists_of_quasiCompact
  条件: [QuasiCompact f]
  证明: ⟨fun _ => ⟨_, f.toImage, f.imageι, inferInstance, inferInstance, f.toImage_imageι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

Depends on / 依赖: f.image, f.toImage, f.toImage_image, toImage
-/
lemma isImmersion_iff_exists_of_quasiCompact [QuasiCompact f] :
    IsImmersion f ↔ exists (Z : Scheme) (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y),
      IsOpenImmersion g₁ ∧ IsClosedImmersion g₂ ∧ g₁ ≫ g₂ = f :=
  ⟨fun _ => ⟨_, f.toImage, f.imageι, inferInstance, inferInstance, f.toImage_imageι⟩,
    fun ⟨_, _, _, _, _, e⟩ => e ▸ inferInstance⟩

end IsImmersion

end AlgebraicGeometry
