/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.Field

/-!

# Smooth morphisms

In this file we define smooth morphisms. The main definitions are:

- `AlgebraicGeometry.Smooth`: A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y`
  and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth.

- `AlgebraicGeometry.SmoothOfRelativeDimension`: A morphism of schemes `f : X ⟶ Y` is smooth of
  relative dimension `n` if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth (of relative dimension `n`).

## Main results

- `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`: A morphism of schemes is smooth
  if and only if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe t w v u

namespace AlgebraicGeometry

open RingHom

variable (n m : Nat) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth. -/
@[mk_iff]
/--
Definition of `Smooth` / `Smooth` 的定义

English:
class Smooth
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - smooth_appLE((f)) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.Smooth

中文:
类 光滑
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - smooth_appLE((f)) : 对任意 {U : Y.Opens} (_ : 是仿射开集 U) {V : X.Opens} (_ : 是仿射开集 V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.光滑

Depends on / 依赖: Smooth, Smooth.smooth_appLE, smooth_appLE
-/
class Smooth (f : X ⟶ Y) : Prop where
  smooth_appLE (f) :
    forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Smooth

alias Scheme.Hom.smooth_appLE := Smooth.smooth_appLE

@[deprecated (since := "2026-02-09")] alias IsSmooth := Smooth

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @Smooth RingHom.Smooth
  body: RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [smooth_iff]; rw [affineLocally_iff_forall_isAffineOpen]

中文:
实例 :
  签名: 有RingHomProperty @光滑 环态射.光滑
  定义体: RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [smooth_iff]; rw [affineLocally_iff_forall_isAffineOpen]

Depends on / 依赖: RingHom, RingHom.Smooth.propertyIsLocal, Smooth, propertyIsLocal
-/
instance : HasRingHomProperty @Smooth RingHom.Smooth where
  isLocal_ringHomProperty := RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [smooth_iff]; rw [affineLocally_iff_forall_isAffineOpen]

/--
lemma `Smooth.iff_forall_exists_isStandardSmooth` / 引理 `Smooth.iff_forall_exists_isStandardSmooth`

English:
lemma Smooth.iff_forall_exists_isStandardSmooth
  given: (f : X ⟶ Y)
  proof: by
  have : HasRingHomProperty @Smooth.{u} (Locally IsStandardSmooth) := by
    convert! (inferInstance : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth)
    ext f
    rw [RingHom.smooth_iff_locally_isStandardSmooth]
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @Smooth)]
  · congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway.left
  · exact isStandardSmooth_respectsIso

中文:
引理 光滑.iff_对任意_存在_isStandardSmooth
  条件: (f : X ⟶ Y)
  证明: by
  have : HasRingHomProperty @Smooth.{u} (Locally IsStandardSmooth) := by
    convert! (inferInstance : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth)
    ext f
    rw [RingHom.smooth_iff_locally_isStandardSmooth]
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @Smooth)]
  · congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway.left
  · exact isStandardSmooth_respectsIso

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.iff_exists_appLE_locally, IsStandardSmooth, Locally, RingHom, RingHom.Smooth, RingHom.smooth_iff_locally_isStandardSmooth, Scheme, Scheme.affineOpens, Smooth, Subtype, Subtype.exists, affineOpens, convert, iff_exists_appLE_locally, isStandardSmooth_respectsIso, isStandardSmooth_stableUnderCompositionWithLocalizationAway, isStandardSmooth_stableUnderCompositionWithLocalizationAway.left, smooth_iff_locally_isStandardSmooth
-/
lemma Smooth.iff_forall_exists_isStandardSmooth (f : X ⟶ Y) :
    Smooth f ↔
      forall (x : X), exists (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x in V)
        (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth := by
  have : HasRingHomProperty @Smooth.{u} (Locally IsStandardSmooth) := by
    convert! (inferInstance : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth)
    ext f
    rw [RingHom.smooth_iff_locally_isStandardSmooth]
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @Smooth)]
  · congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway.left
  · exact isStandardSmooth_respectsIso

/--
lemma `Smooth.exists_isStandardSmooth` / 引理 `Smooth.exists_isStandardSmooth`

English:
lemma Smooth.exists_isStandardSmooth
  given: (f : X ⟶ Y) [Smooth f] (x : X)
  proof: (iff_forall_exists_isStandardSmooth f).mp ‹_› x

中文:
引理 光滑.存在_isStandardSmooth
  条件: (f : X ⟶ Y) [光滑 f] (x : X)
  证明: (iff_forall_exists_isStandardSmooth f).mp ‹_› x

Depends on / 依赖: iff_forall_exists_isStandardSmooth
-/
lemma Smooth.exists_isStandardSmooth (f : X ⟶ Y) [Smooth f] (x : X) :
    exists (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x in V)
        (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth :=
  (iff_forall_exists_isStandardSmooth f).mp ‹_› x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsStableUnderComposition @Smooth
  body: HasRingHomProperty.stableUnderComposition Smooth.stableUnderComposition

中文:
实例 :
  签名: MorphismProperty.是StableUnderComposition @光滑
  定义体: HasRingHomProperty.stableUnderComposition Smooth.stableUnderComposition

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.stableUnderComposition, Smooth, Smooth.stableUnderComposition, stableUnderComposition
-/
instance : MorphismProperty.IsStableUnderComposition @Smooth :=
  HasRingHomProperty.stableUnderComposition Smooth.stableUnderComposition

/--
Instance `smooth_comp` / 实例 `smooth_comp`

English:
instance smooth_comp
  signature: {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g]
  body: MorphismProperty.comp_mem _ f g ‹Smooth f› ‹Smooth g›

中文:
实例 smooth_comp
  签名: {Z : 概形.{u}} (g : Y ⟶ Z) [光滑 f] [光滑 g]
  定义体: MorphismProperty.comp_mem _ f g ‹Smooth f› ‹Smooth g›

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, Smooth, comp_mem
-/
instance smooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Smooth f› ‹Smooth g›

instance (priority := low) [Smooth f] : Flat f where
  flat_appLE {_} hU {_} hV e := (f.smooth_appLE hU hV e).flat

/--
Instance `smooth_isStableUnderBaseChange` / 实例 `smooth_isStableUnderBaseChange`

English:
instance smooth_isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @Smooth
  body: HasRingHomProperty.isStableUnderBaseChange Smooth.isStableUnderBaseChange

中文:
实例 smooth_isStableUnderBaseChange
  签名: : MorphismProperty.是StableUnderBaseChange @光滑
  定义体: HasRingHomProperty.isStableUnderBaseChange Smooth.isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, Smooth, Smooth.isStableUnderBaseChange, isStableUnderBaseChange
-/
instance smooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Smooth :=
  HasRingHomProperty.isStableUnderBaseChange Smooth.isStableUnderBaseChange

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.Respects @Smooth @IsOpenImmersion
  body: HasRingHomProperty.respects_isOpenImmersion
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1

@[deprecated (since := "2026-02-09")]
alias isSmooth_isStableUnderBaseChange := smooth_isStableUnderBaseChange

中文:
实例 :
  签名: MorphismProperty.Respects @光滑 @是开浸入
  定义体: HasRingHomProperty.respects_isOpenImmersion
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1

@[deprecated (since := "2026-02-09")]
alias isSmooth_isStableUnderBaseChange := smooth_isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.respects_isOpenImmersion, RingHom, RingHom.Smooth.holdsForLocalizationAway, RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway, Smooth, holdsForLocalizationAway, respects_isOpenImmersion, stableUnderComposition, stableUnderCompositionWithLocalizationAway
-/
instance : MorphismProperty.Respects @Smooth @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1

@[deprecated (since := "2026-02-09")]
alias isSmooth_isStableUnderBaseChange := smooth_isStableUnderBaseChange

/--
A morphism of schemes `f : X ⟶ Y` is smooth of relative dimension `n` if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth of relative dimension `n`.
-/
@[mk_iff]
/--
Definition of `SmoothOfRelativeDimension` / `SmoothOfRelativeDimension` 的定义

English:
class SmoothOfRelativeDimension
  parameters: : Prop where
  axioms and operations (1):
    - exists_isStandardSmoothOfRelativeDimension : forall (x : X), exists (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x in V) (e : V <= f ⁻¹ᵁ U), IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

中文:
类 SmoothOfRelativeDimension
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_isStandardSmoothOfRelativeDimension : 对任意 (x : X), 存在 (U : Y.Opens) (_ : 是仿射开集 U) (V : X.Opens) (_ : 是仿射开集 V) (_ : x in V) (e : V <= f ⁻¹ᵁ U), 是StandardSmoothOfRelativeDimension n (f.appLE U V e).hom
-/
class SmoothOfRelativeDimension : Prop where
  exists_isStandardSmoothOfRelativeDimension : forall (x : X), exists (U : Y.Opens) (_ : IsAffineOpen U)
    (V : X.Opens) (_ : IsAffineOpen V) (_ : x in V) (e : V <= f ⁻¹ᵁ U),
    IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

@[deprecated (since := "2026-02-09")] alias IsSmoothOfRelativeDimension := SmoothOfRelativeDimension

/--
lemma `SmoothOfRelativeDimension.smooth` / 引理 `SmoothOfRelativeDimension.smooth`

English:
lemma SmoothOfRelativeDimension.smooth
  given: [SmoothOfRelativeDimension n f]
  statement: Smooth f
  proof: by
  rw [Smooth.iff_forall_exists_isStandardSmooth]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨U, hU, V, hV, hx, e, hf.isStandardSmooth⟩

@[deprecated (since := "2026-02-09")]
alias IsSmoothOfRelativeDimension.isSmooth := SmoothOfRelativeDimension.smooth

中文:
引理 SmoothOfRelativeDimension.smooth
  条件: [SmoothOfRelativeDimension n f]
  结论: 光滑 f
  证明: by
  rw [Smooth.iff_forall_exists_isStandardSmooth]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨U, hU, V, hV, hx, e, hf.isStandardSmooth⟩

@[deprecated (since := "2026-02-09")]
alias IsSmoothOfRelativeDimension.isSmooth := SmoothOfRelativeDimension.smooth

Depends on / 依赖: Smooth, Smooth.iff_forall_exists_isStandardSmooth, exists_isStandardSmoothOfRelativeDimension, hf.isStandardSmooth, iff_forall_exists_isStandardSmooth, isStandardSmooth
-/
lemma SmoothOfRelativeDimension.smooth [SmoothOfRelativeDimension n f] : Smooth f := by
  rw [Smooth.iff_forall_exists_isStandardSmooth]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨U, hU, V, hV, hx, e, hf.isStandardSmooth⟩

@[deprecated (since := "2026-02-09")]
alias IsSmoothOfRelativeDimension.isSmooth := SmoothOfRelativeDimension.smooth

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty (@SmoothOfRelativeDimension n)
  body: by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [smoothOfRelativeDimension_iff]
    congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]

中文:
实例 :
  签名: 有RingHomProperty (@SmoothOfRelativeDimension n)
  定义体: by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [smoothOfRelativeDimension_iff]
    congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.locally_of_iff, Scheme, Scheme.affineOpens, Subtype, Subtype.exists, affineOpens, isStandardSmoothOfRelativeDimension_localizationPreserves, isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway, locally_of_iff, smoothOfRelativeDimension_iff
-/
instance : HasRingHomProperty (@SmoothOfRelativeDimension n)
    (Locally (IsStandardSmoothOfRelativeDimension n)) := by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [smoothOfRelativeDimension_iff]
    congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]

/--
lemma `smoothOfRelativeDimension_isStableUnderBaseChange` / 引理 `smoothOfRelativeDimension_isStableUnderBaseChange`

English:
lemma smoothOfRelativeDimension_isStableUnderBaseChange
  proof: HasRingHomProperty.isStableUnderBaseChange locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

@[deprecated (since := "2026-02-09")]
alias isSmoothOfRelativeDimension_isStableUnderBaseChange :=
  smoothOfRelativeDimension_isStableUnderBaseChange

中文:
引理 smoothOfRelativeDimension_isStableUnderBaseChange
  证明: HasRingHomProperty.isStableUnderBaseChange locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

@[deprecated (since := "2026-02-09")]
alias isSmoothOfRelativeDimension_isStableUnderBaseChange :=
  smoothOfRelativeDimension_isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, isStableUnderBaseChange, isStandardSmoothOfRelativeDimension_isStableUnderBaseChange, isStandardSmoothOfRelativeDimension_respectsIso, locally_isStableUnderBaseChange
-/
lemma smoothOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
HasRingHomProperty.isStableUnderBaseChange locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

@[deprecated (since := "2026-02-09")]
alias isSmoothOfRelativeDimension_isStableUnderBaseChange :=
  smoothOfRelativeDimension_isStableUnderBaseChange

/-- Open immersions are smooth of relative dimension `0`. -/
instance (priority := 900) [IsOpenImmersion f] : SmoothOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion
    (locally_holdsForLocalizationAway <|
      isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities

/-- Open immersions are smooth. -/
instance (priority := 900) [IsOpenImmersion f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth g] :
    Smooth (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] :
    Smooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [Smooth f] : Smooth (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Smooth f] :
    Smooth (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
Instance `smoothOfRelativeDimension_comp` / 实例 `smoothOfRelativeDimension_comp`

English:
instance smoothOfRelativeDimension_comp
  signature: {Z : Scheme.{u}} (g : Y ⟶ Z)
  body: by
    obtain ⟨U₂, hU₂, V₂, hV₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f x)
    obtain ⟨U₁', hU₁', V₁', hV₁', hx₁', e₁', hf₁'⟩ :=
      hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x ⟨V₂, hV₂⟩ ⟨U₁', hU₁'⟩ ⟨V₁', hV₁'⟩ ⟨V₁', hV₁'⟩ hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s <= (f ≫ g) ⁻¹ᵁ U₂ :=
le_trans e₁ f.preimage_mono le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra]; rw [CommRingCat.ofHom_hom]; rw [g.appLE_map_assoc]; rw [Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, hU₂, X.basicOpen s, hV₁'.basicOpen s, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₂.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁

中文:
实例 smoothOfRelativeDimension_comp
  签名: {Z : 概形.{u}} (g : Y ⟶ Z)
  定义体: by
    obtain ⟨U₂, hU₂, V₂, hV₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f x)
    obtain ⟨U₁', hU₁', V₁', hV₁', hx₁', e₁', hf₁'⟩ :=
      hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x ⟨V₂, hV₂⟩ ⟨U₁', hU₁'⟩ ⟨V₁', hV₁'⟩ ⟨V₁', hV₁'⟩ hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s <= (f ≫ g) ⁻¹ᵁ U₂ :=
le_trans e₁ f.preimage_mono le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra]; rw [CommRingCat.ofHom_hom]; rw [g.appLE_map_assoc]; rw [Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, hU₂, X.basicOpen s, hV₁'.basicOpen s, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₂.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁

Depends on / 依赖: exists_basicOpen_le_appLE_of_appLE_of_isAffine, exists_isStandardSmoothOfRelativeDimension, hf.exists_isStandardSmoothOfRelativeDimension, hg.exists_isStandardSmoothOfRelativeDimension, isStandardSmoothOfRelativeDimension_localizationPreserves, isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
-/
instance smoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [hf : SmoothOfRelativeDimension n f] [hg : SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (f ≫ g) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U₂, hU₂, V₂, hV₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f x)
    obtain ⟨U₁', hU₁', V₁', hV₁', hx₁', e₁', hf₁'⟩ :=
      hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x ⟨V₂, hV₂⟩ ⟨U₁', hU₁'⟩ ⟨V₁', hV₁'⟩ ⟨V₁', hV₁'⟩ hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s <= (f ≫ g) ⁻¹ᵁ U₂ :=
le_trans e₁ f.preimage_mono le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra]; rw [CommRingCat.ofHom_hom]; rw [g.appLE_map_assoc]; rw [Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, hU₂, X.basicOpen s, hV₁'.basicOpen s, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₂.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [SmoothOfRelativeDimension 0 f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension 0 (f ≫ g) :=
inferInstanceAs SmoothOfRelativeDimension (0 + 0) (f ≫ g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative (@SmoothOfRelativeDimension 0)
  body: inferInstance
  comp_mem _ _ _ _ := inferInstance

中文:
实例 :
  签名: MorphismProperty.是Multiplicative (@SmoothOfRelativeDimension 0)
  定义体: inferInstance
  comp_mem _ _ _ _ := inferInstance
-/
instance : MorphismProperty.IsMultiplicative (@SmoothOfRelativeDimension 0) where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- Smooth morphisms are locally of finite presentation. -/
instance (priority := 100) [hf : Smooth f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  rw [HasRingHomProperty.eq_affineLocally @Smooth] at hf
  exact affineLocally_le (fun hf => hf.finitePresentation) f hf

/--
lemma `formallySmooth_stalkMap_iff` / 引理 `formallySmooth_stalkMap_iff`

English:
lemma formallySmooth_stalkMap_iff
  statement: {f : X ⟶ Y} {x : X} (U : Y.Opens)
  proof: (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallySmooth ↔
      hV.primeIdealOf ⟨x, hx⟩ in Algebra.smoothLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

中文:
引理 formallySmooth_stalkMap_iff
  结论: {f : X ⟶ Y} {x : X} (U : Y.Opens)
  证明: (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallySmooth ↔
      hV.primeIdealOf ⟨x, hx⟩ in Algebra.smoothLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

Depends on / 依赖: f.appLE, hom.toAlgebra, toAlgebra
-/
lemma formallySmooth_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U)
      (hx : x in V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallySmooth ↔
      hV.primeIdealOf ⟨x, hx⟩ in Algebra.smoothLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_smooth_of_formallySmooth_stalk` / 引理 `exists_smooth_of_formallySmooth_stalk`

English:
lemma exists_smooth_of_formallySmooth_stalk
  proof: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsSmoothAt _ _ := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Γ(Y, U)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.smooth_algebraMap] at hr
    convert!
      RingHom.Smooth.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

中文:
引理 存在_smooth_of_formallySmooth_stalk
  证明: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsSmoothAt _ _ := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Γ(Y, U)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.smooth_algebraMap] at hr
    convert!
      RingHom.Smooth.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

Depends on / 依赖: Algebra, Algebra.IsSmoothAt, Algebra.IsSmoothAt.exists_notMem_smooth, IsSmoothAt, Set.mem_univ, X.isBasis_affineOpens.exists_subset_of_mem_open, Y.isBasis_affineOpens.exists_subset_of_mem_open, algebraize, continuous, exists_notMem_smooth, exists_subset_of_mem_open, f.appLE, f.continuous, f.finitePresentation_appLE, finitePresentation_appLE, formallySmooth_stalkMap_iff, hV.primeIdealOf, isBasis_affineOpens, isOpen_univ, mem_univ
-/
lemma exists_smooth_of_formallySmooth_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallySmooth) :
    exists (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U),
      x in V ∧ (f.appLE U V hVU).hom.Smooth := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsSmoothAt _ _ := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Γ(Y, U)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.smooth_algebraMap] at hr
    convert!
      RingHom.Smooth.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

/--
lemma `Scheme.Hom.isOpen_smoothLocus` / 引理 `Scheme.Hom.isOpen_smoothLocus`

English:
lemma Scheme.Hom.isOpen_smoothLocus
  given: [LocallyOfFinitePresentation f]
  proof: by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy => (formallySmooth_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsSmoothAt _ _)), V.2, hxV⟩

中文:
引理 概形.态射.isOpen_smoothLocus
  条件: [局部有限呈现 f]
  证明: by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy => (formallySmooth_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsSmoothAt _ _)), V.2, hxV⟩

Depends on / 依赖: Algebra, Algebra.IsSmoothAt, IsSmoothAt, algebraize, exists_smooth_of_formallySmooth_stalk, f.appLE, formallySmooth_stalkMap_iff, isOpen_iff_forall_mem_open, isOpen_iff_forall_mem_open.mpr
-/
lemma Scheme.Hom.isOpen_smoothLocus [LocallyOfFinitePresentation f] :
    IsOpen { x | (f.stalkMap x).hom.FormallySmooth } := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy => (formallySmooth_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsSmoothAt _ _)), V.2, hxV⟩

/--
Definition of `Scheme.Hom.smoothLocus` / `Scheme.Hom.smoothLocus` 的定义

English:
definition Scheme.Hom.smoothLocus
  signature: (f : X ⟶ Y) [LocallyOfFinitePresentation f]
  body: ⟨{ x | (f.stalkMap x).hom.FormallySmooth }, f.isOpen_smoothLocus⟩

中文:
定义 概形.态射.smoothLocus
  签名: (f : X ⟶ Y) [局部有限呈现 f]
  定义体: ⟨{ x | (f.stalkMap x).hom.FormallySmooth }, f.isOpen_smoothLocus⟩

Depends on / 依赖: FormallySmooth, f.isOpen_smoothLocus, f.stalkMap, hom.FormallySmooth, isOpen_smoothLocus, stalkMap
-/
def Scheme.Hom.smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{ x | (f.stalkMap x).hom.FormallySmooth }, f.isOpen_smoothLocus⟩

/--
lemma `Scheme.Hom.mem_smoothLocus` / 引理 `Scheme.Hom.mem_smoothLocus`

English:
lemma Scheme.Hom.mem_smoothLocus
  given: {f : X ⟶ Y} [LocallyOfFinitePresentation f] {x : X}
  proof: .rfl

中文:
引理 概形.态射.mem_smoothLocus
  条件: {f : X ⟶ Y} [局部有限呈现 f] {x : X}
  证明: .rfl
-/
lemma Scheme.Hom.mem_smoothLocus {f : X ⟶ Y} [LocallyOfFinitePresentation f] {x : X} :
    x in f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth := .rfl

/--
lemma `Scheme.Hom.smoothLocus_eq_top` / 引理 `Scheme.Hom.smoothLocus_eq_top`

English:
lemma Scheme.Hom.smoothLocus_eq_top
  given: (f : X ⟶ Y) [Smooth f]
  proof: by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus]; rw [formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsSmoothAt _ _)

中文:
引理 概形.态射.smoothLocus_eq_top
  条件: (f : X ⟶ Y) [光滑 f]
  证明: by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus]; rw [formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsSmoothAt _ _)

Depends on / 依赖: Algebra, Algebra.IsSmoothAt, IsSmoothAt, Scheme, Scheme.Hom.mem_smoothLocus, Set.mem_univ, X.isBasis_affineOpens.exists_subset_of_mem_open, Y.isBasis_affineOpens.exists_subset_of_mem_open, algebraize, continuous, exists_subset_of_mem_open, f.appLE, f.continuous, f.smooth_appLE, formallySmooth_stalkMap_iff, isBasis_affineOpens, isOpen_univ, mem_smoothLocus, mem_univ, preimage
-/
lemma Scheme.Hom.smoothLocus_eq_top (f : X ⟶ Y) [Smooth f] :
    f.smoothLocus = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus]; rw [formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsSmoothAt _ _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Scheme.Hom.smoothLocus_eq_top_iff` / 引理 `Scheme.Hom.smoothLocus_eq_top_iff`

English:
lemma Scheme.Hom.smoothLocus_eq_top_iff
  given: {f : X ⟶ Y} [LocallyOfFinitePresentation f]
  proof: by
  refine ⟨fun H => ?_, fun _ => f.smoothLocus_eq_top⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

中文:
引理 概形.态射.smoothLocus_eq_top_iff
  条件: {f : X ⟶ Y} [局部有限呈现 f]
  证明: by
  refine ⟨fun H => ?_, fun _ => f.smoothLocus_eq_top⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

Depends on / 依赖: H.ge, HasRingHomProperty, HasRingHomProperty.iff_of_isAffine, IsAffine, IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_exists_resLE.mpr, RingHom, RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff, Set.mem_univ, Smooth, arrowResLEAppIso, arrow_mk_iso_iff, exists_smooth_of_formallySmooth_stalk, f.smoothLocus_eq_top, iff_exists_resLE, iff_of_isAffine, mem_univ, propertyIsLocal, respectsIso, smoothLocus_eq_top
-/
lemma Scheme.Hom.smoothLocus_eq_top_iff {f : X ⟶ Y} [LocallyOfFinitePresentation f] :
    f.smoothLocus = ⊤ ↔ Smooth f := by
  refine ⟨fun H => ?_, fun _ => f.smoothLocus_eq_top⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

/--
lemma `Scheme.Hom.preimage_smoothLocus_eq` / 引理 `Scheme.Hom.preimage_smoothLocus_eq`

English:
lemma Scheme.Hom.preimage_smoothLocus_eq
  statement: {U : Scheme.{u}}
  proof: by
  ext x
  refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp]; rw [← stalkMap_comp]
  rfl

中文:
引理 概形.态射.preimage_smoothLocus_eq
  结论: {U : 概形.{u}}
  证明: by
  ext x
  refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp]; rw [← stalkMap_comp]
  rfl

Depends on / 依赖: CommRingCat, CommRingCat.hom_comp, FormallySmooth, IsFinitelyPresentable, RingHom, RingHom.FormallySmooth.respectsIso.cancel_right_isIso, cancel_right_isIso, f.stalkMap, hom_comp, respectsIso, stalkMap, stalkMap_comp, symm.trans, uliftYoneda, uliftYoneda.obj
-/
lemma Scheme.Hom.preimage_smoothLocus_eq {U : Scheme.{u}}
    (f : U ⟶ X) (g : X ⟶ Y) [IsOpenImmersion f] [LocallyOfFinitePresentation g] :
    f ⁻¹ᵁ g.smoothLocus = (f ≫ g).smoothLocus := by
  ext x
  refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp]; rw [← stalkMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` / 引理 `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`

English:
lemma Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
  proof: by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X))
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (f (genericPoint X)).asIdeal.primeCompl
      (fun x hx => by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X)))
  exact Algebra.FormallySmooth.of_perfectField

中文:
引理 概形.态射.genericPoint_mem_smoothLocus_of_perfectField
  证明: by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X))
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (f (genericPoint X)).asIdeal.primeCompl
      (fun x hx => by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X)))
  exact Algebra.FormallySmooth.of_perfectField

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Field.toIsField, IsAlgebraic, IsLocalization, IsLocalization.atUnits, IsUnit, IsUnit.mem_submonoid_iff, LocallyOfFiniteType, LocallyOfFiniteType.stalkMap, Scheme, Scheme.Hom.mem_smoothLocus, Spec.structureSheaf, algebraize, asIdeal, asIdeal.primeCompl, atUnits, e.symm.injective, e.symm.toAlgHom, e.toRingEquiv.symm.isField
-/
lemma Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : genericPoint X in f.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X))
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (f (genericPoint X)).asIdeal.primeCompl
      (fun x hx => by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X)))
  exact Algebra.FormallySmooth.of_perfectField

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Scheme.Hom.dense_smoothLocus_of_perfectField` / 引理 `Scheme.Hom.dense_smoothLocus_of_perfectField`

English:
lemma Scheme.Hom.dense_smoothLocus_of_perfectField
  proof: by
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq]; rw [Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : U.ι (genericPoint U) in f.smoothLocus := by
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure this)

中文:
引理 概形.态射.dense_smoothLocus_of_perfectField
  证明: by
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq]; rw [Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : U.ι (genericPoint U) in f.smoothLocus := by
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure this)

Depends on / 依赖: Cardinal, Cardinal.fact_isRegular_aleph0, CompactSpace, EffectiveEpi, EffectiveEpi.getStruct, IsNoetherian, IsPullback, IsPullback.of_hasPullback, IsRegularEpiCategory, IsRegularEpiCategory.regularEpiOfEpi, Scheme, Scheme.Hom.coe_preimage, Set.eq_univ_iff_forall, Set.mem_preimage, Set.mem_univ, X.Opens, X.isBasis_affineOpens.exists_subset_of_mem_open, allowSynthFailures, coe_preimage, continuous
-/
lemma Scheme.Hom.dense_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : Dense (f.smoothLocus : Set X) := by
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq]; rw [Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : U.ι (genericPoint U) in f.smoothLocus := by
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure this)

end AlgebraicGeometry
