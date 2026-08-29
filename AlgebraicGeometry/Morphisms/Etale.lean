/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Étale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale.

## Main results

- `AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero`: Etale is equivalent to
  smooth of relative dimension `0`.

-/

@[expose] public section

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale. -/
@[mk_iff]
/--
Definition of `Etale` / `Etale` 的定义

English:
class Etale
  parameters: {X Y : Scheme.{u}} (f : X ⟶ Y)
  axioms and operations (1):
    - etale_appLE((f)) : forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.Etale

中文:
类 平展
  参数: {X Y : 概形.{u}} (f : X ⟶ Y)
  公理与运算 (1 个):
    - etale_appLE((f)) : 对任意 {U : Y.Opens} (_ : 是仿射开集 U) {V : X.Opens} (_ : 是仿射开集 V) (e : V <= f ⁻¹ᵁ U), (f.appLE U V e).hom.平展

Depends on / 依赖: Etale.etale_appLE, etale_appLE
-/
class Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  etale_appLE (f) :
    forall {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Etale

alias Scheme.Hom.etale_appLE := Etale.etale_appLE

@[deprecated (since := "2026-02-09")] alias IsEtale := Etale

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasRingHomProperty @Etale RingHom.Etale
  body: RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [etale_iff]; rw [affineLocally_iff_forall_isAffineOpen]

中文:
实例 :
  签名: 有RingHomProperty @平展 环态射.平展
  定义体: RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [etale_iff]; rw [affineLocally_iff_forall_isAffineOpen]

Depends on / 依赖: RingHom, RingHom.Etale.propertyIsLocal, propertyIsLocal
-/
instance : HasRingHomProperty @Etale RingHom.Etale where
  isLocal_ringHomProperty := RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [etale_iff]; rw [affineLocally_iff_forall_isAffineOpen]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @Etale
  body: HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @平展
  定义体: HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isMultiplicative, RingHom, RingHom.Etale.containsIdentities, RingHom.Etale.stableUnderComposition, containsIdentities, isMultiplicative, stableUnderComposition
-/
instance : MorphismProperty.IsMultiplicative @Etale :=
  HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `etale_comp` / 实例 `etale_comp`

English:
instance etale_comp
  signature: {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g]
  body: MorphismProperty.comp_mem _ f g ‹Etale f› ‹Etale g›

中文:
实例 etale_comp
  签名: {Z : 概形.{u}} (g : Y ⟶ Z) [平展 f] [平展 g]
  定义体: MorphismProperty.comp_mem _ f g ‹Etale f› ‹Etale g›

Depends on / 依赖: MorphismProperty, MorphismProperty.comp_mem, comp_mem
-/
instance etale_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Etale f› ‹Etale g›

/--
Instance `etale_isStableUnderBaseChange` / 实例 `etale_isStableUnderBaseChange`

English:
instance etale_isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @Etale
  body: HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

中文:
实例 etale_isStableUnderBaseChange
  签名: : MorphismProperty.是StableUnderBaseChange @平展
  定义体: HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.isStableUnderBaseChange, RingHom, RingHom.Etale.isStableUnderBaseChange, isStableUnderBaseChange
-/
instance etale_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Etale :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

/-- Open immersions are étale. -/
instance (priority := 900) [IsOpenImmersion f] : Etale f :=
  HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance (f : X ⟶ Y) (V : Y.Opens) [Etale f] : Etale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Etale f] :
    Etale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/--
lemma `eq_smoothOfRelativeDimension_zero` / 引理 `eq_smoothOfRelativeDimension_zero`

English:
lemma eq_smoothOfRelativeDimension_zero
  statement: @Etale = @SmoothOfRelativeDimension 0
  proof: by
  apply HasRingHomProperty.ext
  introv
  have : @RingHom.Etale = @RingHom.IsStandardSmoothOfRelativeDimension 0 := by
    ext; apply RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
  rw [← this]; rw [RingHom.locally_iff_of_localizationSpanTarget]
  · exact RingHom.Etale.respectsIso
  · exact RingHom.Etale.ofLocalizationSpanTarget

中文:
引理 eq_smoothOfRelativeDimension_zero
  结论: @平展 = @SmoothOfRelativeDimension 0
  证明: by
  apply HasRingHomProperty.ext
  introv
  have : @RingHom.Etale = @RingHom.IsStandardSmoothOfRelativeDimension 0 := by
    ext; apply RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
  rw [← this]; rw [RingHom.locally_iff_of_localizationSpanTarget]
  · exact RingHom.Etale.respectsIso
  · exact RingHom.Etale.ofLocalizationSpanTarget

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.ext, IsStandardSmoothOfRelativeDimension, RingHom, RingHom.Etale, RingHom.Etale.ofLocalizationSpanTarget, RingHom.Etale.respectsIso, RingHom.IsStandardSmoothOfRelativeDimension, RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero, RingHom.locally_iff_of_localizationSpanTarget, etale_iff_isStandardSmoothOfRelativeDimension_zero, introv, locally_iff_of_localizationSpanTarget, ofLocalizationSpanTarget, respectsIso
-/
lemma eq_smoothOfRelativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0 := by
  apply HasRingHomProperty.ext
  introv
  have : @RingHom.Etale = @RingHom.IsStandardSmoothOfRelativeDimension 0 := by
    ext; apply RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
  rw [← this]; rw [RingHom.locally_iff_of_localizationSpanTarget]
  · exact RingHom.Etale.respectsIso
  · exact RingHom.Etale.ofLocalizationSpanTarget

/--
lemma `iff_smoothOfRelativeDimension_zero` / 引理 `iff_smoothOfRelativeDimension_zero`

English:
lemma iff_smoothOfRelativeDimension_zero
  statement: Etale f ↔ SmoothOfRelativeDimension 0 f
  proof: by
  rw [eq_smoothOfRelativeDimension_zero]

中文:
引理 iff_smoothOfRelativeDimension_zero
  结论: 平展 f ↔ SmoothOfRelativeDimension 0 f
  证明: by
  rw [eq_smoothOfRelativeDimension_zero]

Depends on / 依赖: eq_smoothOfRelativeDimension_zero
-/
lemma iff_smoothOfRelativeDimension_zero : Etale f ↔ SmoothOfRelativeDimension 0 f := by
  rw [eq_smoothOfRelativeDimension_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Etale
  signature: f] : SmoothOfRelativeDimension 0 f
  body: by
  rwa [← iff_smoothOfRelativeDimension_zero]

中文:
实例 [平展
  签名: f] : SmoothOfRelativeDimension 0 f
  定义体: by
  rwa [← iff_smoothOfRelativeDimension_zero]

Depends on / 依赖: iff_smoothOfRelativeDimension_zero
-/
instance [Etale f] : SmoothOfRelativeDimension 0 f := by
  rwa [← iff_smoothOfRelativeDimension_zero]

instance (priority := low) [Etale f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

open RingHom in
instance (priority := 900) [Etale f] : FormallyUnramified f where
  formallyUnramified_appLE {_} hU {_} hV e :=
    (f.etale_appLE hU hV e).formallyUnramified

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty
  body: by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
exact inferInstanceAs Etale (pullback.diagonal f)

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty
  定义体: by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
exact inferInstanceAs Etale (pullback.diagonal f)

Depends on / 依赖: MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal, diagonal, hasOfPostcompProperty_iff_le_diagonal, pullback, pullback.diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty
    @Etale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
exact inferInstanceAs Etale (pullback.diagonal f)

/--
lemma `of_comp` / 引理 `of_comp`

English:
lemma of_comp
  statement: {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType g]
  proof: of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

中文:
引理 of_comp
  结论: {Z : 概形.{u}} (g : Y ⟶ Z) [平展 (f ≫ g)] [局部有限型 g]
  证明: of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

Depends on / 依赖: FormallyUnramified, LocallyOfFiniteType, of_postcomp
-/
lemma of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : Etale f :=
  of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @Etale @Etale
  body: by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty @平展 @平展
  定义体: by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

Depends on / 依赖: FormallyUnramified, HasOfPostcompProperty, LocallyOfFiniteType, MorphismProperty, MorphismProperty.HasOfPostcompProperty.of_le, Subsingleton, Subsingleton.elim, infer_instance, mk_surjective, of_le, x.mk_surjective, y.mk_surjective
-/
instance : MorphismProperty.HasOfPostcompProperty @Etale @Etale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

/--
lemma `iff_flat_and_formallyUnramified` / 引理 `iff_flat_and_formallyUnramified`

English:
lemma iff_flat_and_formallyUnramified
  given: {f : X ⟶ Y}
  proof: by
  rw [etale_iff]; rw [flat_iff]; rw [formallyUnramified_iff]; rw [locallyOfFinitePresentation_iff]
  grind [RingHom.Etale.iff_flat_and_formallyUnramified]

中文:
引理 iff_flat_and_formallyUnramified
  条件: {f : X ⟶ Y}
  证明: by
  rw [etale_iff]; rw [flat_iff]; rw [formallyUnramified_iff]; rw [locallyOfFinitePresentation_iff]
  grind [RingHom.Etale.iff_flat_and_formallyUnramified]

Depends on / 依赖: RingHom, RingHom.Etale.iff_flat_and_formallyUnramified, etale_iff, flat_iff, formallyUnramified_iff, iff_flat_and_formallyUnramified, locallyOfFinitePresentation_iff
-/
lemma iff_flat_and_formallyUnramified {f : X ⟶ Y} :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f := by
  rw [etale_iff]; rw [flat_iff]; rw [formallyUnramified_iff]; rw [locallyOfFinitePresentation_iff]
  grind [RingHom.Etale.iff_flat_and_formallyUnramified]

/--
lemma `of_formallyUnramified_of_flat` / 引理 `of_formallyUnramified_of_flat`

English:
lemma of_formallyUnramified_of_flat
  statement: [Flat f] [FormallyUnramified f]
  proof: by
  rw [Etale.iff_flat_and_formallyUnramified]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

中文:
引理 of_formallyUnramified_of_flat
  结论: [平坦 f] [形式非分歧 f]
  证明: by
  rw [Etale.iff_flat_and_formallyUnramified]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.instUnique, Etale.iff_flat_and_formallyUnramified, Quotient, Unique, iff_flat_and_formallyUnramified, instUnique
-/
lemma of_formallyUnramified_of_flat [Flat f] [FormallyUnramified f]
    [LocallyOfFinitePresentation f] :
    Etale f := by
  rw [Etale.iff_flat_and_formallyUnramified]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Etale

namespace Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Etale` / `Etale` 的定义

English:
definition Etale
  signature: (X : Scheme.{u})
  body: MorphismProperty.Over @Etale ⊤ X
deriving Category, HasPullbacks, HasFiniteLimits

中文:
定义 平展
  签名: (X : 概形.{u})
  定义体: MorphismProperty.Over @Etale ⊤ X
deriving Category, HasPullbacks, HasFiniteLimits
-/
protected def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @Etale ⊤ X
deriving Category, HasPullbacks, HasFiniteLimits

variable (X : Scheme.{u})

set_option backward.defeqAttrib.useBackward true in
instance (Y : X.Etale) : dsimp% Etale Y.hom := Y.prop

set_option backward.isDefEq.respectTransparency.types false in
instance {X : Scheme.{u}} {Z Y : X.Etale} (f : Z ⟶ Y) : Etale f.left := by
  have : Etale (f.left ≫ Y.hom) := by rw [CategoryTheory.Over.w]; infer_instance
  exact Etale.of_comp f.left Y.hom

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Etale.forget` / `Etale.forget` 的定义

English:
definition Etale.forget
  signature: : X.Etale ⥤ Over X
  body: MorphismProperty.Over.forget @Etale ⊤ X

中文:
定义 平展.forget
  签名: : X.平展 ⥤ Over X
  定义体: MorphismProperty.Over.forget @Etale ⊤ X

Depends on / 依赖: MorphismProperty, MorphismProperty.Over.forget, forget
-/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @Etale ⊤ X

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Etale.forgetFullyFaithful` / `Etale.forgetFullyFaithful` 的定义

English:
definition Etale.forgetFullyFaithful
  signature: : (Etale.forget X).FullyFaithful
  body: MorphismProperty.Comma.forgetFullyFaithful _ _ _

中文:
定义 平展.forgetFullyFaithful
  签名: : (平展.forget X).满忠实
  定义体: MorphismProperty.Comma.forgetFullyFaithful _ _ _

Depends on / 依赖: MorphismProperty, MorphismProperty.Comma.forgetFullyFaithful, forgetFullyFaithful
-/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

-- Note: using `deriving Functor.Full/Faithful` in the declaration of `Etale.forget`
-- would "succeed", but it seems it would fail to create the next two instances
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Etale.forget X).Full
  body: (Etale.forgetFullyFaithful X).full

中文:
实例 :
  签名: (平展.forget X).满
  定义体: (Etale.forgetFullyFaithful X).full

Depends on / 依赖: Etale.forgetFullyFaithful, forgetFullyFaithful
-/
instance : (Etale.forget X).Full :=
  (Etale.forgetFullyFaithful X).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Etale.forget X).Faithful
  body: (Etale.forgetFullyFaithful X).faithful

中文:
实例 :
  签名: (平展.forget X).忠实
  定义体: (Etale.forgetFullyFaithful X).faithful

Depends on / 依赖: Etale.forgetFullyFaithful, faithful, forgetFullyFaithful
-/
instance : (Etale.forget X).Faithful :=
  (Etale.forgetFullyFaithful X).faithful

variable {X} in
/--
Definition of `Etale.mk` / `Etale.mk` 的定义

English:
abbreviation Etale.mk
  signature: {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
  body: MorphismProperty.Over.mk _ f inferInstance

中文:
缩写 平展.mk
  签名: {Y : 概形.{u}} (f : Y ⟶ X) [平展 f]
  定义体: MorphismProperty.Over.mk _ f inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.Over.mk
-/
abbrev Etale.mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] : X.Etale :=
  MorphismProperty.Over.mk _ f inferInstance

variable {X} in
@[simp]
/--
lemma `Etale.forget_mk` / 引理 `Etale.forget_mk`

English:
lemma Etale.forget_mk
  given: {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
  proof: rfl

@[simp]

中文:
引理 平展.forget_mk
  条件: {Y : 概形.{u}} (f : Y ⟶ X) [平展 f]
  证明: rfl

@[simp]
-/
lemma Etale.forget_mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    (Etale.forget X).obj (.mk f) = Over.mk f := rfl

@[simp]
/--
lemma `Etale.forget_obj_left` / 引理 `Etale.forget_obj_left`

English:
lemma Etale.forget_obj_left
  given: (Y : X.Etale)
  proof: rfl

@[simp]

中文:
引理 平展.forget_obj_left
  条件: (Y : X.平展)
  证明: rfl

@[simp]
-/
lemma Etale.forget_obj_left (Y : X.Etale) :
    ((Etale.forget X).obj Y).left = Y.left := rfl

@[simp]
/--
lemma `Etale.forget_obj_hom` / 引理 `Etale.forget_obj_hom`

English:
lemma Etale.forget_obj_hom
  given: (Y : X.Etale)
  proof: rfl

中文:
引理 平展.forget_obj_hom
  条件: (Y : X.平展)
  证明: rfl
-/
lemma Etale.forget_obj_hom (Y : X.Etale) :
    ((Etale.forget X).obj Y).hom = Y.hom := rfl

instance (Y : X.Etale) : Etale (Y.left ↘ X) := Y.prop

/-- Induction principle for the objects of the small étale site of a scheme. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `Etale.rec` / `Etale.rec` 的定义

English:
definition Etale.rec
  signature: {motive : X.Etale -> Sort*}
  body: mk _ _ T.prop

中文:
定义 平展.rec
  签名: {motive : X.平展 -> 类型层*}
  定义体: mk _ _ T.prop

Depends on / 依赖: T.prop
-/
def Etale.rec {motive : X.Etale -> Sort*}
    (mk : forall (Y : Scheme.{u}) (f : Y ⟶ X) (_ : Etale f), motive (Etale.mk f))
    (T : X.Etale) :
    motive T :=
  mk _ _ T.prop

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (Etale.forget X)
  body: inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ ⊤ X))

中文:
实例 :
  签名: 保持FiniteLimits (平展.forget X)
  定义体: inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ ⊤ X))

Depends on / 依赖: DeltaZero.default, MorphismProperty, MorphismProperty.Over.forget, PreservesFiniteLimits, Subsingleton, Unique, Unique.uniq, forget, this.allEq, truncation
-/
instance : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ ⊤ X))

end Scheme

end AlgebraicGeometry
