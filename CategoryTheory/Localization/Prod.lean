/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Localization of product categories

In this file, it is shown that if functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for morphisms properties `W₁` and `W₂`, then
the product functor `C₁ × C₂ ⥤ D₁ × D₂` is a localization functor for
`W₁.prod W₂ : MorphismProperty (C₁ × C₂)`, at least if both `W₁` and `W₂`
contain identities. This main result is the instance `Functor.IsLocalization.prod`.

The proof proceeds by showing first `Localization.Construction.prodIsLocalization`,
which asserts that this holds for the localization functors `W₁.Q` and `W₂.Q` to
the constructed localized categories: this is done by showing that the product
functor `W₁.Q.prod W₂.Q : C₁ × C₂ ⥤ W₁.Localization × W₂.Localization` satisfies
the strict universal property of the localization for `W₁.prod W₂`. The general
case follows by transporting this result through equivalences of categories.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  (L₁ : C₁ ⥤ D₁) {W₁ : MorphismProperty C₁}
  (L₂ : C₂ ⥤ D₂) {W₂ : MorphismProperty C₂}

namespace Localization

namespace StrictUniversalPropertyFixedTarget

variable {E : Type u₅} [Category.{v₅} E] (F : C₁ × C₂ ⥤ E)

/--
lemma `prod_uniq` / 引理 `prod_uniq`

English:
lemma prod_uniq
  statement: (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
  proof: by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

中文:
引理 prod_uniq
  结论: (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
  证明: by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

Depends on / 依赖: Construction, Construction.uniq, F.shiftIso_add, Functor, Functor.curry_obj_injective, Functor.flip_injective, Functor.uncurry_obj_curry_obj_flip_flip, Functor.uncurry_obj_injective, curry_obj_injective, flip_injective, shiftIso_add, uncurry_obj_curry_obj_flip_flip, uncurry_obj_injective
-/
lemma prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
    (h : (W₁.Q.prod W₂.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) :
      F₁ = F₂ := by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

/--
Definition of `prodLift₁` / `prodLift₁` 的定义

English:
definition prodLift₁
  signature: [W₂.ContainsIdentities]
  body: Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
    have : forall (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
      fun X₂ => hF _ ⟨hf₁, MorphismProperty.id_mem _ _⟩
    apply NatIso.isIso_of_isIso_app)

中文:
定义 prodLift₁
  签名: [W₂.余ntainsIdentities]
  定义体: Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
    have : forall (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
      fun X₂ => hF _ ⟨hf₁, MorphismProperty.id_mem _ _⟩
    apply NatIso.isIso_of_isIso_app)

Depends on / 依赖: Construction, Construction.lift, MorphismProperty, MorphismProperty.id_mem, NatIso, NatIso.isIso_of_isIso_app, curry.obj, id_mem, isIso_of_isIso_app
-/
noncomputable def prodLift₁ [W₂.ContainsIdentities]
    (hF : (W₁.prod W₂).IsInvertedBy F) :
    W₁.Localization ⥤ C₂ ⥤ E :=
  Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
    have : forall (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
      fun X₂ => hF _ ⟨hf₁, MorphismProperty.id_mem _ _⟩
    apply NatIso.isIso_of_isIso_app)

variable (hF : (W₁.prod W₂).IsInvertedBy F)

/--
lemma `prod_fac₁` / 引理 `prod_fac₁`

English:
lemma prod_fac₁
  given: [W₂.ContainsIdentities]
  proof: Construction.fac _ _

中文:
引理 prod_fac₁
  条件: [W₂.余ntainsIdentities]
  证明: Construction.fac _ _

Depends on / 依赖: Construction, Construction.fac
-/
lemma prod_fac₁ [W₂.ContainsIdentities] :
    W₁.Q ⋙ prodLift₁ F hF = curry.obj F :=
  Construction.fac _ _

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/--
Definition of `prodLift` / `prodLift` 的定义

English:
definition prodLift
  signature: :
  body: by
  refine uncurry.obj (Construction.lift (prodLift₁ F hF).flip ?_).flip
  intro _ _ f₂ hf₂
  have : forall (X₁ : W₁.Localization),
      IsIso (((Functor.flip (prodLift₁ F hF)).map f₂).app X₁) := fun X₁ => by
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact ((MorphismProperty.isomorphisms E).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
          (hF _ ⟨MorphismProperty.id_mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app

中文:
定义 prodLift
  签名: :
  定义体: by
  refine uncurry.obj (Construction.lift (prodLift₁ F hF).flip ?_).flip
  intro _ _ f₂ hf₂
  have : forall (X₁ : W₁.Localization),
      IsIso (((Functor.flip (prodLift₁ F hF)).map f₂).app X₁) := fun X₁ => by
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact ((MorphismProperty.isomorphisms E).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
          (hF _ ⟨MorphismProperty.id_mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app

Depends on / 依赖: Arrow.mk, Construction, Construction.lift, Construction.objEquiv, Functor, Functor.congr_obj, Functor.flip, Functor.mapArrowFunctor, Localization, MorphismProperty, MorphismProperty.id_mem, MorphismProperty.isomorphisms, NatIso, NatIso.isIso_of_isIso_, arrow_mk_iso_iff, congr_obj, eqToIso, id_mem, isIso_of_isIso_, isomorphisms
-/
noncomputable def prodLift :
    W₁.Localization × W₂.Localization ⥤ E := by
  refine uncurry.obj (Construction.lift (prodLift₁ F hF).flip ?_).flip
  intro _ _ f₂ hf₂
  have : forall (X₁ : W₁.Localization),
      IsIso (((Functor.flip (prodLift₁ F hF)).map f₂).app X₁) := fun X₁ => by
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact ((MorphismProperty.isomorphisms E).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
          (hF _ ⟨MorphismProperty.id_mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app

/--
lemma `prod_fac₂` / 引理 `prod_fac₂`

English:
lemma prod_fac₂
  proof: by
  simp only [prodLift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac

中文:
引理 prod_fac₂
  证明: by
  simp only [prodLift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac

Depends on / 依赖: Construction, Construction.fac, Functor, Functor.curry_obj_uncurry_obj, Functor.flip_flip, curry_obj_uncurry_obj, flip_flip, prodLift
-/
lemma prod_fac₂ :
    W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip := by
  simp only [prodLift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac

/--
lemma `prod_fac` / 引理 `prod_fac`

English:
lemma prod_fac
  proof: by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip']; rw [prod_fac₂]; rw [Functor.flip_flip]; rw [prod_fac₁]; rw [Functor.uncurry_obj_curry_obj]

中文:
引理 prod_fac
  证明: by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip']; rw [prod_fac₂]; rw [Functor.flip_flip]; rw [prod_fac₁]; rw [Functor.uncurry_obj_curry_obj]

Depends on / 依赖: Functor, Functor.flip_flip, Functor.uncurry_obj_curry_obj, Functor.uncurry_obj_curry_obj_flip_flip, flip_flip, uncurry_obj_curry_obj, uncurry_obj_curry_obj_flip_flip
-/
lemma prod_fac :
    (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F := by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip']; rw [prod_fac₂]; rw [Functor.flip_flip]; rw [prod_fac₁]; rw [Functor.uncurry_obj_curry_obj]

variable (W₁ W₂)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: :
  body: (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := fun F hF => prodLift F hF
  fac := fun F hF => prod_fac F hF
  uniq := prod_uniq

中文:
定义 乘积
  签名: :
  定义体: (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := fun F hF => prodLift F hF
  fac := fun F hF => prod_fac F hF
  uniq := prod_uniq

Depends on / 依赖: Localization, Localization.inverts, inverts
-/
noncomputable def prod :
    StrictUniversalPropertyFixedTarget (W₁.Q.prod W₂.Q) (W₁.prod W₂) E where
  inverts := (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := fun F hF => prodLift F hF
  fac := fun F hF => prod_fac F hF
  uniq := prod_uniq

end StrictUniversalPropertyFixedTarget

variable (W₁ W₂)
variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/--
lemma `Construction.prodIsLocalization` / 引理 `Construction.prodIsLocalization`

English:
lemma Construction.prodIsLocalization
  proof: Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

中文:
引理 Construction.prodIsLocalization
  证明: Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

Depends on / 依赖: F.isoShift, Functor, Functor.IsLocalization.mk, IsLocalization, StrictUniversalPropertyFixedTarget, StrictUniversalPropertyFixedTarget.prod, isoShift, preservesZeroMorphisms_of_iso
-/
lemma Construction.prodIsLocalization :
    (W₁.Q.prod W₂.Q).IsLocalization (W₁.prod W₂) :=
  Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (W₁ W₂)
variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  body: by
  have := Construction.prodIsLocalization W₁ W₂
  exact of_equivalence_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    ((uniq W₁.Q L₁ W₁).prod (uniq W₂.Q L₂ W₂))
    (NatIso.prod (compUniqFunctor W₁.Q L₁ W₁) (compUniqFunctor W₂.Q L₂ W₂))

中文:
实例 乘积
  签名: [L₁.是Localization W₁] [L₂.是Localization W₂]
  定义体: by
  have := Construction.prodIsLocalization W₁ W₂
  exact of_equivalence_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    ((uniq W₁.Q L₁ W₁).prod (uniq W₂.Q L₂ W₂))
    (NatIso.prod (compUniqFunctor W₁.Q L₁ W₁) (compUniqFunctor W₂.Q L₂ W₂))

Depends on / 依赖: Construction, Construction.prodIsLocalization, NatIso, NatIso.prod, Q.prod, compUniqFunctor, of_equivalence_target, prodIsLocalization
-/
instance prod [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] :
    (L₁.prod L₂).IsLocalization (W₁.prod W₂) := by
  have := Construction.prodIsLocalization W₁ W₂
  exact of_equivalence_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    ((uniq W₁.Q L₁ W₁).prod (uniq W₂.Q L₂ W₂))
    (NatIso.prod (compUniqFunctor W₁.Q L₁ W₁) (compUniqFunctor W₂.Q L₂ W₂))

end IsLocalization

end Functor

end CategoryTheory
