/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Morphisms of sheaves factor as a locally surjective followed by a locally injective morphism

When morphisms in a concrete category `A` factor in a functorial manner as a surjective map
followed by an injective map, we obtain that any morphism of sheaves in `Sheaf J A`
factors in a functorial manner as a locally surjective morphism (which is epi) followed by
a locally injective morphism (which is mono).

Moreover, if we assume that the category of sheaves `Sheaf J A` is balanced
(see `Sites.LeftExact`), then epimorphisms are exactly locally surjective morphisms.

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Category ConcreteCategory CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] {FA : A -> A -> Type*} {CA : A -> Type w}
  [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]
  [J.WEqualsLocallyBijective A]

namespace Sheaf

/--
Definition of `locallyInjective` / `locallyInjective` 的定义

English:
definition locallyInjective
  signature: : MorphismProperty (Sheaf J A)
  body: fun _ _ f => IsLocallyInjective f

中文:
定义 locallyInjective
  签名: : Morphism命题erty (Sheaf J A)
  定义体: fun _ _ f => IsLocallyInjective f

Depends on / 依赖: IsLocallyInjective
-/
def locallyInjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallyInjective f

/--
Definition of `locallySurjective` / `locallySurjective` 的定义

English:
definition locallySurjective
  signature: : MorphismProperty (Sheaf J A)
  body: fun _ _ f => IsLocallySurjective f

中文:
定义 locallySurjective
  签名: : Morphism命题erty (Sheaf J A)
  定义体: fun _ _ f => IsLocallySurjective f

Depends on / 依赖: IsLocallySurjective
-/
def locallySurjective : MorphismProperty (Sheaf J A) :=
  fun _ _ f => IsLocallySurjective f

section

variable {A}
variable (data : FunctorialSurjectiveInjectiveFactorizationData A) [HasWeakSheafify J A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorialLocallySurjectiveInjectiveFactorization` / `functorialLocallySurjectiveInjectiveFactorization` 的定义

English:
definition functorialLocallySurjectiveInjectiveFactorization
  signature: :
  body: (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := wh

中文:
定义 functorialLocallySurjectiveInjectiveFactorization
  签名: :
  定义体: (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := wh

Depends on / 依赖: data.functorCategory, functorCategory, mapArrow, presheafToSheaf, sheafToPresheaf
-/
noncomputable def functorialLocallySurjectiveInjectiveFactorization :
    (locallySurjective J A).FunctorialFactorizationData (locallyInjective J A) where
  Z := (sheafToPresheaf J A).mapArrow ⋙ (data.functorCategory Cᵒᵖ).Z ⋙ presheafToSheaf J A
  i := whiskerLeft Arrow.leftFunc (inv (sheafificationAdjunction J A).counit) ≫
        whiskerLeft (sheafToPresheaf J A).mapArrow
          (whiskerRight (data.functorCategory Cᵒᵖ).i (presheafToSheaf J A))
  p := whiskerLeft (sheafToPresheaf J A).mapArrow
        (whiskerRight (data.functorCategory Cᵒᵖ).p (presheafToSheaf J A)) ≫
          whiskerLeft Arrow.rightFunc (sheafificationAdjunction J A).counit
  fac := by
    ext f : 2
    dsimp
    simp only [assoc, ← Functor.map_comp_assoc,
      MorphismProperty.FunctorialFactorizationData.fac_app,
      NatIso.isIso_inv_app, IsIso.inv_comp_eq]
    exact (sheafificationAdjunction J A).counit.naturality f.hom
  hi _ := by
    dsimp [locallySurjective]
    rw [← isLocallySurjective_sheafToPresheaf_map_iff]; rw [Functor.map_comp]; rw [Presheaf.comp_isLocallySurjective_iff]; rw [isLocallySurjective_sheafToPresheaf_map_iff]; rw [Presheaf.isLocallySurjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallySurjective_of_surjective
    apply (data.functorCategory Cᵒᵖ).hi
  hp _ := by
    dsimp [locallyInjective]
    rw [← isLocallyInjective_sheafToPresheaf_map_iff]; rw [Functor.map_comp]; rw [Presheaf.isLocallyInjective_comp_iff]; rw [isLocallyInjective_sheafToPresheaf_map_iff]; rw [Presheaf.isLocallyInjective_presheafToSheaf_map_iff]
    apply Presheaf.isLocallyInjective_of_injective
    apply (data.functorCategory Cᵒᵖ).hp

section

variable (f : Arrow (Sheaf J A))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallySurjective
  body: by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hi

中文:
实例 :
  签名: IsLocallySurjective
  定义体: by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hi

Depends on / 依赖: functorialLocallySurjectiveInjectiveFactorization
-/
instance : IsLocallySurjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallyInjective
  body: by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hp

中文:
实例 :
  签名: IsLocallyInjective
  定义体: by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hp

Depends on / 依赖: functorialLocallySurjectiveInjectiveFactorization
-/
instance : IsLocallyInjective
            ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply (functorialLocallySurjectiveInjectiveFactorization J data).hp

variable [J.HasSheafCompose (forget A)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f)
  body: by
  apply epi_of_isLocallySurjective

中文:
实例 :
  签名: Epi ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f)
  定义体: by
  apply epi_of_isLocallySurjective

Depends on / 依赖: epi_of_isLocallySurjective
-/
instance : Epi ((functorialLocallySurjectiveInjectiveFactorization J data).i.app f) := by
  apply epi_of_isLocallySurjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f)
  body: by
  apply mono_of_isLocallyInjective

中文:
实例 :
  签名: Mono ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f)
  定义体: by
  apply mono_of_isLocallyInjective

Depends on / 依赖: mono_of_isLocallyInjective
-/
instance : Mono ((functorialLocallySurjectiveInjectiveFactorization J data).p.app f) := by
  apply mono_of_isLocallyInjective

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (locallySurjective J A).HasFunctorialFactorization (locallyInjective J A)
  body: ⟨functorialLocallySurjectiveInjectiveFactorization J
      (MorphismProperty.functorialFactorizationData _ _)⟩

中文:
实例 :
  签名: (locallySurjective J A).HasFunctorialFactorization (locallyInjective J A)
  定义体: ⟨functorialLocallySurjectiveInjectiveFactorization J
      (MorphismProperty.functorialFactorizationData _ _)⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.functorialFactorizationData, functorialFactorizationData, functorialLocallySurjectiveInjectiveFactorization
-/
instance : (locallySurjective J A).HasFunctorialFactorization (locallyInjective J A) where
  nonempty_functorialFactorizationData :=
    ⟨functorialLocallySurjectiveInjectiveFactorization J
      (MorphismProperty.functorialFactorizationData _ _)⟩

end

section

variable {J}
variable [HasSheafify J A] [J.HasSheafCompose (forget A)] [Balanced (Sheaf J A)]
variable {F G : Sheaf J A} (φ : F ⟶ G)

/--
lemma `isLocallySurjective_iff_epi'` / 引理 `isLocallySurjective_iff_epi'`

English:
lemma isLocallySurjective_iff_epi'
  proof: by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mon

中文:
引理 isLocallySurjective_iff_epi'
  证明: by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mon

Depends on / 依赖: IsLocallyInjective, IsLocallySurjective, data.fac, data.hi, data.hp, data.i, data.p, epi_of_epi_fac, factorizationData, infer_instance, isIso_of_mono_of_epi, locallyInjective, locallySurjective, mono_of_isLocallyInjective
-/
lemma isLocallySurjective_iff_epi' :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    let data := (locallySurjective J A).factorizationData (locallyInjective J A) φ
    have : IsLocallySurjective data.i := data.hi
    have : IsLocallyInjective data.p := data.hp
    have : Epi data.p := epi_of_epi_fac data.fac
    have := mono_of_isLocallyInjective data.p
    have := isIso_of_mono_of_epi data.p
    rw [← data.fac]
    infer_instance

end

end Sheaf

end CategoryTheory
