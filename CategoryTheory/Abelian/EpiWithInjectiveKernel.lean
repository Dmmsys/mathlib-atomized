/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in an
abelian category. We show that this property of morphisms is multiplicative.

This shall be used in the file `Mathlib/Algebra/Homology/Factorizations/Basic.lean` in
order to define morphisms of cochain complexes which satisfy this property
degreewise.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace Abelian

/--
Definition of `epiWithInjectiveKernel` / `epiWithInjectiveKernel` 的定义

English:
definition epiWithInjectiveKernel
  signature: : MorphismProperty C
  body: fun _ _ f => Epi f ∧ Injective (kernel f)

中文:
定义 epiWithInjectiveKernel
  签名: : MorphismProperty C
  定义体: fun _ _ f => Epi f ∧ Injective (kernel f)

Depends on / 依赖: Injective, kernel
-/
def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

/--
lemma `epiWithInjectiveKernel_iff` / 引理 `epiWithInjectiveKernel_iff`

English:
lemma epiWithInjectiveKernel_iff
  given: {X Y : C} (g : X ⟶ Y)
  proof: by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inf

中文:
引理 epiWithInjectiveKernel_iff
  条件: {X Y : C} (g : X ⟶ Y)
  证明: by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inf

Depends on / 依赖: Injective, Injective.factorThru, Injective.of_iso, IsLimit, IsLimit.conePointUniqueUpToIso, IsSplitEpi, S.exact_of_f_is_kernel, S.zero, ShortComplex, ShortComplex.Splitting.ofExactOfRetraction, ShortComplex.mk, Splitting, conePointUniqueUpToIso, exact_of_f_is_kernel, fIsKernel, factorThru, isLimit, kernel, kernelIsKernel, limit.isLimit
-/
lemma epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ exists (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk f g w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inferInstance⟩⟩
  · rintro ⟨I, _, f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso σ.shortExact.fIsKernel (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩

/--
lemma `epiWithInjectiveKernel_of_iso` / 引理 `epiWithInjectiveKernel_of_iso`

English:
lemma epiWithInjectiveKernel_of_iso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  proof: by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩

中文:
引理 epiWithInjectiveKernel_of_iso
  条件: {X Y : C} (f : X ⟶ Y) [是同构 f]
  证明: by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩

Depends on / 依赖: ShortComplex, ShortComplex.Splitting.ofIsZeroOfIsIso, Splitting, epiWithInjectiveKernel_iff, isZero_zero, ofIsZeroOfIsIso
-/
lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩

/--
lemma `epiWithInjectiveKernel_iff_of_isZero` / 引理 `epiWithInjectiveKernel_iff_of_isZero`

English:
lemma epiWithInjectiveKernel_iff_of_isZero
  given: {X Y : C} (f : X ⟶ Y) (hY : IsZero Y)
  proof: by
  simp only [epiWithInjectiveKernel, hY.epi f, true_and]
  exact Injective.iso_iff
    { hom := kernel.ι f
      inv := kernel.lift _ (𝟙 X) (hY.eq_of_tgt _ _) }

中文:
引理 epiWithInjectiveKernel_iff_of_isZero
  条件: {X Y : C} (f : X ⟶ Y) (hY : 是零 Y)
  证明: by
  simp only [epiWithInjectiveKernel, hY.epi f, true_and]
  exact Injective.iso_iff
    { hom := kernel.ι f
      inv := kernel.lift _ (𝟙 X) (hY.eq_of_tgt _ _) }

Depends on / 依赖: Injective, Injective.iso_iff, epiWithInjectiveKernel, eq_of_tgt, hY.epi, hY.eq_of_tgt, iso_iff, kernel, kernel.lift, true_and
-/
lemma epiWithInjectiveKernel_iff_of_isZero {X Y : C} (f : X ⟶ Y) (hY : IsZero Y) :
    epiWithInjectiveKernel f ↔ Injective X := by
  simp only [epiWithInjectiveKernel, hY.epi f, true_and]
  exact Injective.iso_iff
    { hom := kernel.ι f
      inv := kernel.lift _ (𝟙 X) (hY.eq_of_tgt _ _) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative
  body: epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
  

中文:
实例 :
  签名: (epiWithInjectiveKernel : MorphismProperty C).是Multiplicative
  定义体: epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
  

Depends on / 依赖: epiWithInjectiveKernel_of_iso
-/
instance : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  id_mem _ := epiWithInjectiveKernel_of_iso _
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    refine ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, ?_, ⟨?_⟩⟩
    · ext
      · simp [reassoc_of% w₁]
      · simp [reassoc_of% σ₁.s_g, w₂]
    · exact
        { r := σ₁.r ≫ biprod.inl + g₁ ≫ σ₂.r ≫ biprod.inr
          s := σ₂.s ≫ σ₁.s
          f_r := by
            ext
            · simp [σ₁.f_r]
            · simp [reassoc_of% w₁]
            · simp
            · simp [reassoc_of% σ₁.s_g, σ₂.f_r]
          s_g := by simp [reassoc_of% σ₁.s_g, σ₂.s_g]
          id := by
            dsimp
            have h := g₁ ≫= σ₂.id =≫ σ₁.s
            simp only [add_comp, assoc, comp_add, id_comp] at h
            rw [← σ₁.id]; rw [← h]
            simp only [comp_add, add_comp, assoc, BinaryBicone.inl_fst_assoc,
              BinaryBicone.inr_fst_assoc, zero_comp, comp_zero, add_zero,
              BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
            abel }

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (epiWithInjectiveKernel (C := C)).IsStableUnderRetracts
  body: by
    rintro X' Y' X Y f' f r ⟨_, hf⟩
    have : Epi f' :=
      (MorphismProperty.epimorphisms C).of_retract r (.infer_property _)
    let r' : Retract (kernel f') (kernel f) :=
      { i := kernel.map _ _ r.i.left r.i.right (Arrow.w r.i).symm
        r := kernel.map _ _ r.r.left r.r.right (Arrow.

中文:
实例 :
  签名: (epiWithInjectiveKernel (C := C)).是StableUnderRetracts
  定义体: by
    rintro X' Y' X Y f' f r ⟨_, hf⟩
    have : Epi f' :=
      (MorphismProperty.epimorphisms C).of_retract r (.infer_property _)
    let r' : Retract (kernel f') (kernel f) :=
      { i := kernel.map _ _ r.i.left r.i.right (Arrow.w r.i).symm
        r := kernel.map _ _ r.r.left r.r.right (Arrow.

Depends on / 依赖: IsStableUnderRetracts
-/
instance : (epiWithInjectiveKernel (C := C)).IsStableUnderRetracts where
  of_retract := by
    rintro X' Y' X Y f' f r ⟨_, hf⟩
    have : Epi f' :=
      (MorphismProperty.epimorphisms C).of_retract r (.infer_property _)
    let r' : Retract (kernel f') (kernel f) :=
      { i := kernel.map _ _ r.i.left r.i.right (Arrow.w r.i).symm
        r := kernel.map _ _ r.r.left r.r.right (Arrow.w r.r).symm
        retract := by ext; simp }
    exact ⟨inferInstance, r'.injective⟩

/--
lemma `epiWithInjectiveKernel.hasLiftingProperty` / 引理 `epiWithInjectiveKernel.hasLiftingProperty`

English:
lemma epiWithInjectiveKernel.hasLiftingProperty
  proof: by
  suffices (MorphismProperty.monomorphisms C).rlp p from this _ inferInstance
  rw [epiWithInjectiveKernel_iff] at hp
  obtain ⟨I, _, s, hs, ⟨σ⟩⟩ := hp
  have hI : (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
    fun _ _ _ _ => Injective.hasLiftingProperty_of_isZero _ _ (isZero_zero C)
 

中文:
引理 epiWithInjectiveKernel.hasLiftingProperty
  证明: by
  suffices (MorphismProperty.monomorphisms C).rlp p from this _ inferInstance
  rw [epiWithInjectiveKernel_iff] at hp
  obtain ⟨I, _, s, hs, ⟨σ⟩⟩ := hp
  have hI : (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
    fun _ _ _ _ => Injective.hasLiftingProperty_of_isZero _ _ (isZero_zero C)
 

Depends on / 依赖: Injective, Injective.hasLiftingProperty_of_isZero, IsLimit, MorphismProperty, MorphismProperty.monomorphisms, MorphismProperty.of_isPullback, PullbackCone, PullbackCone.IsLimit.mk, epiWithInjectiveKernel_iff, hasLiftingProperty_of_isZero, isZero_zero, monomorphisms, of_isPullback, t.fst, t.snd
-/
lemma epiWithInjectiveKernel.hasLiftingProperty
    {X Y : C} {p : X ⟶ Y} (hp : epiWithInjectiveKernel p)
    {A B : C} (i : A ⟶ B) [Mono i] :
    HasLiftingProperty i p := by
  suffices (MorphismProperty.monomorphisms C).rlp p from this _ inferInstance
  rw [epiWithInjectiveKernel_iff] at hp
  obtain ⟨I, _, s, hs, ⟨σ⟩⟩ := hp
  have hI : (MorphismProperty.monomorphisms C).rlp (0 : I ⟶ 0) :=
    fun _ _ _ _ => Injective.hasLiftingProperty_of_isZero _ _ (isZero_zero C)
  refine MorphismProperty.of_isPullback (f' := σ.r) (f := 0) ⟨by simp, ⟨?_⟩⟩ hI
  refine PullbackCone.IsLimit.mk _ (fun t => t.fst ≫ s + t.snd ≫ σ.s)
    (fun t => by simp [dsimp% σ.f_r]) (fun t => by simp [hs, dsimp% σ.s_g]) (fun t m hm₁ hm₂ => ?_)
  simp [← hm₁, ← hm₂, ← Preadditive.comp_add, dsimp% σ.id]

end Abelian

end CategoryTheory
