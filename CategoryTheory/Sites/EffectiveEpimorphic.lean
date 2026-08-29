/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!

# Effective epimorphic sieves

We define the notion of effective epimorphic (pre)sieves and provide some API for relating the
notion with the notions of effective epimorphism and effective epimorphic family.

More precisely, if `f` is a morphism, then `f` is an effective epi if and only if the sieve
it generates is effective epimorphic; see `CategoryTheory.Sieve.effectiveEpimorphic_singleton`.
The analogous statement for a family of morphisms is in the theorem
`CategoryTheory.Sieve.effectiveEpimorphic_family`.

-/

universe w v u

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
Definition of `Sieve.EffectiveEpimorphic` / `Sieve.EffectiveEpimorphic` 的定义

English:
definition Sieve.EffectiveEpimorphic
  signature: {X : C} (S : Sieve X)
  body: Nonempty (IsColimit (S : Presieve X).cocone)

中文:
定义 筛.EffectiveEpimorphic
  签名: {X : C} (S : 筛 X)
  定义体: Nonempty (IsColimit (S : Presieve X).cocone)

Depends on / 依赖: IsColimit, Nonempty, Presieve, cocone
-/
def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

/--
Definition of `Presieve.EffectiveEpimorphic` / `Presieve.EffectiveEpimorphic` 的定义

English:
abbreviation Presieve.EffectiveEpimorphic
  signature: {X : C} (S : Presieve X)
  body: (Sieve.generate S).EffectiveEpimorphic

中文:
缩写 Presieve.EffectiveEpimorphic
  签名: {X : C} (S : Presieve X)
  定义体: (Sieve.generate S).EffectiveEpimorphic

Depends on / 依赖: EffectiveEpimorphic, Sieve.generate, generate
-/
abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

/--
Definition of `Sieve.generateSingleton` / `Sieve.generateSingleton` 的定义

English:
definition Sieve.generateSingleton
  signature: {X Y : C} (f : Y ⟶ X)
  body: exists (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e, rfl⟩ q
    exact ⟨q ≫ e, by simp⟩

中文:
定义 筛.generateSingleton
  签名: {X Y : C} (f : Y ⟶ X)
  定义体: exists (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e, rfl⟩ q
    exact ⟨q ≫ e, by simp⟩
-/
def Sieve.generateSingleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z g := exists (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e, rfl⟩ q
    exact ⟨q ≫ e, by simp⟩

/--
lemma `Sieve.generateSingleton_eq` / 引理 `Sieve.generateSingleton_eq`

English:
lemma Sieve.generateSingleton_eq
  given: {X Y : C} (f : Y ⟶ X)
  proof: by
  ext Z g
  constructor
  · rintro ⟨W, i, p, ⟨⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨g, h⟩
    exact ⟨Y, g, f, ⟨⟩, h⟩

中文:
引理 筛.generateSingleton_eq
  条件: {X Y : C} (f : Y ⟶ X)
  证明: by
  ext Z g
  constructor
  · rintro ⟨W, i, p, ⟨⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨g, h⟩
    exact ⟨Y, g, f, ⟨⟩, h⟩
-/
lemma Sieve.generateSingleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generateSingleton f := by
  ext Z g
  constructor
  · rintro ⟨W, i, p, ⟨⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨g, h⟩
    exact ⟨Y, g, f, ⟨⟩, h⟩

/--
lemma `Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda` / 引理 `Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda`

English:
lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda
  given: {X : C} (S : Sieve X)
  proof: S.forallYonedaIsSheaf_iff_colimit.symm

中文:
引理 筛.EffectiveEpimorphic.iff_对任意_isSheafFor_yoneda
  条件: {X : C} (S : 筛 X)
  证明: S.forallYonedaIsSheaf_iff_colimit.symm

Depends on / 依赖: S.forallYonedaIsSheaf_iff_colimit.symm, forallYonedaIsSheaf_iff_colimit
-/
lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda {X : C} (S : Sieve X) :
    S.EffectiveEpimorphic ↔ forall Y, S.arrows.IsSheafFor (yoneda.obj Y) :=
  S.forallYonedaIsSheaf_iff_colimit.symm

/--
lemma `Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda` / 引理 `Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda`

English:
lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda
  given: {X : C} (R : Presieve X)
  proof: by
  simp_rw [Presieve.isSheafFor_iff_generate R,
    Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

中文:
引理 Presieve.EffectiveEpimorphic.iff_对任意_isSheafFor_yoneda
  条件: {X : C} (R : Presieve X)
  证明: by
  simp_rw [Presieve.isSheafFor_iff_generate R,
    Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

Depends on / 依赖: EffectiveEpimorphic, Presieve, Presieve.EffectiveEpimorphic, Presieve.isSheafFor_iff_generate, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda, iff_forall_isSheafFor_yoneda, isSheafFor_iff_generate, simp_rw
-/
lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda {X : C} (R : Presieve X) :
    R.EffectiveEpimorphic ↔ forall Y, R.IsSheafFor (yoneda.obj Y) := by
  simp_rw [Presieve.isSheafFor_iff_generate R,
    Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable` / 引理 `Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable`

English:
lemma Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
  statement: {X : C} {R : Presieve X}
  proof: by
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda] at hR
  rw [← isSheafFor_comp_uliftFunctor_iff]
  refine Presieve.isSheafFor_iso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  dsimp only [uliftYoneda, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  rw [isSheafFor_comp_uliftFunctor_iff]
  exact hR _

中文:
引理 Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
  结论: {X : C} {R : Presieve X}
  证明: by
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda] at hR
  rw [← isSheafFor_comp_uliftFunctor_iff]
  refine Presieve.isSheafFor_iso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  dsimp only [uliftYoneda, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  rw [isSheafFor_comp_uliftFunctor_iff]
  exact hR _

Depends on / 依赖: EffectiveEpimorphic, Functor, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Presieve, Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda, Presieve.isSheafFor_iso, comp_obj, iff_forall_isSheafFor_yoneda, isSheafFor_comp_uliftFunctor_iff, isSheafFor_iso, uliftFunctor, uliftYoneda, uliftYonedaReprXIso, whiskeringRight_obj_obj
-/
lemma Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable {X : C} {R : Presieve X}
    (hR : R.EffectiveEpimorphic) (F : Cᵒᵖ ⥤ Type w) [F.IsRepresentable] :
    R.IsSheafFor F := by
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda] at hR
  rw [← isSheafFor_comp_uliftFunctor_iff]
  refine Presieve.isSheafFor_iso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  dsimp only [uliftYoneda, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  rw [isSheafFor_comp_uliftFunctor_iff]
  exact hR _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitOfEffectiveEpiStruct` / `isColimitOfEffectiveEpiStruct` 的定义

English:
definition isColimitOfEffectiveEpiStruct
  signature: {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f)
  body: letI D := ObjectProperty.FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₁)
      let g₂' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₂ (by simp [Y', Z', h]))
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [Y', F, S.w]
    fac := by
      rintro S ⟨T, g, hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, Hf.fac _ h₂]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := ObjectProperty.homMk (Over.homMk g)
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

中文:
定义 isColimitOfEffectiveEpiStruct
  签名: {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f)
  定义体: letI D := ObjectProperty.FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₁)
      let g₂' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₂ (by simp [Y', Z', h]))
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [Y', F, S.w]
    fac := by
      rintro S ⟨T, g, hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, Hf.fac _ h₂]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := ObjectProperty.homMk (Over.homMk g)
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

Depends on / 依赖: F.map, FullSubcategory, Hf.desc, ObjectProperty, ObjectProperty.FullSubcategory, ObjectProperty.homMk, Over.homMk, Over.mk, Sieve.generateSingleton, T.hom, arrows, arrows.diagram, diagram, generateSingleton
-/
def isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f) :
    IsColimit (Sieve.generateSingleton f : Presieve X).cocone :=
  letI D := ObjectProperty.FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₁)
      let g₂' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₂ (by simp [Y', Z', h]))
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [Y', F, S.w]
    fac := by
      rintro S ⟨T, g, hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, Hf.fac _ h₂]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := ObjectProperty.homMk (Over.homMk g)
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
noncomputable
/--
Definition of `effectiveEpiStructOfIsColimit` / `effectiveEpiStructOfIsColimit` 的定义

English:
definition effectiveEpiStructOfIsColimit
  signature: {X Y : C} (f : Y ⟶ X)
  body: let aux {W : C} (e : Y ⟶ W)
    (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨_,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨q : A ⟶ B⟩
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc]; rw [hB.choose_spec]; rw [hA.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => Hf.desc (aux e h)
    fac {W} e h := by
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply Hf.uniq (aux e h)
      rintro ⟨A, g, hA⟩
      dsimp
      simp only [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

中文:
定义 effectiveEpiStructOfIsColimit
  签名: {X Y : C} (f : Y ⟶ X)
  定义体: let aux {W : C} (e : Y ⟶ W)
    (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨_,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨q : A ⟶ B⟩
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc]; rw [hB.choose_spec]; rw [hA.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => Hf.desc (aux e h)
    fac {W} e h := by
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply Hf.uniq (aux e h)
      rintro ⟨A, g, hA⟩
      dsimp
      simp only [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Cocone, Hf.desc, Hf.fac, Over.mk, Over.w, Sieve.generateSingleton, arrows, arrows.diagram, choose_spec, comp_id, diagram, generateSingleton, hA.choose_spec, hB.choose_spec, hT.choose, naturality
-/
def effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X)
    (Hf : IsColimit (Sieve.generateSingleton f : Presieve X).cocone) :
    EffectiveEpiStruct f :=
  let aux {W : C} (e : Y ⟶ W)
    (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨_,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨q : A ⟶ B⟩
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc]; rw [hB.choose_spec]; rw [hA.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => Hf.desc (aux e h)
    fac {W} e h := by
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply Hf.uniq (aux e h)
      rintro ⟨A, g, hA⟩
      dsimp
      simp only [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

/--
theorem `Sieve.effectiveEpimorphic_singleton` / 定理 `Sieve.effectiveEpimorphic_singleton`

English:
theorem Sieve.effectiveEpimorphic_singleton
  given: {X Y : C} (f : Y ⟶ X)
  proof: by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

中文:
定理 筛.effectiveEpimorphic_singleton
  条件: {X Y : C} (f : Y ⟶ X)
  证明: by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

Depends on / 依赖: Nonempty, Nonempty.map, Sieve.generateSingleton_eq, effectiveEpiStructOfIsColimit, generateSingleton_eq, isColimitOfEffectiveEpiStruct
-/
theorem Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

/--
lemma `Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi` / 引理 `Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi`

English:
lemma Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi
  statement: {X Y : C} (f : X ⟶ Y)
  proof: Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
    ((Sieve.effectiveEpimorphic_singleton f).mpr ‹_›) _

中文:
引理 Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi
  结论: {X Y : C} (f : X ⟶ Y)
  证明: Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
    ((Sieve.effectiveEpimorphic_singleton f).mpr ‹_›) _

Depends on / 依赖: EffectiveEpimorphic, Presieve, Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable, Sieve.effectiveEpimorphic_singleton, effectiveEpimorphic_singleton, isSheafFor_of_isRepresentable
-/
lemma Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] (F : Cᵒᵖ ⥤ Type*) [F.IsRepresentable] :
    (Presieve.singleton f).IsSheafFor F :=
  Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
    ((Sieve.effectiveEpimorphic_singleton f).mpr ‹_›) _

/--
Definition of `Sieve.generateFamily` / `Sieve.generateFamily` 的定义

English:
definition Sieve.generateFamily
  signature: {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  body: exists (a : α) (g : Y ⟶ X a), g ≫ π a = f
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a, q, rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩

中文:
定义 筛.generateFamily
  签名: {B : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  定义体: exists (a : α) (g : Y ⟶ X a), g ≫ π a = f
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a, q, rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩
-/
def Sieve.generateFamily {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) :
    Sieve B where
  arrows Y f := exists (a : α) (g : Y ⟶ X a), g ≫ π a = f
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a, q, rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩

/--
lemma `Sieve.generateFamily_eq` / 引理 `Sieve.generateFamily_eq`

English:
lemma Sieve.generateFamily_eq
  given: {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  proof: by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩

中文:
引理 筛.generateFamily_eq
  条件: {B : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  证明: by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩
-/
lemma Sieve.generateFamily_eq {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) :
    Sieve.generate (Presieve.ofArrows X π) = Sieve.generateFamily X π := by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitOfEffectiveEpiFamilyStruct` / `isColimitOfEffectiveEpiFamilyStruct` 的定义

English:
definition isColimitOfEffectiveEpiFamilyStruct
  signature: {B : C} {α : Type*}
  body: letI D := ObjectProperty.FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := ObjectProperty.homMk (Over.homMk g₁)
      let i₂ : Z' ⟶ A₂ := ObjectProperty.homMk (Over.homMk g₂)
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [F, A₁, A₂, S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, H.fac _ h₂]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := ObjectProperty.homMk (Over.homMk g)
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      generalize_proofs h₁ h₂
      apply H.uniq _ h₂
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

中文:
定义 isColimitOfEffectiveEpiFamilyStruct
  签名: {B : C} {α : 类型}
  定义体: letI D := ObjectProperty.FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := ObjectProperty.homMk (Over.homMk g₁)
      let i₂ : Z' ⟶ A₂ := ObjectProperty.homMk (Over.homMk g₂)
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [F, A₁, A₂, S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, H.fac _ h₂]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := ObjectProperty.homMk (Over.homMk g)
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      generalize_proofs h₁ h₂
      apply H.uniq _ h₂
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

Depends on / 依赖: FullSubcategory, H.desc, ObjectProperty, ObjectProperty.FullSubcategory, ObjectProperty.homM, ObjectProperty.homMk, Over.homMk, Over.mk, Sieve.generateFamily, T.hom, arrows, arrows.diagram, diagram, generateFamily
-/
def isColimitOfEffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α -> C) (π : (a : α) -> (X a ⟶ B)) (H : EffectiveEpiFamilyStruct X π) :
    IsColimit (Sieve.generateFamily X π : Presieve B).cocone :=
  letI D := ObjectProperty.FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := ObjectProperty.homMk (Over.homMk g₁)
      let i₂ : Z' ⟶ A₂ := ObjectProperty.homMk (Over.homMk g₂)
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [F, A₁, A₂, S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, H.fac _ h₂]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := ObjectProperty.homMk (Over.homMk g)
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      generalize_proofs h₁ h₂
      apply H.uniq _ h₂
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructOfIsColimit` / `effectiveEpiFamilyStructOfIsColimit` 的定义

English:
definition effectiveEpiFamilyStructOfIsColimit
  signature: {B : C} {α : Type*}
  body: let aux {W : C} (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨_, hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          rintro ⟨A, a, (g₁ : A.left ⟶ _), ha⟩ ⟨B, b, (g₂ : B.left ⟶ _), hb⟩ ⟨q : A ⟶ B⟩
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec]; rw [h4.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => H.desc (aux e h)
    fac {W} e h a := by
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      simp only [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }

中文:
定义 effectiveEpiFamilyStructOfIsColimit
  签名: {B : C} {α : 类型}
  定义体: let aux {W : C} (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨_, hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          rintro ⟨A, a, (g₁ : A.left ⟶ _), ha⟩ ⟨B, b, (g₂ : B.left ⟶ _), hb⟩ ⟨q : A ⟶ B⟩
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec]; rw [h4.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => H.desc (aux e h)
    fac {W} e h a := by
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      simp only [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }

Depends on / 依赖: A.left, B.left, Category, Category.assoc, Category.comp_id, Cocone, Sieve.generateFamily, arrows, arrows.diagram, choose_spe, choose_spec, comp_id, diagram, generalize_proofs, generateFamily, h2.choose_spe, hT.choose, hT.choose_spec.choose, naturality
-/
def effectiveEpiFamilyStructOfIsColimit {B : C} {α : Type*}
    (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    (H : IsColimit (Sieve.generateFamily X π : Presieve B).cocone) :
    EffectiveEpiFamilyStruct X π :=
  let aux {W : C} (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨_, hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          rintro ⟨A, a, (g₁ : A.left ⟶ _), ha⟩ ⟨B, b, (g₂ : B.left ⟶ _), hb⟩ ⟨q : A ⟶ B⟩
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec]; rw [h4.choose_spec]; rw [Over.w] } }
  { desc := fun {_} e h => H.desc (aux e h)
    fac {W} e h a := by
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec]; rw [Category.id_comp]
    uniq {W} e h m hm := by
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      simp only [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }

/--
theorem `Sieve.effectiveEpimorphic_family` / 定理 `Sieve.effectiveEpimorphic_family`

English:
theorem Sieve.effectiveEpimorphic_family
  statement: {B : C} {α : Type*}
  proof: by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h

中文:
定理 筛.effectiveEpimorphic_family
  结论: {B : C} {α : 类型}
  证明: by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h

Depends on / 依赖: Nonempty, Nonempty.map, Sieve.generateFamily_eq, effectiveEpiFamilyStructOfIsColimit, generateFamily_eq, isColimitOfEffectiveEpiFamilyStruct
-/
theorem Sieve.effectiveEpimorphic_family {B : C} {α : Type*}
    (X : α -> C) (π : (a : α) -> (X a ⟶ B)) :
    (Presieve.ofArrows X π).EffectiveEpimorphic ↔ EffectiveEpiFamily X π := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h

end CategoryTheory
