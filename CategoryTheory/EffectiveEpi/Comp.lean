/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Composition of effective epimorphisms

This file provides `EffectiveEpi` instances for certain compositions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

/--
An effective epi family precomposed by a family of split epis is effective epimorphic.
This version takes an explicit section to the split epis, and is mainly used to define
`effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'` / `effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'` 的定义

English:
definition effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'
  signature: {α : Type*} {B : C} {X Y : α -> C}
  body: EffectiveEpiFamily.desc _ f (fun a => i a ≫ e a) fun a₁ a₂ g₁ g₂ _ => (by
    simp only [← Category.assoc]
    apply w _ _ (g₁ ≫ i a₁) (g₂ ≫ i a₂)
    simp only [Category.assoc]
    simp only [← Category.assoc, hi]
    simpa)
  fac e w a := by
    simp only [Category.assoc, EffectiveEpiFamily.fac]
 

中文:
定义 effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi'
  签名: {α : 类型} {B : C} {X Y : α -> C}
  定义体: EffectiveEpiFamily.desc _ f (fun a => i a ≫ e a) fun a₁ a₂ g₁ g₂ _ => (by
    simp only [← Category.assoc]
    apply w _ _ (g₁ ≫ i a₁) (g₂ ≫ i a₂)
    simp only [Category.assoc]
    simp only [← Category.assoc, hi]
    simpa)
  fac e w a := by
    simp only [Category.assoc, EffectiveEpiFamily.fac]
 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, EffectiveEpiFamily, EffectiveEpiFamily.desc, EffectiveEpiFamily.fac, EffectiveEpiFamily.uniq, comp_id, id_comp
-/
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' {α : Type*} {B : C} {X Y : α -> C}
    (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) (i : (a : α) -> X a ⟶ Y a)
    (hi : forall a, i a ≫ g a = 𝟙 _) [EffectiveEpiFamily _ f] :
    EffectiveEpiFamilyStruct _ (fun a => g a ≫ f a) where
  desc e w := EffectiveEpiFamily.desc _ f (fun a => i a ≫ e a) fun a₁ a₂ g₁ g₂ _ => (by
    simp only [← Category.assoc]
    apply w _ _ (g₁ ≫ i a₁) (g₂ ≫ i a₂)
    simp only [Category.assoc]
    simp only [← Category.assoc, hi]
    simpa)
  fac e w a := by
    simp only [Category.assoc, EffectiveEpiFamily.fac]
    rw [← Category.id_comp (e a)]; rw [← Category.assoc]; rw [← Category.assoc]
    apply w
    simp only [Category.comp_id, Category.id_comp, ← Category.assoc]
    aesop
  uniq _ _ _ hm := by
    apply EffectiveEpiFamily.uniq _ f
    intro a
    rw [← hm a]; rw [← Category.assoc]; rw [← Category.assoc]; rw [hi]; rw [Category.id_comp]

/--
An effective epi family precomposed with a family of split epis is effective epimorphic.
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi` / `effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi` 的定义

English:
definition effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi
  signature: {α : Type*} {B : C} {X Y : α -> C}
  body: effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' f g
    (fun a => section_ (g a))
    (fun a => IsSplitEpi.id (g a))

中文:
定义 effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi
  签名: {α : 类型} {B : C} {X Y : α -> C}
  定义体: effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' f g
    (fun a => section_ (g a))
    (fun a => IsSplitEpi.id (g a))

Depends on / 依赖: IsSplitEpi, IsSplitEpi.id, effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi, section_
-/
def effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi {α : Type*} {B : C} {X Y : α -> C}
    (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamilyStruct _ (fun a => g a ≫ f a) :=
  effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi' f g
    (fun a => section_ (g a))
    (fun a => IsSplitEpi.id (g a))

instance {α : Type*} {B : C} {X Y : α -> C}
    (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a, IsSplitEpi (g a)]
    [EffectiveEpiFamily _ f] : EffectiveEpiFamily _ (fun a => g a ≫ f a) :=
  ⟨⟨effectiveEpiFamilyStructCompOfEffectiveEpiSplitEpi f g⟩⟩

example {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g] [EffectiveEpi f] :
    EffectiveEpi (g ≫ f) := inferInstance

/--
Instance `IsSplitEpi.EffectiveEpi` / 实例 `IsSplitEpi.EffectiveEpi`

English:
instance IsSplitEpi.EffectiveEpi
  signature: {B X : C} (f : X ⟶ B) [IsSplitEpi f]
  body: by
  rw [← Category.comp_id f]
  infer_instance

中文:
实例 是分裂满态射.有效满态射
  签名: {B X : C} (f : X ⟶ B) [是分裂满态射 f]
  定义体: by
  rw [← Category.comp_id f]
  infer_instance

Depends on / 依赖: Category, Category.comp_id, comp_id, infer_instance
-/
instance IsSplitEpi.EffectiveEpi {B X : C} (f : X ⟶ B) [IsSplitEpi f] : EffectiveEpi f := by
  rw [← Category.comp_id f]
  infer_instance

/--
Definition of `effectiveEpiFamilyStructOfComp` / `effectiveEpiFamilyStructOfComp` 的定义

English:
definition effectiveEpiFamilyStructOfComp
  signature: {C : Type*} [Category* C]
  body: EffectiveEpiFamily.desc _ (fun i => g i ≫ f i)
    (fun i => g i ≫ φ i) (fun {T} i₁ i₂ g₁ g₂ eq =>
      by simpa [assoc] using h i₁ i₂ (g₁ ≫ g i₁) (g₂ ≫ g i₂) (by simpa [assoc] using eq))
  fac {W} φ h i := by
    rw [← cancel_epi (g i)]; rw [← assoc]; rw [EffectiveEpiFamily.fac _ (fun i => g i ≫ f

中文:
定义 effectiveEpiFamilyStructOfComp
  签名: {C : 类型} [范畴* C]
  定义体: EffectiveEpiFamily.desc _ (fun i => g i ≫ f i)
    (fun i => g i ≫ φ i) (fun {T} i₁ i₂ g₁ g₂ eq =>
      by simpa [assoc] using h i₁ i₂ (g₁ ≫ g i₁) (g₂ ≫ g i₂) (by simpa [assoc] using eq))
  fac {W} φ h i := by
    rw [← cancel_epi (g i)]; rw [← assoc]; rw [EffectiveEpiFamily.fac _ (fun i => g i ≫ f

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.desc
-/
noncomputable def effectiveEpiFamilyStructOfComp {C : Type*} [Category* C]
    {I : Type*} {Z Y : I -> C} {X : C} (g : forall i, Z i ⟶ Y i) (f : forall i, Y i ⟶ X)
    [EffectiveEpiFamily _ (fun i => g i ≫ f i)] [forall i, Epi (g i)] :
    EffectiveEpiFamilyStruct _ f where
  desc {W} φ h := EffectiveEpiFamily.desc _ (fun i => g i ≫ f i)
    (fun i => g i ≫ φ i) (fun {T} i₁ i₂ g₁ g₂ eq =>
      by simpa [assoc] using h i₁ i₂ (g₁ ≫ g i₁) (g₂ ≫ g i₂) (by simpa [assoc] using eq))
  fac {W} φ h i := by
    rw [← cancel_epi (g i)]; rw [← assoc]; rw [EffectiveEpiFamily.fac _ (fun i => g i ≫ f i)]
  uniq {W} φ _ m hm := EffectiveEpiFamily.uniq _ (fun i => g i ≫ f i) _ _ _
    (fun i => by rw [assoc, hm])

/--
lemma `effectiveEpiFamily_of_effectiveEpi_epi_comp` / 引理 `effectiveEpiFamily_of_effectiveEpi_epi_comp`

English:
lemma effectiveEpiFamily_of_effectiveEpi_epi_comp
  statement: {α : Type*} {B : C} {X Y : α -> C}
  proof: ⟨⟨effectiveEpiFamilyStructOfComp g f⟩⟩

中文:
引理 effectiveEpiFamily_of_effectiveEpi_epi_comp
  结论: {α : 类型} {B : C} {X Y : α -> C}
  证明: ⟨⟨effectiveEpiFamilyStructOfComp g f⟩⟩

Depends on / 依赖: effectiveEpiFamilyStructOfComp
-/
lemma effectiveEpiFamily_of_effectiveEpi_epi_comp {α : Type*} {B : C} {X Y : α -> C}
    (f : (a : α) -> X a ⟶ B) (g : (a : α) -> Y a ⟶ X a) [forall a, Epi (g a)]
    [EffectiveEpiFamily _ (fun a => g a ≫ f a)] : EffectiveEpiFamily _ f :=
  ⟨⟨effectiveEpiFamilyStructOfComp g f⟩⟩

/--
lemma `effectiveEpi_of_effectiveEpi_epi_comp` / 引理 `effectiveEpi_of_effectiveEpi_epi_comp`

English:
lemma effectiveEpi_of_effectiveEpi_epi_comp
  statement: {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
  proof: have := (effectiveEpi_iff_effectiveEpiFamily (g ≫ f)).mp inferInstance
  have := effectiveEpiFamily_of_effectiveEpi_epi_comp
    (X := fun () => X) (Y := fun () => Y) (fun () => f) (fun () => g)
  inferInstance

中文:
引理 effectiveEpi_of_effectiveEpi_epi_comp
  结论: {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
  证明: have := (effectiveEpi_iff_effectiveEpiFamily (g ≫ f)).mp inferInstance
  have := effectiveEpiFamily_of_effectiveEpi_epi_comp
    (X := fun () => X) (Y := fun () => Y) (fun () => f) (fun () => g)
  inferInstance

Depends on / 依赖: effectiveEpiFamily_of_effectiveEpi_epi_comp, effectiveEpi_iff_effectiveEpiFamily
-/
lemma effectiveEpi_of_effectiveEpi_epi_comp {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X)
    [Epi g] [EffectiveEpi (g ≫ f)] : EffectiveEpi f :=
  have := (effectiveEpi_iff_effectiveEpiFamily (g ≫ f)).mp inferInstance
  have := effectiveEpiFamily_of_effectiveEpi_epi_comp
    (X := fun () => X) (Y := fun () => Y) (fun () => f) (fun () => g)
  inferInstance

section CompIso

variable {B B' : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  (i : B ⟶ B')

/--
theorem `effectiveEpiFamilyStructCompIso_aux` / 定理 `effectiveEpiFamilyStructCompIso_aux`

English:
theorem effectiveEpiFamilyStructCompIso_aux
  proof: by
  grind

中文:
定理 effectiveEpiFamilyStructCompIso_aux
  证明: by
  grind
-/
theorem effectiveEpiFamilyStructCompIso_aux
    {W : C} (e : (a : α) -> X a ⟶ W)
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ ≫ i = g₂ ≫ π a₂ ≫ i -> g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  grind

variable [EffectiveEpiFamily X π] [IsIso i]

/-- An effective epi family followed by an iso is an effective epi family. -/
noncomputable
/--
Definition of `effectiveEpiFamilyStructCompIso` / `effectiveEpiFamilyStructCompIso` 的定义

English:
definition effectiveEpiFamilyStructCompIso
  signature: : EffectiveEpiFamilyStruct X (fun a => π a ≫ i) where
  body: inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]

中文:
定义 effectiveEpiFamilyStructCompIso
  签名: : EffectiveEpiFamilyStruct X (fun a => π a ≫ i) where
  定义体: inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.desc, effectiveEpiFamilyStructCompIso_aux
-/
def effectiveEpiFamilyStructCompIso : EffectiveEpiFamilyStruct X (fun a => π a ≫ i) where
  desc e h := inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EffectiveEpiFamily X (fun a => π a ≫ i)
  body: ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

中文:
实例 :
  签名: EffectiveEpiFamily X (fun a => π a ≫ i)
  定义体: ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

Depends on / 依赖: effectiveEpiFamilyStructCompIso
-/
instance : EffectiveEpiFamily X (fun a => π a ≫ i) := ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

end CompIso

section IsoComp

variable {B : C} {α : Type*} (X Y : α -> C) (π : (a : α) -> (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : (a : α) -> Y a ⟶ X a) [forall a, IsIso (i a)]

example : EffectiveEpiFamily Y (fun a => i a ≫ π a) :=
  inferInstance

end IsoComp

end CategoryTheory
