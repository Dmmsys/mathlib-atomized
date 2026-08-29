/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The associated sheaf of a presheaf of modules

In this file, given a presheaf of modules `M₀` over a presheaf of rings `R₀`,
we construct the associated sheaf of `M₀`. More precisely, if `R` is a sheaf of
rings and `α : R₀ ⟶ R.val` is locally bijective, and `A` is the sheafification
of the underlying presheaf of abelian groups of `M₀`, i.e. we have a locally bijective
map `φ : M₀.presheaf ⟶ A.val`, then we endow `A` with the structure of a
sheaf of modules over `R`: this is `PresheafOfModules.sheafify α φ`.

In many applications, the morphism `α` shall be the identity, but this more
general construction allows the sheafification of both the presheaf of rings
and the presheaf of modules.

-/

@[expose] public section

universe w v v₁ u₁ u

open CategoryTheory Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

namespace CategoryTheory

namespace Presieve.FamilyOfElements

section smul

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M : PresheafOfModules.{v} R} {X : C} {P : Presieve X}
  (r : FamilyOfElements (R ⋙ forget _) P) (m : FamilyOfElements (M.presheaf ⋙ forget _) P)

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : FamilyOfElements (M.presheaf ⋙ forget _) P
  body: fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.obj (Opposite.op Y)) (r f hf) (m f hf)

中文:
定义 smul
  签名: : FamilyOfElements (M.presheaf ⋙ forget _) P
  定义体: fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.obj (Opposite.op Y)) (r f hf) (m f hf)
-/
def smul : FamilyOfElements (M.presheaf ⋙ forget _) P := fun Y f hf =>
  HSMul.hSMul (α := R.obj (Opposite.op Y)) (β := M.obj (Opposite.op Y)) (r f hf) (m f hf)

end smul

section

variable {R₀ R : Cᵒᵖ ⥤ RingCat.{u}} (α : R₀ ⟶ R) [Presheaf.IsLocallyInjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (φ : M₀.presheaf ⟶ A)
  [Presheaf.IsLocallyInjective J φ] (hA : Presheaf.IsSeparated J A)
  {X : C} (r : R.obj (Opposite.op X)) (m : A.obj (Opposite.op X)) {P : Presieve X}
  (r₀ : FamilyOfElements (R₀ ⋙ forget _) P) (m₀ : FamilyOfElements (M₀.presheaf ⋙ forget _) P)
include hA

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `_root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective` / 引理 `_root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective`

English:
lemma _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
  proof: by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D

中文:
引理 _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
  证明: by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D

Depends on / 依赖: J.intersection_covering, NatTrans, NatTrans.naturality_apply, Presheaf, Presheaf.equalizerSieve, Presheaf.equalizerSieve_mem, equalizerSieve, equalizerSieve_mem, intersection_covering, map_smul, naturality_apply, presheaf
-/
lemma _root_.PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective
    {Y : C} (r₀ r₀' : R₀.obj (Opposite.op Y))
    (m₀ m₀' : M₀.obj (Opposite.op Y))
    (hr₀ : α.app _ r₀ = α.app _ r₀')
    (hm₀ : φ.app _ m₀ = φ.app _ m₀') :
    φ.app _ (r₀ • m₀) = φ.app _ (r₀' • m₀') := by
  apply hA _ (Presheaf.equalizerSieve r₀ r₀' ⊓
      Presheaf.equalizerSieve (F := M₀.presheaf) m₀ m₀')
  · apply J.intersection_covering
    · exact Presheaf.equalizerSieve_mem J α _ _ hr₀
    · exact Presheaf.equalizerSieve_mem J φ _ _ hm₀
  · intro Z g hg
    rw [← NatTrans.naturality_apply (D := Ab)]; rw [← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul, M₀.map_smul, hg.1, hg.2]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCompatible_map_smul_aux` / 引理 `isCompatible_map_smul_aux`

English:
lemma isCompatible_map_smul_aux
  statement: {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
  proof: by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.map g.op m₀) m₀']; rw [M₀.map_smul]
  · rw [hr₀', R.map_comp, RingCat.comp_apply, ← hr₀, ← RingCat.comp_apply, NatTrans.naturality,
      RingCat.comp_apply]
  · rw [hm₀', A.map_comp, AddCommGrpCat

中文:
引理 isCompatible_map_smul_aux
  结论: {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
  证明: by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.map g.op m₀) m₀']; rw [M₀.map_smul]
  · rw [hr₀', R.map_comp, RingCat.comp_apply, ← hr₀, ← RingCat.comp_apply, NatTrans.naturality,
      RingCat.comp_apply]
  · rw [hm₀', A.map_comp, AddCommGrpCat

Depends on / 依赖: A.map_comp, AddCommGrpCat, AddCommGrpCat.coe_comp, Function, Function.comp_apply, NatTrans, NatTrans.naturality, NatTrans.naturality_apply, PresheafOfModules, PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective, R.map_comp, RingCat, RingCat.comp_apply, Sheafify, app_eq_of_isLocallyInjective, coe_comp, comp_apply, g.op, map_comp, map_smul
-/
lemma isCompatible_map_smul_aux {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    (r₀ : R₀.obj (Opposite.op Y)) (r₀' : R₀.obj (Opposite.op Z))
    (m₀ : M₀.obj (Opposite.op Y)) (m₀' : M₀.obj (Opposite.op Z))
    (hr₀ : α.app _ r₀ = R.map f.op r) (hr₀' : α.app _ r₀' = R.map (f.op ≫ g.op) r)
    (hm₀ : φ.app _ m₀ = A.map f.op m) (hm₀' : φ.app _ m₀' = A.map (f.op ≫ g.op) m) :
    φ.app _ (M₀.map g.op (r₀ • m₀)) = φ.app _ (r₀' • m₀') := by
  rw [← PresheafOfModules.Sheafify.app_eq_of_isLocallyInjective α φ hA (R₀.map g.op r₀) r₀'
    (M₀.map g.op m₀) m₀']; rw [M₀.map_smul]
  · rw [hr₀', R.map_comp, RingCat.comp_apply, ← hr₀, ← RingCat.comp_apply, NatTrans.naturality,
      RingCat.comp_apply]
  · rw [hm₀', A.map_comp, AddCommGrpCat.coe_comp, Function.comp_apply, ← hm₀]
    erw [NatTrans.naturality_apply φ]

variable (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
  (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)

include hr₀ hm₀ in
/--
lemma `isCompatible_map_smul` / 引理 `isCompatible_map_smul`

English:
lemma isCompatible_map_smul
  statement: ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible
  proof: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂

中文:
引理 isCompatible_map_smul
  结论: ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible
  证明: by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂

Depends on / 依赖: A.map, Opposi, Opposite, Opposite.op, R.map
-/
lemma isCompatible_map_smul : ((r₀.smul m₀).map (whiskerRight φ (forget _))).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac
  let a₁ := r₀ f₁ h₁
  let b₁ := m₀ f₁ h₁
  let a₂ := r₀ f₂ h₂
  let b₂ := m₀ f₂ h₂
  let a₀ := R₀.map g₁.op a₁
  let b₀ := M₀.map g₁.op b₁
  have ha₁ : (α.app (Opposite.op Y₁)) a₁ = (R.map f₁.op) r := (hr₀ f₁ h₁).symm
  have ha₂ : (α.app (Opposite.op Y₂)) a₂ = (R.map f₂.op) r := (hr₀ f₂ h₂).symm
  have hb₁ : (φ.app (Opposite.op Y₁)) b₁ = (A.map f₁.op) m := (hm₀ f₁ h₁).symm
  have hb₂ : (φ.app (Opposite.op Y₂)) b₂ = (A.map f₂.op) m := (hm₀ f₂ h₂).symm
  have ha₀ : (α.app (Opposite.op Z)) a₀ = (R.map (f₁.op ≫ g₁.op)) r := by
    rw [← RingCat.comp_apply]; rw [NatTrans.naturality]; rw [RingCat.comp_apply]; rw [ha₁]; rw [Functor.map_comp]; rw [RingCat.comp_apply]
  have hb₀ : (φ.app (Opposite.op Z)) b₀ = (A.map (f₁.op ≫ g₁.op)) m := by
    dsimp [b₀]
    erw [NatTrans.naturality_apply φ, hb₁, Functor.map_comp, ConcreteCategory.comp_apply]
  have ha₀' : (α.app (Opposite.op Z)) a₀ = (R.map (f₂.op ≫ g₂.op)) r := by
    rw [ha₀]; rw [← op_comp]; rw [fac]; rw [op_comp]
  have hb₀' : (φ.app (Opposite.op Z)) b₀ = (A.map (f₂.op ≫ g₂.op)) m := by
    rw [hb₀]; rw [← op_comp]; rw [fac]; rw [op_comp]
  dsimp
  erw [← NatTrans.naturality_apply φ, ← NatTrans.naturality_apply φ]
  exact (isCompatible_map_smul_aux α φ hA r m f₁ g₁ a₁ a₀ b₁ b₀ ha₁ ha₀ hb₁ hb₀).trans
    (isCompatible_map_smul_aux α φ hA r m f₂ g₂ a₂ a₀ b₂ b₀ ha₂ ha₀' hb₂ hb₀').symm

end

end Presieve.FamilyOfElements

end CategoryTheory

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

namespace PresheafOfModules

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

namespace Sheafify

variable {X Y : Cᵒᵖ} (π : X ⟶ Y) (r r' : R.obj.obj X) (m m' : A.obj.obj X)

/--
Definition of `SMulCandidate` / `SMulCandidate` 的定义

English:
structure SMulCandidate
  parameters: where
  axioms and operations (2):
    - x : A.obj.obj X
    - h(⦃Y) : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f x = φ.app Y (r₀ • m₀)

中文:
结构 SMulCandidate
  参数: where
  公理与运算 (2 个):
    - x : A.obj.obj X
    - h(⦃Y) : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r) (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f x = φ.app Y (r₀ • m₀)
-/
structure SMulCandidate where
  /-- The candidate for the scalar product `r • m`. -/
  x : A.obj.obj X
  h ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) : A.obj.map f x = φ.app Y (r₀ • m₀)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `SMulCandidate.mk'` / `SMulCandidate.mk'` 的定义

English:
definition SMulCandidate.mk'
  signature: (S : Sieve X.unop) (hS : S in J X.unop)
  body: a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    rw [← ConcreteCategory.comp_apply]; rw [← A.obj.map_comp]; rw [← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul] -- Mismatch between `M₀.map` and `M₀.presheaf.map`

中文:
定义 SMulCandidate.mk'
  签名: (S : Sieve X.unop) (hS : S in J X.unop)
  定义体: a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    rw [← ConcreteCategory.comp_apply]; rw [← A.obj.map_comp]; rw [← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul] -- Mismatch between `M₀.map` and `M₀.presheaf.map`

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, restrictScalarsId
-/
def SMulCandidate.mk' (S : Sieve X.unop) (hS : S in J X.unop)
    (r₀ : Presieve.FamilyOfElements (R₀ ⋙ forget _) S.arrows)
    (m₀ : Presieve.FamilyOfElements (M₀.presheaf ⋙ forget _) S.arrows)
    (hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r)
    (hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m)
    (a : A.obj.obj X)
    (ha : ((r₀.smul m₀).map (whiskerRight φ (forget _))).IsAmalgamation a) :
    SMulCandidate α φ r m where
  x := a
  h Y f a₀ ha₀ b₀ hb₀ := by
    apply A.isSeparated _ _ (J.pullback_stable f.unop hS)
    rintro Z g hg
    dsimp at hg
    rw [← ConcreteCategory.comp_apply]; rw [← A.obj.map_comp]; rw [← NatTrans.naturality_apply (D := Ab)]
    erw [M₀.map_smul] -- Mismatch between `M₀.map` and `M₀.presheaf.map`
    refine (ha _ hg).trans (app_eq_of_isLocallyInjective α φ A.isSeparated _ _ _ _ ?_ ?_)
    · rw [← RingCat.comp_apply, NatTrans.naturality, RingCat.comp_apply, ha₀]
      apply (hr₀ _ hg).symm.trans
      simp
    · erw [NatTrans.naturality_apply φ, hb₀]
      apply (hm₀ _ hg).symm.trans
      dsimp
      rw [Functor.map_comp]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (SMulCandidate α φ r m)
  body: ⟨by
  let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
  have hS : S in J _ := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  have h₁ : S <= Presheaf.imageSieve α r := fun _ _ h => h.1
  have h₂ : S <= Presheaf.imageSieve φ m := fun _ _ h => h.2
  let 

中文:
实例 :
  签名: Nonempty (SMulCandidate α φ r m)
  定义体: ⟨by
  let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
  have hS : S in J _ := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  have h₁ : S <= Presheaf.imageSieve α r := fun _ _ h => h.1
  have h₂ : S <= Presheaf.imageSieve φ m := fun _ _ h => h.2
  let 

Depends on / 依赖: FamilyOfElements, J.intersection_covering, Presheaf, Presheaf.imageSieve, Presheaf.imageSieve_mem, Presieve, Presieve.FamilyOfElements.localPreimage, all_goals, forget, hom.naturality, imageSieve, imageSieve_mem, intersection_covering, localPreimage, naturality, restrict, restrictScalarsId, whiskerRight
-/
instance : Nonempty (SMulCandidate α φ r m) := ⟨by
  let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
  have hS : S in J _ := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  have h₁ : S <= Presheaf.imageSieve α r := fun _ _ h => h.1
  have h₂ : S <= Presheaf.imageSieve φ m := fun _ _ h => h.2
  let r₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight α (forget _)) r).restrict h₁
  let m₀ := (Presieve.FamilyOfElements.localPreimage (whiskerRight φ (forget _)) m).restrict h₂
  have hr₀ : (r₀.map (whiskerRight α (forget _))).IsAmalgamation r := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  have hm₀ : (m₀.map (whiskerRight φ (forget _))).IsAmalgamation m := by
    rw [Presieve.FamilyOfElements.restrict_map]
    apply Presieve.isAmalgamation_restrict
    apply Presieve.FamilyOfElements.isAmalgamation_map_localPreimage
  exact SMulCandidate.mk' α φ r m S hS r₀ m₀ hr₀ hm₀ _ (Presieve.IsSheafFor.isAmalgamation
    (((sheafCompose J (forget _)).obj A).2.isSheafFor S hS)
    (Presieve.FamilyOfElements.isCompatible_map_smul α φ A.isSeparated r m r₀ m₀ hr₀ hm₀))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (SMulCandidate α φ r m)
  body: by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    simp only [SMulCandidate.mk.injEq]
    let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
    have hS : S in J _ := by
      apply J.intersection_covering
      all_goals apply Presheaf.imageSieve_mem
    apply A.isSeparated _ _ hS
    intro Y f ⟨⟨r₀, hr

中文:
实例 :
  签名: Subsingleton (SMulCandidate α φ r m)
  定义体: by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    simp only [SMulCandidate.mk.injEq]
    let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
    have hS : S in J _ := by
      apply J.intersection_covering
      all_goals apply Presheaf.imageSieve_mem
    apply A.isSeparated _ _ hS
    intro Y f ⟨⟨r₀, hr

Depends on / 依赖: A.isSeparated, J.intersection_covering, Presheaf, Presheaf.imageSieve, Presheaf.imageSieve_mem, SMulCandidate, SMulCandidate.mk.injEq, all_goals, f.op, imageSieve, imageSieve_mem, intersection_covering, inv.naturality, isSeparated, naturality, restrictScalarsId
-/
instance : Subsingleton (SMulCandidate α φ r m) where
  allEq := by
    rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩
    simp only [SMulCandidate.mk.injEq]
    let S := (Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m)
    have hS : S in J _ := by
      apply J.intersection_covering
      all_goals apply Presheaf.imageSieve_mem
    apply A.isSeparated _ _ hS
    intro Y f ⟨⟨r₀, hr₀⟩, ⟨m₀, hm₀⟩⟩
    rw [h₁ f.op r₀ hr₀ m₀ hm₀]; rw [h₂ f.op r₀ hr₀ m₀ hm₀]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (SMulCandidate α φ r m)
  body: uniqueOfSubsingleton (Nonempty.some inferInstance)

中文:
实例 :
  签名: Unique (SMulCandidate α φ r m)
  定义体: uniqueOfSubsingleton (Nonempty.some inferInstance)

Depends on / 依赖: Nonempty, Nonempty.some, uniqueOfSubsingleton
-/
noncomputable instance : Unique (SMulCandidate α φ r m) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

/--
Definition of `smulCandidate` / `smulCandidate` 的定义

English:
definition smulCandidate
  signature: : SMulCandidate α φ r m
  body: default

中文:
定义 smulCandidate
  签名: : SMulCandidate α φ r m
  定义体: default
-/
noncomputable def smulCandidate : SMulCandidate α φ r m := default

/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: : A.obj.obj X
  body: (smulCandidate α φ r m).x

中文:
定义 smul
  签名: : A.obj.obj X
  定义体: (smulCandidate α φ r m).x

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, restrictScalarsComp, smulCandidate
-/
noncomputable def smul : A.obj.obj X := (smulCandidate α φ r m).x

/--
lemma `map_smul_eq` / 引理 `map_smul_eq`

English:
lemma map_smul_eq
  statement: {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
  proof: (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

中文:
引理 map_smul_eq
  结论: {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
  证明: (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

Depends on / 依赖: hom.naturality, naturality, restrictScalarsComp, smulCandidate
-/
lemma map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) :
    A.obj.map f (smul α φ r m) = φ.app Y (r₀ • m₀) :=
  (smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `one_smul` / 引理 `one_smul`

English:
lemma one_smul
  statement: smul α φ 1 m = m
  proof: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀]; rw [map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀]; rw [one_smul]

中文:
引理 one_smul
  结论: smul α φ 1 m = m
  证明: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀]; rw [map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀]; rw [one_smul]

Depends on / 依赖: inv.naturality, naturality, restrictScalarsComp
-/
protected lemma one_smul : smul α φ 1 m = m := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀]; rw [map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀]; rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `zero_smul` / 引理 `zero_smul`

English:
lemma zero_smul
  statement: smul α φ 0 m = 0
  proof: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀]; rw [zero_smul]; rw [map_zero]; rw [(A.obj.map f.op).hom.map_zero]

中文:
引理 zero_smul
  结论: smul α φ 0 m = 0
  证明: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀]; rw [zero_smul]; rw [map_zero]; rw [(A.obj.map f.op).hom.map_zero]
-/
protected lemma zero_smul : smul α φ 0 m = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [map_smul_eq α φ 0 m f.op 0 (by simp) m₀ hm₀]; rw [zero_smul]; rw [map_zero]; rw [(A.obj.map f.op).hom.map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `smul_zero` / 引理 `smul_zero`

English:
lemma smul_zero
  statement: smul α φ r 0 = 0
  proof: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  rw [(A.obj.map f.op).hom.map_zero]; rw [map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp)]; rw [smul_zero]; rw [map_zero]

中文:
引理 smul_zero
  结论: smul α φ r 0 = 0
  证明: by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  rw [(A.obj.map f.op).hom.map_zero]; rw [map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp)]; rw [smul_zero]; rw [map_zero]
-/
protected lemma smul_zero : smul α φ r 0 = 0 := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J α r)
  rintro Y f ⟨r₀, hr₀⟩
  rw [(A.obj.map f.op).hom.map_zero]; rw [map_smul_eq α φ r 0 f.op r₀ hr₀ 0 (by simp)]; rw [smul_zero]; rw [map_zero]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `smul_add` / 引理 `smul_add`

English:
lemma smul_add
  statement: smul α φ r (m + m') = smul α φ r m + smul α φ r m'
  proof: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀

中文:
引理 smul_add
  结论: smul α φ r (m + m') = smul α φ r m + smul α φ r m'
  证明: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀
-/
protected lemma smul_add : smul α φ r (m + m') = smul α φ r m + smul α φ r m' := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve φ m ⊓ Presheaf.imageSieve φ m'
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀, hr₀⟩, ⟨m₀ : M₀.obj _, hm₀ : (φ.app _) _ = _⟩⟩,
    ⟨m₀' : M₀.obj _, hm₀' : (φ.app _) _ = _⟩⟩
  rw [(A.obj.map f.op).hom.map_add]; rw [map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀]; rw [map_smul_eq α φ r m' f.op r₀ hr₀ m₀' hm₀']; rw [map_smul_eq α φ r (m + m') f.op r₀ hr₀ (m₀ + m₀')
      (by rw [_root_.map_add]; rw [_root_.map_add]; rw [hm₀]; rw [hm₀']),
    smul_add, _root_.map_add]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `add_smul` / 引理 `add_smul`

English:
lemma add_smul
  statement: smul α φ (r + r') m = smul α φ r m + smul α φ r' m
  proof: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr

中文:
引理 add_smul
  结论: smul α φ (r + r') m = smul α φ r m + smul α φ r' m
  证明: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr
-/
protected lemma add_smul : smul α φ (r + r') m = smul α φ r m + smul α φ r' m := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩, ⟨m₀, hm₀⟩⟩
  rw [(A.obj.map f.op).hom.map_add]; rw [map_smul_eq α φ r m f.op r₀ hr₀ m₀ hm₀]; rw [map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀]; rw [map_smul_eq α φ (r + r') m f.op (r₀ + r₀') (by rw [_root_.map_add]; rw [_root_.map_add]; rw [hr₀]; rw [hr₀'])
      m₀ hm₀, add_smul, _root_.map_add]

/--
lemma `mul_smul` / 引理 `mul_smul`

English:
lemma mul_smul
  statement: smul α φ (r * r') m = smul α φ r (smul α φ r' m)
  proof: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr

中文:
引理 mul_smul
  结论: smul α φ (r * r') m = smul α φ r (smul α φ r' m)
  证明: by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr
-/
protected lemma mul_smul : smul α φ (r * r') m = smul α φ r (smul α φ r' m) := by
  let S := Presheaf.imageSieve α r ⊓ Presheaf.imageSieve α r' ⊓ Presheaf.imageSieve φ m
  have hS : S in J X.unop := by
    refine J.intersection_covering (J.intersection_covering ?_ ?_) ?_
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨⟨r₀ : R₀.obj _, (hr₀ : (α.app (Opposite.op Y)) r₀ = (R.obj.map f.op) r)⟩,
    ⟨r₀' : R₀.obj _, (hr₀' : (α.app (Opposite.op Y)) r₀' = (R.obj.map f.op) r')⟩⟩,
    ⟨m₀ : M₀.obj _, hm₀⟩⟩
  rw [map_smul_eq α φ (r * r') m f.op (r₀ * r₀')
    (by rw [map_mul]; rw [map_mul]; rw [hr₀]; rw [hr₀']) m₀ hm₀, mul_smul,
    map_smul_eq α φ r (smul α φ r' m) f.op r₀ hr₀ (r₀' • m₀)
      (map_smul_eq α φ r' m f.op r₀' hr₀' m₀ hm₀).symm]

variable (X)

/-- The module structure on the sections of the sheafification of the underlying
presheaf of abelian groups of a presheaf of modules. -/
@[instance_reducible]
/--
Definition of `module` / `module` 的定义

English:
definition module
  signature: : Module (R.obj.obj X) (A.obj.obj X) where
  body: smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ

中文:
定义 module
  签名: : Module (R.obj.obj X) (A.obj.obj X) where
  定义体: smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ
-/
noncomputable def module : Module (R.obj.obj X) (A.obj.obj X) where
  smul r m := smul α φ r m
  one_smul := Sheafify.one_smul α φ
  zero_smul := Sheafify.zero_smul α φ
  smul_zero := Sheafify.smul_zero α φ
  smul_add := Sheafify.smul_add α φ
  add_smul := Sheafify.add_smul α φ
  mul_smul := Sheafify.mul_smul α φ

/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  proof: by
  let S := Presheaf.imageSieve α (R.obj.map π r) ⊓ Presheaf.imageSieve φ (A.obj.map π m)
  have hS : S in J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀,
    (hr₀ : (α.app (Opposite.op Y)).hom r₀ = (R.obj

中文:
引理 map_smul
  证明: by
  let S := Presheaf.imageSieve α (R.obj.map π r) ⊓ Presheaf.imageSieve φ (A.obj.map π m)
  have hS : S in J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀,
    (hr₀ : (α.app (Opposite.op Y)).hom r₀ = (R.obj

Depends on / 依赖: commutes, congr_arg, f.commutes, g.hom
-/
protected lemma map_smul :
    A.obj.map π (smul α φ r m) = smul α φ (R.obj.map π r) (A.obj.map π m) := by
  let S := Presheaf.imageSieve α (R.obj.map π r) ⊓ Presheaf.imageSieve φ (A.obj.map π m)
  have hS : S in J Y.unop := by
    apply J.intersection_covering
    all_goals apply Presheaf.imageSieve_mem
  apply A.isSeparated _ _ hS
  rintro Y f ⟨⟨r₀,
    (hr₀ : (α.app (Opposite.op Y)).hom r₀ = (R.obj.map f.op).hom ((R.obj.map π).hom r))⟩,
    ⟨m₀, (hm₀ : (φ.app _) _ = _)⟩⟩
  rw [← ConcreteCategory.comp_apply]; rw [← Functor.map_comp]; rw [map_smul_eq α φ r m (π ≫ f.op) r₀ (by rw [hr₀]; rw [Functor.map_comp]; rw [RingCat.comp_apply]) m₀
      (by rw [hm₀, Functor.map_comp, ConcreteCategory.comp_apply]),
    map_smul_eq α φ (R.obj.map π r) (A.obj.map π m) f.op r₀ hr₀ m₀ hm₀]

end Sheafify

/--
Definition of `sheafify` / `sheafify` 的定义

English:
definition sheafify
  signature: : SheafOfModules.{v} R where
  body: letI := Sheafify.module α φ; ofPresheaf A.obj (Sheafify.map_smul _ _)
  isSheaf := A.property

中文:
定义 sheafify
  签名: : SheafOfModules.{v} R where
  定义体: letI := Sheafify.module α φ; ofPresheaf A.obj (Sheafify.map_smul _ _)
  isSheaf := A.property

Depends on / 依赖: A.obj, Sheafify, Sheafify.map_smul, Sheafify.module, map_smul, module, ofPresheaf
-/
noncomputable def sheafify : SheafOfModules.{v} R where
  val := letI := Sheafify.module α φ; ofPresheaf A.obj (Sheafify.map_smul _ _)
  isSheaf := A.property

/--
Definition of `toSheafify` / `toSheafify` 的定义

English:
definition toSheafify
  signature: : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val
  body: homMk φ (fun X r₀ m₀ => by
    simpa using! (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by simp) m₀ (by simp)).symm)

中文:
定义 toSheafify
  签名: : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val
  定义体: homMk φ (fun X r₀ m₀ => by
    simpa using! (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by simp) m₀ (by simp)).symm)

Depends on / 依赖: Sheafify, Sheafify.map_smul_eq, map_smul_eq
-/
noncomputable def toSheafify : M₀ ⟶ (restrictScalars α).obj (sheafify α φ).val :=
  homMk φ (fun X r₀ m₀ => by
    simpa using! (Sheafify.map_smul_eq α φ (α.app _ r₀) (φ.app _ m₀) (𝟙 _)
      r₀ (by simp) m₀ (by simp)).symm)

/--
lemma `toSheafify_app_apply` / 引理 `toSheafify_app_apply`

English:
lemma toSheafify_app_apply
  given: (X : Cᵒᵖ) (x : M₀.obj X)
  proof: rfl

中文:
引理 toSheafify_app_apply
  条件: (X : Cᵒᵖ) (x : M₀.obj X)
  证明: rfl
-/
lemma toSheafify_app_apply (X : Cᵒᵖ) (x : M₀.obj X) :
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `@[simp]`-normal form of `toSheafify_app_apply`. -/
@[simp]
/--
lemma `toSheafify_app_apply'` / 引理 `toSheafify_app_apply'`

English:
lemma toSheafify_app_apply'
  given: (X : Cᵒᵖ) (x : M₀.obj X)
  proof: rfl

@[simp]

中文:
引理 toSheafify_app_apply'
  条件: (X : Cᵒᵖ) (x : M₀.obj X)
  证明: rfl

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, restrictScalars
-/
lemma toSheafify_app_apply' (X : Cᵒᵖ) (x : M₀.obj X) :
    DFunLike.coe (F := (_ ->ₗ[_] ↑((ModuleCat.restrictScalars (α.app X).hom).obj _)))
    ((toSheafify α φ).app X).hom x = φ.app X x := rfl

@[simp]
/--
lemma `toPresheaf_map_toSheafify` / 引理 `toPresheaf_map_toSheafify`

English:
lemma toPresheaf_map_toSheafify
  statement: (toPresheaf R₀).map (toSheafify α φ) = φ
  proof: rfl

中文:
引理 toPresheaf_map_toSheafify
  结论: (toPresheaf R₀).map (toSheafify α φ) = φ
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.map_add, TensorProduct, TensorProduct.induction_on, induction_on, map_add
-/
lemma toPresheaf_map_toSheafify : (toPresheaf R₀).map (toSheafify α φ) = φ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallyInjective J (toSheafify α φ)
  body: by
  dsimp [IsLocallyInjective]; infer_instance

中文:
实例 :
  签名: IsLocallyInjective J (toSheafify α φ)
  定义体: by
  dsimp [IsLocallyInjective]; infer_instance

Depends on / 依赖: IsLocallyInjective, infer_instance
-/
instance : IsLocallyInjective J (toSheafify α φ) := by
  dsimp [IsLocallyInjective]; infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocallySurjective J (toSheafify α φ)
  body: by
  dsimp [IsLocallySurjective]; infer_instance

中文:
实例 :
  签名: IsLocallySurjective J (toSheafify α φ)
  定义体: by
  dsimp [IsLocallySurjective]; infer_instance

Depends on / 依赖: IsLocallySurjective, infer_instance
-/
instance : IsLocallySurjective J (toSheafify α φ) := by
  dsimp [IsLocallySurjective]; infer_instance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/--
Definition of `sheafifyHomEquiv'` / `sheafifyHomEquiv'` 的定义

English:
definition sheafifyHomEquiv'
  signature: {F : PresheafOfModules.{v} R.obj}
  body: (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)

中文:
定义 sheafifyHomEquiv'
  签名: {F : PresheafOfModules.{v} R.obj}
  定义体: (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)

Depends on / 依赖: homEquivOfIsLocallyBijective, restrictHomEquivOfIsLocallySurjective, restrictScalars, toSheafify
-/
noncomputable def sheafifyHomEquiv' {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) :
    ((sheafify α φ).val ⟶ F) ≃ (M₀ ⟶ (restrictScalars α).obj F) :=
  (restrictHomEquivOfIsLocallySurjective α hF).trans
    (homEquivOfIsLocallyBijective (f := toSheafify α φ)
      (N := (restrictScalars α).obj F) hF)

/--
lemma `comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom` / 引理 `comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom`

English:
lemma comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
  statement: {F : PresheafOfModules.{v} R.obj}
  proof: (toPresheaf _).congr_map ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

中文:
引理 comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
  结论: {F : PresheafOfModules.{v} R.obj}
  证明: (toPresheaf _).congr_map ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

Depends on / 依赖: apply_symm_apply, congr_map, sheafifyHomEquiv, toPresheaf
-/
lemma comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (restrictScalars α).obj F) :
    φ ≫ (toPresheaf R.obj).map ((sheafifyHomEquiv' α φ hF).symm f) = (toPresheaf R₀).map f :=
  (toPresheaf _).congr_map ((sheafifyHomEquiv' α φ hF).apply_symm_apply f)

/--
Definition of `sheafifyHomEquiv` / `sheafifyHomEquiv` 的定义

English:
definition sheafifyHomEquiv
  signature: {F : SheafOfModules.{v} R}
  body: (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (sheafifyHomEquiv' α φ F.isSheaf)

中文:
定义 sheafifyHomEquiv
  签名: {F : SheafOfModules.{v} R}
  定义体: (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (sheafifyHomEquiv' α φ F.isSheaf)

Depends on / 依赖: F.isSheaf, SheafOfModules, SheafOfModules.fullyFaithfulForget, fullyFaithfulForget, homEquiv, homEquiv.trans, isSheaf, sheafifyHomEquiv
-/
noncomputable def sheafifyHomEquiv {F : SheafOfModules.{v} R} :
    (sheafify α φ ⟶ F) ≃
      (M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :=
  (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    (sheafifyHomEquiv' α φ F.isSheaf)

section

variable {M₀' : PresheafOfModules.{v} R₀} {A' : Sheaf J AddCommGrpCat.{v}}
  (φ' : M₀'.presheaf ⟶ A'.obj)
  [Presheaf.IsLocallyInjective J φ'] [Presheaf.IsLocallySurjective J φ']
  (τ₀ : M₀ ⟶ M₀') (τ : A ⟶ A')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The morphism of sheaves of modules `sheafify α φ ⟶ sheafify α φ'`
induced by morphisms `τ₀ : M₀ ⟶ M₀'` and `τ : A ⟶ A'`
which satisfy `τ₀.hom ≫ φ' = φ ≫ τ.val`. -/
@[simps]
/--
Definition of `sheafifyMap` / `sheafifyMap` 的定义

English:
definition sheafifyMap
  signature: (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom)
  body: homMk τ.hom (fun X r m => by
    let f := (sheafifyHomEquiv' α φ (by exact A'.property)).symm (τ₀ ≫ toSheafify α φ')
    suffices τ.hom = (toPresheaf _).map f by simpa only [this] using! (f.app X).hom.map_smul r m
    apply ((J.W_of_isLocallyBijective φ).homEquiv _ A'.property).injective
    dsimp [

中文:
定义 sheafifyMap
  签名: (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom)
  定义体: homMk τ.hom (fun X r m => by
    let f := (sheafifyHomEquiv' α φ (by exact A'.property)).symm (τ₀ ≫ toSheafify α φ')
    suffices τ.hom = (toPresheaf _).map f by simpa only [this] using! (f.app X).hom.map_smul r m
    apply ((J.W_of_isLocallyBijective φ).homEquiv _ A'.property).injective
    dsimp [

Depends on / 依赖: Functor, Functor.map_comp, J.W_of_isLocallyBijective, W_of_isLocallyBijective, _symm_hom, comp_toPresheaf_map_sheafifyHomEquiv, f.app, hom.map_smul, homEquiv, injective, map_comp, map_smul, property, sheafifyHomEquiv, toPresheaf, toPresheaf_map_toSheafify, toSheafify
-/
noncomputable def sheafifyMap (fac : (toPresheaf R₀).map τ₀ ≫ φ' = φ ≫ τ.hom) :
    sheafify α φ ⟶ sheafify α φ' where
  val := homMk τ.hom (fun X r m => by
    let f := (sheafifyHomEquiv' α φ (by exact A'.property)).symm (τ₀ ≫ toSheafify α φ')
    suffices τ.hom = (toPresheaf _).map f by simpa only [this] using! (f.app X).hom.map_smul r m
    apply ((J.W_of_isLocallyBijective φ).homEquiv _ A'.property).injective
    dsimp [f]
    erw [comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom]
    rw [← fac]; rw [Functor.map_comp]; rw [toPresheaf_map_toSheafify])

end

end PresheafOfModules
