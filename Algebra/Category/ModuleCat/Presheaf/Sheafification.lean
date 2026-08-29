/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# The sheafification functor for presheaves of modules

In this file, we construct a functor
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R`
for a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings.
In particular, if `α` is the identity of `R.val`, we obtain the
sheafification functor `PresheafOfModules R.val ⥤ SheafOfModules R`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory Category Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PresheafOfModules

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms
  body: have : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)

中文:
实例 :
  签名: (模层.toSheaf.{v} R).反映同构
  定义体: have : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)

Depends on / 依赖: ReflectsIsomorphisms, SheafOfModules, SheafOfModules.forget, SheafOfModules.toSheaf, forget, reflectsIsomorphisms_of_comp, sheafToPresheaf, toPresheaf, toSheaf
-/
instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  have : (SheafOfModules.toSheaf.{v} R ⋙ sheafToPresheaf _ _).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{v} R ⋙ toPresheaf _).ReflectsIsomorphisms
  reflectsIsomorphisms_of_comp _ (sheafToPresheaf _ _)

section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- Given a locally bijective morphism `α : R₀ ⟶ R.val` where `R₀` is a presheaf of rings
and `R` a sheaf of rings (i.e. `R` identifies to the sheafification of `R₀`), this is
the associated sheaf of modules functor `PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R`. -/
@[simps! -isSimp map]
/--
Definition of `sheafification` / `sheafification` 的定义

English:
definition sheafification
  signature: : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  body: sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f
    ((toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat).map f)
      (by apply toSheafify_naturality)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl

中文:
定义 sheafification
  签名: : 预模层.{v} R₀ ⥤ 模层.{v} R where
  定义体: sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f
    ((toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat).map f)
      (by apply toSheafify_naturality)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl

Depends on / 依赖: CategoryTheory, CategoryTheory.toSheafify, presheaf, sheafify, toSheafify
-/
noncomputable def sheafification : PresheafOfModules.{v} R₀ ⥤ SheafOfModules.{v} R where
  obj M₀ := sheafify α (CategoryTheory.toSheafify J M₀.presheaf)
  map f := sheafifyMap _ _ _ f
    ((toPresheaf R₀ ⋙ presheafToSheaf J AddCommGrpCat).map f)
      (by apply toSheafify_naturality)
  map_id M₀ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl
  map_comp _ _ := by
    ext1
    apply (toPresheaf _).map_injective
    simp
    rfl

/--
Definition of `sheafificationCompToSheaf` / `sheafificationCompToSheaf` 的定义

English:
definition sheafificationCompToSheaf
  signature: :
  body: Iso.refl _

中文:
定义 sheafificationCompToSheaf
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def sheafificationCompToSheaf :
    sheafification.{v} α ⋙ SheafOfModules.toSheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat :=
  Iso.refl _

/--
Definition of `sheafificationCompForgetCompToPresheaf` / `sheafificationCompForgetCompToPresheaf` 的定义

English:
definition sheafificationCompForgetCompToPresheaf
  signature: :
  body: Iso.refl _

中文:
定义 sheafificationCompForgetCompToPresheaf
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def sheafificationCompForgetCompToPresheaf :
    sheafification.{v} α ⋙ SheafOfModules.forget _ ⋙ toPresheaf _ ≅
      toPresheaf _ ⋙ presheafToSheaf J AddCommGrpCat ⋙ sheafToPresheaf J AddCommGrpCat :=
  Iso.refl _

/--
Definition of `sheafificationHomEquiv` / `sheafificationHomEquiv` 的定义

English:
definition sheafificationHomEquiv
  body: by
  apply sheafifyHomEquiv

中文:
定义 sheafificationHomEquiv
  定义体: by
  apply sheafifyHomEquiv

Depends on / 依赖: sheafifyHomEquiv
-/
noncomputable def sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R} :
    ((sheafification α).obj P ⟶ F) ≃
      (P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) := by
  apply sheafifyHomEquiv

/--
lemma `toPresheaf_map_sheafificationHomEquiv_def` / 引理 `toPresheaf_map_sheafificationHomEquiv_def`

English:
lemma toPresheaf_map_sheafificationHomEquiv_def
  proof: rfl

中文:
引理 toPresheaf_map_sheafificationHomEquiv_def
  证明: rfl
-/
lemma toPresheaf_map_sheafificationHomEquiv_def
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      CategoryTheory.toSheafify J P.presheaf ≫ (toPresheaf R.obj).map f.val := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `toPresheaf_map_sheafificationHomEquiv` / 引理 `toPresheaf_map_sheafificationHomEquiv`

English:
lemma toPresheaf_map_sheafificationHomEquiv
  proof: by
  rw [toPresheaf_map_sheafificationHomEquiv_def]; rw [Adjunction.homEquiv_unit]
  dsimp

中文:
引理 toPresheaf_map_sheafificationHomEquiv
  证明: by
  rw [toPresheaf_map_sheafificationHomEquiv_def]; rw [Adjunction.homEquiv_unit]
  dsimp

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, homEquiv_unit, toPresheaf_map_sheafificationHomEquiv_def
-/
lemma toPresheaf_map_sheafificationHomEquiv
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (f : (sheafification α).obj P ⟶ F) :
    (toPresheaf R₀).map (sheafificationHomEquiv α f) =
      (sheafificationAdjunction J AddCommGrpCat).homEquiv P.presheaf
        ((SheafOfModules.toSheaf _).obj F) ((SheafOfModules.toSheaf _).map f) := by
  rw [toPresheaf_map_sheafificationHomEquiv_def]; rw [Adjunction.homEquiv_unit]
  dsimp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toSheaf_map_sheafificationHomEquiv_symm` / 引理 `toSheaf_map_sheafificationHomEquiv_symm`

English:
lemma toSheaf_map_sheafificationHomEquiv_symm
  proof: by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]; rw [Adjunction.homEquiv_unit]; rw [Equiv.symm_apply_apply]
  rfl

中文:
引理 toSheaf_map_sheafificationHomEquiv_symm
  证明: by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]; rw [Adjunction.homEquiv_unit]; rw [Equiv.symm_apply_apply]
  rfl

Depends on / 依赖: AddCommGrpCat, Adjunction, Adjunction.homEquiv_unit, Equiv.apply_symm_apply, Equiv.symm_apply_apply, apply_symm_apply, homEquiv, homEquiv_unit, injective, sheafificationAdjunction, sheafificationHomEquiv, surjective, symm_apply_apply
-/
lemma toSheaf_map_sheafificationHomEquiv_symm
    {P : PresheafOfModules.{v} R₀} {F : SheafOfModules.{v} R}
    (g : P ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F)) :
    (SheafOfModules.toSheaf _).map ((sheafificationHomEquiv α).symm g) =
      (((sheafificationAdjunction J AddCommGrpCat).homEquiv
        P.presheaf ((SheafOfModules.toSheaf R).obj F)).symm ((toPresheaf R₀).map g)) := by
  obtain ⟨f, rfl⟩ := (sheafificationHomEquiv α).surjective g
  apply ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]; rw [Adjunction.homEquiv_unit]; rw [Equiv.symm_apply_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `sheafificationAdjunction` / `sheafificationAdjunction` 的定义

English:
definition sheafificationAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g => by
        apply (SheafOfModules.toSheaf _).map_injective
        simp only [Functor.comp_obj, Functor.map_comp]
        rw [toSheaf_map_sheafificationHomEquiv_symm α (f ≫ g)]; rw [toSheaf_map_sheafificationHomEquiv_symm α g]; rw [Functor.map_comp]
        apply (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).homEquiv_naturality_left_symm
      homEquiv_naturality_right := fun {P₀ M N} f g => by
        apply (toPresheaf _).map_injective
        erw [toPresheaf_map_sheafificationHomEquiv] }

中文:
定义 sheafificationAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g => by
        apply (SheafOfModules.toSheaf _).map_injective
        simp only [Functor.comp_obj, Functor.map_comp]
        rw [toSheaf_map_sheafificationHomEquiv_symm α (f ≫ g)]; rw [toSheaf_map_sheafificationHomEquiv_symm α g]; rw [Functor.map_comp]
        apply (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).homEquiv_naturality_left_symm
      homEquiv_naturality_right := fun {P₀ M N} f g => by
        apply (toPresheaf _).map_injective
        erw [toPresheaf_map_sheafificationHomEquiv] }

Depends on / 依赖: AddCommGrpCat, Adjunction, Adjunction.mkOfHomEquiv, CategoryTheory, CategoryTheory.sheafificationAdjunction, Functor, Functor.comp_obj, Functor.map_comp, SheafOfModules, SheafOfModules.toSheaf, comp_obj, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, map_comp, map_injective, mkOfHomEquiv, sheafificationAdjunction, sheafificationHomEquiv, toSheaf
-/
noncomputable def sheafificationAdjunction :
    sheafification.{v} α ⊣ SheafOfModules.forget R ⋙ restrictScalars α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => sheafificationHomEquiv α
      homEquiv_naturality_left_symm := fun {P₀ Q₀ N} f g => by
        apply (SheafOfModules.toSheaf _).map_injective
        simp only [Functor.comp_obj, Functor.map_comp]
        rw [toSheaf_map_sheafificationHomEquiv_symm α (f ≫ g)]; rw [toSheaf_map_sheafificationHomEquiv_symm α g]; rw [Functor.map_comp]
        apply (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).homEquiv_naturality_left_symm
      homEquiv_naturality_right := fun {P₀ M N} f g => by
        apply (toPresheaf _).map_injective
        erw [toPresheaf_map_sheafificationHomEquiv] }

/--
lemma `sheafificationAdjunction_homEquiv_apply` / 引理 `sheafificationAdjunction_homEquiv_apply`

English:
lemma sheafificationAdjunction_homEquiv_apply
  statement: {P : PresheafOfModules.{v} R₀}
  proof: rfl

@[simp]

中文:
引理 sheafificationAdjunction_homEquiv_apply
  结论: {P : 预模层.{v} R₀}
  证明: rfl

@[simp]
-/
lemma sheafificationAdjunction_homEquiv_apply {P : PresheafOfModules.{v} R₀}
    {F : SheafOfModules.{v} R} (f : (sheafification α).obj P ⟶ F) :
    (sheafificationAdjunction α).homEquiv P F f = sheafificationHomEquiv α f := rfl

@[simp]
/--
lemma `toPresheaf_map_sheafificationAdjunction_unit_app` / 引理 `toPresheaf_map_sheafificationAdjunction_unit_app`

English:
lemma toPresheaf_map_sheafificationAdjunction_unit_app
  given: (M₀ : PresheafOfModules.{v} R₀)
  proof: rfl

@[simp]

中文:
引理 toPresheaf_map_sheafificationAdjunction_unit_app
  条件: (M₀ : 预模层.{v} R₀)
  证明: rfl

@[simp]
-/
lemma toPresheaf_map_sheafificationAdjunction_unit_app (M₀ : PresheafOfModules.{v} R₀) :
    (toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀) =
      CategoryTheory.toSheafify J M₀.presheaf := rfl

@[simp]
/--
lemma `toSheaf_map_sheafificationAdjunction_counit_app` / 引理 `toSheaf_map_sheafificationAdjunction_counit_app`

English:
lemma toSheaf_map_sheafificationAdjunction_counit_app
  given: (M : SheafOfModules.{v} R)
  proof: (toSheaf_map_sheafificationHomEquiv_symm _ _).trans
    (by rw [← Adjunction.homEquiv_symm_id]; rfl)

中文:
引理 toSheaf_map_sheafificationAdjunction_counit_app
  条件: (M : 模层.{v} R)
  证明: (toSheaf_map_sheafificationHomEquiv_symm _ _).trans
    (by rw [← Adjunction.homEquiv_symm_id]; rfl)

Depends on / 依赖: Adjunction, Adjunction.homEquiv_symm_id, DFunLike, DFunLike.congr_fun, ModuleCat, ModuleCat.hom_ext_iff.mp, congr_fun, homEquiv_symm_id, hom_ext_iff, toSheaf_map_sheafificationHomEquiv_symm
-/
lemma toSheaf_map_sheafificationAdjunction_counit_app (M : SheafOfModules.{v} R) :
    (SheafOfModules.toSheaf R).map ((sheafificationAdjunction α).counit.app M) =
      (CategoryTheory.sheafificationAdjunction J
          AddCommGrpCat.{v}).counit.app ((SheafOfModules.toSheaf R).obj M) :=
  (toSheaf_map_sheafificationHomEquiv_symm _ _).trans
    (by rw [← Adjunction.homEquiv_symm_id]; rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (sheafification.{v} α).IsLeftAdjoint
  body: (sheafificationAdjunction α).isLeftAdjoint

中文:
实例 :
  签名: (sheafification.{v} α).是左伴随
  定义体: (sheafificationAdjunction α).isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, mono_iff_injective, sheafificationAdjunction
-/
instance : (sheafification.{v} α).IsLeftAdjoint :=
  (sheafificationAdjunction α).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (sheafificationAdjunction α).counit
  body: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  simp only [Functor.id_obj, toSheaf_map_sheafificationAdjunction_counit_app]
  infer_instance

中文:
实例 :
  签名: 是同构 (sheafificationAdjunction α).counit
  定义体: by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  simp only [Functor.id_obj, toSheaf_map_sheafificationAdjunction_counit_app]
  infer_instance

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, Functor, Functor.id_obj, ModuleCat, NatTrans, NatTrans.isIso_iff_isIso_app, ReflectsIsomorphisms, SheafOfModules, SheafOfModules.toSheaf, forget, id_obj, infer_instance, isIso_iff_isIso_app, isIso_iff_of_reflects_iso, reflectsIsomorphisms_of_comp, restrictScalars, toSheaf, toSheaf_map_sheafificationAdjunction_counit_app
-/
instance : IsIso (sheafificationAdjunction α).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  simp only [Functor.id_obj, toSheaf_map_sheafificationAdjunction_counit_app]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Full
  body: (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.full

中文:
实例 :
  签名: (模层.forget.{v} R ⋙ restrictScalars α).满
  定义体: (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.full

Depends on / 依赖: Module, fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit.full, sheafificationAdjunction
-/
instance : (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Full :=
  (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Faithful
  body: (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.faithful

中文:
实例 :
  签名: (模层.forget.{v} R ⋙ restrictScalars α).忠实
  定义体: (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.faithful

Depends on / 依赖: faithful, fullyFaithfulROfIsIsoCounit, fullyFaithfulROfIsIsoCounit.faithful, sheafificationAdjunction
-/
instance : (SheafOfModules.forget.{v} R ⋙ restrictScalars α).Faithful :=
  (sheafificationAdjunction.{v} α).fullyFaithfulROfIsIsoCounit.faithful

end

section

variable [HasSheafify J AddCommGrpCat.{v}]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: comp_preservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGrpCat)

中文:
实例 :
  定义体: comp_preservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGrpCat)

Depends on / 依赖: AddCommGrpCat, comp_preservesFiniteLimits, presheafToSheaf, toPresheaf
-/
noncomputable instance :
    PreservesFiniteLimits (sheafification.{v} α ⋙ SheafOfModules.toSheaf.{v} R) :=
  comp_preservesFiniteLimits (toPresheaf.{v} R₀) (presheafToSheaf J AddCommGrpCat)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms
  body: reflectsIsomorphisms_of_comp (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)

中文:
实例 :
  签名: (模层.toSheaf.{v} R).反映同构
  定义体: reflectsIsomorphisms_of_comp (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)

Depends on / 依赖: SheafOfModules, SheafOfModules.toSheaf, reflectsIsomorphisms_of_comp, sheafToPresheaf, toSheaf
-/
instance : (SheafOfModules.toSheaf.{v} R).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_comp (SheafOfModules.toSheaf.{v} R) (sheafToPresheaf J _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R)
  body: inferInstance

中文:
实例 :
  签名: ReflectsFiniteLimits (模层.toSheaf.{v} R)
  定义体: inferInstance

Depends on / 依赖: CommRing, sMulCommClass_mk
-/
noncomputable instance : ReflectsFiniteLimits (SheafOfModules.toSheaf.{v} R) where
  reflects _ _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (sheafification.{v} α)
  body: preservesFiniteLimits_of_reflects_of_preserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

中文:
实例 :
  签名: 保持FiniteLimits (sheafification.{v} α)
  定义体: preservesFiniteLimits_of_reflects_of_preserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

Depends on / 依赖: SheafOfModules, SheafOfModules.toSheaf, preservesFiniteLimits_of_reflects_of_preserves, sheafification, toSheaf
-/
noncomputable instance : PreservesFiniteLimits (sheafification.{v} α) :=
  preservesFiniteLimits_of_reflects_of_preserves
    (sheafification.{v} α) (SheafOfModules.toSheaf.{v} R)

end

end PresheafOfModules
