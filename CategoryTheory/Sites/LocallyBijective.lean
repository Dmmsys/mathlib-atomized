/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Localization

/-!
# Locally bijective morphisms of presheaves

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `A` be a concrete category.
In this file, we introduce a type class `J.WEqualsLocallyBijective A` which says
that the class `J.W` (of morphisms of presheaves which become isomorphisms
after sheafification) is the class of morphisms that are both locally injective
and locally surjective (i.e. locally bijective). We prove that this holds iff
for any presheaf `P : Cᵒᵖ ⥤ A`, the sheafification map `toSheafify J P` is locally bijective.
We show that this holds under certain universe assumptions.

-/

public section

universe w' w v' v u' u
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type u'} [Category.{v'} A] {FA : A -> A -> Type*} {CA : A -> Type w'}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]


namespace Sheaf

section

variable {F G : Sheaf J (Type w)} (f : F ⟶ G)

/--
lemma `isLocallyBijective_iff_isIso'` / 引理 `isLocallyBijective_iff_isIso'`

English:
lemma isLocallyBijective_iff_isIso'
  proof: by
  constructor
  · rintro ⟨h₁, _⟩
    rw [isLocallyInjective_iff_injective] at h₁
    suffices forall (X : Cᵒᵖ), Function.Surjective (f.hom.app X) by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [NatTrans.isIso_iff_isIso_app]
      intro X
      rw [isIso_iff_bijective]
      exact ⟨h₁ X, this X⟩
    intro X s
    have H := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _
      (Presheaf.imageSieve_mem J f.hom s)
    let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
      fun Y g hg => Presheaf.localPreimage f.hom s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply h₁
      have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
      have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
      have eq₄ := congr_arg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      rw [← Functor.map_comp_apply]; rw [← Functor.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨H.amalgamate t ht, ?_⟩
    · apply (((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property).isSeparated _
        (Presheaf.imageSieve_mem J f.hom s)).ext
      intro Y g hg
      rw [← NatTrans.naturality_apply]; rw [H.valid_glue ht]
      exact Presheaf.app_localPreimage f.hom s g hg
  · intro
    constructor <;> infer_instance

中文:
引理 isLocallyBijective_iff_isIso'
  证明: by
  constructor
  · rintro ⟨h₁, _⟩
    rw [isLocallyInjective_iff_injective] at h₁
    suffices forall (X : Cᵒᵖ), Function.Surjective (f.hom.app X) by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [NatTrans.isIso_iff_isIso_app]
      intro X
      rw [isIso_iff_bijective]
      exact ⟨h₁ X, this X⟩
    intro X s
    have H := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _
      (Presheaf.imageSieve_mem J f.hom s)
    let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
      fun Y g hg => Presheaf.localPreimage f.hom s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply h₁
      have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
      have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
      have eq₄ := congr_arg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      rw [← Functor.map_comp_apply]; rw [← Functor.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨H.amalgamate t ht, ?_⟩
    · apply (((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property).isSeparated _
        (Presheaf.imageSieve_mem J f.hom s)).ext
      intro Y g hg
      rw [← NatTrans.naturality_apply]; rw [H.valid_glue ht]
      exact Presheaf.app_localPreimage f.hom s g hg
  · intro
    constructor <;> infer_instance
-/
private lemma isLocallyBijective_iff_isIso' :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨h₁, _⟩
    rw [isLocallyInjective_iff_injective] at h₁
    suffices forall (X : Cᵒᵖ), Function.Surjective (f.hom.app X) by
      rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]; rw [NatTrans.isIso_iff_isIso_app]
      intro X
      rw [isIso_iff_bijective]
      exact ⟨h₁ X, this X⟩
    intro X s
    have H := (isSheaf_iff_isSheaf_of_type J F.obj).1 F.property _
      (Presheaf.imageSieve_mem J f.hom s)
    let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
      fun Y g hg => Presheaf.localPreimage f.hom s g hg
    have ht : t.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ w
      apply h₁
      have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
      have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
      have eq₃ := congr_arg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
      have eq₄ := congr_arg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
      refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
      rw [← Functor.map_comp_apply]; rw [← Functor.map_comp_apply]
      simp only [← op_comp, w]
    refine ⟨H.amalgamate t ht, ?_⟩
    · apply (((isSheaf_iff_isSheaf_of_type J G.obj).1 G.property).isSeparated _
        (Presheaf.imageSieve_mem J f.hom s)).ext
      intro Y g hg
      rw [← NatTrans.naturality_apply]; rw [H.valid_glue ht]
      exact Presheaf.app_localPreimage f.hom s g hg
  · intro
    constructor <;> infer_instance

end

section

variable {F G : Sheaf J A} (f : F ⟶ G) [(forget A).ReflectsIsomorphisms]
  [J.HasSheafCompose (forget A)]

/--
lemma `isLocallyBijective_iff_isIso` / 引理 `isLocallyBijective_iff_isIso`

English:
lemma isLocallyBijective_iff_isIso
  proof: by
  constructor
  · rintro ⟨_, _⟩
    rw [← isIso_iff_of_reflects_iso f (sheafCompose J (forget A))]; rw [← isLocallyBijective_iff_isIso']
    constructor <;> infer_instance
  · intro
    constructor <;> infer_instance

中文:
引理 isLocallyBijective_iff_isIso
  证明: by
  constructor
  · rintro ⟨_, _⟩
    rw [← isIso_iff_of_reflects_iso f (sheafCompose J (forget A))]; rw [← isLocallyBijective_iff_isIso']
    constructor <;> infer_instance
  · intro
    constructor <;> infer_instance

Depends on / 依赖: forget, infer_instance, isIso_iff_of_reflects_iso, isLocallyBijective_iff_isIso, sheafCompose
-/
lemma isLocallyBijective_iff_isIso :
    IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f := by
  constructor
  · rintro ⟨_, _⟩
    rw [← isIso_iff_of_reflects_iso f (sheafCompose J (forget A))]; rw [← isLocallyBijective_iff_isIso']
    constructor <;> infer_instance
  · intro
    constructor <;> infer_instance

end

end Sheaf

variable (J A)

namespace GrothendieckTopology

/--
Definition of `WEqualsLocallyBijective` / `WEqualsLocallyBijective` 的定义

English:
class WEqualsLocallyBijective
  parameters: : Prop where
  axioms and operations (1):
    - iff({X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)) : J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f

中文:
类 WEqualsLocallyBijective
  参数: : 命题 where
  公理与运算 (1 个):
    - iff({X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)) : J.W f ↔ 预层.是LocallyInjective J f ∧ 预层.是LocallySurjective J f
-/
class WEqualsLocallyBijective : Prop where
  iff {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y) :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f

section

variable {A}
variable [J.WEqualsLocallyBijective A] {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)

/--
lemma `W_iff_isLocallyBijective` / 引理 `W_iff_isLocallyBijective`

English:
lemma W_iff_isLocallyBijective
  proof: by
  apply WEqualsLocallyBijective.iff

中文:
引理 W_iff_isLocallyBijective
  证明: by
  apply WEqualsLocallyBijective.iff

Depends on / 依赖: WEqualsLocallyBijective, WEqualsLocallyBijective.iff
-/
lemma W_iff_isLocallyBijective :
    J.W f ↔ Presheaf.IsLocallyInjective J f ∧ Presheaf.IsLocallySurjective J f := by
  apply WEqualsLocallyBijective.iff

/--
lemma `W_of_isLocallyBijective` / 引理 `W_of_isLocallyBijective`

English:
lemma W_of_isLocallyBijective
  statement: [Presheaf.IsLocallyInjective J f]
  proof: by
  rw [W_iff_isLocallyBijective]
  constructor <;> infer_instance

中文:
引理 W_of_isLocallyBijective
  结论: [预层.是LocallyInjective J f]
  证明: by
  rw [W_iff_isLocallyBijective]
  constructor <;> infer_instance

Depends on / 依赖: W_iff_isLocallyBijective, infer_instance
-/
lemma W_of_isLocallyBijective [Presheaf.IsLocallyInjective J f]
    [Presheaf.IsLocallySurjective J f] : J.W f := by
  rw [W_iff_isLocallyBijective]
  constructor <;> infer_instance

variable {J f}

/--
lemma `W.isLocallyInjective` / 引理 `W.isLocallyInjective`

English:
lemma W.isLocallyInjective
  given: (hf : J.W f)
  statement: Presheaf.IsLocallyInjective J f
  proof: ((J.W_iff_isLocallyBijective f).1 hf).1

中文:
引理 W.isLocallyInjective
  条件: (hf : J.W f)
  结论: 预层.是LocallyInjective J f
  证明: ((J.W_iff_isLocallyBijective f).1 hf).1

Depends on / 依赖: J.W_iff_isLocallyBijective, W_iff_isLocallyBijective
-/
lemma W.isLocallyInjective (hf : J.W f) : Presheaf.IsLocallyInjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).1

/--
lemma `W.isLocallySurjective` / 引理 `W.isLocallySurjective`

English:
lemma W.isLocallySurjective
  given: (hf : J.W f)
  statement: Presheaf.IsLocallySurjective J f
  proof: ((J.W_iff_isLocallyBijective f).1 hf).2

中文:
引理 W.isLocallySurjective
  条件: (hf : J.W f)
  结论: 预层.是LocallySurjective J f
  证明: ((J.W_iff_isLocallyBijective f).1 hf).2

Depends on / 依赖: J.W_iff_isLocallyBijective, W_iff_isLocallyBijective
-/
lemma W.isLocallySurjective (hf : J.W f) : Presheaf.IsLocallySurjective J f :=
  ((J.W_iff_isLocallyBijective f).1 hf).2

variable [HasWeakSheafify J A] (P : Cᵒᵖ ⥤ A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)
  body: (J.W_toSheafify P).isLocallyInjective

中文:
实例 :
  签名: 预层.是LocallyInjective J (范畴论.toSheafify J P)
  定义体: (J.W_toSheafify P).isLocallyInjective

Depends on / 依赖: J.W_toSheafify, W_toSheafify, isLocallyInjective
-/
instance : Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallyInjective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P)
  body: (J.W_toSheafify P).isLocallySurjective

中文:
实例 :
  签名: 预层.是LocallySurjective J (范畴论.toSheafify J P)
  定义体: (J.W_toSheafify P).isLocallySurjective

Depends on / 依赖: J.W_toSheafify, W_toSheafify, isLocallySurjective
-/
instance : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) :=
  (J.W_toSheafify P).isLocallySurjective

end

/--
lemma `WEqualsLocallyBijective.mk'` / 引理 `WEqualsLocallyBijective.mk'`

English:
lemma WEqualsLocallyBijective.mk'
  statement: [HasWeakSheafify J A] [(forget A).ReflectsIsomorphisms]
  proof: by
    rw [W_iff]; rw [← Sheaf.isLocallyBijective_iff_isIso (A := A)]; rw [← Presheaf.isLocallyInjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [← Presheaf.isLocallySurjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [CategoryTheory.toSheafify_naturality]; rw [Presheaf.comp_isLocallyInjective_iff]; rw [Presheaf.comp_isLocallySurjective_iff]

中文:
引理 WEqualsLocallyBijective.mk'
  结论: [HasWeakSheafify J A] [(forget A).反映同构]
  证明: by
    rw [W_iff]; rw [← Sheaf.isLocallyBijective_iff_isIso (A := A)]; rw [← Presheaf.isLocallyInjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [← Presheaf.isLocallySurjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [CategoryTheory.toSheafify_naturality]; rw [Presheaf.comp_isLocallyInjective_iff]; rw [Presheaf.comp_isLocallySurjective_iff]

Depends on / 依赖: CategoryTheory, CategoryTheory.toSheafify, CategoryTheory.toSheafify_naturality, Presheaf, Presheaf.comp_isLocallyInjective_iff, Presheaf.comp_isLocallySurjective_iff, Presheaf.isLocallyInjective_comp_iff, Presheaf.isLocallySurjective_comp_iff, Sheaf.isLocallyBijective_iff_isIso, W_iff, comp_isLocallyInjective_iff, comp_isLocallySurjective_iff, isLocallyBijective_iff_isIso, isLocallyInjective_comp_iff, isLocallySurjective_comp_iff, toSheafify, toSheafify_naturality
-/
lemma WEqualsLocallyBijective.mk' [HasWeakSheafify J A] [(forget A).ReflectsIsomorphisms]
    [J.HasSheafCompose (forget A)]
    [forall (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)]
    [forall (P : Cᵒᵖ ⥤ A), Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P)] :
    J.WEqualsLocallyBijective A where
  iff {P Q} f := by
    rw [W_iff]; rw [← Sheaf.isLocallyBijective_iff_isIso (A := A)]; rw [← Presheaf.isLocallyInjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [← Presheaf.isLocallySurjective_comp_iff J f (CategoryTheory.toSheafify J Q)]; rw [CategoryTheory.toSheafify_naturality]; rw [Presheaf.comp_isLocallyInjective_iff]; rw [Presheaf.comp_isLocallySurjective_iff]

instance {D : Type w} [Category.{w'} D] {FD : D -> D -> Type*} {CD : D -> Type (max u v)}
    [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max u v} D FD]
    [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] [(forget D).ReflectsIsomorphisms] :
    J.WEqualsLocallyBijective D := by
  apply WEqualsLocallyBijective.mk'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: J.WEqualsLocallyBijective (Type (max u v))
  body: inferInstance

中文:
实例 :
  签名: J.WEqualsLocallyBijective (类型 (最大值 u v))
  定义体: inferInstance
-/
instance : J.WEqualsLocallyBijective (Type (max u v)) :=
  inferInstance

end GrothendieckTopology

namespace Presheaf

variable {A}
variable [HasWeakSheafify J A] [J.WEqualsLocallyBijective A] {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocallyInjective_presheafToSheaf_map_iff` / 引理 `isLocallyInjective_presheafToSheaf_map_iff`

English:
lemma isLocallyInjective_presheafToSheaf_map_iff
  proof: by
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]; rw [← isLocallyInjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallyInjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

中文:
引理 isLocallyInjective_presheafToSheaf_map_iff
  证明: by
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]; rw [← isLocallyInjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallyInjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

Depends on / 依赖: ObjectProperty, Sheaf.isLocallyInjective_sheafToPresheaf_map_iff, comp_isLocallyInjective_iff, isLocallyInjective_comp_iff, isLocallyInjective_sheafToPresheaf_map_iff, toSheafify, toSheafify_naturality
-/
lemma isLocallyInjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallyInjective ((presheafToSheaf J A).map φ) ↔ IsLocallyInjective J φ := by
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]; rw [← isLocallyInjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallyInjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocallySurjective_presheafToSheaf_map_iff` / 引理 `isLocallySurjective_presheafToSheaf_map_iff`

English:
lemma isLocallySurjective_presheafToSheaf_map_iff
  proof: by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]; rw [← isLocallySurjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallySurjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

中文:
引理 isLocallySurjective_presheafToSheaf_map_iff
  证明: by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]; rw [← isLocallySurjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallySurjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

Depends on / 依赖: ObjectProperty, Sheaf.isLocallySurjective_sheafToPresheaf_map_iff, comp_isLocallySurjective_iff, isLocallySurjective_comp_iff, isLocallySurjective_sheafToPresheaf_map_iff, toSheafify, toSheafify_naturality
-/
lemma isLocallySurjective_presheafToSheaf_map_iff :
    Sheaf.IsLocallySurjective ((presheafToSheaf J A).map φ) ↔ IsLocallySurjective J φ := by
  rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]; rw [← isLocallySurjective_comp_iff J _ (toSheafify J Q)]; rw [← comp_isLocallySurjective_iff J (toSheafify J P)]; rw [toSheafify_naturality]; rw [ObjectProperty.ι_map]

end Presheaf

end CategoryTheory
