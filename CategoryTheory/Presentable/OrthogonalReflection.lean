/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Localization.BousfieldTransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `W.isLocal.isLocal` and
is an isomorphism iff `Z` belongs to `W.isLocal` (see the lemma `isIso_toSucc_iff`).
The morphism `toSucc W Z : Z ⟶ succ W Z` is defined as a composition
of two morphisms that are roughly described as follows:
* `toStep W Z : Z ⟶ step W Z`: for any morphism `f : X ⟶ Y` satisfying `W`
  and any morphism `X ⟶ Z`, we "attach" a morphism `Y ⟶ step W Z` (using
  coproducts and a pushout in essentially the same way as it is done in
  the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` for the small object
  argument);
* `fromStep W Z : step W Z ⟶ succ W Z`: this morphism coequalizes all pairs
  of morphisms `g₁ g₂ : Y ⟶ step W Z` such that there is a `f : X ⟶ Y`
  satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.

The morphism `toSucc W Z : Z ⟶ succ W Z` is a variant of the (wrong) definition
p. 32 in the book by Adámek and Rosický. In this book, a slightly different object
than `succ W Z` is defined directly as a colimit of an intricate diagram, but
contrary to what is stated on p. 33, it does not satisfy `isIso_toSucc_iff`.
The author of this file was unable to understand the attempt of the authors
to fix this mistake in the errata to this book. This led to the definition
in two steps outlined above.

## Main results

The morphisms described above `toSucc W Z : Z ⟶ succ W Z` for all `Z : C` allow to
define `succStruct W Z₀ : SuccStruct C` for any `Z₀ : C`. By applying
a transfinite iteration to this `SuccStruct`, we obtain the following results
under the assumption that `W : MorphismProperty C` is a `w`-small property
of morphisms in a locally `κ`-presentable category `C` (with `κ : Cardinal.{w}`
a regular cardinal) such that the domains and codomains of the morphisms
satisfying `W` are `κ`-presentable:
* `MorphismProperty.isRightAdjoint_ι_isLocal`: existence of the left adjoint
  of the inclusion `W.isLocal ⥤ C`;
* `MorphismProperty.isLocallyPresentable_isLocal`: the full subcategory
  `W.isLocal` is locally presentable.

This is essentially the implication (i) → (ii) in Theorem 1.39 (and the corollary 1.40)
in the book by Adámek and Rosický (note that according to the
errata to this book, the implication (ii) → (i) is wrong when `κ = ℵ₀`).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Limits Localization Opposite

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `MorphismProperty.isClosedUnderColimitsOfShape_isLocal` / 引理 `MorphismProperty.isClosedUnderColimitsOfShape_isLocal`

English:
lemma MorphismProperty.isClosedUnderColimitsOfShape_isLocal
  proof: fun Z ⟨p⟩ X Y f hf => by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u]; rw [← p.w v]; rw [reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩

中文:
引理 MorphismProperty.isClosedUnderColimitsOfShape_isLocal
  证明: fun Z ⟨p⟩ X Y f hf => by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u]; rw [← p.w v]; rw [reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩

Depends on / 依赖: Category, Category.assoc, IsCardinalPresentable, IsCardinalPresentable.exists_eq_of_isColimit, IsCardinalPresentable.exists_hom_of_isColimit, exists_eq_of_isColimit, exists_hom_of_isColimit, isColimit, p.isColimit, p.prop_diag_obj, prop_diag_obj, reassoc_of
-/
lemma MorphismProperty.isClosedUnderColimitsOfShape_isLocal
    (J : Type u') [Category.{v'} J] [EssentiallySmall.{w} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun Z ⟨p⟩ X Y f hf => by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u]; rw [← p.w v]; rw [reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩

/--
lemma `MorphismProperty.isCardinalAccessible_ι_isLocal` / 引理 `MorphismProperty.isCardinalAccessible_ι_isLocal`

English:
lemma MorphismProperty.isCardinalAccessible_ι_isLocal
  proof: by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    infer_instance

中文:
引理 MorphismProperty.isCardinalAccessible_ι_isLocal
  证明: by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    infer_instance

Depends on / 依赖: HasCardinalFilteredColimits, HasCardinalFilteredColimits.hasColimitsOfShape, W.isClosedUnderColimitsOfShape_isLocal, hasColimitsOfShape, infer_instance, isClosedUnderColimitsOfShape_isLocal
-/
lemma MorphismProperty.isCardinalAccessible_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits C κ]
    (hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.ι.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    have := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    infer_instance

namespace OrthogonalReflection

variable (Z : C)

/--
Definition of `D₁` / `D₁` 的定义

English:
definition D₁
  signature: : Type _
  body: Σ (f : W.toSet), f.1.left ⟶ Z

中文:
定义 D₁
  签名: : 类型 _
  定义体: Σ (f : W.toSet), f.1.left ⟶ Z

Depends on / 依赖: W.toSet
-/
def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MorphismProperty.IsSmall.{w}
  signature: W] [LocallySmall.{w} C] :
  body: by
  dsimp [D₁]
  infer_instance

中文:
实例 [MorphismProperty.是Small.{w}
  签名: W] [LocallySmall.{w} C] :
  定义体: by
  dsimp [D₁]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C] :
    Small.{w} (D₁ (W := W) (Z := Z)) := by
  dsimp [D₁]
  infer_instance

/--
lemma `D₁.hasCoproductsOfShape` / 引理 `D₁.hasCoproductsOfShape`

English:
lemma D₁.hasCoproductsOfShape
  statement: [MorphismProperty.IsSmall.{w} W]
  proof: hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)

中文:
引理 D₁.hasCoproductsOfShape
  结论: [MorphismProperty.是Small.{w} W]
  证明: hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)
-/
lemma D₁.hasCoproductsOfShape [MorphismProperty.IsSmall.{w} W]
    [LocallySmall.{w} C] [HasCoproducts.{w} C] :
    HasCoproductsOfShape (D₁ (W := W) (Z := Z)) C :=
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)

variable {W Z} in
/--
Definition of `D₁.obj₁` / `D₁.obj₁` 的定义

English:
definition D₁.obj₁
  signature: (d : D₁ W Z)
  body: d.1.1.left

中文:
定义 D₁.obj₁
  签名: (d : D₁ W Z)
  定义体: d.1.1.left
-/
def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in
/--
Definition of `D₁.obj₂` / `D₁.obj₂` 的定义

English:
definition D₁.obj₂
  signature: (d : D₁ W Z)
  body: d.1.1.right

中文:
定义 D₁.obj₂
  签名: (d : D₁ W Z)
  定义体: d.1.1.right
-/
def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

section

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

/--
Definition of `D₁.l` / `D₁.l` 的定义

English:
abbreviation D₁.l
  signature: : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z
  body: Sigma.desc (fun d => d.2)

中文:
缩写 D₁.l
  签名: : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z
  定义体: Sigma.desc (fun d => d.2)
-/
noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d => d.2)

variable {W Z} in
/--
Definition of `D₁.ιLeft` / `D₁.ιLeft` 的定义

English:
abbreviation D₁.ιLeft
  signature: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  body: Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

中文:
缩写 D₁.ιLeft
  签名: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  定义体: Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩
-/
noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ obj₁ (W := W) (Z := Z) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
/--
lemma `D₁.ιLeft_comp_l` / 引理 `D₁.ιLeft_comp_l`

English:
lemma D₁.ιLeft_comp_l
  given: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  proof: Sigma.ι_desc _ _

中文:
引理 D₁.ιLeft_comp_l
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  证明: Sigma.ι_desc _ _
-/
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g :=
  Sigma.ι_desc _ _

variable [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]

/--
Definition of `D₁.t` / `D₁.t` 的定义

English:
abbreviation D₁.t
  signature: : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z))
  body: Limits.Sigma.map (fun d => d.1.1.hom)

中文:
缩写 D₁.t
  签名: : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z))
  定义体: Limits.Sigma.map (fun d => d.1.1.hom)
-/
noncomputable abbrev D₁.t : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Limits.Sigma.map (fun d => d.1.1.hom)

variable {W Z} in
/--
Definition of `D₁.ιRight` / `D₁.ιRight` 的定义

English:
abbreviation D₁.ιRight
  signature: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  body: Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

中文:
缩写 D₁.ιRight
  签名: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  定义体: Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩
-/
noncomputable abbrev D₁.ιRight {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    Y ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

set_option backward.isDefEq.respectTransparency false in -- Needed below
variable {W Z} in
@[reassoc]
/--
lemma `D₁.ι_comp_t` / 引理 `D₁.ι_comp_t`

English:
lemma D₁.ι_comp_t
  given: (d : D₁ W Z)
  proof: by
  apply ι_colimMap

中文:
引理 D₁.ι_comp_t
  条件: (d : D₁ W Z)
  证明: by
  apply ι_colimMap
-/
lemma D₁.ι_comp_t (d : D₁ W Z) :
    Sigma.ι _ d ≫ D₁.t W Z = d.1.1.hom ≫ Sigma.ι obj₂ d := by
  apply ι_colimMap

variable {W Z} in
@[reassoc]
/--
lemma `D₁.ιLeft_comp_t` / 引理 `D₁.ιLeft_comp_t`

English:
lemma D₁.ιLeft_comp_t
  given: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  proof: by
  apply ι_colimMap

中文:
引理 D₁.ιLeft_comp_t
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  证明: by
  apply ι_colimMap
-/
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

/--
Definition of `step` / `step` 的定义

English:
abbreviation step
  body: pushout (D₁.t W Z) (D₁.l W Z)

中文:
缩写 step
  定义体: pushout (D₁.t W Z) (D₁.l W Z)

Depends on / 依赖: pushout
-/
noncomputable abbrev step := pushout (D₁.t W Z) (D₁.l W Z)

/--
Definition of `toStep` / `toStep` 的定义

English:
abbreviation toStep
  signature: : Z ⟶ step W Z
  body: pushout.inr _ _

中文:
缩写 toStep
  签名: : Z ⟶ step W Z
  定义体: pushout.inr _ _

Depends on / 依赖: pushout, pushout.inr
-/
noncomputable abbrev toStep : Z ⟶ step W Z := pushout.inr _ _

/--
Definition of `D₂` / `D₂` 的定义

English:
definition D₂
  signature: : Type _
  body: Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

中文:
定义 D₂
  签名: : 类型 _
  定义体: Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

Depends on / 依赖: W.toSet
-/
def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

/-- The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
/--
Definition of `D₂.multispanShape` / `D₂.multispanShape` 的定义

English:
definition D₂.multispanShape
  signature: : MultispanShape where
  body: D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

中文:
定义 D₂.multispanShape
  签名: : MultispanShape where
  定义体: D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit
-/
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

section

variable [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{w} (D₂ (W := W) (Z := Z))
  body: by
  dsimp [D₂]
  infer_instance

中文:
实例 :
  签名: Small.{w} (D₂ (W := W) (Z := Z))
  定义体: by
  dsimp [D₂]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Small.{w} (D₂ (W := W) (Z := Z)) := by
  dsimp [D₂]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{w} (D₂.multispanShape W Z).L
  body: by dsimp; infer_instance

中文:
实例 :
  签名: Small.{w} (D₂.multispanShape W Z).L
  定义体: by dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance : Small.{w} (D₂.multispanShape W Z).L := by dsimp; infer_instance

attribute [local instance] essentiallySmall_of_small_of_locallySmall in
/--
lemma `D₂.hasColimitsOfShape` / 引理 `D₂.hasColimitsOfShape`

English:
lemma D₂.hasColimitsOfShape
  given: [HasColimitsOfSize.{w, w} C]
  proof: hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).symm

中文:
引理 D₂.hasColimitsOfShape
  条件: [有余limitsOfSize.{w, w} C]
  证明: hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).symm

Depends on / 依赖: equivSmallModel, hasColimitsOfShape_of_equivalence
-/
lemma D₂.hasColimitsOfShape [HasColimitsOfSize.{w, w} C] :
    HasColimitsOfShape (WalkingMultispan (multispanShape W Z)) C :=
  hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).symm

end

/-- The diagram of the multicoequalizer of all pair of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
/--
Definition of `D₂.multispanIndex` / `D₂.multispanIndex` 的定义

English:
definition D₂.multispanIndex
  signature: : MultispanIndex (multispanShape W Z) C where
  body: d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2

中文:
定义 D₂.multispanIndex
  签名: : MultispanIndex (multispanShape W Z) C where
  定义体: d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2
-/
noncomputable def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

/--
Definition of `succ` / `succ` 的定义

English:
abbreviation succ
  body: multicoequalizer (D₂.multispanIndex W Z)

中文:
缩写 succ
  定义体: multicoequalizer (D₂.multispanIndex W Z)

Depends on / 依赖: multicoequalizer, multispanIndex
-/
noncomputable abbrev succ := multicoequalizer (D₂.multispanIndex W Z)

/--
Definition of `fromStep` / `fromStep` 的定义

English:
abbreviation fromStep
  signature: : step W Z ⟶ succ W Z
  body: Multicoequalizer.π (D₂.multispanIndex W Z) .unit

中文:
缩写 fromStep
  签名: : step W Z ⟶ succ W Z
  定义体: Multicoequalizer.π (D₂.multispanIndex W Z) .unit

Depends on / 依赖: Multicoequalizer, multispanIndex
-/
noncomputable abbrev fromStep : step W Z ⟶ succ W Z :=
  Multicoequalizer.π (D₂.multispanIndex W Z) .unit

variable {W Z} in
@[reassoc]
/--
lemma `D₂.condition` / 引理 `D₂.condition`

English:
lemma D₂.condition
  statement: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

中文:
引理 D₂.condition
  结论: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

Depends on / 依赖: Arrow.mk, Multicoequalizer, Multicoequalizer.condition, condition, multispanIndex
-/
lemma D₂.condition {X Y : C} (f : X ⟶ Y) (hf : W f)
    {g₁ g₂ : Y ⟶ step W Z} (h : f ≫ g₁ = f ≫ g₂) :
      g₁ ≫ fromStep W Z = g₂ ≫ fromStep W Z :=
  Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

/--
Definition of `toSucc` / `toSucc` 的定义

English:
abbreviation toSucc
  signature: : Z ⟶ succ W Z
  body: toStep W Z ≫ fromStep W Z

中文:
缩写 toSucc
  签名: : Z ⟶ succ W Z
  定义体: toStep W Z ≫ fromStep W Z

Depends on / 依赖: fromStep, toStep
-/
noncomputable abbrev toSucc : Z ⟶ succ W Z := toStep W Z ≫ fromStep W Z

variable {W Z} in
/--
lemma `toSucc_injectivity` / 引理 `toSucc_injectivity`

English:
lemma toSucc_injectivity
  statement: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

中文:
引理 toSucc_injectivity
  结论: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

Depends on / 依赖: condition, reassoc_of, toStep
-/
lemma toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f)
    (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z := by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

set_option backward.isDefEq.respectTransparency false in
variable {W Z} in
/--
lemma `toSucc_surjectivity` / 引理 `toSucc_surjectivity`

English:
lemma toSucc_surjectivity
  given: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  proof: ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

中文:
引理 toSucc_surjectivity
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z)
  证明: ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

Depends on / 依赖: condition_assoc, fromStep, pushout, pushout.condition_assoc, pushout.inl
-/
lemma toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    exists (g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z :=
  ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocal_isLocal_toSucc` / 引理 `isLocal_isLocal_toSucc`

English:
lemma isLocal_isLocal_toSucc
  proof: by
  refine fun T hT => ⟨fun φ₁ φ₂ h => ?_, fun g => ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) => (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ => pushout.desc (Sigma.desc f) g)
      (fun d => (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

中文:
引理 isLocal_isLocal_toSucc
  证明: by
  refine fun T hT => ⟨fun φ₁ φ₂ h => ?_, fun g => ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) => (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ => pushout.desc (Sigma.desc f) g)
      (fun d => (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

Depends on / 依赖: Category, Category.assoc, Multicoequalizer, Multicoequalizer.desc, Sigma.desc, condition_assoc, pushout, pushout.condition_assoc, pushout.desc, reassoc_of
-/
lemma isLocal_isLocal_toSucc :
    W.isLocal.isLocal (toSucc W Z) := by
  refine fun T hT => ⟨fun φ₁ φ₂ h => ?_, fun g => ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) => (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ => pushout.desc (Sigma.desc f) g)
      (fun d => (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_toSucc_iff` / 引理 `isIso_toSucc_iff`

English:
lemma isIso_toSucc_iff
  proof: by
  refine ⟨fun _ X Y f hf => ?_, fun hZ => ?_⟩
  · refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (isLocal_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition_assoc]; rw [reassoc_of% hf]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition]
    · simp [reassoc_of% hf]

中文:
引理 isIso_toSucc_iff
  证明: by
  refine ⟨fun _ X Y f hf => ?_, fun hZ => ?_⟩
  · refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (isLocal_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition_assoc]; rw [reassoc_of% hf]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition]
    · simp [reassoc_of% hf]

Depends on / 依赖: Category, Category.assoc, IsIso.hom_inv_id, cancel_mono, condition, condition_assoc, fromStep, hom_inv_id, isLocal_isLocal_toSucc, pushout, pushout.condition_assoc, pushout.inl, reassoc_of, toStep, toSucc
-/
lemma isIso_toSucc_iff :
    IsIso (toSucc W Z) ↔ W.isLocal Z := by
  refine ⟨fun _ X Y f hf => ?_, fun hZ => ?_⟩
  · refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (isLocal_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition_assoc]; rw [reassoc_of% hf]; rw [← D₁.ι_comp_t_assoc]; rw [pushout.condition]
    · simp [reassoc_of% hf]

end

open SmallObject

variable [HasPushouts C]
  [forall Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [forall Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [forall Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

/--
Definition of `succStruct` / `succStruct` 的定义

English:
definition succStruct
  signature: (Z₀ : C)
  body: Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

中文:
定义 succStruct
  签名: (Z₀ : C)
  定义体: Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z
-/
noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

variable (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
  [HasIterationOfShape κ.ord.ToType C]

/--
Definition of `reflectionObj` / `reflectionObj` 的定义

English:
definition reflectionObj
  signature: : C
  body: (succStruct W Z).iteration κ.ord.ToType

中文:
定义 reflectionObj
  签名: : C
  定义体: (succStruct W Z).iteration κ.ord.ToType

Depends on / 依赖: ToType, iteration, ord.ToType, succStruct
-/
noncomputable def reflectionObj : C := (succStruct W Z).iteration κ.ord.ToType

/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: : Z ⟶ reflectionObj W Z κ
  body: (succStruct W Z).ιIteration κ.ord.ToType

中文:
定义 reflection
  签名: : Z ⟶ reflectionObj W Z κ
  定义体: (succStruct W Z).ιIteration κ.ord.ToType

Depends on / 依赖: ToType, ord.ToType, succStruct
-/
noncomputable def reflection : Z ⟶ reflectionObj W Z κ :=
  (succStruct W Z).ιIteration κ.ord.ToType

/--
Definition of `transfiniteCompositionOfShapeReflection` / `transfiniteCompositionOfShapeReflection` 的定义

English:
definition transfiniteCompositionOfShapeReflection
  signature: :
  body: ((succStruct W Z).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE (by
    rintro Z₀ _ _ ⟨_⟩
    exact isLocal_isLocal_toSucc W Z₀)

中文:
定义 transfiniteCompositionOfShapeReflection
  签名: :
  定义体: ((succStruct W Z).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE (by
    rintro Z₀ _ _ ⟨_⟩
    exact isLocal_isLocal_toSucc W Z₀)

Depends on / 依赖: ToType, isLocal_isLocal_toSucc, ord.ToType, succStruct
-/
noncomputable def transfiniteCompositionOfShapeReflection :
    W.isLocal.isLocal.TransfiniteCompositionOfShape κ.ord.ToType
      (reflection W Z κ) :=
  ((succStruct W Z).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE (by
    rintro Z₀ _ _ ⟨_⟩
    exact isLocal_isLocal_toSucc W Z₀)

/--
Definition of `iteration` / `iteration` 的定义

English:
abbreviation iteration
  signature: : κ.ord.ToType ⥤ C
  body: (transfiniteCompositionOfShapeReflection W Z κ).F

中文:
缩写 iteration
  签名: : κ.ord.ToType ⥤ C
  定义体: (transfiniteCompositionOfShapeReflection W Z κ).F

Depends on / 依赖: transfiniteCompositionOfShapeReflection
-/
noncomputable abbrev iteration : κ.ord.ToType ⥤ C :=
  (transfiniteCompositionOfShapeReflection W Z κ).F

section

variable [Fact κ.IsRegular]

/--
Definition of `iterationObjSuccIso` / `iterationObjSuccIso` 的定义

English:
definition iterationObjSuccIso
  signature: (j : κ.ord.ToType)
  body: (succStruct W Z).iterationFunctorObjSuccIso j (by
      have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
      exact not_isMax j)

@[reassoc]

中文:
定义 iterationObjSuccIso
  签名: (j : κ.ord.ToType)
  定义体: (succStruct W Z).iterationFunctorObjSuccIso j (by
      have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
      exact not_isMax j)

@[reassoc]

Depends on / 依赖: Cardinal, Cardinal.noMaxOrder, Fact.elim, IsRegular, aleph0_le, iterationFunctorObjSuccIso, noMaxOrder, not_isMax, succStruct
-/
noncomputable def iterationObjSuccIso (j : κ.ord.ToType) :
  (iteration W Z κ).obj (Order.succ j) ≅ succ W ((iteration W Z κ).obj j) :=
    (succStruct W Z).iterationFunctorObjSuccIso j (by
      have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
      exact not_isMax j)

@[reassoc]
/--
lemma `iteration_map_succ` / 引理 `iteration_map_succ`

English:
lemma iteration_map_succ
  given: (j : κ.ord.ToType)
  proof: (succStruct W Z).iterationFunctor_map_succ _ _

中文:
引理 iteration_map_succ
  条件: (j : κ.ord.ToType)
  证明: (succStruct W Z).iterationFunctor_map_succ _ _

Depends on / 依赖: iterationFunctor_map_succ, succStruct
-/
lemma iteration_map_succ (j : κ.ord.ToType) :
    (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      toSucc W _ ≫ (iterationObjSuccIso W Z κ j).inv :=
  (succStruct W Z).iterationFunctor_map_succ _ _

variable {κ W Z} in
/--
lemma `iteration_map_succ_injectivity` / 引理 `iteration_map_succ_injectivity`

English:
lemma iteration_map_succ_injectivity
  statement: {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
  proof: by
  simp [iteration_map_succ, reassoc_of% (toSucc_injectivity f hf _ _ hg)]

中文:
引理 iteration_map_succ_injectivity
  结论: {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
  证明: by
  simp [iteration_map_succ, reassoc_of% (toSucc_injectivity f hf _ _ hg)]

Depends on / 依赖: iteration_map_succ, reassoc_of, toSucc_injectivity
-/
lemma iteration_map_succ_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g₁ g₂ : Y ⟶ (iteration W Z κ).obj j) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      g₂ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp [iteration_map_succ, reassoc_of% (toSucc_injectivity f hf _ _ hg)]

variable {κ W Z} in
/--
lemma `iteration_map_succ_surjectivity` / 引理 `iteration_map_succ_surjectivity`

English:
lemma iteration_map_succ_surjectivity
  statement: {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
  proof: by
  simp only [iteration_map_succ]
  obtain ⟨g', hg'⟩ := toSucc_surjectivity f hf g
  exact ⟨g' ≫ (iterationObjSuccIso W Z κ j).inv, by simp [reassoc_of% hg']⟩

中文:
引理 iteration_map_succ_surjectivity
  结论: {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
  证明: by
  simp only [iteration_map_succ]
  obtain ⟨g', hg'⟩ := toSucc_surjectivity f hf g
  exact ⟨g' ≫ (iterationObjSuccIso W Z κ j).inv, by simp [reassoc_of% hg']⟩

Depends on / 依赖: iterationObjSuccIso, iteration_map_succ, reassoc_of, toSucc_surjectivity
-/
lemma iteration_map_succ_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g : X ⟶ (iteration W Z κ).obj j) :
    exists (g' : Y ⟶ (iteration W Z κ).obj (Order.succ j)),
      f ≫ g' = g ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp only [iteration_map_succ]
  obtain ⟨g', hg'⟩ := toSucc_surjectivity f hf g
  exact ⟨g' ≫ (iterationObjSuccIso W Z κ j).inv, by simp [reassoc_of% hg']⟩

end

/--
lemma `isLocal_isLocal_reflection` / 引理 `isLocal_isLocal_reflection`

English:
lemma isLocal_isLocal_reflection
  proof: W.isLocal.isLocal.transfiniteCompositionsOfShape_le κ.ord.ToType _
    ⟨transfiniteCompositionOfShapeReflection W Z κ⟩

中文:
引理 isLocal_isLocal_reflection
  证明: W.isLocal.isLocal.transfiniteCompositionsOfShape_le κ.ord.ToType _
    ⟨transfiniteCompositionOfShapeReflection W Z κ⟩

Depends on / 依赖: ToType, W.isLocal.isLocal.transfiniteCompositionsOfShape_le, isLocal, ord.ToType, transfiniteCompositionOfShapeReflection, transfiniteCompositionsOfShape_le
-/
lemma isLocal_isLocal_reflection :
     W.isLocal.isLocal (reflection W Z κ) :=
  W.isLocal.isLocal.transfiniteCompositionsOfShape_le κ.ord.ToType _
    ⟨transfiniteCompositionOfShapeReflection W Z κ⟩

variable {W} {κ} [Fact κ.IsRegular]
  (hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)

include hW

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocal_reflectionObj` / 引理 `isLocal_reflectionObj`

English:
lemma isLocal_reflectionObj
  proof: by
  let H := transfiniteCompositionOfShapeReflection W Z κ
  intro X Y f hf
  obtain ⟨_, _⟩ := hW f hf
  refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
  · obtain ⟨j, g₁, g₂, rfl, rfl⟩ :
      exists (j : κ.ord.ToType) (g₁' g₂' : Y ⟶ H.F.obj j), g₁' ≫ H.incl.app j = g₁ ∧
        g₂' ≫ H.incl.app j = g₂ := by
      obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₂
      exact ⟨max j₁ j₂, g₁ ≫ H.F.map (homOfLE (le_max_left _ _)),
        g₂ ≫ H.F.map (homOfLE (le_max_right _ _)), by simp⟩
    dsimp at h
    obtain ⟨k, u, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ H.isColimit
      (f ≫ g₁) (f ≫ g₂) (by simpa)
    have hg := iteration_map_succ_injectivity f hf
      (g₁ ≫ H.F.map u) (g₂ ≫ H.F.map u) (by simpa using hk)
    simp only [homOfLE_leOfHom, Category.assoc] at hg
    have := H.incl.naturality (u ≫ homOfLE (Order.le_succ k))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    simp only [← this, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hg]
  · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g
    obtain ⟨g', hg'⟩ := iteration_map_succ_surjectivity f hf g
    exact ⟨g' ≫ H.incl.app (Order.succ j), by simp [reassoc_of% hg']⟩

中文:
引理 isLocal_reflectionObj
  证明: by
  let H := transfiniteCompositionOfShapeReflection W Z κ
  intro X Y f hf
  obtain ⟨_, _⟩ := hW f hf
  refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
  · obtain ⟨j, g₁, g₂, rfl, rfl⟩ :
      exists (j : κ.ord.ToType) (g₁' g₂' : Y ⟶ H.F.obj j), g₁' ≫ H.incl.app j = g₁ ∧
        g₂' ≫ H.incl.app j = g₂ := by
      obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₂
      exact ⟨max j₁ j₂, g₁ ≫ H.F.map (homOfLE (le_max_left _ _)),
        g₂ ≫ H.F.map (homOfLE (le_max_right _ _)), by simp⟩
    dsimp at h
    obtain ⟨k, u, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ H.isColimit
      (f ≫ g₁) (f ≫ g₂) (by simpa)
    have hg := iteration_map_succ_injectivity f hf
      (g₁ ≫ H.F.map u) (g₂ ≫ H.F.map u) (by simpa using hk)
    simp only [homOfLE_leOfHom, Category.assoc] at hg
    have := H.incl.naturality (u ≫ homOfLE (Order.le_succ k))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    simp only [← this, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hg]
  · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g
    obtain ⟨g', hg'⟩ := iteration_map_succ_surjectivity f hf g
    exact ⟨g' ≫ H.incl.app (Order.succ j), by simp [reassoc_of% hg']⟩

Depends on / 依赖: H.F.map, H.F.obj, H.incl.app, H.isColimit, IsCardinalPresentable, IsCardinalPresentable.exists_hom_of_isColimit, ToType, exists_hom_of_isColimit, homOfLE, isColimit, le_ma, ord.ToType, transfiniteCompositionOfShapeReflection
-/
lemma isLocal_reflectionObj :
    W.isLocal (reflectionObj W Z κ) := by
  let H := transfiniteCompositionOfShapeReflection W Z κ
  intro X Y f hf
  obtain ⟨_, _⟩ := hW f hf
  refine ⟨fun g₁ g₂ h => ?_, fun g => ?_⟩
  · obtain ⟨j, g₁, g₂, rfl, rfl⟩ :
      exists (j : κ.ord.ToType) (g₁' g₂' : Y ⟶ H.F.obj j), g₁' ≫ H.incl.app j = g₁ ∧
        g₂' ≫ H.incl.app j = g₂ := by
      obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₂
      exact ⟨max j₁ j₂, g₁ ≫ H.F.map (homOfLE (le_max_left _ _)),
        g₂ ≫ H.F.map (homOfLE (le_max_right _ _)), by simp⟩
    dsimp at h
    obtain ⟨k, u, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ H.isColimit
      (f ≫ g₁) (f ≫ g₂) (by simpa)
    have hg := iteration_map_succ_injectivity f hf
      (g₁ ≫ H.F.map u) (g₂ ≫ H.F.map u) (by simpa using hk)
    simp only [homOfLE_leOfHom, Category.assoc] at hg
    have := H.incl.naturality (u ≫ homOfLE (Order.le_succ k))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    simp only [← this, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hg]
  · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g
    obtain ⟨g', hg'⟩ := iteration_map_succ_surjectivity f hf g
    exact ⟨g' ≫ H.incl.app (Order.succ j), by simp [reassoc_of% hg']⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `corepresentableBy` / `corepresentableBy` 的定义

English:
definition corepresentableBy
  signature: :
  body: (ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Equiv.ofBijective _ (isLocal_isLocal_reflection W Z κ _ A.2))

中文:
定义 corepresentableBy
  签名: :
  定义体: (ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Equiv.ofBijective _ (isLocal_isLocal_reflection W Z κ _ A.2))

Depends on / 依赖: A.biUnion, Equiv.ofBijective, FinsetCoe, FinsetCoe.fintype, ObjectProperty, ObjectProperty.fullyFaithful, R.image, SetRel, SetRel.image, biUnion, fintype, homEquiv, homEquiv.trans, isLocal_isLocal_reflection, ofBijective, toFinset
-/
noncomputable def corepresentableBy :
  (W.isLocal.ι ⋙ coyoneda.obj (op Z)).CorepresentableBy
    ⟨_, isLocal_reflectionObj Z hW⟩ where
  homEquiv {A} :=
    (ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Equiv.ofBijective _ (isLocal_isLocal_reflection W Z κ _ A.2))

variable (W κ)

/--
lemma `isRightAdjoint_ι` / 引理 `isRightAdjoint_ι`

English:
lemma isRightAdjoint_ι
  proof: by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  ext Z
  simpa using! (corepresentableBy Z hW).isCorepresentable

中文:
引理 isRightAdjoint_ι
  证明: by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  ext Z
  simpa using! (corepresentableBy Z hW).isCorepresentable

Depends on / 依赖: Functor, Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top, corepresentableBy, isCorepresentable, isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top
-/
lemma isRightAdjoint_ι :
    W.isLocal.ι.IsRightAdjoint := by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  ext Z
  simpa using! (corepresentableBy Z hW).isCorepresentable

end OrthogonalReflection

namespace MorphismProperty

open OrthogonalReflection in
/--
lemma `isRightAdjoint_ι_isLocal` / 引理 `isRightAdjoint_ι_isLocal`

English:
lemma isRightAdjoint_ι_isLocal
  proof: by
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero Fact.out
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have := D₁.hasCoproductsOfShape.{w} W
  have := D₂.hasColimitsOfShape.{w} W
  exact isRightAdjoint_ι W κ hW

中文:
引理 isRightAdjoint_ι_isLocal
  证明: by
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero Fact.out
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have := D₁.hasCoproductsOfShape.{w} W
  have := D₂.hasColimitsOfShape.{w} W
  exact isRightAdjoint_ι W κ hW

Depends on / 依赖: Cardinal, Cardinal.IsRegular.ne_zero, Fact.out, IsRegular, Nonempty, ToType, WellFoundedLT, WellFoundedLT.toOrderBot, hasColimitsOfShape, hasCoproductsOfShape, ne_zero, ord.ToType, toOrderBot
-/
lemma isRightAdjoint_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]
    (hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)
    [HasColimitsOfSize.{w, w} C] :
    W.isLocal.ι.IsRightAdjoint := by
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero Fact.out
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have := D₁.hasCoproductsOfShape.{w} W
  have := D₂.hasColimitsOfShape.{w} W
  exact isRightAdjoint_ι W κ hW

/--
lemma `isLocallyPresentable_isLocal` / 引理 `isLocallyPresentable_isLocal`

English:
lemma isLocallyPresentable_isLocal
  proof: by
    have := isRightAdjoint_ι_isLocal W κ hW
    have := MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW
    exact (Adjunction.ofIsRightAdjoint W.isLocal.ι).isCardinalLocallyPresentable κ

中文:
引理 isLocallyPresentable_isLocal
  证明: by
    have := isRightAdjoint_ι_isLocal W κ hW
    have := MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW
    exact (Adjunction.ofIsRightAdjoint W.isLocal.ι).isCardinalLocallyPresentable κ

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, MorphismProperty, MorphismProperty.isCardinalAccessible_, W.isLocal, isCardinalLocallyPresentable, isLocal, ofIsRightAdjoint
-/
lemma isLocallyPresentable_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ]
    [MorphismProperty.IsSmall.{w} W]
    (hW : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f -> IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
  IsCardinalLocallyPresentable W.isLocal.FullSubcategory κ := by
    have := isRightAdjoint_ι_isLocal W κ hW
    have := MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW
    exact (Adjunction.ofIsRightAdjoint W.isLocal.ι).isCardinalLocallyPresentable κ

end MorphismProperty

end CategoryTheory
