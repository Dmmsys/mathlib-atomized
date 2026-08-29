/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.GuitartExact.Opposite

/-!
# Derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a localizer morphism, i.e. `W₁ : MorphismProperty C₁`,
`W₂ : MorphismProperty C₂`, and `Φ.functor : C₁ ⥤ C₂` is a functor which maps `W₁` to `W₂`.
Following the definition introduced by Bruno Kahn and Georges Maltsiniotis in
[Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008],
we say that `Φ` is a right derivability structure if `Φ` has right resolutions and
the following 2-square is Guitart exact, where `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are
localization functors for `W₁` and `W₂`, and `F : D₁ ⥤ D₂` is the induced functor
on the localized categories:

```
    Φ.functor
  C₁ ⥤ C₂
  | |
L₁| | L₂
  v v
  D₁ ⥤ D₂
       F
```

## Implementation details

In the field `guitartExact'` of the structure `LocalizerMorphism.IsRightDerivabilityStructure`,
The condition that the square is Guitart exact is stated for the localization functors
of the constructed categories (`W₁.Q` and `W₂.Q`).
The lemma `LocalizerMorphism.isRightDerivabilityStructure_iff` shows that it does
not depend on the choice of the localization functors.

## TODO

* Construct the injective derivability structure in order to derive functor from
  the bounded below homotopy category in an abelian category with enough injectives
* Construct the projective derivability structure in order to derive functor from
  the bounded above homotopy category in an abelian category with enough projectives
* Construct the flat derivability structure on the bounded above homotopy category
  of categories of modules (and categories of sheaves of modules)
* Define the product derivability structure and formalize derived functors of
  functors in several variables

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

public section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Localization CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/--
Definition of `IsRightDerivabilityStructure` / `IsRightDerivabilityStructure` 的定义

English:
class IsRightDerivabilityStructure
  parameters: : Prop where
  axioms and operations (2):
    - hasRightResolutions : Φ.HasRightResolutions  [default: by infer_instance]
    - guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

中文:
类 IsRightDerivabilityStructure
  参数: : 命题 where
  公理与运算 (2 个):
    - hasRightResolutions : Φ.HasRightResolutions  [默认: by infer_instance]
    - guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

Depends on / 依赖: infer_instance
-/
class IsRightDerivabilityStructure : Prop where
  hasRightResolutions : Φ.HasRightResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isRightDerivabilityStructure` instead,
  see also the lemma `isRightDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom

attribute [instance] IsRightDerivabilityStructure.hasRightResolutions
  IsRightDerivabilityStructure.guitartExact'

variable {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] (F : D₁ ⥤ D₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isRightDerivabilityStructure_iff` / 引理 `isRightDerivabilityStructure_iff`

English:
lemma isRightDerivabilityStructure_iff
  given: [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
  proof: by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L

中文:
引理 isRightDerivabilityStructure_iff
  条件: [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
  证明: by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L

Depends on / 依赖: GuitartExact, IsRightDerivabilityStructure, Localization, Localization.uniq, TwoSquare, TwoSquare.GuitartExact, associator, catCommSq, compUniqFunctor, functor, guitartExact, h.guitartExact
-/
lemma isRightDerivabilityStructure_iff [Φ.HasRightResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsRightDerivabilityStructure ↔ TwoSquare.GuitartExact e.hom := by
  have : Φ.IsRightDerivabilityStructure ↔
      TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).hom :=
    ⟨fun h => h.guitartExact', fun h => ⟨inferInstance, h⟩⟩
  rw [this]
  let e' := (Φ.catCommSq W₁.Q W₂.Q).iso
  let E₁ := Localization.uniq W₁.Q L₁ W₁
  let E₂ := Localization.uniq W₂.Q L₂ W₂
  let e₁ : W₁.Q ⋙ E₁.functor ≅ L₁ := compUniqFunctor W₁.Q L₁ W₁
  let e₂ : W₂.Q ⋙ E₂.functor ≅ L₂ := compUniqFunctor W₂.Q L₂ W₂
  let e'' : (Φ.functor ⋙ W₂.Q) ⋙ E₂.functor ≅ (W₁.Q ⋙ E₁.functor) ⋙ F :=
    associator _ _ _ ≪≫ isoWhiskerLeft _ e₂ ≪≫ e ≪≫ isoWhiskerRight e₁.symm F
  let e''' : Φ.localizedFunctor W₁.Q W₂.Q ⋙ E₂.functor ≅ E₁.functor ⋙ F :=
    liftNatIso W₁.Q W₁ _ _ _ _ e''
  have : TwoSquare.vComp' e'.hom e'''.hom e₁ e₂ = e.hom := by
    ext X₁
    rw [TwoSquare.vComp'_app]; rw [liftNatIso_hom]; rw [liftNatTrans_app]
    simp only [Functor.comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, whiskerLeft_app,
      whiskerRight_app, id_comp, assoc, e'']
    dsimp [Lifting.iso]
    rw [F.map_id]; rw [id_comp]; rw [← F.map_comp]; rw [Iso.inv_hom_id_app]; rw [F.map_id]; rw [comp_id]; rw [← Functor.map_comp_assoc]
    erw [show (CatCommSq.iso Φ.functor W₁.Q W₂.Q (localizedFunctor Φ W₁.Q W₂.Q)).hom =
      (Lifting.iso W₁.Q W₁ _ _).inv by rfl, Iso.inv_hom_id_app]
    simp
  rw [← TwoSquare.GuitartExact.vComp'_iff_of_equivalences e'.hom E₁ E₂ e''' e₁ e₂]; rw [this]

/--
Instance `guitartExact_of_isRightDerivabilityStructure'` / 实例 `guitartExact_of_isRightDerivabilityStructure'`

English:
instance guitartExact_of_isRightDerivabilityStructure'
  signature: [h : Φ.IsRightDerivabilityStructure]
  body: by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h

中文:
实例 guitartExact_of_isRightDerivabilityStructure'
  签名: [h : Φ.IsRightDerivabilityStructure]
  定义体: by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h

Depends on / 依赖: isRightDerivabilityStructure_iff
-/
instance guitartExact_of_isRightDerivabilityStructure' [h : Φ.IsRightDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.hom := by
  simpa only [Φ.isRightDerivabilityStructure_iff L₁ L₂ F e] using h

/--
Instance `guitartExact_of_isRightDerivabilityStructure` / 实例 `guitartExact_of_isRightDerivabilityStructure`

English:
instance guitartExact_of_isRightDerivabilityStructure
  signature: [Φ.IsRightDerivabilityStructure]
  body: guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _

中文:
实例 guitartExact_of_isRightDerivabilityStructure
  签名: [Φ.IsRightDerivabilityStructure]
  定义体: guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _

Depends on / 依赖: guitartExact_of_isRightDerivabilityStructure
-/
instance guitartExact_of_isRightDerivabilityStructure [Φ.IsRightDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).hom :=
  guitartExact_of_isRightDerivabilityStructure' _ _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.ContainsIdentities]
  signature: : (LocalizerMorphism.id W₁).HasRightResolutions
  body: fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

中文:
实例 [W₁.ContainsIdentities]
  签名: : (LocalizerMorphism.id W₁).HasRightResolutions
  定义体: fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

Depends on / 依赖: RightResolution, RightResolution.mk, id_mem
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasRightResolutions :=
  fun X₂ => ⟨RightResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.ContainsIdentities]
  signature: : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure
  body: by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

中文:
实例 [W₁.ContainsIdentities]
  签名: : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure
  定义体: by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

Depends on / 依赖: Iso.refl, Localization, LocalizerMorphism, LocalizerMorphism.id, TwoSquare, TwoSquare.guitartExact_id, guitartExact_id, isRightDerivabilityStructure_iff
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsRightDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isRightDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id W₁.Q

/--
Definition of `IsLeftDerivabilityStructure` / `IsLeftDerivabilityStructure` 的定义

English:
class IsLeftDerivabilityStructure
  parameters: : Prop where
  axioms and operations (2):
    - hasLeftResolutions : Φ.HasLeftResolutions  [default: by infer_instance]
    - guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv

中文:
类 IsLeftDerivabilityStructure
  参数: : 命题 where
  公理与运算 (2 个):
    - hasLeftResolutions : Φ.HasLeftResolutions  [默认: by infer_instance]
    - guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv

Depends on / 依赖: infer_instance
-/
class IsLeftDerivabilityStructure : Prop where
  hasLeftResolutions : Φ.HasLeftResolutions := by infer_instance
  /-- Do not use this field directly: use the more general
  `guitartExact_of_isLeftDerivabilityStructure` instead,
  see also the lemma `isLeftDerivabilityStructure_iff`. -/
  guitartExact' : TwoSquare.GuitartExact ((Φ.catCommSq W₁.Q W₂.Q).iso).inv

attribute [instance] IsLeftDerivabilityStructure.hasLeftResolutions
  IsLeftDerivabilityStructure.guitartExact'

/--
lemma `isLeftDerivabilityStructure_iff_op` / 引理 `isLeftDerivabilityStructure_iff_op`

English:
lemma isLeftDerivabilityStructure_iff_op
  proof: by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.hom ↔ TwoSquare.GuitartExact e.inv :=
    TwoSquare.guitartExact_op_iff _
  con

中文:
引理 isLeftDerivabilityStructure_iff_op
  证明: by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.hom ↔ TwoSquare.GuitartExact e.inv :=
    TwoSquare.guitartExact_op_iff _
  con

Depends on / 依赖: F.op, GuitartExact, HasLeftResolutions, NatIso, NatIso.op, Q.op, TwoSquare, TwoSquare.GuitartExact, TwoSquare.guitartExact_op_iff, catCommSq, e.inv, e.symm, functor, functor.op, guitartExact_op_iff, hasLeftResolutions_iff_op, infer_instance, isRightDerivabilityStructure_iff, localizedFunctor, op.isRightDerivabilityStructure_iff
-/
lemma isLeftDerivabilityStructure_iff_op :
    Φ.IsLeftDerivabilityStructure ↔
      Φ.op.IsRightDerivabilityStructure := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.hom ↔ TwoSquare.GuitartExact e.inv :=
    TwoSquare.guitartExact_op_iff _
  constructor
  · rintro ⟨_, _⟩
    rwa [Φ.op.isRightDerivabilityStructure_iff _ _ _ e', eq]
  · intro
    have : Φ.HasLeftResolutions := by
      rw [hasLeftResolutions_iff_op]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [← eq]
    exact Φ.op.guitartExact_of_isRightDerivabilityStructure' _ _ _ e'

/--
lemma `isLeftDerivabilityStructure_iff` / 引理 `isLeftDerivabilityStructure_iff`

English:
lemma isLeftDerivabilityStructure_iff
  given: [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
  proof: by
  rw [isLeftDerivabilityStructure_iff_op]; rw [Φ.op.isRightDerivabilityStructure_iff L₁.op L₂.op F.op (NatIso.op e.symm)]; rw [← TwoSquare.guitartExact_op_iff e.inv]
  rfl

中文:
引理 isLeftDerivabilityStructure_iff
  条件: [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F)
  证明: by
  rw [isLeftDerivabilityStructure_iff_op]; rw [Φ.op.isRightDerivabilityStructure_iff L₁.op L₂.op F.op (NatIso.op e.symm)]; rw [← TwoSquare.guitartExact_op_iff e.inv]
  rfl

Depends on / 依赖: F.op, NatIso, NatIso.op, TwoSquare, TwoSquare.guitartExact_op_iff, e.inv, e.symm, guitartExact_op_iff, isLeftDerivabilityStructure_iff_op, isRightDerivabilityStructure_iff, op.isRightDerivabilityStructure_iff
-/
lemma isLeftDerivabilityStructure_iff [Φ.HasLeftResolutions] (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) :
    Φ.IsLeftDerivabilityStructure ↔ TwoSquare.GuitartExact e.inv := by
  rw [isLeftDerivabilityStructure_iff_op]; rw [Φ.op.isRightDerivabilityStructure_iff L₁.op L₂.op F.op (NatIso.op e.symm)]; rw [← TwoSquare.guitartExact_op_iff e.inv]
  rfl

/--
Instance `guitartExact_of_isLeftDerivabilityStructure'` / 实例 `guitartExact_of_isLeftDerivabilityStructure'`

English:
instance guitartExact_of_isLeftDerivabilityStructure'
  signature: [h : Φ.IsLeftDerivabilityStructure]
  body: by
  simpa only [Φ.isLeftDerivabilityStructure_iff L₁ L₂ F e] using h

中文:
实例 guitartExact_of_isLeftDerivabilityStructure'
  签名: [h : Φ.IsLeftDerivabilityStructure]
  定义体: by
  simpa only [Φ.isLeftDerivabilityStructure_iff L₁ L₂ F e] using h

Depends on / 依赖: isLeftDerivabilityStructure_iff
-/
instance guitartExact_of_isLeftDerivabilityStructure' [h : Φ.IsLeftDerivabilityStructure]
    (e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ F) : TwoSquare.GuitartExact e.inv := by
  simpa only [Φ.isLeftDerivabilityStructure_iff L₁ L₂ F e] using h

/--
Instance `guitartExact_of_isLeftDerivabilityStructure` / 实例 `guitartExact_of_isLeftDerivabilityStructure`

English:
instance guitartExact_of_isLeftDerivabilityStructure
  signature: [Φ.IsLeftDerivabilityStructure]
  body: guitartExact_of_isLeftDerivabilityStructure' _ _ _ _ _

中文:
实例 guitartExact_of_isLeftDerivabilityStructure
  签名: [Φ.IsLeftDerivabilityStructure]
  定义体: guitartExact_of_isLeftDerivabilityStructure' _ _ _ _ _

Depends on / 依赖: guitartExact_of_isLeftDerivabilityStructure
-/
instance guitartExact_of_isLeftDerivabilityStructure [Φ.IsLeftDerivabilityStructure] :
    TwoSquare.GuitartExact ((Φ.catCommSq L₁ L₂).iso).inv :=
  guitartExact_of_isLeftDerivabilityStructure' _ _ _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.ContainsIdentities]
  signature: : (LocalizerMorphism.id W₁).HasLeftResolutions
  body: fun X₂ => ⟨LeftResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

中文:
实例 [W₁.ContainsIdentities]
  签名: : (LocalizerMorphism.id W₁).HasLeftResolutions
  定义体: fun X₂ => ⟨LeftResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

Depends on / 依赖: LeftResolution, LeftResolution.mk, id_mem
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).HasLeftResolutions :=
  fun X₂ => ⟨LeftResolution.mk (𝟙 X₂) (W₁.id_mem X₂)⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.ContainsIdentities]
  signature: : (LocalizerMorphism.id W₁).IsLeftDerivabilityStructure
  body: by
  rw [(LocalizerMorphism.id W₁).isLeftDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id' W₁.Q

中文:
实例 [W₁.ContainsIdentities]
  签名: : (LocalizerMorphism.id W₁).IsLeftDerivabilityStructure
  定义体: by
  rw [(LocalizerMorphism.id W₁).isLeftDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id' W₁.Q

Depends on / 依赖: Iso.refl, Localization, LocalizerMorphism, LocalizerMorphism.id, TwoSquare, TwoSquare.guitartExact_id, guitartExact_id, isLeftDerivabilityStructure_iff
-/
instance [W₁.ContainsIdentities] : (LocalizerMorphism.id W₁).IsLeftDerivabilityStructure := by
  rw [(LocalizerMorphism.id W₁).isLeftDerivabilityStructure_iff W₁.Q W₁.Q (𝟭 W₁.Localization)
    (Iso.refl _)]
  dsimp
  exact TwoSquare.guitartExact_id' W₁.Q

/--
lemma `isRightDerivabilityStructure_iff_op` / 引理 `isRightDerivabilityStructure_iff_op`

English:
lemma isRightDerivabilityStructure_iff_op
  proof: by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.inv ↔ TwoSquare.GuitartExact e.hom :=
    TwoSquare.guitartExact_op_iff _
  ref

中文:
引理 isRightDerivabilityStructure_iff_op
  证明: by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.inv ↔ TwoSquare.GuitartExact e.hom :=
    TwoSquare.guitartExact_op_iff _
  ref

Depends on / 依赖: F.op, GuitartExact, HasRightResolutions, NatIso, NatIso.op, Q.op, TwoSquare, TwoSquare.GuitartExact, TwoSquare.guitartExact_op_iff, catCommSq, e.hom, e.symm, functor, functor.op, guitartExact_op_iff, hasRightResolutions_iff_op, infer_instance, isLeftDerivabilityStructure_iff, localizedFunctor, op.isLeftDerivabilityStructure_iff
-/
lemma isRightDerivabilityStructure_iff_op :
    Φ.IsRightDerivabilityStructure ↔
      Φ.op.IsLeftDerivabilityStructure := by
  let F := Φ.localizedFunctor W₁.Q W₂.Q
  let e : Φ.functor ⋙ W₂.Q ≅ W₁.Q ⋙ F := (Φ.catCommSq W₁.Q W₂.Q).iso
  let e' : Φ.functor.op ⋙ W₂.Q.op ≅ W₁.Q.op ⋙ F.op := NatIso.op e.symm
  have eq : TwoSquare.GuitartExact e'.inv ↔ TwoSquare.GuitartExact e.hom :=
    TwoSquare.guitartExact_op_iff _
  refine ⟨fun ⟨_, _⟩ => ?_, fun _ => ?_⟩
  · simpa only [Φ.op.isLeftDerivabilityStructure_iff _ _ _ e', eq]
  · have : Φ.HasRightResolutions := by
      rw [hasRightResolutions_iff_op]
      infer_instance
    refine ⟨inferInstance, ?_⟩
    rw [← eq]
    exact Φ.op.guitartExact_of_isLeftDerivabilityStructure' _ _ _ e'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsLeftDerivabilityStructure]
  signature: : Φ.op.IsRightDerivabilityStructure
  body: by
  rwa [← isLeftDerivabilityStructure_iff_op]

中文:
实例 [Φ.IsLeftDerivabilityStructure]
  签名: : Φ.op.IsRightDerivabilityStructure
  定义体: by
  rwa [← isLeftDerivabilityStructure_iff_op]

Depends on / 依赖: isLeftDerivabilityStructure_iff_op
-/
instance [Φ.IsLeftDerivabilityStructure] : Φ.op.IsRightDerivabilityStructure := by
  rwa [← isLeftDerivabilityStructure_iff_op]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.IsRightDerivabilityStructure]
  signature: : Φ.op.IsLeftDerivabilityStructure
  body: by
  rwa [← isRightDerivabilityStructure_iff_op]

中文:
实例 [Φ.IsRightDerivabilityStructure]
  签名: : Φ.op.IsLeftDerivabilityStructure
  定义体: by
  rwa [← isRightDerivabilityStructure_iff_op]

Depends on / 依赖: isRightDerivabilityStructure_iff_op
-/
instance [Φ.IsRightDerivabilityStructure] : Φ.op.IsLeftDerivabilityStructure := by
  rwa [← isRightDerivabilityStructure_iff_op]

end LocalizerMorphism

end CategoryTheory
