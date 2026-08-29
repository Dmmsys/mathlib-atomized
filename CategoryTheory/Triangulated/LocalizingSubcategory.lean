/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Localizing subcategories

Let `C` be a pretriangulated category. If `A` and `B` are triangulated
subcategories of `C`, we define predicates (typeclasses
`IsVerdierRightLocalizing` and `IsVerdierLeftLocalizing`)
saying that `A` is right `B`-localizing (or left `B`-localizing).
When `B` is closed under isomorphisms, we show that this implies that
the functor from the Verdier quotient `A/(A ⊓ B)` to `C/B` is fully
faithful.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*,
  Proposition 2.3.5, Chapitre II][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Opposite

namespace ObjectProperty

variable {C D D₁ D₂ : Type*} [Category* C] [Category* D] [Category* D₁] [Category* D₂]

/--
Definition of `IsVerdierRightLocalizing` / `IsVerdierRightLocalizing` 的定义

English:
class IsVerdierRightLocalizing
  parameters: (A B : ObjectProperty C)
  axioms and operations (1):
    - fac({X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y)) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

中文:
类 IsVerdierRightLocalizing
  参数: (A B : Object命题erty C)
  公理与运算 (1 个):
    - fac({X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y)) : 存在 (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f
-/
class IsVerdierRightLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y) :
    exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

/--
Definition of `IsVerdierLeftLocalizing` / `IsVerdierLeftLocalizing` 的定义

English:
class IsVerdierLeftLocalizing
  parameters: (A B : ObjectProperty C)
  axioms and operations (1):
    - fac({X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y)) : exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

中文:
类 IsVerdierLeftLocalizing
  参数: (A B : Object命题erty C)
  公理与运算 (1 个):
    - fac({X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y)) : 存在 (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f
-/
class IsVerdierLeftLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y) :
    exists (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

instance (A B : ObjectProperty C) [A.IsVerdierLeftLocalizing B] :
    A.op.IsVerdierRightLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ :=
      IsVerdierLeftLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierLeftLocalizing B] :
    A.unop.IsVerdierRightLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierLeftLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

instance (A B : ObjectProperty C) [A.IsVerdierRightLocalizing B] :
    A.op.IsVerdierLeftLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩

instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierRightLocalizing B] :
    A.unop.IsVerdierLeftLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

variable (A B : ObjectProperty C)

/--
lemma `isVerdierLeftLocalizing_op_iff` / 引理 `isVerdierLeftLocalizing_op_iff`

English:
lemma isVerdierLeftLocalizing_op_iff
  proof: ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierRightLocalizing B.op.unop),
    fun _ => inferInstance⟩

中文:
引理 isVerdierLeftLocalizing_op_iff
  证明: ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierRightLocalizing B.op.unop),
    fun _ => inferInstance⟩

Depends on / 依赖: A.op.unop.IsVerdierRightLocalizing, B.op.unop, IsVerdierRightLocalizing
-/
lemma isVerdierLeftLocalizing_op_iff :
    A.op.IsVerdierLeftLocalizing B.op ↔ A.IsVerdierRightLocalizing B :=
  ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierRightLocalizing B.op.unop),
    fun _ => inferInstance⟩

/--
lemma `isVerdierRightLocalizing_op_iff` / 引理 `isVerdierRightLocalizing_op_iff`

English:
lemma isVerdierRightLocalizing_op_iff
  proof: ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierLeftLocalizing B.op.unop),
    fun _ => inferInstance⟩

中文:
引理 isVerdierRightLocalizing_op_iff
  证明: ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierLeftLocalizing B.op.unop),
    fun _ => inferInstance⟩

Depends on / 依赖: A.op.unop.IsVerdierLeftLocalizing, B.op.unop, IsVerdierLeftLocalizing
-/
lemma isVerdierRightLocalizing_op_iff :
    A.op.IsVerdierRightLocalizing B.op ↔ A.IsVerdierLeftLocalizing B :=
  ⟨fun _ => inferInstanceAs (A.op.unop.IsVerdierLeftLocalizing B.op.unop),
    fun _ => inferInstance⟩

variable [HasZeroObject C] [HasShift C Int] [Preadditive C]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isVerdierRightLocalizing_iff` / 引理 `isVerdierRightLocalizing_iff`

English:
lemma isVerdierRightLocalizing_iff
  statement: [A.IsTriangulated] [B.IsTriangulated]
  proof: by
  refine ⟨fun _ X Y s hX hs => ?_, fun hA => ⟨fun {X Y} f hX hY => ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
   

中文:
引理 isVerdierRightLocalizing_iff
  结论: [A.IsTriangulated] [B.IsTriangulated]
  证明: by
  refine ⟨fun _ X Y s hX hs => ?_, fun hA => ⟨fun {X Y} f hX hY => ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
   

Depends on / 依赖: A.distinguished_cocone_triangle, IsVerdierRightLocalizing, IsVerdierRightLocalizing.fac, ObjectProperty, ObjectProperty.trW_iff, Pretriangulated, Pretriangulated.complete_distinguished_triangle_morphism, cat_disch, complete_distinguished_triangle_morphism, distinguished_cocone_triangle, trW_iff
-/
lemma isVerdierRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierRightLocalizing B ↔
      forall ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A X) (_ : B.trW s),
        exists (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' := by
  refine ⟨fun _ X Y s hX hs => ?_, fun hA => ⟨fun {X Y} f hX hY => ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
    obtain ⟨g, hg, _⟩ := Pretriangulated.complete_distinguished_triangle_morphism _ _ hT hT'
      c (𝟙 _) (by cat_disch)
    refine ⟨U, e, g, hU, ?_, by cat_disch⟩
    rw [ObjectProperty.trW_iff']
    exact ⟨_, _, _, hT', h₁, h₂⟩
  · obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    have hs : B.trW s := by
      rw [trW_iff']
      exact ⟨_, _, _, hT, hX⟩
    obtain ⟨W, s', g, hW, hs', fac⟩ := hA s hY hs
    obtain ⟨U, hU, a, c, hT'⟩ := A.distinguished_cocone_triangle₁ s' hY hW
    obtain ⟨t, ht, ht'⟩ :=
      complete_distinguished_triangle_morphism₁ _ _ hT hT' (𝟙 Y) g (by cat_disch)
    exact ⟨U, t, a, hU, (B.trW_iff_of_distinguished' _ hT').1 (trW_monotone (by simp) _ hs'),
      by cat_disch⟩

variable {A B} in
/--
lemma `IsVerdierRightLocalizing.fac'` / 引理 `IsVerdierRightLocalizing.fac'`

English:
lemma IsVerdierRightLocalizing.fac'
  proof: (isVerdierRightLocalizing_iff A B).1 inferInstance s hX hs

中文:
引理 IsVerdierRightLocalizing.fac'
  证明: (isVerdierRightLocalizing_iff A B).1 inferInstance s hX hs

Depends on / 依赖: isVerdierRightLocalizing_iff
-/
lemma IsVerdierRightLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierRightLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hX : A X) (hs : B.trW s) :
    exists (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' :=
  (isVerdierRightLocalizing_iff A B).1 inferInstance s hX hs

/--
lemma `isVerdierLeftLocalizing_iff` / 引理 `isVerdierLeftLocalizing_iff`

English:
lemma isVerdierLeftLocalizing_iff
  statement: [A.IsTriangulated] [B.IsTriangulated]
  proof: by
  rw [← isVerdierRightLocalizing_op_iff]; rw [isVerdierRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs => ?_, fun hA X Y s hX hs => ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain

中文:
引理 isVerdierLeftLocalizing_iff
  结论: [A.IsTriangulated] [B.IsTriangulated]
  证明: by
  rw [← isVerdierRightLocalizing_op_iff]; rw [isVerdierRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs => ?_, fun hA X Y s hX hs => ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain

Depends on / 依赖: b.op, b.unop, cat_disch, isVerdierRightLocalizing_iff, isVerdierRightLocalizing_op_iff, s.op, s.unop, trW_of_op, trW_of_unop, trW_op_iff
-/
lemma isVerdierLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierLeftLocalizing B ↔
      forall ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A Y) (_ : B.trW s),
        exists (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' := by
  rw [← isVerdierRightLocalizing_op_iff]; rw [isVerdierRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs => ?_, fun hA X Y s hX hs => ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.unop hX (trW_of_op _ hs)
    exact ⟨_, s'.op, b.op, hZ', trW_of_unop _ hs', by cat_disch⟩

variable {A B} in
/--
lemma `IsVerdierLeftLocalizing.fac'` / 引理 `IsVerdierLeftLocalizing.fac'`

English:
lemma IsVerdierLeftLocalizing.fac'
  proof: (isVerdierLeftLocalizing_iff A B).1 inferInstance s hY hs

中文:
引理 IsVerdierLeftLocalizing.fac'
  证明: (isVerdierLeftLocalizing_iff A B).1 inferInstance s hY hs

Depends on / 依赖: isVerdierLeftLocalizing_iff
-/
lemma IsVerdierLeftLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierLeftLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hY : A Y) (hs : B.trW s) :
    exists (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' :=
  (isVerdierLeftLocalizing_iff A B).1 inferInstance s hY hs

/-- If `A` is a triangulated subcategory of a pretriangulated category `C`,
and `B : ObjectProperty C`, this is the inclusion functor
`A.ι : A.FullSubcategory ⥤ C`, considered as a localizer morphism,
where `C` is equipped with the property of morphisms `B.trW`
and `A.FullSubcategory` with the property of morphisms `(B.inverseImage A.ι).trW`. -/
@[instance_reducible]
/--
Definition of `triangulatedLocalizerMorphism` / `triangulatedLocalizerMorphism` 的定义

English:
definition triangulatedLocalizerMorphism
  signature: [A.IsTriangulated]
  body: A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩

中文:
定义 triangulatedLocalizerMorphism
  签名: [A.IsTriangulated]
  定义体: A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩
-/
def triangulatedLocalizerMorphism [A.IsTriangulated] :
    LocalizerMorphism (B.inverseImage A.ι).trW B.trW where
  functor := A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [A.IsTriangulated]
  signature: :
  body: inferInstanceAs (A.ι.CommShift Int)

中文:
实例 [A.IsTriangulated]
  签名: :
  定义体: inferInstanceAs (A.ι.CommShift Int)

Depends on / 依赖: CommShift
-/
instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.CommShift Int :=
  inferInstanceAs (A.ι.CommShift Int)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [A.IsTriangulated]
  signature: :
  body: inferInstanceAs A.ι.IsTriangulated

中文:
实例 [A.IsTriangulated]
  签名: :
  定义体: inferInstanceAs A.ι.IsTriangulated

Depends on / 依赖: IsTriangulated
-/
instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.IsTriangulated :=
  inferInstanceAs A.ι.IsTriangulated

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `trW_inverseImage_ι_iff` / 引理 `trW_inverseImage_ι_iff`

English:
lemma trW_inverseImage_ι_iff
  given: [A.IsTriangulated] {X Y : A.FullSubcategory} (f : X ⟶ Y)
  proof: by
  simp only [trW_iff]
  constructor
  · rintro ⟨Z, a, b, h, hZ⟩
    exact ⟨_, _, _, A.ι.map_distinguished _ h, Z.property, hZ⟩
  · rintro ⟨Z, a, b, h, hZ⟩
    refine ⟨⟨Z, hZ.1⟩, A.homMk a, A.homMk (b ≫ (A.ι.commShiftIso 1).inv.app _), ?_, hZ.2⟩
    rw [← A.ι.map_distinguished_iff]
    refine isom

中文:
引理 trW_inverseImage_ι_iff
  条件: [A.IsTriangulated] {X Y : A.FullSubcategory} (f : X ⟶ Y)
  证明: by
  simp only [trW_iff]
  constructor
  · rintro ⟨Z, a, b, h, hZ⟩
    exact ⟨_, _, _, A.ι.map_distinguished _ h, Z.property, hZ⟩
  · rintro ⟨Z, a, b, h, hZ⟩
    refine ⟨⟨Z, hZ.1⟩, A.homMk a, A.homMk (b ≫ (A.ι.commShiftIso 1).inv.app _), ?_, hZ.2⟩
    rw [← A.ι.map_distinguished_iff]
    refine isom

Depends on / 依赖: A.homMk, Iso.refl, Triangle, Triangle.isoMk, Z.property, cat_disch, commShiftIso, inv.app, inv_hom_id_app, isomorphic_distinguished, map_distinguished, map_distinguished_iff, property, trW_iff
-/
lemma trW_inverseImage_ι_iff [A.IsTriangulated] {X Y : A.FullSubcategory} (f : X ⟶ Y) :
    (B.inverseImage A.ι).trW f ↔ (A ⊓ B).trW f.hom := by
  simp only [trW_iff]
  constructor
  · rintro ⟨Z, a, b, h, hZ⟩
    exact ⟨_, _, _, A.ι.map_distinguished _ h, Z.property, hZ⟩
  · rintro ⟨Z, a, b, h, hZ⟩
    refine ⟨⟨Z, hZ.1⟩, A.homMk a, A.homMk (b ≫ (A.ι.commShiftIso 1).inv.app _), ?_, hZ.2⟩
    rw [← A.ι.map_distinguished_iff]
    refine isomorphic_distinguished _ h _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
    · cat_disch
    · cat_disch
    · simp [dsimp% (A.ι.commShiftIso (1 : Int)).inv_hom_id_app X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op` / 引理 `inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op`

English:
lemma inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op
  statement: [A.IsTriangulated]
  proof: by
  ext ⟨X₁⟩ ⟨X₂⟩ a
  simp [trW_op, trW_inverseImage_ι_iff, ← op_inf]

中文:
引理 inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op
  结论: [A.IsTriangulated]
  证明: by
  ext ⟨X₁⟩ ⟨X₂⟩ a
  simp [trW_op, trW_inverseImage_ι_iff, ← op_inf]

Depends on / 依赖: op_inf, trW_op
-/
lemma inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op [A.IsTriangulated]
    [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    (B.op.inverseImage A.op.ι).trW.inverseImage A.opEquivalence.inverse =
      (B.inverseImage A.ι).op.trW := by
  ext ⟨X₁⟩ ⟨X₂⟩ a
  simp [trW_op, trW_inverseImage_ι_iff, ← op_inf]

variable [IsTriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]

section

variable [A.IsVerdierRightLocalizing B]
  (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full
  body: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  have : L₁.EssSurj := Localization.essSurj L₁ (B.inverseImage A.ι).trW
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine F.full_of_comp_essSurj L₁ (fun X₁ X₂ φ => ?_)

中文:
实例 :
  签名: ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full
  定义体: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  have : L₁.EssSurj := Localization.essSurj L₁ (B.inverseImage A.ι).trW
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine F.full_of_comp_essSurj L₁ (fun X₁ X₂ φ => ?_)

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, CatCommSq, CatCommSq.iso, EssSurj, F.full_of_comp_essSurj, Localization, Localization.essSurj, Localization.exists_lef, e.hom.app, e.inv.app, e.inv_hom_id_app, e.inv_hom_id_app_assoc, essSurj, exists_lef, full_of_comp_essSurj, functor, inv_hom_id_app, inv_hom_id_app_assoc, inverseImage
-/
instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  have : L₁.EssSurj := Localization.essSurj L₁ (B.inverseImage A.ι).trW
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine F.full_of_comp_essSurj L₁ (fun X₁ X₂ φ => ?_)
  obtain ⟨φ', hφ'⟩ : exists φ', φ = e.inv.app X₁ ≫ φ' ≫ e.hom.app X₂ :=
    ⟨e.hom.app X₁ ≫ φ ≫ e.inv.app X₂, by
      simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L₂ B.trW φ'
  obtain ⟨X₃, s', a, hX₃, hs', fac⟩ :=
    IsVerdierRightLocalizing.fac' f.s X₂.property f.hs
  let g : (B.inverseImage A.ι).trW.LeftFraction X₁ X₂ :=
    { Y' := ⟨X₃, hX₃⟩
      f := A.homMk (f.f ≫ a)
      s := A.homMk s'
      hs := by rwa [trW_inverseImage_ι_iff] }
  have := Localization.inverts L₁ _ _ g.hs
  refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
  rw [← cancel_mono (F.map (L₁.map g.s))]; rw [← Functor.map_comp]; rw [MorphismProperty.LeftFraction.map_comp_map_s]
  simp [g, ← fac, hφ', hf, ← dsimp% NatIso.naturality_1 e,
    dsimp% e.hom_inv_id_app_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
  body: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

中文:
实例 [Preadditive
  签名: D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
  定义体: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, CatCommSq, CatCommSq.iso, Functor, Functor.additive_of_iso, Localization, Localization.functor_additive_iff, additive_of_iso, functor, functor_additive_iff, inverseImage, localizedFunctor, triangulatedLocalizerMorphism
-/
instance [Preadditive D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful
  body: by
  let := Localization.preadditive L₁ (B.inverseImage A.ι).trW
  let := Localization.preadditive L₂ B.trW
  have := Localization.functor_additive L₁ (B.inverseImage A.ι).trW
  have := Localization.functor_additive L₂ B.trW
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let

中文:
实例 :
  签名: ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful
  定义体: by
  let := Localization.preadditive L₁ (B.inverseImage A.ι).trW
  let := Localization.preadditive L₂ B.trW
  have := Localization.functor_additive L₁ (B.inverseImage A.ι).trW
  have := Localization.functor_additive L₂ B.trW
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, B.trW, CatCommSq, CatCommSq.iso, Functor, Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions, Localization, Localization.functor_additive, Localization.preadditive, faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions, functor, functor_additive, inverseImage, localizedFunctor, preadditive, triangulatedLocalizerMorphism
-/
instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  let := Localization.preadditive L₁ (B.inverseImage A.ι).trW
  let := Localization.preadditive L₂ B.trW
  have := Localization.functor_additive L₁ (B.inverseImage A.ι).trW
  have := Localization.functor_additive L₂ B.trW
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F :=
    CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions L₁
    (B.inverseImage A.ι).trW F (fun X₁ X₂ f hf => ?_)
  replace hf : L₂.map f.hom = L₂.map 0 := by
    simp [← dsimp% NatIso.naturality_2 e f, hf]
  rw [MorphismProperty.map_eq_iff_postcomp L₂ B.trW] at hf
  obtain ⟨X₃, s, hs, fac⟩ := hf
  obtain ⟨X₄, t, a, hX₄, ht, fac'⟩ :=
    IsVerdierRightLocalizing.fac' s X₂.property hs
  let t' : X₂ ⟶ ⟨X₄, hX₄⟩ := A.homMk t
  have := Localization.inverts L₁ (B.inverseImage A.ι).trW t'
    (by rwa [trW_inverseImage_ι_iff])
  rw [← cancel_mono (L₁.map t')]; rw [zero_comp]; rw [← L₁.map_comp]; rw [← L₁.map_zero]
  congr 1
  ext
  simp [t', ← fac', reassoc_of% fac]

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [A.IsVerdierRightLocalizing
  signature: B] :
  body: ⟨.ofFullyFaithful _⟩

中文:
实例 [A.IsVerdierRightLocalizing
  签名: B] :
  定义体: ⟨.ofFullyFaithful _⟩

Depends on / 依赖: ofFullyFaithful
-/
instance [A.IsVerdierRightLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨.ofFullyFaithful _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [A.IsVerdierLeftLocalizing
  signature: B] :
  body: by
  let L₁ := (B.inverseImage A.ι).trW.Q
  let L₂ := B.trW.Q
  let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
    (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let : CatCommSq (A.op.triangulatedLocalizerMorphism B.op).functor
    (A.opEquivalence.functor ⋙ L₁.o

中文:
实例 [A.IsVerdierLeftLocalizing
  签名: B] :
  定义体: by
  let L₁ := (B.inverseImage A.ι).trW.Q
  let L₂ := B.trW.Q
  let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
    (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let : CatCommSq (A.op.triangulatedLocalizerMorphism B.op).functor
    (A.opEquivalence.functor ⋙ L₁.o

Depends on / 依赖: A.op.triangulatedLocalizerMorphism, A.opEquivalence.functor, A.triangulatedLocalizerMorphism, B.inverseImage, B.op, B.op.trW, B.trW.Localization, B.trW.Q, CatCommSq, CatCommSq.iso, F.op, Functor, Functor.isoWhiskerLeft, IsLocalization, Localization, NatIso, NatIso.op, functor, infer_ins, inverseImage
-/
instance [A.IsVerdierLeftLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful := by
  let L₁ := (B.inverseImage A.ι).trW.Q
  let L₂ := B.trW.Q
  let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
    (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let : CatCommSq (A.op.triangulatedLocalizerMorphism B.op).functor
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op :=
    ⟨Functor.isoWhiskerLeft A.opEquivalence.functor
      (NatIso.op (CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F).symm)⟩
  have : L₂.op.IsLocalization B.op.trW := by rw [trW_op]; infer_instance
  have : (A.opEquivalence.functor ⋙ L₁.op).IsLocalization (B.op.inverseImage A.op.ι).trW := by
    refine Functor.IsLocalization.of_equivalence_source L₁.op (B.inverseImage A.ι).trW.op
      _ _ A.opEquivalence.symm ?_ ?_
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight A.opEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
    · rw [← trW_op, ← inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op]
      intro _ _ f hf
      simp only [MorphismProperty.inverseImage_iff, Equivalence.symm_functor] at hf ⊢
      exact MorphismProperty.le_isoClosure _ _ hf
    · refine fun _ _ _ hf => Localization.inverts L₁.op (B.inverseImage A.ι).trW.op _ ?_
      simpa [trW_inverseImage_ι_iff, ← op_inf, trW_op] using! hf
  exact LocalizerMorphism.IsLocalizedFullyFaithful.mk' (A.triangulatedLocalizerMorphism B)
    L₁ L₂ F (((A.op.triangulatedLocalizerMorphism B.op).fullyFaithful
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op).unop)

section

variable [A.IsVerdierLeftLocalizing B] (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW]
  [L₂.IsLocalization B.trW]

example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  infer_instance

example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preadditive
  signature: D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
  body: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

中文:
实例 [Preadditive
  签名: D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
  定义体: by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, CatCommSq, CatCommSq.iso, Functor, Functor.additive_of_iso, Localization, Localization.functor_additive_iff, additive_of_iso, functor, functor_additive_iff, inverseImage, localizedFunctor, triangulatedLocalizerMorphism
-/
instance [Preadditive D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

/-- If `A` is a left `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
/--
Definition of `IsVerdierLeftLocalizing.fullyFaithful` / `IsVerdierLeftLocalizing.fullyFaithful` 的定义

English:
definition IsVerdierLeftLocalizing.fullyFaithful
  body: Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

中文:
定义 IsVerdierLeftLocalizing.fullyFaithful
  定义体: Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, FullyFaithful, Functor, Functor.FullyFaithful.ofIso, Localization, Localization.liftNatIso, e.symm, functor, inverseImage, liftNatIso, localizedFunctor, ofFullyFaithful, triangulatedLocalizerMorphism
-/
noncomputable def IsVerdierLeftLocalizing.fullyFaithful
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

/-- If `A` is a right `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
/--
Definition of `IsVerdierRightLocalizing.fullyFaithful` / `IsVerdierRightLocalizing.fullyFaithful` 的定义

English:
definition IsVerdierRightLocalizing.fullyFaithful
  signature: [A.IsVerdierRightLocalizing B]
  body: Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

中文:
定义 IsVerdierRightLocalizing.fullyFaithful
  签名: [A.IsVerdierRightLocalizing B]
  定义体: Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

Depends on / 依赖: A.triangulatedLocalizerMorphism, B.inverseImage, FullyFaithful, Functor, Functor.FullyFaithful.ofIso, Localization, Localization.liftNatIso, e.symm, functor, inverseImage, liftNatIso, localizedFunctor, ofFullyFaithful, triangulatedLocalizerMorphism
-/
noncomputable def IsVerdierRightLocalizing.fullyFaithful [A.IsVerdierRightLocalizing B]
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

end

end ObjectProperty

end CategoryTheory
