/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Morphism properties that are inverted by a functor

In this file, we introduce the predicate `P.IsInvertedBy F` which expresses
that the morphisms satisfying `P : MorphismProperty C` are mapped to
isomorphisms by a functor `F : C ⥤ D`.

This is used in the localization of categories API (folder `CategoryTheory.Localization`).

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/--
Definition of `IsInvertedBy` / `IsInvertedBy` 的定义

English:
definition IsInvertedBy
  signature: (P : MorphismProperty C) (F : C ⥤ D)
  body: forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

中文:
定义 IsInvertedBy
  签名: (P : MorphismProperty C) (F : C ⥤ D)
  定义体: forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

Depends on / 依赖: F.map
-/
def IsInvertedBy (P : MorphismProperty C) (F : C ⥤ D) : Prop :=
  forall ⦃X Y : C⦄ (f : X ⟶ Y) (_ : P f), IsIso (F.map f)

namespace IsInvertedBy

/--
lemma `of_le` / 引理 `of_le`

English:
lemma of_le
  given: (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q)
  proof: fun _ _ _ hf => hQ _ (h _ hf)

中文:
引理 of_le
  条件: (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q)
  证明: fun _ _ _ hf => hQ _ (h _ hf)
-/
lemma of_le (P Q : MorphismProperty C) (F : C ⥤ D) (hQ : Q.IsInvertedBy F) (h : P <= Q) :
    P.IsInvertedBy F :=
  fun _ _ _ hf => hQ _ (h _ hf)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `of_comp` / 定理 `of_comp`

English:
theorem of_comp
  statement: {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  proof: fun X Y f hf => by
  have := hF f hf
  dsimp
  infer_instance

中文:
定理 of_comp
  结论: {C₁ C₂ C₃ : 类型} [范畴* C₁] [范畴* C₂] [范畴* C₃]
  证明: fun X Y f hf => by
  have := hF f hf
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
theorem of_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (hF : W.IsInvertedBy F) (G : C₂ ⥤ C₃) :
    W.IsInvertedBy (F ⋙ G) := fun X Y f hf => by
  have := hF f hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
theorem `op` / 定理 `op`

English:
theorem op
  given: {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L)
  statement: W.op.IsInvertedBy L.op
  proof: fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

中文:
定理 op
  条件: {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L)
  结论: W.op.IsInvertedBy L.op
  证明: fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

Depends on / 依赖: f.unop, infer_instance
-/
theorem op {W : MorphismProperty C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op :=
  fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
theorem `rightOp` / 定理 `rightOp`

English:
theorem rightOp
  given: {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L)
  proof: fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

中文:
定理 rightOp
  条件: {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L)
  证明: fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

Depends on / 依赖: f.op, infer_instance
-/
theorem rightOp {W : MorphismProperty C} {L : Cᵒᵖ ⥤ D} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.rightOp := fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
theorem `leftOp` / 定理 `leftOp`

English:
theorem leftOp
  given: {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L)
  proof: fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

中文:
定理 leftOp
  条件: {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L)
  证明: fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

Depends on / 依赖: f.unop, infer_instance
-/
theorem leftOp {W : MorphismProperty C} {L : C ⥤ Dᵒᵖ} (h : W.IsInvertedBy L) :
    W.op.IsInvertedBy L.leftOp := fun X Y f hf => by
  have := h f.unop hf
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  given: {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L)
  proof: fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

中文:
定理 unop
  条件: {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L)
  证明: fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

Depends on / 依赖: f.op, infer_instance
-/
theorem unop {W : MorphismProperty C} {L : Cᵒᵖ ⥤ Dᵒᵖ} (h : W.op.IsInvertedBy L) :
    W.IsInvertedBy L.unop := fun X Y f hf => by
  have := h f.op hf
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `prod` / 引理 `prod`

English:
lemma prod
  statement: {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  proof: fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩

中文:
引理 乘积
  结论: {C₁ C₂ : 类型} [范畴* C₁] [范畴* C₂]
  证明: fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩

Depends on / 依赖: isIso_prod_iff
-/
lemma prod {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
    {E₁ E₂ : Type*} [Category* E₁] [Category* E₂] {F₁ : C₁ ⥤ E₁} {F₂ : C₂ ⥤ E₂}
    (h₁ : W₁.IsInvertedBy F₁) (h₂ : W₂.IsInvertedBy F₂) :
    (W₁.prod W₂).IsInvertedBy (F₁.prod F₂) := fun _ _ f hf => by
  rw [isIso_prod_iff]
  exact ⟨h₁ _ hf.1, h₂ _ hf.2⟩

/--
lemma `pi` / 引理 `pi`

English:
lemma pi
  statement: {J : Type w} {C : J -> Type u} {D : J -> Type u'}
  proof: by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

中文:
引理 pi
  结论: {J : 类型 w} {C : J -> 类型u} {D : J -> 类型u'}
  证明: by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

Depends on / 依赖: isIso_pi_iff
-/
lemma pi {J : Type w} {C : J -> Type u} {D : J -> Type u'}
    [forall j, Category.{v} (C j)] [forall j, Category.{v'} (D j)]
    (W : forall j, MorphismProperty (C j)) (F : forall j, C j ⥤ D j)
    (hF : forall j, (W j).IsInvertedBy (F j)) :
    (MorphismProperty.pi W).IsInvertedBy (Functor.pi F) := by
  intro _ _ f hf
  rw [isIso_pi_iff]
  intro j
  exact hF j _ (hf j)

end IsInvertedBy

/--
Definition of `FunctorsInverting` / `FunctorsInverting` 的定义

English:
definition FunctorsInverting
  signature: (W : MorphismProperty C) (D : Type*) [Category* D]
  body: ObjectProperty.FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F

@[ext]

中文:
定义 FunctorsInverting
  签名: (W : MorphismProperty C) (D : 类型) [范畴* D]
  定义体: ObjectProperty.FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F

@[ext]

Depends on / 依赖: FullSubcategory, IsInvertedBy, ObjectProperty, ObjectProperty.FullSubcategory, W.IsInvertedBy
-/
def FunctorsInverting (W : MorphismProperty C) (D : Type*) [Category* D] :=
  ObjectProperty.FullSubcategory fun F : C ⥤ D => W.IsInvertedBy F

@[ext]
/--
lemma `FunctorsInverting.ext` / 引理 `FunctorsInverting.ext`

English:
lemma FunctorsInverting.ext
  statement: {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
  proof: by
  cases F₁
  cases F₂
  subst h
  rfl

中文:
引理 FunctorsInverting.ext
  结论: {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
  证明: by
  cases F₁
  cases F₂
  subst h
  rfl
-/
lemma FunctorsInverting.ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    (h : F₁.obj = F₂.obj) : F₁ = F₂ := by
  cases F₁
  cases F₂
  subst h
  rfl

instance (W : MorphismProperty C) (D : Type*) [Category* D] : Category (FunctorsInverting W D) :=
  ObjectProperty.FullSubcategory.category _

@[simp]
/--
lemma `FunctorsInverting.id_hom` / 引理 `FunctorsInverting.id_hom`

English:
lemma FunctorsInverting.id_hom
  proof: rfl

@[simp, reassoc]

中文:
引理 FunctorsInverting.id_hom
  证明: rfl

@[simp, reassoc]
-/
lemma FunctorsInverting.id_hom
    {W : MorphismProperty C} (F : FunctorsInverting W D) :
    InducedCategory.Hom.hom (𝟙 F) = 𝟙 _ := rfl

@[simp, reassoc]
/--
lemma `FunctorsInverting.comp_hom` / 引理 `FunctorsInverting.comp_hom`

English:
lemma FunctorsInverting.comp_hom
  proof: rfl

@[ext]

中文:
引理 FunctorsInverting.comp_hom
  证明: rfl

@[ext]
-/
lemma FunctorsInverting.comp_hom
    {W : MorphismProperty C} {F₁ F₂ F₃ : FunctorsInverting W D}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[ext]
/--
lemma `FunctorsInverting.hom_ext` / 引理 `FunctorsInverting.hom_ext`

English:
lemma FunctorsInverting.hom_ext
  statement: {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
  proof: ObjectProperty.hom_ext _ (NatTrans.ext h)

中文:
引理 FunctorsInverting.hom_ext
  结论: {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
  证明: ObjectProperty.hom_ext _ (NatTrans.ext h)

Depends on / 依赖: NatTrans, NatTrans.ext, ObjectProperty, ObjectProperty.hom_ext, hom_ext
-/
lemma FunctorsInverting.hom_ext {W : MorphismProperty C} {F₁ F₂ : FunctorsInverting W D}
    {α β : F₁ ⟶ F₂} (h : α.hom.app = β.hom.app) : α = β :=
  ObjectProperty.hom_ext _ (NatTrans.ext h)

/--
Definition of `FunctorsInverting.mk` / `FunctorsInverting.mk` 的定义

English:
definition FunctorsInverting.mk
  signature: {W : MorphismProperty C} {D : Type*} [Category* D] (F : C ⥤ D)
  body: ⟨F, hF⟩

中文:
定义 FunctorsInverting.mk
  签名: {W : MorphismProperty C} {D : 类型} [范畴* D] (F : C ⥤ D)
  定义体: ⟨F, hF⟩
-/
def FunctorsInverting.mk {W : MorphismProperty C} {D : Type*} [Category* D] (F : C ⥤ D)
    (hF : W.IsInvertedBy F) : W.FunctorsInverting D :=
  ⟨F, hF⟩

/--
theorem `IsInvertedBy.iff_of_iso` / 定理 `IsInvertedBy.iff_of_iso`

English:
theorem IsInvertedBy.iff_of_iso
  given: (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
  proof: by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]

中文:
定理 IsInvertedBy.iff_of_iso
  条件: (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
  证明: by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]

Depends on / 依赖: IsInvertedBy, NatIso, NatIso.isIso_map_iff, isIso_map_iff
-/
theorem IsInvertedBy.iff_of_iso (W : MorphismProperty C) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) :
    W.IsInvertedBy F₁ ↔ W.IsInvertedBy F₂ := by
  dsimp [IsInvertedBy]
  simp only [NatIso.isIso_map_iff e]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `IsInvertedBy.isoClosure_iff` / 引理 `IsInvertedBy.isoClosure_iff`

English:
lemma IsInvertedBy.isoClosure_iff
  given: (W : MorphismProperty C) (F : C ⥤ D)
  proof: by
  constructor
  · intro h X Y f hf
    exact h _ (W.le_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    simp only [Arrow.iso_w' e, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]

中文:
引理 IsInvertedBy.isoClosure_iff
  条件: (W : MorphismProperty C) (F : C ⥤ D)
  证明: by
  constructor
  · intro h X Y f hf
    exact h _ (W.le_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    simp only [Arrow.iso_w' e, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]

Depends on / 依赖: Arrow.iso_w, F.map_comp, W.le_isoClosure, infer_instance, iso_w, le_isoClosure, map_comp
-/
lemma IsInvertedBy.isoClosure_iff (W : MorphismProperty C) (F : C ⥤ D) :
    W.isoClosure.IsInvertedBy F ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    exact h _ (W.le_isoClosure _ hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    simp only [Arrow.iso_w' e, F.map_comp]
    have := h _ hf'
    infer_instance

@[simp]
/--
lemma `IsInvertedBy.iff_comp` / 引理 `IsInvertedBy.iff_comp`

English:
lemma IsInvertedBy.iff_comp
  statement: {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  proof: by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G

中文:
引理 IsInvertedBy.iff_comp
  结论: {C₁ C₂ C₃ : 类型} [范畴* C₁] [范畴* C₂] [范畴* C₃]
  证明: by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G

Depends on / 依赖: F.map, G.map, IsInvertedBy, IsInvertedBy.of_comp, isIso_of_reflects_iso, of_comp
-/
lemma IsInvertedBy.iff_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [G.ReflectsIsomorphisms] :
    W.IsInvertedBy (F ⋙ G) ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have : IsIso (G.map (F.map f)) := h _ hf
    exact isIso_of_reflects_iso (F.map f) G
  · intro hF
    exact IsInvertedBy.of_comp W F hF G

/--
lemma `IsInvertedBy.iff_le_inverseImage_isomorphisms` / 引理 `IsInvertedBy.iff_le_inverseImage_isomorphisms`

English:
lemma IsInvertedBy.iff_le_inverseImage_isomorphisms
  given: (W : MorphismProperty C) (F : C ⥤ D)
  proof: Iff.rfl

中文:
引理 IsInvertedBy.iff_le_inverseImage_isomorphisms
  条件: (W : MorphismProperty C) (F : C ⥤ D)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma IsInvertedBy.iff_le_inverseImage_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W <= (isomorphisms D).inverseImage F := Iff.rfl

/--
lemma `IsInvertedBy.iff_map_le_isomorphisms` / 引理 `IsInvertedBy.iff_map_le_isomorphisms`

English:
lemma IsInvertedBy.iff_map_le_isomorphisms
  given: (W : MorphismProperty C) (F : C ⥤ D)
  proof: by
  rw [iff_le_inverseImage_isomorphisms]; rw [map_le_iff]

中文:
引理 IsInvertedBy.iff_map_le_isomorphisms
  条件: (W : MorphismProperty C) (F : C ⥤ D)
  证明: by
  rw [iff_le_inverseImage_isomorphisms]; rw [map_le_iff]

Depends on / 依赖: iff_le_inverseImage_isomorphisms, map_le_iff
-/
lemma IsInvertedBy.iff_map_le_isomorphisms (W : MorphismProperty C) (F : C ⥤ D) :
    W.IsInvertedBy F ↔ W.map F <= isomorphisms D := by
  rw [iff_le_inverseImage_isomorphisms]; rw [map_le_iff]

/--
lemma `IsInvertedBy.map_iff` / 引理 `IsInvertedBy.map_iff`

English:
lemma IsInvertedBy.map_iff
  statement: {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  proof: by
  simp only [IsInvertedBy.iff_map_le_isomorphisms, map_map]

中文:
引理 IsInvertedBy.map_iff
  结论: {C₁ C₂ C₃ : 类型} [范畴* C₁] [范畴* C₂] [范畴* C₃]
  证明: by
  simp only [IsInvertedBy.iff_map_le_isomorphisms, map_map]

Depends on / 依赖: IsInvertedBy, IsInvertedBy.iff_map_le_isomorphisms, iff_map_le_isomorphisms, map_map
-/
lemma IsInvertedBy.map_iff {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (W : MorphismProperty C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    (W.map F).IsInvertedBy G ↔ W.IsInvertedBy (F ⋙ G) := by
  simp only [IsInvertedBy.iff_map_le_isomorphisms, map_map]

/--
lemma `isInvertedBy_isomorphisms` / 引理 `isInvertedBy_isomorphisms`

English:
lemma isInvertedBy_isomorphisms
  given: (F : C ⥤ D)
  statement: (isomorphisms C).IsInvertedBy F
  proof: by
  intro _ _ _ hf
  simp only [isomorphisms.iff] at hf
  infer_instance

中文:
引理 isInvertedBy_isomorphisms
  条件: (F : C ⥤ D)
  结论: (isomorphisms C).IsInvertedBy F
  证明: by
  intro _ _ _ hf
  simp only [isomorphisms.iff] at hf
  infer_instance

Depends on / 依赖: infer_instance, isomorphisms, isomorphisms.iff
-/
lemma isInvertedBy_isomorphisms (F : C ⥤ D) : (isomorphisms C).IsInvertedBy F := by
  intro _ _ _ hf
  simp only [isomorphisms.iff] at hf
  infer_instance

end MorphismProperty

end CategoryTheory
