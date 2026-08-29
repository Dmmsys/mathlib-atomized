/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Smallness of a property of objects

In this file, given `P : ObjectProperty C`, we define
`ObjectProperty.Small.{w} P` as an abbreviation for `Small.{w} (Subtype P)`.

-/

public section

universe w' w v v' u u'

namespace CategoryTheory.ObjectProperty

open Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A property of objects is small relative to a universe `w`
if the corresponding subtype is. -/
@[pp_with_univ]
/--
Definition of `Small` / `Small` 的定义

English:
abbreviation Small
  signature: (P : ObjectProperty C)
  body: _root_.Small.{w} (Subtype P)

中文:
缩写 Small
  签名: (P : ObjectProperty C)
  定义体: _root_.Small.{w} (Subtype P)
-/
protected abbrev Small (P : ObjectProperty C) : Prop := _root_.Small.{w} (Subtype P)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    Small.{w} P.FullSubcategory :=
  small_of_surjective (f := fun (x : Subtype P) => ⟨x.1, x.2⟩) (fun x => ⟨⟨x.1, x.2⟩, rfl⟩)

/--
lemma `Small.of_le` / 引理 `Small.of_le`

English:
lemma Small.of_le
  given: {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P <= Q)
  proof: small_of_injective (Subtype.map_injective h Function.injective_id)

中文:
引理 Small.of_le
  条件: {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P <= Q)
  证明: small_of_injective (Subtype.map_injective h Function.injective_id)

Depends on / 依赖: Function, Function.injective_id, Subtype, Subtype.map_injective, injective_id, map_injective, small_of_injective
-/
lemma Small.of_le {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P <= Q) :
    ObjectProperty.Small.{w} P :=
  small_of_injective (Subtype.map_injective h Function.injective_id)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.op :=
  small_of_injective P.subtypeOpEquiv.injective

instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.unop := by
  simpa only [← small_congr P.unop.subtypeOpEquiv]

instance {ι : Type*} (X : ι -> C) [Small.{w} ι] :
    ObjectProperty.Small.{w} (ofObj X) :=
  small_of_surjective (f := fun i => ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; simp)

instance (X Y : C) : ObjectProperty.Small.{w} (.pair X Y) := by
  dsimp [pair]
  infer_instance

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_right

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  Small.of_le inf_le_left

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊔ Q) :=
  small_of_surjective (f := fun (x : Subtype P oplus Subtype Q) => match x with
      | .inl x => ⟨x.1, Or.inl x.2⟩
      | .inr x => ⟨x.1, Or.inr x.2⟩)
    (by rintro ⟨x, hx | hx⟩ <;> aesop)

instance {α : Type*} (P : α -> ObjectProperty C)
    [forall a, ObjectProperty.Small.{w} (P a)] [Small.{w} α] :
    ObjectProperty.Small.{w} (⨆ a, P a) :=
  small_of_surjective (f := fun (x : Σ a, Subtype (P a)) => ⟨x.2.1, by aesop⟩)
    (fun ⟨x, hx⟩ => by aesop)

@[simp]
/--
lemma `small_op_iff` / 引理 `small_op_iff`

English:
lemma small_op_iff
  given: (P : ObjectProperty C)
  proof: small_congr
    { toFun x := ⟨x.1.unop, x.2⟩
      invFun x := ⟨op x.1, x.2⟩}

@[simp]

中文:
引理 small_op_iff
  条件: (P : ObjectProperty C)
  证明: small_congr
    { toFun x := ⟨x.1.unop, x.2⟩
      invFun x := ⟨op x.1, x.2⟩}

@[simp]

Depends on / 依赖: invFun, small_congr
-/
lemma small_op_iff (P : ObjectProperty C) :
    ObjectProperty.Small.{w} P.op ↔ ObjectProperty.Small.{w} P :=
  small_congr
    { toFun x := ⟨x.1.unop, x.2⟩
      invFun x := ⟨op x.1, x.2⟩}

@[simp]
/--
lemma `small_unop_iff` / 引理 `small_unop_iff`

English:
lemma small_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  proof: by
  rw [← small_op_iff]; rw [op_unop]

中文:
引理 small_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  证明: by
  rw [← small_op_iff]; rw [op_unop]

Depends on / 依赖: op_unop, small_op_iff
-/
lemma small_unop_iff (P : ObjectProperty Cᵒᵖ) :
    ObjectProperty.Small.{w} P.unop ↔ ObjectProperty.Small.{w} P := by
  rw [← small_op_iff]; rw [op_unop]

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.op := by
  simpa

instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} P.unop := by
  simpa

/-- A property of objects is essentially small relative to a universe `w`
if it is contained in the closure by isomorphisms of a small property. -/
@[pp_with_univ]
/--
Definition of `EssentiallySmall` / `EssentiallySmall` 的定义

English:
class EssentiallySmall
  parameters: (P : ObjectProperty C)
  axioms and operations (1):
    - exists_small_le'((P)) : exists (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q), P <= Q.isoClosure

中文:
类 EssentiallySmall
  参数: (P : ObjectProperty C)
  公理与运算 (1 个):
    - exists_small_le'((P)) : 存在 (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q), P <= Q.isoClosure
-/
protected class EssentiallySmall (P : ObjectProperty C) : Prop where
  exists_small_le' (P) : exists (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q),
    P <= Q.isoClosure

/--
lemma `EssentiallySmall.exists_small_le` / 引理 `EssentiallySmall.exists_small_le`

English:
lemma EssentiallySmall.exists_small_le
  statement: (P : ObjectProperty C)
  proof: by
  obtain ⟨Q, _, hQ⟩ := exists_small_le' P
  let P' := Q ⊓ P.isoClosure
  have h (X' : Subtype P') : exists (X : Subtype P), Nonempty (X'.1 ≅ X.1) :=
    ⟨⟨X'.2.2.choose, X'.2.2.choose_spec.choose⟩, X'.2.2.choose_spec.choose_spec⟩
  choose φ hφ using h
  refine ⟨fun X => X in Set.range (Subtype.val ∘ φ), ?_, ?_, ?_⟩
  · exact small_of_surjective (f := fun X => ⟨(φ X).1, by tauto⟩)
      (by rintro ⟨_, Z, rfl⟩; exact ⟨Z, rfl⟩)
  · intro X hX
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact (φ ⟨Y, hY⟩).2
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    let Z : Subtype P' := ⟨Y, hY, ⟨X, hX, ⟨e.symm⟩⟩⟩
    exact ⟨_, ⟨Z, rfl⟩, ⟨e ≪≫ (hφ Z).some⟩⟩

中文:
引理 EssentiallySmall.存在_small_le
  结论: (P : ObjectProperty C)
  证明: by
  obtain ⟨Q, _, hQ⟩ := exists_small_le' P
  let P' := Q ⊓ P.isoClosure
  have h (X' : Subtype P') : exists (X : Subtype P), Nonempty (X'.1 ≅ X.1) :=
    ⟨⟨X'.2.2.choose, X'.2.2.choose_spec.choose⟩, X'.2.2.choose_spec.choose_spec⟩
  choose φ hφ using h
  refine ⟨fun X => X in Set.range (Subtype.val ∘ φ), ?_, ?_, ?_⟩
  · exact small_of_surjective (f := fun X => ⟨(φ X).1, by tauto⟩)
      (by rintro ⟨_, Z, rfl⟩; exact ⟨Z, rfl⟩)
  · intro X hX
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact (φ ⟨Y, hY⟩).2
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    let Z : Subtype P' := ⟨Y, hY, ⟨X, hX, ⟨e.symm⟩⟩⟩
    exact ⟨_, ⟨Z, rfl⟩, ⟨e ≪≫ (hφ Z).some⟩⟩

Depends on / 依赖: Function, Function.comp_apply, Nonempty, P.isoClosure, Set.mem_range, Set.range, Subtype, Subtype.exists, Subtype.val, choose_spec, choose_spec.choose, choose_spec.choose_spec, comp_apply, exists_small_le, isoClosure, mem_range, small_of_surjective
-/
lemma EssentiallySmall.exists_small_le (P : ObjectProperty C)
    [ObjectProperty.EssentiallySmall.{w} P] :
    exists (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q), Q <= P ∧ P <= Q.isoClosure := by
  obtain ⟨Q, _, hQ⟩ := exists_small_le' P
  let P' := Q ⊓ P.isoClosure
  have h (X' : Subtype P') : exists (X : Subtype P), Nonempty (X'.1 ≅ X.1) :=
    ⟨⟨X'.2.2.choose, X'.2.2.choose_spec.choose⟩, X'.2.2.choose_spec.choose_spec⟩
  choose φ hφ using h
  refine ⟨fun X => X in Set.range (Subtype.val ∘ φ), ?_, ?_, ?_⟩
  · exact small_of_surjective (f := fun X => ⟨(φ X).1, by tauto⟩)
      (by rintro ⟨_, Z, rfl⟩; exact ⟨Z, rfl⟩)
  · intro X hX
    simp only [Set.mem_range, Function.comp_apply, Subtype.exists] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact (φ ⟨Y, hY⟩).2
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    let Z : Subtype P' := ⟨Y, hY, ⟨X, hX, ⟨e.symm⟩⟩⟩
    exact ⟨_, ⟨Z, rfl⟩, ⟨e ≪≫ (hφ Z).some⟩⟩

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := ⟨P, inferInstance, le_isoClosure P⟩

instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.isoClosure where
  exists_small_le' := by
    obtain ⟨Q, _, _, _⟩ := EssentiallySmall.exists_small_le.{w} P
    exact ⟨Q, inferInstance, by rwa [isoClosure_le_iff]⟩

/--
lemma `EssentiallySmall.exists_small` / 引理 `EssentiallySmall.exists_small`

English:
lemma EssentiallySmall.exists_small
  statement: (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  proof: by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_small_le P
  exact ⟨Q, inferInstance, le_antisymm hQ₂ (by rwa [isoClosure_le_iff])⟩

中文:
引理 EssentiallySmall.存在_small
  结论: (P : ObjectProperty C) [P.在同构下封闭]
  证明: by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_small_le P
  exact ⟨Q, inferInstance, le_antisymm hQ₂ (by rwa [isoClosure_le_iff])⟩

Depends on / 依赖: exists_small_le, isoClosure_le_iff, le_antisymm
-/
lemma EssentiallySmall.exists_small (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    exists (P₀ : ObjectProperty C) (_ : ObjectProperty.Small.{w} P₀), P = P₀.isoClosure := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_small_le P
  exact ⟨Q, inferInstance, le_antisymm hQ₂ (by rwa [isoClosure_le_iff])⟩

/--
lemma `EssentiallySmall.of_le` / 引理 `EssentiallySmall.of_le`

English:
lemma EssentiallySmall.of_le
  statement: {P Q : ObjectProperty C}
  proof: by
    obtain ⟨R, _, hR⟩ := EssentiallySmall.exists_small_le' Q
    exact ⟨R, inferInstance, h.trans hR⟩

中文:
引理 EssentiallySmall.of_le
  结论: {P Q : ObjectProperty C}
  证明: by
    obtain ⟨R, _, hR⟩ := EssentiallySmall.exists_small_le' Q
    exact ⟨R, inferInstance, h.trans hR⟩

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, exists_small_le, h.trans
-/
lemma EssentiallySmall.of_le {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} Q] (h : P <= Q) :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le' := by
    obtain ⟨R, _, hR⟩ := EssentiallySmall.exists_small_le' Q
    exact ⟨R, inferInstance, h.trans hR⟩

instance {P Q : ObjectProperty C}
    [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q] :
    ObjectProperty.EssentiallySmall.{w} (P ⊔ Q) := by
  obtain ⟨P', _, hP'⟩ := EssentiallySmall.exists_small_le' P
  obtain ⟨Q', _, hQ'⟩ := EssentiallySmall.exists_small_le' Q
  refine ⟨P' ⊔ Q', inferInstance, ?_⟩
  simp only [sup_le_iff]
  constructor
  · exact hP'.trans (monotone_isoClosure le_sup_left)
  · exact hQ'.trans (monotone_isoClosure le_sup_right)

instance {α : Type*} (P : α -> ObjectProperty C)
    [forall a, ObjectProperty.EssentiallySmall.{w} (P a)] [Small.{w} α] :
    ObjectProperty.EssentiallySmall.{w} (⨆ a, P a) where
  exists_small_le' := by
    have h (a : α) := EssentiallySmall.exists_small_le' (P a)
    choose Q _ hQ using h
    refine ⟨⨆ a, Q a, inferInstance, ?_⟩
    simp only [iSup_le_iff]
    intro a
    exact (hQ a).trans (monotone_isoClosure (le_iSup Q a))

@[simp]
/--
lemma `essentiallySmall_op_iff` / 引理 `essentiallySmall_op_iff`

English:
lemma essentiallySmall_op_iff
  given: (P : ObjectProperty C)
  proof: by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P.op
    exact ⟨Q.unop, inferInstance, by rwa [← unop_isoClosure, ← op_monotone_iff, op_unop]⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P
    exact ⟨Q.op, inferInstance, by rwa [← op_isoClosure, op_monotone_iff]⟩

@[simp]

中文:
引理 essentiallySmall_op_iff
  条件: (P : ObjectProperty C)
  证明: by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P.op
    exact ⟨Q.unop, inferInstance, by rwa [← unop_isoClosure, ← op_monotone_iff, op_unop]⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P
    exact ⟨Q.op, inferInstance, by rwa [← op_isoClosure, op_monotone_iff]⟩

@[simp]

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, P.op, Q.op, Q.unop, exists_small_le, op_isoClosure, op_monotone_iff, op_unop, unop_isoClosure
-/
lemma essentiallySmall_op_iff (P : ObjectProperty C) :
    ObjectProperty.EssentiallySmall.{w} P.op ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P.op
    exact ⟨Q.unop, inferInstance, by rwa [← unop_isoClosure, ← op_monotone_iff, op_unop]⟩
  · obtain ⟨Q, h₁, _, h₂⟩ := EssentiallySmall.exists_small_le P
    exact ⟨Q.op, inferInstance, by rwa [← op_isoClosure, op_monotone_iff]⟩

@[simp]
/--
lemma `essentiallySmall_unop_iff` / 引理 `essentiallySmall_unop_iff`

English:
lemma essentiallySmall_unop_iff
  given: (P : ObjectProperty Cᵒᵖ)
  proof: by
  rw [← essentiallySmall_op_iff]; rw [op_unop]

中文:
引理 essentiallySmall_unop_iff
  条件: (P : ObjectProperty Cᵒᵖ)
  证明: by
  rw [← essentiallySmall_op_iff]; rw [op_unop]

Depends on / 依赖: essentiallySmall_op_iff, op_unop
-/
lemma essentiallySmall_unop_iff (P : ObjectProperty Cᵒᵖ) :
    ObjectProperty.EssentiallySmall.{w} P.unop ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  rw [← essentiallySmall_op_iff]; rw [op_unop]

instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.op := by
  simpa

instance (P : ObjectProperty Cᵒᵖ) [ObjectProperty.EssentiallySmall.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.unop := by
  simpa

instance (P : ObjectProperty C) [LocallySmall.{w} C]
    [ObjectProperty.EssentiallySmall.{w} P] : EssentiallySmall.{w} P.FullSubcategory := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  have := (isEquivalence_ιOfLE_iff h₁).2 h₂
  rw [← essentiallySmall_congr (ιOfLE h₁).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall.{w}
  signature: C] :
  body: ⟨ofObj (equivSmallModel.{w} C).inverse.obj, inferInstance,
      fun X _ => ⟨_, ⟨_⟩, ⟨(equivSmallModel.{w} C).unitIso.app X⟩⟩⟩

中文:
实例 [EssentiallySmall.{w}
  签名: C] :
  定义体: ⟨ofObj (equivSmallModel.{w} C).inverse.obj, inferInstance,
      fun X _ => ⟨_, ⟨_⟩, ⟨(equivSmallModel.{w} C).unitIso.app X⟩⟩⟩

Depends on / 依赖: equivSmallModel, inverse, inverse.obj, unitIso, unitIso.app
-/
instance [EssentiallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (⊤ : ObjectProperty C) where
  exists_small_le' :=
    ⟨ofObj (equivSmallModel.{w} C).inverse.obj, inferInstance,
      fun X _ => ⟨_, ⟨_⟩, ⟨(equivSmallModel.{w} C).unitIso.app X⟩⟩⟩

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] (F : C ⥤ D) :
    ObjectProperty.Small.{w} (P.strictMap F) :=
  small_of_surjective (f := fun (X : Subtype P) => ⟨F.obj X.1, ⟨_, X.2⟩⟩) (by
    rintro ⟨_, ⟨X, hX⟩⟩
    exact ⟨⟨X, hX⟩, rfl⟩)

instance (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P]
    (F : C ⥤ D) : ObjectProperty.EssentiallySmall.{w} (P.map F) := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  exact ⟨Q.strictMap F, inferInstance, (map_monotone h₂ F).trans (by simp)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssentiallySmall.{w}
  signature: C] (F
  body: by
  rw [← ObjectProperty.map_top]
  infer_instance

中文:
实例 [EssentiallySmall.{w}
  签名: C] (F
  定义体: by
  rw [← ObjectProperty.map_top]
  infer_instance

Depends on / 依赖: ObjectProperty, ObjectProperty.map_top, infer_instance, map_top
-/
instance [EssentiallySmall.{w} C] (F : C ⥤ D) :
    ObjectProperty.EssentiallySmall.{w} F.essImage := by
  rw [← ObjectProperty.map_top]
  infer_instance

instance (P : ObjectProperty C) [LocallySmall.{w} C]
    [ObjectProperty.EssentiallySmall.{w} P] : EssentiallySmall.{w} P.FullSubcategory := by
  obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le P
  have := (isEquivalence_ιOfLE_iff h₁).2 h₂
  rw [← essentiallySmall_congr (ιOfLE h₁).asEquivalence]
  exact essentiallySmall_of_small_of_locallySmall _

/--
lemma `EssentiallySmall.of_functor` / 引理 `EssentiallySmall.of_functor`

English:
lemma EssentiallySmall.of_functor
  statement: (P : ObjectProperty C) (F : C ⥤ D)
  proof: by
  choose P₁ hP₁ x hP₁x hx using H₁.1
  choose P₂ hP₂ y hP₂y hy using fun Y => (H₂ Y).1
  let f : Subtype P -> Σ i : Subtype P₁, Subtype (P₂ i.1) := fun c =>
    ⟨⟨_, hP₁x _ _⟩, _, hP₂y _ c ⟨c.2, hx _ ⟨_, c.2, ⟨.refl _⟩⟩⟩⟩
  let g : (Σ i : Subtype P₁, Subtype (P₂ i.1)) -> C := fun i => i.2.1
  exact ⟨.ofObj g, inferInstance, fun X hX => ⟨_, ⟨f ⟨X, hX⟩⟩, hy _ _ _⟩⟩

中文:
引理 EssentiallySmall.of_functor
  结论: (P : ObjectProperty C) (F : C ⥤ D)
  证明: by
  choose P₁ hP₁ x hP₁x hx using H₁.1
  choose P₂ hP₂ y hP₂y hy using fun Y => (H₂ Y).1
  let f : Subtype P -> Σ i : Subtype P₁, Subtype (P₂ i.1) := fun c =>
    ⟨⟨_, hP₁x _ _⟩, _, hP₂y _ c ⟨c.2, hx _ ⟨_, c.2, ⟨.refl _⟩⟩⟩⟩
  let g : (Σ i : Subtype P₁, Subtype (P₂ i.1)) -> C := fun i => i.2.1
  exact ⟨.ofObj g, inferInstance, fun X hX => ⟨_, ⟨f ⟨X, hX⟩⟩, hy _ _ _⟩⟩

Depends on / 依赖: Subtype
-/
lemma EssentiallySmall.of_functor (P : ObjectProperty C) (F : C ⥤ D)
    (H₁ : ObjectProperty.EssentiallySmall.{w} (P.map F))
    (H₂ : forall Y : D, ObjectProperty.EssentiallySmall.{w} (P ⊓ (Nonempty <| F.obj · ≅ Y))) :
    ObjectProperty.EssentiallySmall.{w} P := by
  choose P₁ hP₁ x hP₁x hx using H₁.1
  choose P₂ hP₂ y hP₂y hy using fun Y => (H₂ Y).1
  let f : Subtype P -> Σ i : Subtype P₁, Subtype (P₂ i.1) := fun c =>
    ⟨⟨_, hP₁x _ _⟩, _, hP₂y _ c ⟨c.2, hx _ ⟨_, c.2, ⟨.refl _⟩⟩⟩⟩
  let g : (Σ i : Subtype P₁, Subtype (P₂ i.1)) -> C := fun i => i.2.1
  exact ⟨.ofObj g, inferInstance, fun X hX => ⟨_, ⟨f ⟨X, hX⟩⟩, hy _ _ _⟩⟩

/--
lemma `exists_equivalence_iff` / 引理 `exists_equivalence_iff`

English:
lemma exists_equivalence_iff
  given: (P : ObjectProperty C) [LocallySmall.{w'} C]
  proof: by
  refine ⟨fun ⟨J, _, ⟨e⟩⟩ => ?_, fun _ => ?_⟩
  · exact ⟨.ofObj (e.inverse ⋙ P.ι).obj, inferInstance,
      fun X hX => ⟨_, ⟨⟨(e.functor.obj ⟨X, hX⟩)⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩⟩
  · obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
    rw [← isEquivalence_ιOfLE_iff h₁] at h₂
    exact ⟨_, _, ⟨((ιOfLE h₁).asEquivalence.symm.trans
      (Shrink.equivalence.{w} Q.FullSubcategory)).trans (ShrinkHoms.equivalence.{w'} _)⟩⟩

中文:
引理 存在_equivalence_iff
  条件: (P : ObjectProperty C) [LocallySmall.{w'} C]
  证明: by
  refine ⟨fun ⟨J, _, ⟨e⟩⟩ => ?_, fun _ => ?_⟩
  · exact ⟨.ofObj (e.inverse ⋙ P.ι).obj, inferInstance,
      fun X hX => ⟨_, ⟨⟨(e.functor.obj ⟨X, hX⟩)⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩⟩
  · obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
    rw [← isEquivalence_ιOfLE_iff h₁] at h₂
    exact ⟨_, _, ⟨((ιOfLE h₁).asEquivalence.symm.trans
      (Shrink.equivalence.{w} Q.FullSubcategory)).trans (ShrinkHoms.equivalence.{w'} _)⟩⟩

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, FullSubcategory, Q.FullSubcategory, Shrink, Shrink.equivalence, ShrinkHoms, ShrinkHoms.equivalence, asEquivalence, asEquivalence.symm.trans, e.functor.obj, e.inverse, e.unitIso.app, equivalence, exists_small_le, functor, inverse, mapIso, unitIso
-/
lemma exists_equivalence_iff (P : ObjectProperty C) [LocallySmall.{w'} C] :
    (exists (J : Type w) (_ : Category.{w'} J), Nonempty (P.FullSubcategory ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨fun ⟨J, _, ⟨e⟩⟩ => ?_, fun _ => ?_⟩
  · exact ⟨.ofObj (e.inverse ⋙ P.ι).obj, inferInstance,
      fun X hX => ⟨_, ⟨⟨(e.functor.obj ⟨X, hX⟩)⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩⟩
  · obtain ⟨Q, _, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
    rw [← isEquivalence_ιOfLE_iff h₁] at h₂
    exact ⟨_, _, ⟨((ιOfLE h₁).asEquivalence.symm.trans
      (Shrink.equivalence.{w} Q.FullSubcategory)).trans (ShrinkHoms.equivalence.{w'} _)⟩⟩

end ObjectProperty

variable {C D : Type*} [Category* C] [Category* D]

/--
lemma `exists_equivalence_iff_of_locallySmall` / 引理 `exists_equivalence_iff_of_locallySmall`

English:
lemma exists_equivalence_iff_of_locallySmall
  given: [LocallySmall.{w'} C]
  proof: by
  rw [← ObjectProperty.exists_equivalence_iff]
  exact ⟨fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).trans e⟩⟩,
    fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).symm.trans e⟩⟩⟩

中文:
引理 存在_equivalence_iff_of_locallySmall
  条件: [LocallySmall.{w'} C]
  证明: by
  rw [← ObjectProperty.exists_equivalence_iff]
  exact ⟨fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).trans e⟩⟩,
    fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).symm.trans e⟩⟩⟩

Depends on / 依赖: ObjectProperty, ObjectProperty.exists_equivalence_iff, ObjectProperty.topEquivalence, exists_equivalence_iff, symm.trans, topEquivalence
-/
lemma exists_equivalence_iff_of_locallySmall [LocallySmall.{w'} C] :
    (exists (J : Type w) (_ : Category.{w'} J), Nonempty (C ≌ J)) ↔
      ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  rw [← ObjectProperty.exists_equivalence_iff]
  exact ⟨fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).trans e⟩⟩,
    fun ⟨J, _, ⟨e⟩⟩ => ⟨J, _, ⟨(ObjectProperty.topEquivalence C).symm.trans e⟩⟩⟩

/--
lemma `essentiallySmall_iff_objectPropertyEssentiallySmall_top` / 引理 `essentiallySmall_iff_objectPropertyEssentiallySmall_top`

English:
lemma essentiallySmall_iff_objectPropertyEssentiallySmall_top
  proof: by
  rw [← exists_equivalence_iff_of_locallySmall]
  exact ⟨fun _ => ⟨_, _, ⟨equivSmallModel.{w} C⟩⟩,
    fun ⟨C₀, _, ⟨e⟩⟩ => ⟨C₀, inferInstance, ⟨e⟩⟩⟩

中文:
引理 essentiallySmall_iff_objectPropertyEssentiallySmall_top
  证明: by
  rw [← exists_equivalence_iff_of_locallySmall]
  exact ⟨fun _ => ⟨_, _, ⟨equivSmallModel.{w} C⟩⟩,
    fun ⟨C₀, _, ⟨e⟩⟩ => ⟨C₀, inferInstance, ⟨e⟩⟩⟩

Depends on / 依赖: equivSmallModel, exists_equivalence_iff_of_locallySmall
-/
lemma essentiallySmall_iff_objectPropertyEssentiallySmall_top
    (C : Type u) [Category.{v} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C ↔ ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  rw [← exists_equivalence_iff_of_locallySmall]
  exact ⟨fun _ => ⟨_, _, ⟨equivSmallModel.{w} C⟩⟩,
    fun ⟨C₀, _, ⟨e⟩⟩ => ⟨C₀, inferInstance, ⟨e⟩⟩⟩

/--
lemma `essentiallySmall_iff_objectPropertyEssentiallySmall` / 引理 `essentiallySmall_iff_objectPropertyEssentiallySmall`

English:
lemma essentiallySmall_iff_objectPropertyEssentiallySmall
  proof: by
  wlog hC : LocallySmall.{w} C; · simp [essentiallySmall_iff, hC]
  simp only [hC, ← exists_equivalence_iff_of_locallySmall, true_and]
  refine ⟨fun H => H.1, fun H => ⟨H⟩⟩

中文:
引理 essentiallySmall_iff_objectPropertyEssentiallySmall
  证明: by
  wlog hC : LocallySmall.{w} C; · simp [essentiallySmall_iff, hC]
  simp only [hC, ← exists_equivalence_iff_of_locallySmall, true_and]
  refine ⟨fun H => H.1, fun H => ⟨H⟩⟩

Depends on / 依赖: LocallySmall, essentiallySmall_iff, exists_equivalence_iff_of_locallySmall, true_and
-/
lemma essentiallySmall_iff_objectPropertyEssentiallySmall :
    EssentiallySmall.{w} C ↔ LocallySmall.{w} C ∧
      ObjectProperty.EssentiallySmall.{w} (C := C) ⊤ := by
  wlog hC : LocallySmall.{w} C; · simp [essentiallySmall_iff, hC]
  simp only [hC, ← exists_equivalence_iff_of_locallySmall, true_and]
  refine ⟨fun H => H.1, fun H => ⟨H⟩⟩

/--
lemma `EssentiallySmall.of_functor` / 引理 `EssentiallySmall.of_functor`

English:
lemma EssentiallySmall.of_functor
  statement: (F : C ⥤ D)
  proof: by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  exact ⟨‹_›, .of_functor _ F (.of_le (Q := F.essImage)
    fun Y => by simp [ObjectProperty.map, Functor.essImage]) (by simpa)⟩

中文:
引理 EssentiallySmall.of_functor
  结论: (F : C ⥤ D)
  证明: by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  exact ⟨‹_›, .of_functor _ F (.of_le (Q := F.essImage)
    fun Y => by simp [ObjectProperty.map, Functor.essImage]) (by simpa)⟩
-/
lemma EssentiallySmall.of_functor (F : C ⥤ D)
    [LocallySmall.{w} C] (H₁ : ObjectProperty.EssentiallySmall.{w} F.essImage)
    (H₂ : forall Y : D, ObjectProperty.EssentiallySmall.{w} (Nonempty <| F.obj · ≅ Y)) :
    EssentiallySmall.{w} C := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall]
  exact ⟨‹_›, .of_functor _ F (.of_le (Q := F.essImage)
    fun Y => by simp [ObjectProperty.map, Functor.essImage]) (by simpa)⟩

end CategoryTheory
