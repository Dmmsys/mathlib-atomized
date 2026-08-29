/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Order.OrderIsoNat
public import Mathlib.CategoryTheory.Simple

/-!
# Artinian objects

We shall say that an object `X` in a category `C` is Artinian
(type class `IsArtinianObject X`) if the ordered type `Subobject X`
satisfies the descending chain condition. The corresponding property of
objects `isArtinianObject : ObjectProperty C` is always
closed under subobjects.

## Future work

* when `C` is an abelian category, relate `IsArtinianObject` in `C`
  with `IsNoetherianObject` in `Cᵒᵖ`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C]

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. This definition is a
term in `ObjectProperty C` which allows to study the stability
properties of Artinian objects. For statements regarding
specific objects, it is advisable to use the type class
`IsArtinianObject` instead. -/
@[stacks 0FCF]
/--
Definition of `isArtinianObject` / `isArtinianObject` 的定义

English:
definition isArtinianObject
  signature: : ObjectProperty C
  body: fun X => WellFoundedLT (Subobject X)

中文:
定义 isArtinianObject
  签名: : Object命题erty C
  定义体: fun X => WellFoundedLT (Subobject X)

Depends on / 依赖: Subobject, WellFoundedLT
-/
def isArtinianObject : ObjectProperty C :=
  fun X => WellFoundedLT (Subobject X)

variable (X Y : C)

/-- An object `X` in a category `C` is Artinian if `Subobject X`
satisfies the descending chain condition. -/
@[stacks 0FCF]
/--
Definition of `IsArtinianObject` / `IsArtinianObject` 的定义

English:
abbreviation IsArtinianObject
  signature: : Prop
  body: isArtinianObject.Is X

中文:
缩写 IsArtinianObject
  签名: : 命题
  定义体: isArtinianObject.Is X

Depends on / 依赖: isArtinianObject, isArtinianObject.Is
-/
abbrev IsArtinianObject : Prop := isArtinianObject.Is X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsArtinianObject
  signature: X] : WellFoundedLT (Subobject X)
  body: isArtinianObject.prop_of_is X

中文:
实例 [IsArtinianObject
  签名: X] : WellFoundedLT (Subobject X)
  定义体: isArtinianObject.prop_of_is X

Depends on / 依赖: isArtinianObject, isArtinianObject.prop_of_is, prop_of_is
-/
instance [IsArtinianObject X] : WellFoundedLT (Subobject X) :=
  isArtinianObject.prop_of_is X

/--
lemma `isArtinianObject_iff_antitone_chain_condition` / 引理 `isArtinianObject_iff_antitone_chain_condition`

English:
lemma isArtinianObject_iff_antitone_chain_condition
  proof: by
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [← wellFoundedGT_dual_iff]; rw [wellFoundedGT_iff_monotone_chain_condition]

中文:
引理 isArtinianObject_iff_antitone_chain_condition
  证明: by
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [← wellFoundedGT_dual_iff]; rw [wellFoundedGT_iff_monotone_chain_condition]

Depends on / 依赖: IsArtinianObject, ObjectProperty, ObjectProperty.is_iff, isArtinianObject, is_iff, wellFoundedGT_dual_iff, wellFoundedGT_iff_monotone_chain_condition
-/
lemma isArtinianObject_iff_antitone_chain_condition :
    IsArtinianObject X ↔ forall (f : Nat ->o (Subobject X)ᵒᵈ),
      exists (n : Nat), forall (m : Nat), n <= m -> f n = f m := by
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [← wellFoundedGT_dual_iff]; rw [wellFoundedGT_iff_monotone_chain_condition]

variable {X} in
/--
lemma `antitone_chain_condition_of_isArtinianObject` / 引理 `antitone_chain_condition_of_isArtinianObject`

English:
lemma antitone_chain_condition_of_isArtinianObject
  proof: (isArtinianObject_iff_antitone_chain_condition X).1 inferInstance f

中文:
引理 antitone_chain_condition_of_isArtinianObject
  证明: (isArtinianObject_iff_antitone_chain_condition X).1 inferInstance f

Depends on / 依赖: isArtinianObject_iff_antitone_chain_condition
-/
lemma antitone_chain_condition_of_isArtinianObject
    [IsArtinianObject X] (f : Nat ->o (Subobject X)ᵒᵈ) :
    exists (n : Nat), forall (m : Nat), n <= m -> f n = f m :=
  (isArtinianObject_iff_antitone_chain_condition X).1 inferInstance f

/--
lemma `isArtinianObject_iff_not_strictAnti` / 引理 `isArtinianObject_iff_not_strictAnti`

English:
lemma isArtinianObject_iff_not_strictAnti
  proof: by
  refine ⟨fun _ => not_strictAnti_of_wellFoundedLT, fun h => ?_⟩
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [WellFoundedLT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2 h)⟩

中文:
引理 isArtinianObject_iff_not_strictAnti
  证明: by
  refine ⟨fun _ => not_strictAnti_of_wellFoundedLT, fun h => ?_⟩
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [WellFoundedLT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2 h)⟩

Depends on / 依赖: IsArtinianObject, ObjectProperty, ObjectProperty.is_iff, RelEmbedding, RelEmbedding.wellFounded_iff_isEmpty, WellFoundedLT, f.map_rel_iff, f.toFun, isArtinianObject, isWellFounded_iff, is_iff, map_rel_iff, not_strictAnti_of_wellFoundedLT, wellFounded_iff_isEmpty
-/
lemma isArtinianObject_iff_not_strictAnti :
    IsArtinianObject X ↔ forall (f : Nat -> Subobject X), ¬ StrictAnti f := by
  refine ⟨fun _ => not_strictAnti_of_wellFoundedLT, fun h => ?_⟩
  dsimp only [IsArtinianObject]
  rw [ObjectProperty.is_iff]; rw [isArtinianObject]; rw [WellFoundedLT]; rw [isWellFounded_iff]; rw [RelEmbedding.wellFounded_iff_isEmpty]
  exact ⟨fun f => h f.toFun (fun a b h => f.map_rel_iff.2 h)⟩

variable {X} in
/--
lemma `not_strictAnti_of_isArtinianObject` / 引理 `not_strictAnti_of_isArtinianObject`

English:
lemma not_strictAnti_of_isArtinianObject
  proof: (isArtinianObject_iff_not_strictAnti X).1 inferInstance f

中文:
引理 not_strictAnti_of_isArtinianObject
  证明: (isArtinianObject_iff_not_strictAnti X).1 inferInstance f

Depends on / 依赖: isArtinianObject_iff_not_strictAnti
-/
lemma not_strictAnti_of_isArtinianObject
    [IsArtinianObject X] (f : Nat -> Subobject X) :
    ¬ StrictAnti f :=
  (isArtinianObject_iff_not_strictAnti X).1 inferInstance f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isArtinianObject_iff_isEventuallyConstant` / 引理 `isArtinianObject_iff_isEventuallyConstant`

English:
lemma isArtinianObject_iff_isEventuallyConstant
  proof: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver X).inverse.op ⋙
      (orderDualEquivalence _).inverse).monotone⟩
    refine ⟨n, fun m hm => ?_⟩
    rw [← isIso_unop_iff]; rw [MonoOver.isIso_iff

中文:
引理 isArtinianObject_iff_isEventuallyConstant
  证明: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver X).inverse.op ⋙
      (orderDualEquivalence _).inverse).monotone⟩
    refine ⟨n, fun m hm => ?_⟩
    rw [← isIso_unop_iff]; rw [MonoOver.isIso_iff

Depends on / 依赖: Eq.symm, F.monotone.functor, MonoOver, MonoOver.isIso_iff_subobjectMk_eq, Subobject, Subobject.equivMonoOver, Subobject.representative.op, equivMonoOver, functor, inverse, inverse.op, isArtinianObject_iff_antitone_chain_condition, isIso_if, isIso_iff_subobjectMk_eq, isIso_op_iff, isIso_unop_iff, leOfHom, monotone, orderDualEquivalence, representative
-/
lemma isArtinianObject_iff_isEventuallyConstant :
    IsArtinianObject X ↔ forall (F : Nat ⥤ (MonoOver X)ᵒᵖ),
      IsFiltered.IsEventuallyConstant F := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  refine ⟨fun h G => ?_, fun h F => ?_⟩
  · obtain ⟨n, hn⟩ := h ⟨_, (G ⋙ (Subobject.equivMonoOver X).inverse.op ⋙
      (orderDualEquivalence _).inverse).monotone⟩
    refine ⟨n, fun m hm => ?_⟩
    rw [← isIso_unop_iff]; rw [MonoOver.isIso_iff_subobjectMk_eq]
    exact (hn m (leOfHom hm)).symm
  · obtain ⟨n, hn⟩ := h (F.monotone.functor ⋙ (orderDualEquivalence _).functor ⋙
      Subobject.representative.op)
    refine ⟨n, fun m hm => Eq.symm ?_⟩
    simpa [isIso_op_iff, isIso_iff_of_reflects_iso, PartialOrder.isIso_iff_eq]
      using hn (homOfLE hm)

variable {X} in
/--
lemma `isEventuallyConstant_of_isArtinianObject` / 引理 `isEventuallyConstant_of_isArtinianObject`

English:
lemma isEventuallyConstant_of_isArtinianObject
  statement: [IsArtinianObject X]
  proof: (isArtinianObject_iff_isEventuallyConstant X).1 inferInstance F

中文:
引理 isEventuallyConstant_of_isArtinianObject
  结论: [IsArtinianObject X]
  证明: (isArtinianObject_iff_isEventuallyConstant X).1 inferInstance F

Depends on / 依赖: isArtinianObject_iff_isEventuallyConstant
-/
lemma isEventuallyConstant_of_isArtinianObject [IsArtinianObject X]
    (F : Nat ⥤ (MonoOver X)ᵒᵖ) : IsFiltered.IsEventuallyConstant F :=
  (isArtinianObject_iff_isEventuallyConstant X).1 inferInstance F

variable {X Y}

/--
lemma `isArtinianObject_of_isZero` / 引理 `isArtinianObject_of_isZero`

English:
lemma isArtinianObject_of_isZero
  given: (hX : IsZero X)
  statement: IsArtinianObject X
  proof: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

中文:
引理 isArtinianObject_of_isZero
  条件: (hX : IsZero X)
  结论: IsArtinianObject X
  证明: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

Depends on / 依赖: Subobject, Subobject.subsingleton_of_isZero, Subsingleton, Subsingleton.elim, isArtinianObject_iff_antitone_chain_condition, subsingleton_of_isZero
-/
lemma isArtinianObject_of_isZero (hX : IsZero X) : IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  have := Subobject.subsingleton_of_isZero hX
  intro f
  exact ⟨0, fun m hm => Subsingleton.elim _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] : (isArtinianObject (C := C)).ContainsZero where
  body: ⟨0, isZero_zero _, by
    rw [← isArtinianObject.is_iff]
    exact isArtinianObject_of_isZero (isZero_zero C)⟩

中文:
实例 [HasZeroObject
  签名: C] : (isArtinianObject (C := C)).ContainsZero where
  定义体: ⟨0, isZero_zero _, by
    rw [← isArtinianObject.is_iff]
    exact isArtinianObject_of_isZero (isZero_zero C)⟩

Depends on / 依赖: ContainsZero
-/
instance [HasZeroObject C] : (isArtinianObject (C := C)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    rw [← isArtinianObject.is_iff]
    exact isArtinianObject_of_isZero (isZero_zero C)⟩

/--
lemma `isArtinianObject_of_mono` / 引理 `isArtinianObject_of_mono`

English:
lemma isArtinianObject_of_mono
  given: (i : X ⟶ Y) [Mono i] [IsArtinianObject Y]
  proof: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject
    ⟨fun n => (Subobject.map i).obj (f n),
      fun _ _ h => (Subobject.map i).monotone (f.2 h)⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

中文:
引理 isArtinianObject_of_mono
  条件: (i : X ⟶ Y) [Mono i] [IsArtinianObject Y]
  证明: by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject
    ⟨fun n => (Subobject.map i).obj (f n),
      fun _ _ h => (Subobject.map i).monotone (f.2 h)⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

Depends on / 依赖: Subobject, Subobject.map, Subobject.map_obj_injective, antitone_chain_condition_of_isArtinianObject, isArtinianObject_iff_antitone_chain_condition, map_obj_injective, monotone
-/
lemma isArtinianObject_of_mono (i : X ⟶ Y) [Mono i] [IsArtinianObject Y] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject
    ⟨fun n => (Subobject.map i).obj (f n),
      fun _ _ h => (Subobject.map i).monotone (f.2 h)⟩
  exact ⟨n, fun m hm => Subobject.map_obj_injective i (hn m hm)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isArtinianObject (C := C)).IsClosedUnderSubobjects
  body: by
    rw [← isArtinianObject.is_iff] at hY ⊢
    exact isArtinianObject_of_mono f

中文:
实例 :
  签名: (isArtinianObject (C := C)).IsClosedUnderSubobjects
  定义体: by
    rw [← isArtinianObject.is_iff] at hY ⊢
    exact isArtinianObject_of_mono f

Depends on / 依赖: IsClosedUnderSubobjects
-/
instance : (isArtinianObject (C := C)).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [← isArtinianObject.is_iff] at hY ⊢
    exact isArtinianObject_of_mono f

open Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

/--
theorem `exists_simple_subobject` / 定理 `exists_simple_subobject`

English:
theorem exists_simple_subobject
  given: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  proof: by
  have : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩

中文:
定理 exists_simple_subobject
  条件: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  证明: by
  have : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩

Depends on / 依赖: IsAtomic, IsAtomic.eq_bot_or_exists_atom_le, Nontrivial, Subobject, eq_bot_or_exists_atom_le, nontrivial_of_not_isZero, resolve_left, subobject_simple_iff_isAtom, top_ne_bot
-/
theorem exists_simple_subobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    exists Y : Subobject X, Simple (Y : C) := by
  have : Nontrivial (Subobject X) := nontrivial_of_not_isZero h
  obtain ⟨Y, s⟩ := (IsAtomic.eq_bot_or_exists_atom_le (⊤ : Subobject X)).resolve_left top_ne_bot
  exact ⟨Y, (subobject_simple_iff_isAtom _).mpr s.1⟩

/--
Definition of `simpleSubobject` / `simpleSubobject` 的定义

English:
definition simpleSubobject
  signature: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  body: (exists_simple_subobject h).choose

中文:
定义 simpleSubobject
  签名: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  定义体: (exists_simple_subobject h).choose

Depends on / 依赖: exists_simple_subobject
-/
noncomputable def simpleSubobject {X : C} [IsArtinianObject X] (h : ¬IsZero X) : C :=
  (exists_simple_subobject h).choose

/--
Definition of `simpleSubobjectArrow` / `simpleSubobjectArrow` 的定义

English:
definition simpleSubobjectArrow
  signature: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  body: (exists_simple_subobject h).choose.arrow

中文:
定义 simpleSubobjectArrow
  签名: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  定义体: (exists_simple_subobject h).choose.arrow

Depends on / 依赖: choose.arrow, exists_simple_subobject
-/
noncomputable def simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    simpleSubobject h ⟶ X :=
  (exists_simple_subobject h).choose.arrow

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mono_simpleSubobjectArrow` / 实例 `mono_simpleSubobjectArrow`

English:
instance mono_simpleSubobjectArrow
  signature: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  body: by
  dsimp only [simpleSubobjectArrow]
  infer_instance

中文:
实例 mono_simpleSubobjectArrow
  签名: {X : C} [IsArtinianObject X] (h : ¬IsZero X)
  定义体: by
  dsimp only [simpleSubobjectArrow]
  infer_instance

Depends on / 依赖: infer_instance, simpleSubobjectArrow
-/
instance mono_simpleSubobjectArrow {X : C} [IsArtinianObject X] (h : ¬IsZero X) :
    Mono (simpleSubobjectArrow h) := by
  dsimp only [simpleSubobjectArrow]
  infer_instance

instance {X : C} [IsArtinianObject X] (h : ¬IsZero X) : Simple (simpleSubobject h) :=
  (exists_simple_subobject h).choose_spec

end CategoryTheory
