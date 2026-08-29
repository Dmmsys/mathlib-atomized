/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Small classes of morphisms

A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is.

-/

public section

universe w t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is. -/
@[pp_with_univ]
/--
Definition of `IsSmall` / `IsSmall` 的定义

English:
class IsSmall
  parameters: : Prop where
  axioms and operations (1):
    - small_toSet : Small.{w} W.toSet

中文:
类 是Small
  参数: : 命题 where
  公理与运算 (1 个):
    - small_toSet : Small.{w} W.toSet
-/
class IsSmall : Prop where
  small_toSet : Small.{w} W.toSet

attribute [instance] IsSmall.small_toSet

/--
Instance `isSmall_ofHoms` / 实例 `isSmall_ofHoms`

English:
instance isSmall_ofHoms
  signature: {ι : Type t} [Small.{w} ι] {A B : ι -> C} (f : forall i, A i ⟶ B i)
  body: by
  let φ (i : ι) : (ofHoms f).toSet := ⟨Arrow.mk (f i), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  exact ⟨small_of_surjective hφ⟩

中文:
实例 isSmall_ofHoms
  签名: {ι : 类型 t} [Small.{w} ι] {A B : ι -> C} (f : 对任意 i, A i ⟶ B i)
  定义体: by
  let φ (i : ι) : (ofHoms f).toSet := ⟨Arrow.mk (f i), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  exact ⟨small_of_surjective hφ⟩

Depends on / 依赖: Arrow.mk, Function, Function.Surjective, Surjective, ofHoms, small_of_surjective
-/
instance isSmall_ofHoms {ι : Type t} [Small.{w} ι] {A B : ι -> C} (f : forall i, A i ⟶ B i) :
    IsSmall.{w} (ofHoms f) := by
  let φ (i : ι) : (ofHoms f).toSet := ⟨Arrow.mk (f i), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  exact ⟨small_of_surjective hφ⟩

/--
lemma `isSmall_iff_eq_ofHoms` / 引理 `isSmall_iff_eq_ofHoms`

English:
lemma isSmall_iff_eq_ofHoms
  proof: by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i => ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_e

中文:
引理 isSmall_iff_eq_ofHoms
  证明: by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i => ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_e

Depends on / 依赖: Arrow.mk_eq, Shrink, Subtype, Subtype.coe_prop, W.arrow_mk_mem_toSet_iff, W.toSet, arrow_mk_mem_toSet_iff, coe_prop, equivShrink, infer_instance, mk_eq, ofHoms_iff
-/
lemma isSmall_iff_eq_ofHoms :
    IsSmall.{w} W ↔ exists (ι : Type w) (A B : ι -> C) (f : forall i, A i ⟶ B i),
      W = ofHoms f := by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i => ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_eq, Subtype.coe_prop]
  · rintro ⟨_, _, _, _, rfl⟩
    infer_instance

/--
Instance `isSmall_iSup` / 实例 `isSmall_iSup`

English:
instance isSmall_iSup
  signature: {α : Type*} (W : α -> MorphismProperty C)
  body: by
    rw [toSet_iSup]
    refine small_of_surjective (f := fun (⟨i, f⟩ : Σ i, (W i).toSet) =>
      ⟨f, by rw [Set.mem_iUnion]; exact ⟨i, f.prop⟩⟩) ?_
    rintro ⟨f, hf⟩
    simp only [Set.mem_iUnion] at hf
    obtain ⟨i, hf⟩ := hf
    exact ⟨⟨i, ⟨_, hf⟩⟩, rfl⟩

中文:
实例 isSmall_iSup
  签名: {α : 类型} (W : α -> MorphismProperty C)
  定义体: by
    rw [toSet_iSup]
    refine small_of_surjective (f := fun (⟨i, f⟩ : Σ i, (W i).toSet) =>
      ⟨f, by rw [Set.mem_iUnion]; exact ⟨i, f.prop⟩⟩) ?_
    rintro ⟨f, hf⟩
    simp only [Set.mem_iUnion] at hf
    obtain ⟨i, hf⟩ := hf
    exact ⟨⟨i, ⟨_, hf⟩⟩, rfl⟩

Depends on / 依赖: Set.mem_iUnion, f.prop, mem_iUnion, small_of_surjective, toSet_iSup
-/
instance isSmall_iSup {α : Type*} (W : α -> MorphismProperty C)
    [Small.{w} α] [forall a, IsSmall.{w} (W a)] :
    IsSmall.{w} (iSup W) where
  small_toSet := by
    rw [toSet_iSup]
    refine small_of_surjective (f := fun (⟨i, f⟩ : Σ i, (W i).toSet) =>
      ⟨f, by rw [Set.mem_iUnion]; exact ⟨i, f.prop⟩⟩) ?_
    rintro ⟨f, hf⟩
    simp only [Set.mem_iUnion] at hf
    obtain ⟨i, hf⟩ := hf
    exact ⟨⟨i, ⟨_, hf⟩⟩, rfl⟩

instance {α : Type t} [Small.{w} α] (W : α -> MorphismProperty C) [forall i, IsSmall.{w} (W i)] :
    IsSmall.{w} (⨆ i, W i) := by
  choose α A B f hf using fun i => (isSmall_iff_eq_ofHoms.{w} (W i)).1 inferInstance
  simp only [hf, iSup_ofHoms]
  infer_instance

end MorphismProperty

end CategoryTheory
