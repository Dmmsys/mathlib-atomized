/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.CompleteLattice.Basic

/-!
# ObjectProperty is a complete lattice

-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

example : CompleteLattice (ObjectProperty C) := inferInstance

section

variable (P Q : ObjectProperty C) (X : C)

/--
lemma `prop_inf_iff` / 引理 `prop_inf_iff`

English:
lemma prop_inf_iff
  statement: (P ⊓ Q) X ↔ P X ∧ Q X
  proof: Iff.rfl

中文:
引理 prop_inf_iff
  结论: (P ⊓ Q) X ↔ P X ∧ Q X
  证明: Iff.rfl
-/
@[simp high] lemma prop_inf_iff : (P ⊓ Q) X ↔ P X ∧ Q X := Iff.rfl

/--
lemma `prop_sup_iff` / 引理 `prop_sup_iff`

English:
lemma prop_sup_iff
  statement: (P ⊔ Q) X ↔ P X ∨ Q X
  proof: Iff.rfl

中文:
引理 prop_sup_iff
  结论: (P ⊔ Q) X ↔ P X ∨ Q X
  证明: Iff.rfl
-/
@[simp high] lemma prop_sup_iff : (P ⊔ Q) X ↔ P X ∨ Q X := Iff.rfl

/--
Instance `nonempty_sup_left` / 实例 `nonempty_sup_left`

English:
instance nonempty_sup_left
  signature: [P.Nonempty]
  body: nonempty_of_prop (Or.inl P.prop_arbitrary)

中文:
实例 nonempty_sup_left
  签名: [P.非空]
  定义体: nonempty_of_prop (Or.inl P.prop_arbitrary)

Depends on / 依赖: Or.inl, P.prop_arbitrary, nonempty_of_prop, prop_arbitrary
-/
instance nonempty_sup_left [P.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inl P.prop_arbitrary)

/--
Instance `nonempty_sup_right` / 实例 `nonempty_sup_right`

English:
instance nonempty_sup_right
  signature: [Q.Nonempty]
  body: nonempty_of_prop (Or.inr Q.prop_arbitrary)

中文:
实例 nonempty_sup_right
  签名: [Q.非空]
  定义体: nonempty_of_prop (Or.inr Q.prop_arbitrary)

Depends on / 依赖: Or.inr, Q.prop_arbitrary, nonempty_of_prop, prop_arbitrary
-/
instance nonempty_sup_right [Q.Nonempty] : (P ⊔ Q).Nonempty :=
  nonempty_of_prop (Or.inr Q.prop_arbitrary)

/--
Instance `nonempty_top` / 实例 `nonempty_top`

English:
instance nonempty_top
  signature: [Nonempty C]
  body: nonempty_of_prop (X := Classical.arbitrary C) (by trivial)

中文:
实例 nonempty_top
  签名: [非空 C]
  定义体: nonempty_of_prop (X := Classical.arbitrary C) (by trivial)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, nonempty_of_prop
-/
instance nonempty_top [Nonempty C] : (⊤ : ObjectProperty C).Nonempty :=
  nonempty_of_prop (X := Classical.arbitrary C) (by trivial)

/--
lemma `isoClosure_sup` / 引理 `isoClosure_sup`

English:
lemma isoClosure_sup
  statement: (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure
  proof: by
  ext X
  simp only [prop_sup_iff]
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_sup_iff] at hY
    obtain hY | hY := hY
    · exact Or.inl ⟨Y, hY, ⟨e⟩⟩
    · exact Or.inr ⟨Y, hY, ⟨e⟩⟩
  · rintro (hY | hY)
    · exact monotone_isoClosure le_sup_left _ hY
    · exact monotone_isoClosur

中文:
引理 isoClosure_sup
  结论: (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure
  证明: by
  ext X
  simp only [prop_sup_iff]
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_sup_iff] at hY
    obtain hY | hY := hY
    · exact Or.inl ⟨Y, hY, ⟨e⟩⟩
    · exact Or.inr ⟨Y, hY, ⟨e⟩⟩
  · rintro (hY | hY)
    · exact monotone_isoClosure le_sup_left _ hY
    · exact monotone_isoClosur

Depends on / 依赖: Or.inl, Or.inr, le_sup_left, le_sup_right, monotone_isoClosure, prop_sup_iff
-/
lemma isoClosure_sup : (P ⊔ Q).isoClosure = P.isoClosure ⊔ Q.isoClosure := by
  ext X
  simp only [prop_sup_iff]
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_sup_iff] at hY
    obtain hY | hY := hY
    · exact Or.inl ⟨Y, hY, ⟨e⟩⟩
    · exact Or.inr ⟨Y, hY, ⟨e⟩⟩
  · rintro (hY | hY)
    · exact monotone_isoClosure le_sup_left _ hY
    · exact monotone_isoClosure le_sup_right _ hY

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: [Q.IsClosedUnderIsomorphisms]
  body: by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_sup, isoClosure_eq_self]

中文:
实例 [P.在同构下封闭]
  签名: [Q.在同构下封闭]
  定义体: by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_sup, isoClosure_eq_self]

Depends on / 依赖: isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_eq_self, isoClosure_sup
-/
instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    (P ⊔ Q).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_sup, isoClosure_eq_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: [Q.IsClosedUnderIsomorphisms]
  body: ⟨IsClosedUnderIsomorphisms.of_iso e h.1, IsClosedUnderIsomorphisms.of_iso e h.2⟩

中文:
实例 [P.在同构下封闭]
  签名: [Q.在同构下封闭]
  定义体: ⟨IsClosedUnderIsomorphisms.of_iso e h.1, IsClosedUnderIsomorphisms.of_iso e h.2⟩

Depends on / 依赖: IsClosedUnderIsomorphisms, IsClosedUnderIsomorphisms.of_iso, of_iso
-/
instance [P.IsClosedUnderIsomorphisms] [Q.IsClosedUnderIsomorphisms] :
    IsClosedUnderIsomorphisms (P ⊓ Q) where
  of_iso e h := ⟨IsClosedUnderIsomorphisms.of_iso e h.1, IsClosedUnderIsomorphisms.of_iso e h.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderIsomorphisms (⊥ : ObjectProperty C)
  body: h

中文:
实例 :
  签名: 在同构下封闭 (⊥ : ObjectProperty C)
  定义体: h
-/
instance : IsClosedUnderIsomorphisms (⊥ : ObjectProperty C) where
  of_iso _ h := h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedUnderIsomorphisms (⊤ : ObjectProperty C)
  body: by simp

中文:
实例 :
  签名: 在同构下封闭 (⊤ : ObjectProperty C)
  定义体: by simp
-/
instance : IsClosedUnderIsomorphisms (⊤ : ObjectProperty C) where
  of_iso := by simp

end

section

variable {α : Sort*} (P : α -> ObjectProperty C) (X : C)

/--
lemma `prop_iSup_iff` / 引理 `prop_iSup_iff`

English:
lemma prop_iSup_iff
  proof: by simp

中文:
引理 prop_iSup_iff
  证明: by simp

Depends on / 依赖: isLE_of_isZero, isZero_zero, t.isLE_of_isZero
-/
@[simp high] lemma prop_iSup_iff :
    (⨆ (a : α), P a) X ↔ exists (a : α), P a X := by simp

/--
lemma `nonempty_iSup` / 引理 `nonempty_iSup`

English:
lemma nonempty_iSup
  given: (a : α) [(P a).Nonempty]
  statement: (⨆ a, P a).Nonempty
  proof: nonempty_of_prop ((prop_iSup_iff P _).mpr ⟨a, (P a).prop_arbitrary⟩)

中文:
引理 nonempty_iSup
  条件: (a : α) [(P a).非空]
  结论: (⨆ a, P a).非空
  证明: nonempty_of_prop ((prop_iSup_iff P _).mpr ⟨a, (P a).prop_arbitrary⟩)

Depends on / 依赖: isGE_of_isZero, isZero_zero, nonempty_of_prop, prop_arbitrary, prop_iSup_iff, t.isGE_of_isZero
-/
lemma nonempty_iSup (a : α) [(P a).Nonempty] : (⨆ a, P a).Nonempty :=
  nonempty_of_prop ((prop_iSup_iff P _).mpr ⟨a, (P a).prop_arbitrary⟩)

/--
lemma `isoClosure_iSup` / 引理 `isoClosure_iSup`

English:
lemma isoClosure_iSup
  proof: by
  refine le_antisymm ?_ ?_
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hY ⊢
    obtain ⟨a, hY⟩ := hY
    exact ⟨a, _, hY, ⟨e⟩⟩
  · simp only [iSup_le_iff]
    intro a
    rw [isoClosure_le_iff]
    exact (le_iSup P a).trans (le_isoClosure _)

中文:
引理 isoClosure_iSup
  证明: by
  refine le_antisymm ?_ ?_
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hY ⊢
    obtain ⟨a, hY⟩ := hY
    exact ⟨a, _, hY, ⟨e⟩⟩
  · simp only [iSup_le_iff]
    intro a
    rw [isoClosure_le_iff]
    exact (le_iSup P a).trans (le_isoClosure _)

Depends on / 依赖: iSup_le_iff, isoClosure_le_iff, le_antisymm, le_iSup, le_isoClosure, prop_iSup_iff
-/
lemma isoClosure_iSup :
    ((⨆ (a : α), P a)).isoClosure = ⨆ (a : α), (P a).isoClosure := by
  refine le_antisymm ?_ ?_
  · rintro X ⟨Y, hY, ⟨e⟩⟩
    simp only [prop_iSup_iff] at hY ⊢
    obtain ⟨a, hY⟩ := hY
    exact ⟨a, _, hY, ⟨e⟩⟩
  · simp only [iSup_le_iff]
    intro a
    rw [isoClosure_le_iff]
    exact (le_iSup P a).trans (le_isoClosure _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: a, (P a).IsClosedUnderIsomorphisms] :
  body: by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self,
    isoClosure_iSup, isoClosure_eq_self]

中文:
实例 [对任意
  签名: a, (P a).在同构下封闭] :
  定义体: by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self,
    isoClosure_iSup, isoClosure_eq_self]

Depends on / 依赖: isClosedUnderIsomorphisms_iff_isoClosure_eq_self, isoClosure_eq_self, isoClosure_iSup
-/
instance [forall a, (P a).IsClosedUnderIsomorphisms] :
    ((⨆ (a : α), P a)).IsClosedUnderIsomorphisms := by
  simp only [isClosedUnderIsomorphisms_iff_isoClosure_eq_self,
    isoClosure_iSup, isoClosure_eq_self]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: a, (P a).IsClosedUnderIsomorphisms] :
  body: by
    simp only [iInf_apply, iInf_Prop_eq] at h ⊢
    intro a
    exact (P a).prop_of_iso e (h a)

中文:
实例 [对任意
  签名: a, (P a).在同构下封闭] :
  定义体: by
    simp only [iInf_apply, iInf_Prop_eq] at h ⊢
    intro a
    exact (P a).prop_of_iso e (h a)

Depends on / 依赖: iInf_Prop_eq, iInf_apply, infer_instance, prop_of_iso
-/
instance [forall a, (P a).IsClosedUnderIsomorphisms] :
    ((⨅ (a : α), P a)).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [iInf_apply, iInf_Prop_eq] at h ⊢
    intro a
    exact (P a).prop_of_iso e (h a)

end

@[push]
/--
lemma `ne_bot_iff_exists` / 引理 `ne_bot_iff_exists`

English:
lemma ne_bot_iff_exists
  given: (P : ObjectProperty C)
  statement: ¬ P = ⊥ ↔ exists X, P X
  proof: by
  simp [← le_bot_iff, not_le_iff_exists]

中文:
引理 ne_bot_iff_存在
  条件: (P : ObjectProperty C)
  结论: ¬ P = ⊥ ↔ 存在 X, P X
  证明: by
  simp [← le_bot_iff, not_le_iff_exists]

Depends on / 依赖: le_bot_iff, not_le_iff_exists
-/
lemma ne_bot_iff_exists (P : ObjectProperty C) : ¬ P = ⊥ ↔ exists X, P X := by
  simp [← le_bot_iff, not_le_iff_exists]

/--
lemma `nonempty_iff_ne_bot` / 引理 `nonempty_iff_ne_bot`

English:
lemma nonempty_iff_ne_bot
  given: (P : ObjectProperty C)
  statement: P.Nonempty ↔ ¬ P = ⊥
  proof: by
  rw [ne_bot_iff_exists]; rw [nonempty_iff]

@[push]

中文:
引理 nonempty_iff_ne_bot
  条件: (P : ObjectProperty C)
  结论: P.非空 ↔ ¬ P = ⊥
  证明: by
  rw [ne_bot_iff_exists]; rw [nonempty_iff]

@[push]

Depends on / 依赖: ne_bot_iff_exists, nonempty_iff
-/
lemma nonempty_iff_ne_bot (P : ObjectProperty C) : P.Nonempty ↔ ¬ P = ⊥ := by
  rw [ne_bot_iff_exists]; rw [nonempty_iff]

@[push]
/--
lemma `not_nonempty_iff_eq_bot` / 引理 `not_nonempty_iff_eq_bot`

English:
lemma not_nonempty_iff_eq_bot
  given: (P : ObjectProperty C)
  statement: ¬ P.Nonempty ↔ P = ⊥
  proof: by
  rw [P.nonempty_iff_ne_bot]; rw [not_not]

@[simp]

中文:
引理 not_nonempty_iff_eq_bot
  条件: (P : ObjectProperty C)
  结论: ¬ P.非空 ↔ P = ⊥
  证明: by
  rw [P.nonempty_iff_ne_bot]; rw [not_not]

@[simp]

Depends on / 依赖: P.nonempty_iff_ne_bot, nonempty_iff_ne_bot, not_not
-/
lemma not_nonempty_iff_eq_bot (P : ObjectProperty C) : ¬ P.Nonempty ↔ P = ⊥ := by
  rw [P.nonempty_iff_ne_bot]; rw [not_not]

@[simp]
/--
lemma `ι_map_top` / 引理 `ι_map_top`

English:
lemma ι_map_top
  given: (P : ObjectProperty C)
  proof: by
  ext X
  constructor
  · rintro ⟨⟨Y, hY⟩, _, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, by simp, ⟨e.symm⟩⟩

中文:
引理 ι_map_top
  条件: (P : ObjectProperty C)
  证明: by
  ext X
  constructor
  · rintro ⟨⟨Y, hY⟩, _, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, by simp, ⟨e.symm⟩⟩

Depends on / 依赖: e.symm
-/
lemma ι_map_top (P : ObjectProperty C) :
    (⊤ : ObjectProperty _).map P.ι = P.isoClosure := by
  ext X
  constructor
  · rintro ⟨⟨Y, hY⟩, _, ⟨e⟩⟩
    exact ⟨Y, hY, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, by simp, ⟨e.symm⟩⟩

end CategoryTheory.ObjectProperty
