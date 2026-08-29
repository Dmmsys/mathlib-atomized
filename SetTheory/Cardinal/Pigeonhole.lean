/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Infinite pigeonhole principle

This file proves variants of the infinite pigeonhole principle.

## TODO

Generalize universes of results.
-/

public section

open Order Ordinal Set

universe u

namespace Cardinal

/--
theorem `infinite_pigeonhole` / 定理 `infinite_pigeonhole`

English:
theorem infinite_pigeonhole
  given: {β α : Type u} (f : β -> α) (h₁ : ℵ₀ <= #β) (h₂ : #α < (#β).ord.cof)
  proof: by
  have : exists a, #β <= #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ]; rw [← iUnion_of_singleton]; rw [preimage_iUnion]
    exact
mk_iUnion_le_sum_mk.trans_lt (sum_le_mk_mul_iSup _).trans_lt
        mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt_of

中文:
定理 infinite_pigeonhole
  条件: {β α : 类型u} (f : β -> α) (h₁ : ℵ₀ <= #β) (h₂ : #α < (#β).ord.cof)
  证明: by
  have : exists a, #β <= #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ]; rw [← iUnion_of_singleton]; rw [preimage_iUnion]
    exact
mk_iUnion_le_sum_mk.trans_lt (sum_le_mk_mul_iSup _).trans_lt
        mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt_of

Depends on / 依赖: antisymm, cof_ord_le, h.antisymm, iSup_lt_of_lt_cof_ord, iUnion_of_singleton, le_mk_iff_exists_set, mk_iUnion_le_sum_mk, mk_iUnion_le_sum_mk.trans_lt, mk_univ, mk_univ.not_lt, mul_lt_of_lt, not_lt, preimage_iUnion, preimage_univ, sum_le_mk_mul_iSup, trans_le, trans_lt
-/
theorem infinite_pigeonhole {β α : Type u} (f : β -> α) (h₁ : ℵ₀ <= #β) (h₂ : #α < (#β).ord.cof) :
    exists a : α, #(f ⁻¹' {a}) = #β := by
  have : exists a, #β <= #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ]; rw [← iUnion_of_singleton]; rw [preimage_iUnion]
    exact
mk_iUnion_le_sum_mk.trans_lt (sum_le_mk_mul_iSup _).trans_lt
        mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt_of_lt_cof_ord h₂ h)
  obtain ⟨x, h⟩ := this
  refine ⟨x, h.antisymm' ?_⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/--
theorem `infinite_pigeonhole_card` / 定理 `infinite_pigeonhole_card`

English:
theorem infinite_pigeonhole_card
  statement: {β α : Type u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β)
  proof: by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := infinite_pigeonhole (f ∘ Subtype.val : s -> α) h₁ h₂
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

中文:
定理 infinite_pigeonhole_card
  结论: {β α : 类型u} (f : β -> α) (θ : 基数) (hθ : θ <= #β)
  证明: by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := infinite_pigeonhole (f ∘ Subtype.val : s -> α) h₁ h₂
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, infinite_pigeonhole, le_mk_iff_exists_set, mk_preimage_of_injective, preimage_comp, val_injective
-/
theorem infinite_pigeonhole_card {β α : Type u} (f : β -> α) (θ : Cardinal) (hθ : θ <= #β)
    (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.cof) : exists a : α, θ <= #(f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := infinite_pigeonhole (f ∘ Subtype.val : s -> α) h₁ h₂
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

/--
theorem `infinite_pigeonhole_set` / 定理 `infinite_pigeonhole_set`

English:
theorem infinite_pigeonhole_set
  statement: {β α : Type u} {s : Set β} (f : s -> α) (θ : Cardinal)
  proof: by
  obtain ⟨a, ha⟩ := infinite_pigeonhole_card f θ hθ h₁ h₂
  refine ⟨a, { x | exists h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp

中文:
定理 infinite_pigeonhole_set
  结论: {β α : 类型u} {s : 集合 β} (f : s -> α) (θ : 基数)
  证明: by
  obtain ⟨a, ha⟩ := infinite_pigeonhole_card f θ hθ h₁ h₂
  refine ⟨a, { x | exists h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp

Depends on / 依赖: Equiv.subtypeSubtypeEquivSubtypeExists, Equiv.trans, Quotient, Quotient.sound, coe_eq_subtype, ge_of_eq, ha.trans, infinite_pigeonhole_card, mem_ofPred_eq, mem_preimage, mem_singleton_iff, subtypeSubtypeEquivSubtypeExists
-/
theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s -> α) (θ : Cardinal)
    (hθ : θ <= #s) (h₁ : ℵ₀ <= θ) (h₂ : #α < θ.ord.cof) :
    exists (a : α) (t : Set β) (h : t subseteq s), θ <= #t ∧ forall ⦃x⦄ (hx : x in t), f ⟨x, h hx⟩ = a := by
  obtain ⟨a, ha⟩ := infinite_pigeonhole_card f θ hθ h₁ h₂
  refine ⟨a, { x | exists h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_ofPred_eq]
    rfl
  rintro x ⟨_, hx'⟩; exact hx'

/--
theorem `infinite_pigeonhole_card_lt` / 定理 `infinite_pigeonhole_card_lt`

English:
theorem infinite_pigeonhole_card_lt
  given: {β α : Type u} (f : β -> α) (h : #α < #β) (hβ : ℵ₀ <= #β)
  proof: by
  simp_rw [← succ_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card f ℵ₀ hβ le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
    exact ⟨a, ha.trans' (succ_le_of_lt hα)⟩
  · exact infinite_pigeonhole_card f (succ #α) (succ_le_of_lt h) (hα.trans (le_succ _)

中文:
定理 infinite_pigeonhole_card_lt
  条件: {β α : 类型u} (f : β -> α) (h : #α < #β) (hβ : ℵ₀ <= #β)
  证明: by
  simp_rw [← succ_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card f ℵ₀ hβ le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
    exact ⟨a, ha.trans' (succ_le_of_lt hα)⟩
  · exact infinite_pigeonhole_card f (succ #α) (succ_le_of_lt h) (hα.trans (le_succ _)

Depends on / 依赖: cof_ord, ha.trans, infinite_pigeonhole_card, isRegular_aleph0, isRegular_aleph0.cof_ord, isRegular_succ, le_rfl, le_succ, lt_or_ge, lt_succ, simp_rw, succ_le_iff, succ_le_of_lt, trans_le
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β -> α) (h : #α < #β) (hβ : ℵ₀ <= #β) :
    exists a : α, #α < #(f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card f ℵ₀ hβ le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
    exact ⟨a, ha.trans' (succ_le_of_lt hα)⟩
  · exact infinite_pigeonhole_card f (succ #α) (succ_le_of_lt h) (hα.trans (le_succ _))
      ((lt_succ _).trans_le (isRegular_succ hα).2.ge)

/--
theorem `exists_infinite_fiber` / 定理 `exists_infinite_fiber`

English:
theorem exists_infinite_fiber
  given: {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite β]
  proof: by
  simp_rw [Cardinal.infinite_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₀ (aleph0_le_mk β) le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    exact ⟨a, hα.trans ha.le⟩

中文:
定理 存在_infinite_fiber
  条件: {β α : 类型u} (f : β -> α) (h : #α < #β) [无限 β]
  证明: by
  simp_rw [Cardinal.infinite_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₀ (aleph0_le_mk β) le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    exact ⟨a, hα.trans ha.le⟩

Depends on / 依赖: Cardinal, Cardinal.infinite_iff, aleph0_le_mk, cof_ord, ha.le, infinite_iff, infinite_pigeonhole_card, infinite_pigeonhole_card_lt, isRegular_aleph0, isRegular_aleph0.cof_ord, le_rfl, lt_or_ge, simp_rw
-/
theorem exists_infinite_fiber {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite β] :
    exists a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₀ (aleph0_le_mk β) le_rfl
      (by rwa [isRegular_aleph0.cof_ord])
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    exact ⟨a, hα.trans ha.le⟩

/--
theorem `exists_infinite_fiber'` / 定理 `exists_infinite_fiber'`

English:
theorem exists_infinite_fiber'
  given: {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite α]
  proof: by
  suffices Infinite β from exists_infinite_fiber f h
  exact .of_cardinalMk_le h.le

中文:
定理 存在_infinite_fiber'
  条件: {β α : 类型u} (f : β -> α) (h : #α < #β) [无限 α]
  证明: by
  suffices Infinite β from exists_infinite_fiber f h
  exact .of_cardinalMk_le h.le

Depends on / 依赖: Infinite, exists_infinite_fiber, h.le, of_cardinalMk_le
-/
theorem exists_infinite_fiber' {β α : Type u} (f : β -> α) (h : #α < #β) [Infinite α] :
    exists a : α, Infinite (f ⁻¹' {a}) := by
  suffices Infinite β from exists_infinite_fiber f h
  exact .of_cardinalMk_le h.le

/--
theorem `exists_uncountable_fiber` / 定理 `exists_uncountable_fiber`

English:
theorem exists_uncountable_fiber
  given: {β α : Type u} (f : β -> α) (h : #α < #β) [Uncountable β]
  proof: by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← aleph_one_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ (by simp) aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_ord]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_

中文:
定理 存在_uncountable_fiber
  条件: {β α : 类型u} (f : β -> α) (h : #α < #β) [不可数 β]
  证明: by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← aleph_one_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ (by simp) aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_ord]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_mk_iff, Order.succ_le_succ_iff, aleph0_le_mk, aleph0_lt_aleph_one, aleph0_lt_aleph_one.le, aleph0_lt_mk_iff, aleph_one_le_iff, cof_ord, infinite_pigeonhole_card, infinite_pigeonhole_card_lt, isRegular_aleph_one, isRegular_aleph_one.cof_ord, lt_or_ge, simp_rw, succ_aleph0, succ_le_of_lt, succ_le_succ_iff
-/
theorem exists_uncountable_fiber {β α : Type u} (f : β -> α) (h : #α < #β) [Uncountable β] :
    exists a : α, Uncountable (f ⁻¹' {a}) := by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← aleph_one_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ (by simp) aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_ord]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (aleph0_le_mk β)
    rw [← Order.succ_le_succ_iff]; rw [succ_aleph0] at hα
    exact ⟨a, hα.trans (succ_le_of_lt ha)⟩

/--
theorem `le_range_of_union_finset_eq_univ` / 定理 `le_range_of_union_finset_eq_univ`

English:
theorem le_range_of_union_finset_eq_univ
  statement: {α β : Type*} [Infinite β] (f : α -> Finset β)
  proof: by
  by_contra h
  simp only [not_le] at h
  let u : forall b, exists a, b in f a := fun b => by simpa using (w.ge :) (Set.mem_univ b)
  let u' : β -> range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : forall a, u' ⁻¹' {⟨f a, by simp⟩} <= f a := by
    rintro a p m
    have m : f (u p).choose

中文:
定理 le_range_of_union_finset_eq_univ
  结论: {α β : 类型} [无限 β] (f : α -> 有限集 β)
  证明: by
  by_contra h
  simp only [not_le] at h
  let u : forall b, exists a, b in f a := fun b => by simpa using (w.ge :) (Set.mem_univ b)
  let u' : β -> range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : forall a, u' ⁻¹' {⟨f a, by simp⟩} <= f a := by
    rintro a p m
    have m : f (u p).choose

Depends on / 依赖: Infinite, Infinite.of_injective, Set.mem_univ, choose_spec, exists_infinite_fiber, inclusion, inclusion_injective, mem_univ, not_le, of_injective, w.ge
-/
theorem le_range_of_union_finset_eq_univ {α β : Type*} [Infinite β] (f : α -> Finset β)
    (w : ⋃ a, (f a : Set β) = Set.univ) : #β <= #(range f) := by
  by_contra h
  simp only [not_le] at h
  let u : forall b, exists a, b in f a := fun b => by simpa using (w.ge :) (Set.mem_univ b)
  let u' : β -> range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : forall a, u' ⁻¹' {⟨f a, by simp⟩} <= f a := by
    rintro a p m
    have m : f (u p).choose = f a := by simpa [u'] using m
    rw [← m]
    apply fun b => (u b).choose_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false

@[deprecated (since := "2026-01-17")] alias le_range_of_union_finset_eq_top :=
  le_range_of_union_finset_eq_univ

end Cardinal
