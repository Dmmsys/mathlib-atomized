/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Order.Zorn

/-!
# Extend a partial order to a linear order

This file constructs a linear order which is an extension of the given partial order, using Zorn's
lemma.
-/

@[expose] public section


universe u

open Set

/--
theorem `extend_partialOrder` / 定理 `extend_partialOrder`

English:
theorem extend_partialOrder
  given: {α : Type u} (r : α -> α -> Prop) [IsPartialOrder α r]
  proof: by
  let S := { s | IsPartialOrder α s }
  have hS : forall c, c subseteq S -> IsChain (· <= ·) c -> forall y in c, exists ub in S, forall z in c, z <= ub := by
    rintro c hc₁ hc₂ s hs
    have := (hc₁ hs).1
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    refine
        { refl := ?_
          

中文:
定理 extend_partialOrder
  条件: {α : 类型u} (r : α -> α -> 命题) [是偏序 α r]
  证明: by
  let S := { s | IsPartialOrder α s }
  have hS : forall c, c subseteq S -> IsChain (· <= ·) c -> forall y in c, exists ub in S, forall z in c, z <= ub := by
    rintro c hc₁ hc₂ s hs
    have := (hc₁ hs).1
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    refine
        { refl := ?_
          

Depends on / 依赖: IsChain, IsPartialOrder, antisymm, binary_relation_sSup_iff, le_sSup, simp_rw, subseteq
-/
theorem extend_partialOrder {α : Type u} (r : α -> α -> Prop) [IsPartialOrder α r] :
    exists s : α -> α -> Prop, IsLinearOrder α s ∧ r <= s := by
  let S := { s | IsPartialOrder α s }
  have hS : forall c, c subseteq S -> IsChain (· <= ·) c -> forall y in c, exists ub in S, forall z in c, z <= ub := by
    rintro c hc₁ hc₂ s hs
    have := (hc₁ hs).1
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    refine
        { refl := ?_
          trans := ?_
          antisymm := ?_ } <;>
      simp_rw [binary_relation_sSup_iff]
    · intro x
      exact ⟨s, hs, refl x⟩
    · rintro x y z ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      have : IsPartialOrder _ _ := hc₁ h₁s₁
      have : IsPartialOrder _ _ := hc₁ h₁s₂
      rcases hc₂.total h₁s₁ h₁s₂ with h | h
      · exact ⟨s₂, h₁s₂, _root_.trans (h _ _ h₂s₁) h₂s₂⟩
      · exact ⟨s₁, h₁s₁, _root_.trans h₂s₁ (h _ _ h₂s₂)⟩
    · rintro x y ⟨s₁, h₁s₁, h₂s₁⟩ ⟨s₂, h₁s₂, h₂s₂⟩
      have : IsPartialOrder _ _ := hc₁ h₁s₁
      have : IsPartialOrder _ _ := hc₁ h₁s₂
      rcases hc₂.total h₁s₁ h₁s₂ with h | h
      · exact antisymm (h _ _ h₂s₁) h₂s₂
      · apply antisymm h₂s₁ (h _ _ h₂s₂)
  obtain ⟨s, hrs, hs⟩ := zorn_le_nonempty₀ S hS r ‹_›
  have : IsPartialOrder α s := hs.prop
  refine ⟨s,
    { total := ?_, refl := hs.1.refl, trans := hs.1.trans, antisymm := hs.1.antisymm }, hrs⟩
  intro x y
  by_contra! h
  let s' x' y' := s x' y' ∨ s x' x ∧ s y y'
  rw [hs.eq_of_le (y := s') ?_ fun _ _ => Or.inl] at h
  · apply h.1 (Or.inr ⟨refl _, refl _⟩)
  · refine
    { refl := fun x => Or.inl (refl _)
      trans := ?_
      antisymm := ?_ }
    · rintro a b c (ab | ⟨ax : s a x, yb : s y b⟩) (bc | ⟨bx : s b x, yc : s y c⟩)
      · exact Or.inl (_root_.trans ab bc)
      · exact Or.inr ⟨_root_.trans ab bx, yc⟩
      · exact Or.inr ⟨ax, _root_.trans yb bc⟩
      · exact Or.inr ⟨ax, yc⟩
    rintro a b (ab | ⟨ax : s a x, yb : s y b⟩) (ba | ⟨bx : s b x, ya : s y a⟩)
    · exact antisymm ab ba
    · exact (h.2 (_root_.trans ya (_root_.trans ab bx))).elim
    · exact (h.2 (_root_.trans yb (_root_.trans ba ax))).elim
    · exact (h.2 (_root_.trans yb bx)).elim

/--
Definition of `LinearExtension` / `LinearExtension` 的定义

English:
definition LinearExtension
  signature: (α : Type u)
  body: α

中文:
定义 LinearExtension
  签名: (α : 类型u)
  定义体: α
-/
def LinearExtension (α : Type u) : Type u :=
  α

noncomputable instance {α : Type u} [PartialOrder α] : LinearOrder (LinearExtension α) where
  le := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose
  le_refl := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.1.1.1.1.1
  le_trans := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.1.1.1.2.1
  le_antisymm := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.1.1.2.1
  le_total := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.1.2.1
  toDecidableLE := Classical.decRel _

/--
Definition of `toLinearExtension` / `toLinearExtension` 的定义

English:
definition toLinearExtension
  signature: {α : Type u} [PartialOrder α]
  body: x
  monotone' := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.2

中文:
定义 toLinearExtension
  签名: {α : 类型u} [偏序 α]
  定义体: x
  monotone' := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.2
-/
noncomputable def toLinearExtension {α : Type u} [PartialOrder α] : α ->o LinearExtension α where
  toFun x := x
  monotone' := (extend_partialOrder ((· <= ·) : α -> α -> Prop)).choose_spec.2

instance {α : Type u} [Inhabited α] : Inhabited (LinearExtension α) :=
  ⟨(default : α)⟩
