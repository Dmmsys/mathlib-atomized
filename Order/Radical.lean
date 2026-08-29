/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison
-/
module

public import Mathlib.Order.Atoms

/-!
# The radical of a lattice

This file contains results on the order radical of a lattice: the infimum of the coatoms.
-/

@[expose] public section

/--
Definition of `Order.radical` / `Order.radical` 的定义

English:
definition Order.radical
  signature: (α : Type*) [Preorder α] [OrderTop α] [InfSet α]
  body: ⨅ a in {H | IsCoatom H}, a

中文:
定义 Order.radical
  签名: (α : 类型) [预序 α] [有顶序 α] [下确界集 α]
  定义体: ⨅ a in {H | IsCoatom H}, a

Depends on / 依赖: IsCoatom
-/
def Order.radical (α : Type*) [Preorder α] [OrderTop α] [InfSet α] : α :=
  ⨅ a in {H | IsCoatom H}, a

variable {α : Type*} [CompleteLattice α]

/--
lemma `Order.radical_le_coatom` / 引理 `Order.radical_le_coatom`

English:
lemma Order.radical_le_coatom
  given: {a : α} (h : IsCoatom a)
  statement: radical α <= a
  proof: biInf_le _ h

中文:
引理 Order.radical_le_coatom
  条件: {a : α} (h : IsCoatom a)
  结论: radical α <= a
  证明: biInf_le _ h

Depends on / 依赖: biInf_le
-/
lemma Order.radical_le_coatom {a : α} (h : IsCoatom a) : radical α <= a := biInf_le _ h

variable {β : Type*} [CompleteLattice β]

/--
theorem `OrderIso.map_radical` / 定理 `OrderIso.map_radical`

English:
theorem OrderIso.map_radical
  given: (f : α ≃o β)
  statement: f (Order.radical α) = Order.radical β
  proof: by
  unfold Order.radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · simp

中文:
定理 OrderIso.map_radical
  条件: (f : α ≃o β)
  结论: f (Order.radical α) = Order.radical β
  证明: by
  unfold Order.radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · simp

Depends on / 依赖: Equiv.iInf_congr, Order.radical, OrderIso, OrderIso.map_iInf, f.toEquiv, fapply, iInf_congr, map_iInf, radical, toEquiv
-/
theorem OrderIso.map_radical (f : α ≃o β) : f (Order.radical α) = Order.radical β := by
  unfold Order.radical
  simp only [OrderIso.map_iInf]
  fapply Equiv.iInf_congr
  · exact f.toEquiv
  · simp

/--
theorem `Order.radical_nongenerating` / 定理 `Order.radical_nongenerating`

English:
theorem Order.radical_nongenerating
  given: [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤)
  statement: a = ⊤
  proof: by
  -- Since the lattice is coatomic, either `a` is already the top element,
  -- or there is a coatom above it.
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · -- In the first case, we're done, this was already the goal.
    rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α <= m := sup_le le (radical_le_coatom c)
    -- Now note that `a ⊔ radical α ≤ m` since both `a ≤ m` and `radical α ≤ m`.
    rw [h]; rw [top_le_iff] at q
    simpa using c.1 q

中文:
定理 Order.radical_nongenerating
  条件: [是余原子的 α] {a : α} (h : a ⊔ radical α = ⊤)
  结论: a = ⊤
  证明: by
  -- Since the lattice is coatomic, either `a` is already the top element,
  -- or there is a coatom above it.
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · -- In the first case, we're done, this was already the goal.
    rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α <= m := sup_le le (radical_le_coatom c)
    -- Now note that `a ⊔ radical α ≤ m` since both `a ≤ m` and `radical α ≤ m`.
    rw [h]; rw [top_le_iff] at q
    simpa using c.1 q
-/
theorem Order.radical_nongenerating [IsCoatomic α] {a : α} (h : a ⊔ radical α = ⊤) : a = ⊤ := by
  -- Since the lattice is coatomic, either `a` is already the top element,
  -- or there is a coatom above it.
  obtain (rfl | w) := eq_top_or_exists_le_coatom a
  · -- In the first case, we're done, this was already the goal.
    rfl
  · obtain ⟨m, c, le⟩ := w
    have q : a ⊔ radical α <= m := sup_le le (radical_le_coatom c)
    -- Now note that `a ⊔ radical α ≤ m` since both `a ≤ m` and `radical α ≤ m`.
    rw [h]; rw [top_le_iff] at q
    simpa using c.1 q
