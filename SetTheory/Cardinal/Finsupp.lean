/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset

/-! # Results on the cardinality of finitely supported functions and multisets. -/

public section

universe u v

namespace Cardinal

@[simp]
/--
theorem `mk_finsupp_lift_of_fintype` / 定理 `mk_finsupp_lift_of_fintype`

English:
theorem mk_finsupp_lift_of_fintype
  given: (α : Type u) (β : Type v) [Fintype α] [Zero β]
  proof: by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq

中文:
定理 mk_finsupp_lift_of_fintype
  条件: (α : 类型u) (β : 类型v) [有限类型 α] [零 β]
  证明: by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite, cardinal_eq, equivFunOnFinite
-/
theorem mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] :
    #(α ->₀ β) = lift.{u} #β ^ Fintype.card α := by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq

/--
theorem `mk_finsupp_of_fintype` / 定理 `mk_finsupp_of_fintype`

English:
theorem mk_finsupp_of_fintype
  given: (α β : Type u) [Fintype α] [Zero β]
  proof: by simp

@[simp]

中文:
定理 mk_finsupp_of_fintype
  条件: (α β : 类型u) [有限类型 α] [零 β]
  证明: by simp

@[simp]
-/
theorem mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] :
    #(α ->₀ β) = #β ^ Fintype.card α := by simp

@[simp]
/--
theorem `mk_finsupp_lift_of_infinite` / 定理 `mk_finsupp_lift_of_infinite`

English:
theorem mk_finsupp_lift_of_infinite
  given: (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β]
  proof: by
  apply le_antisymm
  · calc
      #(α ->₀ β) <= #(Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = #(α × β) := mk_finset_of_infinite _
      _ = max (lift.{v} #α) (lift.{u} #β) := by
        rw [mk_prod]; rw [mul_eq_max_of_aleph0_le_left] <;> simp
  · apply max_le <;> rw [← lift_id #(α ->₀ β), ← lift_umax]
    · obtain ⟨b, hb⟩ := exists_ne (0 : β)
      exact lift_mk_le.{v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
    · inhabit α
      exact lift_mk_le.{u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩

中文:
定理 mk_finsupp_lift_of_infinite
  条件: (α : 类型u) (β : 类型v) [无限 α] [零 β] [非平凡 β]
  证明: by
  apply le_antisymm
  · calc
      #(α ->₀ β) <= #(Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = #(α × β) := mk_finset_of_infinite _
      _ = max (lift.{v} #α) (lift.{u} #β) := by
        rw [mk_prod]; rw [mul_eq_max_of_aleph0_le_left] <;> simp
  · apply max_le <;> rw [← lift_id #(α ->₀ β), ← lift_umax]
    · obtain ⟨b, hb⟩ := exists_ne (0 : β)
      exact lift_mk_le.{v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
    · inhabit α
      exact lift_mk_le.{u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩

Depends on / 依赖: Finset, Finsupp, Finsupp.graph_injective, Finsupp.single_injective, Finsupp.single_left_injective, exists_ne, graph_injective, inhabit, le_antisymm, lift_id, lift_mk_le, lift_umax, max_le, mk_finset_of_infinite, mk_le_of_injective, mk_prod, mul_eq_max_of_aleph0_le_left, single_injective, single_left_injective
-/
theorem mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] :
    #(α ->₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  apply le_antisymm
  · calc
      #(α ->₀ β) <= #(Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = #(α × β) := mk_finset_of_infinite _
      _ = max (lift.{v} #α) (lift.{u} #β) := by
        rw [mk_prod]; rw [mul_eq_max_of_aleph0_le_left] <;> simp
  · apply max_le <;> rw [← lift_id #(α ->₀ β), ← lift_umax]
    · obtain ⟨b, hb⟩ := exists_ne (0 : β)
      exact lift_mk_le.{v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
    · inhabit α
      exact lift_mk_le.{u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩

/--
theorem `mk_finsupp_of_infinite` / 定理 `mk_finsupp_of_infinite`

English:
theorem mk_finsupp_of_infinite
  given: (α β : Type u) [Infinite α] [Zero β] [Nontrivial β]
  proof: by simp

@[simp]

中文:
定理 mk_finsupp_of_infinite
  条件: (α β : 类型u) [无限 α] [零 β] [非平凡 β]
  证明: by simp

@[simp]
-/
theorem mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β] :
    #(α ->₀ β) = max #α #β := by simp

@[simp]
/--
theorem `mk_finsupp_lift_of_infinite'` / 定理 `mk_finsupp_lift_of_infinite'`

English:
theorem mk_finsupp_lift_of_infinite'
  given: (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β]
  proof: by
  cases fintypeOrInfinite α
  · rw [mk_finsupp_lift_of_fintype]
    have : ℵ₀ <= (#β).lift := aleph0_le_lift.2 (aleph0_le_mk β)
    rw [max_eq_right (le_trans _ this)]; rw [power_nat_eq this]
    exacts [Fintype.card_pos, lift_le_aleph0.2 (lt_aleph0_of_finite _).le]
  · apply mk_finsupp_lift_of_infinite

中文:
定理 mk_finsupp_lift_of_infinite'
  条件: (α : 类型u) (β : 类型v) [非空 α] [零 β] [无限 β]
  证明: by
  cases fintypeOrInfinite α
  · rw [mk_finsupp_lift_of_fintype]
    have : ℵ₀ <= (#β).lift := aleph0_le_lift.2 (aleph0_le_mk β)
    rw [max_eq_right (le_trans _ this)]; rw [power_nat_eq this]
    exacts [Fintype.card_pos, lift_le_aleph0.2 (lt_aleph0_of_finite _).le]
  · apply mk_finsupp_lift_of_infinite

Depends on / 依赖: Fintype, Fintype.card_pos, aleph0_le_lift, aleph0_le_mk, card_pos, exacts, fintypeOrInfinite, le_trans, lift_le_aleph0, lt_aleph0_of_finite, max_eq_right, mk_finsupp_lift_of_fintype, mk_finsupp_lift_of_infinite, power_nat_eq
-/
theorem mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] :
    #(α ->₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  cases fintypeOrInfinite α
  · rw [mk_finsupp_lift_of_fintype]
    have : ℵ₀ <= (#β).lift := aleph0_le_lift.2 (aleph0_le_mk β)
    rw [max_eq_right (le_trans _ this)]; rw [power_nat_eq this]
    exacts [Fintype.card_pos, lift_le_aleph0.2 (lt_aleph0_of_finite _).le]
  · apply mk_finsupp_lift_of_infinite

/--
theorem `mk_finsupp_of_infinite'` / 定理 `mk_finsupp_of_infinite'`

English:
theorem mk_finsupp_of_infinite'
  given: (α β : Type u) [Nonempty α] [Zero β] [Infinite β]
  proof: by simp

中文:
定理 mk_finsupp_of_infinite'
  条件: (α β : 类型u) [非空 α] [零 β] [无限 β]
  证明: by simp
-/
theorem mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] :
    #(α ->₀ β) = max #α #β := by simp

/--
theorem `mk_finsupp_nat` / 定理 `mk_finsupp_nat`

English:
theorem mk_finsupp_nat
  given: (α : Type u) [Nonempty α]
  statement: #(α ->₀ Nat) = max #α ℵ₀
  proof: by simp

中文:
定理 mk_finsupp_nat
  条件: (α : 类型u) [非空 α]
  结论: #(α ->₀ 自然数) = 最大值 #α ℵ₀
  证明: by simp
-/
theorem mk_finsupp_nat (α : Type u) [Nonempty α] : #(α ->₀ Nat) = max #α ℵ₀ := by simp

/--
theorem `mk_multiset_of_isEmpty` / 定理 `mk_multiset_of_isEmpty`

English:
theorem mk_multiset_of_isEmpty
  given: (α : Type u) [IsEmpty α]
  statement: #(Multiset α) = 1
  proof: Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)

@[simp]

中文:
定理 mk_multiset_of_isEmpty
  条件: (α : 类型u) [是空 α]
  结论: #(Multiset α) = 1
  证明: Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)

@[simp]

Depends on / 依赖: Multiset, Multiset.toFinsupp.toEquiv.cardinal_eq.trans, cardinal_eq, toEquiv, toFinsupp
-/
theorem mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : #(Multiset α) = 1 :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)

@[simp]
/--
theorem `mk_multiset_of_nonempty` / 定理 `mk_multiset_of_nonempty`

English:
theorem mk_multiset_of_nonempty
  given: (α : Type u) [Nonempty α]
  statement: #(Multiset α) = max #α ℵ₀
  proof: by
  classical
  exact Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)

中文:
定理 mk_multiset_of_nonempty
  条件: (α : 类型u) [非空 α]
  结论: #(Multiset α) = 最大值 #α ℵ₀
  证明: by
  classical
  exact Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)

Depends on / 依赖: Multiset, Multiset.toFinsupp.toEquiv.cardinal_eq.trans, cardinal_eq, classical, mk_finsupp_nat, toEquiv, toFinsupp
-/
theorem mk_multiset_of_nonempty (α : Type u) [Nonempty α] : #(Multiset α) = max #α ℵ₀ := by
  classical
  exact Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)

/--
theorem `mk_multiset_of_infinite` / 定理 `mk_multiset_of_infinite`

English:
theorem mk_multiset_of_infinite
  given: (α : Type u) [Infinite α]
  statement: #(Multiset α) = #α
  proof: by simp

中文:
定理 mk_multiset_of_infinite
  条件: (α : 类型u) [无限 α]
  结论: #(Multiset α) = #α
  证明: by simp
-/
theorem mk_multiset_of_infinite (α : Type u) [Infinite α] : #(Multiset α) = #α := by simp

end Cardinal
