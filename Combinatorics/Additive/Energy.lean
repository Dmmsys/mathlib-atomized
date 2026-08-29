/-
Copyright (c) 2022 Yaël Dillies, Ella Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Ella Yu
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Additive energy

This file defines the additive energy of two finsets of a group. This is a central quantity in
additive combinatorics.

## Main declarations

* `Finset.addEnergy`: The additive energy of two finsets in an additive group.
* `Finset.mulEnergy`: The multiplicative energy of two finsets in a group.

## Notation

The following notations are defined in the `Combinatorics.Additive` scope:
* `E[s, t]` for `Finset.addEnergy s t`.
* `Eₘ[s, t]` for `Finset.mulEnergy s t`.
* `E[s]` for `E[s, s]`.
* `Eₘ[s]` for `Eₘ[s, s]`.

## TODO

It's possibly interesting to have
`(s ×ˢ s) ×ˢ t ×ˢ t).filter (fun x : (α × α) × α × α ↦ x.1.1 * x.2.1 = x.1.2 * x.2.2)`
(whose `card` is `mulEnergy s t`) as a standalone definition.
-/

@[expose] public section

open scoped Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset
section Mul
variable [Mul α] {s s₁ s₂ t t₁ t₂ : Finset α}

/-- The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of
quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`.

The notation `Eₘ[s, t]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`.

The notation `E[s, t]` is available in scope `Combinatorics.Additive`. -/]
/--
Definition of `mulEnergy` / `mulEnergy` 的定义

English:
definition mulEnergy
  signature: (s t : Finset α)
  body: #{x in ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2}

中文:
定义 mulEnergy
  签名: (s t : Finset α)
  定义体: #{x in ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2}
-/
def mulEnergy (s t : Finset α) : Nat :=
  #{x in ((s ×ˢ s) ×ˢ t ×ˢ t) | x.1.1 * x.2.1 = x.1.2 * x.2.2}

/-- The multiplicative energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s ", " t "]" => Finset.mulEnergy s t

/-- The additive energy of two finsets `s` and `t` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s ", " t "]" => Finset.addEnergy s t

/-- The multiplicative energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ * b₁ = a₂ * b₂`. -/
scoped[Combinatorics.Additive] notation3:max "Eₘ[" s "]" => Finset.mulEnergy s s

/-- The additive energy of a finset `s` in a group is the number of quadruples
`(a₁, a₂, b₁, b₂) ∈ s × s × s × s` such that `a₁ + b₁ = a₂ + b₂`. -/
scoped[Combinatorics.Additive] notation3:max "E[" s "]" => Finset.addEnergy s s

open scoped Combinatorics.Additive

@[to_additive (attr := gcongr)]
/--
lemma `mulEnergy_mono` / 引理 `mulEnergy_mono`

English:
lemma mulEnergy_mono
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: Eₘ[s₁, t₁] <= Eₘ[s₂, t₂]
  proof: by
  unfold mulEnergy; gcongr

中文:
引理 mulEnergy_mono
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: Eₘ[s₁, t₁] <= Eₘ[s₂, t₂]
  证明: by
  unfold mulEnergy; gcongr

Depends on / 依赖: mulEnergy
-/
lemma mulEnergy_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : Eₘ[s₁, t₁] <= Eₘ[s₂, t₂] := by
  unfold mulEnergy; gcongr

/--
lemma `mulEnergy_mono_left` / 引理 `mulEnergy_mono_left`

English:
lemma mulEnergy_mono_left
  given: (hs : s₁ subseteq s₂)
  statement: Eₘ[s₁, t] <= Eₘ[s₂, t]
  proof: mulEnergy_mono hs Subset.rfl

中文:
引理 mulEnergy_mono_left
  条件: (hs : s₁ subseteq s₂)
  结论: Eₘ[s₁, t] <= Eₘ[s₂, t]
  证明: mulEnergy_mono hs Subset.rfl
-/
@[to_additive] lemma mulEnergy_mono_left (hs : s₁ subseteq s₂) : Eₘ[s₁, t] <= Eₘ[s₂, t] :=
  mulEnergy_mono hs Subset.rfl

/--
lemma `mulEnergy_mono_right` / 引理 `mulEnergy_mono_right`

English:
lemma mulEnergy_mono_right
  given: (ht : t₁ subseteq t₂)
  statement: Eₘ[s, t₁] <= Eₘ[s, t₂]
  proof: mulEnergy_mono Subset.rfl ht

中文:
引理 mulEnergy_mono_right
  条件: (ht : t₁ subseteq t₂)
  结论: Eₘ[s, t₁] <= Eₘ[s, t₂]
  证明: mulEnergy_mono Subset.rfl ht
-/
@[to_additive] lemma mulEnergy_mono_right (ht : t₁ subseteq t₂) : Eₘ[s, t₁] <= Eₘ[s, t₂] :=
  mulEnergy_mono Subset.rfl ht

/--
lemma `le_mulEnergy` / 引理 `le_mulEnergy`

English:
lemma le_mulEnergy
  statement: #s * #t <= Eₘ[s, t]
  proof: by
  rw [← card_product]
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)

中文:
引理 le_mulEnergy
  结论: #s * #t <= Eₘ[s, t]
  证明: by
  rw [← card_product]
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)
-/
@[to_additive] lemma le_mulEnergy : #s * #t <= Eₘ[s, t] := by
  rw [← card_product]
  exact card_le_card_of_injOn (fun x => ((x.1, x.1), x.2, x.2)) (by simp [Set.MapsTo]) (by simp)

/--
lemma `le_mulEnergy_self` / 引理 `le_mulEnergy_self`

English:
lemma le_mulEnergy_self
  statement: #s ^ 2 <= Eₘ[s]
  proof: sq #s ▸ le_mulEnergy

中文:
引理 le_mulEnergy_self
  结论: #s ^ 2 <= Eₘ[s]
  证明: sq #s ▸ le_mulEnergy
-/
@[to_additive] lemma le_mulEnergy_self : #s ^ 2 <= Eₘ[s] := sq #s ▸ le_mulEnergy

/--
lemma `mulEnergy_pos` / 引理 `mulEnergy_pos`

English:
lemma mulEnergy_pos
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  statement: 0 < Eₘ[s, t]
  proof: (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy

中文:
引理 mulEnergy_pos
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  结论: 0 < Eₘ[s, t]
  证明: (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy
-/
@[to_additive] lemma mulEnergy_pos (hs : s.Nonempty) (ht : t.Nonempty) : 0 < Eₘ[s, t] :=
  (mul_pos hs.card_pos ht.card_pos).trans_le le_mulEnergy

/--
lemma `mulEnergy_self_pos` / 引理 `mulEnergy_self_pos`

English:
lemma mulEnergy_self_pos
  given: (hs : s.Nonempty)
  statement: 0 < Eₘ[s]
  proof: mulEnergy_pos hs hs

中文:
引理 mulEnergy_self_pos
  条件: (hs : s.Nonempty)
  结论: 0 < Eₘ[s]
  证明: mulEnergy_pos hs hs
-/
@[to_additive] lemma mulEnergy_self_pos (hs : s.Nonempty) : 0 < Eₘ[s] :=
  mulEnergy_pos hs hs

variable (s t)

/--
lemma `mulEnergy_empty_left` / 引理 `mulEnergy_empty_left`

English:
lemma mulEnergy_empty_left
  statement: Eₘ[∅, t] = 0
  proof: by simp [mulEnergy]

中文:
引理 mulEnergy_empty_left
  结论: Eₘ[∅, t] = 0
  证明: by simp [mulEnergy]
-/
@[to_additive (attr := simp)] lemma mulEnergy_empty_left : Eₘ[∅, t] = 0 := by simp [mulEnergy]

/--
lemma `mulEnergy_empty_right` / 引理 `mulEnergy_empty_right`

English:
lemma mulEnergy_empty_right
  statement: Eₘ[s, ∅] = 0
  proof: by simp [mulEnergy]

中文:
引理 mulEnergy_empty_right
  结论: Eₘ[s, ∅] = 0
  证明: by simp [mulEnergy]
-/
@[to_additive (attr := simp)] lemma mulEnergy_empty_right : Eₘ[s, ∅] = 0 := by simp [mulEnergy]

variable {s t}

/--
lemma `mulEnergy_pos_iff` / 引理 `mulEnergy_pos_iff`

English:
lemma mulEnergy_pos_iff
  statement: 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  proof: by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy_pos h.1 h.2

中文:
引理 mulEnergy_pos_iff
  结论: 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  证明: by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy_pos h.1 h.2
-/
@[to_additive (attr := simp)] lemma mulEnergy_pos_iff : 0 < Eₘ[s, t] ↔ s.Nonempty ∧ t.Nonempty where
  mp h := by by_contra! +distrib rfl | rfl <;> simp at h
  mpr h := mulEnergy_pos h.1 h.2

/--
lemma `mulEnergy_eq_zero_iff` / 引理 `mulEnergy_eq_zero_iff`

English:
lemma mulEnergy_eq_zero_iff
  statement: Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅
  proof: by
  simp [← (Nat.zero_le _).not_lt_iff_eq', imp_iff_or_not, or_comm]

中文:
引理 mulEnergy_eq_zero_iff
  结论: Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅
  证明: by
  simp [← (Nat.zero_le _).not_lt_iff_eq', imp_iff_or_not, or_comm]
-/
@[to_additive (attr := simp)] lemma mulEnergy_eq_zero_iff : Eₘ[s, t] = 0 ↔ s = ∅ ∨ t = ∅ := by
  simp [← (Nat.zero_le _).not_lt_iff_eq', imp_iff_or_not, or_comm]

/--
lemma `mulEnergy_self_pos_iff` / 引理 `mulEnergy_self_pos_iff`

English:
lemma mulEnergy_self_pos_iff
  statement: 0 < Eₘ[s] ↔ s.Nonempty
  proof: by
  rw [mulEnergy_pos_iff]; rw [and_self_iff]

中文:
引理 mulEnergy_self_pos_iff
  结论: 0 < Eₘ[s] ↔ s.Nonempty
  证明: by
  rw [mulEnergy_pos_iff]; rw [and_self_iff]
-/
@[to_additive] lemma mulEnergy_self_pos_iff : 0 < Eₘ[s] ↔ s.Nonempty := by
  rw [mulEnergy_pos_iff]; rw [and_self_iff]

/--
lemma `mulEnergy_self_eq_zero_iff` / 引理 `mulEnergy_self_eq_zero_iff`

English:
lemma mulEnergy_self_eq_zero_iff
  statement: Eₘ[s] = 0 ↔ s = ∅
  proof: by
  rw [mulEnergy_eq_zero_iff]; rw [or_self_iff]

中文:
引理 mulEnergy_self_eq_zero_iff
  结论: Eₘ[s] = 0 ↔ s = ∅
  证明: by
  rw [mulEnergy_eq_zero_iff]; rw [or_self_iff]
-/
@[to_additive] lemma mulEnergy_self_eq_zero_iff : Eₘ[s] = 0 ↔ s = ∅ := by
  rw [mulEnergy_eq_zero_iff]; rw [or_self_iff]

/--
lemma `mulEnergy_eq_card_filter` / 引理 `mulEnergy_eq_card_filter`

English:
lemma mulEnergy_eq_card_filter
  given: (s t : Finset α)
  proof: card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

中文:
引理 mulEnergy_eq_card_filter
  条件: (s t : Finset α)
  证明: card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])
-/
@[to_additive] lemma mulEnergy_eq_card_filter (s t : Finset α) :
    Eₘ[s, t] = #{x in ((s ×ˢ t) ×ˢ s ×ˢ t) | x.1.1 * x.1.2 = x.2.1 * x.2.2} :=
  card_equiv (.prodProdProdComm _ _ _ _) (by simp [and_and_and_comm])

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mulEnergy_eq_sum_sq'` / 引理 `mulEnergy_eq_sum_sq'`

English:
lemma mulEnergy_eq_sum_sq'
  given: (s t : Finset α)
  proof: by
  simp_rw [mulEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)

中文:
引理 mulEnergy_eq_sum_sq'
  条件: (s t : Finset α)
  证明: by
  simp_rw [mulEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)
-/
@[to_additive] lemma mulEnergy_eq_sum_sq' (s t : Finset α) :
    Eₘ[s, t] = ∑ a in s * t, #{xy in s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  simp_rw [mulEnergy_eq_card_filter, sq, ← card_product]
  rw [← card_disjiUnion]
  swap
  · aesop (add simp [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left])
  · congr
    aesop (add unsafe mul_mem_mul)

/--
lemma `mulEnergy_eq_sum_sq` / 引理 `mulEnergy_eq_sum_sq`

English:
lemma mulEnergy_eq_sum_sq
  given: [Fintype α] (s t : Finset α)
  proof: by
  rw [mulEnergy_eq_sum_sq']
exact Fintype.sum_subset by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_addEnergy]

中文:
引理 mulEnergy_eq_sum_sq
  条件: [Fintype α] (s t : Finset α)
  证明: by
  rw [mulEnergy_eq_sum_sq']
exact Fintype.sum_subset by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_addEnergy]
-/
@[to_additive] lemma mulEnergy_eq_sum_sq [Fintype α] (s t : Finset α) :
    Eₘ[s, t] = ∑ a, #{xy in s ×ˢ t | xy.1 * xy.2 = a} ^ 2 := by
  rw [mulEnergy_eq_sum_sq']
exact Fintype.sum_subset by aesop (add simp [filter_eq_empty_iff, mul_mem_mul])

@[to_additive card_sq_le_card_mul_addEnergy]
/--
lemma `card_sq_le_card_mul_mulEnergy` / 引理 `card_sq_le_card_mul_mulEnergy`

English:
lemma card_sq_le_card_mul_mulEnergy
  given: (s t u : Finset α)
  proof: by
  calc
    _ = (∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ <= #u * ∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := Nat) _ 1 _
    _ <= #u * ∑ c in s * t, #{xy in s ×ˢ t | xy.

中文:
引理 card_sq_le_card_mul_mulEnergy
  条件: (s t u : Finset α)
  证明: by
  calc
    _ = (∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ <= #u * ∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := Nat) _ 1 _
    _ <= #u * ∑ c in s * t, #{xy in s ×ˢ t | xy.

Depends on / 依赖: filter_eq_empty_iff, mulEnergy_eq_sum_sq, mul_le_mul_right, mul_mem_mul, sum_card_fiberwise_eq_card_filter, sum_le_sum_of_ne_zero, sum_mul_sq_le_sq_mul_sq, unsafe
-/
lemma card_sq_le_card_mul_mulEnergy (s t u : Finset α) :
    #{xy in s ×ˢ t | xy.1 * xy.2 in u} ^ 2 <= #u * Eₘ[s, t] := by
  calc
    _ = (∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c}) ^ 2 := by
        rw [← sum_card_fiberwise_eq_card_filter]
    _ <= #u * ∑ c in u, #{xy in s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        simpa using sum_mul_sq_le_sq_mul_sq (R := Nat) _ 1 _
    _ <= #u * ∑ c in s * t, #{xy in s ×ˢ t | xy.1 * xy.2 = c} ^ 2 := by
        refine mul_le_mul_right (sum_le_sum_of_ne_zero ?_) _
        aesop (add simp [filter_eq_empty_iff]) (add unsafe mul_mem_mul)
    _ = #u * Eₘ[s, t] := by rw [mulEnergy_eq_sum_sq']

/--
lemma `le_card_mul_mul_mulEnergy` / 引理 `le_card_mul_mul_mulEnergy`

English:
lemma le_card_mul_mul_mulEnergy
  given: (s t : Finset α)
  proof: calc
    _ = #{xy in s ×ˢ t | xy.1 * xy.2 in s * t} ^ 2 := by
      rw [filter_eq_self.2]; rw [card_product]; rw [mul_pow]; aesop (add unsafe mul_mem_mul)
    _ <= #(s * t) * Eₘ[s, t] := card_sq_le_card_mul_mulEnergy _ _ _

中文:
引理 le_card_mul_mul_mulEnergy
  条件: (s t : Finset α)
  证明: calc
    _ = #{xy in s ×ˢ t | xy.1 * xy.2 in s * t} ^ 2 := by
      rw [filter_eq_self.2]; rw [card_product]; rw [mul_pow]; aesop (add unsafe mul_mem_mul)
    _ <= #(s * t) * Eₘ[s, t] := card_sq_le_card_mul_mulEnergy _ _ _
-/
@[to_additive le_card_add_mul_addEnergy] lemma le_card_mul_mul_mulEnergy (s t : Finset α) :
    #s ^ 2 * #t ^ 2 <= #(s * t) * Eₘ[s, t] :=
  calc
    _ = #{xy in s ×ˢ t | xy.1 * xy.2 in s * t} ^ 2 := by
      rw [filter_eq_self.2]; rw [card_product]; rw [mul_pow]; aesop (add unsafe mul_mem_mul)
    _ <= #(s * t) * Eₘ[s, t] := card_sq_le_card_mul_mulEnergy _ _ _

end Mul

open scoped Combinatorics.Additive

section CommMonoid

variable [CommMonoid α]

/--
lemma `mulEnergy_comm` / 引理 `mulEnergy_comm`

English:
lemma mulEnergy_comm
  given: (s t : Finset α)
  statement: Eₘ[s, t] = Eₘ[t, s]
  proof: by
  rw [mulEnergy]; rw [← Finset.card_map (Equiv.prodComm _ _).toEmbedding]; rw [map_filter]
  simp [mulEnergy, mul_comm, map_eq_image]

中文:
引理 mulEnergy_comm
  条件: (s t : Finset α)
  结论: Eₘ[s, t] = Eₘ[t, s]
  证明: by
  rw [mulEnergy]; rw [← Finset.card_map (Equiv.prodComm _ _).toEmbedding]; rw [map_filter]
  simp [mulEnergy, mul_comm, map_eq_image]
-/
@[to_additive] lemma mulEnergy_comm (s t : Finset α) : Eₘ[s, t] = Eₘ[t, s] := by
  rw [mulEnergy]; rw [← Finset.card_map (Equiv.prodComm _ _).toEmbedding]; rw [map_filter]
  simp [mulEnergy, mul_comm, map_eq_image]

end CommMonoid

section CommGroup

variable [CommGroup α] [Fintype α] (s t : Finset α)

@[to_additive (attr := simp)]
/--
lemma `mulEnergy_univ_left` / 引理 `mulEnergy_univ_left`

English:
lemma mulEnergy_univ_left
  statement: Eₘ[univ, t] = Fintype.card α * t.card ^ 2
  proof: by
  simp only [mulEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α -> (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [f, P

中文:
引理 mulEnergy_univ_left
  结论: Eₘ[univ, t] = Fintype.card α * t.card ^ 2
  证明: by
  simp only [mulEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α -> (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [f, P

Depends on / 依赖: Finset, Fintype, Fintype.card, Prod.exists, Prod.ext_iff, card_image_of_injOn, card_product, ext_iff, mem_filter, mem_image, mem_product, mem_univ, mulEnergy, mul_right_cancel, simp_rw, true_and, univ_product_univ
-/
lemma mulEnergy_univ_left : Eₘ[univ, t] = Fintype.card α * t.card ^ 2 := by
  simp only [mulEnergy, univ_product_univ, Fintype.card, sq, ← card_product]
  let f : α × α × α -> (α × α) × α × α := fun x => ((x.1 * x.2.2, x.1 * x.2.1), x.2)
  have : (↑((univ : Finset α) ×ˢ t ×ˢ t) : Set (α × α × α)).InjOn f := by
    rintro ⟨a₁, b₁, c₁⟩ _ ⟨a₂, b₂, c₂⟩ h₂ h
    simp_rw [f, Prod.ext_iff] at h
    obtain ⟨h, rfl, rfl⟩ := h
    rw [mul_right_cancel h.1]
  rw [← card_image_of_injOn this]
  congr with a
  simp only [mem_filter, mem_product, mem_univ, true_and, mem_image,
    Prod.exists]
  refine ⟨fun h => ⟨a.1.1 * a.2.2⁻¹, _, _, h.1, by simp [f, mul_right_comm, h.2]⟩, ?_⟩
  rintro ⟨b, c, d, hcd, rfl⟩
  simpa [f, mul_right_comm]

@[to_additive (attr := simp)]
/--
lemma `mulEnergy_univ_right` / 引理 `mulEnergy_univ_right`

English:
lemma mulEnergy_univ_right
  statement: Eₘ[s, univ] = Fintype.card α * s.card ^ 2
  proof: by
  rw [mulEnergy_comm]; rw [mulEnergy_univ_left]

中文:
引理 mulEnergy_univ_right
  结论: Eₘ[s, univ] = Fintype.card α * s.card ^ 2
  证明: by
  rw [mulEnergy_comm]; rw [mulEnergy_univ_left]

Depends on / 依赖: mulEnergy_comm, mulEnergy_univ_left
-/
lemma mulEnergy_univ_right : Eₘ[s, univ] = Fintype.card α * s.card ^ 2 := by
  rw [mulEnergy_comm]; rw [mulEnergy_univ_left]

end CommGroup

end Finset
